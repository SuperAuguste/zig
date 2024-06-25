const std = @import("std");
const Zir = std.zig.Zir;
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const Zcu = @import("Module.zig");
const Compilation = @import("Compilation.zig");
const codegen = @import("codegen/c.zig");
const trace = @import("tracy.zig").trace;
const InternPool = @import("InternPool.zig");
const Type = @import("type.zig").Type;

const EmitH = @This();
const Error = error{ OutOfMemory, AnalysisFail };

comp: *Compilation,
loc: Compilation.EmitLoc,
last_err: ?*Zcu.ErrorMsg = null,
decl_table: std.AutoArrayHashMapUnmanaged(InternPool.DeclIndex, DeclBlock) = .{},

pub const DeclBlock = struct {
    fwd_decl: std.ArrayListUnmanaged(u8) = .{},
    /// Each `Decl` stores a set of used `CType`s.  In `flush()`, we iterate
    /// over each `Decl` and generate the definition for each used `CType` once.
    ctype_pool: codegen.CType.Pool = codegen.CType.Pool.empty,

    fn deinit(db: *DeclBlock, gpa: Allocator) void {
        db.ctype_pool.deinit(gpa);
        db.* = undefined;
    }
};

pub fn deinit(emit_h: *EmitH) void {
    const gpa = emit_h.comp.module.?.gpa;
    for (emit_h.decl_table.values()) |*block| {
        block.deinit(gpa);
    }
    emit_h.decl_table.deinit(gpa);
    emit_h.* = undefined;
}

pub fn destroyDecl(emit_h: *EmitH, decl_index: InternPool.DeclIndex) void {
    const gpa = emit_h.comp.module.?.gpa;
    var kv = emit_h.decl_table.fetchSwapRemove(decl_index) orelse return;
    kv.value.deinit(gpa);
}

pub fn genDecl(emit_h: *EmitH, decl_index: InternPool.DeclIndex) Error!void {
    const zcu = emit_h.comp.module.?;
    const gpa = zcu.gpa;
    const decl = zcu.declPtr(decl_index);

    const gop = try emit_h.decl_table.getOrPut(gpa, decl_index);
    if (gop.found_existing) @panic("TODO");

    const block = gop.value_ptr;
    block.* = .{};
    try block.ctype_pool.init(gpa);

    var scratch = std.ArrayListUnmanaged(u32){};
    defer scratch.deinit(gpa);

    // const ctype = try block.ctype_pool.fromType(
    //     gpa,
    //     &scratch,
    //     decl.val.typeOf(zcu),
    //     zcu,
    //     zcu.namespacePtr(decl.src_namespace).file_scope.mod,
    //     .complete,
    //     .emit_h,
    // );

    var dg = codegen.DeclGen{
        .gpa = gpa,
        .zcu = zcu,
        .mod = zcu.namespacePtr(decl.src_namespace).file_scope.mod,
        .error_msg = null,
        .pass = .{ .decl = decl_index },
        .is_naked_fn = false,
        .fwd_decl = block.fwd_decl.toManaged(gpa),
        .ctype_pool = block.ctype_pool,
        .scratch = .{},
        .anon_decl_deps = .{},
        .aligned_anon_decls = .{},
    };

    defer {
        block.fwd_decl = dg.fwd_decl.moveToUnmanaged();
        block.ctype_pool = dg.ctype_pool.move();
        block.ctype_pool.freeUnusedCapacity(gpa);
        dg.scratch.deinit(gpa);
    }

    codegen.genHeaderDecl(&dg, zcu) catch |err| switch (err) {
        error.AnalysisFail => {
            // try zcu.failed_decls.put(gpa, decl_index, object.dg.error_msg.?);
            return;
        },
        else => |e| return e,
    };

    // const writer = block.fwd_decl.writer(gpa);

    // try writer.print("{}", .{try codegen.renderTypePrefix(
    //     .{ .decl = decl_index },
    //     &block.ctype_pool,
    //     zcu,
    //     writer,
    //     ctype,
    //     .suffix,
    //     .{},
    // )});
    // try codegen.renderTypeSuffix(
    //     .{ .decl = decl_index },
    //     &block.ctype_pool,
    //     zcu,
    //     writer,
    //     ctype,
    //     .suffix,
    //     .{},
    // );
}

fn fail(emit_h: *EmitH, comptime format: []const u8, args: anytype) Error {
    emit_h.last_err = Zcu.ErrorMsg.create(emit_h.gpa, emit_h.decl.navSrcLoc(emit_h.zcu).upgrade(emit_h.zcu), format, args) catch |err| return err;
    return error.AnalysisFail;
}

pub const HeaderSection = enum {
    unknown,
    typedefs,
    variables,
    functions,
};

pub fn flushEmitH(emit_h: *EmitH, arena: Allocator, prog_node: std.Progress.Node) !void {
    _ = arena; // Has the same lifetime as the call to Compilation.update.

    const tracy = trace(@src());
    defer tracy.end();

    const sub_prog_node = prog_node.start("Flush Module", 0);
    defer sub_prog_node.end();

    const comp = emit_h.comp;
    const gpa = comp.gpa;
    const zcu = comp.module.?;

    // This code path happens exclusively with -ofmt=c. The flush logic for
    // emit-h is in `flushEmitH`.

    var f: Flush = .{
        .ctype_pool = codegen.CType.Pool.empty,
        .lazy_ctype_pool = codegen.CType.Pool.empty,
    };
    defer f.deinit(gpa);

    // Covers defines, zig.h, ctypes, asm, lazy fwd.
    try f.all_buffers.ensureUnusedCapacity(gpa, 5);

    const ctypes_index = f.all_buffers.items.len;
    f.all_buffers.items.len += 1;

    try f.lazy_ctype_pool.init(gpa);

    // Unlike other backends, the .c code we are emitting has order-dependent decls.
    // `CType`s, forward decls, and non-functions first.

    {
        var export_names: std.AutoHashMapUnmanaged(InternPool.NullTerminatedString, void) = .{};
        defer export_names.deinit(gpa);
        try export_names.ensureTotalCapacity(gpa, @intCast(zcu.decl_exports.entries.len));
        for (zcu.decl_exports.values()) |exports| for (exports.items) |@"export"|
            try export_names.put(gpa, @"export".opts.name, {});

        for (emit_h.decl_table.keys(), emit_h.decl_table.values()) |decl_index, *decl_block| {
            const decl = zcu.declPtr(decl_index);
            assert(decl.has_tv);

            try f.all_buffers.ensureUnusedCapacity(gpa, 1);
            f.appendBufAssumeCapacity(decl_block.fwd_decl.items);
        }
    }

    {
        // We need to flush lazy ctypes after flushing all decls but before flushing any decl ctypes.
        // This ensures that every lazy CType.Index exactly matches the global CType.Index.
        try f.ctype_pool.init(gpa);
        try emit_h.flushCTypes(zcu, &f, .flush, &f.lazy_ctype_pool);

        for (emit_h.decl_table.keys(), emit_h.decl_table.values()) |decl_index, decl_block| {
            try emit_h.flushCTypes(zcu, &f, .{ .decl = decl_index }, &decl_block.ctype_pool);
        }
    }

    f.all_buffers.items[ctypes_index] = .{
        .base = if (f.ctypes_buf.items.len > 0) f.ctypes_buf.items.ptr else "",
        .len = f.ctypes_buf.items.len,
    };
    f.file_size += f.ctypes_buf.items.len;

    const directory = emit_h.loc.directory orelse comp.local_cache_directory;
    const file = try directory.handle.createFile(emit_h.loc.basename, .{
        // We set the end position explicitly below; by not truncating the file, we possibly
        // make it easier on the file system by doing 1 reallocation instead of two.
        .truncate = false,
    });
    defer file.close();

    try file.setEndPos(f.file_size);
    try file.pwritevAll(f.all_buffers.items, 0);
}

const Flush = struct {
    ctype_pool: codegen.CType.Pool,
    ctype_global_from_decl_map: std.ArrayListUnmanaged(codegen.CType) = .{},
    ctypes_buf: std.ArrayListUnmanaged(u8) = .{},

    lazy_ctype_pool: codegen.CType.Pool,

    /// We collect a list of buffers to write, and write them all at once with pwritev 😎
    all_buffers: std.ArrayListUnmanaged(std.posix.iovec_const) = .{},
    /// Keeps track of the total bytes of `all_buffers`.
    file_size: u64 = 0,

    fn appendBufAssumeCapacity(f: *Flush, buf: []const u8) void {
        if (buf.len == 0) return;
        f.all_buffers.appendAssumeCapacity(.{ .base = buf.ptr, .len = buf.len });
        f.file_size += buf.len;
    }

    fn deinit(f: *Flush, gpa: Allocator) void {
        f.all_buffers.deinit(gpa);
        f.lazy_ctype_pool.deinit(gpa);
        f.ctypes_buf.deinit(gpa);
        assert(f.ctype_global_from_decl_map.items.len == 0);
        f.ctype_global_from_decl_map.deinit(gpa);
        f.ctype_pool.deinit(gpa);
    }
};

fn flushCTypes(
    emit_h: *EmitH,
    zcu: *Zcu,
    f: *Flush,
    pass: codegen.DeclGen.Pass,
    decl_ctype_pool: *const codegen.CType.Pool,
) Error!void {
    const gpa = emit_h.comp.gpa;
    const global_ctype_pool = &f.ctype_pool;

    const global_from_decl_map = &f.ctype_global_from_decl_map;
    assert(global_from_decl_map.items.len == 0);
    try global_from_decl_map.ensureTotalCapacity(gpa, decl_ctype_pool.items.len);
    defer global_from_decl_map.clearRetainingCapacity();

    var ctypes_buf = f.ctypes_buf.toManaged(gpa);
    defer f.ctypes_buf = ctypes_buf.moveToUnmanaged();
    const writer = ctypes_buf.writer();

    for (0..decl_ctype_pool.items.len) |decl_ctype_pool_index| {
        const PoolAdapter = struct {
            global_from_decl_map: []const codegen.CType,
            pub fn eql(pool_adapter: @This(), decl_ctype: codegen.CType, global_ctype: codegen.CType) bool {
                return if (decl_ctype.toPoolIndex()) |decl_pool_index|
                    decl_pool_index < pool_adapter.global_from_decl_map.len and
                        pool_adapter.global_from_decl_map[decl_pool_index].eql(global_ctype)
                else
                    decl_ctype.index == global_ctype.index;
            }
            pub fn copy(pool_adapter: @This(), decl_ctype: codegen.CType) codegen.CType {
                return if (decl_ctype.toPoolIndex()) |decl_pool_index|
                    pool_adapter.global_from_decl_map[decl_pool_index]
                else
                    decl_ctype;
            }
        };
        const decl_ctype = codegen.CType.fromPoolIndex(decl_ctype_pool_index);
        const global_ctype, const found_existing = try global_ctype_pool.getOrPutAdapted(
            gpa,
            decl_ctype_pool,
            decl_ctype,
            PoolAdapter{ .global_from_decl_map = global_from_decl_map.items },
        );
        global_from_decl_map.appendAssumeCapacity(global_ctype);
        try codegen.genTypeDecl(
            zcu,
            writer,
            global_ctype_pool,
            global_ctype,
            pass,
            decl_ctype_pool,
            decl_ctype,
            found_existing,
        );
    }
}
