const std = @import("std");
const Air = @import("../../Air.zig");
const Liveness = @import("../../Liveness.zig");
const link = @import("../../link.zig");
const Module = @import("../../Module.zig");
const InternPool = @import("../../InternPool.zig");
const codegen = @import("../../codegen.zig");
const CodeGenError = codegen.CodeGenError;
const Result = codegen.Result;
const DebugInfoOutput = codegen.DebugInfoOutput;
const Encoding = @import("Encoding.zig");
const bits = @import("bits.zig");
const abi = @import("abi.zig");
const Register = bits.Register;
const RegisterManager = abi.RegisterManager;
const Mir = @import("Mir.zig");
const Package = @import("../../Package.zig");
const ErrorMsg = Module.ErrorMsg;
const Allocator = std.mem.Allocator;
const InnerError = CodeGenError || error{OutOfRegisters};

/// General Purpose
const gp = abi.RegisterClass.gp;
/// Function Args
const fa = abi.RegisterClass.fa;
/// Function Returns
const fr = abi.RegisterClass.fr;

const Self = @This();

gpa: Allocator,

register_manager: RegisterManager = .{},

/// MIR Instructions
mir_instructions: std.MultiArrayList(Mir.Inst) = .{},
/// MIR extra data
mir_extra: std.ArrayListUnmanaged(u32) = .{},

air: Air,
mod: *Package.Module,
liveness: Liveness,
bin_file: *link.File,
err_msg: ?*ErrorMsg,
src_loc: Module.SrcLoc,

/// Debug field, used to find bugs in the compiler.
air_bookkeeping: @TypeOf(air_bookkeeping_init) = air_bookkeeping_init,

const air_bookkeeping_init = if (std.debug.runtime_safety) @as(usize, 0) else {};

const MCValue = union(enum) {
    /// Control flow will not allow this value to be observed.
    unreach,
    /// The value is undefined.
    undef,
    /// A pointer-sized integer that fits in a register.
    /// If the type is a pointer, this is the pointer address in virtual address space.
    immediate: u64,
    /// The value is in a target-specific register.
    register: Register,
};

pub fn generate(
    bin_file: *link.File,
    src_loc: Module.SrcLoc,
    func_index: InternPool.Index,
    air: Air,
    liveness: Liveness,
    code: *std.ArrayList(u8),
    debug_output: DebugInfoOutput,
) CodeGenError!Result {
    _ = debug_output; // autofix
    const comp = bin_file.comp;
    const gpa = comp.gpa;
    const zcu = comp.module.?;
    // const ip = &zcu.intern_pool;
    // _ = ip; // autofix
    const func = zcu.funcInfo(func_index);
    const fn_owner_decl = zcu.declPtr(func.owner_decl);
    std.debug.assert(fn_owner_decl.has_tv);
    // const fn_type = fn_owner_decl.typeOf(zcu);
    // _ = fn_type; // autofix
    const namespace = zcu.namespacePtr(fn_owner_decl.src_namespace);
    // const target = &namespace.file_scope.mod.resolved_target.result;
    // _ = target; // autofix
    const mod = namespace.file_scope.mod;

    var function = Self{
        .gpa = gpa,
        .air = air,
        .mod = mod,
        .liveness = liveness,
        .bin_file = bin_file,
        .err_msg = null,
        .src_loc = src_loc,
    };

    try code.appendSlice(&std.mem.toBytes(Encoding.Instruction{
        .opcode = .{
            .class = .jmp,
            .rest = .{
                .jump = .{
                    .operation = .exit,
                    .source = .immediate,
                },
            },
        },
        .dst_reg = .r0,
        .src_reg = .r0,
        .offset = 0,
        .immediate = .{
            .imm = 0,
        },
    }));

    function.gen() catch |err| switch (err) {
        error.CodegenFail => return Result{ .fail = function.err_msg.? },
        error.OutOfRegisters => return Result{
            .fail = try ErrorMsg.create(gpa, src_loc, "CodeGen ran out of registers. This is a bug in the Zig compiler.", .{}),
        },
        else => |e| return e,
    };

    var mir = Mir{
        .instructions = function.mir_instructions.toOwnedSlice(),
        .extra = try function.mir_extra.toOwnedSlice(gpa),
    };
    defer mir.deinit(gpa);

    return .ok;
}

fn gen(self: *Self) !void {
    try self.genBody(self.air.getMainBody());
}

fn addInst(self: *Self, inst: Mir.Inst) error{OutOfMemory}!Mir.Inst.Index {
    const result_index: Mir.Inst.Index = @enumFromInt(self.mir_instructions.len);
    try self.mir_instructions.append(self.gpa, inst);
    return result_index;
}

pub fn addExtra(self: *Self, extra: []const u32) Allocator.Error!u32 {
    const extra_index: Mir.Inst.Index = @intCast(self.mir_extra.len);
    try self.mir_extra.append(self.gpa, extra);
    return extra_index;
}

fn genBody(self: *Self, body: []const Air.Inst.Index) InnerError!void {
    const zcu = self.bin_file.comp.module.?;
    const ip = &zcu.intern_pool;
    const air_tags = self.air.instructions.items(.tag);

    for (body) |inst| {
        if (self.liveness.isUnused(inst) and !self.air.mustLower(inst, ip)) continue;

        const old_air_bookkeeping = self.air_bookkeeping;
        switch (air_tags[@intFromEnum(inst)]) {
            // zig fmt: off
            .ptr_add => return self.fail("TODO: ptr_add", .{}),
            .ptr_sub => return self.fail("TODO: ptr_sub", .{}),

            .add => return self.fail("TODO: add", .{}),
            .sub => return self.fail("TODO: sub", .{}),

            .add_safe,
            .sub_safe,
            .mul_safe,
            => return self.fail("TODO implement safety_checked_instructions", .{}),

            .add_wrap        => return self.fail("TODO: add_wrap", .{}),
            .add_sat         => return self.fail("TODO: add_sat", .{}),
            .sub_wrap        => return self.fail("TODO: sub_wrap", .{}),
            .sub_sat         => return self.fail("TODO: sub_sat", .{}),
            .mul             => return self.fail("TODO: mul", .{}),
            .mul_wrap        => return self.fail("TODO: mul_wrap", .{}),
            .mul_sat         => return self.fail("TODO: mul_sat", .{}),
            .rem             => return self.fail("TODO: rem", .{}),
            .mod             => return self.fail("TODO: mod", .{}),
            .shl, .shl_exact => return self.fail("TODO: shl", .{}),
            .shl_sat         => return self.fail("TODO: shl_sat", .{}),
            .min             => return self.fail("TODO: min", .{}),
            .max             => return self.fail("TODO: max", .{}),
            .slice           => return self.fail("TODO: slice", .{}),

            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .floor,
            .ceil,
            .round,
            .trunc_float,
            .neg,
            => return self.fail("TODO: unary math", .{}),

            .add_with_overflow => return self.fail("TODO: add_with_overflow", .{}),
            .sub_with_overflow => return self.fail("TODO: sub_with_overflow", .{}),
            .mul_with_overflow => return self.fail("TODO: mul_with_overflow", .{}),
            .shl_with_overflow => return self.fail("TODO: shl_with_overflow", .{}),

            .div_float, .div_trunc, .div_floor, .div_exact => return self.fail("TODO: div", .{}),

            .cmp_lt  => return self.fail("TODO: cmp_lt", .{}),
            .cmp_lte => return self.fail("TODO: cmp_lte", .{}),
            .cmp_eq  => return self.fail("TODO: cmp_eq", .{}),
            .cmp_gte => return self.fail("TODO: cmp_gte", .{}),
            .cmp_gt  => return self.fail("TODO: cmp_gt", .{}),
            .cmp_neq => return self.fail("TODO: cmp_neq", .{}),

            .cmp_vector => return self.fail("TODO: cmp_vector", .{}),
            .cmp_lt_errors_len => return self.fail("TODO: cmp_lt_errors_len", .{}),

            .bool_and        => return self.fail("TODO: bool_and", .{}),
            .bool_or         => return self.fail("TODO: bool_or", .{}),
            .bit_and         => return self.fail("TODO: bit_and", .{}),
            .bit_or          => return self.fail("TODO: bit_or", .{}),
            .xor             => return self.fail("TODO: xor", .{}),
            .shr, .shr_exact => return self.fail("TODO: shr", .{}),

            .alloc           => return self.fail("TODO: alloc", .{}),
            .ret_ptr         => return self.fail("TODO: ret_ptr", .{}),
            .arg             => return self.fail("TODO: arg", .{}),
            .assembly        => return self.fail("TODO: assembly", .{}),
            .bitcast         => return self.fail("TODO: bitcast", .{}),
            .block           => return self.fail("TODO: block", .{}),
            .br              => return self.fail("TODO: br", .{}),
            .trap            => return self.fail("TODO: trap", .{}),
            .breakpoint      => return self.fail("TODO: breakpoint", .{}),
            .ret_addr        => return self.fail("TODO: ret_addr", .{}),
            .frame_addr      => return self.fail("TODO: frame_addr", .{}),
            .fence           => return self.fail("TODO: fence", .{}),
            .cond_br         => return self.fail("TODO: cond_br", .{}),
            .dbg_stmt        => return self.fail("TODO: dbg_stmt", .{}),
            .fptrunc         => return self.fail("TODO: fptrunc", .{}),
            .fpext           => return self.fail("TODO: fpext", .{}),
            .intcast         => return self.fail("TODO: intcast", .{}),
            .trunc           => return self.fail("TODO: trunc", .{}),
            .int_from_bool   => return self.fail("TODO: int_from_bool", .{}),
            .is_non_null     => return self.fail("TODO: is_non_null", .{}),
            .is_non_null_ptr => return self.fail("TODO: is_non_null_ptr", .{}),
            .is_null         => return self.fail("TODO: is_null", .{}),
            .is_null_ptr     => return self.fail("TODO: is_null_ptr", .{}),
            .is_non_err      => return self.fail("TODO: is_non_err", .{}),
            .is_non_err_ptr  => return self.fail("TODO: is_non_err_ptr", .{}),
            .is_err          => return self.fail("TODO: is_err", .{}),
            .is_err_ptr      => return self.fail("TODO: is_err_ptr", .{}),
            .load            => return self.fail("TODO: load", .{}),
            .loop            => return self.fail("TODO: loop", .{}),
            .not             => return self.fail("TODO: not", .{}),
            .int_from_ptr    => return self.fail("TODO: int_from_ptr", .{}),
            .ret             => return self.fail("TODO: ret", .{}),
            .ret_safe        => return self.fail("TODO: ret_safe", .{}),
            .ret_load        => return self.fail("TODO: ret_load", .{}),
            .store           => return self.fail("TODO: store", .{}),
            .store_safe      => return self.fail("TODO: store_safe", .{}),
            .struct_field_ptr=> return self.fail("TODO: struct_field_ptr", .{}),
            .struct_field_val=> return self.fail("TODO: struct_field_val", .{}),
            .array_to_slice  => return self.fail("TODO: array_to_slice", .{}),
            .float_from_int  => return self.fail("TODO: float_from_int", .{}),
            .int_from_float  => return self.fail("TODO: int_from_float", .{}),
            .cmpxchg_strong  => return self.fail("TODO: cmpxchg_strong", .{}),
            .cmpxchg_weak    => return self.fail("TODO: cmpxchg_weak", .{}),
            .atomic_rmw      => return self.fail("TODO: atomic_rmw", .{}),
            .atomic_load     => return self.fail("TODO: atomic_load", .{}),
            .memcpy          => return self.fail("TODO: memcpy", .{}),
            .memset          => return self.fail("TODO: memset", .{}),
            .memset_safe     => return self.fail("TODO: memset_safe", .{}),
            .set_union_tag   => return self.fail("TODO: set_union_tag", .{}),
            .get_union_tag   => return self.fail("TODO: get_union_tag", .{}),
            .clz             => return self.fail("TODO: clz", .{}),
            .ctz             => return self.fail("TODO: ctz", .{}),
            .popcount        => return self.fail("TODO: popcount", .{}),
            .abs             => return self.fail("TODO: abs", .{}),
            .byte_swap       => return self.fail("TODO: byte_swap", .{}),
            .bit_reverse     => return self.fail("TODO: bit_reverse", .{}),
            .tag_name        => return self.fail("TODO: tag_name", .{}),
            .error_name      => return self.fail("TODO: error_name", .{}),
            .splat           => return self.fail("TODO: splat", .{}),
            .select          => return self.fail("TODO: select", .{}),
            .shuffle         => return self.fail("TODO: shuffle", .{}),
            .reduce          => return self.fail("TODO: reduce", .{}),
            .aggregate_init  => return self.fail("TODO: aggregate_init", .{}),
            .union_init      => return self.fail("TODO: union_init", .{}),
            .prefetch        => return self.fail("TODO: prefetch", .{}),
            .mul_add         => return self.fail("TODO: mul_add", .{}),
            .addrspace_cast  => return self.fail("TODO: addrspace_cast", .{}),

            .@"try"          =>  return self.fail("TODO: try", .{}),
            .try_ptr         =>  return self.fail("TODO: try_ptr", .{}),

            .dbg_var_ptr,
            .dbg_var_val,
            => return self.fail("TODO: dbg_var_*", .{}),

            .dbg_inline_block => return self.fail("TODO: dbg_inline_block", .{}),

            .call              => return self.fail("TODO: call", .{}),
            .call_always_tail  => return self.fail("TODO: call_always_tail", .{}),
            .call_never_tail   => return self.fail("TODO: call_never_tail", .{}),
            .call_never_inline => return self.fail("TODO: call_never_inline", .{}),

            .atomic_store_unordered => return self.fail("TODO: atomic_store_unordered", .{}),
            .atomic_store_monotonic => return self.fail("TODO: atomic_store_monotonic", .{}),
            .atomic_store_release   => return self.fail("TODO: atomic_store_release", .{}),
            .atomic_store_seq_cst   => return self.fail("TODO: atomic_store_seq_cst", .{}),

            .struct_field_ptr_index_0 => return self.fail("TODO: struct_field_ptr_index_0", .{}),
            .struct_field_ptr_index_1 => return self.fail("TODO: struct_field_ptr_index_1", .{}),
            .struct_field_ptr_index_2 => return self.fail("TODO: struct_field_ptr_index_2", .{}),
            .struct_field_ptr_index_3 => return self.fail("TODO: struct_field_ptr_index_3", .{}),

            .field_parent_ptr => return self.fail("TODO: field_parent_ptr", .{}),

            .switch_br       => return self.fail("TODO: switch_br", .{}),
            .slice_ptr       => return self.fail("TODO: slice_ptr", .{}),
            .slice_len       => return self.fail("TODO: slice_len", .{}),

            .ptr_slice_len_ptr => return self.fail("TODO: ptr_slice_len_ptr", .{}),
            .ptr_slice_ptr_ptr => return self.fail("TODO: ptr_slice_ptr_ptr", .{}),

            .array_elem_val      => return self.fail("TODO: array_elem_val", .{}),
            .slice_elem_val      => return self.fail("TODO: slice_elem_val", .{}),
            .slice_elem_ptr      => return self.fail("TODO: slice_elem_ptr", .{}),
            .ptr_elem_val        => return self.fail("TODO: ptr_elem_val", .{}),
            .ptr_elem_ptr        => return self.fail("TODO: ptr_elem_ptr", .{}),

            .inferred_alloc, .inferred_alloc_comptime => unreachable,
            .unreach  => self.finishAirBookkeeping(),

            .optional_payload           => return self.fail("TODO: optional_payload", .{}),
            .optional_payload_ptr       => return self.fail("TODO: optional_payload_ptr", .{}),
            .optional_payload_ptr_set   => return self.fail("TODO: optional_payload_ptr_set", .{}),
            .unwrap_errunion_err        => return self.fail("TODO: unwrap_errunion_err", .{}),
            .unwrap_errunion_payload    => return self.fail("TODO: unwrap_errunion_payload", .{}),
            .unwrap_errunion_err_ptr    => return self.fail("TODO: unwrap_errunion_err_ptr", .{}),
            .unwrap_errunion_payload_ptr=> return self.fail("TODO: unwrap_errunion_payload_ptr", .{}),
            .errunion_payload_ptr_set   => return self.fail("TODO: errunion_payload_ptr_set", .{}),
            .err_return_trace           => return self.fail("TODO: err_return_trace", .{}),
            .set_err_return_trace       => return self.fail("TODO: set_err_return_trace", .{}),
            .save_err_return_trace_index=> return self.fail("TODO: save_err_return_trace_index", .{}),

            .wrap_optional         => return self.fail("TODO: wrap_optional", .{}),
            .wrap_errunion_payload => return self.fail("TODO: wrap_errunion_payload", .{}),
            .wrap_errunion_err     => return self.fail("TODO: wrap_errunion_err", .{}),

            .add_optimized,
            .sub_optimized,
            .mul_optimized,
            .div_float_optimized,
            .div_trunc_optimized,
            .div_floor_optimized,
            .div_exact_optimized,
            .rem_optimized,
            .mod_optimized,
            .neg_optimized,
            .cmp_lt_optimized,
            .cmp_lte_optimized,
            .cmp_eq_optimized,
            .cmp_gte_optimized,
            .cmp_gt_optimized,
            .cmp_neq_optimized,
            .cmp_vector_optimized,
            .reduce_optimized,
            .int_from_float_optimized,
            => return self.fail("TODO implement optimized float mode", .{}),

            .is_named_enum_value => return self.fail("TODO implement is_named_enum_value", .{}),
            .error_set_has_value => return self.fail("TODO implement error_set_has_value", .{}),
            .vector_store_elem => return self.fail("TODO implement vector_store_elem", .{}),

            .c_va_arg => return self.fail("TODO implement c_va_arg", .{}),
            .c_va_copy => return self.fail("TODO implement c_va_copy", .{}),
            .c_va_end => return self.fail("TODO implement c_va_end", .{}),
            .c_va_start => return self.fail("TODO implement c_va_start", .{}),

            .wasm_memory_size => unreachable,
            .wasm_memory_grow => unreachable,

            .work_item_id => unreachable,
            .work_group_size => unreachable,
            .work_group_id => unreachable,
            // zig fmt: on
        }

        std.debug.assert(!self.register_manager.lockedRegsExist());

        if (std.debug.runtime_safety) {
            if (self.air_bookkeeping < old_air_bookkeeping + 1) {
                std.debug.panic("in codegen.zig, handling of AIR instruction %{d} ('{}') did not do proper bookkeeping. Look for a missing call to finishAir.", .{ inst, air_tags[@intFromEnum(inst)] });
            }

            // { // check consistency of tracked registers
            //     var it = self.register_manager.free_registers.iterator(.{ .kind = .unset });
            //     while (it.next()) |index| {
            //         const tracked_inst = self.register_manager.registers[index];
            //         const tracking = self.getResolvedInstValue(tracked_inst);
            //         for (tracking.getRegs()) |reg| {
            //             if (RegisterManager.indexOfRegIntoTracked(reg).? == index) break;
            //         } else return self.fail(
            //             \\%{} takes up these regs: {any}, however those regs don't use it
            //         , .{ index, tracking.getRegs() });
            //     }
            // }
        }
    }
}

fn fail(self: *Self, comptime format: []const u8, args: anytype) InnerError {
    @setCold(true);
    std.debug.assert(self.err_msg == null);
    self.err_msg = try ErrorMsg.create(self.gpa, self.src_loc, format, args);
    return error.CodegenFail;
}

/// Called when there are no operands, and the instruction is always unreferenced.
fn finishAirBookkeeping(self: *Self) void {
    if (std.debug.runtime_safety) {
        self.air_bookkeeping += 1;
    }
}
