const std = @import("std");
const Mir = @import("Mir.zig");
const Module = @import("../../Module.zig");
const link = @import("../../link.zig");
const ErrorMsg = Module.ErrorMsg;
const bits = @import("bits.zig");
const Instruction = bits.Instruction;

const Emit = @This();

const InnerError = error{
    OutOfMemory,
    EmitFail,
};

mir: Mir,
bin_file: *link.File,
// target: *const std.Target,
err_msg: ?*ErrorMsg = null,
src_loc: Module.SrcLoc,
code: *std.ArrayList(u8),

pub fn emitMir(emit: *Emit) InnerError!void {
    const tags = emit.mir.instructions.items(.tag);
    const datas = emit.mir.instructions.items(.data);

    for (tags, datas) |tag, data| {
        switch (tag) {
            .store_from_register => {
                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .stx,
                        .rest = .{
                            .load_store = .{
                                .mode = .mem,
                                .size = data.mov_with_offset.size,
                            },
                        },
                    },
                    .dst_reg = data.mov_with_offset.dst_reg,
                    .src_reg = data.mov_with_offset.src_reg,
                    .offset = data.mov_with_offset.offset,
                    .immediate = .{
                        .imm = 0,
                    },
                });
            },
            .store_from_immediate => {
                const sfi = emit.mir.getExtra(Mir.Inst.Data.StoreFromImmediate, data.extra);

                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .st,
                        .rest = .{
                            .load_store = .{
                                .mode = .mem,
                                .size = sfi.rest.size,
                            },
                        },
                    },
                    .dst_reg = sfi.rest.dst_reg,
                    .src_reg = .r0,
                    .offset = sfi.rest.offset,
                    .immediate = .{
                        .imm = sfi.immediate,
                    },
                });
            },
            else => return emit.fail("mir lowering not implemented: {s}", .{@tagName(tag)}),
        }
    }
}

fn emitInstruction(emit: *Emit, instruction: Instruction) InnerError!void {
    try emit.code.appendSlice(&std.mem.toBytes(instruction));
}

fn fail(emit: *Emit, comptime format: []const u8, args: anytype) InnerError {
    @setCold(true);
    std.debug.assert(emit.err_msg == null);
    const comp = emit.bin_file.comp;
    const gpa = comp.gpa;
    emit.err_msg = try ErrorMsg.create(gpa, emit.src_loc, format, args);
    return error.EmitFail;
}
