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
            .exit => {
                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .jmp,
                        .rest = .{
                            .jump = .{
                                .source = .immediate,
                                .operation = .exit,
                            },
                        },
                    },
                    .dst_reg = .r0,
                    .src_reg = .r0,
                    .offset = 0,
                    .immediate = .{
                        .imm = 0,
                    },
                });
            },
            inline .alu64_add_imm32,
            .alu64_sub_imm32,
            .alu64_mul_imm32,
            .alu64_div_imm32,
            .alu64_sdiv_imm32,
            .alu64_or_imm32,
            .alu64_and_imm32,
            .alu64_lsh_imm32,
            .alu64_rsh_imm32,
            .alu64_mod_imm32,
            .alu64_smod_imm32,
            .alu64_xor_imm32,
            .alu64_mov_imm32,
            .alu64_movsx8_imm32,
            .alu64_movsx16_imm32,
            .alu64_movsx32_imm32,
            .alu64_arsh_imm32,
            => |alu64_imm_tag| {
                const di = emit.mir.getExtra(Mir.Inst.Data.DstImmediate, data.extra);

                const operation =
                    comptime switch (alu64_imm_tag) {
                    .alu64_sdiv_imm32 => .div,
                    .alu64_smod_imm32 => .mod,
                    .alu64_movsx8_imm32, .alu64_movsx16_imm32, .alu64_movsx32_imm32 => .mov,
                    else => blk: {
                        var tag_iterator = std.mem.split(u8, @tagName(alu64_imm_tag), "_");
                        _ = tag_iterator.next().?;
                        break :blk @field(Instruction.Opcode.Alu.Operation, tag_iterator.next().?);
                    },
                };

                const offset: i16 =
                    comptime switch (alu64_imm_tag) {
                    .alu64_sdiv_imm32, .alu64_smod_imm32 => 1,
                    .alu64_movsx8_imm32 => 8,
                    .alu64_movsx16_imm32 => 16,
                    .alu64_movsx32_imm32 => 32,
                    else => 0,
                };

                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .alu64,
                        .rest = .{
                            .alu = .{
                                .source = .immediate_or_to_le,
                                .operation = operation,
                            },
                        },
                    },
                    .dst_reg = di.rest.dst_reg,
                    .src_reg = .r0,
                    .offset = offset,
                    .immediate = .{
                        .imm = di.immediate,
                    },
                });
            },
            inline .alu64_add_src_reg,
            .alu64_sub_src_reg,
            .alu64_mul_src_reg,
            .alu64_div_src_reg,
            .alu64_sdiv_src_reg,
            .alu64_or_src_reg,
            .alu64_and_src_reg,
            .alu64_lsh_src_reg,
            .alu64_rsh_src_reg,
            .alu64_mod_src_reg,
            .alu64_smod_src_reg,
            .alu64_xor_src_reg,
            .alu64_mov_src_reg,
            .alu64_movsx8_src_reg,
            .alu64_movsx16_src_reg,
            .alu64_movsx32_src_reg,
            .alu64_arsh_src_reg,
            => |alu64_reg_tag| {
                const ds = data.dst_src;

                const operation =
                    comptime switch (alu64_reg_tag) {
                    .alu64_sdiv_src_reg => .div,
                    .alu64_smod_src_reg => .mod,
                    .alu64_movsx8_src_reg, .alu64_movsx16_src_reg, .alu64_movsx32_src_reg => .mov,
                    else => blk: {
                        var tag_iterator = std.mem.split(u8, @tagName(alu64_reg_tag), "_");
                        _ = tag_iterator.next().?;
                        break :blk @field(Instruction.Opcode.Alu.Operation, tag_iterator.next().?);
                    },
                };

                const offset: i16 =
                    comptime switch (alu64_reg_tag) {
                    .alu64_sdiv_src_reg, .alu64_smod_src_reg => 1,
                    .alu64_movsx8_src_reg => 8,
                    .alu64_movsx16_src_reg => 16,
                    .alu64_movsx32_src_reg => 32,
                    else => 0,
                };

                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .alu64,
                        .rest = .{
                            .alu = .{
                                .source = .src_reg_or_to_be,
                                .operation = operation,
                            },
                        },
                    },
                    .dst_reg = ds.dst_reg,
                    .src_reg = ds.src_reg,
                    .offset = offset,
                    .immediate = .{
                        .imm = 0,
                    },
                });
            },
            .ja => {
                if (data.immediate <= std.math.maxInt(u16)) {
                    try emit.emitInstruction(.{
                        .opcode = .{
                            .class = .jmp,
                            .rest = .{
                                .jump = .{
                                    .source = .immediate,
                                    .operation = .ja,
                                },
                            },
                        },
                        .dst_reg = .r0,
                        .src_reg = .r0,
                        .offset = @intCast(data.immediate),
                        .immediate = .{
                            .imm = 0,
                        },
                    });
                } else {
                    try emit.emitInstruction(.{
                        .opcode = .{
                            .class = .jmp32,
                            .rest = .{
                                .jump = .{
                                    .source = .immediate,
                                    .operation = .ja,
                                },
                            },
                        },
                        .dst_reg = .r0,
                        .src_reg = .r0,
                        .offset = 0,
                        .immediate = .{
                            .imm = data.immediate,
                        },
                    });
                }
            },
            inline .jmp64_jeq_imm32,
            .jmp64_jgt_imm32,
            .jmp64_jge_imm32,
            .jmp64_jset_imm32,
            .jmp64_jne_imm32,
            .jmp64_jsgt_imm32,
            .jmp64_jsge_imm32,
            .jmp64_jlt_imm32,
            .jmp64_jle_imm32,
            .jmp64_jslt_imm32,
            .jmp64_jsle_imm32,
            => |jmp64_imm_tag| {
                const dio = emit.mir.getExtra(Mir.Inst.Data.DstImmediateOffset, data.extra);

                const operation = comptime blk: {
                    var tag_iterator = std.mem.split(u8, @tagName(jmp64_imm_tag), "_");
                    _ = tag_iterator.next().?;
                    break :blk @field(Instruction.Opcode.Jump.Operation, tag_iterator.next().?);
                };

                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .jmp,
                        .rest = .{
                            .jump = .{
                                .source = .immediate,
                                .operation = operation,
                            },
                        },
                    },
                    .dst_reg = dio.rest.dst_reg,
                    .src_reg = .r0,
                    .offset = dio.rest.offset,
                    .immediate = .{
                        .imm = dio.immediate,
                    },
                });
            },
            inline .jmp64_jeq_src_reg,
            .jmp64_jgt_src_reg,
            .jmp64_jge_src_reg,
            .jmp64_jset_src_reg,
            .jmp64_jne_src_reg,
            .jmp64_jsgt_src_reg,
            .jmp64_jsge_src_reg,
            .jmp64_jlt_src_reg,
            .jmp64_jle_src_reg,
            .jmp64_jslt_src_reg,
            .jmp64_jsle_src_reg,
            => |jmp64_imm_tag| {
                const operation = comptime blk: {
                    var tag_iterator = std.mem.split(u8, @tagName(jmp64_imm_tag), "_");
                    _ = tag_iterator.next().?;
                    break :blk @field(Instruction.Opcode.Jump.Operation, tag_iterator.next().?);
                };

                try emit.emitInstruction(.{
                    .opcode = .{
                        .class = .jmp,
                        .rest = .{
                            .jump = .{
                                .source = .src_reg,
                                .operation = operation,
                            },
                        },
                    },
                    .dst_reg = data.dst_src_offset.dst_reg,
                    .src_reg = data.dst_src_offset.src_reg,
                    .offset = data.dst_src_offset.offset,
                    .immediate = .{
                        .imm = 0,
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
