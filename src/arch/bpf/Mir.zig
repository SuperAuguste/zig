const Mir = @This();

const std = @import("std");
const Register = @import("bits.zig").Register;
const Size = @import("bits.zig").Instruction.Opcode.LoadStore.Size;

instructions: std.MultiArrayList(Inst).Slice,
extra: []const u32,

pub const Inst = struct {
    tag: Tag,
    data: Data,

    pub const Index = enum(u32) { _ };

    /// Tags ported from ISA.
    ///
    /// Took some liberties and renamed `alu` to `alu32`
    /// and `jmp` to `jmp64` for clarity.
    pub const Tag = enum(u8) {
        // ALU
        // imm32 and src_reg indicate the operand source.

        alu32_add_imm32,
        alu32_add_src_reg,
        alu64_add_imm32,
        alu64_add_src_reg,
        alu32_sub_imm32,
        alu32_sub_src_reg,
        alu64_sub_imm32,
        alu64_sub_src_reg,
        alu32_mul_imm32,
        alu32_mul_src_reg,
        alu64_mul_imm32,
        alu64_mul_src_reg,
        alu32_div_imm32,
        alu32_div_src_reg,
        alu64_div_imm32,
        alu64_div_src_reg,
        alu32_sdiv_imm32,
        alu32_sdiv_src_reg,
        alu64_sdiv_imm32,
        alu64_sdiv_src_reg,
        alu32_or_imm32,
        alu32_or_src_reg,
        alu64_or_imm32,
        alu64_or_src_reg,
        alu32_and_imm32,
        alu32_and_src_reg,
        alu64_and_imm32,
        alu64_and_src_reg,
        alu32_lsh_imm32,
        alu32_lsh_src_reg,
        alu64_lsh_imm32,
        alu64_lsh_src_reg,
        alu32_rsh_imm32,
        alu32_rsh_src_reg,
        alu64_rsh_imm32,
        alu64_rsh_src_reg,
        alu32_neg_imm32,
        alu32_neg_src_reg,
        alu64_neg_imm32,
        alu64_neg_src_reg,
        alu32_mod_imm32,
        alu32_mod_src_reg,
        alu64_mod_imm32,
        alu64_mod_src_reg,
        alu32_smod_imm32,
        alu32_smod_src_reg,
        alu64_smod_imm32,
        alu64_smod_src_reg,
        alu32_xor_imm32,
        alu32_xor_src_reg,
        alu64_xor_imm32,
        alu64_xor_src_reg,
        alu32_mov_imm32,
        alu32_mov_src_reg,
        alu64_mov_imm32,
        alu64_mov_src_reg,
        alu32_movsx8_imm32,
        alu32_movsx8_src_reg,
        alu64_movsx8_imm32,
        alu64_movsx8_src_reg,
        alu32_movsx16_imm32,
        alu32_movsx16_src_reg,
        alu64_movsx16_imm32,
        alu64_movsx16_src_reg,
        alu32_movsx32_imm32,
        alu32_movsx32_src_reg,
        alu64_movsx32_imm32,
        alu64_movsx32_src_reg,
        alu32_arsh_imm32,
        alu32_arsh_src_reg,
        alu64_arsh_imm32,
        alu64_arsh_src_reg,

        /// `ByteSwapWidth`
        to_le,
        /// `ByteSwapWidth`
        to_be,
        /// Unconditional byteswap
        /// `ByteSwapWidth`
        byteswap,

        // Jump

        ja_offset,
        ja_imm32,
        call_static_id,
        call_imm32,
        call_btf_id,
        exit,

        // imm32 and src_reg indicate the rhs source.
        // S in name indicates signed comparison; otherwise unsigned
        jmp32_jeq_imm32,
        jmp32_jeq_src_reg,
        jmp64_jeq_imm32,
        jmp64_jeq_src_reg,
        jmp32_jgt_imm32,
        jmp32_jgt_src_reg,
        jmp64_jgt_imm32,
        jmp64_jgt_src_reg,
        jmp32_jge_imm32,
        jmp32_jge_src_reg,
        jmp64_jge_imm32,
        jmp64_jge_src_reg,
        jmp32_jset_imm32,
        jmp32_jset_src_reg,
        jmp64_jset_imm32,
        jmp64_jset_src_reg,
        jmp32_jne_imm32,
        jmp32_jne_src_reg,
        jmp64_jne_imm32,
        jmp64_jne_src_reg,
        jmp32_jsgt_imm32,
        jmp32_jsgt_src_reg,
        jmp64_jsgt_imm32,
        jmp64_jsgt_src_reg,
        jmp32_jsge_imm32,
        jmp32_jsge_src_reg,
        jmp64_jsge_imm32,
        jmp64_jsge_src_reg,
        jmp32_jlt_imm32,
        jmp32_jlt_src_reg,
        jmp64_jlt_imm32,
        jmp64_jlt_src_reg,
        jmp32_jle_imm32,
        jmp32_jle_src_reg,
        jmp64_jle_imm32,
        jmp64_jle_src_reg,
        jmp32_jslt_imm32,
        jmp32_jslt_src_reg,
        jmp64_jslt_imm32,
        jmp64_jslt_src_reg,
        jmp32_jsle_imm32,
        jmp32_jsle_src_reg,
        jmp64_jsle_imm32,
        jmp64_jsle_src_reg,

        // Load / store
        /// `MovWithOffset` where
        /// `(dst + offset).* = src`
        store_from_register,
        /// `StoreFromImmediate` in `extra`
        store_from_immediate,
        /// `MovWithOffset` where
        /// `dst = (src + offset).*`
        load,

        atomic_add,
        atomic_add_fetch,
        atomic_or,
        atomic_or_fetch,
        atomic_and,
        atomic_and_fetch,
        atomic_xor,
        atomic_xor_fetch,
        xchg,
        cmpxchg,

        // TODO: add 64-bit immediate instructions including map/platform var utils
    };

    pub const Data = union {
        pub const DstSrc = struct {
            dst_reg: Register,
            src_reg: Register,
        };

        /// In extra.
        pub const DstImmediate = struct {
            immediate: u32,
            rest: packed struct(u32) {
                dst_reg: Register,

                padding: u28 = 0,
            },
        };

        pub const ByteSwap = struct {
            pub const Width = enum(u2) {
                @"16",
                @"32",
                @"64",
            };

            dst_reg: Register,
            src_reg: Register,
            width: Width,
        };

        pub const MovWithOffset = packed struct(u32) {
            dst_reg: Register,
            src_reg: Register,
            offset: i16,
            size: Size,

            padding: u6 = 0,
        };

        /// In extra.
        pub const StoreFromImmediate = struct {
            immediate: u32,
            rest: packed struct(u32) {
                dst_reg: Register,
                offset: i16,
                size: Size,

                padding: u10 = 0,
            },
        };

        none: void,
        dst_src: DstSrc,
        byte_swap: ByteSwap,
        mov_with_offset: MovWithOffset,
        extra: u32,
    };

    comptime {
        if (@import("builtin").mode != .Debug) {
            std.debug.assert(@bitSizeOf(Data) == 32);
        }
    }
};

pub fn getExtra(self: *Mir, comptime T: type, extra: u32) T {
    var result: T = undefined;

    const fields = std.meta.fields(T);
    inline for (fields, 0..) |field, i| {
        @field(result, field.name) = @bitCast(self.extra[extra + i]);
    }
    return result;
}

pub fn deinit(self: *Mir, gpa: std.mem.Allocator) void {
    self.instructions.deinit(gpa);
    gpa.free(self.extra);
    self.* = undefined;
}
