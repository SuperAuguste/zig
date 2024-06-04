pub const Register = enum(u4) {
    // zig fmt: off
    r0, // return value from function calls, and exit value for eBPF programs
    r1, r2, r3, r4, r5, // arguments for function calls
    r6, r7, r8, r9, // callee saved registers
    /// read-only frame pointer
    r10,
    // r0-r5 are scratch registers; all registers 64-bit
    // zig fmt: on

    pub fn id(reg: Register) u4 {
        return @intFromEnum(reg);
    }
};

/// Unused fields must be zeroed.
/// https://docs.kernel.org/bpf/standardization/instruction-set.html
/// https://gcc.gnu.org/wiki/BPFBackEnd
pub const Instruction = packed struct(u64) {
    pub const Immediate32 = u32;
    pub const Offset = i16;

    pub const Class = enum(u3) {
        /// non-standard load
        ld,
        /// load into register
        ldx,
        /// store from immediate
        st,
        /// store from register
        stx,
        /// 32-bit alu
        alu,
        /// 64-bit jump
        jmp,
        /// 32-bit jump
        jmp32,
        /// 64-bit jump
        alu64,
    };

    pub const Opcode = packed struct(u8) {
        // Technically Alu and Jmp should share one,
        // encoding but for simplicity's sake, I've split
        // them here.

        pub const Alu = packed struct(u5) {
            pub const Source = enum(u1) {
                /// use 32-bit immediate as source operand
                /// if `operation` is `end`, this becomes a
                /// `bpf_to_le`.
                ///
                /// also known as `k`.
                immediate_or_to_le,
                /// use `src_reg` register as source operand
                /// if `operation` is `end`, this becomes a
                /// `bpf_to_be`.
                ///
                /// also known as `x`.
                src_reg_or_to_be,
            };

            pub const Operation = enum(u4) {
                add,
                sub,
                mul,
                div,
                @"or",
                @"and",
                lsh,
                rsh,
                neg,
                mod,
                xor,
                mov,
                /// sign extending shift right
                arsh,
                /// byte swap operations
                end,
            };

            source: Source,
            operation: Operation,
        };

        pub const Jump = packed struct(u5) {
            pub const Source = enum(u1) {
                /// use 32-bit immediate as source operand.
                /// also known as `k`.
                immediate,
                /// use `src_reg` register as source operand.
                /// also known as `x`.
                src_reg,
            };

            /// Comparison order is dst OP src so
            /// `jlt` is `dst < src` for example.
            pub const Operation = enum(u4) {
                /// PC += off.
                /// jmp32 not supported.
                ja,
                jeq,
                jgt,
                jge,
                jset,
                jne,
                jsgt,
                jsge,
                call,
                /// function / program return
                /// need to store the return value into register r0 before this
                /// jmp32 not supported.
                exit,
                jlt,
                jle,
                jslt,
                jsle,
            };

            source: Source,
            operation: Operation,
        };

        pub const LoadStore = packed struct(u5) {
            pub const Size = enum(u2) {
                /// 4 bytes (u32)
                w,
                /// 2 bytes (u16)
                hw,
                /// 1 byte (u8)
                b,
                /// 8 bytes (u64)
                dw,
            };

            pub const Mode = enum(u3) {
                /// 64-bit immediates
                imm = 0,
                /// legacy BPF packet access (absolute)
                abs = 1,
                /// legacy BPF packet access (indirect)
                ind = 2,
                /// regular load and store operations
                mem = 3,
                /// sign-extension load operations
                memsx = 4,
                /// atomic operations
                atomic = 6,
            };

            /// Value of `immediate` when `mode` is `atomic`. Describes an atomic operation.
            ///
            /// If `_fetch`, then the operation also overwrites src_reg with the value that was
            /// in memory before it was modified.
            pub const AtomicOperation = enum(u32) {
                add = 0x00,
                add_fetch = 0x01,
                @"or" = 0x40,
                or_fetch = 0x41,
                @"and" = 0x50,
                and_fetch = 0x51,
                xor = 0xa0,
                xor_fetch = 0xa1,
                xchg = 0xe1,
                cmpxchg = 0xf1,
            };

            size: Size,
            mode: Mode,
        };

        class: Class,
        rest: packed union {
            alu: Alu,
            jump: Jump,
            load_store: LoadStore,
        },
    };

    opcode: Opcode,
    dst_reg: Register,
    src_reg: Register,
    offset: Offset,
    immediate: packed union {
        imm: Immediate32,
        atomic_op: Opcode.LoadStore.AtomicOperation,
    },
};
