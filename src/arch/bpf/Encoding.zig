const Register = @import("bits.zig").Register;

/// Unused fields must be zeroed.
pub const Instruction = packed struct(u64) {
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
                immediate_or_to_le,
                /// use `src_reg` register as source operand
                /// if `operation` is `end`, this becomes a
                /// `bpf_to_be`.
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
                /// use 32-bit immediate as source operand
                immediate,
                /// use `src_reg` register as source operand
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
                imm,
                /// legacy BPF packet access (absolute)
                abs,
                /// legacy BPF packet access (indirect)
                ind,
                /// regular load and store operations
                mem,
                /// atomic operations
                atomic,
            };

            /// Value of `immediate` when `mode` is `atomic`. Describes an atomic operation.
            ///
            /// If `_fetch`, then the operation also overwrites src_reg with thevalue that was
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
    offset: i16,
    immediate: packed union {
        imm: u32,
        atomic_op: Opcode.LoadStore.AtomicOperation,
    },
};
