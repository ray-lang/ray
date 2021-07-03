bitflags::bitflags! {
    pub(super) struct Attribute: u64 {
        const None = 0;
        const ZExt = 1 << 0;
        const SExt = 1 << 1;
        const NoReturn = 1 << 2;
        const InReg = 1 << 3;
        const StructRet = 1 << 4;
        const NoUnwind = 1 << 5;
        const NoAlias = 1 << 6;
        const ByVal = 1 << 7;
        const Nest = 1 << 8;
        const ReadNone = 1 << 9;
        const ReadOnly = 1 << 10;
        const NoInline = 1 << 11;
        const AlwaysInline = 1 << 12;
        const OptimizeForSize = 1 << 13;
        const StackProtect = 1 << 14;
        const StackProtectReq = 1 << 15;
        const Alignment = 31 << 16;
        const NoCapture = 1 << 21;
        const NoRedZone = 1 << 22;
        const NoImplicitFloat = 1 << 23;
        const Naked = 1 << 24;
        const InlineHint = 1 << 25;
        const StackAlignment = 7 << 26;
        const ReturnsTwice = 1 << 29;
        const UWTable = 1 << 30;
        const NonLazyBind = 1 << 31;
        const SanitizeAddress = 1 << 32;
        const MinSize = 1 << 33;
        const NoDuplicate = 1 << 34;
        const StackProtectStrong = 1 << 35;
        const SanitizeThread = 1 << 36;
        const SanitizeMemory = 1 << 37;
        const NoBuiltin = 1 << 38;
        const Returned = 1 << 39;
        const Cold = 1 << 40;
        const Builtin = 1 << 41;
        const OptimizeNone = 1 << 42;
        const InAlloca = 1 << 43;
        const NonNull = 1 << 44;
        const JumpTable = 1 << 45;
        const Convergent = 1 << 46;
        const SafeStack = 1 << 47;
        const NoRecurse = 1 << 48;
        const InaccessibleMemOnly = 1 << 49;
        const InaccessibleMemOrArgMemOnly = 1 << 50;
        const SwiftSelf = 1 << 51;
        const SwiftError = 1 << 52;
        const WriteOnly = 1 << 53;
        const Speculatable = 1 << 54;
        const StrictFP = 1 << 55;
        const SanitizeHWAddress = 1 << 56;
        const NoCfCheck = 1 << 57;
        const OptForFuzzing = 1 << 58;
        const ShadowCallStack = 1 << 59;
        const SpeculativeLoadHardening = 1 << 60;
        const ImmArg = 1 << 61;
        const WillReturn = 1 << 62;
        const NoFree = 1 << 63;
    }
}