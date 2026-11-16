//! The architecture of the build process, which the workload install state is
//! keyed by (`metadata/workloads/{architecture}/{band}/InstallState`,
//! `WorkloadInstallType.GetInstallStateFolder`, which names the folder with
//! `RuntimeInformation.ProcessArchitecture.ToString()`).
//!
//! A build runs in the process of the `dotnet` muxer it was started with, so
//! the architecture is the muxer executable's, which its header names: an ELF
//! file's `e_machine`, a Mach-O file's `cputype`, a PE file's `Machine`. That
//! is what the process runs as even under emulation (an x64 muxer on an arm64
//! Mac runs under Rosetta, and reports `X64`), and it is why the host's own
//! architecture is no substitute. [`ProcessArchitecture::of_executable`] reads
//! it from the first [`EXECUTABLE_HEADER_BYTES`] bytes of the file, and says
//! nothing where the header does not settle it:
//!
//! * a universal (fat) Mach-O file whose slices are of different
//!   architectures: which one runs depends on the host and on the launching
//!   process (a process under Rosetta can prefer the x86-64 slice), neither of
//!   which the file says;
//! * a 32-bit ARM ELF file: `Arm` and `Armv6` builds of .NET share
//!   `EM_ARM`, and only the file's attributes section, past the header, tells
//!   them apart;
//! * anything else outside the table below: a script, a format or machine
//!   .NET does not run on, a header cut short or past the bytes read.

/// `System.Runtime.InteropServices.Architecture`, whose member names
/// [`Self::name`] spells as `ToString()` does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ProcessArchitecture {
    X86,
    X64,
    Arm,
    Arm64,
    Wasm,
    S390x,
    LoongArch64,
    Armv6,
    Ppc64le,
    RiscV64,
}

/// How many leading bytes of an executable [`ProcessArchitecture::of_executable`]
/// reads: a page, which holds the ELF and thin Mach-O headers many times over,
/// a fat Mach-O header's architecture table, and the PE header wherever the
/// linker put it in practice (it follows the DOS stub, a few hundred bytes in).
pub const EXECUTABLE_HEADER_BYTES: u64 = 4096;

impl ProcessArchitecture {
    /// Every member, in declaration order.
    pub const ALL: [Self; 10] = [
        Self::X86,
        Self::X64,
        Self::Arm,
        Self::Arm64,
        Self::Wasm,
        Self::S390x,
        Self::LoongArch64,
        Self::Armv6,
        Self::Ppc64le,
        Self::RiscV64,
    ];

    /// The member's name, as `Architecture.ToString()` spells it: the
    /// install-state folder's name.
    pub fn name(self) -> &'static str {
        match self {
            Self::X86 => "X86",
            Self::X64 => "X64",
            Self::Arm => "Arm",
            Self::Arm64 => "Arm64",
            Self::Wasm => "Wasm",
            Self::S390x => "S390x",
            Self::LoongArch64 => "LoongArch64",
            Self::Armv6 => "Armv6",
            Self::Ppc64le => "Ppc64le",
            Self::RiscV64 => "RiscV64",
        }
    }

    /// The member [`Self::name`] spells as `name`, exactly.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|arch| arch.name() == name)
    }

    /// The architecture a process running the executable whose leading bytes
    /// are `header` runs as, where the header settles it (see the module
    /// docs). `header` may be the whole file or any prefix of it at least as
    /// long as the header; bytes past the header are not looked at.
    pub fn of_executable(header: &[u8]) -> Option<Self> {
        match header.get(..4)? {
            b"\x7fELF" => elf(header),
            [0xfe, 0xed, 0xfa, 0xce | 0xcf] | [0xce | 0xcf, 0xfa, 0xed, 0xfe] => thin_macho(header),
            [0xca, 0xfe, 0xba, 0xbe | 0xbf] => fat_macho(header),
            [b'M', b'Z', ..] => pe(header),
            _ => None,
        }
    }

    /// The architecture of a Mach-O `cputype`, whose `CPU_ARCH_ABI64` bit
    /// (`0x0100_0000`) marks the 64-bit ABIs.
    fn of_macho_cputype(cputype: u32) -> Option<Self> {
        match cputype {
            CPU_TYPE_X86 => Some(Self::X86),
            CPU_TYPE_X86_64 => Some(Self::X64),
            CPU_TYPE_ARM64 => Some(Self::Arm64),
            _ => None,
        }
    }
}

const CPU_ARCH_ABI64: u32 = 0x0100_0000;
const CPU_TYPE_X86: u32 = 7;
const CPU_TYPE_X86_64: u32 = CPU_TYPE_X86 | CPU_ARCH_ABI64;
const CPU_TYPE_ARM64: u32 = 12 | CPU_ARCH_ABI64;

/// The `N` bytes at `at`, where `bytes` holds them.
fn field<const N: usize>(bytes: &[u8], at: usize) -> Option<[u8; N]> {
    bytes.get(at..at.checked_add(N)?)?.try_into().ok()
}

fn u16_at(bytes: &[u8], at: usize, big_endian: bool) -> Option<u16> {
    let raw = field(bytes, at)?;
    Some(if big_endian {
        u16::from_be_bytes(raw)
    } else {
        u16::from_le_bytes(raw)
    })
}

fn u32_at(bytes: &[u8], at: usize, big_endian: bool) -> Option<u32> {
    let raw = field(bytes, at)?;
    Some(if big_endian {
        u32::from_be_bytes(raw)
    } else {
        u32::from_le_bytes(raw)
    })
}

/// An ELF header: `EI_CLASS` (byte 4) says 32 or 64 bits, `EI_DATA` (byte 5)
/// the byte order, and `e_machine` (bytes 18 and 19) the machine. Each
/// machine is taken only with the width and byte order .NET builds it with,
/// so an x32 or big-endian AArch64 file reads as nothing.
fn elf(header: &[u8]) -> Option<ProcessArchitecture> {
    use ProcessArchitecture::*;
    let wide = match header.get(4)? {
        1 => false,
        2 => true,
        _ => return None,
    };
    let big_endian = match header.get(5)? {
        1 => false,
        2 => true,
        _ => return None,
    };
    const EM_386: u16 = 3;
    const EM_PPC64: u16 = 21;
    const EM_S390: u16 = 22;
    const EM_X86_64: u16 = 62;
    const EM_AARCH64: u16 = 183;
    const EM_RISCV: u16 = 243;
    const EM_LOONGARCH: u16 = 258;
    match (u16_at(header, 18, big_endian)?, wide, big_endian) {
        (EM_386, false, false) => Some(X86),
        (EM_X86_64, true, false) => Some(X64),
        (EM_AARCH64, true, false) => Some(Arm64),
        (EM_S390, true, true) => Some(S390x),
        (EM_PPC64, true, false) => Some(Ppc64le),
        (EM_LOONGARCH, true, false) => Some(LoongArch64),
        (EM_RISCV, true, false) => Some(RiscV64),
        _ => None,
    }
}

/// A thin Mach-O header: the magic (`MH_MAGIC`, `MH_MAGIC_64`, or either
/// byte-swapped) gives the width and byte order, and `cputype` (bytes 4 to 7)
/// the machine. Every architecture .NET runs on macOS is little-endian, and a
/// header must be as wide as its `cputype`'s ABI.
fn thin_macho(header: &[u8]) -> Option<ProcessArchitecture> {
    let big_endian = header[0] == 0xfe;
    let wide = u32_at(header, 0, big_endian)? == 0xfeed_facf;
    let cputype = u32_at(header, 4, big_endian)?;
    if big_endian || wide != (cputype & CPU_ARCH_ABI64 != 0) {
        return None;
    }
    ProcessArchitecture::of_macho_cputype(cputype)
}

/// A universal Mach-O header (`FAT_MAGIC`, or `FAT_MAGIC_64` for 64-bit
/// offsets), always big-endian: `nfat_arch` (bytes 4 to 7), then that many
/// `fat_arch` entries of 20 bytes (32 for `FAT_MAGIC_64`), each starting with
/// its slice's `cputype`. The loader picks a slice by the host and the
/// launching process, so the file settles the architecture only where every
/// slice has the same one. Twenty slices or more is a Java class file, whose
/// major version shares the field, as `file(1)` reads it.
fn fat_macho(header: &[u8]) -> Option<ProcessArchitecture> {
    let entry = if header[3] == 0xbf { 32 } else { 20 };
    let slices = usize::try_from(u32_at(header, 4, true)?).ok()?;
    if !(1..20).contains(&slices) {
        return None;
    }
    let mut architecture = None;
    for slice in 0..slices {
        let cputype = u32_at(header, 8 + slice * entry, true)?;
        let this = ProcessArchitecture::of_macho_cputype(cputype)?;
        if architecture.is_some_and(|seen| seen != this) {
            return None;
        }
        architecture = Some(this);
    }
    architecture
}

/// A PE file: the DOS header's `e_lfanew` (bytes `0x3c` to `0x3f`) locates
/// the `PE\0\0` signature, which the COFF header's `Machine` follows, and the
/// optional header's magic (24 bytes past the signature) says PE32 or PE32+.
/// Each machine is taken only with the optional header of its width.
fn pe(header: &[u8]) -> Option<ProcessArchitecture> {
    use ProcessArchitecture::*;
    const IMAGE_FILE_MACHINE_I386: u16 = 0x014c;
    const IMAGE_FILE_MACHINE_ARMNT: u16 = 0x01c4;
    const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;
    const IMAGE_FILE_MACHINE_ARM64: u16 = 0xaa64;
    const PE32: u16 = 0x10b;
    const PE32_PLUS: u16 = 0x20b;
    let signature = usize::try_from(u32_at(header, 0x3c, false)?).ok()?;
    if field::<4>(header, signature)? != *b"PE\0\0" {
        return None;
    }
    let machine = u16_at(header, signature.checked_add(4)?, false)?;
    let optional_magic = u16_at(header, signature.checked_add(24)?, false)?;
    match (machine, optional_magic) {
        (IMAGE_FILE_MACHINE_I386, PE32) => Some(X86),
        (IMAGE_FILE_MACHINE_ARMNT, PE32) => Some(Arm),
        (IMAGE_FILE_MACHINE_AMD64, PE32_PLUS) => Some(X64),
        (IMAGE_FILE_MACHINE_ARM64, PE32_PLUS) => Some(Arm64),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::ProcessArchitecture::{self, *};
    use proptest::prelude::*;

    // The specification each format's generator is graded against, written
    // from the formats' own documents rather than from the parser.

    /// ELF (`e_machine`, `EI_CLASS`, `EI_DATA`) to the architecture .NET
    /// builds for it.
    fn elf_spec(machine: u16, wide: bool, big_endian: bool) -> Option<ProcessArchitecture> {
        match (machine, wide, big_endian) {
            (3, false, false) => Some(X86),          // EM_386
            (62, true, false) => Some(X64),          // EM_X86_64
            (183, true, false) => Some(Arm64),       // EM_AARCH64
            (22, true, true) => Some(S390x),         // EM_S390
            (21, true, false) => Some(Ppc64le),      // EM_PPC64
            (258, true, false) => Some(LoongArch64), // EM_LOONGARCH
            (243, true, false) => Some(RiscV64),     // EM_RISCV
            _ => None,
        }
    }

    /// Mach-O `cputype` (with the 64-bit ABI bit) to architecture.
    fn macho_spec(cputype: u32) -> Option<ProcessArchitecture> {
        match cputype {
            7 => Some(X86),             // CPU_TYPE_X86
            0x0100_0007 => Some(X64),   // CPU_TYPE_X86_64
            0x0100_000c => Some(Arm64), // CPU_TYPE_ARM64
            _ => None,
        }
    }

    /// PE `Machine` and optional-header magic to architecture.
    fn pe_spec(machine: u16, optional_magic: u16) -> Option<ProcessArchitecture> {
        match (machine, optional_magic) {
            (0x014c, 0x10b) => Some(X86),   // IMAGE_FILE_MACHINE_I386, PE32
            (0x01c4, 0x10b) => Some(Arm),   // IMAGE_FILE_MACHINE_ARMNT, PE32
            (0x8664, 0x20b) => Some(X64),   // IMAGE_FILE_MACHINE_AMD64, PE32+
            (0xaa64, 0x20b) => Some(Arm64), // IMAGE_FILE_MACHINE_ARM64, PE32+
            _ => None,
        }
    }

    /// Machines worth generating: every one the specs name, the 32-bit ARM
    /// that they deliberately leave out, and a few others.
    const ELF_MACHINES: &[u16] = &[0, 2, 3, 8, 20, 21, 22, 40, 62, 183, 243, 258, 0xffff];
    const MACHO_CPUTYPES: &[u32] = &[
        7,
        12,
        18,
        0x0100_0007,
        0x0100_000c,
        0x0100_0012,
        0x0200_000c,
        0xffff_ffff,
    ];
    const PE_MACHINES: &[u16] = &[
        0, 0x014c, 0x01c0, 0x01c4, 0x0200, 0x5064, 0x6264, 0x8664, 0xa641, 0xaa64,
    ];
    const PE_MAGICS: &[u16] = &[0x10b, 0x20b, 0x107, 0];

    /// A generated executable: its leading bytes, how many of them the header
    /// spans, and what the specification says it runs as.
    #[derive(Debug, Clone)]
    struct Generated {
        bytes: Vec<u8>,
        header_len: usize,
        expected: Option<ProcessArchitecture>,
    }

    fn put_u16(bytes: &mut [u8], at: usize, value: u16, big_endian: bool) {
        let encoded = if big_endian {
            value.to_be_bytes()
        } else {
            value.to_le_bytes()
        };
        bytes[at..at + 2].copy_from_slice(&encoded);
    }

    fn put_u32(bytes: &mut [u8], at: usize, value: u32, big_endian: bool) {
        let encoded = if big_endian {
            value.to_be_bytes()
        } else {
            value.to_le_bytes()
        };
        bytes[at..at + 4].copy_from_slice(&encoded);
    }

    /// Random filler, then the header fields written over it, then more
    /// filler past the header.
    fn filler(len: impl Into<prop::collection::SizeRange>) -> impl Strategy<Value = Vec<u8>> {
        prop::collection::vec(any::<u8>(), len)
    }

    fn elf() -> impl Strategy<Value = Generated> {
        (
            prop::sample::select(ELF_MACHINES),
            any::<bool>(),
            any::<bool>(),
            filler(20),
            filler(0..200),
        )
            .prop_map(|(machine, wide, big_endian, mut bytes, tail)| {
                bytes[..4].copy_from_slice(b"\x7fELF");
                bytes[4] = if wide { 2 } else { 1 };
                bytes[5] = if big_endian { 2 } else { 1 };
                put_u16(&mut bytes, 18, machine, big_endian);
                bytes.extend(tail);
                Generated {
                    bytes,
                    header_len: 20,
                    expected: elf_spec(machine, wide, big_endian),
                }
            })
    }

    fn thin_macho() -> impl Strategy<Value = Generated> {
        (
            prop::sample::select(MACHO_CPUTYPES),
            any::<bool>(),
            any::<bool>(),
            filler(8),
            filler(0..200),
        )
            .prop_map(|(cputype, wide, big_endian, mut bytes, tail)| {
                let magic = if wide { 0xfeed_facf } else { 0xfeed_face };
                put_u32(&mut bytes, 0, magic, big_endian);
                put_u32(&mut bytes, 4, cputype, big_endian);
                bytes.extend(tail);
                // Every architecture .NET runs on macOS is little-endian, and
                // its header's width is its ABI's.
                let consistent = !big_endian && wide == (cputype & 0x0100_0000 != 0);
                Generated {
                    bytes,
                    header_len: 8,
                    expected: macho_spec(cputype).filter(|_| consistent),
                }
            })
    }

    fn fat_macho() -> impl Strategy<Value = Generated> {
        (
            prop::collection::vec(prop::sample::select(MACHO_CPUTYPES), 1..5),
            any::<bool>(),
            filler(8 + 4 * 32),
            filler(0..200),
        )
            .prop_map(|(cputypes, wide, mut bytes, tail)| {
                let entry = if wide { 32 } else { 20 };
                put_u32(
                    &mut bytes,
                    0,
                    if wide { 0xcafe_babf } else { 0xcafe_babe },
                    true,
                );
                put_u32(&mut bytes, 4, cputypes.len() as u32, true);
                for (i, cputype) in cputypes.iter().enumerate() {
                    put_u32(&mut bytes, 8 + i * entry, *cputype, true);
                }
                // The last field read is the last slice's `cputype`.
                let header_len = 8 + (cputypes.len() - 1) * entry + 4;
                bytes.truncate(8 + cputypes.len() * entry);
                bytes.extend(tail);
                let arches: Vec<_> = cputypes.iter().map(|c| macho_spec(*c)).collect();
                let expected = arches[0].filter(|_| arches.iter().all(|a| *a == arches[0]));
                Generated {
                    bytes,
                    header_len,
                    expected,
                }
            })
    }

    fn pe() -> impl Strategy<Value = Generated> {
        (
            prop::sample::select(PE_MACHINES),
            prop::sample::select(PE_MAGICS),
            0x40usize..1024,
            filler(1024 + 26),
            filler(0..200),
        )
            .prop_map(|(machine, magic, lfanew, mut bytes, tail)| {
                bytes[..2].copy_from_slice(b"MZ");
                put_u32(&mut bytes, 0x3c, lfanew as u32, false);
                bytes[lfanew..lfanew + 4].copy_from_slice(b"PE\0\0");
                put_u16(&mut bytes, lfanew + 4, machine, false);
                put_u16(&mut bytes, lfanew + 24, magic, false);
                let header_len = lfanew + 26;
                bytes.truncate(header_len);
                bytes.extend(tail);
                Generated {
                    bytes,
                    header_len,
                    expected: pe_spec(machine, magic),
                }
            })
    }

    /// Each format's magic, with the bytes after it that choose its variant.
    const MAGICS: &[&[u8]] = &[
        b"",
        b"\x7fELF\x01\x01",
        b"\x7fELF\x02\x02",
        b"\xcf\xfa\xed\xfe",
        b"\xfe\xed\xfa\xce",
        b"\xca\xfe\xba\xbe",
        b"\xca\xfe\xba\xbf",
        b"MZ",
    ];

    fn any_executable() -> impl Strategy<Value = Generated> {
        prop_oneof![elf(), thin_macho(), fat_macho(), pe()]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2048))]

        /// Each format's header, whatever surrounds its fields, reads as the
        /// specification says.
        #[test]
        fn a_generated_header_reads_as_its_specification(generated in any_executable()) {
            prop_assert_eq!(
                ProcessArchitecture::of_executable(&generated.bytes),
                generated.expected,
                "{:02x?}",
                &generated.bytes[..generated.header_len]
            );
        }

        /// The header is all that is read: any prefix that holds it reads
        /// the same, and one that cuts it short reads as nothing.
        #[test]
        fn only_the_header_is_read(generated in any_executable(), cut in any::<prop::sample::Index>()) {
            let len = cut.index(generated.bytes.len() + 1);
            let expected = if len >= generated.header_len { generated.expected } else { None };
            prop_assert_eq!(
                ProcessArchitecture::of_executable(&generated.bytes[..len]),
                expected,
                "{:02x?}",
                &generated.bytes[..len]
            );
        }

        /// Arbitrary bytes, and arbitrary bytes behind each format's magic,
        /// never panic.
        #[test]
        fn arbitrary_bytes_are_read_without_panicking(
            magic in prop::sample::select(MAGICS),
            rest in prop::collection::vec(any::<u8>(), 0..300),
        ) {
            let mut bytes = magic.to_vec();
            bytes.extend(rest);
            let _ = ProcessArchitecture::of_executable(&bytes);
        }
    }

    /// A PE header whose `e_lfanew` points anywhere, the end of the address
    /// space included, reads as nothing rather than overflowing.
    #[test]
    fn a_pe_offset_past_the_bytes_reads_as_nothing() {
        for lfanew in [u32::MAX, u32::MAX - 3, u32::MAX - 25, 4096, 0x41] {
            let mut bytes = vec![0u8; 0x80];
            bytes[..2].copy_from_slice(b"MZ");
            put_u32(&mut bytes, 0x3c, lfanew, false);
            assert_eq!(ProcessArchitecture::of_executable(&bytes), None);
        }
    }

    /// A fat header that counts twenty or more slices is a Java class file
    /// (whose major version shares the field), as `file(1)` reads it.
    #[test]
    fn a_fat_magic_with_many_slices_reads_as_nothing() {
        let mut bytes = vec![0u8; 8 + 20 * 52];
        put_u32(&mut bytes, 0, 0xcafe_babe, true);
        put_u32(&mut bytes, 4, 52, true);
        for i in 0..52 {
            put_u32(&mut bytes, 8 + i * 20, 0x0100_000c, true);
        }
        assert_eq!(ProcessArchitecture::of_executable(&bytes), None);
    }

    #[test]
    fn names_round_trip() {
        for arch in ProcessArchitecture::ALL {
            assert_eq!(ProcessArchitecture::from_name(arch.name()), Some(arch));
        }
        assert_eq!(ProcessArchitecture::from_name("x64"), None);
    }
}
