# Target Specification: x86 Real Mode (16-bit)

This document defines the machine state model, segmented memory translation, and BIOS/DOS interface semantics for **16-bit x86 Real Address Mode** (8086 / 80286 / bootloaders).

---

## 1. Machine State Model

### 1.1 16-Bit General Purpose Registers
8 16-bit registers with high/low byte addressing:
- `AX` (`AH` / `AL`), `BX` (`BH` / `BL`), `CX` (`CH` / `CL`), `DX` (`DH` / `DL`).
- Pointer/Index registers: `SI`, `DI`, `BP`, `SP`.
- Instruction pointer: `IP`.
- Flags register: `FLAGS` (`CF, PF, AF, ZF, SF, TF, IF, DF, OF`).

---

## 2. 21-Bit Segmented Memory Model & Intra-Segment Wrapping

In Real Mode, memory addresses are formed by shifting a 16-bit segment selector left by 4 bits and adding a 16-bit effective offset:

$$\text{Address} = (\text{Segment} \ll 4) + \text{Offset}$$

### 2.1 Intra-Segment Offset Wrapping on Multi-Byte Access
On 8086 silicon hardware, effective offset calculations for multi-byte accesses wrap modulo $2^{16}$ within the segment. If an access begins at offset `0xFFFF`, byte 0 is at offset `0xFFFF` and byte 1 wraps to offset `0x0000`:

```lean
/-- Real Mode 21-bit Physical Address normalization with intra-segment wrapping -/
def toPhysicalAddress (a20 : Bool) (seg : UInt16) (off : UInt16) (byteIndex : Nat := 0) : BitVec 21 :=
  let effectiveOff := (off.toNat + byteIndex) % 0x10000
  let raw := (seg.toNat <<< 4) + effectiveOff
  if a20 then
    BitVec.ofNat 21 raw
  else
    BitVec.ofNat 21 (raw % 0x100000)

/-- Capability tokens are indexed by canonical 21-bit physical addresses -/
def HasRealModeWritePerm (m : MachineState x86_RealMode) (seg : UInt16) (off : UInt16) (len : Nat) : Prop :=
  ∀ (i : Nat), i < len →
    m.perms.contains (PhysicalMemoryPerm (toPhysicalAddress m.a20Gate seg off i) 1 .Exclusive)
```

---

## 3. BIOS / DOS Interrupt Services & Typestates

- **BIOS Services**: `INT 0x10` (Video Teletype / Modes), `INT 0x13` (Disk Read/Write/Sectors), `INT 0x16` (Keyboard Input).
- **DOS API**: `INT 0x21` (`AH = 0x09` Print String `$`-terminated, `AH = 0x4C` Exit).
