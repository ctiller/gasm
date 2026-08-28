/-
Copyright 2026 Craig Tiller

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean
import Gasm.Core.Types

namespace Gasm.Targets.BareMetal.UART

open Gasm.Core

/- REF: uart-pc16550d#register-descriptions -/
/-- 16550 UART COM1 Base Port. -/
def COM1_BASE : UInt16 := 0x3F8

/- REF: uart-pc16550d#register-descriptions -/
/-- Receiver Buffer Register (read) / Transmitter Holding Register (write) / Divisor Latch Low (when DLAB=1). -/
def UART_DATA : UInt16 := 0x3F8

/- REF: uart-pc16550d#register-descriptions -/
/-- Interrupt Enable Register (when DLAB=0) / Divisor Latch High (when DLAB=1). -/
def UART_IER : UInt16 := 0x3F9

/- REF: uart-pc16550d#register-descriptions -/
/-- Interrupt Identification Register (read) / FIFO Control Register (write). -/
def UART_IIR_FCR : UInt16 := 0x3FA

/- REF: uart-pc16550d#register-descriptions -/
/-- Line Control Register. -/
def UART_LCR : UInt16 := 0x3FB

/- REF: uart-pc16550d#register-descriptions -/
/-- Modem Control Register. -/
def UART_MCR : UInt16 := 0x3FC

/- REF: uart-pc16550d#register-descriptions -/
/-- Line Status Register. -/
def UART_LSR : UInt16 := 0x3FD

/- REF: uart-pc16550d#register-descriptions -/
/-- Modem Status Register. -/
def UART_MSR : UInt16 := 0x3FE

/- REF: uart-pc16550d#register-descriptions -/
/-- Scratchpad Register. -/
def UART_SCR : UInt16 := 0x3FF

/- REF: uart-pc16550d#register-descriptions -/
/-- Divisor Latch Access Bit in Line Control Register (LCR bit 7). -/
def LCR_DLAB : UInt8 := 0x80

/- REF: uart-pc16550d#register-descriptions -/
/-- 8 data bits, no parity, 1 stop bit mode in Line Control Register. -/
def LCR_8N1 : UInt8 := 0x03

/- REF: uart-pc16550d#register-descriptions -/
/-- FIFO Control initialization: Enable FIFO, clear TX/RX FIFOs, 14-byte threshold. -/
def FCR_INIT : UInt8 := 0xC7

/- REF: uart-pc16550d#register-descriptions -/
/-- Modem Control initialization: Assert DTR, RTS, and OUT2. -/
def MCR_INIT : UInt8 := 0x0B

/- REF: uart-pc16550d#register-descriptions -/
/-- Disable all UART interrupts. -/
def IER_DISABLE : UInt8 := 0x00

/- REF: uart-pc16550d#register-descriptions -/
/-- Transmitter Holding Register Empty (LSR bit 5). -/
def LSR_THRE : UInt8 := 0x20

/- REF: uart-pc16550d#programmable-baud-generator -/
/-- Divisor low byte for standard 115,200 baud rate. -/
def BAUD_115200_DLL : UInt8 := 0x01

/- REF: uart-pc16550d#programmable-baud-generator -/
/-- Divisor high byte for standard 115,200 baud rate. -/
def BAUD_115200_DLM : UInt8 := 0x00

end Gasm.Targets.BareMetal.UART
