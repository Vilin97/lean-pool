/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrLSD
-/

import LeanPool.Lean4EVM.Primitives.UInt
import LeanPool.Lean4EVM.Primitives.FixedBytes

/-!
# Verified Ethereum Virtual Machine primitives

Source: url:https://github.com/mrLSD/Lean4EVM
Authors: mrLSD
Status: verified
Main declarations: `Lean4EVM.U256.toNat_addmod`, `Lean4EVM.U256.toNat_mulmod`
Tags: verified-algorithms, ethereum, fixed-width-arithmetic, byte-representations
MSC: 68Q60, 68V20
-/

/-!
# Lean4EVM

Fixed-width integer and byte primitives for Ethereum, with proofs of their arithmetic and
conversion operations. The imported library does not define an EVM interpreter, machine state,
gas accounting, or transaction semantics.

`Primitives.UInt` and `Primitives.FixedBytes` are family façades. Their `Core` modules own shared
representations and proofs; modules named after public types own width- or meaning-specific APIs.
Optional conversions use the suffix `Opt` so the repository declaration audit resolves their full
names distinctly from the wrapping conversions.
-/

/-
Upstream MIT notice retained from mrLSD/Lean4EVM at commit
0109646545bc1f29c719c1268bad7c561d2035f8.

MIT License

Copyright (c) 2026 Evgeny Ukhanov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
