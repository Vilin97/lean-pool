/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: mrLSD
-/

import LeanPool.Lean4EVM.Primitives.UInt
import LeanPool.Lean4EVM.Primitives.FixedBytes

/-!
# Verified Ethereum Virtual Machine primitives

Source: url:https://github.com/mrLSD/Lean4EVM
Authors: mrLSD
Status: verified
Main declarations: `Lean4EVM.FixedUInt.toNat_add`, `Lean4EVM.FixedUInt.toNat_mul`, `Lean4EVM.U256.toNat_addmod`, `Lean4EVM.U256.toNat_mulmod`, `Lean4EVM.U256.toNat_byteAt_of_lt`
Tags: verified-algorithms, ethereum, fixed-width-arithmetic, blockchain-semantics
MSC: 68Q60, 68V20
-/

/-!
# Lean4EVM

Lean definitions of Ethereum EVM and their verified executable operations.

`Primitives.UInt` and `Primitives.FixedBytes` are family façades. Their `Core` modules own shared
representations and proofs; modules named after public types own width- or meaning-specific APIs.
-/
