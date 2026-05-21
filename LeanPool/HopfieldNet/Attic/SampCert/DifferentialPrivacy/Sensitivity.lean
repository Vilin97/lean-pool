/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Group.Basic
import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Neighbours

/-!
# Sensitivity

Notion of the "sensitivity" of a query over lists.
-/

open Classical Nat Int Real

variable {T : Type}

/--
A query `q` has sensivity `Δ`.

Namely, `|q(x) - q(x')| ≤ Δ` for neighbouring lists `x` and `x'`.
-/
noncomputable def sensitivity (q : List T → ℤ) (Δ : ℕ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → Int.natAbs (q l₁ - q l₂) ≤ Δ
