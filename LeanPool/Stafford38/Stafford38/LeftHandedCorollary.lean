/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Statement
import LeanPool.Stafford38.Stafford38.Weyl.TranspositionFiltration

/-! The left-handed form is the formal-adjoint/opposite-ring image of the
    written-order Stafford identity. -/

namespace Stafford38.LeftHandedCorollary

open Stafford38
open Stafford38.WeylTransposition
open Stafford38.WeylTranspositionFiltration

universe u

def LeftHandedStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
    d ≠ 0 → ∃ R S F : WeylAlg k n,
      (1 : WeylAlg k n) = R * d + S * d * F

theorem leftHanded_of_universalStatement
    (h : UniversalStatement.{u}) : LeftHandedStatement.{u} := by
  intro k _ _ n d hd
  have htd : transpose k n d ≠ 0 := by
    intro hz
    apply hd
    simpa only [transpose_transpose, transpose_zero] using congrArg (transpose k n) hz
  rcases h k n (transpose k n d) htd with ⟨F, R, S, hone⟩
  refine ⟨transpose k n R, transpose k n S, transpose k n F, ?_⟩
  have ht := congrArg (transpose k n) hone
  have h1 : transpose k n (1 : WeylAlg k n) = 1 := by simp [transpose]
  rw [h1] at ht
  simpa [transpose_add, transpose_mul, transpose_transpose, mul_assoc] using ht

end Stafford38.LeftHandedCorollary
