/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Opposite
import Mathlib.Tactic
import Mathlib.Tactic.Abel

/-!
# Exact filtered Schreyer criterion

This file isolates the abstract equivalence used when a right-linear
presentation is combined with a lower filtration piece.  The right action is
encoded by the opposite scalar ring, while the lower piece is only an
additive subgroup.  No Ore, Weyl, or characteristic-variety structure is
needed.
-/

namespace AlgebraicAnalysis.FilteredSchreyer

universe u v

variable {A : Type u} {E : Type v}
  [Ring A] [AddCommGroup E] [Module Aᵐᵒᵖ E]

/-- A right-linear presentation map sends the explicit right action on its
source to right multiplication in the target ring. -/
theorem map_rightSMul (phi : E →ₗ[Aᵐᵒᵖ] A) (b : E) (x : A) :
    phi ((MulOpposite.op x) • b) = phi b * x := by
  rw [phi.map_smul, op_smul_eq_mul]

/-- Exact filtered Schreyer criterion for one distinguished right action.

The left side says that `C` lies in the image of `phi` modulo the lower
subgroup `L`.  The right side expresses the corresponding source relation as
an element mapping into `L`, plus an explicit right multiple of `x`.  The
hypotheses separate the two directions: right-coordinate stability is used
forward, and strictness under that coordinate is used backward. -/
theorem range_add_lower_iff_preimage_add_rightMultiple
    (phi : E →ₗ[Aᵐᵒᵖ] A) (L : AddSubgroup A)
    (a : E) (C x : A)
    (ha : phi a = 1 + C * x)
    (hone : (1 : A) ∈ L)
    (hLx : ∀ z : A, z ∈ L → z * x ∈ L)
    (hstrict : ∀ z : A, z * x ∈ L → z ∈ L) :
    (∃ b : E, ∃ l : A, l ∈ L ∧ C = phi b + l) ↔
      ∃ t b : E, phi t ∈ L ∧
        a = t + (MulOpposite.op x) • b := by
  constructor
  · rintro ⟨b, l, hl, rfl⟩
    let t := a - (MulOpposite.op x) • b
    have hphiRight : phi ((MulOpposite.op x) • b) = phi b * x :=
      map_rightSMul phi b x
    have hphit : phi t = 1 + l * x := by
      dsimp [t]
      rw [map_sub, hphiRight, ha]
      noncomm_ring
    have htLower : phi t ∈ L := by
      rw [hphit]
      exact L.add_mem hone (hLx l hl)
    refine ⟨t, b, htLower, ?_⟩
    dsimp [t]
    abel
  · rintro ⟨t, b, htLower, rfl⟩
    have hphiRight : phi ((MulOpposite.op x) • b) = phi b * x :=
      map_rightSMul phi b x
    rw [map_add, hphiRight] at ha
    have hCx : C * x = phi t + phi b * x - 1 := by
      apply (eq_sub_iff_add_eq).2
      calc
        C * x + 1 = 1 + C * x := add_comm _ _
        _ = phi t + phi b * x := ha.symm
    have hproduct : (C - phi b) * x = phi t - 1 := by
      rw [sub_mul, hCx]
      abel
    have hproductLower : (C - phi b) * x ∈ L := by
      rw [hproduct]
      exact L.sub_mem htLower hone
    have hlower : C - phi b ∈ L := hstrict _ hproductLower
    exact ⟨b, C - phi b, hlower, by abel⟩


end AlgebraicAnalysis.FilteredSchreyer
