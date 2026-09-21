/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Rank and torsion over Ore localizations

This file contains the part of handover packet 2 which is available without
postulating a noncommutative flatness theorem.  A right `R`-module is encoded
as a left `Rᵐᵒᵖ`-module.  When the right Ore condition needed for this
localization holds, its Ore localization is a module over the division ring
of fractions of `Rᵐᵒᵖ`; `oreRank` is the ordinary vector-space rank of that
localization.

The pinned Mathlib has the Ore localization and its division-ring structure,
but not the noncommutative tensor/localization exactness theorem (the
commutative tensor-product exactness file explicitly lists this as TODO).
Consequently this file proves the rank-nullity and torsion criteria for the
localized division-ring module, and records the exact first missing bridge:
that localization sends an arbitrary short exact sequence of right
`R`-modules to a short exact sequence.  No proposition in this file assumes
that bridge or introduces an axiom for it.

The commutative-domain criterion `rank_eq_zero_iff_isTorsion` imported from
Mathlib remains available, but is deliberately not reused as a theorem about
noncommutative `R`.
-/

namespace AlgebraicAnalysis
namespace RankTorsion

open nonZeroDivisors
open OreLocalization

universe u v

section DivisionRingRank

variable {Q : Type u} [DivisionRing Q]
variable {V V' : Type v} [AddCommGroup V] [Module Q V]
variable [AddCommGroup V'] [Module Q V']

/-! ## Unconditional vector-space rank facts -/

theorem rank_quotient_add_rank (P : Submodule Q V) :
    Module.rank Q (V ⧸ P) + Module.rank Q P = Module.rank Q V :=
  rank_quotient_add_rank_of_divisionRing P

theorem rank_eq_zero_iff_subsingleton :
    Module.rank Q V = 0 ↔ Subsingleton V := by
  exact rank_zero_iff

theorem rank_eq_zero_iff_forall_zero :
    Module.rank Q V = 0 ↔ ∀ v : V, v = 0 := by
  constructor
  · intro h v
    letI : Subsingleton V := (rank_zero_iff.mp h)
    exact Subsingleton.elim v 0
  · intro h
    apply rank_zero_iff.mpr
    exact ⟨fun x y => (h x).trans (h y).symm⟩

theorem rank_eq_zero_iff_isTorsionOverDivisionRing :
    Module.rank Q V = 0 ↔
      (∀ v : V, ∃ a : Q, a ≠ 0 ∧ a • v = 0) := by
  exact rank_eq_zero_iff

theorem finrank_quotient_add_finrank [Module.Finite Q V] (P : Submodule Q V) :
    Module.finrank Q (V ⧸ P) + Module.finrank Q P = Module.finrank Q V :=
  P.finrank_quotient_add_finrank

theorem rank_eq_of_surjective (f : V →ₗ[Q] V') (hf : Function.Surjective f) :
    Module.rank Q V = Module.rank Q V' + Module.rank Q (LinearMap.ker f) :=
  LinearMap.rank_eq_of_surjective hf

@[nolint unusedArguments]
theorem finrank_eq_of_surjective [Module.Finite Q V]
    [Module.Finite Q V'] (f : V →ₗ[Q] V') (hf : Function.Surjective f) :
    Module.finrank Q V = Module.finrank Q V' +
      Module.finrank Q (LinearMap.ker f) := by
  have h := (LinearMap.ker f).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivOfSurjective f hf)] at h
  exact h.symm

end DivisionRingRank

section OreLocalizedRightModules

/-!
`OreSet R⁰` is the left Ore condition.  A right module is localized using the
opposite ring, so the corresponding right Ore condition is represented by an
explicit `OreSet (Rᵐᵒᵖ)⁰` assumption.  This is intentional: left Ore alone does
not imply right Ore for a general domain.
-/

variable {R : Type u} [Ring R] [Nontrivial R] [NoZeroDivisors R]
variable [OreLocalization.OreSet (Rᵐᵒᵖ)⁰]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The full Ore localization of the opposite coefficient ring. -/
@[nolint unusedArguments]
abbrev FractionRingOp (R : Type u) [Ring R] [Nontrivial R]
    [NoZeroDivisors R] [OreLocalization.OreSet (Rᵐᵒᵖ)⁰] :=
  (Rᵐᵒᵖ)[(Rᵐᵒᵖ)⁰⁻¹]

/-- Localization of a right `R`-module, represented as a left opposite-module. -/
@[nolint unusedArguments]
abbrev LocalizedRightModule (R : Type u) (M : Type v)
    [Ring R] [Nontrivial R] [NoZeroDivisors R]
    [OreLocalization.OreSet (Rᵐᵒᵖ)⁰] [AddCommGroup M] [Module Rᵐᵒᵖ M] :=
  M[(Rᵐᵒᵖ)⁰⁻¹]

/-- The rank of a right module after passage to the full fraction ring. -/
noncomputable def oreRank (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] : Cardinal :=
  Module.rank (FractionRingOp R) (LocalizedRightModule R M)

@[nolint unusedArguments]
theorem oreRank_eq_rank_localized :
    oreRank (R := R) M =
      Module.rank (FractionRingOp R) (LocalizedRightModule R M) :=
  rfl

@[nolint unusedArguments]
theorem oreRank_eq_of_localizedLinearEquiv {N : Type v}
    [AddCommGroup N] [Module Rᵐᵒᵖ N]
    (e : LocalizedRightModule R M ≃ₗ[FractionRingOp R]
      LocalizedRightModule R N) :
    oreRank (R := R) M = oreRank (R := R) N := by
  exact e.rank_eq

@[nolint unusedArguments]
theorem localized_oreDiv_one_eq_zero_iff (m : M) :
    (m /ₒ (1 : (Rᵐᵒᵖ)⁰) : LocalizedRightModule R M) = 0 ↔
      ∃ s : (Rᵐᵒᵖ)⁰, s • m = 0 := by
  constructor
  · intro h
    rw [← OreLocalization.zero_oreDiv (1 : (Rᵐᵒᵖ)⁰)] at h
    rw [OreLocalization.oreDiv_eq_iff] at h
    rcases h with ⟨u, v, huv, hden⟩
    have hv : v = (u : Rᵐᵒᵖ) := by simpa using hden.symm
    refine ⟨u, ?_⟩
    change (u : Rᵐᵒᵖ) • m = 0
    rw [← hv]
    simpa using huv.symm
  · rintro ⟨s, hs⟩
    change (s : Rᵐᵒᵖ) • m = 0 at hs
    rw [← OreLocalization.zero_oreDiv (1 : (Rᵐᵒᵖ)⁰)]
    rw [OreLocalization.oreDiv_eq_iff]
    refine ⟨s, (s : Rᵐᵒᵖ), ?_, ?_⟩
    · simpa using hs.symm
    · simp

theorem oreRank_zero_iff_localized_subsingleton :
    oreRank (R := R) M = 0 ↔ Subsingleton (LocalizedRightModule R M) := by
  exact rank_zero_iff

theorem oreRank_zero_iff_rightTorsion :
    oreRank (R := R) M = 0 ↔
      (∀ m : M, ∃ s : (Rᵐᵒᵖ)⁰, s • m = 0) := by
  rw [oreRank_zero_iff_localized_subsingleton]
  constructor
  · intro h m
    have hz : (m /ₒ (1 : (Rᵐᵒᵖ)⁰) : LocalizedRightModule R M) = 0 := by
      exact Subsingleton.elim _ _
    exact (localized_oreDiv_one_eq_zero_iff m).mp hz
  · intro h
    refine ⟨fun x y => ?_⟩
    have hzero : ∀ z : LocalizedRightModule R M, z = 0 := by
      intro z
      induction z using OreLocalization.ind with
      | _ m s =>
          rw [← OreLocalization.zero_oreDiv (s : (Rᵐᵒᵖ)⁰)]
          obtain ⟨t, ht⟩ := h m
          change (t : Rᵐᵒᵖ) • m = 0 at ht
          rw [OreLocalization.oreDiv_eq_iff]
          refine ⟨t, (t : Rᵐᵒᵖ), ?_, ?_⟩
          · simpa using ht.symm
          · simp
    exact (hzero x).trans (hzero y).symm

theorem oreRank_zero_iff_localized_torsion :
    oreRank (R := R) M = 0 ↔
      (∀ z : LocalizedRightModule R M,
        ∃ a : FractionRingOp R, a ≠ 0 ∧ a • z = 0) := by
  exact rank_eq_zero_iff_isTorsionOverDivisionRing


end OreLocalizedRightModules

end RankTorsion
end AlgebraicAnalysis
