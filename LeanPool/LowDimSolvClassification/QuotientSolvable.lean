/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Nilpotent

/-!
# LeanPool.LowDimSolvClassification.QuotientSolvable
-/

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A reformulation of `LieIdeal.comap_incl_eq_bot` under the additional hypothesis `J ≤ I`. -/
theorem comap_incl_eq_bot_of_le {I J : LieIdeal R L} (h : J ≤ I) :
    comap I.incl J = ⊥ ↔ J = ⊥ := by
  rw [comap_incl_eq_bot, disjoint_iff, inf_of_le_right h]

end LieIdeal

namespace LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- TODO. -/
def _root_.LieAlgebra.Quotient.mk' (I : LieIdeal R L) : L →ₗ⁅R⁆ L ⧸ I := {
  toFun := LieSubmodule.Quotient.mk (N := I)
  map_add' := by simp only [Submodule.Quotient.mk_add, implies_true]
  map_smul' := by simp only [Submodule.Quotient.mk_smul, RingHom.id_apply, implies_true]
  map_lie' := by simp only [LieSubmodule.Quotient.mk_bracket, implies_true]
}

theorem surjective_mk' (I : LieIdeal R L) : Function.Surjective (Quotient.mk' I)
    := Quot.mk_surjective

theorem solvable_of_ideal_and_quot_solvable {I : LieIdeal R L} (quotsol : LieAlgebra.IsSolvable
    (L ⧸ I))
     (Isol : LieAlgebra.IsSolvable I) :
    LieAlgebra.IsSolvable L := by
  rw [LieAlgebra.isSolvable_iff R] at *
  obtain ⟨k₁, hk₁⟩ := quotsol
  obtain ⟨k₂, hk₂⟩ := Isol
  use k₂ + k₁
  have : derivedSeries R L k₁ ≤ I := by
    rw [← LieIdeal.derivedSeries_map_eq k₁ (surjective_mk' I), eq_bot_iff, LieIdeal.map_le] at hk₁
    intro x hx
    rw [← LieSubmodule.Quotient.mk_eq_zero']
    apply hk₁
    use x, hx
    rfl
  rw [derivedSeries_def, derivedSeriesOfIdeal_add, ← derivedSeries_def R L k₁, eq_bot_iff]
  have h₁ : derivedSeriesOfIdeal R L k₂ (derivedSeries R L k₁) ≤ derivedSeriesOfIdeal R L k₂ I := by
    apply derivedSeriesOfIdeal_le this
    apply le_refl
  rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap] at hk₂
  rw [LieIdeal.comap_incl_eq_bot_of_le (derivedSeriesOfIdeal_le_self I k₂)] at hk₂
  rw [hk₂] at h₁
  assumption

end LieAlgebra
