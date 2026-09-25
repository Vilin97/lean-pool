/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.NumberField.Discriminant.Different
/-!
# No nontrivial everywhere-unramified extension of ℚ

The global Kronecker--Weber argument forms a fixed field which is unramified
at every finite prime.  Minkowski's
discriminant bound to show that this field is ℚ.  This file records that
source theorem directly in terms of the local unramified predicates on the
prime ideals of the ring of integers.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory.Ramification

open NumberField

/-- A number field unramified at every prime over ℤ has degree one over ℚ.

The proof first shows that its different ideal is the unit ideal.  Its
absolute discriminant therefore has absolute value one, while the
Hermite--Minkowski bound says that every number field of degree greater than
one has absolute discriminant greater than two. -/
theorem numberField_finrank_eq_one_of_forall_isUnramifiedAt
    (K : Type*) [Field K] [NumberField K]
    (hunramified : ∀ (P : Ideal (𝓞 K)) [P.IsPrime],
      Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 := by
  have hdiff : differentIdeal ℤ (𝓞 K) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal
      (differentIdeal ℤ (𝓞 K)) hne
    let : P.IsPrime := hPmax.isPrime
    have hdvd : P ∣ differentIdeal ℤ (𝓞 K) :=
      Ideal.dvd_iff_le.mpr hle
    have hramified : ¬ Algebra.IsUnramifiedAt ℤ P :=
      dvd_differentIdeal_iff.mp hdvd
    exact hramified (hunramified P)
  have hdiscr : (discr K).natAbs = 1 := by
    rw [← absNorm_differentIdeal K (𝓞 K), hdiff]
    exact Ideal.absNorm_top
  have hle : Module.finrank ℚ K ≤ 1 := by
    by_contra hnot
    have hgt := abs_discr_gt_two (K := K) (by omega)
    have habs : |discr K| = 1 := by
      rcases Int.natAbs_eq_iff.mp hdiscr with h | h
      · simp [h]
      · simp [h]
    omega
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

end AlgebraicNumberTheory.Ramification
