/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Examples.Periodic.PeriodicGeneralComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A concrete periodic scalar coefficient field

This file defines the deterministic periodic coefficient field
`a(x) = m(x) I`, where `m(x) = d + 2 + sum_i cos (2 pi x_i)`, and proves it is
periodic, isotropic, adjoint-invariant, and uniformly elliptic (`λ = 2`,
`Λ = 2d + 2`).  These structural facts are *consumed by*
`PeriodicConcreteComparison` (and, through it, `PeriodicSmoothComparison`) to
instantiate the periodic comparison corollary.
-/

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The scalar multiplier `m(x) = d + 2 + sum_i cos (2 pi x_i)`. -/
noncomputable def mField {d : ℕ} (x : Vec d) : ℝ :=
  ((d : ℝ) + 2) + ∑ i : Fin d, Real.cos (2 * Real.pi * x i)

/-- The coefficient field `a(x) = m(x) I`. -/
noncomputable def mFieldCoeff {d : ℕ} : CoeffField d :=
  fun x => scalarMatrix (d := d) (mField x)

theorem measurable_mField {d : ℕ} :
    Measurable (mField (d := d)) := by
  unfold mField
  fun_prop

theorem mField_sum_cos_le {d : ℕ} (x : Vec d) :
    (∑ i : Fin d, Real.cos (2 * Real.pi * x i)) ≤ (d : ℝ) := by
  calc
    (∑ i : Fin d, Real.cos (2 * Real.pi * x i))
        ≤ ∑ _i : Fin d, (1 : ℝ) := by
          exact Finset.sum_le_sum fun i _hi => Real.cos_le_one _
    _ = (d : ℝ) := by simp

theorem neg_card_le_mField_sum_cos {d : ℕ} (x : Vec d) :
    -((d : ℝ)) ≤ ∑ i : Fin d, Real.cos (2 * Real.pi * x i) := by
  calc
    -((d : ℝ)) = ∑ _i : Fin d, (-1 : ℝ) := by simp
    _ ≤ ∑ i : Fin d, Real.cos (2 * Real.pi * x i) := by
          exact Finset.sum_le_sum fun i _hi => Real.neg_one_le_cos _

theorem two_le_mField {d : ℕ} (x : Vec d) :
    (2 : ℝ) ≤ mField x := by
  have hsum := neg_card_le_mField_sum_cos (d := d) x
  dsimp [mField]
  nlinarith

theorem mField_le_two_mul_dim_add_two {d : ℕ} (x : Vec d) :
    mField x ≤ 2 * (d : ℝ) + 2 := by
  have hsum := mField_sum_cos_le (d := d) x
  dsimp [mField]
  nlinarith

theorem abs_mField_le {d : ℕ} (x : Vec d) :
    |mField x| ≤ 2 * (d : ℝ) + 2 := by
  have hlo := two_le_mField (d := d) x
  have hhi := mField_le_two_mul_dim_add_two (d := d) x
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- The explicit periodic field `a(x) = m(x) I` as a carrier element: each entry
is measurable (a cosine sum) and bounded, hence locally integrable. -/
noncomputable def mFieldReg {d : ℕ} : RegCoeffField d where
  toFun := mFieldCoeff
  entry_measurable := fun i j => by
    by_cases hij : i = j
    · subst j
      simpa [mFieldCoeff, scalarMatrix] using measurable_mField (d := d)
    · simp [mFieldCoeff, scalarMatrix, hij]
  entry_locInt := fun i j => by
    by_cases hij : i = j
    · subst j
      have hmeas : Measurable (fun x : Vec d => mFieldCoeff (d := d) x i i) := by
        simpa [mFieldCoeff, scalarMatrix] using measurable_mField (d := d)
      refine RegCoeffField.locallyIntegrable_of_bounded_measurable hmeas
        (C := 2 * (d : ℝ) + 2) fun x => ?_
      simpa [mFieldCoeff, scalarMatrix] using abs_mField_le (d := d) x
    · have hzero : (fun x : Vec d => mFieldCoeff (d := d) x i j)
          = fun _ : Vec d => (0 : ℝ) := by
        funext x
        simp [mFieldCoeff, scalarMatrix, hij]
      rw [hzero]
      exact MeasureTheory.locallyIntegrable_const (0 : ℝ)

@[simp] theorem mFieldReg_toFun {d : ℕ} :
    (mFieldReg (d := d)).toFun = mFieldCoeff := rfl

theorem isEllipticMatrix_scalarMatrix_of_bounds {d : ℕ} {lam Lam sigma : ℝ}
    (hlam : 0 < lam) (hlo : lam ≤ sigma) (hhi : sigma ≤ Lam) :
    IsEllipticMatrix lam Lam (scalarMatrix (d := d) sigma) := by
  exact (isEllipticMatrix_scalarMatrix (lt_of_lt_of_le hlam hlo)).mono hlam hlo hhi

theorem mFieldCoeff_isEllipticFieldOn {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsEllipticFieldOn (2 : ℝ) (2 * (d : ℝ) + 2) U (mFieldCoeff (d := d)) := by
  classical
  refine ⟨?_, ?_⟩
  · refine (measurable_pi_iff).2 ?_
    intro i
    refine (measurable_pi_iff).2 ?_
    intro j
    have hentry : Measurable fun x : Vec d => mFieldCoeff (d := d) x i j := by
      by_cases hij : i = j
      · subst j
        simpa [mFieldCoeff, scalarMatrix] using measurable_mField (d := d)
      · have hzero :
            (fun x : Vec d => mFieldCoeff (d := d) x i j) = fun _x => (0 : ℝ) := by
          funext x
          simp [mFieldCoeff, scalarMatrix, hij]
        rw [hzero]
        exact measurable_const
    have hpiece :
        Measurable
          (U.piecewise (fun x : Vec d => mFieldCoeff (d := d) x i j) (fun _ => 0)) :=
      hentry.piecewise hU measurable_const
    have hEq :
        (U.piecewise (fun x : Vec d => mFieldCoeff (d := d) x i j) (fun _ => 0)) =
          (fun x : Vec d => if x ∈ U then mFieldCoeff (d := d) x i j else 0) := by
      funext x
      by_cases hx : x ∈ U <;> simp [Set.piecewise, hx]
    simpa [hEq] using hpiece
  · intro x _hx
    exact isEllipticMatrix_scalarMatrix_of_bounds
      (d := d) (lam := 2) (Lam := 2 * (d : ℝ) + 2)
      (sigma := mField x) (by norm_num)
      (two_le_mField (d := d) x)
      (mField_le_two_mul_dim_add_two (d := d) x)

theorem mFieldReg_aeeEllipticOn {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    Book.Ch04.AEEllipticOn (2 : ℝ) (2 * (d : ℝ) + 2) U (mFieldReg (d := d)) := by
  exact IsAEEllipticFieldOn.of_isEllipticFieldOn (mFieldCoeff_isEllipticFieldOn hU)

theorem mField_translate_int {d : ℕ} (z : Fin d → ℤ) (x : Vec d) :
    mField (fun i => x i + (z i : ℝ)) = mField x := by
  unfold mField
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have harg :
      2 * Real.pi * (x i + (z i : ℝ)) =
        2 * Real.pi * x i + (z i : ℝ) * (2 * Real.pi) := by
    ring
  rw [harg, Real.cos_add_int_mul_two_pi]

theorem mFieldCoeff_periodic {d : ℕ} :
    IsPeriodicCoeffField (mFieldCoeff (d := d)) := by
  intro z
  ext x i j
  simp [mFieldCoeff, translateByInt, translateCoeffField, intVecToRealVec,
    mField_translate_int]

private theorem matVecMul_signedPermutation_apply {d : ℕ} {R : Mat d}
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0)
    (x : Vec d) (i : Fin d) :
    matVecMul R x i = s (σ.symm i) * x (σ.symm i) := by
  rw [matVecMul, Finset.sum_eq_single (σ.symm i)]
  · rw [hRdef i (σ.symm i)]
    simp
  · intro j _hj hj
    rw [hRdef i j]
    have hij : i ≠ σ j := by
      intro h
      apply hj
      have hsymm : σ.symm i = j := by
        rw [h]
        simp
      exact hsymm.symm
    simp [hij]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem mField_signedPermutation {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (x : Vec d) :
    mField (matVecMul R x) = mField x := by
  classical
  rcases hR with ⟨σ, s, hs, hRdef⟩
  unfold mField
  congr 1
  calc
    (∑ i : Fin d, Real.cos (2 * Real.pi * matVecMul R x i))
        = ∑ i : Fin d, Real.cos (2 * Real.pi * (s (σ.symm i) * x (σ.symm i))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [matVecMul_signedPermutation_apply (hRdef := hRdef)]
    _ = ∑ i : Fin d, Real.cos (2 * Real.pi * x (σ.symm i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rcases hs (σ.symm i) with hsign | hsign
          · simp [hsign]
          · rw [hsign]
            have harg :
                2 * Real.pi * ((-1 : ℝ) * x (σ.symm i)) =
                  -(2 * Real.pi * x (σ.symm i)) := by
              ring
            rw [harg, Real.cos_neg]
    _ = ∑ i : Fin d, Real.cos (2 * Real.pi * x i) := by
          simpa using (Equiv.sum_comp σ.symm
            (fun i : Fin d => Real.cos (2 * Real.pi * x i)))

theorem mFieldCoeff_isotropic {d : ℕ} :
    IsIsotropicCoeffField (mFieldCoeff (d := d)) := by
  intro R hR
  ext x i j
  have hm : mField (matVecMul R x) = mField x :=
    mField_signedPermutation hR x
  simp [mFieldCoeff, rotateCoeffField, scalarMatrix, hm, hR.transpose_mul_self]

theorem mFieldCoeff_adjointInvariant {d : ℕ} :
    IsAdjointInvariantCoeffField (mFieldCoeff (d := d)) := by
  ext x i j
  by_cases hij : i = j
  · subst j
    simp [mFieldCoeff, adjointCoeffField, matTranspose, scalarMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [mFieldCoeff, adjointCoeffField, matTranspose, scalarMatrix, hij, hji]

end

end Periodic
end Examples
end Homogenization
