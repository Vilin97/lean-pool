/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.GaussianPeriodization

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module Submodule MeasureTheory Set

namespace NumberField.Odlyzko

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coordinate int lattice used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntLattice : Submodule ℤ (ι → ℝ) :=
  span ℤ (Set.range (Pi.basisFun ℝ ι))

/-- A coordinate int basis used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntBasis :
    Basis ι ℤ (coordinateIntLattice (ι := ι)) :=
  (Pi.basisFun ℝ ι).restrictScalars ℤ

/-- A coordinate int point used in the Odlyzko-bound argument. -/
noncomputable def coordinateIntPoint (n : ι → ℤ) :
    coordinateIntLattice (ι := ι) :=
  (coordinateIntBasis (ι := ι)).equivFun.symm n

omit [DecidableEq ι] in
@[simp]
theorem coordinateIntPoint_apply (n : ι → ℤ) (i : ι) :
    (coordinateIntPoint n : ι → ℝ) i = n i := by
  classical
  rw [coordinateIntPoint, Basis.equivFun_symm_apply]
  change (coordinateIntLattice (ι := ι)).subtype
    (∑ j, n j • coordinateIntBasis j) i = _
  rw [map_sum]
  simp_rw [map_zsmul]
  rw [Finset.sum_apply]
  have hb (j : ι) :
      (coordinateIntLattice (ι := ι)).subtype
        (coordinateIntBasis j) =
          Pi.basisFun ℝ ι j :=
    Basis.restrictScalars_apply ℤ (Pi.basisFun ℝ ι) j
  simp_rw [hb]
  simp only [Pi.basisFun_apply, Pi.smul_apply, zsmul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · simp_all
  · simp

omit [DecidableEq ι] in
theorem pi_Ioc_ae_eq_pi_Ico :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} := by
  have hioc :
      ({x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ioc (0 : ℝ) 1 := by grind
  have hico :
      ({x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1} : Set (ι → ℝ)) =
        Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1 := by
    ext
    simp
  rw [hioc, hico, MeasureTheory.volume_pi]
  exact (Measure.pi_Ioc_ae_eq_pi_Icc.trans
    Measure.pi_Ico_ae_eq_pi_Icc.symm)

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ico
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  letI : VAddInvariantMeasure
      (span ℤ (Set.range (Pi.basisFun ℝ ι))) (ι → ℝ) volume :=
    ⟨fun c s _ ↦ measure_preimage_add volume (c : ι → ℝ) s⟩
  have hfund :=
    (ZSpan.isAddFundamentalDomain
      (Pi.basisFun ℝ ι) volume).integral_eq_tsum'' f hf
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hfund
  have hset :
      (Set.pi Set.univ fun _ : ι ↦ Ico (0 : ℝ) 1) =
        {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1} := by grind
  rw [hset] at hfund
  have hvadd
      (z : span ℤ (Set.range (Pi.basisFun ℝ ι)))
      (x : ι → ℝ) :
      z +ᵥ x = (z : ι → ℝ) + x := rfl
  simp_rw [hvadd] at hfund
  calc
    ∫ x, f x =
        ∑' z : coordinateIntLattice (ι := ι),
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((z : ι → ℝ) + x) := by
      simpa [coordinateIntLattice] using hfund
    _ = ∑' n : ι → ℤ,
          ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico 0 1},
            f ((coordinateIntPoint n : ι → ℝ) + x) := by
      exact (Equiv.tsum_eq
        (coordinateIntBasis (ι := ι)).equivFun.toEquiv.symm _).symm
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      funext x
      congr 2
      funext i
      simp

omit [DecidableEq ι] in
theorem integral_eq_tsum_integral_pi_Ioc
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : (ι → ℝ) → A) (hf : Integrable f) :
    ∫ x, f x =
      ∑' n : ι → ℤ,
        ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc 0 1},
          f ((fun i ↦ (n i : ℝ)) + x) := by
  classical
  rw [integral_eq_tsum_integral_pi_Ico f hf]
  apply tsum_congr
  intro n
  exact setIntegral_congr_set pi_Ioc_ae_eq_pi_Ico.symm

end NumberField.Odlyzko
