/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.SpaceAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Fixed-time spatial regularity and zero-mean gradient of the summed corrector. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

/-- Finite set of corrector cutoff indices active at a specified time. -/
noncomputable def ChiMRegularity.chiMIndexFinset {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) : Finset ℤ :=
  (xiMK_support_finite I hm t).toFinset

/-- At fixed time the corrector series is an ordinary finite sum. -/
theorem chiM_eq_finset_sum {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ t : ℝ) (x : Vec 2) :
    I.chiM κ m t x =
      ∑ k ∈ ChiMRegularity.chiMIndexFinset I hm t,
        I.xiMK m k t • I.chiMK κ m k t x := by
  classical
  unfold Ingredients.chiM
  apply tsum_eq_sum (s := ChiMRegularity.chiMIndexFinset I hm t)
  intro k hk
  have hnotS : k ∉ (xiMK_support_finite I hm t).toFinset := by
    simpa [ChiMRegularity.chiMIndexFinset] using hk
  have hnot : k ∉ {k : ℤ | I.xiMK m k t ≠ 0} := by
    intro hmem
    exact hnotS ((xiMK_support_finite I hm t).mem_toFinset.mpr hmem)
  have hzero : I.xiMK m k t = 0 := by
    by_contra hne
    exact hnot hne
  simp [hzero]

/-- Each fixed-time coordinate of the summed corrector is smooth in space. -/
theorem chiM_component_contDiff {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (κ t : ℝ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => I.chiM κ m t x i) := by
  classical
  have hrepr : (fun x : Vec 2 => I.chiM κ m t x i) =
      fun x => ∑ k ∈ ChiMRegularity.chiMIndexFinset I hm t,
        I.xiMK m k t * I.chiMK κ m k t x i := by
    funext x
    rw [chiM_eq_finset_sum I hm κ t x]
    simp [Pi.smul_apply]
  rw [hrepr]
  apply ContDiff.sum
  intro k hk
  have hmode : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => I.chiMK κ m k t x i) := by
    have hu : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => uShear β I.Λ m k x i) := by
      fin_cases i
      all_goals
        by_cases hk1 : k % 4 = 1
        · simp only [uShear, ↓reduceIte, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
            uShear, hk1, ↓reduceIte, Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          all_goals fun_prop
        · by_cases hk3 : k % 4 = 3
          · simp only [uShear, OfNat.ofNat_ne_one, ↓reduceIte, Fin.isValue, Fin.zero_eta,
              Matrix.cons_val_zero, uShear, hk3, OfNat.ofNat_ne_one, ↓reduceIte, Fin.isValue,
              Fin.mk_one, Matrix.cons_val_one,
              Matrix.cons_val_fin_one]
            all_goals fun_prop
          · simp only [uShear, ↓reduceIte, Pi.zero_apply, uShear, hk1, ↓reduceIte, hk3,
              Pi.zero_apply]
            exact contDiff_const
    simpa [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul] using
      (contDiff_const.mul hu : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => -(I.corrTime κ m k t) * uShear β I.Λ m k x i))
  simpa only [Pi.smul_apply] using
    (contDiff_const.mul hmode : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => I.xiMK m k t * I.chiMK κ m k t x i))

theorem ChiMRegularity.cos_integer_frequency_periodic (ε : ℝ) {N : ℕ}
    (hεinv : ε⁻¹ = (N : ℝ)) (x : ℝ) (n : ℤ) :
    Real.cos (2 * Real.pi * (x + (n : ℝ)) / ε) =
      Real.cos (2 * Real.pi * x / ε) := by
  have hshift : 2 * Real.pi * (x + (n : ℝ)) / ε =
      2 * Real.pi * x / ε + ((n * (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    calc
      _ = 2 * Real.pi * x / ε + 2 * Real.pi * (n : ℝ) / ε := by ring
      _ = 2 * Real.pi * x / ε + 2 * Real.pi * ((n : ℝ) * (N : ℝ)) := by
        rw [div_eq_mul_inv, ← hεinv]
        ring
      _ = 2 * Real.pi * x / ε + ((n * (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
  rw [hshift, Real.cos_add_int_mul_two_pi]

theorem ChiMRegularity.uShear_z2_periodic {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (k : ℤ) :
    AVenhance.IsZ2Periodic (fun x : Vec 2 => uShear β I.Λ m k x) := by
  intro n x
  have hεinv := epsilon_inv_eq_ceil I hm
  ext i
  by_cases hk1 : k % 4 = 1
  · simp [uShear, hk1, latticeShift,
      ChiMRegularity.cos_integer_frequency_periodic (epsilon β I.Λ m) hεinv (x 0) (n 0)]
  · by_cases hk3 : k % 4 = 3
    · simp [uShear, hk3, latticeShift,
        ChiMRegularity.cos_integer_frequency_periodic (epsilon β I.Λ m) hεinv (x 1) (n 1)]
    · simp [uShear, hk1, hk3]

/-- Each fixed-time coordinate of the summed corrector is integer-periodic. -/
theorem chiM_component_z2_periodic {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun x : Vec 2 => I.chiM κ m t x i) := by
  classical
  intro n x
  change I.chiM κ m t (x + latticeShift n) i = I.chiM κ m t x i
  rw [chiM_eq_finset_sum I hm κ t (x + latticeShift n),
    chiM_eq_finset_sum I hm κ t x]
  apply congrArg (fun v : Vec 2 => v i)
  apply Finset.sum_congr rfl
  intro k hk
  have hperiod := ChiMRegularity.uShear_z2_periodic I hm k n x
  change uShear β I.Λ m k (x + latticeShift n) = uShear β I.Λ m k x at hperiod
  simp only [Ingredients.chiMK]
  rw [hperiod]

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def ChiMRegularity.closedUnitSquare : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem ChiMRegularity.real_integrableOn_unitCell {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) := by
  have hcompact : IsCompact ChiMRegularity.closedUnitSquare := by
    simpa [ChiMRegularity.closedUnitSquare] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hsubset : AVenhance.Infra.Torus.unitCell 2 ⊆ ChiMRegularity.closedUnitSquare := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [ChiMRegularity.closedUnitSquare, Set.mem_pi]
    intro i _hi
    exact ⟨le_of_lt (hx i).1, by simpa only [zero_add] using (hx i).2⟩
  exact (hf.continuousOn.integrableOn_compact hcompact).mono_set hsubset

/-- Every coordinate derivative of the fixed-time summed corrector has zero
mean over the spatial torus. -/
theorem spaceAvg_chiM_component_deriv_eq_zero {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) (i j : Fin 2) :
    spaceAvg (fun x => spaceGrad (fun y => I.chiM κ m t y i) x j) = 0 := by
  let f : Vec 2 → ℝ := fun x => I.chiM κ m t x i
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact chiM_component_contDiff I hm κ t i
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hper : AVenhance.IsZ2Periodic f := by
    exact chiM_component_z2_periodic I hm κ t i
  have hperC : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex f) := by
    intro n x
    have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hper n x
    exact congrArg (fun y : ℝ => (y : ℂ)) h
  have hcomplex := AVenhance.Infra.Torus.integral_unitCell_coord_deriv_eq_zero
    (n := 1) j (Complex.ofRealCLM.contDiff.comp hf1) hperC
  change (∫ x in AVenhance.Infra.Torus.unitCell 2,
      AVenhance.Infra.Torus.coordDeriv j
        (AVenhance.Infra.Torus.realToComplex f) x) = 0 at hcomplex
  have hderiv : AVenhance.Infra.Torus.coordDeriv j
      (AVenhance.Infra.Torus.realToComplex f) =
      fun x => (spaceGrad f x j : ℂ) := by
    funext x
    exact AVenhance.Infra.Torus.coordDeriv_realToComplex hf1 j x
  rw [hderiv] at hcomplex
  have hcont : Continuous (fun x => spaceGrad f x j) := by
    unfold spaceGrad
    exact (hf1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmap : (∫ x in AVenhance.Infra.Torus.unitCell 2,
      (spaceGrad f x j : ℂ)) =
      ((∫ x in AVenhance.Infra.Torus.unitCell 2, spaceGrad f x j : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm
      (μ := (volume : Measure (Vec 2)).restrict
        (AVenhance.Infra.Torus.unitCell 2))
      (ChiMRegularity.real_integrableOn_unitCell hcont))
  have hcell : ∫ x in AVenhance.Infra.Torus.unitCell 2,
      spaceGrad f x j = 0 := by
    apply Complex.ofReal_injective
    calc
      ((∫ x in AVenhance.Infra.Torus.unitCell 2, spaceGrad f x j : ℝ) : ℂ) =
          ∫ x in AVenhance.Infra.Torus.unitCell 2, (spaceGrad f x j : ℂ) := hmap.symm
      _ = 0 := hcomplex
  unfold spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  simpa [f] using hcell

end AVenhance.Infra.Section3
