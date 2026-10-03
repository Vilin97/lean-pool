/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.Approx
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy

/-! Time primitives of the actual large-cell diffusivity coefficient. -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Primitive control uses the period length, rather than the time interval length. -/
theorem iterate_periodic_primitive_bound {f : ℝ → ℝ} {P B : ℝ}
    (hP : 0 < P) (hB : 0 ≤ B) (hf : Continuous f) (hp : Function.Periodic f P)
    (hz : (∫ t in (0 : ℝ)..P, f t) = 0)
    (hb : ∀ t, |f t| ≤ B) (t : ℝ) :
    |∫ s in (0 : ℝ)..t, f s| ≤ P * B := by
  have hper : Function.Periodic (fun u => ∫ s in (0 : ℝ)..u, f s) P := by
    intro u
    have hcell : (∫ s in u..u + P, f s) = 0 := by
      rw [hp.intervalIntegral_add_eq u 0]
      simpa using hz
    dsimp only
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u (u + P)), hcell, add_zero]
  have hcellbound : ∀ u ∈ Set.Icc 0 P, |∫ s in (0 : ℝ)..u, f s| ≤ P * B := by
    intro u hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := u) (f := f)
      (fun s _ => by simpa only [Real.norm_eq_abs] using hb s)
    have huabs : |u - 0| = u := by simp [abs_of_nonneg hu.1]
    rw [huabs, Real.norm_eq_abs] at h
    exact h.trans (by nlinarith only [hu.2, hB])
  have hglobal : ∀ u, |∫ s in (0 : ℝ)..u, f s| ≤ P * B := by
    intro u
    obtain ⟨v, hv, heq⟩ := hper.exists_mem_Ico₀ hP u
    rw [heq]
    exact hcellbound v ⟨hv.1, hv.2.le⟩
  exact hglobal t

/-- Periodicity follows from the explicit finite sum defining `Kmat`. -/
theorem iterate_Kmat_periodic {β : ℝ} (I : Ingredients β) (κ : ℝ) (m : ℕ) :
    Function.Periodic (I.Kmat κ m) (tauPP β I.Λ m) := by
  intro t
  unfold Ingredients.Kmat
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Infra.Section3.LMN_periodic I κ m n t]

/-- The uncentered primitive is zero at both endpoints and differentiates
back to the centered periodic coefficient. -/
theorem iterate_centered_primitive {f : ℝ → ℝ} {P B : ℝ} {N : ℕ}
    (hP : 0 < P) (hB : 0 ≤ B) (hf : Continuous f)
    (hp : Function.Periodic f P) (hunit : (N : ℝ) * P = 1)
    (hb : ∀ t, |f t| ≤ B) :
    let avg := ∫ s in (0 : ℝ)..1, f s
    let Q := fun t => ∫ s in (0 : ℝ)..t, (f s - avg)
    Q 0 = 0 ∧ Q 1 = 0 ∧
      (∀ t, HasDerivAt Q (f t - avg) t) ∧
      (∀ t, |Q t| ≤ 2 * P * B) := by
  dsimp only
  let avg := ∫ s in (0 : ℝ)..1, f s
  let g := fun s => f s - avg
  have hg : Continuous g := hf.sub continuous_const
  have hgp : Function.Periodic g P := by
    intro t
    dsimp [g]
    rw [hp t]
  have hzero : (∫ s in (0 : ℝ)..1, g s) = 0 := by
    dsimp [g]
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => avg) volume 0 1)]
    simp [avg]
  have hperiod := Infra.Section3.intervalIntegral_unit_eq_period_mul hgp hg hunit
  have hN : (N : ℝ) ≠ 0 := by
    intro h
    rw [h] at hunit
    norm_num at hunit
  have hz : (∫ s in (0 : ℝ)..P, g s) = 0 := by
    rw [hzero] at hperiod
    exact (mul_eq_zero.mp hperiod.symm).resolve_left hN
  have havg : |avg| ≤ B := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := f)
      (fun s _ => by simpa only [Real.norm_eq_abs] using hb s)
    simpa [avg, Real.norm_eq_abs] using h
  have hgb : ∀ t, |g t| ≤ 2 * B := by
    intro t
    exact (abs_sub (f t) avg).trans ((add_le_add (hb t) havg).trans_eq (by ring))
  refine ⟨by simp, hzero, ?_, ?_⟩
  · intro t
    exact (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
  · intro t
    have h := iterate_periodic_primitive_bound hP (by positivity : 0 ≤ 2 * B)
      hg hgp hz hgb t
    convert h using 1
    ring

/-- The material integration by parts uses this explicit primitive of `Kmat`. -/
def iterateKmatPrimitive {β : ℝ} (I : Ingredients β) (κ : ℝ) (m : ℕ)
    (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∫ s in (0 : ℝ)..t,
    (I.Kmat κ m s i j - timeAvgMat (I.Kmat κ m) i j)

/-- Quantitative endpoint and derivative facts for the actual matrix primitive. -/
theorem iterateKmatPrimitive_properties {β : ℝ} (I : Ingredients β)
    {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t i j, |I.Kmat κ m t i j| ≤ B) :
    iterateKmatPrimitive I κ m 0 = 0 ∧ iterateKmatPrimitive I κ m 1 = 0 ∧
      (∀ t i j, HasDerivAt (fun s => iterateKmatPrimitive I κ m s i j)
        (I.Kmat κ m t i j - timeAvgMat (I.Kmat κ m) i j) t) ∧
      (∀ t i j, |iterateKmatPrimitive I κ m t i j| ≤ 2 * tauPP β I.Λ m * B) := by
  have hP := I.tauPP_pos' m
  obtain ⟨k, hk⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
  have hunit : ((4 * k : ℕ) : ℝ) * tauPP β I.Λ m = 1 := by
    have heq : 1 / tauPP β I.Λ m = ((4 * k : ℕ) : ℝ) := by exact_mod_cast hk
    exact ((div_eq_iff hP.ne').mp heq).symm
  have hentry (i j : Fin 2) : Continuous (fun t => I.Kmat κ m t i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Infra.Section3.Kmat_contDiff I hm hκ).continuous)
  have hp (i j : Fin 2) : Function.Periodic (fun t => I.Kmat κ m t i j)
      (tauPP β I.Λ m) := fun t => congrFun (congrFun (iterate_Kmat_periodic I κ m t) i) j
  have h (i j : Fin 2) := iterate_centered_primitive hP hB (hentry i j) (hp i j)
    hunit (fun t => hb t i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    exact (h i j).1
  · ext i j
    exact (h i j).2.1
  · intro t i j
    exact (h i j).2.2.1 t
  · intro t i j
    exact (h i j).2.2.2 t

end AVenhance.Infra.Section4
