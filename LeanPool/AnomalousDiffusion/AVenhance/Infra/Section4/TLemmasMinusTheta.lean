/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TLemmasAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TLemmasNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL2

/-! The zeroth spatial-derivative consequence of `l.V.m-1.reg.upgrade`:
the actual iterates telescope to `T_{m-1} - θ_{m-1}`, and their
factorial-weighted amplitudes close to the scale in `l.Tm.minus.thetam`.
The conditional input below is exactly the `n = 0`, positive-increment slice
of the upstream `l.V` estimate, expressed in the torus norms. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4
open AVenhance

theorem TLemmasMinusTheta.classical_spatial_smooth {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol b κ F u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  exact hu.1.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)

theorem TLemmasMinusTheta.iterateIncrement_value_memL2On {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hThetaSmooth : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (θprev t))
    {i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ Nstar β) {t : ℝ} (ht : 0 ≤ t) :
    MemL2On unitCube (iterateIncrement T i t) := by
  have hnext : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev (T (i - 1))) θ₀ (T i) := hT.2 i hi hiN
  have hnextSmooth := TLemmasMinusTheta.classical_spatial_smooth hnext ht
  have hprevSmooth : ContDiff ℝ (⊤ : ℕ∞) (T (i - 1) t) := by
    by_cases hzero : i = 1
    · rw [show i - 1 = 0 by omega, hT.1]
      exact hThetaSmooth t ht
    · exact TLemmasMinusTheta.classical_spatial_smooth
        (hT.2 (i - 1) (by omega) (by omega)) ht
  have hiEq : i = (i - 1) + 1 := by omega
  rw [hiEq, iterateIncrement_succ]
  have hLp := Infra.Ergodic.continuous_unitCell_memLp_two
    (hnextSmooth.sub hprevSmooth).continuous
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at hLp
  simpa [Nat.sub_add_cancel hi] using hLp

/-! The pointwise value estimate uses only the positive-increment value part
of `l.V`. Its torus-cell integrability follows from the actual classical
iterates, so no spacetime-gradient integrability premise is needed. -/

/-- Value-only finite telescope from the positive-increment `l.V` bound. -/
theorem iterate_Tm_minus_theta_value_bound_of_V_zero {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hThetaSmooth : ∀ t : ℝ, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (θprev t))
    {S : ℝ} (hS : 0 ≤ S) {η A ρ : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hscale : η ≤ A * ρ) (hAρ : 0 ≤ A * ρ)
    (hV : ∀ i ∈ Finset.range (Nstar β), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (iterateIncrement T (i + 1) t)) +
        Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
          (fun s x => spaceGrad (iterateIncrement T (i + 1) s) x)) ≤
      (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1) * S)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (l2NormSq (fun x => T (Nstar β) t x - θprev t x)) ≤
      (Nat.factorial (2 * Nstar β) : ℝ) * (4 * A * ρ) * S := by
  let n := Nstar β
  have hsumValue : Real.sqrt (l2NormSq (fun x => T n t x - θprev t x)) ≤
      ∑ i ∈ Finset.range n,
        Real.sqrt (l2NormSq (iterateIncrement T (i + 1) t)) := by
    have htel (s : ℝ) : (fun x => T n s x - θprev s x) =
        fun x => ∑ i ∈ Finset.range n, iterateIncrement T (i + 1) s x := by
      funext x
      exact iterate_sub_theta_eq_sum I hΦ hT n s x
    rw [htel t]
    exact sqrt_l2NormSq_finset_sum_le (Finset.range n)
      (fun i x => iterateIncrement T (i + 1) t x)
      (fun i hi => TLemmasMinusTheta.iterateIncrement_value_memL2On I hΦ hT hThetaSmooth
        (by omega) (by have := Finset.mem_range.mp hi; omega) ht.1)
  have hpieces :
      (∑ i ∈ Finset.range n,
        Real.sqrt (l2NormSq (iterateIncrement T (i + 1) t))) ≤
      ∑ i ∈ Finset.range n,
        (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1) * S := by
    apply Finset.sum_le_sum
    intro i hi
    have hpoint := hV i hi t ht
    have hgrad : 0 ≤ Real.sqrt κprev * Real.sqrt (spaceTimeGradNormSq
        (fun s x => spaceGrad (iterateIncrement T (i + 1) s) x)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans (le_add_of_nonneg_right hgrad) hpoint
  have hamplitude := iterate_Tm_minus_theta_factorial_sum_bound
    (N := n) hη hηsmall hscale hAρ
  have hweighted :
      (∑ i ∈ Finset.range n,
        (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1) * S) =
      ((∑ i ∈ Finset.range n,
        (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1)) * S) := by
    rw [Finset.sum_mul]
  have hbound :
      (∑ i ∈ Finset.range n,
        (Nat.factorial (2 * (i + 1)) : ℝ) * iterateAmplitude η (i + 1) * S) ≤
      (Nat.factorial (2 * n) : ℝ) * (4 * A * ρ) * S := by
    rw [hweighted]
    exact mul_le_mul_of_nonneg_right hamplitude hS
  have hfinal := (hsumValue.trans hpieces).trans hbound
  simpa only [n] using hfinal

end AVenhance.Infra.Section4
