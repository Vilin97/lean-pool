/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.WeakModeSystem
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.Limit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.Optimize

/-!
# Lemma U: assembly of the Fourier estimates

For `s ≤ t` in `[0,1]`, the squared `L²` increment of a weak solution is the limit of the finite
coefficient sums; each of these is bounded by the low/high split with threshold `K`, and the
optimisation over `K` finishes the proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization Filter
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Classical

namespace AVenhance.Infra.FullTheorem.LemmaU

theorem cellCoeff_sub (M : ℕ) {f g : Vec 2 → ℝ} (hf : MemL2On AVenhance.unitCube f)
    (hg : MemL2On AVenhance.unitCube g) (a : RealFourierIndex M) :
    cellCoeff M (fun x => f x - g x) a = cellCoeff M f a - cellCoeff M g a := by
  have hψ : MemL2On AVenhance.unitCube (realFourierModeAmbient M a) :=
    weak_continuous_memL2On (realFourierModeAmbient_contDiff M a).continuous
  unfold cellCoeff
  simp_rw [sub_mul]
  exact integral_sub (weak_product_integrable_cell hf hψ) (weak_product_integrable_cell hg hψ)

theorem final_algebra {κ K A2 D2 h B' : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hA2 : 0 ≤ A2)
    (hD2 : 0 ≤ D2) (hh : 0 ≤ h) :
    2 * h * ((κ ^ 2 * (80 * K ^ 2) + B' ^ 2) * (A2 / (2 * κ))) +
        4 * (D2 / (36 * K ^ 2) + B' ^ 2 * (A2 / (2 * κ)) / (2 * κ * (36 * K ^ 2))) ≤
      (A2 + D2) * (h * (80 * κ * K ^ 2 + B' ^ 2 / κ) + 1 / (9 * K ^ 2) +
        B' ^ 2 / (36 * κ ^ 2 * K ^ 2)) := by
  have hT1 : 0 ≤ h * (80 * κ * K ^ 2 + B' ^ 2 / κ) := by positivity
  have hT2 : 0 ≤ B' ^ 2 / (36 * κ ^ 2 * K ^ 2) := by positivity
  have hT3 : 0 ≤ 1 / (9 * K ^ 2) := by positivity
  have e : 2 * h * ((κ ^ 2 * (80 * K ^ 2) + B' ^ 2) * (A2 / (2 * κ))) +
        4 * (D2 / (36 * K ^ 2) + B' ^ 2 * (A2 / (2 * κ)) / (2 * κ * (36 * K ^ 2))) =
      A2 * (h * (80 * κ * K ^ 2 + B' ^ 2 / κ) + B' ^ 2 / (36 * κ ^ 2 * K ^ 2)) +
        D2 * (1 / (9 * K ^ 2)) := by
    field_simp
    ring
  rw [e]
  have := mul_nonneg hA2 hT3
  have := mul_nonneg hD2 (add_nonneg hT1 hT2)
  nlinarith

theorem modePath_zero {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {Dθ₀ : Vec 2 → Vec 2}
    {θ : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hθ₀ : AVenhance.IsPeriodicH1With θ₀ Dθ₀)
    (hu : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D) (M : ℕ) (a : RealFourierIndex M) :
    modePath M θ a 0 = cellCoeff M θ₀ a := by
  have h := weak_solution_mode_integral_path hu hθ₀.2.2.1
    ((realFourierModeAmbient_contDiff M a).of_le (by simp))
    (realFourierModeAmbient_periodic M a) 0 ⟨le_rfl, zero_le_one⟩
  simp only [intervalIntegral.integral_same, sub_zero] at h
  exact h

/-- The finite-cutoff increment bound. -/
theorem increment_finite {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {θ₀ : Vec 2 → ℝ}
    {Dθ₀ : Vec 2 → Vec 2} {θ : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hκ : 0 < κ) (hB0 : 0 ≤ B)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B)
    (hθ₀ : AVenhance.IsPeriodicH1With θ₀ Dθ₀)
    (hu : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D) (M : ℕ) {K : ℝ} (hK : 0 < K)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    ∑ a : RealFourierIndex M, cellCoeff M (fun x => θ t x - θ s x) a ^ 2 ≤
      2 * (t - s) * (((κ ^ 2 * (80 * K ^ 2) + (2 * B) ^ 2)) *
        (AVenhance.l2NormSq θ₀ / (2 * κ))) +
      4 * (AVenhance.gradNormSq Dθ₀ / (36 * K ^ 2) +
        (2 * B) ^ 2 * (AVenhance.l2NormSq θ₀ / (2 * κ)) / (2 * κ * (36 * K ^ 2))) := by
  classical
  have hM := weak_modeSystem hκ hB0 hb_meas hb_per hdiv hB hθ₀ hu M
  have hinit : ∑ a, modeLam M a * modePath M θ a 0 ^ 2 ≤ AVenhance.gradNormSq Dθ₀ := by
    simp_rw [modePath_zero hθ₀ hu M]
    exact modeLam_sum_le hθ₀ M
  have hK0 : 0 ≤ K := hK.le
  have hinc := hM.increment_sum_le (fun a => ∀ i, |realFourierModeDerivativeScale a i| ≤ 2 *
      Real.pi * K)
    (Λ := 80 * K ^ 2) (L := 36 * K ^ 2) (D2 := AVenhance.gradNormSq Dθ₀) (by positivity)
    (by positivity) (fun a ha => modeLam_le_of_low M K a ha)
    (fun a ha => modeLam_ge_of_high M hK0 a ha) hinit hs ht hst
  have hmem : ∀ r ∈ Icc (0 : ℝ) 1, MemL2On AVenhance.unitCube (θ r) := fun r hr => (hu.1 r hr).2
  have heq : ∀ a : RealFourierIndex M, cellCoeff M (fun x => θ t x - θ s x) a =
      modePath M θ a t - modePath M θ a s := fun a => by
    rw [cellCoeff_sub M (hmem t ht) (hmem s hs) a]; rfl
  simp_rw [heq]
  convert hinc using 2

/-- The `s ≤ t` case of Lemma U, with drift constant `2B`. -/
theorem lemmaU_core {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {θ₀ : Vec 2 → ℝ}
    {Dθ₀ : Vec 2 → Vec 2} {θ : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB0 : 0 ≤ B)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B)
    (hθ₀ : AVenhance.IsPeriodicH1With θ₀ Dθ₀)
    (hu : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    Real.sqrt (AVenhance.l2NormSq (fun x => θ t x - θ s x)) ≤
      20 * (1 + 2 * B) / Real.sqrt κ * (t - s) ^ ((1 : ℝ) / 4) *
        Real.sqrt (AVenhance.l2NormSq θ₀ + AVenhance.gradNormSq Dθ₀) := by
  have hA2 := l2NormSq_nonneg θ₀
  have hD2 := gradNormSq_nonneg Dθ₀
  rcases hst.eq_or_lt with rfl | hlt
  · have h0 : AVenhance.l2NormSq (fun x => θ s x - θ s x) = 0 := by simp [AVenhance.l2NormSq]
    rw [h0, sub_self, Real.zero_rpow (by norm_num)]
    simp
  · have hh : 0 < t - s := sub_pos.mpr hlt
    have hh1 : t - s ≤ 1 := by linarith [hs.1, ht.2]
    have hmemd : MemL2On AVenhance.unitCube (fun x => θ t x - θ s x) :=
      (hu.1 t ht).2.sub (hu.1 s hs).2
    set S : ℝ := Real.sqrt (AVenhance.l2NormSq θ₀ + AVenhance.gradNormSq Dθ₀) with hS
    have hS2 : S ^ 2 = AVenhance.l2NormSq θ₀ + AVenhance.gradNormSq Dθ₀ :=
      Real.sq_sqrt (add_nonneg hA2 hD2)
    refine lemmaU_optimize (B := 2 * B) hh hh1 hκ hκ1 (by positivity) (Real.sqrt_nonneg _) ?_
    intro K hK
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    refine le_of_tendsto' (sum_cellCoeff_sq_tendsto hmemd) (fun M => ?_)
    refine (increment_finite hκ hB0 hb_meas hb_per hdiv hB hθ₀ hu M hKpos hs ht hst).trans ?_
    rw [hS2]
    exact final_algebra hκ hKpos hA2 hD2 hh.le

end AVenhance.Infra.FullTheorem.LemmaU

end
