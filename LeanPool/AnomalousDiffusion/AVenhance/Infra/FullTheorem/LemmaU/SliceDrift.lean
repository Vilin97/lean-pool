/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.TimeSlices

/-!
# Lemma U: the drift term on a time slice

For a bounded drift, the drift pairing `g_t = b_t · Dθ_t` of a.e. time slice lies in `L²` of the
cell with `‖g_t‖² ≤ 2 B² ‖Dθ_t‖²`, and the forcing `weakModeForcing` of a real mode splits as
`⟨g_t, ψ_a⟩ + κ λ_a ⟨θ_t, ψ_a⟩`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness

namespace AVenhance.Infra.FullTheorem.LemmaU

theorem vecNormSq_nonneg' (x : Vec 2) : 0 ≤ Homogenization.vecNormSq x := by
  unfold Homogenization.vecNormSq Homogenization.vecDot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

theorem gradNormSq_nonneg (Du : Vec 2 → Vec 2) : 0 ≤ AVenhance.gradNormSq Du :=
  integral_nonneg (fun x => vecNormSq_nonneg' (Du x))

theorem l2NormSq_nonneg (f : Vec 2 → ℝ) : 0 ≤ AVenhance.l2NormSq f :=
  integral_nonneg (fun x => sq_nonneg (f x))

/-- Pointwise bound of the drift pairing for a sup-norm-bounded drift. -/
theorem vecDot_sq_le {u v : Vec 2} {B : ℝ} (hu : ‖u‖ ≤ B) :
    Homogenization.vecDot u v ^ 2 ≤ 2 * B ^ 2 * Homogenization.vecNormSq v := by
  have h0 : |u 0| ≤ B := (Real.norm_eq_abs _ ▸ norm_le_pi_norm u 0).trans hu
  have h1 : |u 1| ≤ B := (Real.norm_eq_abs _ ▸ norm_le_pi_norm u 1).trans hu
  have s0 : u 0 ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have s1 : u 1 ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e : Homogenization.vecDot u v = u 0 * v 0 + u 1 * v 1 := by simp [Homogenization.vecDot,
      Fin.sum_univ_two]
  have e2 : Homogenization.vecNormSq v = v 0 ^ 2 + v 1 ^ 2 := by
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_two, sq]
  rw [e, e2]
  have a0 : (u 0 * v 0) ^ 2 ≤ B ^ 2 * v 0 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right s0 (sq_nonneg _)
  have a1 : (u 1 * v 1) ^ 2 ≤ B ^ 2 * v 1 ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right s1 (sq_nonneg _)
  nlinarith [sq_nonneg (u 0 * v 0 - u 1 * v 1)]

theorem integrable_vecNormSq_cell {Du : Vec 2 → Vec 2}
    (hD : Homogenization.GradMemL2On AVenhance.unitCube Du) :
    Integrable (fun x => Homogenization.vecNormSq (Du x)) (volume.restrict AVenhance.unitCube) := by
  have : (fun x => Homogenization.vecNormSq (Du x)) = fun x => ∑ i : Fin 2, Du x i ^ 2 := by
    funext x
    simp [Homogenization.vecNormSq, Homogenization.vecDot, sq]
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (hD i).integrable_sq)

theorem integrable_vecNormSq_timeCube {D : ℝ → Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2
      (volume.restrict AVenhance.timeCube)) :
    Integrable (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (D p.1 p.2))
      (volume.restrict AVenhance.timeCube) := by
  have : (fun p : ℝ × Vec 2 => Homogenization.vecNormSq (D p.1 p.2)) =
      fun p => ∑ i : Fin 2, D p.1 p.2 i ^ 2 := by
    funext p
    simp [Homogenization.vecNormSq, Homogenization.vecDot, sq]
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (hD i).integrable_sq)

theorem integrable_vecDot_gradMode {Du : Vec 2 → Vec 2}
    (hD : Homogenization.GradMemL2On AVenhance.unitCube Du) (M : ℕ) (a : RealFourierIndex M) :
    Integrable (fun x => Homogenization.vecDot (Du x) (AVenhance.spaceGrad (realFourierModeAmbient
        M a) x))
      (volume.restrict AVenhance.unitCube) := by
  have : (fun x => Homogenization.vecDot (Du x) (AVenhance.spaceGrad (realFourierModeAmbient M a)
      x)) =
      fun x => ∑ i : Fin 2, Du x i * AVenhance.spaceGrad (realFourierModeAmbient M a) x i := rfl
  rw [this]
  refine integrable_finsetSum _ (fun i _ => weak_product_integrable_cell (hD i) ?_)
  have hc : Continuous (fun x : Vec 2 => AVenhance.spaceGrad (realFourierModeAmbient M a) x i) :=
    ((realFourierModeAmbient_contDiff M a).continuous_fderiv (by simp)).clm_apply
      continuous_const
  exact weak_continuous_memL2On hc

/-- The slice facts for the drift pairing. -/
theorem drift_slice_ae {b : ℝ → Vec 2 → Vec 2} {κ B : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B)
    (hu : AVenhance.IsWeakSolutionGrad b κ θ₀ θ D) (M : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With (θ t) (D t) ∧
      MemL2On AVenhance.unitCube (fun x => Homogenization.vecDot (b t x) (D t x)) ∧
      AVenhance.l2NormSq (fun x => Homogenization.vecDot (b t x) (D t x)) ≤
        2 * B ^ 2 * AVenhance.gradNormSq (D t) ∧
      ∀ a : RealFourierIndex M, weakModeForcing b κ D (realFourierModeAmbient M a) t =
        cellCoeff M (fun x => Homogenization.vecDot (b t x) (D t x)) a +
          κ * (modeLam M a * cellCoeff M (θ t) a) := by
  have hdrift := hu.2.2.2.2.2.1
  have hH1 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), AVenhance.IsPeriodicH1With (θ t) (D t) := by
    rw [← timeMeasure_Ioo_eq_Ioc]; exact hu.2.2.2.2.1
  filter_upwards [hH1, section_integrable_ae hdrift, ae_restrict_mem measurableSet_Ioc]
    with t htH hint htmem
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htmem.1.le, htmem.2⟩
  have hDi := htH.2.2.2.1
  -- MemL2 of the drift pairing
  have hgL2 : MemL2On AVenhance.unitCube (fun x => Homogenization.vecDot (b t x) (D t x)) := by
    have hbound : MemLp (fun x => B * (‖D t x 0‖ + ‖D t x 1‖)) 2
        (volume.restrict AVenhance.unitCube) :=
      (((hDi 0).norm).add ((hDi 1).norm)).const_mul B
    refine hbound.mono' hint.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h0 : |b t x 0| ≤ B := (Real.norm_eq_abs _ ▸ norm_le_pi_norm (b t x) 0).trans (hB t htIcc x)
    have h1 : |b t x 1| ≤ B := (Real.norm_eq_abs _ ▸ norm_le_pi_norm (b t x) 1).trans (hB t htIcc x)
    have e : Homogenization.vecDot (b t x) (D t x) = b t x 0 * D t x 0 + b t x 1 * D t x 1 := by
      simp [Homogenization.vecDot, Fin.sum_univ_two]
    rw [Real.norm_eq_abs, e]
    calc |b t x 0 * D t x 0 + b t x 1 * D t x 1|
        ≤ |b t x 0 * D t x 0| + |b t x 1 * D t x 1| := abs_add_le _ _
      _ = |b t x 0| * ‖D t x 0‖ + |b t x 1| * ‖D t x 1‖ := by
          rw [abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ B * ‖D t x 0‖ + B * ‖D t x 1‖ := by gcongr
      _ = B * (‖D t x 0‖ + ‖D t x 1‖) := by ring
  refine ⟨htH, hgL2, ?_, ?_⟩
  · unfold AVenhance.l2NormSq AVenhance.gradNormSq
    rw [← integral_const_mul]
    refine integral_mono (hgL2.integrable_sq)
      ((integrable_vecNormSq_cell hDi).const_mul _) (fun x => ?_)
    exact vecDot_sq_le (hB t htIcc x)
  · intro a
    have hψ : MemL2On AVenhance.unitCube (realFourierModeAmbient M a) :=
      weak_continuous_memL2On (realFourierModeAmbient_contDiff M a).continuous
    have h1 := weak_product_integrable_cell hgL2 hψ
    have h2 := (integrable_vecDot_gradMode hDi M a).const_mul κ
    unfold weakModeForcing cellCoeff
    rw [integral_add h1 h2, integral_const_mul, vecDot_gradMode htH M a]
    rfl

end AVenhance.Infra.FullTheorem.LemmaU

end
