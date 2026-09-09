/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothApproximation

@[expose] public section

/-! Actual all-order translation regularity from ordinary square-integrable spatial derivatives. -/

noncomputable section


namespace EulerLpTranslation

open MeasureTheory EulerSmoothLimit EulerLpDerivative Filter
open scoped ContDiff Topology

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivativeMap_translation (D : L2Space (Space →L[ℝ] V)) (a : Space) :
    derivativeMap volume (translation a D) =
      (translation a).toContinuousLinearMap.comp (derivativeMap volume D) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [derivativeMap_ae volume (translation a D) v, translation_ae a D,
    translation_ae a (derivativeMap volume D v),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (derivativeMap_ae volume D v)] with x hm ht hv hd
  change derivativeMap volume (translation a D) v x = translation a (derivativeMap volume D v) x
  rw [hm, ht, hv, hd]

/-- The hypotheses are ordinary derivatives of a concrete smooth function, not translation-orbit regularity. -/
structure SmoothL2Field (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : Space → V
  smooth : ContDiff ℝ ∞ field
  integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume

namespace SmoothL2Field

theorem memLp (A : SmoothL2Field V) : MemLp A.field 2 volume :=
  (A.integrable 0).congr_norm A.smooth.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_iteratedFDeriv_zero))

def toLp (A : SmoothL2Field V) : L2Space V := A.memLp.toLp A.field

theorem toLp_ae (A : SmoothL2Field V) : A.toLp =ᵐ[volume] A.field := A.memLp.coeFn_toLp

def jetLp (A : SmoothL2Field V) (n : ℕ) : L2Space (Space [×n]→L[ℝ] V) :=
  (A.integrable n).toLp (iteratedFDeriv ℝ n A.field)

def derivative (A : SmoothL2Field V) : SmoothL2Field (Space →L[ℝ] V) where
  field := fderiv ℝ A.field
  smooth := A.smooth.fderiv_right (m := ∞) (by simp)
  integrable n := (A.integrable (n+1)).congr_norm
    ((A.smooth.fderiv_right (m := ∞) (by simp)).continuous_iteratedFDeriv (by
      simp)).aestronglyMeasurable
    (Eventually.of_forall (fun x => norm_iteratedFDeriv_fderiv.symm))

theorem translation_hasFDerivAt (A : SmoothL2Field V) (a : Space) :
    HasFDerivAt (fun b : Space => translation b A.toLp)
      (derivativeMap volume (translation a A.derivative.toLp)) a := by
  rw [derivativeMap_translation]
  exact translation_hasFDerivAt_all A.toLp (derivativeMap volume A.derivative.toLp)
    (smooth_hasFDerivAt A.field A.smooth A.memLp A.derivative.memLp) a

theorem translation_fderiv (A : SmoothL2Field V) :
    fderiv ℝ (fun a : Space => translation a A.toLp) =
      fun a => derivativeBundling volume (translation a A.derivative.toLp) :=
  funext (fun a => (A.translation_hasFDerivAt a).fderiv)

private theorem translation_contDiff_nat_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V),
      ContDiff ℝ n (fun a : Space => translation a A.toLp) := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (translation_continuous A.toLp)
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.translation_hasFDerivAt a).differentiableAt, by simp, ?_⟩
    rw [A.translation_fderiv]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : WithTop ℕ∞))
      (E := L2Space (Space →L[ℝ] V)) (F := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)).comp (ih (Space →L[ℝ] V) A.derivative)

/-- Genuine all-order smoothness of the translation orbit follows from the ordinary spatial L² jets. -/
theorem translation_contDiff (A : SmoothL2Field V) :
    ContDiff ℝ ∞ (fun a : Space => translation a A.toLp) :=
  contDiff_infty.mpr (fun n => translation_contDiff_nat_aux n V A)

theorem norm_jetLp_zero (A : SmoothL2Field V) : ‖A.jetLp 0‖ = ‖A.toLp‖ := by
  simp only [jetLp, toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall (fun x => norm_iteratedFDeriv_zero))

theorem norm_derivative_jetLp (A : SmoothL2Field V) (n : ℕ) :
    ‖A.derivative.jetLp n‖ = ‖A.jetLp (n+1)‖ := by
  simp only [jetLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall (fun x => norm_iteratedFDeriv_fderiv))

private theorem norm_iteratedFDeriv_translation_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V) (a : Space),
      ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero, (translation a).norm_map, A.norm_jetLp_zero]
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.translation_fderiv]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
      (F := L2Space (Space →L[ℝ] V)) (G := Space →L[ℝ] L2Space V)
      (derivativeBundling volume)
      (A.derivative.translation_contDiff.contDiffAt (x := a)) (n := n) (by simp)
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := Space) (V := V) volume) (norm_nonneg _)).trans
      (by simpa only [one_mul, A.norm_derivative_jetLp n] using ih (Space →L[ℝ] V) A.derivative a))

/-- Translation jets are controlled with constant one by the actual ordinary spatial L² jets. -/
theorem norm_iteratedFDeriv_translation_le (A : SmoothL2Field V) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translation b A.toLp) a‖ ≤ ‖A.jetLp n‖ :=
  norm_iteratedFDeriv_translation_aux n V A a

end SmoothL2Field

end EulerLpTranslation
