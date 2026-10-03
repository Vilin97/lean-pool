/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Ordered spatial words connect to the stream-regularity barNorm carrier. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Ordered words are the coordinate evaluations of the Frechet jets. -/
theorem iterateSpatialWord_eq_iteratedFDeriv {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) :
    iterateSpatialWord w f = fun x => iteratedFDeriv ℝ w.length f x
      (fun j => basisVec (w.get j)) := by
  induction w with
  | nil =>
    funext x
    simp [iterateSpatialWord, iteratedFDeriv_zero_apply]
  | cons i w ih =>
    simp only [iterateSpatialWord, ih]
    funext x
    have hd := hf.differentiable_iteratedFDeriv (m := w.length) (WithTop.coe_lt_coe.mpr
        (ENat.natCast_lt_top _)) x
    have he := ordered_derivative_eq_gradient_component
      (fun j : Fin (w.length + 1) => (i :: w).get j) hd
    simpa only [List.length_cons, List.get_cons_zero, List.get_eq_getElem,
      Fin.val_succ, Fin.val_zero, List.getElem_cons_zero, List.getElem_cons_succ] using he.symm

/-- Continuity turns a volume essential-supremum bound into a pointwise bound. -/
theorem iterate_continuous_enorm_le_eLpNorm_top {f : Vec 2 → ℝ}
    (hf : Continuous f) (x : Vec 2) : ‖f x‖ₑ ≤ eLpNorm f ⊤ volume := by
  have hae : ∀ᵐ y ∂(volume : Measure (Vec 2)), ‖f y‖ₑ ≤ eLpNorm f ⊤ volume :=
    ae_le_eLpNormEssSup.mono (fun _ h => h.trans eLpNormEssSup_le_eLpNorm_top)
  have hd := Measure.dense_of_ae hae
  have hc : IsClosed {y : Vec 2 | ‖f y‖ₑ ≤ eLpNorm f ⊤ volume} :=
    isClosed_le hf.enorm continuous_const
  have hs := hc.closure_subset
  rw [hd.closure_eq] at hs
  exact hs (Set.mem_univ x)

/-- Literal barNorm bounds supply every actual ordered spatial jet pointwise.
The ENNReal normalization is retained exactly as in the definition. -/
theorem iterate_word_enorm_bound_of_barNorm {f : Vec 2 → ℝ} {R B : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R)
    (w : List (Fin 2)) (hbar : barNorm w.length R f ≤ ENNReal.ofReal B) (x : Vec 2) :
    ‖iterateSpatialWord w f x‖ₑ ≤ ENNReal.ofReal B /
      (ENNReal.ofReal (((w.length : ℝ) + 1) ^ 2 / (w.length.factorial : ℝ)) *
        (ENNReal.ofReal R)⁻¹ ^ w.length) := by
  have hn := barNorm_coordinate_eLpNorm_le hR hbar (fun j => w.get j)
  rw [← iterateSpatialWord_eq_iteratedFDeriv hf w] at hn
  exact (iterate_continuous_enorm_le_eLpNorm_top (iterateSpatialWord_smooth hf w).continuous
      x).trans hn

/-- Real form of the barNorm jet bound, with its exact analytic normalization. -/
theorem iterate_word_abs_bound_of_barNorm {f : Vec 2 → ℝ} {R B : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hB : 0 ≤ B)
    (w : List (Fin 2)) (hbar : barNorm w.length R f ≤ ENNReal.ofReal B) (x : Vec 2) :
    |iterateSpatialWord w f x| ≤ B /
      ((((w.length : ℝ) + 1) ^ 2 / (w.length.factorial : ℝ)) * R⁻¹ ^ w.length) := by
  have hcoef : 0 < ((w.length : ℝ) + 1) ^ 2 / (w.length.factorial : ℝ) := by positivity
  have hden : ENNReal.ofReal (((w.length : ℝ) + 1) ^ 2 / (w.length.factorial : ℝ)) *
      (ENNReal.ofReal R)⁻¹ ^ w.length ≠ 0 := by
    apply mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hcoef)
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  have h := ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) hden)
    (iterate_word_enorm_bound_of_barNorm hf hR w hbar x)
  simpa only [toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hB, ENNReal.toReal_ofReal hcoef.le,
    ENNReal.toReal_ofReal hR.le] using h

/-- The real analytic normalization is a factorial times the radius power. -/
theorem iterate_word_abs_factorial_bound_of_barNorm {f : Vec 2 → ℝ} {R B : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hB : 0 ≤ B)
    (w : List (Fin 2)) (hbar : barNorm w.length R f ≤ ENNReal.ofReal B) (x : Vec 2) :
    |iterateSpatialWord w f x| ≤
      B * (w.length.factorial : ℝ) * R ^ w.length / ((w.length : ℝ) + 1) ^ 2 := by
  have h := iterate_word_abs_bound_of_barNorm hf hR hB w hbar x
  have hn : (w.length : ℝ) + 1 ≠ 0 := by positivity
  have hfac : (w.length.factorial : ℝ) ≠ 0 := by positivity
  have heq : B / ((((w.length : ℝ) + 1) ^ 2 / (w.length.factorial : ℝ)) * R⁻¹ ^ w.length) =
      B * (w.length.factorial : ℝ) * R ^ w.length / ((w.length : ℝ) + 1) ^ 2 := by
    field_simp
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel hR.ne', one_pow, mul_one]
  rwa [heq] at h

end AVenhance.Infra.Section4
