/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Holder Triple Products

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace CKN.Foundation.Measure

/-- Hölder's inequality for the exponent triple `(2, 3; 6/5)`: for `f ∈ L²` and `g ∈ L³`,
the product `f·g` is in `L^{6/5}` with the corresponding norm bound. -/
theorem eLpNorm_mul_le_two_three {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal (6 / 5 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (2 : ℝ)) μ * eLpNorm g (ENNReal.ofReal (3 : ℝ)) μ := by
  have htriple : (ENNReal.ofReal (2 : ℝ)).HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (6 / 5 : ℝ)) := by
    have h : (2 : ℝ).HolderTriple 3 (6 / 5 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g)
    (p := ENNReal.ofReal (2 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
    (r := ENNReal.ofReal (6 / 5 : ℝ)) (b := fun a b : ℝ => a * b)
    (c := (1 : NNReal)) (by exact continuous_mul) hf hg (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  simpa using h

/-- Hölder's inequality for the exponent triple `(3, 3; 3/2)`: for `f, g ∈ L³`,
the product `f·g` is in `L^{3/2}` with the corresponding norm bound. -/
theorem eLpNorm_mul_le_three_three {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (3 : ℝ)) μ * eLpNorm g (ENNReal.ofReal (3 : ℝ)) μ := by
  have htriple : (ENNReal.ofReal (3 : ℝ)).HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : (3 : ℝ).HolderTriple 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    exact h.ennrealOfReal
  have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (μ := μ) (f := f) (g := g)
    (p := ENNReal.ofReal (3 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
    (r := ENNReal.ofReal (3 / 2 : ℝ)) (b := fun a b : ℝ => a * b)
    (c := (1 : NNReal)) (by exact continuous_mul) hf hg (by
      filter_upwards [] with x
      simp only [one_mul]
      simp [nnnorm_mul])
  simpa using h

/-- Multiplying an Lᵖ function by an a.e.-bounded function `a` with `|a| ≤ C` a.e.
preserves the Lᵖ norm up to a factor of `C`. -/
theorem eLpNorm_mul_le_ofReal_mul {a f : α → ℝ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hf : AEStronglyMeasurable f μ)
    (hC : 0 ≤ C) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) {p : ℝ≥0∞} :
    eLpNorm (fun x => a x * f x) p μ ≤ ENNReal.ofReal C * eLpNorm f p μ := by
  have hmono : eLpNorm (fun x => a x * f x) p μ ≤
      eLpNorm (fun x => C * f x) p μ := by
    apply eLpNorm_mono_ae (ha.mul hf)
    filter_upwards [haC] with x hx
    change |a x * f x| ≤ |C * f x|
    rw [abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))
  have hsmul : (fun x => C * f x) = C • f := by
    funext x
    rfl
  rw [hsmul, eLpNorm_const_smul] at hmono
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC] using hmono

end CKN.Foundation.Measure
