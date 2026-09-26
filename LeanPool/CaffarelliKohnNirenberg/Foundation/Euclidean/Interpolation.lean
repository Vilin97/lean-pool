/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationBasic

/-!
# Marcinkiewicz interpolation between weak `(1,1)` and strong `(2,2)`

For a sublinear operator `T` on functions `Vec3 → ℝ` that is of weak type
`(1,1)` with constant `A₁` and of strong type `(2,2)` with constant `A₂`, the
interpolation theorem `interpolation_weak11_strong22` gives the strong `(p,p)`
bound with the explicit constant `p · 2^p · (A₁/(p-1) + A₂²/(2-p))` for every
`1 < p < 2`.  The exponents `p = 3/2` and `p = 6/5` are recorded as corollaries.

The analytic ingredients — the distribution-function estimate obtained by
truncating at level `t/2`, and its layer-cake integral against the weight
`p t^{p-1}` — are in `InterpolationBasic.lean`.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- **Marcinkiewicz interpolation.**  A sublinear operator `T` that is of weak type
`(1,1)` with constant `A₁` and of strong type `(2,2)` with constant `A₂` satisfies the
strong `(p,p)` bound for every `1 < p < 2`, with the explicit constant
`p · 2^p · (A₁/(p-1) + A₂²/(2-p))`.  This is the distribution-function estimate at the
level `t`, integrated against the layer-cake weight `p t^{p-1}`. -/
theorem interpolation_weak11_strong22 {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hweak : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤ ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) {f : Vec3 → ℝ} (hf : Measurable f) :
    ∫⁻ x, absE (T f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hM : Measurable (absE f) := measurable_absE hf
  have hMfin : ∀ x, absE f x < ∞ := fun _ => ENNReal.ofReal_lt_top
  let _ : SFinite (volume : Measure Vec3) := inferInstance
  have hF1 : AEMeasurable (fun t : ℝ => ENNReal.ofReal (2 * A₁) *
      (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_weightedHighIntegrand hM (p := p)).lintegral_prod_right.congr
      (Eventually.of_forall fun t => inner_High_eq hM t)).const_mul _
  calc ∫⁻ x, absE (T f) x ^ p
      = ∫⁻ t in Ioi (0 : ℝ), volume {x | t < |T f x|} * ENNReal.ofReal (p * t ^ (p - 1)) :=
        layer_cake (hTmeas f hf) hp1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
            ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) *
          ENNReal.ofReal (p * t ^ (p - 1)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_le_mul_left (tail_bound hTsub hTmeas hweak hstrong hf ht) _
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t) +
            ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [interp_integrand hA₁ hp1 ht, ← rpowExt_eq (a := p - 2) ht,
          ← rpowExt_eq (a := p - 3) ht]
    _ = ENNReal.ofReal p *
          ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t)) +
            (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t))) := by
        rw [lintegral_add_left' hF1]
    _ = ENNReal.ofReal p *
          (ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) *
            ∫⁻ x, absE f x ^ p) := by
        rw [weighted_combined hM hMfin hA₁ hp1 hp2]
    _ = ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
          ∫⁻ x, absE f x ^ p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp0]

/-- Interpolation at the exponent `p = 3/2`: weak `(1,1)` and strong `(2,2)` estimates
give the strong `(3/2,3/2)` estimate, with the constant of
`interpolation_weak11_strong22` specialized to `p = 3/2`. -/
theorem interpolation_weak11_strong22_threeHalves {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hweak : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤ ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) {f : Vec3 → ℝ} (hf : Measurable f) :
    ∫⁻ x, absE (T f) x ^ ((3 : ℝ) / 2) ≤
      ENNReal.ofReal ((3 : ℝ) / 2 * (2 ^ ((3 : ℝ) / 2) *
        (A₁ / ((3 : ℝ) / 2 - 1) + A₂ ^ 2 / (2 - (3 : ℝ) / 2)))) *
        ∫⁻ x, absE f x ^ ((3 : ℝ) / 2) :=
  interpolation_weak11_strong22 hTsub hTmeas hweak hstrong hA₁ (by norm_num) (by norm_num) hf

/-- Interpolation at the exponent `p = 6/5`: weak `(1,1)` and strong `(2,2)` estimates
give the strong `(6/5,6/5)` estimate, with the constant of
`interpolation_weak11_strong22` specialized to `p = 6/5`. -/
theorem interpolation_weak11_strong22_sixFifths {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hweak : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤ ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) {f : Vec3 → ℝ} (hf : Measurable f) :
    ∫⁻ x, absE (T f) x ^ ((6 : ℝ) / 5) ≤
      ENNReal.ofReal ((6 : ℝ) / 5 * (2 ^ ((6 : ℝ) / 5) *
        (A₁ / ((6 : ℝ) / 5 - 1) + A₂ ^ 2 / (2 - (6 : ℝ) / 5)))) *
        ∫⁻ x, absE f x ^ ((6 : ℝ) / 5) :=
  interpolation_weak11_strong22 hTsub hTmeas hweak hstrong hA₁ (by norm_num) (by norm_num) hf

end CKN.Foundation.Euclidean
