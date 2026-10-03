/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Bounded holomorphic families and Cayley transforms

Cauchy estimates control bounded families; Cayley transforms apply them to the half-plane.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ### Weak Montel: equicontinuity from a uniform bound

The Cauchy estimate bounds the derivative of a bounded holomorphic function, which makes a
uniformly bounded family uniformly Lipschitz on a smaller ball. For the exponential iterates
this is enough: if no image of `V` meets the real axis then each image, being connected, lies
in one open half-plane, and a Möbius transformation makes the family bounded. -/

/-- Cauchy's estimate: a holomorphic function bounded by `M` has `‖deriv f z‖ ≤ M / r`
whenever `closedBall z r` lies in the domain. -/
theorem norm_deriv_le_of_bounded
    {f : ℂ → ℂ} {U : Set ℂ} {M r : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hzr : closedBall z r ⊆ U)
    (hb : ∀ w ∈ U, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by
  rw [← Complex.cderiv_eq_deriv hU hf hr hzr]
  exact Complex.norm_cderiv_le hr
    (fun w hw => hb w (hzr (sphere_subset_closedBall hw)))

/-- A holomorphic function bounded by `M` on `ball c (2ρ)` is `2M/ρ`-Lipschitz on `ball c ρ`. -/
theorem norm_sub_le_of_bounded
    {f : ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball c (2 * ρ)))
    (hb : ∀ w ∈ ball c (2 * ρ), ‖f w‖ ≤ M)
    {x y : ℂ} (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) :
    ‖f x - f y‖ ≤ (2 * M / ρ) * ‖x - y‖ := by
  have hsub : ball c ρ ⊆ ball c (2 * ρ) := by
    intro v hv
    rw [Metric.mem_ball] at hv ⊢
    linarith
  have hder : ∀ v ∈ ball c ρ, HasFDerivWithinAt f
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f v)) (ball c ρ) v := by
    intro v hv
    exact (((hf.differentiableAt
      (isOpen_ball.mem_nhds (hsub hv))).hasDerivAt).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ v ∈ ball c ρ,
      ‖ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f v)‖ ≤ 2 * M / ρ := by
    intro v hv
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
    have hvb : dist v c < ρ := by rwa [Metric.mem_ball] at hv
    have hball : closedBall v (ρ / 2) ⊆ ball c (2 * ρ) := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      rw [Metric.mem_ball]
      calc dist w c ≤ dist w v + dist v c := dist_triangle _ _ _
        _ < 2 * ρ := by linarith
    have hcauchy := norm_deriv_le_of_bounded isOpen_ball hf
      (by linarith : (0 : ℝ) < ρ / 2) hball hb
    calc ‖deriv f v‖ ≤ M / (ρ / 2) := hcauchy
      _ = 2 * M / ρ := by field_simp
  exact (convex_ball c ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hy hx

/-- **Weak Montel, equicontinuity form.** A uniformly bounded family of holomorphic functions
on `ball c (2ρ)` is equicontinuous on `ball c ρ`, with a modulus independent of the index. -/
theorem equicontinuous_of_bounded
    {ι : Type*} {F : ι → ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) (ball c (2 * ρ)))
    (hb : ∀ i, ∀ w ∈ ball c (2 * ρ), ‖F i w‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i : ι, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      ‖x - y‖ < δ → ‖F i x - F i y‖ < ε := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0⟩ := hne
    have hM : 0 ≤ M :=
      le_trans (norm_nonneg _) (hb i0 c (Metric.mem_ball_self (by linarith)))
    have hpos : 0 < 2 * M / ρ + 1 := by positivity
    refine ⟨ε / (2 * M / ρ + 1), by positivity, ?_⟩
    intro i x hx y hy hxy
    have h1 := norm_sub_le_of_bounded hρ (hF i) (hb i) hx hy
    have h2 : (2 * M / ρ) * ‖x - y‖ < ε := by
      have hcoef : (0 : ℝ) ≤ 2 * M / ρ := by positivity
      have := mul_le_mul_of_nonneg_left (le_of_lt hxy) hcoef
      calc (2 * M / ρ) * ‖x - y‖
          ≤ (2 * M / ρ) * (ε / (2 * M / ρ + 1)) := this
        _ < ε := by
            rw [mul_div_assoc']
            rw [div_lt_iff₀ hpos]
            nlinarith [hε]
    linarith
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩

/-! ### The Cayley transform, used to bound the family

If no image of `V` meets the real axis then each image, being connected, lies in one open
half-plane. A Cayley transform carries that half-plane into the unit disc, making the
transformed family uniformly bounded, so `equicontinuous_of_bounded` applies. -/

/-- `z ↦ (z - i)/(z + i)` maps the upper half-plane into the unit disc. -/
theorem norm_cayleyUp_lt_one {z : ℂ} (hz : 0 < z.im) :
    ‖(z - Complex.I) / (z + Complex.I)‖ < 1 := by
  have hlt : ‖z - Complex.I‖ < ‖z + Complex.I‖ := by
    have hsq : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
      nlinarith [hz]
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I), hsq]
  rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) hlt)]
  exact hlt

/-- `z ↦ (z + i)/(z - i)` maps the lower half-plane into the unit disc. -/
theorem norm_cayleyDown_lt_one {z : ℂ} (hz : z.im < 0) :
    ‖(z + Complex.I) / (z - Complex.I)‖ < 1 := by
  have hupper := norm_cayleyUp_lt_one (z := -z) (by simpa using hz)
  simpa only [show -z - Complex.I = -(z + Complex.I) by ring,
    show -z + Complex.I = -(z - Complex.I) by ring, neg_div_neg_eq] using hupper

/-- The Cayley transform of the upper half-plane is inverted by `u ↦ i(1+u)/(1-u)`. -/
theorem cayleyUp_inv {w : ℂ} (hw : w + Complex.I ≠ 0) :
    Complex.I * (1 + (w - Complex.I) / (w + Complex.I))
      / (1 - (w - Complex.I) / (w + Complex.I)) = w := by
  have h1 : 1 + (w - Complex.I) / (w + Complex.I) = 2 * w / (w + Complex.I) := by
    field_simp
    ring
  have h2 : 1 - (w - Complex.I) / (w + Complex.I)
      = 2 * Complex.I / (w + Complex.I) := by
    field_simp
    ring
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rw [h1, h2]
  field_simp

/-- The Cayley transform of the lower half-plane is inverted by `u ↦ i(u+1)/(u-1)`. -/
theorem cayleyDown_inv {w : ℂ} (hw : w - Complex.I ≠ 0) :
    Complex.I * (1 + (w + Complex.I) / (w - Complex.I))
      / ((w + Complex.I) / (w - Complex.I) - 1) = w := by
  have hden : -w + Complex.I ≠ 0 := by
    intro h
    apply hw
    linear_combination -h
  have hupper := cayleyUp_inv hden
  rw [show -w - Complex.I = -(w + Complex.I) by ring,
    show -w + Complex.I = -(w - Complex.I) by ring, neg_div_neg_eq] at hupper
  rw [show (w + Complex.I) / (w - Complex.I) - 1 =
    -(1 - (w + Complex.I) / (w - Complex.I)) by ring, div_neg, hupper, neg_neg]

/-- The denominator of the upper-half-plane Cayley transform does not vanish there. -/
theorem add_I_ne_zero {z : ℂ} (h : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro hc
  have him : (z + Complex.I).im = 0 := by rw [hc, Complex.zero_im]
  simp only [Complex.add_im, Complex.I_im] at him
  linarith

/-- The denominator of the lower-half-plane Cayley transform does not vanish there. -/
theorem sub_I_ne_zero {z : ℂ} (h : z.im < 0) : z - Complex.I ≠ 0 := by
  have hupper := add_I_ne_zero (z := -z) (by simpa using h)
  simpa only [show -z + Complex.I = -(z - Complex.I) by ring, neg_ne_zero] using hupper

/-- **Each image lies wholly in one open half-plane.** If no forward image of the connected
set `V` meets the real axis, then for each `n` the image is entirely in the upper half-plane
or entirely in the lower one — by the intermediate value theorem applied to `Im`. -/
theorem image_in_half_plane {V : Set ℂ} (hVconn : IsConnected V)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) (n : ℕ) :
    (∀ z ∈ V, 0 < (expIterate n z).im) ∨ (∀ z ∈ V, (expIterate n z).im < 0) := by
  have hcont : ContinuousOn (fun y => (expIterate n y).im) V :=
    (Complex.continuous_im.comp (continuous_expIterate n)).continuousOn
  by_cases hpos : ∀ z ∈ V, 0 < (expIterate n z).im
  · exact Or.inl hpos
  refine Or.inr ?_
  push Not at hpos
  obtain ⟨b, hb, hble⟩ := hpos
  have hbneg : (expIterate n b).im < 0 := lt_of_le_of_ne hble (hnoreal n b hb)
  intro z hz
  by_contra hzge
  push Not at hzge
  have hzpos : 0 < (expIterate n z).im :=
    lt_of_le_of_ne hzge (Ne.symm (hnoreal n z hz))
  obtain ⟨y, hy, hyval⟩ :=
    hVconn.isPreconnected.intermediate_value hb hz hcont
      ⟨le_of_lt hbneg, le_of_lt hzpos⟩
  exact hnoreal n y hy hyval

/-- The Cayley transform of an iterate is holomorphic wherever the iterate has positive
imaginary part. -/
theorem differentiableOn_cayleyUp {U : Set ℂ} {n : ℕ}
    (hpos : ∀ z ∈ U, 0 < (expIterate n z).im) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w - Complex.I) / (expIterate n w + Complex.I)) U := by
  intro z hz
  have h1 : DifferentiableAt ℂ (expIterate n) z := differentiable_expIterate n z
  exact (((h1.sub_const _).div (h1.add_const _)
    (add_I_ne_zero (hpos z hz)))).differentiableWithinAt

/-- The lower-half-plane Cayley transform of an iterate is holomorphic wherever
that iterate has negative imaginary part. -/
theorem differentiableOn_cayleyDown {U : Set ℂ} {n : ℕ}
    (hneg : ∀ z ∈ U, (expIterate n z).im < 0) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w + Complex.I) / (expIterate n w - Complex.I)) U := by
  intro z hz
  have h1 : DifferentiableAt ℂ (expIterate n) z := differentiable_expIterate n z
  exact (((h1.add_const _).div (h1.sub_const _)
    (sub_I_ne_zero (hneg z hz)))).differentiableWithinAt

/-- **The transformed family is uniformly bounded, hence equicontinuous.** Along any set of
times whose images all lie in the upper half-plane, the Cayley transforms of the iterates are
bounded by `1` on `ball c (2ρ)`, so `equicontinuous_of_bounded` applies on `ball c ρ`. -/
theorem equicontinuous_cayleyUp {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {T : Set ℕ} (hT : ∀ n ∈ T, ∀ z ∈ ball c (2 * ρ), 0 < (expIterate n z).im)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n : T, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ, ‖x - y‖ < δ →
      ‖(expIterate n.1 x - Complex.I) / (expIterate n.1 x + Complex.I)
        - (expIterate n.1 y - Complex.I) / (expIterate n.1 y + Complex.I)‖ < ε := by
  refine equicontinuous_of_bounded (F := fun n : T => fun w =>
      (expIterate n.1 w - Complex.I) / (expIterate n.1 w + Complex.I)) hρ
    (fun n => differentiableOn_cayleyUp (fun z hz => hT n.1 n.2 z hz))
    (fun n w hw => le_of_lt (norm_cayleyUp_lt_one (hT n.1 n.2 w hw))) hε

/-- The Cayley transform never takes the value `1`. -/
theorem cayleyUp_ne_one {w : ℂ} (hw : w + Complex.I ≠ 0) :
    (w - Complex.I) / (w + Complex.I) ≠ 1 := by
  intro h
  rw [div_eq_one_iff_eq hw] at h
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, Complex.I_ne_zero, or_self] at h2

/-- **Push-back.** Near a finite point `p ≠ -i`, closeness of Cayley
transforms gives closeness of the points themselves. This is what converts the equicontinuity
of the transformed family back into Euclidean information about the iterates. -/
theorem norm_sub_lt_of_cayley_close
    {p : ℂ} (hp : p + Complex.I ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ w : ℂ, w + Complex.I ≠ 0 →
      ‖(w - Complex.I) / (w + Complex.I) - (p - Complex.I) / (p + Complex.I)‖ < ε →
      ‖w - p‖ < η := by
  have hne : (1 : ℂ) - (p - Complex.I) / (p + Complex.I) ≠ 0 := by
    intro hc
    refine cayleyUp_ne_one hp ?_
    linear_combination -hc
  have hcont : ContinuousAt (fun u : ℂ => Complex.I * (1 + u) / (1 - u))
      ((p - Complex.I) / (p + Complex.I)) := by
    refine ContinuousAt.div ?_ ?_ hne
    · exact (continuous_const.mul (continuous_const.add continuous_id)).continuousAt
    · exact (continuous_const.sub continuous_id).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ε, hε, hball⟩ := hcont η hη
  refine ⟨ε, hε, fun w hw hclose => ?_⟩
  have hd : dist ((w - Complex.I) / (w + Complex.I))
      ((p - Complex.I) / (p + Complex.I)) < ε := by
    rwa [dist_eq_norm]
  have h1 := hball hd
  rw [dist_eq_norm, cayleyUp_inv hw, cayleyUp_inv hp] at h1
  exact h1

end

end ExponentialJuliaSetMisiurewicz
