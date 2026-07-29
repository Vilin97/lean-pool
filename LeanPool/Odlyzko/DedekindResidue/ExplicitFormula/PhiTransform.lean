/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.Normalisation
public import LeanPool.Odlyzko.DedekindResidue.ExplicitFormula.TestFunction

/-!
# The two-sided transform Φ of the explicit formula  (SP2-Φ)

Poitou's proof of Weil's explicit formula works with the two-sided Laplace/Mellin
transform (his eq. (2), p. 6-01):

* `Φ(s) := ∫_ℝ F(x)·e^{(s−1/2)x} dx`,

integrable in the closed band `-ε ≤ Re s ≤ 1+ε` for an admissible test function `F`
(the admissibility field `bv_integrable_exp` provides exactly the required decay).
On the critical line it recovers the paper's Fourier transform (B–F eq. (2)):
`Φ(1/2 + iγ) = F̂(γ)`, and for even `F` it satisfies the reflection `Φ(1−s) = Φ(s)`,
which folds the left contour edge onto the right one in the explicit-formula rectangle
(Poitou's `{Φ(s) + Φ(1−s)}` is `2Φ(s)` for even `F`).

## Main declarations

* `paperPhi` — the transform;
* `integrableOn_Iio_comp_neg_iff`, `integral_comp_neg_real` — reflection helpers;
* `integrableOn_Ici_mul_cexp` — the half-line domination workhorse;
* `integrable_paperPhi_kernel` — kernel integrability in the closed band;
* `paperPhi_half_add_mul_I` — `Φ(1/2+iγ) = F̂(γ)`;
* `paperPhi_one_sub` — `Φ(1−s) = Φ(s)` for even `F`.

Source: Poitou pp. 6-01/6-02 (`refs/DedekindResidue/poitou-petits-discriminants.pdf`);
B–F p. 3. Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-Φ.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex

/-- **Poitou's transform** (his eq. (2)): `Φ(s) = ∫_ℝ F(x)·e^{(s−1/2)x} dx`. -/
noncomputable def paperPhi (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp ((s - 1/2) * x)

/-- Reflection of half-line integrability through `x ↦ -x`. -/
theorem integrableOn_Iio_comp_neg_iff (G : ℝ → ℂ) :
    IntegrableOn G (Set.Iio (0:ℝ)) ↔ IntegrableOn (fun x => G (-x)) (Set.Ioi (0:ℝ)) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : volume.restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) (volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [IntegrableOn, hmap, A.integrable_map_iff]
  rfl

/-- **Half-line domination workhorse**: if `G·e^{(1/2+ε)x}` is integrable on `[0,∞)`
and `Re c ≤ 1/2 + ε`, then `G·e^{cx}` is integrable on `[0,∞)`. -/
theorem integrableOn_Ici_mul_cexp {G : ℝ → ℂ} {ε : ℝ}
    (hG : IntegrableOn (fun x : ℝ => G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
      (Set.Ici 0))
    {c : ℂ} (hc : c.re ≤ 1/2 + ε) :
    IntegrableOn (fun x : ℝ => G x * Complex.exp (c * x)) (Set.Ici 0) := by
  have hpt : ∀ x : ℝ, G x * Complex.exp (c * x)
      = (Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ))
        * (G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ)) := by
    intro x
    rw [mul_mul_mul_comm]
    rw [show ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ) * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ)
        = 1 by rw [← Complex.ofReal_mul, ← Real.exp_add]; norm_num]
    ring
  have hbd : ∀ x ∈ Set.Ici (0:ℝ),
      ‖Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ)‖ ≤ 1 := by
    intro x hx
    rw [Set.mem_Ici] at hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp, ← Real.exp_add]
    rw [show (c * (x:ℂ)).re = c.re * x by simp [Complex.mul_re]]
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have hprod : IntegrableOn (fun x : ℝ =>
      (Complex.exp (c * x) * ((Real.exp (-((1/2 + ε) * x)) : ℝ) : ℂ))
        * (G x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))) (Set.Ici 0) :=
    hG.bdd_mul ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      ((ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall hbd))
  exact hprod.congr_fun (fun x _ => (hpt x).symm) measurableSet_Ici

/-- **Φ-a: kernel integrability** in the closed band `-ε ≤ Re s ≤ 1 + ε` for an
admissible test function (with the admissibility witness `ε` made explicit). -/
theorem integrable_paperPhi_kernel {F : ℝ → ℂ} (hF : IsAdmissibleTestFn F)
    {ε : ℝ}
    (hint : IntegrableOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0))
    {s : ℂ} (hs1 : -ε ≤ s.re) (hs2 : s.re ≤ 1 + ε) :
    Integrable (fun x : ℝ => F x * Complex.exp ((s - 1/2) * x)) := by
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · -- left half-line: reflect and use evenness
    rw [integrableOn_Iio_comp_neg_iff]
    have hpt : ∀ x : ℝ, F (-x) * Complex.exp ((s - 1/2) * ((-x : ℝ) : ℂ))
        = F x * Complex.exp ((1/2 - s) * x) := by
      intro x
      rw [hF.even x]
      congr 1
      push_cast
      ring_nf
    have h1 : IntegrableOn (fun x : ℝ => F x * Complex.exp ((1/2 - s) * x))
        (Set.Ici 0) := by
      refine integrableOn_Ici_mul_cexp hint ?_
      have hre : ((1:ℂ)/2 - s).re = 1/2 - s.re := by
        rw [Complex.sub_re]
        norm_num
      rw [hre]
      linarith
    refine (h1.mono_set Set.Ioi_subset_Ici_self).congr_fun (fun x _ => ?_)
      measurableSet_Ioi
    exact (hpt x).symm
  · -- right half-line
    refine integrableOn_Ici_mul_cexp hint ?_
    have hre : (s - (1:ℂ)/2).re = s.re - 1/2 := by
      rw [Complex.sub_re]
      norm_num
    rw [hre]
    linarith

/-- **Φ-b**: on the critical line, `Φ` is the paper's Fourier transform (B–F eq. (2)):
`Φ(1/2 + iγ) = F̂(γ)`. -/
theorem paperPhi_half_add_mul_I (F : ℝ → ℂ) (γ : ℝ) :
    paperPhi F (1/2 + (γ : ℂ) * Complex.I) = paperFourierIntegral F γ := by
  rw [paperPhi, paperFourierIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have : ((1:ℂ)/2 + (γ:ℂ) * Complex.I - 1/2) * x = Complex.I * x * γ := by ring
  simp only [this]

/-- Full-line integrals are invariant under `x ↦ -x`. -/
theorem integral_comp_neg_real (f : ℝ → ℂ) : ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  calc ∫ x : ℝ, f (-x) = ∫ x, f x ∂(Measure.map (fun x : ℝ => -x) volume) :=
        (A.integral_map f).symm
    _ = ∫ x : ℝ, f x := by rw [Measure.map_neg_eq_self (volume : Measure ℝ)]

/-- **Φ-c: the reflection** `Φ(1−s) = Φ(s)` for an even test function — this folds the
left edge of Poitou's rectangle onto the right edge (his `{Φ(s) + Φ(1−s)}` is `2Φ(s)`
for even `F`). -/
theorem paperPhi_one_sub {F : ℝ → ℂ} (heven : ∀ x : ℝ, F (-x) = F x) (s : ℂ) :
    paperPhi F (1 - s) = paperPhi F s := by
  rw [paperPhi, paperPhi]
  rw [← integral_comp_neg_real (fun x : ℝ => F x * Complex.exp ((1 - s - 1/2) * x))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [heven x]
  congr 1
  push_cast
  ring_nf

/-- The two-sided majorant `‖F x‖·(e^{(1/2+ε)x} + e^{-(1/2+ε)x})` is integrable for an
admissible test function: it is the sum of the kernel norms at the band endpoints. -/
theorem integrable_admissible_majorant {F : ℝ → ℂ} (hF : IsAdmissibleTestFn F)
    {ε : ℝ} (hε : 0 < ε)
    (hint : IntegrableOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0)) :
    Integrable (fun x : ℝ =>
      ‖F x‖ * (Real.exp ((1/2 + ε) * x) + Real.exp (-((1/2 + ε) * x)))) := by
  have hR : Integrable (fun x : ℝ =>
      F x * Complex.exp ((((1 + ε : ℝ) : ℂ) - 1/2) * x)) := by
    refine integrable_paperPhi_kernel hF hint ?_ ?_
    · simp only [Complex.ofReal_re]
      linarith
    · simp only [Complex.ofReal_re]
      exact le_refl _
  have hL : Integrable (fun x : ℝ =>
      F x * Complex.exp ((((-ε : ℝ) : ℂ) - 1/2) * x)) := by
    refine integrable_paperPhi_kernel hF hint ?_ ?_
    · simp only [Complex.ofReal_re]
      exact le_refl _
    · simp only [Complex.ofReal_re]
      linarith
  have hsum := hR.norm.add hL.norm
  refine hsum.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.add_apply, norm_mul, Complex.norm_exp]
  have e1 : ((((1 + ε : ℝ) : ℂ) - 1/2) * x).re = (1/2 + ε) * x := by
    rw [show (((1 + ε : ℝ) : ℂ) - 1/2) * x = (((1/2 + ε : ℝ)) : ℂ) * x by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have e2 : ((((-ε : ℝ) : ℂ) - 1/2) * x).re = -((1/2 + ε) * x) := by
    rw [show (((-ε : ℝ) : ℂ) - 1/2) * x = ((-(1/2 + ε) * x : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
    ring
  rw [e1, e2]
  ring

/-- **Φ holomorphy** (SP2-Φ-c): in the open band `-ε < Re s < 1+ε`, `Φ` is
complex-differentiable with derivative `∫ x·F(x)·e^{(s-1/2)x} dx`. -/
theorem hasDerivAt_paperPhi {F : ℝ → ℂ} (hF : IsAdmissibleTestFn F)
    {ε : ℝ} (hε : 0 < ε)
    (hint : IntegrableOn (fun x : ℝ => F x * ((Real.exp ((1/2 + ε) * x) : ℝ) : ℂ))
        (Set.Ici 0))
    {s₀ : ℂ} (hs1 : -ε < s₀.re) (hs2 : s₀.re < 1 + ε) :
    HasDerivAt (paperPhi F)
      (∫ x : ℝ, (x : ℂ) * (F x * Complex.exp ((s₀ - 1/2) * x))) s₀ := by
  classical
  set gap : ℝ := min (s₀.re + ε) (1 + ε - s₀.re) with hgap
  have hgappos : 0 < gap := by
    rw [hgap]
    rw [lt_min_iff]
    constructor <;> linarith
  set δ : ℝ := gap / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact half_pos hgappos
  -- inside the ball, the real part keeps a margin gap/2 from the band edges
  have hband : ∀ s ∈ Metric.ball s₀ δ, |s.re - 1/2| ≤ 1/2 + ε - gap/2 := by
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [show s.re - s₀.re = (s - s₀).re by simp [Complex.sub_re]]
      exact Complex.abs_re_le_norm _
    have habs := abs_le.mp (le_of_lt (lt_of_le_of_lt hre hs))
    have hg1 : gap ≤ s₀.re + ε := by rw [hgap]; exact min_le_left _ _
    have hg2 : gap ≤ 1 + ε - s₀.re := by rw [hgap]; exact min_le_right _ _
    have hδeq : δ = gap / 2 := hδ
    rw [abs_le]
    constructor
    · linarith [habs.1]
    · linarith [habs.2]
  -- the dominating function
  have habsorb : ∀ x : ℝ, |x| * Real.exp (-((gap/2) * |x|)) ≤ 2/gap := by
    intro x
    have hgt : (0:ℝ) ≤ |x| := abs_nonneg x
    have h1 : (gap/2) * |x| ≤ Real.exp ((gap/2) * |x|) := by
      have := Real.add_one_le_exp ((gap/2) * |x|)
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    calc |x| = (2/gap) * ((gap/2) * |x|) := by field_simp
      _ ≤ (2/gap) * Real.exp ((gap/2) * |x|) := by
          refine mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2/gap * Real.exp ((gap/2) * |x|) := by ring
  set bound : ℝ → ℝ := fun x =>
    (2/gap) * (‖F x‖ * (Real.exp ((1/2 + ε) * x) + Real.exp (-((1/2 + ε) * x)))) with hbd
  have hboundint : Integrable bound :=
    (integrable_admissible_majorant hF hε hint).const_mul _
  -- pointwise derivative and its ball-uniform norm bound
  have hker_deriv : ∀ (x : ℝ) (s : ℂ), HasDerivAt (fun z => F x * Complex.exp ((z - 1/2) * x))
      ((x : ℂ) * (F x * Complex.exp ((s - 1/2) * x))) s := by
    intro x s
    have h1 : HasDerivAt (fun z : ℂ => (z - 1/2) * x) (x : ℂ) s := by
      simpa using ((hasDerivAt_id s).sub_const (1/2 : ℂ)).mul_const (x : ℂ)
    have h2 := (h1.cexp).const_mul (F x)
    have hval : F x * (Complex.exp ((s - 1/2) * x) * (x:ℂ))
        = (x : ℂ) * (F x * Complex.exp ((s - 1/2) * x)) := by ring
    rw [hval] at h2
    exact h2
  have hker_deriv_bound : ∀ x : ℝ, ∀ s ∈ Metric.ball s₀ δ,
      ‖(x : ℂ) * (F x * Complex.exp ((s - 1/2) * x))‖ ≤ bound x := by
    intro x s hs
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : ((s - 1/2) * (x:ℂ)).re = (s.re - 1/2) * x := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [hre]
    have h1 : (s.re - 1/2) * x ≤ (1/2 + ε - gap/2) * |x| := by
      calc (s.re - 1/2) * x ≤ |(s.re - 1/2) * x| := le_abs_self _
        _ = |s.re - 1/2| * |x| := abs_mul _ _
        _ ≤ (1/2 + ε - gap/2) * |x| :=
            mul_le_mul_of_nonneg_right (hband s hs) (abs_nonneg x)
    have h2 : Real.exp ((s.re - 1/2) * x) ≤ Real.exp ((1/2 + ε - gap/2) * |x|) :=
      Real.exp_le_exp.mpr h1
    have h3 : |x| * Real.exp ((1/2 + ε - gap/2) * |x|)
        ≤ (2/gap) * Real.exp ((1/2 + ε) * |x|) := by
      have hkey := habsorb x
      have hexp : (1/2 + ε - gap/2) * |x| = (-((gap/2) * |x|)) + (1/2 + ε) * |x| := by
        ring
      calc |x| * Real.exp ((1/2 + ε - gap/2) * |x|)
          = (|x| * Real.exp (-((gap/2) * |x|))) * Real.exp ((1/2 + ε) * |x|) := by
            rw [hexp, Real.exp_add, ← mul_assoc]
        _ ≤ (2/gap) * Real.exp ((1/2 + ε) * |x|) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    have h4 : Real.exp ((1/2 + ε) * |x|)
        ≤ Real.exp ((1/2 + ε) * x) + Real.exp (-((1/2 + ε) * x)) := by
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        linarith [Real.exp_pos (-((1/2 + ε) * x))]
      · rw [abs_of_neg hx]
        rw [show (1/2 + ε) * -x = -((1/2 + ε) * x) by ring]
        linarith [Real.exp_pos ((1/2 + ε) * x)]
    calc |x| * (‖F x‖ * Real.exp ((s.re - 1/2) * x))
        ≤ |x| * (‖F x‖ * Real.exp ((1/2 + ε - gap/2) * |x|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
          exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖F x‖ * (|x| * Real.exp ((1/2 + ε - gap/2) * |x|)) := by ring
      _ ≤ ‖F x‖ * ((2/gap) * Real.exp ((1/2 + ε) * |x|)) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ ≤ ‖F x‖ * ((2/gap) * (Real.exp ((1/2 + ε) * x) + Real.exp (-((1/2 + ε) * x)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = bound x := by rw [hbd]; ring
  -- the dominated-differentiation theorem
  have hballmem : Metric.ball s₀ δ ∈ nhds s₀ := Metric.ball_mem_nhds s₀ hδpos
  have hmeas : ∀ᶠ s in nhds s₀, AEStronglyMeasurable
      (fun x : ℝ => F x * Complex.exp ((s - 1/2) * x)) volume := by
    filter_upwards [hballmem] with s hs
    have := hband s hs
    have habs := abs_le.mp this
    exact (integrable_paperPhi_kernel hF hint (by linarith [habs.1])
      (by linarith [habs.2])).aestronglyMeasurable
  have hint₀ : Integrable (fun x : ℝ => F x * Complex.exp ((s₀ - 1/2) * x)) :=
    integrable_paperPhi_kernel hF hint (le_of_lt hs1) (le_of_lt hs2)
  have hF'meas : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ) * (F x * Complex.exp ((s₀ - 1/2) * x))) volume := by
    refine AEStronglyMeasurable.mul ?_ hint₀.aestronglyMeasurable
    exact Continuous.aestronglyMeasurable (by fun_prop)
  have hlip : ∀ᵐ x : ℝ ∂volume, LipschitzOnWith (Real.nnabs (bound x))
      (fun s => F x * Complex.exp ((s - 1/2) * x)) (Metric.ball s₀ δ) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hconv : Convex ℝ (Metric.ball s₀ δ) := convex_ball s₀ δ
    refine hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun s => (x : ℂ) * (F x * Complex.exp ((s - 1/2) * x)))
      (fun s hs => ((hker_deriv x s).hasDerivWithinAt)) (fun s hs => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    refine le_trans (hker_deriv_bound x s hs) (le_abs_self _)
  have := hasDerivAt_integral_of_dominated_loc_of_lip hballmem hmeas hint₀ hF'meas
    hlip hboundint (Filter.Eventually.of_forall (fun x => hker_deriv x s₀))
  exact this.2

end DedekindResidue

end
