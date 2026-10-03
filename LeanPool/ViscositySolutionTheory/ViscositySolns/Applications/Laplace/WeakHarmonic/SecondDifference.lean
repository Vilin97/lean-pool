/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Coordinate second differences and the trace Laplacian

For a function `f : R^n -> R` and a step `h`, the coordinate second-difference
Laplacian is

`Δ_h f(x) = h⁻² ∑ i, (f(x + h eᵢ) + f(x - h eᵢ) - 2 f(x))`.

This file proves the facts about `Δ_h` needed to pass from viscosity to
distributional subharmonicity:

* for a `C²` function `χ` with compact support, `Δ_h χ → Δχ` uniformly as
  `h → 0`, where `Δχ = lapTrace χ` is the trace of the second Fréchet
  derivative (`exists_forall_abs_coordSecondDifference_sub_lapTrace_le`);
* consequently `∫ w Δ_h χ → ∫ w Δχ` for continuous `w`
  (`tendsto_integral_mul_coordSecondDifference`);
* the discrete integration by parts `∫ (Δ_h f) g = ∫ f (Δ_h g)`, a consequence
  of translation invariance of Lebesgue measure
  (`integral_coordSecondDifference_mul`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace ViscositySolns

variable {n : Nat}

/--
The trace Laplacian `Δχ(x) = ∑ i, D²χ(x)(eᵢ, eᵢ)`, computed from the second
Fréchet derivative of `χ`.
-/
def lapTrace (χ : Point n → ℝ) (x : Point n) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ χ) x (Pi.single i 1) (Pi.single i 1)

/-- The central second difference `f(x + v) + f(x - v) - 2 f(x)`. -/
def centralSecondDifference (f : Point n → ℝ) (v x : Point n) : ℝ :=
  f (x + v) + f (x - v) - 2 * f x

/--
The coordinate second-difference Laplacian with step `h`:
`h⁻² ∑ i, (f(x + h eᵢ) + f(x - h eᵢ) - 2 f(x))`.
-/
def coordSecondDifference (f : Point n → ℝ) (h : ℝ) (x : Point n) : ℝ :=
  (h ^ 2)⁻¹ * ∑ i, centralSecondDifference f (h • Pi.single i 1) x

theorem norm_single_one_le_one (i : Fin n) : ‖(Pi.single i (1 : ℝ) : Point n)‖ ≤ 1 := by
  rw [Pi.norm_single]
  simp

/-! ### A one-dimensional second-order mean value estimate -/

/--
If `g''` stays within `ε` of `a` on `[-h, h]`, then the central second
difference of `g` is within `2 ε h²` of `a h²`.
-/
theorem abs_central_second_difference_sub_le {g g' g'' : ℝ → ℝ} {a ε h : ℝ}
    (hh : 0 ≤ h)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hbound : ∀ t ∈ Icc (-h) h, |g'' t - a| ≤ ε) :
    |g h + g (-h) - 2 * g 0 - a * h ^ 2| ≤ 2 * ε * h ^ 2 := by
  have hmemI : ∀ t ∈ Icc (0 : ℝ) h, t ∈ Icc (-h) h ∧ -t ∈ Icc (-h) h := by
    intro t ht
    exact ⟨⟨by linarith [ht.1], ht.2⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have h0 : (0 : ℝ) ∈ Icc (-h) h := ⟨by linarith, hh⟩
  -- first derivative: `φ t = g' t - a t` has derivative `g'' t - a`
  have hφ : ∀ t ∈ Icc (-h) h, |(g' t - a * t) - (g' 0 - a * 0)| ≤ ε * |t| := by
    intro t ht
    have hderiv : ∀ s ∈ Icc (-h) h,
        HasDerivWithinAt (fun s => g' s - a * s) (g'' s - a * 1) (Icc (-h) h) s :=
      fun s _ => ((hg' s).sub ((hasDerivAt_id' s).const_mul a)).hasDerivWithinAt
    have hb : ∀ s ∈ Icc (-h) h, ‖g'' s - a * 1‖ ≤ ε := by
      intro s hs
      simpa [Real.norm_eq_abs] using hbound s hs
    have := (convex_Icc (-h) h).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hb h0 ht
    simpa [Real.norm_eq_abs] using this
  -- second step: `ψ t = g t + g (-t) - 2 g 0 - a t²`
  let ψ : ℝ → ℝ := fun t => g t + g (-t) - 2 * g 0 - a * (t * t)
  let ψ' : ℝ → ℝ := fun t => g' t - g' (-t) - 2 * a * t
  have hψ : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    have hneg : HasDerivAt (fun s => g (-s)) (g' (-t) * -1) t :=
      (hg (-t)).comp t (hasDerivAt_neg t)
    have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
      (hasDerivAt_id' t).mul (hasDerivAt_id' t)
    have := (((hg t).add hneg).sub (hasDerivAt_const t (2 * g 0))).sub (hsq.const_mul a)
    refine this.congr_deriv ?_
    simp only [ψ']
    ring
  have hψb : ∀ t ∈ Icc (0 : ℝ) h, ‖ψ' t‖ ≤ 2 * ε * h := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := hmemI t ht
    have e1 := hφ t ht1
    have e2 := hφ (-t) ht2
    have habs : |t| ≤ h := by rw [abs_of_nonneg ht.1]; exact ht.2
    have habs' : |-t| ≤ h := by rw [abs_neg]; exact habs
    have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hbound 0 h0)
    have hdecomp : ψ' t = ((g' t - a * t) - (g' 0 - a * 0)) -
        ((g' (-t) - a * (-t)) - (g' 0 - a * 0)) := by
      simp only [ψ']
      ring
    rw [Real.norm_eq_abs, hdecomp]
    calc |((g' t - a * t) - (g' 0 - a * 0)) - ((g' (-t) - a * (-t)) - (g' 0 - a * 0))|
        ≤ |(g' t - a * t) - (g' 0 - a * 0)| + |(g' (-t) - a * (-t)) - (g' 0 - a * 0)| :=
          abs_sub _ _
      _ ≤ ε * |t| + ε * |-t| := add_le_add e1 e2
      _ ≤ ε * h + ε * h := add_le_add (mul_le_mul_of_nonneg_left habs hε)
          (mul_le_mul_of_nonneg_left habs' hε)
      _ = 2 * ε * h := by ring
  have hmvt := (convex_Icc (0 : ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hψ t).hasDerivWithinAt) hψb ⟨le_rfl, hh⟩ ⟨hh, le_rfl⟩
  have hψ0 : ψ 0 = 0 := by simp only [ψ, neg_zero]; ring
  rw [hψ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at hmvt
  have hψh : ψ h = g h + g (-h) - 2 * g 0 - a * h ^ 2 := by
    simp only [ψ]
    ring
  rw [← hψh]
  calc |ψ h| ≤ 2 * ε * h * h := hmvt
    _ = 2 * ε * h ^ 2 := by ring

/-! ### Uniform convergence of second differences of test functions -/

/-- The trace Laplacian of a function vanishes off its topological support. -/
theorem lapTrace_eq_zero_of_notMem_tsupport {χ : Point n → ℝ} {x : Point n}
    (hx : x ∉ tsupport χ) : lapTrace χ x = 0 := by
  have h2 : x ∉ tsupport (fderiv ℝ (fderiv ℝ χ)) := fun hx2 =>
    hx (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ hx2))
  have hzero : fderiv ℝ (fderiv ℝ χ) x = 0 := image_eq_zero_of_notMem_tsupport h2
  simp [lapTrace, hzero]

/-- The trace Laplacian of a `C²` function is continuous. -/
theorem continuous_lapTrace {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) :
    Continuous (lapTrace χ) := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ χ) := hχ.fderiv_right (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ χ)) := hD1.continuous_fderiv (by norm_num)
  exact continuous_finsetSum _ fun i _ =>
    (hD2.clm_apply continuous_const).clm_apply continuous_const

/-- The trace Laplacian of a `C²` function with compact support has compact support. -/
theorem hasCompactSupport_lapTrace {χ : Point n → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (lapTrace χ) :=
  HasCompactSupport.intro hχc (fun _ hx => lapTrace_eq_zero_of_notMem_tsupport hx)

theorem dist_add_smul_single_le (x : Point n) (t : ℝ) (i : Fin n) :
    dist (x + t • (Pi.single i 1 : Point n)) x ≤ |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg t) (norm_single_one_le_one i)

/--
For a `C²` function with compact support, the coordinate second differences
converge uniformly to the trace Laplacian.
-/
theorem exists_forall_abs_coordSecondDifference_sub_lapTrace_le
    {χ : Point n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ x : Point n,
      |coordSecondDifference χ h x - lapTrace χ x| ≤ ε := by
  set D1 := fderiv ℝ χ with hD1def
  set D2 := fderiv ℝ D1 with hD2def
  have hD1 : ContDiff ℝ 1 D1 := hχ.fderiv_right (by norm_num)
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hdD1 : Differentiable ℝ D1 := hD1.differentiable (by norm_num)
  have hD2 : Continuous D2 := hD1.continuous_fderiv (by norm_num)
  have hD2c : HasCompactSupport D2 := (hχc.fderiv ℝ).fderiv ℝ
  have hunif := hD2c.uniformContinuous_of_continuous hD2
  set ε' : ℝ := ε / (2 * n + 1) with hε'def
  have hn : (0 : ℝ) < 2 * n + 1 := by positivity
  have hε' : 0 < ε' := div_pos hε hn
  obtain ⟨δ, hδ, hδD2⟩ :=
    (Metric.uniformContinuous_iff (f := D2)).mp (by exact hunif) ε' hε'
  refine ⟨δ, hδ, fun h hh hhδ x => ?_⟩
  -- one coordinate direction
  have hdir : ∀ i : Fin n,
      |centralSecondDifference χ (h • Pi.single i 1) x -
          D2 x (Pi.single i 1) (Pi.single i 1) * h ^ 2| ≤ 2 * ε' * h ^ 2 := by
    intro i
    set e : Point n := Pi.single i 1
    have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • e) e t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    have hg : ∀ t : ℝ, HasDerivAt (fun t => χ (x + t • e)) (D1 (x + t • e) e) t :=
      fun t => (hdχ (x + t • e)).hasFDerivAt.comp_hasDerivAt t (hl t)
    have hg' : ∀ t : ℝ, HasDerivAt (fun t => D1 (x + t • e) e) (D2 (x + t • e) e e) t := by
      intro t
      have h1 : HasDerivAt (fun t => D1 (x + t • e)) (D2 (x + t • e) e) t :=
        (hdD1 (x + t • e)).hasFDerivAt.comp_hasDerivAt t (hl t)
      exact (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
    have hbound : ∀ t ∈ Icc (-h) h, |D2 (x + t • e) e e - D2 x e e| ≤ ε' := by
      intro t ht
      have hdist : dist (x + t • e) x < δ := by
        refine lt_of_le_of_lt (dist_add_smul_single_le x t i) ?_
        exact lt_of_le_of_lt (abs_le.mpr ⟨ht.1, ht.2⟩) hhδ
      have hclose : dist (D2 (x + t • e)) (D2 x) < ε' := hδD2 hdist
      have he : ‖e‖ ≤ 1 := norm_single_one_le_one i
      calc |D2 (x + t • e) e e - D2 x e e| = ‖(D2 (x + t • e) - D2 x) e e‖ := by
            rw [Real.norm_eq_abs]; simp
        _ ≤ ‖D2 (x + t • e) - D2 x‖ * ‖e‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ ‖D2 (x + t • e) - D2 x‖ * 1 * 1 := by
            gcongr
        _ ≤ ε' := by
            rw [mul_one, mul_one]
            exact le_of_lt (lt_of_eq_of_lt (dist_eq_norm (D2 (x + t • e)) (D2 x)).symm hclose)
    have hmain := abs_central_second_difference_sub_le hh.le hg hg' hbound
    have hcsd : centralSecondDifference χ (h • e) x =
        χ (x + h • e) + χ (x + (-h) • e) - 2 * χ (x + (0 : ℝ) • e) := by
      simp [centralSecondDifference, neg_smul, sub_eq_add_neg]
    rw [hcsd]
    exact hmain
  have hh2 : (h ^ 2) ≠ 0 := by positivity
  have hsplit : coordSecondDifference χ h x - lapTrace χ x =
      (h ^ 2)⁻¹ * ∑ i, (centralSecondDifference χ (h • Pi.single i 1) x -
          D2 x (Pi.single i 1) (Pi.single i 1) * h ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, mul_sub, coordSecondDifference, lapTrace]
    congr 1
    rw [mul_comm, mul_assoc, mul_inv_cancel₀ hh2, mul_one]
  rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < h ^ 2))]
  calc (h ^ 2)⁻¹ * |∑ i, (centralSecondDifference χ (h • Pi.single i 1) x -
          D2 x (Pi.single i 1) (Pi.single i 1) * h ^ 2)|
      ≤ (h ^ 2)⁻¹ * ∑ _i : Fin n, 2 * ε' * h ^ 2 := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hdir i)
    _ = 2 * n * ε' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ ≤ ε := by
        rw [hε'def, ← mul_div_assoc, div_le_iff₀ hn]
        nlinarith

/-! ### Supports and continuity of second differences -/

theorem continuous_coordSecondDifference {f : Point n → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (coordSecondDifference f h) := by
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact ((hf.comp (continuous_id.add continuous_const)).add
    (hf.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hf)

/--
The second difference with step `0 ≤ h ≤ r` vanishes outside the closed
`r`-thickening of the topological support.
-/
theorem coordSecondDifference_eq_zero_of_notMem_cthickening {f : Point n → ℝ}
    {h r : ℝ} (hh : 0 ≤ h) (hhr : h ≤ r) {x : Point n}
    (hx : x ∉ cthickening r (tsupport f)) : coordSecondDifference f h x = 0 := by
  have hnot : ∀ y : Point n, dist x y ≤ r → f y = 0 := by
    intro y hy
    by_contra hne
    exact hx (mem_cthickening_of_dist_le x y r _ (subset_tsupport f hne) hy)
  have hterm : ∀ i : Fin n, centralSecondDifference f (h • Pi.single i 1) x = 0 := by
    intro i
    have hr : 0 ≤ r := hh.trans hhr
    have h1 : f (x + h • Pi.single i 1) = 0 := by
      refine hnot _ ?_
      rw [dist_comm]
      exact (dist_add_smul_single_le x h i).trans (by rw [abs_of_nonneg hh]; exact hhr)
    have h2 : f (x - h • Pi.single i 1) = 0 := by
      refine hnot _ ?_
      rw [dist_comm, sub_eq_add_neg, ← neg_smul]
      exact (dist_add_smul_single_le x (-h) i).trans
        (by rw [abs_neg, abs_of_nonneg hh]; exact hhr)
    have h3 : f x = 0 := hnot x (by rw [dist_self]; exact hr)
    simp [centralSecondDifference, h1, h2, h3]
  simp [coordSecondDifference, hterm]

/--
A continuous function whose support lies in a compact set is integrable.
-/
theorem integrable_of_continuous_of_forall_notMem_eq_zero {f : Point n → ℝ}
    (hf : Continuous f) {S : Set (Point n)} (hS : IsCompact S)
    (hzero : ∀ x, x ∉ S → f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hS hzero)

/--
For continuous `w` and a `C²` function `χ` with compact support,
`∫ w Δ_h χ → ∫ w Δχ` as `h → 0⁺`.
-/
theorem tendsto_integral_mul_coordSecondDifference {w χ : Point n → ℝ}
    (hw : Continuous w) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun h => ∫ x, w x * coordSecondDifference χ h x) (𝓝[>] 0)
      (𝓝 (∫ x, w x * lapTrace χ x)) := by
  set S := cthickening 1 (tsupport χ) with hSdef
  have hS : IsCompact S := hχc.isCompact.cthickening
  have hχcont : Continuous χ := hχ.continuous
  set A : ℝ := ∫ x in S, |w x| with hAdef
  have hA : 0 ≤ A := setIntegral_nonneg hS.measurableSet (fun _ _ => abs_nonneg _)
  have hLint : Integrable (fun x => w x * lapTrace χ x) :=
    integrable_of_continuous_of_forall_notMem_eq_zero (hw.mul (continuous_lapTrace hχ)) hS
      (fun x hx => by
        rw [lapTrace_eq_zero_of_notMem_tsupport (fun h' => hx (self_subset_cthickening _ h')),
          mul_zero])
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_abs_coordSecondDifference_sub_lapTrace_le hχ hχc
    (ε := ε / (2 * (A + 1))) (by positivity)
  refine ⟨min δ 1, lt_min hδ one_pos, fun h hhpos hhdist => ?_⟩
  have hhpos' : 0 < h := hhpos
  have hhlt : h < min δ 1 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hhpos'] at hhdist
    exact hhdist
  have hh1 : h ≤ 1 := (hhlt.trans_le (min_le_right _ _)).le
  have hΔint : Integrable (fun x => w x * coordSecondDifference χ h x) :=
    integrable_of_continuous_of_forall_notMem_eq_zero
      (hw.mul (continuous_coordSecondDifference hχcont h)) hS
      (fun x hx => by
        rw [coordSecondDifference_eq_zero_of_notMem_cthickening hhpos'.le hh1 hx, mul_zero])
  have hgint : Integrable (S.indicator fun x => ε / (2 * (A + 1)) * |w x|) := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact ((hw.continuousOn.integrableOn_compact hS).norm.const_mul (ε / (2 * (A + 1)))).congr
      (ae_of_all _ fun x => by simp [Real.norm_eq_abs])
  rw [Real.dist_eq, ← integral_sub hΔint hLint]
  have hbound : ∀ x, ‖w x * coordSecondDifference χ h x - w x * lapTrace χ x‖ ≤
      S.indicator (fun x => ε / (2 * (A + 1)) * |w x|) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_comm]
      exact mul_le_mul_of_nonneg_right
        (hδb h hhpos' (hhlt.trans_le (min_le_left _ _)) x) (abs_nonneg _)
    · rw [indicator_of_notMem hx,
        coordSecondDifference_eq_zero_of_notMem_cthickening hhpos'.le hh1 hx,
        lapTrace_eq_zero_of_notMem_tsupport (fun h' => hx (self_subset_cthickening _ h'))]
      simp
  have hle := norm_integral_le_of_norm_le hgint (ae_of_all _ hbound)
  rw [integral_indicator hS.measurableSet, integral_const_mul, ← hAdef] at hle
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, (w x * coordSecondDifference χ h x - w x * lapTrace χ x)‖
      ≤ ε / (2 * (A + 1)) * A := hle
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-! ### Discrete integration by parts -/

/--
Translation invariance of Lebesgue measure moves a central second difference
from one factor to the other.
-/
theorem integral_centralSecondDifference_mul {f g : Point n → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (v : Point n) :
    ∫ x, centralSecondDifference f v x * g x =
      ∫ x, f x * centralSecondDifference g v x := by
  have hint : ∀ a : Point n, Integrable (fun x => f (x + a) * g x) := fun a =>
    ((hf.comp (continuous_add_const a)).mul hg).integrable_of_hasCompactSupport
      hgc.mul_left
  have hint' : ∀ a : Point n, Integrable (fun x => f x * g (x + a)) := fun a =>
    (hf.mul (hg.comp (continuous_add_const a))).integrable_of_hasCompactSupport
      (hgc.comp_homeomorph (Homeomorph.addRight a)).mul_left
  have hshift : ∀ a : Point n, ∫ x, f (x + a) * g x = ∫ x, f x * g (x + -a) := by
    intro a
    have := integral_add_right_eq_self (μ := volume) (fun x => f (x + a) * g x) (-a)
    simp only [neg_add_cancel_right] at this
    exact this.symm
  have hL : (fun x => centralSecondDifference f v x * g x) =
      fun x => f (x + v) * g x + f (x + -v) * g x - 2 * (f (x + 0) * g x) := by
    funext x
    simp only [centralSecondDifference, add_zero, ← sub_eq_add_neg]
    ring
  have hR : (fun x => f x * centralSecondDifference g v x) =
      fun x => f x * g (x + -v) + f x * g (x + v) - 2 * (f x * g (x + 0)) := by
    funext x
    simp only [centralSecondDifference, add_zero, ← sub_eq_add_neg]
    ring
  have eL : ∫ x, (f (x + v) * g x + f (x + -v) * g x - 2 * (f (x + 0) * g x)) =
      (∫ x, f (x + v) * g x) + (∫ x, f (x + -v) * g x) - 2 * ∫ x, f (x + 0) * g x := by
    rw [integral_sub, integral_add, integral_const_mul]
    · exact hint v
    · exact hint (-v)
    · exact (hint v).add (hint (-v))
    · exact (hint 0).const_mul 2
  have eR : ∫ x, (f x * g (x + -v) + f x * g (x + v) - 2 * (f x * g (x + 0))) =
      (∫ x, f x * g (x + -v)) + (∫ x, f x * g (x + v)) - 2 * ∫ x, f x * g (x + 0) := by
    rw [integral_sub, integral_add, integral_const_mul]
    · exact hint' (-v)
    · exact hint' v
    · exact (hint' (-v)).add (hint' v)
    · exact (hint' 0).const_mul 2
  rw [hL, hR, eL, eR, hshift v, hshift (-v), hshift 0, neg_neg, neg_zero]

/--
Discrete integration by parts: `∫ (Δ_h f) g = ∫ f (Δ_h g)` for continuous `f`
and continuous compactly supported `g`.
-/
theorem integral_coordSecondDifference_mul {f g : Point n → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (h : ℝ) :
    ∫ x, coordSecondDifference f h x * g x = ∫ x, f x * coordSecondDifference g h x := by
  have hcsd : ∀ v : Point n, Continuous (centralSecondDifference f v) := fun v =>
    ((hf.comp (continuous_id.add continuous_const)).add
      (hf.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hf)
  have hintL : ∀ i : Fin n,
      Integrable (fun x => centralSecondDifference f (h • Pi.single i 1) x * g x) :=
    fun i => ((hcsd _).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  have hintR : ∀ i : Fin n,
      Integrable (fun x => f x * centralSecondDifference g (h • Pi.single i 1) x) := by
    intro i
    have hcg : Continuous (centralSecondDifference g (h • Pi.single i 1)) :=
      ((hg.comp (continuous_id.add continuous_const)).add
        (hg.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hg)
    refine (hf.mul hcg).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left ?_
    have h1 := hgc.comp_homeomorph (Homeomorph.addRight (h • (Pi.single i 1 : Point n)))
    have h2 := hgc.comp_homeomorph (Homeomorph.subRight (h • (Pi.single i 1 : Point n)))
    have h3 : HasCompactSupport (fun x => 2 * g x) := hgc.mul_left
    exact (h1.add h2).sub h3
  have hL : (fun x => coordSecondDifference f h x * g x) =
      fun x => (h ^ 2)⁻¹ * ∑ i, centralSecondDifference f (h • Pi.single i 1) x * g x := by
    funext x
    rw [coordSecondDifference, mul_assoc, Finset.sum_mul]
  have hR : (fun x => f x * coordSecondDifference g h x) =
      fun x => (h ^ 2)⁻¹ * ∑ i, f x * centralSecondDifference g (h • Pi.single i 1) x := by
    funext x
    rw [coordSecondDifference, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hL, hR, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun i _ => hintL i, integral_finsetSum _ fun i _ => hintR i]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    integral_centralSecondDifference_mul hf hg hgc _

end ViscositySolns
