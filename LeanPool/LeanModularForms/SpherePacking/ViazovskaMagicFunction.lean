/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.GeneralizedResidueTheorem
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Cycle
import LeanPool.LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanPool.LeanModularForms.Modularforms.Eisenstein
import LeanPool.LeanModularForms.SpherePacking.PhiHolomorphic
import LeanPool.LeanModularForms.SpherePacking.CuspDecay

/-!
# Viazovska's Magic Function — Original Contour Integrals

This file defines the magic function `a(r)` from Viazovska's proof of the
optimality of the E₈ sphere packing [Via2017] and proves the key contour
equivalence `I₁₂ = I₁₂_vert + I₁₂_horiz` (rectangular decomposition of the
diagonal contour from `-1` to `i`).

## What we prove

The function `aRad(r)` is defined using the **original triangular contours**
from Viazovska's paper:
```
aRad(r) = ∫_{-1→i} φ₀(-1/(z+1)) · (z+1)² · e^{πirz} dz
         + ∫_{1→i}  φ₀(-1/(z-1)) · (z-1)² · e^{πirz} dz
         - 2 ∫_{0→i} φ₀(-1/z) · z² · e^{πirz} dz
         + 2 ∫_{i→i∞} φ₀(z) · e^{πirz} dz
```
where `φ₀(z) = (E₂E₄ - E₆)² / Δ(z)`.

The main result `I12_eq_rectangular` proves that the diagonal contour integral
`∫_{-1→i}` equals the sum of a vertical integral `∫_{-1→-1+i}` and a
horizontal integral `∫_{-1+i→i}`. This is the first step toward evaluating
`aRad(r)` via the Fourier expansion of φ₀.

## How this differs from Sphere-Packing-Lean (Gauss2 PR)

The Sphere-Packing-Lean formalization
deforms the original triangular contours into **rectangular** contours from the
start, avoiding the cusp singularity at `z = -1, 0, 1` entirely. The contour
integrals are then evaluated on rectangles where all four sides lie strictly
inside the upper half-plane.

Our approach keeps Viazovska's original contours and handles the cusp
singularities directly:

1. **Holomorphicity of φ₀**: We prove `E₂` is holomorphic on ℍ via
   `E₂ = (πI/12)⁻¹ · logDeriv(η)` (Dedekind eta), then build up to `φ₀''`
   holomorphic on ℍ (`PhiHolomorphic.lean`). The Gauss2 PR instead uses the
   Serre derivative and Ramanujan's identity `E₂E₄ - E₆ = 3D(E₄)`.

2. **Cusp decay**: We prove `φ₀` is bounded at `Im → ∞` via the q-expansion
   bound `|E₂E₄-E₆| ≤ K|q|` (`CuspDecay.lean`), using `|E₂-1| ≤ 192|q|`
   from a comparison test on the Eisenstein series.

3. **Contour equivalence**: We prove `I₁₂ = I₁₂_vert + I₁₂_horiz` using
   path independence from `holomorphic_convex_primitive` on the convex upper
   half-plane. The proof takes a primitive `G` of the integrand, applies FTC
   to truncated integrals (starting at height `δ > 0`), then takes `δ → 0`
   using the cusp cancellation `(z+1)² → 0` at `z = -1`.

4. **Infrastructure**: The key tool is `holomorphic_convex_primitive` from
   `GeneralizedResidueTheory/CauchyPrimitive.lean`, which gives path independence
   for holomorphic functions on convex open sets. This is part of our broader
   generalized residue theorem framework (Hungerbühler-Wasem, Theorem 3.3),
   though this file only uses the convex primitive — the full generalized
   residue theorem and `ContourCycle` framework will be applied when computing
   `aRad(r)` via the S-transformation of φ₀.

## Main results

* `φ₀''_differentiableOn` : φ₀ is holomorphic on ℍ
* `continuousOn_diagonal_integrand` : the parameterized diagonal integrand is
  continuous on `[0,1]` (including the cusp endpoint `t = 0`)
* `continuousOn_vertical_integrand` : same for the vertical parameterization
* `I12_eq_rectangular` : `I₁₂(r) = I₁₂_vert(r) + I₁₂_horiz(r)`

## References

* Viazovska, M. S. (2017). "The sphere packing problem in dimension 8."
  Annals of Mathematics, 185(3), 991-1015.
* Hungerbühler, N., Wasem, M. (2019). "A generalized version of the
  residue theorem." arXiv:1808.00997v2.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval

-- `instIsScalarTowerRealComplexComplex` lives in `LeanPool.LeanModularForms.ForMathlib.Instances`;
-- redeclaring it here at the same name would shadow that one in the project-wide index.

noncomputable section

/-! ## Modular form ingredients

We use `φ₀''` (the ℂ-extended version of φ₀) from `Modularforms/Eisenstein.lean`.
This is defined as `φ₀''(z) = φ₀(z)` when `Im(z) > 0`, and `0` otherwise.
The underlying `φ₀(z) = (E₂E₄ - E₆)² / Δ(z)` is defined on the upper half-plane ℍ.

Key properties (proven in Eisenstein.lean and Delta.lean):
- `φ₀` is holomorphic on ℍ (since Δ ≠ 0 on ℍ)
- Periodic: `φ₀(z+1) = φ₀(z)`
- S-transform: `φ₀(-1/z) = φ₀(z) - (12i/π)·(1/z)·φ₋₂(z) - (36/π²)·(1/z²)·φ₋₄(z)`
- Vanishing: `φ₀(z) = O(e^{-2πIm(z)})` as `Im(z) → ∞`
-/

/-! ## Original Viazovska contour integrals

The four integrals defining aRad(r), using straight-line contours
from the real axis to i. -/

/-- The integrand for I₁+I₂: φ₀(-1/(z+1)) · (z+1)² · e^{πirz}.
At z = -1 (the cusp), (z+1)² = 0 cancels the singularity of φ₀. -/
def viazovskaIntegrandLeft (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₃+I₄: φ₀(-1/(z-1)) · (z-1)² · e^{πirz}.
At z = 1 (the cusp), (z-1)² = 0 cancels the singularity. -/
def viazovskaIntegrandRight (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₅: φ₀(-1/z) · z² · e^{πirz}.
At z = 0 (the cusp), z² = 0 cancels the singularity. -/
def viazovskaIntegrandCenter (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' (-1 / z) * z ^ 2 * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The integrand for I₆: φ₀(z) · e^{πirz}.
No singularity issues (Im(z) ≥ 1 on the contour). -/
def viazovskaIntegrandTail (r : ℝ) (z : ℂ) : ℂ :=
  φ₀'' z * Complex.exp (↑Real.pi * I * ↑r * z)

/-- The straight-line contour from -1 to i (original Viazovska path). -/
def contourNeg1ToI (t : ℝ) : ℂ := -1 + (1 + I) * ↑t

/-- The straight-line contour from 1 to i (original Viazovska path). -/
def contour1ToI (t : ℝ) : ℂ := 1 + (-1 + I) * ↑t

/-- The straight-line contour from 0 to i (vertical segment). -/
def contour0ToI (t : ℝ) : ℂ := I * ↑t

/-! ## The magic function aRad(r)

Defined using the original Viazovska contours. -/

/-- I₁₂(r) = ∫_{-1}^{i} φ₀(-1/(z+1)) · (z+1)² · e^{πirz} dz -/
def I12 (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r (contourNeg1ToI t) *
    deriv contourNeg1ToI t

/-- I₃₄(r) = ∫_{1}^{i} φ₀(-1/(z-1)) · (z-1)² · e^{πirz} dz -/
def I34 (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, viazovskaIntegrandRight r (contour1ToI t) *
    deriv contour1ToI t

/-- I₅(r) = -2 ∫_{0}^{i} φ₀(-1/z) · z² · e^{πirz} dz -/
def I5 (r : ℝ) : ℂ :=
  -2 * ∫ t in (0 : ℝ)..1, viazovskaIntegrandCenter r (contour0ToI t) *
    deriv contour0ToI t

/-- I₆(r) = 2 ∫_{i}^{i∞} φ₀(z) · e^{πirz} dz
(the semi-infinite vertical integral). -/
def I6 (r : ℝ) : ℂ :=
  2 * ∫ t in Set.Ici (1 : ℝ), viazovskaIntegrandTail r (I * ↑t)  * I

/-- The radial magic function aRad(r) from Viazovska [Via2017]. -/
def aRad (r : ℝ) : ℂ := I12 r + I34 r + I5 r + I6 r

/-! ## Holomorphicity of φ₀

φ₀ = (E₂·E₄ - E₆)² / Δ is holomorphic on ℍ because:
- E₂ is holomorphic (proved in PhiHolomorphic.lean via `E₂ = const · logDeriv(η)`)
- E₄, E₆ are modular forms (holomorphic by `.holo'`)
- Δ is a cusp form (holomorphic) and Δ ≠ 0 on ℍ
- Products, differences, squares, and ratios of holomorphic functions
  (with nonzero denominator) are holomorphic -/

/-- φ₀'' is holomorphic on the upper half-plane. -/
theorem φ₀''_differentiableOn : DifferentiableOn ℂ φ₀'' {z : ℂ | 0 < z.im} := by
  have hE₂ := E₂_differentiableOn
  have hE₄ := UpperHalfPlane.mdifferentiable_iff.mp E₄.holo'
  have hE₆ := UpperHalfPlane.mdifferentiable_iff.mp E₆.holo'
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
  intro z hz
  have hz' : 0 < z.im := hz
  have hE₂z := (E₂_differentiableOn z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hE₄z := (hE₄ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hE₆z := (hE₆ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hΔz := (hΔ z hz).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz')
  have hΔ_ne : (Delta.toSlashInvariantForm ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz',
      CuspForm.toSlashInvariantForm_coe, ne_eq]
    exact Δ_ne_zero ⟨z, hz'⟩
  have hdiff := ((hE₂z.mul hE₄z).sub hE₆z).pow 2 |>.div hΔz hΔ_ne
  have hopen := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz'
  apply hdiff.differentiableWithinAt.congr_of_eventuallyEq
  · rw [nhdsWithin_eq_nhds.mpr (Filter.mem_of_superset hopen (fun _ h => h))]
    filter_upwards [hopen] with w hw
    simp only [φ₀'', hw, dif_pos, φ₀, Function.comp,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw, Pi.mul_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.div_apply]; rfl
  · simp only [φ₀'', hz', dif_pos, φ₀, Function.comp,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz', Pi.mul_apply, Pi.sub_apply,
      Pi.pow_apply, Pi.div_apply]; rfl

/-! ## Upper half-plane: convexity and openness -/

-- `isOpen_upperHalfPlaneSet` from mathlib (`UpperHalfPlane.isOpen_upperHalfPlaneSet`)
alias isOpen_upperHalfPlaneSet := UpperHalfPlane.isOpen_upperHalfPlaneSet

/-- The upper half-plane `{z : ℂ | 0 < z.im}` is convex. -/
theorem convex_upperHalfPlaneSet : Convex ℝ {z : ℂ | 0 < z.im} := by
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y).im
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp [Complex.add_im]
  rw [him]
  have hx' : (0 : ℝ) < x.im := hx
  have hy' : (0 : ℝ) < y.im := hy
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp; linarith
  · linarith [mul_pos ha' hx', mul_nonneg hb (le_of_lt hy')]

/-! ## Holomorphicity of the integrand -/

/-- When `Im(z) > 0`, the point `-1/(z+1)` also has positive imaginary part. -/
theorem neg_inv_add_one_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / (z + 1)).im := by
  have hne : z + 1 ≠ 0 := by intro h; have := (Complex.ext_iff.mp h).2; simp at this; linarith
  rw [neg_div, Complex.neg_im, Complex.div_im]
  rw [Complex.one_im, Complex.one_re, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
  exact div_pos (by simpa using hz) (Complex.normSq_pos.mpr hne)

/-- The integrand `viazovskaIntegrandLeft r` is holomorphic on the upper half-plane.
This follows from holomorphicity of `φ₀''` and the algebraic factors. -/
theorem viazovska_integrand_left_differentiableOn (r : ℝ) :
    DifferentiableOn ℂ (viazovskaIntegrandLeft r) {z : ℂ | 0 < z.im} := by
  intro z hz
  unfold viazovskaIntegrandLeft
  have hz' : 0 < z.im := hz
  have hne : z + 1 ≠ 0 := by intro h; have := (Complex.ext_iff.mp h).2; simp at this; linarith
  have him := neg_inv_add_one_im_pos hz'
  have hφ : DifferentiableAt ℂ φ₀'' (-1 / (z + 1)) :=
    (φ₀''_differentiableOn _ him).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds him)
  have hinv : DifferentiableAt ℂ (fun w => -1 / (w + 1)) z :=
    (differentiableAt_const _).div
      (differentiableAt_id.add (differentiableAt_const _)) hne
  exact ((hφ.comp z hinv).mul
    ((differentiableAt_id.add (differentiableAt_const _)).pow 2) |>.mul
    (Complex.differentiable_exp.differentiableAt.comp z
      ((differentiableAt_const _).mul differentiableAt_id))).differentiableWithinAt

/-! ## Contour equivalence infrastructure

### Segment integrals and the fundamental theorem of calculus

Given a holomorphic function `f` on a convex open set `S` with primitive `G`
(i.e., `G' = f` on `S`), the segment integral from `a` to `b` equals `G(b) - G(a)`.
This gives path independence: for `a, b, c ∈ S`,
```
∫_{a→b} f dz = ∫_{a→c} f dz + ∫_{c→b} f dz
```
since both sides equal `G(b) - G(a)`. -/

/-- FTC for segment integrals: if `G' = f` on a convex open set,
then the segment integral of `f` from `a` to `b` equals `G(b) - G(a)`. -/
theorem segment_integral_eq_sub_of_hasDerivAt {f G : ℂ → ℂ} {S : Set ℂ}
    (_hS_open : IsOpen S) (hS_convex : Convex ℝ S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S)
    (hG : ∀ z ∈ S, HasDerivAt G (f z) z)
    (hf_cont : ContinuousOn f S) :
    ∫ t in (0 : ℝ)..1, f (a + t • (b - a)) * (b - a) = G b - G a := by
  have h_mem : ∀ t ∈ Icc (0 : ℝ) 1, a + ↑t • (b - a) ∈ S := by
    intro t ht
    have : a + ↑t • (b - a) = (1 - t) • a + t • b := by
      simp only [smul_sub, sub_smul, one_smul]; ring
    rw [this]
    exact hS_convex ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hcont : ContinuousOn (fun t : ℝ => f (a + t • (b - a))) (Icc 0 1) :=
    hf_cont.comp (continuous_const.add
      (continuous_ofReal.smul continuous_const)).continuousOn h_mem
  have key := @intervalIntegral.integral_unitInterval_deriv_eq_sub ℂ ℂ _ _ _ _ _
    IsScalarTower.right G f a (b - a)
    hcont (fun t ht => hG _ (h_mem t ht))
  rw [show a + (b - a) = b from by ring] at key
  rw [smul_eq_mul] at key
  erw [intervalIntegral.integral_mul_const]; rw [mul_comm]
  exact key

/-- Contour additivity: for a holomorphic function on a convex open set,
the segment integral from `a` to `b` equals the sum of segment integrals
from `a` to `c` and from `c` to `b`. -/
theorem segment_integral_add_of_holomorphic {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℂ f S)
    {a b c : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    ∫ t in (0 : ℝ)..1, f (a + t • (b - a)) * (b - a) =
    (∫ t in (0 : ℝ)..1, f (a + t • (c - a)) * (c - a)) +
    (∫ t in (0 : ℝ)..1, f (c + t • (b - c)) * (b - c)) := by
  obtain ⟨G, hG⟩ := holomorphic_convex_primitive hS_convex hS_open ⟨a, ha⟩ hf
  rw [segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex ha hb hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex ha hc hG hf.continuousOn,
      segment_integral_eq_sub_of_hasDerivAt hS_open hS_convex hc hb hG hf.continuousOn]
  ring

/-! ### Contour parameterization lemmas -/

/-- The derivative of the diagonal contour map. -/
private theorem hasDerivAt_contour_neg1_to_i (t : ℝ) :
    HasDerivAt (fun s : ℝ => contourNeg1ToI s) (1 + I : ℂ) t := by
  simp only [contourNeg1ToI]
  have h1 := (ofRealCLM.hasDerivAt (x := t)).const_mul (1 + I : ℂ)
  simp only [ofRealCLM, LinearIsometry.coe_toContinuousLinearMap, ofRealLI_apply, ofReal_one,
    mul_one] at h1
  simpa only [contourNeg1ToI] using h1.const_add (-1 : ℂ)

/-- The derivative of the vertical contour map. -/
private theorem hasDerivAt_vert_contour (t : ℝ) :
    HasDerivAt (fun s : ℝ => (-1 : ℂ) + I * ↑s) (I : ℂ) t := by
  have h1 := (ofRealCLM.hasDerivAt (x := t)).const_mul (I : ℂ)
  simp only [ofRealCLM, LinearIsometry.coe_toContinuousLinearMap, ofRealLI_apply, ofReal_one,
    mul_one] at h1
  simpa using h1.const_add (-1 : ℂ)

/-- The derivative of `contourNeg1ToI` is the constant `1 + I`. -/
theorem deriv_contour_neg1_to_i (t : ℝ) : deriv contourNeg1ToI t = 1 + I :=
  (hasDerivAt_contour_neg1_to_i t).deriv

/-- `I12` expressed as a segment integral from `-1` to `I`. -/
theorem I12_eq_segment_integral (r : ℝ) :
    I12 r = ∫ t in (0 : ℝ)..1,
      viazovskaIntegrandLeft r ((-1 : ℂ) + t • ((I : ℂ) - (-1))) *
        ((I : ℂ) - (-1)) := by
  unfold I12; congr 1; ext t
  rw [deriv_contour_neg1_to_i]
  have h1 : contourNeg1ToI t = (-1 : ℂ) + ↑t • ((I : ℂ) - (-1)) := by
    simp [contourNeg1ToI, Complex.real_smul, sub_neg_eq_add]; ring
  rw [h1, show (1 : ℂ) + I = (I : ℂ) - (-1) from by ring]

/-! ### Rectangular decomposition integrals -/

/-- The vertical integral from `-1` to `-1+I`: left side of the rectangular path. -/
def I12Vert (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r (-1 + I * ↑t) * I

/-- The horizontal integral from `-1+I` to `I`: top side of the rectangular path. -/
def I12Horiz (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r (-1 + I + ↑t)

/-- `I12Vert` expressed as a segment integral from `-1` to `-1+I`. -/
theorem I12_vert_eq_segment (r : ℝ) :
    I12Vert r = ∫ t in (0 : ℝ)..1,
      viazovskaIntegrandLeft r ((-1 : ℂ) + t • ((-1 + I) - (-1 : ℂ))) *
        ((-1 + I) - (-1 : ℂ)) := by
  simp only [I12Vert]; congr 1; ext t
  congr 1
  · congr 1; simp [Complex.real_smul]; ring
  · ring

/-- `I12Horiz` expressed as a segment integral from `-1+I` to `I`. -/
theorem I12_horiz_eq_segment (r : ℝ) :
    I12Horiz r = ∫ t in (0 : ℝ)..1,
      viazovskaIntegrandLeft r ((-1 + I : ℂ) + t • ((I : ℂ) - (-1 + I))) *
        ((I : ℂ) - (-1 + I)) := by
  simp only [I12Horiz]; congr 1; ext t
  have h1 : (I : ℂ) - (-1 + I) = 1 := by ring
  rw [h1, mul_one]
  congr 1; simp [Complex.real_smul]

/-! ### Truncated contour equivalence

For `δ > 0`, the diagonal integral from `-1 + δI` to `I` equals the
vertical integral from `-1 + δI` to `-1 + I` plus the horizontal integral
from `-1 + I` to `I`. All three segments lie in the upper half-plane,
so path independence (from `holomorphic_convex_primitive`) applies. -/

/-- The point `-1 + δI` lies in the upper half-plane for `δ > 0`. -/
theorem neg_one_add_delta_I_mem_uhp {δ : ℝ} (hδ : 0 < δ) :
    (-1 + ↑δ * I : ℂ) ∈ {z : ℂ | 0 < z.im} := by simpa using hδ

/-- The point `-1 + I` lies in the upper half-plane. -/
theorem neg_one_add_I_mem_uhp : (-1 + I : ℂ) ∈ {z : ℂ | 0 < z.im} := by simp

/-- The point `I` lies in the upper half-plane. -/
theorem I_mem_uhp : (I : ℂ) ∈ {z : ℂ | 0 < z.im} := by simp

/-- Truncated contour equivalence: for `δ > 0`, the diagonal segment integral from
`-1 + δI` to `I` equals the vertical from `-1 + δI` to `-1 + I` plus the
horizontal from `-1 + I` to `I`. This is path independence for holomorphic
functions on the convex open upper half-plane. -/
theorem truncated_contour_equivalence (r : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    let a : ℂ := -1 + ↑δ * I
    let c : ℂ := -1 + I
    let b : ℂ := I
    let F := viazovskaIntegrandLeft r
    (∫ t in (0 : ℝ)..1, F (a + t • (b - a)) * (b - a)) =
    (∫ t in (0 : ℝ)..1, F (a + t • (c - a)) * (c - a)) +
    (∫ t in (0 : ℝ)..1, F (c + t • (b - c)) * (b - c)) :=
  segment_integral_add_of_holomorphic
    isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (viazovska_integrand_left_differentiableOn r)
    (neg_one_add_delta_I_mem_uhp hδ) I_mem_uhp neg_one_add_I_mem_uhp

/-- The horizontal part of the truncated equivalence equals `I12Horiz`.
The segment from `-1+I` to `I` does not depend on `δ`. -/
theorem truncated_horiz_eq_I12_horiz (r : ℝ) :
    (∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r
      ((-1 + I : ℂ) + t • ((I : ℂ) - (-1 + I))) * ((I : ℂ) - (-1 + I))) =
    I12Horiz r := by rw [I12_horiz_eq_segment]

/-- φ₀ is bounded at Im -> infinity. -/
private theorem phi0_bounded_at_infty : UpperHalfPlane.IsBoundedAtImInfty φ₀ :=
  phi0_isBoundedAtImInfty

/-! ### Path-specific cusp decay

Along the diagonal contour `t -> -1 + t(1+I)` and the vertical contour
`t -> -1 + tI`, as `t -> 0+` the substitution `w = -1/(z+1)` sends
`Im(w) -> +infty`. So `phi0_isBoundedAtImInfty` gives a bound on
`phi_0(w)`, and the `(z+1)^2 = O(t^2)` factor drives the integrand to 0. -/

/-- The integrand at `contourNeg1ToI 0 = -1` equals zero, because `(z+1)^2 = 0`. -/
private theorem integrand_at_zero_diag (r : ℝ) :
    viazovskaIntegrandLeft r (contourNeg1ToI 0) * (1 + I) = 0 := by
  simp [viazovskaIntegrandLeft, contourNeg1ToI]

/-- The integrand at vertical contour parameter 0 equals zero. -/
private theorem integrand_at_zero_vert (r : ℝ) :
    viazovskaIntegrandLeft r (-1 + I * (0 : ℝ)) * I = 0 := by simp [viazovskaIntegrandLeft]

/-- The diagonal contour point has positive imaginary part for `t > 0`. -/
private theorem contour_neg1_to_i_im_pos {t : ℝ} (ht : 0 < t) :
    0 < (contourNeg1ToI t).im := by simpa [contourNeg1ToI] using ht

/-- The vertical contour point has positive imaginary part for `t > 0`. -/
private theorem vertical_contour_im_pos {t : ℝ} (ht : 0 < t) :
    0 < (-1 + I * (↑t : ℂ)).im := by simpa using ht

/-! ### Step 5: Cusp decay and integrand boundary behavior

To pass from the truncated contour equivalence (δ > 0) to the full equivalence
(starting at -1), we need the integrand to vanish at z = -1. This follows from
the cusp behavior of φ₀: as z → -1, the substitution w = -1/(z+1) sends
Im(w) → +∞, and the q-expansion of φ₀ shows φ₀(w) = O(e^{-2πIm(w)}).
The factor (z+1)² cancels the 1/w² from the change of variables, leaving
the integrand → 0.

We state the key cusp estimates as sorry'd lemmas (requiring q-expansion
infrastructure) and prove the contour equivalence from them. -/

/-! The general statement `Tendsto (viazovskaIntegrandLeft r) (𝓝[ℍ] (-1)) (𝓝 0)` requires
T-periodicity of φ₀ and compactness arguments on the fundamental domain. Since the main
theorem `I12_eq_rectangular` uses a direct bound on the connecting segment (where
Im(w) ≥ 1/(2δ) → ∞) via `phi0_isBoundedAtImInfty`, this general tendsto is not needed. -/

/-! ### Helpers for cusp-decay continuity at t = 0

Both `continuousOn_diagonal_integrand` and `continuousOn_vertical_integrand` need
an epsilon-delta squeeze at `t = 0` using `phi0_isBoundedAtImInfty`. We factor out
the common sub-arguments into reusable helpers. -/

/-- Along the diagonal contour, `contourNeg1ToI t + 1 = (1+I) * t`. -/
private theorem diag_contour_add_one (t : ℝ) :
    contourNeg1ToI t + 1 = (1 + I) * ↑t := by simp [contourNeg1ToI]

/-- Along the vertical contour, `(-1 + I*t) + 1 = I * t`. -/
private theorem vert_contour_add_one (t : ℝ) :
    (-1 : ℂ) + I * ↑t + 1 = I * ↑t := by ring

/-- Along the diagonal contour, `Im(-1/(z+1)) = 1/(2t)` for `t > 0`. -/
private theorem im_neg_inv_diag {t : ℝ} (ht : 0 < t) :
    (-1 / (contourNeg1ToI t + 1)).im = 1 / (2 * t) := by
  rw [diag_contour_add_one, neg_div, Complex.neg_im, Complex.div_im]
  simp only [one_im, mul_re, add_re, one_re, I_re, add_zero, ofReal_re, one_mul, add_im, I_im,
    zero_add, ofReal_im, mul_zero, sub_zero, zero_mul, map_mul, normSq_ofReal, zero_div, mul_im,
    zero_sub, neg_neg, one_div, mul_inv_rev]
  rw [Complex.normSq_mk]
  simp only [Complex.I_re, Complex.I_im, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im]
  field_simp; ring

/-- Along the vertical contour, `Im(-1/(z+1)) = 1/t` for `t > 0`. -/
private theorem im_neg_inv_vert {t : ℝ} (_ht : 0 < t) :
    (-1 / ((-1 : ℂ) + I * ↑t + 1)).im = 1 / t := by
  rw [vert_contour_add_one, neg_div, Complex.neg_im, Complex.div_im]
  simp

/-- Norm bound for `(z+1)^2` along the diagonal: `‖((1+I)t)^2‖ ≤ 2t^2`. -/
private theorem norm_sq_diag {t : ℝ} (ht : 0 < t) :
    ‖(contourNeg1ToI t + 1) ^ 2‖ ≤ 2 * t ^ 2 := by
  rw [diag_contour_add_one]
  simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [mul_pow]; gcongr ?_ * _
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]

/-- Norm bound for `(z+1)^2` along the vertical: `‖(It)^2‖ ≤ t^2`. -/
private theorem norm_sq_vert {t : ℝ} (ht : 0 < t) :
    ‖((-1 : ℂ) + I * ↑t + 1) ^ 2‖ ≤ t ^ 2 := by
  rw [vert_contour_add_one]
  simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  simp [Complex.norm_I]

/-- Exponential bound along the diagonal contour for `t ∈ (0, 1]`. -/
private theorem exp_bound_diag {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖Complex.exp (↑Real.pi * I * ↑r * contourNeg1ToI t)‖ ≤
      Real.exp (Real.pi * |r| * 2) := by
  rw [Complex.norm_exp]; apply Real.exp_le_exp_of_le
  simp [contourNeg1ToI, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r, ht1,
    mul_le_mul_of_nonneg_right (neg_abs_le r) ht.le,
    mul_le_mul_of_nonneg_left (show t ≤ 2 from by linarith) (abs_nonneg r)]

/-- Exponential bound along the vertical contour for `t ∈ (0, 1]`. -/
private theorem exp_bound_vert {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖Complex.exp (↑Real.pi * I * ↑r * ((-1 : ℂ) + I * ↑t))‖ ≤
      Real.exp (Real.pi * |r|) := by
  rw [Complex.norm_exp]; apply Real.exp_le_exp_of_le
  simp [Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r, ht1,
    mul_le_mul_of_nonneg_right (neg_abs_le r) ht.le,
    mul_le_mul_of_nonneg_left ht1 (abs_nonneg r)]

/-- For small `t > 0`, the phi0 bound `M` applies along the diagonal contour,
because `Im(-1/(z+1)) = 1/(2t) >= A`. -/
private theorem phi0_bound_of_small_diag {t A : ℝ} (ht : 0 < t) (ht_lt : t < 1 / (2 * max A 1))
    (M : ℝ) (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) :
    ‖φ₀'' (-1 / (contourNeg1ToI t + 1))‖ ≤ M := by
  have him_w : 0 < (-1 / (contourNeg1ToI t + 1)).im :=
    neg_inv_add_one_im_pos (contour_neg1_to_i_im_pos ht)
  simp only [φ₀'', him_w, dif_pos]
  refine hMA ⟨_, him_w⟩ ?_
  simp only [UpperHalfPlane.mk_im]; rw [im_neg_inv_diag ht]
  have : max A 1 ≤ 1 / (2 * t) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * max A 1)] at ht_lt
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]; linarith
  linarith [le_max_left A 1]

/-- For small `t > 0`, the phi0 bound `M` applies along the vertical contour,
because `Im(-1/(z+1)) = 1/t >= A`. -/
private theorem phi0_bound_of_small_vert {t A : ℝ} (ht : 0 < t) (ht_lt : t < 1 / max A 1)
    (M : ℝ) (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) :
    ‖φ₀'' (-1 / ((-1 : ℂ) + I * ↑t + 1))‖ ≤ M := by
  have him_w : 0 < (-1 / ((-1 : ℂ) + I * ↑t + 1)).im :=
    neg_inv_add_one_im_pos (vertical_contour_im_pos ht)
  simp only [φ₀'', him_w, dif_pos]
  refine hMA ⟨_, him_w⟩ ?_
  change A ≤ (-1 / ((-1 : ℂ) + I * ↑t + 1)).im
  rw [im_neg_inv_vert ht]
  have : max A 1 ≤ 1 / t := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < max A 1)] at ht_lt
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < t)]; linarith
  linarith [le_max_left A 1]

/-- The integrand norm along the diagonal is bounded by `C * t^2` for small `t > 0`. -/
private theorem integrand_norm_bound_diag {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {M A : ℝ} (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (ht_lt_A : t < 1 / (2 * max A 1)) :
    ‖viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)‖ ≤
      ((M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1) * t ^ 2 := by
  set C_bd := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1
  calc ‖viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)‖
      ≤ ‖viazovskaIntegrandLeft r (contourNeg1ToI t)‖ * ‖(1 : ℂ) + I‖ :=
        norm_mul_le _ _
    _ ≤ (‖φ₀'' (-1 / (contourNeg1ToI t + 1))‖ *
          ‖(contourNeg1ToI t + 1) ^ 2‖ *
          ‖Complex.exp (↑Real.pi * I * ↑r * contourNeg1ToI t)‖) *
        ‖(1 : ℂ) + I‖ := by
        gcongr; unfold viazovskaIntegrandLeft
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (M * (2 * t ^ 2) * Real.exp (Real.pi * |r| * 2)) * ‖(1 : ℂ) + I‖ := by
        gcongr
        · exact phi0_bound_of_small_diag ht ht_lt_A M hMA
        · exact norm_sq_diag ht
        · exact exp_bound_diag ht ht1
    _ ≤ C_bd * t ^ 2 := by
        simp only [C_bd]
        nlinarith [hM_nn, norm_nonneg ((1 : ℂ) + I), Real.exp_pos (Real.pi * |r| * 2),
          sq_nonneg t,
          mul_nonneg (Real.exp_pos (Real.pi * |r| * 2)).le (norm_nonneg ((1 : ℂ) + I))]

/-- The integrand norm along the vertical is bounded by `C * t^2` for small `t > 0`. -/
private theorem integrand_norm_bound_vert {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {M A : ℝ} (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (ht_lt_A : t < 1 / max A 1) :
    ‖viazovskaIntegrandLeft r (-1 + I * ↑t) * I‖ ≤
      ((M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1) * t ^ 2 := by
  set C_bd := (M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1
  calc ‖viazovskaIntegrandLeft r (-1 + I * ↑t) * I‖
      ≤ ‖viazovskaIntegrandLeft r (-1 + I * ↑t)‖ * ‖(I : ℂ)‖ :=
        norm_mul_le _ _
    _ ≤ (‖φ₀'' (-1 / ((-1 : ℂ) + I * ↑t + 1))‖ *
          ‖((-1 : ℂ) + I * ↑t + 1) ^ 2‖ *
          ‖Complex.exp (↑Real.pi * I * ↑r * ((-1 : ℂ) + I * ↑t))‖) *
        ‖(I : ℂ)‖ := by
        gcongr; unfold viazovskaIntegrandLeft
        exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ (M * t ^ 2 * Real.exp (Real.pi * |r|)) * ‖(I : ℂ)‖ := by
        gcongr
        · exact phi0_bound_of_small_vert ht ht_lt_A M hMA
        · exact norm_sq_vert ht
        · exact exp_bound_vert ht ht1
    _ ≤ C_bd * t ^ 2 := by
        simp only [C_bd]
        nlinarith [hM_nn, norm_nonneg (I : ℂ), Real.exp_pos (Real.pi * |r|),
          sq_nonneg t,
          mul_nonneg (Real.exp_pos (Real.pi * |r|)).le (norm_nonneg (I : ℂ))]

/-- At `t = 0`, the diagonal integrand is `ContinuousWithinAt` on `[0, 1]`.
The value is 0 (since `(z+1)^2 = 0`), and the squeeze bound `C * t^2 < epsilon`
holds for small `t`. -/
private theorem continuousWithinAt_zero_diag (r : ℝ) :
    ContinuousWithinAt (fun t : ℝ =>
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I : ℂ))
      (Icc 0 1) 0 := by
  have hval := integrand_at_zero_diag r
  rw [ContinuousWithinAt, hval, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_bounded_at_infty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  set C_bd := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2) * ‖(1 : ℂ) + I‖ + 1
  have hC_pos : 0 < C_bd := by simp only [C_bd]; positivity
  set δ := min (1 / (2 * max A 1)) (Real.sqrt (ε / C_bd))
  filter_upwards [inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0
    (by positivity : 0 < δ))) self_mem_nhdsWithin] with t ⟨ht_ball, ht_Icc⟩
  simp only [dist_zero_right]
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht_ball
  by_cases ht0 : t = 0
  · rw [ht0, hval]; simp only [norm_zero, gt_iff_lt]; exact hε
  · have ht_pos : 0 < t := lt_of_le_of_ne ht_Icc.1 (Ne.symm ht0)
    have ht_abs : t < δ := by rwa [abs_of_pos ht_pos] at ht_ball
    calc ‖viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)‖
        ≤ C_bd * t ^ 2 := integrand_norm_bound_diag ht_pos ht_Icc.2 hMA
            (le_max_right _ _) (lt_of_lt_of_le ht_abs (min_le_left _ _))
      _ < C_bd * (ε / C_bd) := by
          gcongr
          calc t ^ 2 < (Real.sqrt (ε / C_bd)) ^ 2 :=
                pow_lt_pow_left₀ (lt_of_lt_of_le ht_abs (min_le_right _ _))
                  ht_pos.le (by norm_num : 2 ≠ 0)
            _ = ε / C_bd := Real.sq_sqrt (by positivity)
      _ = ε := by field_simp

/-- At `t = 0`, the vertical integrand is `ContinuousWithinAt` on `[0, 1]`. -/
private theorem continuousWithinAt_zero_vert (r : ℝ) :
    ContinuousWithinAt (fun t : ℝ =>
      viazovskaIntegrandLeft r (-1 + I * ↑t) * I)
      (Icc 0 1) 0 := by
  have hval := integrand_at_zero_vert r
  rw [ContinuousWithinAt, hval, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_bounded_at_infty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  set C_bd := (M + 1) * Real.exp (Real.pi * |r|) * ‖(I : ℂ)‖ + 1
  have hC_pos : 0 < C_bd := by simp only [C_bd]; positivity
  set δ := min (1 / max A 1) (Real.sqrt (ε / C_bd))
  filter_upwards [inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0
    (by positivity : 0 < δ))) self_mem_nhdsWithin] with t ⟨ht_ball, ht_Icc⟩
  simp only [dist_zero_right]
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht_ball
  by_cases ht0 : t = 0
  · rw [ht0, hval]; simp only [norm_zero, gt_iff_lt]; exact hε
  · have ht_pos : 0 < t := lt_of_le_of_ne ht_Icc.1 (Ne.symm ht0)
    have ht_abs : t < δ := by rwa [abs_of_pos ht_pos] at ht_ball
    calc ‖viazovskaIntegrandLeft r (-1 + I * ↑t) * I‖
        ≤ C_bd * t ^ 2 := integrand_norm_bound_vert ht_pos ht_Icc.2 hMA
            (le_max_right _ _) (lt_of_lt_of_le ht_abs (min_le_left _ _))
      _ < C_bd * (ε / C_bd) := by
          gcongr
          calc t ^ 2 < (Real.sqrt (ε / C_bd)) ^ 2 :=
                pow_lt_pow_left₀ (lt_of_lt_of_le ht_abs (min_le_right _ _))
                  ht_pos.le (by norm_num : 2 ≠ 0)
            _ = ε / C_bd := Real.sq_sqrt (by positivity)
      _ = ε := by field_simp

/-- The parameterized diagonal integrand is continuous on `[0,1]`. -/
theorem continuousOn_diagonal_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I : ℂ))
      (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · exact continuousWithinAt_zero_diag r
  · exact ((viazovska_integrand_left_differentiableOn r).continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
      (fun t ht => contour_neg1_to_i_im_pos ht) |>.mul continuousOn_const
      |>.continuousAt (Ioi_mem_nhds hx_pos)).continuousWithinAt

/-- The parameterized vertical integrand is continuous on `[0,1]`. -/
theorem continuousOn_vertical_integrand (r : ℝ) :
    ContinuousOn (fun t : ℝ =>
      viazovskaIntegrandLeft r (-1 + I * ↑t) * I)
      (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · exact continuousWithinAt_zero_vert r
  · exact ((viazovska_integrand_left_differentiableOn r).continuousOn.comp
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
      (fun t ht => vertical_contour_im_pos ht) |>.mul continuousOn_const
      |>.continuousAt (Ioi_mem_nhds hx_pos)).continuousWithinAt

/-! ### Step 5b: FTC-based limit argument

The key observation is that all segment integrals equal `G(endpoint) - G(startpoint)`
for a primitive `G` on the upper half-plane. As `δ → 0`, the starting point
`-1 + δI` approaches `-1`, and `G(-1 + δI)` converges by continuity.

We work with the primitive directly to avoid dominated convergence. -/

/-- The primitive `G` of `viazovskaIntegrandLeft r` on the upper half-plane,
whose existence follows from `holomorphic_convex_primitive`. -/
theorem exists_primitive_viazovska_integrand_left (r : ℝ) :
    ∃ G : ℂ → ℂ, ∀ z ∈ {z : ℂ | 0 < z.im},
      HasDerivAt G (viazovskaIntegrandLeft r z) z :=
  holomorphic_convex_primitive convex_upperHalfPlaneSet
    isOpen_upperHalfPlaneSet ⟨I, I_mem_uhp⟩ (viazovska_integrand_left_differentiableOn r)

/-- The truncated diagonal integral from `-1 + δI` to `I` equals `G(I) - G(-1+δI)`
for the primitive `G` of the integrand. -/
theorem truncated_diagonal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r
      ((-1 + ↑δ * I) + t • ((I : ℂ) - (-1 + ↑δ * I))) *
        ((I : ℂ) - (-1 + ↑δ * I))) = G I - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ) I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The truncated vertical integral from `-1 + δI` to `-1 + I` equals
`G(-1+I) - G(-1+δI)` for the primitive. -/
theorem truncated_vertical_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r
      ((-1 + ↑δ * I) + t • ((-1 + I) - (-1 + ↑δ * I))) *
        ((-1 + I) - (-1 + ↑δ * I))) = G (-1 + I) - G (-1 + ↑δ * I) :=
  segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    (neg_one_add_delta_I_mem_uhp hδ) neg_one_add_I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-- The horizontal integral from `-1 + I` to `I` equals `G(I) - G(-1+I)`. -/
theorem horizontal_eq_primitive_sub (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z) :
    I12Horiz r = G I - G (-1 + I) := by
  rw [I12_horiz_eq_segment]
  exact segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet convex_upperHalfPlaneSet
    neg_one_add_I_mem_uhp I_mem_uhp hG
    (viazovska_integrand_left_differentiableOn r).continuousOn

/-! ### Step 6: Full contour equivalence via primitive cancellation

The full contour equivalence `I12 = I12Vert + I12Horiz` follows from
the primitive approach: both sides equal `G(I) - lim_{δ→0} G(-1+δI)`.

The truncated versions give:
- Diagonal: `G(I) - G(-1+δI)`
- Vertical + Horizontal: `(G(-1+I) - G(-1+δI)) + (G(I) - G(-1+I)) = G(I) - G(-1+δI)`

So truncated diagonal = truncated vertical + horizontal for all δ > 0.
Taking δ → 0 and using continuity of the integrals gives the result. -/

/-- `I12` equals the integral restricted to `[δ, 1]` plus the integral on `[0, δ]`.
For continuous integrands (from `continuousOn_diagonal_integrand`), the `[0, δ]` part
vanishes as `δ → 0`. -/
theorem I12_split_at_delta (r : ℝ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hcont : ContinuousOn (fun t : ℝ =>
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I : ℂ)) (Icc 0 1)) :
    I12 r = (∫ t in (0 : ℝ)..δ,
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)) +
      (∫ t in δ..1,
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)) := by
  have hI12 : I12 r = ∫ t in (0 : ℝ)..1,
      viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I) := by
    unfold I12; congr 1; ext t; rw [deriv_contour_neg1_to_i]
  rw [hI12]
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : (0 : ℝ) ≤ 1)
  have hδ_mem : δ ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc.mpr (Or.inl ⟨hδ₀, hδ₁⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (Set.uIcc_subset_uIcc_left hδ_mem))
    (hint.mono_set (Set.uIcc_subset_uIcc_right hδ_mem))).symm

/-- `I12Vert` equals the integral restricted to `[δ, 1]` plus the integral on `[0, δ]`. -/
theorem I12_vert_split_at_delta (r : ℝ) (δ : ℝ) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hcont : ContinuousOn (fun t : ℝ =>
      viazovskaIntegrandLeft r (-1 + I * ↑t) * I) (Icc 0 1)) :
    I12Vert r = (∫ t in (0 : ℝ)..δ,
      viazovskaIntegrandLeft r (-1 + I * ↑t) * I) +
      (∫ t in δ..1,
      viazovskaIntegrandLeft r (-1 + I * ↑t) * I) := by
  unfold I12Vert
  have hint := hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : (0 : ℝ) ≤ 1)
  have hδ_mem : δ ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc.mpr (Or.inl ⟨hδ₀, hδ₁⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (Set.uIcc_subset_uIcc_left hδ_mem))
    (hint.mono_set (Set.uIcc_subset_uIcc_right hδ_mem))).symm

/-! ### Helpers for I12_eq_rectangular

The proof of `I12_eq_rectangular` decomposes into:
1. Chain rule / FTC for tail integrals
2. An algebraic identity expressing the difference as three small terms
3. Each of those three terms tending to zero as delta -> 0+
4. Tendsto uniqueness to conclude -/

/-- FTC for the tail diagonal integral: for delta in (0, 1], the integral from
delta to 1 of the diagonal integrand equals G(I) - G(contour(delta)). -/
private theorem ftc_tail_diag (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in δ..1, viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I) =
      G (contourNeg1ToI 1) - G (contourNeg1ToI δ) := by
  have hcont := continuousOn_diagonal_integrand r
  have hGdiag : ∀ t ∈ Set.uIcc δ 1, HasDerivAt (fun s => G (contourNeg1ToI s))
      (viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)) t := by
    intro t ht
    have ht_pos : 0 < t := by rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    exact ((@HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
      (hG _ (contour_neg1_to_i_im_pos ht_pos))
      (hasDerivAt_contour_neg1_to_i t))).congr_deriv (by simp [smul_eq_mul]; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hGdiag
    ((hcont.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable_of_Icc
      (by linarith))
  simpa [Function.comp] using h

/-- FTC for the tail vertical integral: for delta in (0, 1], the integral from
delta to 1 of the vertical integrand equals G(-1+I) - G(-1+delta*I). -/
private theorem ftc_tail_vert (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in δ..1, viazovskaIntegrandLeft r (-1 + I * ↑t) * I =
      G (-1 + I * (1 : ℝ)) - G (-1 + I * ↑δ) := by
  have hcont := continuousOn_vertical_integrand r
  have hGvert : ∀ t ∈ Set.uIcc δ 1, HasDerivAt (fun s : ℝ => G (-1 + I * ↑s))
      (viazovskaIntegrandLeft r (-1 + I * ↑t) * I) t := by
    intro t ht
    have ht_pos : 0 < t := by rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
    exact ((@HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
      (hG _ (vertical_contour_im_pos ht_pos))
      (hasDerivAt_vert_contour t))).congr_deriv (by simp [smul_eq_mul]; ring)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hGvert
    ((hcont.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable_of_Icc
      (by linarith))

/-- For each delta in (0, 1], the difference `I12 - (I12Vert + I12Horiz)` equals
the sum of two head integrals plus a G-difference. -/
private theorem D_eq_three_terms (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    I12 r - (I12Vert r + I12Horiz r) =
      (∫ t in (0 : ℝ)..δ, viazovskaIntegrandLeft r (contourNeg1ToI t) * (1 + I)) -
      (∫ t in (0 : ℝ)..δ, viazovskaIntegrandLeft r (-1 + I * ↑t) * I) +
      (G (-1 + ↑δ * I) - G (contourNeg1ToI δ)) := by
  have hcont_diag := continuousOn_diagonal_integrand r
  have hcont_vert := continuousOn_vertical_integrand r
  have hsd := I12_split_at_delta r δ hδ.le hδ1 hcont_diag
  have hsv := I12_vert_split_at_delta r δ hδ.le hδ1 hcont_vert
  have htd := ftc_tail_diag r G hG δ hδ hδ1
  have hc1 : contourNeg1ToI 1 = I := by simp [contourNeg1ToI]
  rw [hc1] at htd
  have htv := ftc_tail_vert r G hG δ hδ hδ1
  have hv1 : (-1 : ℂ) + I * (1 : ℝ) = -1 + I := by push_cast; ring
  rw [hv1] at htv
  have hhoriz := horizontal_eq_primitive_sub r G hG
  have hcomm : (-1 : ℂ) + ↑δ * I = -1 + I * ↑δ := by ring
  rw [hcomm]
  linear_combination hsd + htd - hsv - htv - hhoriz

/-- A bounded continuous integrand on `[0,1]` has its head integral
`integral_0^delta` tending to zero as `delta -> 0+`. -/
private theorem head_integral_tendsto_zero {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Icc 0 1)) :
    Filter.Tendsto (fun δ => ∫ t in (0 : ℝ)..δ, f t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hC_nn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_refl _, zero_le_one⟩)
  rw [Metric.tendsto_nhds]; intro ε hε
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds 0 (show 0 < min (ε / (C + 1)) 1 by positivity)]
    with δ hball hδ_pos
  simp only [Set.mem_Ioi] at hδ_pos
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
  rw [abs_of_pos hδ_pos] at hball
  rw [dist_zero_right]
  calc ‖∫ t in (0 : ℝ)..δ, f t‖
      ≤ (C + 1) * |δ - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht; rcases Set.mem_uIoc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hC t ⟨by linarith, by linarith [lt_of_lt_of_le hball (min_le_right _ _)]⟩).trans
            (by linarith)
        · linarith
    _ < (C + 1) * (ε / (C + 1)) := by
        rw [sub_zero, abs_of_pos hδ_pos]
        exact mul_lt_mul_of_pos_left
          (lt_of_lt_of_le hball (min_le_left _ _)) (by linarith)
    _ = ε := by field_simp

/-- The norm of the integrand on the connecting segment from `-1+delta(1+I)` to
`-1+delta*I` is bounded by `delta`, for sufficiently small `delta`. -/
private theorem segment_integrand_norm_bound (r : ℝ) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ1 : δ ≤ 1) {M A : ℝ}
    (hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M) (hM_nn : 0 ≤ M)
    (hδ_lt_A : δ < 1 / (2 * max A 1))
    (hδ_lt_sqrt : δ < Real.sqrt (1 / ((M + 1) * 2 * Real.exp (Real.pi * |r| * 2))))
    {t : ℝ} (ht1 : 0 < t) (ht2 : t ≤ 1) :
    let a : ℂ := -1 + ↑δ * ((1 : ℂ) + I)
    let dir : ℂ := -(↑δ : ℂ)
    ‖viazovskaIntegrandLeft r (a + ↑t • dir) * dir‖ ≤ δ := by
  intro a dir
  set z₀ := a + ↑t • dir
  have him : 0 < z₀.im := by
    simp [z₀, a, dir, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.one_im, Complex.one_re]; linarith
  have hz_plus_1 : z₀ + 1 = ↑δ * ((1 - ↑t : ℂ) + I) := by simp [z₀, a, dir]; ring
  have him_w : 0 < (-1 / (z₀ + 1)).im := neg_inv_add_one_im_pos him
  have hnsq : Complex.normSq (z₀ + 1) = δ ^ 2 * ((1 - t) ^ 2 + 1) := by
    rw [hz_plus_1, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]; ring
  have him_eq : (z₀ + 1).im = δ := by
    rw [hz_plus_1]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.one_im]
  -- Im(-1/(z+1)) >= 1/(2*delta) >= A
  have h1t_sq : (1 - t) ^ 2 + 1 ≤ 2 := by nlinarith
  have him_lb : 1 / (2 * δ) ≤ (-1 / (z₀ + 1)).im := by
    rw [neg_div, Complex.neg_im, Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, zero_sub, neg_neg]
    rw [hnsq, him_eq]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)
      (by positivity : 0 < δ ^ 2 * ((1 - t) ^ 2 + 1))]
    nlinarith [sq_nonneg δ]
  have hA_le : A ≤ (-1 / (z₀ + 1)).im := by
    have : max A 1 ≤ 1 / (2 * δ) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * max A 1)] at hδ_lt_A
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]; linarith
    linarith [le_max_left A 1]
  -- Bound phi0, (z+1)^2, exp
  have hφ : ‖φ₀'' (-1 / (z₀ + 1))‖ ≤ M := by
    simp only [φ₀'', him_w, dif_pos]
    exact hMA ⟨_, him_w⟩ (by simp [UpperHalfPlane.im]; linarith)
  have hsq : ‖(z₀ + 1) ^ 2‖ ≤ 2 * δ ^ 2 := by
    rw [norm_pow, ← Complex.normSq_eq_norm_sq, hnsq]
    nlinarith [sq_nonneg δ, h1t_sq]
  have hexp : ‖Complex.exp (↑Real.pi * I * ↑r * z₀)‖ ≤
      Real.exp (Real.pi * |r| * 2) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp_of_le
    simp [z₀, a, dir, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.one_im, Complex.one_re]
    nlinarith [Real.pi_pos, neg_abs_le r, abs_nonneg r,
      mul_le_mul_of_nonneg_right (neg_abs_le r) hδ_pos.le,
      mul_le_mul_of_nonneg_left hδ1 (abs_nonneg r)]
  -- ||F(z0)|| <= C_seg * delta^2 <= 1
  set C_seg := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2)
  have hC_seg_pos : 0 < C_seg := by positivity
  have hFb : ‖viazovskaIntegrandLeft r z₀‖ ≤ 1 := by
    have hF_unfold : ‖viazovskaIntegrandLeft r z₀‖ ≤
        ‖φ₀'' (-1 / (z₀ + 1))‖ * ‖(z₀ + 1) ^ 2‖ *
        ‖Complex.exp (↑Real.pi * I * ↑r * z₀)‖ := by
      unfold viazovskaIntegrandLeft
      exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    have hCδ : C_seg * δ ^ 2 ≤ 1 := by
      have h1 : δ ^ 2 < (Real.sqrt (1 / C_seg)) ^ 2 :=
        pow_lt_pow_left₀ hδ_lt_sqrt hδ_pos.le (by norm_num : 2 ≠ 0)
      rw [Real.sq_sqrt (by positivity)] at h1
      have h2 : C_seg * δ ^ 2 < C_seg * (1 / C_seg) :=
        mul_lt_mul_of_pos_left h1 hC_seg_pos
      simp [ne_of_gt hC_seg_pos] at h2; linarith
    calc ‖viazovskaIntegrandLeft r z₀‖
        ≤ M * (2 * δ ^ 2) * Real.exp (Real.pi * |r| * 2) :=
          hF_unfold.trans (by gcongr)
      _ ≤ C_seg * δ ^ 2 := by
          simp only [C_seg]
          nlinarith [hM_nn, Real.exp_pos (Real.pi * |r| * 2), sq_nonneg δ]
      _ ≤ 1 := hCδ
  -- ||F(z0) * dir|| = ||F(z0)|| * delta <= 1 * delta = delta
  have hneg_norm : ‖dir‖ = δ := by
    change ‖(-(↑δ : ℂ))‖ = δ
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
  calc ‖viazovskaIntegrandLeft r z₀ * dir‖
      ≤ ‖viazovskaIntegrandLeft r z₀‖ * ‖dir‖ := norm_mul_le _ _
    _ ≤ 1 * δ := by rw [hneg_norm]; exact mul_le_mul_of_nonneg_right hFb hδ_pos.le
    _ = δ := one_mul _

/-- The G-difference `G(-1 + delta*I) - G(contourNeg1ToI delta)` tends to 0
as `delta -> 0+`. This is the hardest piece: we express the difference as a
segment integral and bound the integrand using the phi0 cusp decay. -/
private theorem G_diff_tendsto_zero (r : ℝ) (G : ℂ → ℂ)
    (hG : ∀ z ∈ {z : ℂ | 0 < z.im}, HasDerivAt G (viazovskaIntegrandLeft r z) z) :
    Filter.Tendsto
      (fun δ : ℝ => G (-1 + ↑δ * I) - G (contourNeg1ToI δ)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro ε hε
  obtain ⟨M₀, A, hMA₀⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp phi0_bounded_at_infty
  set M := max M₀ 0
  have hMA : ∀ z : UpperHalfPlane, A ≤ z.im → ‖φ₀ z‖ ≤ M :=
    fun z hz => (hMA₀ z hz).trans (le_max_left _ _)
  have hM_nn : (0 : ℝ) ≤ M := le_max_right _ _
  set C_seg := (M + 1) * 2 * Real.exp (Real.pi * |r| * 2)
  have hC_seg_pos : 0 < C_seg := by positivity
  set δ_bd := min (min ε (1 / (2 * max A 1))) (min (Real.sqrt (1 / C_seg)) 1)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds 0 (by positivity : 0 < δ_bd)] with δ hball_δ hδ_pos
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, Set.mem_Ioi] at hball_δ hδ_pos
  rw [abs_of_pos hδ_pos] at hball_δ
  have hδ_lt_ε : δ < ε :=
    lt_of_lt_of_le hball_δ (min_le_left _ _ |>.trans (min_le_left _ _))
  have hδ_lt_A : δ < 1 / (2 * max A 1) :=
    lt_of_lt_of_le hball_δ (min_le_left _ _ |>.trans (min_le_right _ _))
  have hδ_lt_sqrt : δ < Real.sqrt (1 / C_seg) :=
    lt_of_lt_of_le hball_δ (min_le_right _ _ |>.trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hball_δ (min_le_right _ _ |>.trans (min_le_right _ _)))
  -- Express G-diff as segment integral via FTC
  have hcδ : contourNeg1ToI δ = -1 + ↑δ * ((1 : ℂ) + I) := by simp [contourNeg1ToI]; ring
  rw [dist_zero_right, hcδ]
  set a : ℂ := -1 + ↑δ * ((1 : ℂ) + I)
  set dir : ℂ := -(↑δ : ℂ)
  have ha_uhp : a ∈ {z : ℂ | 0 < z.im} := by
    simp only [a, Set.mem_setOf_eq, Complex.add_im, Complex.neg_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.one_re,
      Complex.I_re, Complex.I_im]; nlinarith
  have hb_uhp := neg_one_add_delta_I_mem_uhp hδ_pos
  have hdir_eq : (-1 + ↑δ * I : ℂ) - a = dir := by simp [a, dir]; ring
  have hG_seg : G (-1 + ↑δ * I) - G a =
      ∫ t in (0 : ℝ)..1, viazovskaIntegrandLeft r (a + ↑t • dir) * dir := by
    rw [show dir = (-1 + ↑δ * I : ℂ) - a from hdir_eq.symm]
    symm; exact segment_integral_eq_sub_of_hasDerivAt isOpen_upperHalfPlaneSet
      convex_upperHalfPlaneSet ha_uhp hb_uhp hG
      (viazovska_integrand_left_differentiableOn r).continuousOn
  rw [hG_seg]
  have hpt_bound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖viazovskaIntegrandLeft r (a + ↑t • dir) * dir‖ ≤ δ := by
    intro t ht
    rcases Set.mem_uIoc.mp ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    swap; · linarith
    exact segment_integrand_norm_bound r hδ_pos hδ1 hMA hM_nn hδ_lt_A hδ_lt_sqrt ht1 ht2
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt_bound
  simp only [sub_zero, abs_one, mul_one] at hbound
  linarith

/-- **Full contour equivalence**: the diagonal integral `I12` from `-1` to `I`
equals the sum of the vertical integral `I12Vert` (from `-1` to `-1+I`)
and the horizontal integral `I12Horiz` (from `-1+I` to `I`). -/
theorem I12_eq_rectangular (r : ℝ) : I12 r = I12Vert r + I12Horiz r := by
  suffices hsuff : I12 r - (I12Vert r + I12Horiz r) = 0 from eq_of_sub_eq_zero hsuff
  obtain ⟨G, hG⟩ := exists_primitive_viazovska_integrand_left r
  set F := viazovskaIntegrandLeft r
  -- Abbreviation for the three-term sum that each delta maps to
  set S := fun δ : ℝ => (∫ t in (0 : ℝ)..δ, F (contourNeg1ToI t) * (1 + I)) -
    (∫ t in (0 : ℝ)..δ, F (-1 + I * ↑t) * I) + (G (-1 + ↑δ * I) - G (contourNeg1ToI δ))
  -- D = S(delta) for all delta in (0,1], and S(delta) -> 0
  have heq : ∀ᶠ δ in 𝓝[>] 0, I12 r - (I12Vert r + I12Horiz r) = S δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with δ hδ hδ_ball
    simp only [Set.mem_Ioi] at hδ; simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hδ_ball
    exact D_eq_three_terms r G hG δ hδ (by linarith [abs_of_pos hδ])
  have hS : Filter.Tendsto S (𝓝[>] 0) (𝓝 0) := by
    have := (head_integral_tendsto_zero (continuousOn_diagonal_integrand r)).sub
      (head_integral_tendsto_zero (continuousOn_vertical_integrand r))
      |>.add (G_diff_tendsto_zero r G hG)
    convert this using 1; ext; ring
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hS

/-! ### Summary of sorry dependencies

Remaining sorry'd lemmas:

All sorries have been filled:
- `phi0_bounded_at_infty` — via `CuspDecay.lean` import
- `continuousOn_diagonal_integrand` — direct squeeze bound using `phi0_isBoundedAtImInfty`
- `continuousOn_vertical_integrand` — same pattern as diagonal
- `I12_eq_rectangular` — primitive + FTC + limit argument, with direct segment bound
  (avoids `viazovska_integrand_left_tendsto_zero` by bounding φ₀ on the connecting
  segment where Im(w) ≥ 1/(2δ) → ∞) -/

end
