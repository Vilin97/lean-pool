/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.RCLike.Extend
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviForm
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analysis.LinearFunctional
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Topology.Frontier

/-!
# Levi convex boundaries

A local `C²` defining function for an open set `U` at a boundary point `p` is a `C²` function
`ρ` on an open neighborhood `V` of `p`, vanishing at `p`, with nonzero derivative at `p`, such
that `U ∩ V` is the set where `ρ` is negative. The complex tangent space at `p` is the kernel of
the complex-linear part of the derivative of `ρ`. The set `U` satisfies the Levi condition at
`p` if the Levi form of every local defining function is positive semidefinite on the complex
tangent space; it is Levi pseudoconvex if this holds at every boundary point. Quantifying over
all defining functions avoids the lemma that two defining functions differ by a positive factor.

This file proves that convex open sets are Levi pseudoconvex: along a real tangent line the
defining function vanishes to first order at `p`, so a negative second derivative would put two
symmetric points of the line into `U` and, by convexity, the boundary point itself.

It also provides the complex-linear part `complexPart ℓ` of a real functional `ℓ`, with `ℓ (ζ •
c) = Re (ζ * complexPart ℓ c)`, and the decomposition of a symmetric real bilinear form along a
complex line into a Hermitian part, the Levi form, and the real part of a complex quadratic
term. Both are used for the Levi polynomial in `LeviConvexity.Necessity`.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 4;
[Range][Range1986] (1986), Chapter II, Sections 2.4–2.6.

## Main definitions

* `complexPart`: The complex-linear part of a real functional: `ℓ c - I * ℓ (I • c)`.
* `IsLocalDefiningFunction`: A local `C²` defining function for `U` at `p` on the open neighborhood
  `V`: `ρ p = 0`, the real derivative of `ρ` at `p` is nonzero, and `U ∩ V` is the negative sublevel
  set of `ρ` in `V`.
* `HasC2Boundary`: A set has `C²` boundary if every boundary point has a local defining function.
* `IsComplexTangent`: The complex tangent space of the level set of `ρ` at `p`: the kernel of the
  complex-linear part of the derivative.
* `IsLeviPseudoconvexAt`: The Levi condition at a boundary point: the Levi form of every local
  defining function is positive semidefinite on the complex tangent space.
* `IsLeviPseudoconvex`: Levi pseudoconvexity: the Levi condition at every boundary point.

## Main results

* `bilinear_smul_smul_eq`: **Quadratic decomposition along a complex line.** For a symmetric real
  bilinear form `B`, `B (ζ • w) (ζ • w) / 2` is `‖ζ‖ ^ 2` times the Hermitian part `(B w w + B (I •
  w) (I • w)) / 4` plus the real part of `ζ ^ 2` times the complex quadratic coefficient `(B w w - B
  (I • w) (I • w)) / 4 - I / 2 * B w (I • w)`.
* `Convex.isLeviPseudoconvex`: **Convex open sets are Levi pseudoconvex** ([Range][Range1986], Lemma
  2.10).

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section ComplexPart

/-- The complex-linear part `c ↦ ℓ c - I * ℓ (I • c)` of a real functional: Mathlib's
`StrongDual.extendRCLike` with the scalar field fixed to `ℂ`. -/
abbrev complexPart (ℓ : E →L[ℝ] ℝ) : E →L[ℂ] ℂ := StrongDual.extendRCLike ℓ

/-- The defining formula of the complex-linear part. -/
theorem complexPart_apply (ℓ : E →L[ℝ] ℝ) (c : E) :
    complexPart ℓ c = (ℓ c : ℂ) - I * (ℓ (I • c) : ℂ) := rfl

/-- A real functional on a complex multiple is the real part of the complex multiple of its
complex-linear part. -/
theorem apply_smul_eq_re_mul_complexPart (ℓ : E →L[ℝ] ℝ) (ζ : ℂ) (c : E) :
    ℓ (ζ • c) = (ζ * complexPart ℓ c).re := by
  rw [Complex.smul_eq_re_smul_add_im_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    complexPart_apply]
  simp [Complex.mul_re, Complex.mul_im]

/-- The real part of the complex part of a real functional is the functional itself. -/
theorem re_complexPart (ℓ : E →L[ℝ] ℝ) (c : E) : (complexPart ℓ c).re = ℓ c := by
  simp [complexPart_apply]

/-- A nonzero real functional has a vector on which its complex-linear part is nonzero. -/
theorem exists_complexPart_ne_zero {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : ∃ c, complexPart ℓ c ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, ℓ c ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  refine ⟨c, fun h => hc ?_⟩
  rw [← re_complexPart, h, Complex.zero_re]

/-- Every complex value is attained by the complex-linear part of a nonzero real functional. -/
theorem exists_complexPart_eq {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) (q : ℂ) :
    ∃ c, complexPart ℓ c = q := by
  obtain ⟨c₀, hc₀⟩ := exists_complexPart_ne_zero hℓ
  refine ⟨(q / complexPart ℓ c₀) • c₀, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc₀]

/-- **Quadratic decomposition along a complex line.** For a symmetric real bilinear form `B`,
`B (ζ • w) (ζ • w) / 2` is `‖ζ‖ ^ 2` times the Hermitian part
`(B w w + B (I • w) (I • w)) / 4` plus the real part of `ζ ^ 2` times the complex quadratic
coefficient `(B w w - B (I • w) (I • w)) / 4 - I / 2 * B w (I • w)`. -/
theorem bilinear_smul_smul_eq (B : E →L[ℝ] E →L[ℝ] ℝ) {w : E}
    (hsymm : B w (I • w) = B (I • w) w) (ζ : ℂ) :
    (1 / 2 : ℝ) * B (ζ • w) (ζ • w) =
      ‖ζ‖ ^ 2 * ((B w w + B (I • w) (I • w)) / 4) +
        (ζ ^ 2 * (((B w w - B (I • w) (I • w)) / 4 : ℝ) - I / 2 * B w (I • w))).re := by
  rw [Complex.smul_eq_re_smul_add_im_smul]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hsymm]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

end ComplexPart

section Defining

/-- A local `C²` defining function for `U` at `p` on the open neighborhood `V`: `ρ p = 0`, the real
derivative of `ρ` at `p` is nonzero, and `U ∩ V` is the negative sublevel set of `ρ` in `V`. -/
structure IsLocalDefiningFunction (U : Set E) (p : E) (ρ : E → ℝ) (V : Set E) : Prop where
  /-- The defining neighborhood is open. -/
  isOpen : IsOpen V
  /-- The boundary point lies in the defining neighborhood. -/
  mem : p ∈ V
  /-- The defining function is twice continuously real differentiable. -/
  contDiffOn : ContDiffOn ℝ 2 ρ V
  /-- The defining function vanishes at the boundary point. -/
  eq_zero : ρ p = 0
  /-- The real derivative is nonzero at the boundary point. -/
  fderiv_ne : fderiv ℝ ρ p ≠ 0
  /-- The domain is the negative sublevel set in the defining neighborhood. -/
  inter_eq : U ∩ V = {z | ρ z < 0} ∩ V

/-- A set has `C²` boundary if every boundary point has a local defining function. -/
@[expose] def HasC2Boundary (U : Set E) : Prop :=
  ∀ p ∈ frontier U, ∃ (ρ : E → ℝ) (V : Set E), IsLocalDefiningFunction U p ρ V

/-- The complex tangent space of the level set of `ρ` at `p`: the kernel of the complex-linear part
of the derivative. -/
@[expose] def IsComplexTangent (ρ : E → ℝ) (p w : E) : Prop :=
  fderiv ℝ ρ p w = 0 ∧ fderiv ℝ ρ p (I • w) = 0

/-- The Levi condition at a boundary point: the Levi form of every local defining function is
positive semidefinite on the complex tangent space. -/
@[expose] def IsLeviPseudoconvexAt (U : Set E) (p : E) : Prop :=
  ∀ (ρ : E → ℝ) (V : Set E), IsLocalDefiningFunction U p ρ V →
    ∀ w, IsComplexTangent ρ p w → 0 ≤ leviForm ρ p w

/-- Levi pseudoconvexity: the Levi condition at every boundary point. -/
@[expose] def IsLeviPseudoconvex (U : Set E) : Prop :=
  ∀ p ∈ frontier U, IsLeviPseudoconvexAt U p

/-- The complex tangent space is closed under multiplication by `I`. -/
theorem IsComplexTangent.smul_I {ρ : E → ℝ} {p w : E} (h : IsComplexTangent ρ p w) :
    IsComplexTangent ρ p (I • w) := by
  refine ⟨h.2, ?_⟩
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, h.1, neg_zero]

/-- Points near `p` where the defining function is negative lie in `U`. -/
theorem IsLocalDefiningFunction.mem_of_neg {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}
    (h : IsLocalDefiningFunction U p ρ V) {z : E} (hz : z ∈ V) (hρ : ρ z < 0) : z ∈ U := by
  have : z ∈ {z | ρ z < 0} ∩ V := ⟨hρ, hz⟩
  rw [← h.inter_eq] at this
  exact this.1

/-- Points of `V` in `U` have negative defining function. -/
theorem IsLocalDefiningFunction.neg_of_mem {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}
    (h : IsLocalDefiningFunction U p ρ V) {z : E} (hz : z ∈ V) (hU : z ∈ U) : ρ z < 0 := by
  have : z ∈ U ∩ V := ⟨hU, hz⟩
  rw [h.inter_eq] at this
  exact this.1

end Defining

section Convex

variable {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}

/-- Along a real tangent direction, the second derivative of a defining function of a convex open
set is nonnegative. -/
theorem IsLocalDefiningFunction.fderiv_fderiv_nonneg_of_convex (hU : IsOpen U)
    (hconv : Convex ℝ U) (hp : p ∈ frontier U) (h : IsLocalDefiningFunction U p ρ V)
    {w : E} (hw : fderiv ℝ ρ p w = 0) : 0 ≤ fderiv ℝ (fderiv ℝ ρ) p w w := by
  by_contra hneg
  push Not at hneg
  set A := fderiv ℝ (fderiv ℝ ρ) p w w with hA
  -- the slice along the complex line through `p` in direction `w`
  set g : ℂ → ℝ := fun t => ρ (p + t • w) with hg
  have hρp : ContDiffAt ℝ 2 ρ (p + (0 : ℂ) • w) := by
    simpa using h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)
  have hgc : ContDiffAt ℝ 2 g 0 := hρp.comp 0
    (by fun_prop : ContDiff ℝ 2 fun t : ℂ => p + t • w).contDiffAt
  obtain ⟨δ₁, hδ₁, htaylor⟩ := exists_taylor_bound hgc (ε := -A / 4) (by linarith)
  obtain ⟨δ₂, hδ₂, hV⟩ := Metric.mem_nhds_iff.mp
    ((by fun_prop : Continuous fun t : ℂ => p + t • w).continuousAt.preimage_mem_nhds (by
      change V ∈ 𝓝 ((fun t : ℂ => p + t • w) 0)
      simpa using h.isOpen.mem_nhds h.mem))
  have hD1 : fderiv ℝ g 0 = (fderiv ℝ ρ p).comp ((ContinuousLinearMap.id ℝ ℂ).smulRight w) := by
    have := fderiv_slice (f := ρ) (a := p) (w := w) (t₀ := 0) (hρp.differentiableAt (by norm_num))
    simpa using this
  have hD2 : ∀ s s' : ℂ, fderiv ℝ (fderiv ℝ g) 0 s s' = fderiv ℝ (fderiv ℝ ρ) p (s • w) (s' • w)
    := by
    intro s s'
    have := fderiv_fderiv_slice (f := ρ) (a := p) (w := w) (t₀ := 0) hρp s s'
    simpa using this
  -- the slice is negative at small nonzero real parameters
  have hneg' : ∀ x : ℝ, x ≠ 0 → |x| < min δ₁ δ₂ → p + (x : ℂ) • w ∈ U := by
    intro x hx hxδ
    have hxδ₁ : ‖(x : ℂ)‖ < δ₁ := by simpa using hxδ.trans_le (min_le_left _ _)
    have hxδ₂ : (x : ℂ) ∈ ball (0 : ℂ) δ₂ := by
      simpa using hxδ.trans_le (min_le_right _ _)
    have ht := htaylor (x : ℂ) hxδ₁
    have hg0 : g 0 = 0 := by simp [hg, h.eq_zero]
    have hlin : fderiv ℝ g 0 (x : ℂ) = 0 := by
      rw [hD1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, Complex.coe_smul, map_smul, hw,
        smul_zero]
    have hquad : fderiv ℝ (fderiv ℝ g) 0 (x : ℂ) (x : ℂ) = x ^ 2 * A := by
      rw [hD2, Complex.coe_smul, map_smul, map_smul]
      simp only [smul_apply, smul_eq_mul]
      rw [hA]
      ring
    rw [hg0, hlin, hquad, sub_zero, sub_zero, zero_add] at ht
    have hxn : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by simp [sq_abs]
    rw [hxn] at ht
    have hx2 : 0 < x ^ 2 := by positivity
    have : g (x : ℂ) < 0 := by
      have := (abs_le.mp ht).2
      nlinarith
    exact h.mem_of_neg (hV hxδ₂) this
  -- convexity puts `p` into `U`
  set x : ℝ := min δ₁ δ₂ / 2 with hx
  have hx0 : 0 < x := by positivity
  have hxlt : |x| < min δ₁ δ₂ := by
    rw [abs_of_pos hx0, hx]
    linarith [lt_min hδ₁ hδ₂]
  have h1 := hneg' x hx0.ne' hxlt
  have h2 := hneg' (-x) (neg_ne_zero.mpr hx0.ne') (by rwa [abs_neg])
  have hmid : p = (1 / 2 : ℝ) • (p + (x : ℂ) • w) + (1 / 2 : ℝ) • (p + ((-x : ℝ) : ℂ) • w) := by
    simp only [Complex.coe_smul]
    module
  have : p ∈ U := by
    rw [hmid]
    exact hconv h1 h2 (by norm_num) (by norm_num) (by norm_num)
  exact hU.notMem_of_mem_frontier hp this

/-- **Convex open sets are Levi pseudoconvex** ([Range][Range1986], Lemma 2.10). -/
theorem _root_.Convex.isLeviPseudoconvex (hU : IsOpen U) (hconv : Convex ℝ U) :
    IsLeviPseudoconvex U := by
  intro p hp ρ V h w hw
  have h1 := h.fderiv_fderiv_nonneg_of_convex hU hconv hp hw.1
  have h2 := h.fderiv_fderiv_nonneg_of_convex hU hconv hp hw.smul_I.1
  rw [leviForm_eq_fderiv]
  linarith

end Convex

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
