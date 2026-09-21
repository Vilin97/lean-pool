/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.RadonNikodymL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Multiplication operators form a `⋆`-algebra

`TauCeti.mulLp` sends a bounded measurable symbol to a bounded operator on `L²`.  This file
records that the assignment is a `⋆`-algebra homomorphism: it takes the constant `1` to the
identity, sums to sums, scalar multiples to scalar multiples, products to *compositions*, and
complex conjugation to the *adjoint*.  Every operator so produced is normal.

## Why the statements look the way they do

`mulLp` carries its measurability and boundedness hypotheses as explicit arguments, so a naive
statement like `mulLp ρ (g₁ * g₂) = mulLp ρ g₁ ∘L mulLp ρ g₂` would force the caller to produce
the exact proof terms the left-hand side expects.  Each law is therefore stated for an
*arbitrary* symbol `h` together with an almost-everywhere identification of `h` with the
combination in question.  At the call sites -- building a `⋆`-algebra homomorphism out of
`C(s, ℂ)` -- the symbols are already-composed functions, so the a.e. hypothesis is discharged by
`Filter.Eventually.of_forall` and nothing has to be matched syntactically.

The bound `C` is *not* a source of friction: `LinearMap.mkContinuous` uses it only inside a
continuity proof, and `Measurable` is a `Prop`, so two invocations of `mulLp` differing only in
their hypotheses are definitionally equal.  It is only the symbol that matters, and only up to
`ρ`-a.e. equality (`mulLp_congr_ae`).

## Main results

* `TauCeti.mulLp_eq_one`: a symbol that is a.e. `1` gives the identity operator.
* `TauCeti.mulLp_eq_add`, `TauCeti.mulLp_eq_smul`: additivity and homogeneity in the symbol.
* `TauCeti.mulLp_eq_comp`: **multiplying symbols composes operators.**
* `TauCeti.adjoint_mulLp`, `TauCeti.star_mulLp`: **conjugating the symbol takes the adjoint.**
* `TauCeti.isStarNormal_mulLp`: **every multiplication operator is normal.**
* `TauCeti.norm_mulLp_le`: the operator norm is at most any uniform bound on the symbol.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ComplexConjugate InnerProductSpace

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

section Algebra

variable (ρ : Measure α)

/-- **A symbol that is almost everywhere `1` gives the identity operator.** -/
theorem mulLp_eq_one {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (heq : ∀ᵐ x ∂ρ, h x = 1) : mulLp ρ hh hhC = 1 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, heq] with x h1 h2
  rw [h1, h2, one_mul]
  rfl

/-- **A symbol that is almost everywhere `0` gives the zero operator.** -/
theorem mulLp_eq_zero {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (heq : ∀ᵐ x ∂ρ, h x = 0) : mulLp ρ hh hhC = 0 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, heq,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := ρ)] with x h1 h2 h3
  rw [h1, h2, zero_mul, zero_apply, h3, Pi.zero_apply]

/-- **Additivity in the symbol.** -/
theorem mulLp_eq_add {g₁ g₂ h : α → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hh : Measurable h) {C₁ C₂ C : ℝ} (hg₁C : ∀ x, ‖g₁ x‖ ≤ C₁) (hg₂C : ∀ x, ‖g₂ x‖ ≤ C₂)
    (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = g₁ x + g₂ x) :
    mulLp ρ hh hhC = mulLp ρ hg₁ hg₁C + mulLp ρ hg₂ hg₂C := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, coeFn_mulLp ρ hg₁ hg₁C F, coeFn_mulLp ρ hg₂ hg₂C F,
    Lp.coeFn_add (mulLp ρ hg₁ hg₁C F) (mulLp ρ hg₂ hg₂C F), heq] with x h1 h2 h3 h4 h5
  rw [h1, h5, add_apply, h4, Pi.add_apply, h2, h3, add_mul]

/-- **Homogeneity in the symbol.** -/
theorem mulLp_eq_smul {g h : α → ℂ} (hg : Measurable g) (hh : Measurable h) {Cg C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hhC : ∀ x, ‖h x‖ ≤ C) (c : ℂ)
    (heq : ∀ᵐ x ∂ρ, h x = c * g x) : mulLp ρ hh hhC = c • mulLp ρ hg hgC := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, coeFn_mulLp ρ hg hgC F,
    Lp.coeFn_smul c (mulLp ρ hg hgC F), heq] with x h1 h2 h3 h4
  rw [h1, h4, smul_apply, h3, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]

/-- **A constant symbol gives the corresponding scalar.**

This is the `commutes'` obligation of a `ℂ`-algebra homomorphism, in the form the construction
of `mulLpStarHom` needs it. -/
theorem mulLp_eq_algebraMap {h : α → ℂ} (hh : Measurable h) {C : ℝ} (hhC : ∀ x, ‖h x‖ ≤ C)
    (c : ℂ) (heq : ∀ᵐ x ∂ρ, h x = c) :
    mulLp ρ hh hhC = algebraMap ℂ (Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) c := by
  have hone : ∀ _ : α, ‖(1 : ℂ)‖ ≤ (1 : ℝ) := fun _ => le_of_eq norm_one
  have hsmul : mulLp ρ hh hhC = c • mulLp ρ (measurable_const (a := (1 : ℂ))) hone :=
    mulLp_eq_smul ρ measurable_const hh hone hhC c (by filter_upwards [heq] with x hx; simp [hx])
  rw [hsmul, mulLp_eq_one ρ measurable_const hone (Filter.Eventually.of_forall fun _ => rfl),
    Algebra.algebraMap_eq_smul_one]

/-- **Multiplying symbols composes operators.**

Both orders give the same operator, `ℂ` being commutative; the statement is fixed to
`g₁ ∘L g₂` and the caller chooses. -/
theorem mulLp_eq_comp {g₁ g₂ h : α → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hh : Measurable h) {C₁ C₂ C : ℝ} (hg₁C : ∀ x, ‖g₁ x‖ ≤ C₁) (hg₂C : ∀ x, ‖g₂ x‖ ≤ C₂)
    (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = g₁ x * g₂ x) :
    mulLp ρ hh hhC = (mulLp ρ hg₁ hg₁C).comp (mulLp ρ hg₂ hg₂C) := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, coeFn_mulLp ρ hg₂ hg₂C F,
    coeFn_mulLp ρ hg₁ hg₁C (mulLp ρ hg₂ hg₂C F), heq] with x h1 h2 h3 h4
  rw [h1, h4, ContinuousLinearMap.comp_apply, h3, h2, mul_assoc]

/-- **The operator norm is bounded by any uniform bound on the symbol.**

Stated with `|C|`, for the same reason as `eLpNorm_two_mul_le`: a hypothesis `∀ x, ‖g x‖ ≤ C`
does not force `0 ≤ C` when the space is empty. -/
theorem norm_mulLp_le {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    ‖mulLp ρ hg hgC‖ ≤ |C| :=
  ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg C) fun F => by
    rw [mulLp_apply]; exact norm_toLp_mul_le ρ hg hgC F

end Algebra

section Adjoint

variable (ρ : Measure α)

/-- **Conjugating the symbol takes the adjoint.**

The `L²` inner product is an integral of pointwise inner products, and on `ℂ` the pointwise
inner product is `⟪z, w⟫ = conj z * w`; the identity is then the pointwise associativity
`conj (conj (g x) * F x) * G x = conj (F x) * (g x * G x)`. -/
theorem adjoint_mulLp {g h : α → ℂ} (hg : Measurable g) (hh : Measurable h) {Cg C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = conj (g x)) :
    ContinuousLinearMap.adjoint (mulLp ρ hg hgC) = mulLp ρ hh hhC := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun F G => ?_).symm
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulLp ρ hh hhC F, coeFn_mulLp ρ hg hgC G, heq] with x h1 h2 h3
  rw [h1, h2, h3, RCLike.inner_apply, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

/-- **Multiplication is `star`-equivariant, with the symbol conjugated.**

The operator-level statement is `star_mulLp` below; this is the *vector*-level one, and it is
the form the real multiplicity model needs: taking `h = g` almost everywhere real, it says
multiplication by a real symbol maps `star`-fixed classes to `star`-fixed classes, whereas a
symbol with a nonvanishing imaginary part moves them off. -/
theorem star_mulLp_apply {g h : α → ℂ} (hg : Measurable g) (hh : Measurable h) {Cg C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = conj (g x))
    (F : Lp ℂ 2 ρ) :
    star (mulLp ρ hg hgC F) = mulLp ρ hh hhC (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (mulLp ρ hg hgC F), coeFn_mulLp ρ hg hgC F,
    coeFn_mulLp ρ hh hhC (star F), Lp.coeFn_star F, heq] with x h1 h2 h3 h4 h5
  calc ((star (mulLp ρ hg hgC F) : Lp ℂ 2 ρ) : α → ℂ) x
      = star (g x * (F : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = conj (g x) * conj ((F : α → ℂ) x) := by rw [RCLike.star_def, map_mul]
    _ = h x * ((star F : Lp ℂ 2 ρ) : α → ℂ) x := by
        rw [h5, h4, Pi.star_apply, RCLike.star_def]
    _ = ((mulLp ρ hh hhC (star F) : Lp ℂ 2 ρ) : α → ℂ) x := h3.symm

/-- The adjoint statement in `⋆`-ring form, which is what a `StarAlgHom` obligation asks for. -/
theorem star_mulLp {g h : α → ℂ} (hg : Measurable g) (hh : Measurable h) {Cg C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hhC : ∀ x, ‖h x‖ ≤ C) (heq : ∀ᵐ x ∂ρ, h x = conj (g x)) :
    star (mulLp ρ hg hgC) = mulLp ρ hh hhC := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact adjoint_mulLp ρ hg hh hgC hhC heq

/-- **Every multiplication operator is normal.**

Both `star a * a` and `a * star a` are multiplication by `conj g * g`, `ℂ` being commutative.
This is what makes the continuous functional calculus available for the model operators of
spectral multiplicity theory. -/
theorem isStarNormal_mulLp {g : α → ℂ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    IsStarNormal (mulLp ρ hg hgC) := by
  have hcg : Measurable fun x => conj (g x) := Complex.continuous_conj.measurable.comp hg
  have hcgC : ∀ x, ‖conj (g x)‖ ≤ C := fun x => by
    rw [RCLike.norm_conj]; exact hgC x
  have hstar : star (mulLp ρ hg hgC) = mulLp ρ hcg hcgC :=
    star_mulLp ρ hg hcg hgC hcgC (Filter.Eventually.of_forall fun _ => rfl)
  have hprod : Measurable fun x => conj (g x) * g x := hcg.mul hg
  have hprodC : ∀ x, ‖conj (g x) * g x‖ ≤ C * C := fun x => by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hgC x) (hgC x) (norm_nonneg _) ((norm_nonneg _).trans (hgC x))
  refine ⟨?_⟩
  rw [hstar]
  have h₁ : mulLp ρ hprod hprodC = (mulLp ρ hcg hcgC).comp (mulLp ρ hg hgC) :=
    mulLp_eq_comp ρ hcg hg hprod hcgC hgC hprodC (Filter.Eventually.of_forall fun _ => rfl)
  have h₂ : mulLp ρ hprod hprodC = (mulLp ρ hg hgC).comp (mulLp ρ hcg hcgC) :=
    mulLp_eq_comp ρ hg hcg hprod hgC hcgC hprodC
      (Filter.Eventually.of_forall fun x => mul_comm (conj (g x)) (g x))
  exact (h₁.symm.trans h₂)

end Adjoint

end TauCeti
