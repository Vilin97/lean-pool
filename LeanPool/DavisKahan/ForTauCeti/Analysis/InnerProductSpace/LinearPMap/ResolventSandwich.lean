/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.QuadraticFormBounds
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The Loewner-order resolvent sandwich

For a self-adjoint `A` bounded below by `β` in the quadratic-form sense and a
real `lam < β`, the resolvent `R = (A - lam)⁻¹` exists and is squeezed between
the two multiples of the identity that the scalar picture predicts:

```text
0 ≤ R ≤ (β - lam)⁻¹ • 1
```

and, conjugating by an arbitrary bounded `B`,

```text
0 ≤ B⋆ R B ≤ (β - lam)⁻¹ • B⋆ B .
```

Both are **order** statements in the Loewner order, not norm statements.  A norm
bound `‖R‖ ≤ (β - lam)⁻¹` is strictly weaker and does not substitute for either:
it says nothing about the sign of `re ⟪R φ, φ⟫`, and it is not what survives
conjugation in the form the Schur-complement arguments of the Davis--Kahan
Section 9 examples consume.

## Main results

Carrier-free, in `TauCeti.ContinuousLinearMap`:

* `le_smul_one_of_upperFormBoundOn_top` — an upper form bound *is* an upper
  Loewner bound, for a symmetric operator.  This is the missing companion of
  `isPositive_of_lowerFormBoundOn_top` in `QuadraticFormBounds.lean`.
* `norm_apply_le_of_coercive`, `lowerFormBoundOn_top_of_coercive`,
  `upperFormBoundOn_top_of_coercive` — a bounded operator satisfying
  `c ‖R φ‖² ≤ re ⟪R φ, φ⟫` is positive and bounded above by `c⁻¹`.

Bounded carrier, in `TauCeti.ContinuousLinearMap`:

* `rightInverse_sandwich_of_lowerFormBoundOn_top` — the sandwich for a bounded
  symmetric `T`, with the inverse of `T - lam` supplied as data.

Unbounded carrier, in `TauCeti.LinearPMap` — this is the deliverable:

* `mem_resolventSet_of_lowerFormBound` — the resolvent exists, so nothing below
  is vacuous.
* `coercive_neg_resolvent_of_lowerFormBound` — the resolvent satisfies the
  coercivity estimate with `c = β - lam`.
* `neg_resolvent_nonneg_of_lowerFormBound` and
  `neg_resolvent_le_smul_one_of_lowerFormBound` — **the sandwich**, in Mathlib's
  Loewner order; `neg_resolvent_sandwich_of_lowerFormBound` packages both.
* `adjoint_conj_neg_resolvent_le_of_lowerFormBound` — the conjugated form
  `B⋆ R B ≤ (β - lam)⁻¹ • B⋆ B`.
* `lowerFormBound_of_spectrum_subset_Ici` — the bridge from the spectral
  hypothesis `spectrum A ⊆ [β, ∞)` to the form hypothesis actually used, so a
  caller may state either.

## Why the form hypothesis and not the spectral one

The theorems below take the **form lower bound** `β ‖x‖² ≤ re ⟪A x, x⟫` on
`dom A` as their hypothesis, and derive it from `spectrum A ⊆ [β, ∞)` in the
last section.  Three reasons, in order of weight.

1. It is what the surrounding API produces: `SpectralFormBounds.lean` ends at
   exactly this statement, and `RealLowerBound.lean` consumes a bound of this
   shape to manufacture the resolvent point.
2. It is strictly the weaker hypothesis, so the theorems are stronger, and it
   survives compression to a subspace — which is how the Davis--Kahan consumer
   meets the operator.
3. It avoids the spectral measure entirely on the main path.  The proof below
   is Cauchy--Schwarz twice; routing it through the diagonal measure and
   `spectralPVM_resolvent_formula` would make a functional-calculus dependency
   out of an estimate that has none.

## The proof, in one paragraph

Write `x = R φ`, so `A x - lam x = φ`.  Then
`re ⟪R φ, φ⟫ = re ⟪x, A x⟫ - lam ‖x‖² = re ⟪A x, x⟫ - lam ‖x‖² ≥ (β - lam) ‖x‖²`,
which is both the positivity and the coercivity estimate.  Cauchy--Schwarz on
the same quantity gives `(β - lam) ‖x‖² ≤ ‖x‖ ‖φ‖`, hence
`‖x‖ ≤ (β - lam)⁻¹ ‖φ‖`, and feeding that back into `re ⟪R φ, φ⟫ ≤ ‖x‖ ‖φ‖`
produces the upper bound.  The constant is sharp: for the scalar operator
`A = β` on `ℂ` the two sides of the upper bound agree.

The same three lines prove the bounded case, which is why the coercivity
estimate rather than the resolvent is what the carrier-free section is about.

## Sources

*Follows nothing in particular.*  The inequality is the operator-order form of
the elementary scalar bound `0 ≤ (t - lam)⁻¹ ≤ (β - lam)⁻¹` on `[β, ∞)`, which
is standard; the route taken here — coercivity of the inverse rather than the
functional calculus of `t ↦ (t - lam)⁻¹` — is chosen because it needs no
spectral theory.

## Provenance

*New.*  Statement and proof are ours.  The consumer that identified this as the
theorem to prove is the Davis--Kahan 1970 Section 9 Schur-complement example,
whose recorded obligation names an "operator-order resolvent sandwich"; the
generic statement is deliberately free of everything beam-specific.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContinuousLinearMap

/-! ### Form bounds and the Loewner order

`QuadraticFormBounds.lean` grounds the *lower* form bound on `⊤` against
Mathlib's `IsPositive`.  The upper bound has the same grounding, and it is the
one this file needs: an upper form bound at constant `c` says exactly that the
operator is below `c • 1`. -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open TauCeti

/-- **An upper form bound is a Loewner upper bound**, in the `IsPositive`
formulation: for symmetric `R` with `re ⟪R φ, φ⟫ ≤ c ‖φ‖²` the difference
`c • 1 - R` is positive. -/
theorem isPositive_smul_one_sub_of_upperFormBoundOn_top {R : E →L[𝕜] E}
    (hsym : R.IsSymmetric) {c : ℝ} (h : R.UpperFormBoundOn ⊤ c) :
    (((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R).IsPositive := by
  have happ : ∀ w : E, (((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R) w
      = ((c : ℝ) : 𝕜) • w - R w := fun _ => rfl
  -- restates symmetry with the bundled application rather than the coerced linear
  -- map, so that the rewrites below match syntactically.
  have hsym' : ∀ w z : E, ⟪R w, z⟫_𝕜 = ⟪w, R z⟫_𝕜 := fun w z => hsym w z
  refine ⟨fun u v => ?_, fun φ => ?_⟩
  · -- restates symmetry with the operator applications unfolded, which is the
    -- shape the inner-product rewrites match against.
    change ⟪(((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R) u, v⟫_𝕜
      = ⟪u, (((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R) v⟫_𝕜
    rw [happ u, happ v, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal, hsym' u v]
  · have hval : (((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R).reApplyInnerSelf φ
        = c * ‖φ‖ ^ 2 - RCLike.re ⟪R φ, φ⟫_𝕜 := by
      -- `reApplyInnerSelf` is the real part of the diagonal form, by definition.
      change RCLike.re ⟪(((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) - R) φ, φ⟫_𝕜
        = c * ‖φ‖ ^ 2 - RCLike.re ⟪R φ, φ⟫_𝕜
      rw [happ φ, inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hval]
    have hb := h φ Submodule.mem_top
    linarith

/-- **An upper form bound is a Loewner upper bound.**  The companion of
`isPositive_of_lowerFormBoundOn_top`, which grounds the lower bound. -/
theorem le_smul_one_of_upperFormBoundOn_top {R : E →L[𝕜] E}
    (hsym : R.IsSymmetric) {c : ℝ} (h : R.UpperFormBoundOn ⊤ c) :
    R ≤ ((c : ℝ) : 𝕜) • (1 : E →L[𝕜] E) :=
  _root_.ContinuousLinearMap.le_def.mpr
    (isPositive_smul_one_sub_of_upperFormBoundOn_top hsym h)

/-! ### The carrier-free core

Nothing in this section knows what a resolvent is.  A bounded operator whose
quadratic form dominates `c ‖R φ‖²` is automatically positive *and* bounded
above by `c⁻¹`, and both halves of the resolvent sandwich are this lemma. -/

/-- **Coercivity bounds the operator norm pointwise.**  If
`c ‖R φ‖² ≤ re ⟪R φ, φ⟫` then `‖R φ‖ ≤ c⁻¹ ‖φ‖`.

This is Cauchy--Schwarz and one division: `c ‖R φ‖² ≤ ‖R φ‖ ‖φ‖`. -/
theorem norm_apply_le_of_coercive {R : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hR : ∀ φ : E, c * ‖R φ‖ ^ 2 ≤ RCLike.re ⟪R φ, φ⟫_𝕜) (φ : E) :
    ‖R φ‖ ≤ c⁻¹ * ‖φ‖ := by
  have hcs : RCLike.re ⟪R φ, φ⟫_𝕜 ≤ ‖R φ‖ * ‖φ‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h := hR φ
  rcases eq_or_lt_of_le (norm_nonneg (R φ)) with h0 | h0
  · rw [← h0]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (norm_nonneg _)
  · rw [inv_mul_eq_div, le_div_iff₀ hc]
    nlinarith

/-- **A coercive operator is positive.**  The lower half of the sandwich, and it
is immediate: the dominating term `c ‖R φ‖²` is already nonnegative. -/
theorem lowerFormBoundOn_top_of_coercive {R : E →L[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hR : ∀ φ : E, c * ‖R φ‖ ^ 2 ≤ RCLike.re ⟪R φ, φ⟫_𝕜) :
    R.LowerFormBoundOn ⊤ 0 := by
  intro φ _
  refine le_trans ?_ (hR φ)
  rw [zero_mul]
  exact mul_nonneg hc (sq_nonneg _)

/-- **A coercive operator is bounded above by `c⁻¹` in the form order.**  The
upper half of the sandwich: Cauchy--Schwarz once more, now fed the norm bound
`norm_apply_le_of_coercive` that coercivity has already produced. -/
theorem upperFormBoundOn_top_of_coercive {R : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hR : ∀ φ : E, c * ‖R φ‖ ^ 2 ≤ RCLike.re ⟪R φ, φ⟫_𝕜) :
    R.UpperFormBoundOn ⊤ c⁻¹ := by
  intro φ _
  have hn := norm_apply_le_of_coercive hc hR φ
  calc RCLike.re ⟪R φ, φ⟫_𝕜 ≤ ‖R φ‖ * ‖φ‖ :=
        (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ c⁻¹ * ‖φ‖ * ‖φ‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = c⁻¹ * ‖φ‖ ^ 2 := by ring

/-! ### The bounded carrier

For a bounded symmetric `T` the sandwich holds verbatim, with the inverse of
`T - lam` supplied as data: only the *right* inverse property is used, and that
is all the estimate needs.  Existence of the inverse under the same hypotheses
is the unbounded theorem specialized —
`TauCeti.LinearPMap.mem_resolventSet_of_lowerFormBound` below. -/

/-- **The shifted quadratic form, computed.**  `re ⟪v, T v - lam v⟫` is
`re ⟪T v, v⟫ - lam ‖v‖²` for real `lam`: the first inner product is the
conjugate of `⟪T v, v⟫` and so has the same real part, and the second is real
because `lam` is. -/
theorem re_inner_self_sub_smul (T : E →L[𝕜] E) (lam : ℝ) (v : E) :
    RCLike.re ⟪v, T v - ((lam : ℝ) : 𝕜) • v⟫_𝕜
      = RCLike.re ⟪T v, v⟫_𝕜 - lam * ‖v‖ ^ 2 := by
  rw [inner_sub_right, map_sub, inner_smul_right, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq, inner_re_symm]

/-- **A right inverse of `T - lam` inherits symmetry from `T`.**

`⟪R u, v⟫ = ⟪R u, (T - lam)(R v)⟫ = ⟪(T - lam)(R u), R v⟫ = ⟪u, R v⟫`, where the
middle step is symmetry of `T` together with `lam` being real. -/
theorem isSymmetric_of_rightInverse_sub_smul {T R : E →L[𝕜] E}
    (hT : T.IsSymmetric) {lam : ℝ}
    (hR : ∀ φ : E, T (R φ) - ((lam : ℝ) : 𝕜) • R φ = φ) : R.IsSymmetric := by
  -- restates symmetry of `T` with the bundled application rather than the coerced
  -- linear map, so that the rewrite below matches syntactically.
  have hT' : ∀ w z : E, ⟪T w, z⟫_𝕜 = ⟪w, T z⟫_𝕜 := fun w z => hT w z
  intro u v
  calc ⟪R u, v⟫_𝕜 = ⟪R u, T (R v) - ((lam : ℝ) : 𝕜) • R v⟫_𝕜 := by rw [hR v]
    _ = ⟪T (R u) - ((lam : ℝ) : 𝕜) • R u, R v⟫_𝕜 := by
        rw [inner_sub_right, inner_sub_left, hT' (R u) (R v), inner_smul_right,
          inner_smul_left, RCLike.conj_ofReal]
    _ = ⟪u, R v⟫_𝕜 := by rw [hR u]

/-- **A right inverse of `T - lam` is coercive**, with constant `β - lam`, when
`T` has form lower bound `β`. -/
theorem coercive_rightInverse_of_lowerFormBoundOn_top {T R : E →L[𝕜] E}
    {β lam : ℝ} (hform : T.LowerFormBoundOn ⊤ β)
    (hR : ∀ φ : E, T (R φ) - ((lam : ℝ) : 𝕜) • R φ = φ) (φ : E) :
    (β - lam) * ‖R φ‖ ^ 2 ≤ RCLike.re ⟪R φ, φ⟫_𝕜 := by
  have key := re_inner_self_sub_smul T lam (R φ)
  rw [hR φ] at key
  have hb := hform (R φ) Submodule.mem_top
  rw [key]
  linarith

/-- **The Loewner-order sandwich, bounded carrier.**

`0 ≤ R ≤ (β - lam)⁻¹ • 1` for any right inverse `R` of `T - lam`, where `T` is
bounded symmetric with form lower bound `β` and `lam < β`. -/
theorem rightInverse_sandwich_of_lowerFormBoundOn_top {T R : E →L[𝕜] E}
    (hT : T.IsSymmetric) {β lam : ℝ} (hlt : lam < β)
    (hform : T.LowerFormBoundOn ⊤ β)
    (hR : ∀ φ : E, T (R φ) - ((lam : ℝ) : 𝕜) • R φ = φ) :
    (0 : E →L[𝕜] E) ≤ R ∧ R ≤ (((β - lam)⁻¹ : ℝ) : 𝕜) • (1 : E →L[𝕜] E) := by
  have hcoer := coercive_rightInverse_of_lowerFormBoundOn_top hform hR
  have hsym := isSymmetric_of_rightInverse_sub_smul hT hR
  refine ⟨(_root_.ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
      (isPositive_of_lowerFormBoundOn_top hsym
        (lowerFormBoundOn_top_of_coercive (by linarith) hcoer)), ?_⟩
  exact le_smul_one_of_upperFormBoundOn_top hsym
    (upperFormBoundOn_top_of_coercive (by linarith) hcoer)

end ContinuousLinearMap

namespace LinearPMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {A : E →ₗ.[ℂ] E}

/-! ### From a form lower bound to a coercive resolvent -/

/-- **The shifted quadratic form of a partially defined operator, computed.**
The unbounded counterpart of `TauCeti.ContinuousLinearMap.re_inner_self_sub_smul`,
carrying the domain membership that lets `A` be applied.

Both the resolvent estimate and the norm lower bound that produces the resolvent
point are this identity plus Cauchy--Schwarz. -/
theorem re_inner_self_sub_smul (lam : ℝ) {v : E} (hv : v ∈ A.domain) :
    (⟪v, A ⟨v, hv⟩ - (lam : ℂ) • v⟫_ℂ).re
      = (⟪A ⟨v, hv⟩, v⟫_ℂ).re - lam * ‖v‖ ^ 2 := by
  have hswap : (⟪v, A ⟨v, hv⟩⟫_ℂ).re = (⟪A ⟨v, hv⟩, v⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  have hself : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [inner_sub_right, Complex.sub_re, inner_smul_right, hswap, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hself]

/-- **The shifted operator is bounded below in norm.**  A form lower bound `β`
gives `(β - lam) ‖x‖ ≤ ‖A x - lam x‖` at every real `lam`.

This is the estimate `RealLowerBound.lean` asks for in exchange for a resolvent
point.  No separation `lam < β` is needed: when `β ≤ lam` the left-hand side is
already nonpositive, and the interesting case is the other one. -/
theorem norm_sub_smul_ge_of_lowerFormBound {β lam : ℝ}
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (x : A.domain) :
    (β - lam) * ‖(x : E)‖ ≤ ‖A x - (lam : ℂ) • (x : E)‖ := by
  have key : (⟪(x : E), A x - (lam : ℂ) • (x : E)⟫_ℂ).re
      = (⟪A x, (x : E)⟫_ℂ).re - lam * ‖(x : E)‖ ^ 2 :=
    re_inner_self_sub_smul lam x.2
  have hcs : (⟪(x : E), A x - (lam : ℂ) • (x : E)⟫_ℂ).re
      ≤ ‖(x : E)‖ * ‖A x - (lam : ℂ) • (x : E)‖ :=
    (RCLike.re_le_norm (K := ℂ) _).trans (norm_inner_le_norm _ _)
  have hb := hform x
  rw [key] at hcs
  rcases eq_or_lt_of_le (norm_nonneg ((x : E))) with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · nlinarith

/-- **A real point below a form lower bound is a resolvent point.**

`mem_resolventSet_and_norm_le_of_lower_bound` does the analytic work; this is
the packaging that lets a caller supply the *form* bound the rest of this file
uses, rather than the norm bound that theorem states. -/
theorem mem_resolventSet_of_lowerFormBound [CompleteSpace E]
    (hA : IsSelfAdjoint A) {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re) :
    (lam : ℂ) ∈ resolventSet A :=
  (mem_resolventSet_and_norm_le_of_lower_bound hA (by simpa using sub_pos.mpr hlt)
    (norm_sub_smul_ge_of_lowerFormBound hform)).1

/-- **The resolvent of a form-semibounded operator is coercive**, with constant
`β - lam`.

Everything else in this section is this estimate plus the carrier-free core.
The proof is `re_inner_self_sub_smul` at the domain point `x = R φ`, where
`A x - lam x = φ` is the defining property of the resolvent. -/
theorem coercive_neg_resolvent_of_lowerFormBound {β lam : ℝ}
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) (φ : E) :
    (β - lam) * ‖(-resolvent A (lam : ℂ)) φ‖ ^ 2
      ≤ (⟪(-resolvent A (lam : ℂ)) φ, φ⟫_ℂ).re := by
  simp only [_root_.neg_apply]
  have hmem : -(resolvent A (lam : ℂ) φ) ∈ A.domain :=
    neg_mem (resolvent_mem_domain hlam φ)
  have key := re_inner_self_sub_smul (A := A) lam hmem
  -- `A v - lam v = φ` at `v = -R φ`, because `lam • R φ - A (R φ) = φ`
  have hAv : A (⟨-(resolvent A (lam : ℂ) φ), hmem⟩ : A.domain)
      - (lam : ℂ) • (-(resolvent A (lam : ℂ) φ)) = φ := by
    have h := smul_sub_apply_resolvent hlam φ
    have hneg : A (⟨-(resolvent A (lam : ℂ) φ), hmem⟩ : A.domain)
        = -(A ⟨resolvent A (lam : ℂ) φ, resolvent_mem_domain hlam φ⟩) :=
      _root_.LinearPMap.map_neg A ⟨resolvent A (lam : ℂ) φ, resolvent_mem_domain hlam φ⟩
    rw [hneg]
    linear_combination (norm := module) h
  rw [hAv] at key
  have hb : β * ‖-(resolvent A (lam : ℂ) φ)‖ ^ 2
      ≤ (⟪A ⟨-(resolvent A (lam : ℂ) φ), hmem⟩,
          -(resolvent A (lam : ℂ) φ)⟫_ℂ).re :=
    hform ⟨-(resolvent A (lam : ℂ) φ), hmem⟩
  rw [key]
  linarith

/-! ### The sandwich

The two halves, first as this repository's form bounds and then in Mathlib's
Loewner order.  The form-bound versions carry no completeness hypothesis; the
order versions do, because self-adjointness of the resolvent does. -/

/-- **Positivity of the resolvent, as a form bound.** -/
theorem lowerFormBoundOn_neg_resolvent_of_lowerFormBound {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    (-resolvent A (lam : ℂ)).LowerFormBoundOn ⊤ 0 :=
  ContinuousLinearMap.lowerFormBoundOn_top_of_coercive (by linarith)
    (coercive_neg_resolvent_of_lowerFormBound hform hlam)

/-- **The upper bound on the resolvent, as a form bound.**  The constant is
sharp: for the scalar operator `A = β` on `ℂ` the two sides agree. -/
theorem upperFormBoundOn_neg_resolvent_of_lowerFormBound {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    (-resolvent A (lam : ℂ)).UpperFormBoundOn ⊤ (β - lam)⁻¹ :=
  ContinuousLinearMap.upperFormBoundOn_top_of_coercive (by linarith)
    (coercive_neg_resolvent_of_lowerFormBound hform hlam)

section Order

variable [CompleteSpace E]

/-- **The resolvent is a positive operator.** -/
theorem isPositive_neg_resolvent_of_lowerFormBound (hA : IsSelfAdjoint A) {β lam : ℝ}
    (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    (-resolvent A (lam : ℂ)).IsPositive :=
  TauCeti.ContinuousLinearMap.isPositive_of_lowerFormBoundOn_top
    ((isSelfAdjoint_resolvent_ofReal hA hlam).neg.isSymmetric)
    (lowerFormBoundOn_neg_resolvent_of_lowerFormBound hlt hform hlam)

/-- **The lower half of the sandwich, in the Loewner order**: `0 ≤ -R(lam)`, i.e.
`0 ≤ (A - lam)⁻¹`. -/
theorem neg_resolvent_nonneg_of_lowerFormBound (hA : IsSelfAdjoint A) {β lam : ℝ}
    (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    (0 : E →L[ℂ] E) ≤ -resolvent A (lam : ℂ) :=
  (_root_.ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
    (isPositive_neg_resolvent_of_lowerFormBound hA hlt hform hlam)

/-- The difference `(β - lam)⁻¹ • 1 - (-R(lam))` is a positive operator.  This
is the content of the upper bound; `neg_resolvent_le_smul_one_of_lowerFormBound`
reads it as an order relation, and the conjugated corollary consumes it in this
form. -/
theorem isPositive_smul_one_sub_neg_resolvent_of_lowerFormBound (hA : IsSelfAdjoint A)
    {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    ((((β - lam)⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E) - -resolvent A (lam : ℂ)).IsPositive :=
  TauCeti.ContinuousLinearMap.isPositive_smul_one_sub_of_upperFormBoundOn_top
    ((isSelfAdjoint_resolvent_ofReal hA hlam).neg.isSymmetric)
    (upperFormBoundOn_neg_resolvent_of_lowerFormBound hlt hform hlam)

/-- **The Loewner-order resolvent sandwich, upper half.**

`-R(lam) = (A - lam)⁻¹ ≤ (β - lam)⁻¹ • 1` whenever `A` is self-adjoint with form lower
bound `β` and `lam < β` is a resolvent point.  Together with
`neg_resolvent_nonneg_of_lowerFormBound` this is the statement

```text
0 ≤ -R(lam) = (A - lam)⁻¹ ≤ (β - lam)⁻¹ • 1 .
```

An operator-norm estimate does not substitute for this: the consumer needs the
order relation, which is what survives conjugation. -/
theorem neg_resolvent_le_smul_one_of_lowerFormBound (hA : IsSelfAdjoint A) {β lam : ℝ}
    (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) :
    -resolvent A (lam : ℂ) ≤ (((β - lam)⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E) :=
  TauCeti.ContinuousLinearMap.le_smul_one_of_upperFormBoundOn_top
    ((isSelfAdjoint_resolvent_ofReal hA hlam).neg.isSymmetric)
    (upperFormBoundOn_neg_resolvent_of_lowerFormBound hlt hform hlam)

/-- **The sandwich, both halves at once.**  Stated so a consumer can name one
theorem, and with the resolvent point obtained from the hypotheses rather than
assumed, so the statement cannot be vacuous. -/
theorem neg_resolvent_sandwich_of_lowerFormBound (hA : IsSelfAdjoint A) {β lam : ℝ}
    (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re) :
    (0 : E →L[ℂ] E)
        ≤ -resolvent A (lam : ℂ) ∧
      -resolvent A (lam : ℂ)
        ≤ (((β - lam)⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E) :=
  ⟨neg_resolvent_nonneg_of_lowerFormBound hA hlt hform
      (mem_resolventSet_of_lowerFormBound hA hlt hform),
    neg_resolvent_le_smul_one_of_lowerFormBound hA hlt hform
      (mem_resolventSet_of_lowerFormBound hA hlt hform)⟩

end Order

/-! ### Conjugation

Conjugating a Loewner inequality by a bounded map preserves it.  This is the
form the Schur-complement arguments consume: they never see `(A - lam)⁻¹` on the
whole space, only its compression `B⋆ (A - lam)⁻¹ B` to a trial subspace. -/

section Conjugate

variable [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The conjugated sandwich, lower half**: `0 ≤ -B⋆ R(lam) B`. -/
theorem adjoint_conj_neg_resolvent_nonneg_of_lowerFormBound (hA : IsSelfAdjoint A)
    {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) (B : F →L[ℂ] E) :
    (0 : F →L[ℂ] F)
      ≤ ContinuousLinearMap.adjoint B ∘L (-resolvent A (lam : ℂ)) ∘L B :=
  (_root_.ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
    ((isPositive_neg_resolvent_of_lowerFormBound hA hlt hform hlam).adjoint_conj B)

/-- **The conjugated sandwich, upper half**:
`-B⋆ R(lam) B ≤ (β - lam)⁻¹ • B⋆ B`.

This is one application of `ContinuousLinearMap.IsPositive.adjoint_conj` to the
difference `(β - lam)⁻¹ • 1 - (A - lam)⁻¹`, after identifying
`B⋆ ((β - lam)⁻¹ • 1) B` with `(β - lam)⁻¹ • (B⋆ B)`. -/
theorem adjoint_conj_neg_resolvent_le_of_lowerFormBound (hA : IsSelfAdjoint A)
    {β lam : ℝ} (hlt : lam < β)
    (hform : ∀ x : A.domain, β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re)
    (hlam : (lam : ℂ) ∈ resolventSet A) (B : F →L[ℂ] E) :
    ContinuousLinearMap.adjoint B ∘L (-resolvent A (lam : ℂ)) ∘L B
      ≤ (((β - lam)⁻¹ : ℝ) : ℂ) • (ContinuousLinearMap.adjoint B ∘L B) := by
  have hpos :=
    (isPositive_smul_one_sub_neg_resolvent_of_lowerFormBound hA hlt hform hlam).adjoint_conj B
  have hexp : ContinuousLinearMap.adjoint B
        ∘L ((((β - lam)⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E) - (-resolvent A (lam : ℂ))) ∘L B
      = (((β - lam)⁻¹ : ℝ) : ℂ) • (ContinuousLinearMap.adjoint B ∘L B)
        - ContinuousLinearMap.adjoint B ∘L (-resolvent A (lam : ℂ)) ∘L B := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, _root_.smul_apply,
      _root_.one_apply_eq_self, map_sub, map_smul]
  rw [hexp] at hpos
  exact _root_.ContinuousLinearMap.le_def.mpr hpos

end Conjugate

/-! ### The spectral hypothesis

`spectrum A ⊆ [β, ∞)` is the hypothesis a reader expects; it implies the form
bound the theorems above take, through the support statement for the spectral
measure.  Stating both, with this bridge between them, lets a caller supply
whichever one is at hand. -/

section Spectral

variable [CompleteSpace E]

/-- **From a half-line spectrum to the form lower bound.**

`spectrum A ⊆ [β, ∞)`, read through `mem_of_subset_ofReal_image`, puts every
real `l < β` in the resolvent set; the spectral measure therefore gives no mass
to `(-∞, β)`, and `le_re_inner_of_specProjection_Iio_eq_zero` converts that into
the form bound. -/
theorem lowerFormBound_of_spectrum_subset_Ici (hA : IsSelfAdjoint A) {β : ℝ}
    (hσ : spectrum A ⊆ (RCLike.ofReal (K := ℂ) '' Set.Ici β)) (x : A.domain) :
    β * ‖(x : E)‖ ^ 2 ≤ (⟪A x, (x : E)⟫_ℂ).re := by
  refine le_re_inner_of_specProjection_Iio_eq_zero hA ?_ x
  refine specProjection_eq_zero_of_subset_resolventSet hA _ measurableSet_Iio
    fun l hl => ?_
  rw [← notMem_spectrum_iff]
  intro hmem
  have hl' : l ∈ Set.Ici β := mem_of_subset_ofReal_image hσ hmem
  exact absurd (Set.mem_Ici.mp hl') (not_le.mpr (Set.mem_Iio.mp hl))

/-- **The sandwich under the spectral hypothesis.**  The same statement as
`neg_resolvent_sandwich_of_lowerFormBound`, with `spectrum A ⊆ [β, ∞)` in place of
the form bound. -/
theorem neg_resolvent_sandwich_of_spectrum_subset_Ici (hA : IsSelfAdjoint A)
    {β lam : ℝ} (hlt : lam < β)
    (hσ : spectrum A ⊆ (RCLike.ofReal (K := ℂ) '' Set.Ici β)) :
    (0 : E →L[ℂ] E)
        ≤ -resolvent A (lam : ℂ) ∧
      -resolvent A (lam : ℂ)
        ≤ (((β - lam)⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E) :=
  neg_resolvent_sandwich_of_lowerFormBound hA hlt
    (lowerFormBound_of_spectrum_subset_Ici hA hσ)

end Spectral

end LinearPMap

end TauCeti
