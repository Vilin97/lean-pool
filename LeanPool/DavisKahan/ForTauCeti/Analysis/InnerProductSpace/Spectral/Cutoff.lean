/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Spectral cutoffs of a positive operator

For a positive operator `A : E →L[ℂ] E` and a level `s : ℝ` the **spectral cutoff** is the
positive part of `A - s`, and the **spectral cocutoff** is the positive part of `s - A`,
both formed with the continuous functional calculus:

```
A.spectralCutoff s = (A - s)₊,   A.spectralCocutoff s = (s - A)₊.
```

Their point is that the closed subspace `ker (A.spectralCutoff s)` splits `E` exactly the
way the spectral projection of `A` for `[0, s]` would, *without* needing a projection-valued
measure:

* on `ker (A.spectralCutoff s)`, `A` is bounded above by `s`;
* on its orthogonal complement, `A` is bounded below by `s`.

That is all the spectral theorem is used for in the min--max theorem for approximation
numbers, so with these two lemmas that theorem needs no measure theory — see
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`.

## The two inequalities

Both come from a pointwise inequality of real functions fed to `cfc_nonneg`, so neither
needs `A` to be compact, `E` to be separable, or any spectral decomposition to exist.

For the upper bound, `t * t - s ^ 2 ≤ (t + s) * max (t - s) 0` holds for every `t ≥ 0` —
with equality when `t ≥ s` and with a negative left side otherwise.  Reading it through the
functional calculus gives `A * A ≤ s ^ 2 + (A + s) * (A - s)₊`, and the second summand
annihilates the kernel of the cutoff, leaving `‖A y‖ ^ 2 ≤ s ^ 2 * ‖y‖ ^ 2` there.

For the lower bound, `(s - t) ≤ max (s - t) 0` gives `s - A ≤ (s - A)₊`.  The cocutoff
kills the orthogonal complement of the kernel — its range lies in the kernel, because
`max (t - s) 0 * max (s - t) 0 = 0` identically, and it is self-adjoint, so it preserves the
complement as well — leaving `s * ‖y‖ ^ 2 ≤ re ⟪A y, y⟫`, and Cauchy--Schwarz finishes.

## The smooth cutoff, and why there are two of them

`TauCeti.tailCutoff u` is a *continuous* profile — `1 - u² / max x u²` — vanishing below `u²`
and tending to `1` above it, and `norm_comp_cfc_one_sub_tailCutoff_le` and
`mul_norm_cfc_tailCutoff_le_norm_apply` are the same pair of inequalities for it, stated for
the Gram operator `S⋆S` of an operator between two spaces rather than for a positive operator
on one.

**A kernel cutoff and a multiplier cutoff are not interchangeable, and the difference is what
the real min--max theorem turns on.**  `ker (A.spectralCutoff s)` is a subspace; the
orthogonal projection onto it need not be a continuous function of `A`.  A multiplier
`cfc f A` is one by construction, so it commutes with everything `A` commutes with — in
particular with a conjugation, which is exactly what lets the cutoff *descend from a
complexification to a real operator*.  That is why
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxReal.lean` cannot reuse the
kernel pair and needs this one.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.  The smooth
  cutoff section arrived later, from
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxReal.lean`, where it had been
  written `private` against one Hilbert space; it is stated here for any.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.  `vendor/Spectra` proves the corresponding facts through its
  projection-valued-measure and Borel functional calculus layer; the point of this module is
  that the continuous functional calculus already in Mathlib suffices.
-/

public section

namespace TauCeti

/-! ## The smooth cutoff profile

`spectralCutoff` below cuts by a *kernel*; this section builds the ingredients for cutting by
a *continuous multiplier* instead.  The two do the same job and are not interchangeable: a
multiplier that is a continuous function of the operator commutes with everything the
operator does, and in particular survives a conjugation, which a kernel projection need
not. -/

/-- A continuous cutoff which vanishes at energies at most `u²`, tends to one
at high energy, and gives a tail operator bounded by `u`.

Named `tailCutoff` rather than `spectralCutoff` because
`ContinuousLinearMap.spectralCutoff` in this same module is a different object — the
positive part of `A - s`, an *operator*, where this is the scalar profile a smooth
multiplier is built from. -/
noncomputable def tailCutoff (u x : ℝ) : ℝ :=
  1 - u ^ 2 / max x (u ^ 2)

/-- The profile is continuous, which is the whole reason for choosing it: only a continuous
function of an operator is available to the continuous functional calculus.  The denominator
`max x (u ^ 2)` never vanishes for `0 < u`, which is what makes the quotient continuous
everywhere rather than only away from `0`. -/
theorem continuous_tailCutoff (u : ℝ) (hu : 0 < u) :
    Continuous (tailCutoff u) := by
  have hden : ∀ x : ℝ, max x (u ^ 2) ≠ 0 := by
    intro x hx
    have hle : u ^ 2 ≤ max x (u ^ 2) := le_max_right _ _
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    rw [hx] at hle
    linarith
  exact continuous_const.sub
    (continuous_const.div (continuous_id.max continuous_const) hden)

/-- Below the threshold the profile is identically zero, so the multiplier annihilates the
low end of the spectrum exactly rather than merely damping it. -/
theorem tailCutoff_eq_zero_of_le
    {u x : ℝ} (hu : 0 < u) (hx : x ≤ u ^ 2) :
    tailCutoff u x = 0 := by
  rw [tailCutoff, max_eq_right hx]
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  rw [div_self hu2, sub_self]

/-- **The bound the cutoff was designed for.**  The complementary profile `1 - tailCutoff u`
is supported below `u ^ 2` and decays like `u ^ 2 / x` above it, so `x` times its square never
exceeds `u ^ 2`.  Fed to the functional calculus this says the low-energy piece of an operator
has norm at most `u`. -/
theorem tailCutoff_tail_bound
    {u x : ℝ} (hu : 0 < u) (_hx0 : 0 ≤ x) :
    x * (1 - tailCutoff u x) ^ 2 ≤ u ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [tailCutoff_eq_zero_of_le hu hx]
    simpa using hx
  · have hux : u ^ 2 < x := lt_of_not_ge hx
    have hxpos : 0 < x := (sq_pos_of_pos hu).trans hux
    rw [tailCutoff, max_eq_left hux.le]
    have hid : 1 - (1 - u ^ 2 / x) = u ^ 2 / x := by ring
    rw [hid]
    have hmul : u ^ 4 ≤ u ^ 2 * x := by
      nlinarith [sq_nonneg (u ^ 2)]
    calc
      x * (u ^ 2 / x) ^ 2 = u ^ 4 / x := by
        field_simp [hxpos.ne']
      _ ≤ u ^ 2 := (div_le_iff₀ hxpos).2 hmul

/-- On the support of the profile the argument is at least `u ^ 2`, so multiplying by the
square of the profile only increases what `u ^ 2` would give.  This is the bound behind the
lower modulus on the high end of the spectrum. -/
theorem tailCutoff_lower_bound
    {u x : ℝ} (hu : 0 < u) :
    u ^ 2 * (tailCutoff u x) ^ 2 ≤
      x * (tailCutoff u x) ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [tailCutoff_eq_zero_of_le hu hx]
    simp
  · exact mul_le_mul_of_nonneg_right (le_of_not_ge hx)
      (sq_nonneg (tailCutoff u x))

end TauCeti

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The positive part `(A - s)₊` of `A - s`, formed with the continuous functional
calculus. -/
noncomputable def spectralCutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (t - s) 0) A

/-- The positive part `(s - A)₊` of `s - A`, formed with the continuous functional
calculus. -/
noncomputable def spectralCocutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (s - t) 0) A

/-- The operator identity behind the upper bound: `s ^ 2 + (A + s) (A - s)₊ - A ^ 2` is the
functional calculus of a single real function. -/
theorem cutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * A.spectralCutoff s - A * A
      = cfc (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0 - t * t) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  simp only [spectralCutoff,
    cfc_sub (a := A) (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0) (fun t : ℝ => t * t),
    cfc_add (a := A) (fun _ : ℝ => s ^ 2) (fun t : ℝ => (t + s) * max (t - s) 0),
    cfc_mul (fun t : ℝ => t + s) (fun t : ℝ => max (t - s) 0) A,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A,
    cfc_add (a := A) (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_const (s ^ 2) A, cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The operator identity behind the lower bound. -/
theorem cocutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    A.spectralCocutoff s - ((s : ℝ) • (1 : E →L[ℂ] E) - A)
      = cfc (fun t : ℝ => max (s - t) 0 - (s - t)) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectralCocutoff,
    cfc_sub (a := A) (fun t : ℝ => max (s - t) 0) (fun t : ℝ => s - t),
    cfc_sub (a := A) (fun _ : ℝ => s) (fun t : ℝ => t),
    cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The cutoff and the cocutoff annihilate each other: the real functions defining them have
disjoint supports. -/
theorem spectralCutoff_mul_spectralCocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    A.spectralCutoff s * A.spectralCocutoff s = 0 := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectralCutoff, spectralCocutoff,
    ← cfc_mul (fun t : ℝ => max (t - s) 0) (fun t : ℝ => max (s - t) 0) A]
  have hzero : (fun t : ℝ => max (t - s) 0 * max (s - t) 0) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_right (a := s - t) (by linarith)]; ring
  rw [hzero, cfc_const_zero]

/-- The complementary spectral cut-off is self-adjoint, hence an orthogonal projection. -/
theorem isSelfAdjoint_spectralCocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    IsSelfAdjoint (A.spectralCocutoff s) := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  exact cfc_predicate _ A

/-- The range of the cocutoff lies in the kernel of the cutoff. -/
@[simp]
theorem spectralCutoff_spectralCocutoff_apply (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) (x : E) :
    A.spectralCutoff s (A.spectralCocutoff s x) = 0 := by
  have h := congrArg (fun B : E →L[ℂ] E => B x) (spectralCutoff_mul_spectralCocutoff A hA s)
  simpa [mul_apply_eq_comp] using h

section Auxiliary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem re_inner_mul_self {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (y : H) :
    RCLike.re ⟪(A * A) y, y⟫_ℂ = ‖A y‖ ^ 2 := by
  have hadj : A.adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa.star_eq
  have hstep : ⟪(A * A) y, y⟫_ℂ = ⟪A y, A y⟫_ℂ := by
    rw [mul_apply_eq_comp, ← hadj, ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [hstep, inner_self_eq_norm_sq_to_K]
  norm_cast

omit [CompleteSpace H] in
private theorem nonneg_re_inner {B : H →L[ℂ] H} (hB : 0 ≤ B) (y : H) :
    0 ≤ RCLike.re ⟪B y, y⟫_ℂ :=
  ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).2 y

omit [CompleteSpace H] in
private theorem re_inner_real_smul_self (c : ℝ) (y : H) :
    RCLike.re ⟪c • y, y⟫_ℂ = c * ‖y‖ ^ 2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c y, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

end Auxiliary

/-- **`A` is bounded above by `s` on the kernel of its `s`-cutoff.** -/
theorem norm_apply_le_of_spectralCutoff_apply_eq_zero {A : E →L[ℂ] E} (hA : 0 ≤ A) {s : ℝ}
    (hs : 0 ≤ s) {y : E} (hy : A.spectralCutoff s y = 0) : ‖A y‖ ≤ s * ‖y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hpt : ∀ t ∈ spectrum ℝ A, 0 ≤ s ^ 2 + (t + s) * max (t - s) 0 - t * t := by
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hA ht
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith
  have hnn : (0 : E →L[ℂ] E) ≤
      (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * A.spectralCutoff s - A * A := by
    rw [cutoff_split A hA s]
    exact cfc_nonneg hpt
  have hform := nonneg_re_inner hnn y
  have happ : ((A + (s : ℝ) • 1) * A.spectralCutoff s) y = 0 := by
    rw [mul_apply_eq_comp]
    simp [hy]
  simp only [sub_apply, add_apply, happ, add_zero, smul_apply, one_apply_eq_self,
    inner_sub_left, map_sub, re_inner_mul_self hsa y,
    re_inner_real_smul_self (s ^ 2) y] at hform
  have hsq : ‖A y‖ ^ 2 ≤ (s * ‖y‖) ^ 2 := by nlinarith
  have h1 : (0 : ℝ) ≤ ‖A y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ s * ‖y‖ := mul_nonneg hs (norm_nonneg _)
  nlinarith

/-- **`A` is bounded below by `s` on the orthogonal complement of the kernel of its
`s`-cutoff.** -/
theorem le_norm_apply_of_mem_orthogonal_ker_spectralCutoff {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {s : ℝ} {y : E} (hy : y ∈ (LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E))ᗮ) :
    s * ‖y‖ ≤ ‖A y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hco : IsSelfAdjoint (A.spectralCocutoff s) := isSelfAdjoint_spectralCocutoff A hA s
  have hcoadj : (A.spectralCocutoff s).adjoint = A.spectralCocutoff s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hco.star_eq
  have hrange : ∀ x : E,
      A.spectralCocutoff s x ∈ LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E) :=
    fun x => spectralCutoff_spectralCocutoff_apply A hA s x
  have hzero : A.spectralCocutoff s y = 0 := by
    have hperp : ∀ u ∈ LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E), ⟪u, y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ y).mp hy
    have hself : ⟪A.spectralCocutoff s y, A.spectralCocutoff s y⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcoadj]
      exact hperp _ (hrange (A.spectralCocutoff s y))
    exact inner_self_eq_zero.mp hself
  have hnn : (0 : E →L[ℂ] E) ≤ A.spectralCocutoff s - ((s : ℝ) • (1 : E →L[ℂ] E) - A) := by
    rw [cocutoff_split A hA s]
    refine cfc_nonneg fun t _ => ?_
    rcases le_or_gt (s - t) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  have hform := nonneg_re_inner hnn y
  simp only [sub_apply, hzero, smul_apply, one_apply_eq_self, inner_sub_left,
    map_sub, re_inner_real_smul_self s y, zero_sub, neg_sub] at hform
  have hcs : RCLike.re ⟪A y, y⟫_ℂ ≤ ‖A y‖ * ‖y‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hkey : s * ‖y‖ ^ 2 ≤ ‖A y‖ * ‖y‖ := by linarith
    nlinarith

section SmoothCutoff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Compressing `C` by `cfc p C` is the calculus applied to `x * p x ^ 2`.**

Both cutoff bounds below need this, at `p = tailCutoff u` and at `p = 1 - tailCutoff u`,
and each had written the same four-step `calc` out in full. -/
theorem cfc_mul_self_mul_eq_cfc_mul_sq {C : E →L[ℂ] E} (hC : IsSelfAdjoint C)
    {p : ℝ → ℝ} (hpcont : Continuous p) :
    cfc p C * C * cfc p C = cfc (fun x => x * (p x) ^ 2) C := by
  calc
    cfc p C * C * cfc p C =
        cfc p C * cfc (fun x : ℝ => x) C * cfc p C := by
      rw [cfc_id' ℝ C]
    _ = cfc (fun x : ℝ => p x * x) C * cfc p C := by
      rw [cfc_mul p (fun x : ℝ => x) C
        hpcont.continuousOn continuous_id.continuousOn]
    _ = cfc (fun x : ℝ => (p x * x) * p x) C := by
      rw [cfc_mul (fun x : ℝ => p x * x) p C
        (hpcont.mul continuous_id).continuousOn hpcont.continuousOn]
    _ = cfc (fun x => x * (p x) ^ 2) C := by
      apply cfc_congr
      intro x _
      ring

/-- **A weighted spectral identity, read through the continuous functional calculus.**

The pointwise identity `(x - u ^ 2) * p x ^ 2 = x * p x ^ 2 - u ^ 2 * p x ^ 2` becomes an
operator identity: the left side is `cfc p C * C * cfc p C`, the compression of `C` by
`cfc p C`, and the right side is `u ^ 2` times `cfc p C ^ 2`.

Nothing here is about cutoffs.  `p` is any continuous real function and `u` any real
number, which is why this is stated on its own rather than inline: the cutoff lemma below
uses it at `p = tailCutoff u`, and the argument never looks at what `p` is. -/
theorem cfc_sub_sq_mul_eq_compression_sub_smul {C : E →L[ℂ] E} (hC : IsSelfAdjoint C)
    {p : ℝ → ℝ} (hpcont : Continuous p) (u : ℝ) :
    cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
      cfc p C * C * cfc p C - u ^ 2 • (cfc p C * cfc p C) := by
  have hpcmul : cfc p C * cfc p C = cfc (fun x => (p x) ^ 2) C := by
    calc
      cfc p C * cfc p C = cfc (fun x : ℝ => p x * p x) C :=
        (cfc_mul p p C hpcont.continuousOn hpcont.continuousOn).symm
      _ = cfc (fun x => (p x) ^ 2) C := by
        apply cfc_congr
        intro x _
        ring
  have hpcCpc : cfc p C * C * cfc p C = cfc (fun x => x * (p x) ^ 2) C :=
    cfc_mul_self_mul_eq_cfc_mul_sq hC hpcont
  have hscale :
      u ^ 2 • (cfc p C * cfc p C) = cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
    rw [hpcmul]
    -- No detour through a scoped real-algebra instance is needed here: off the
    -- complexification there is only one `Module ℝ (E →L[ℂ] E)` and `cfc_const_mul`
    -- applies directly.  That detour is what tied this argument to one Hilbert space.
    exact (cfc_const_mul (u ^ 2) (fun x => (p x) ^ 2) C
      (hpcont.fun_pow 2).continuousOn).symm
  calc
    cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
        cfc (fun x => x * (p x) ^ 2 - u ^ 2 * (p x) ^ 2) C := by
      apply cfc_congr
      intro x _
      ring
    _ = cfc (fun x => x * (p x) ^ 2) C -
        cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
      exact cfc_sub (fun x => x * (p x) ^ 2)
        (fun x => u ^ 2 * (p x) ^ 2) C
        ((continuous_id.mul (hpcont.fun_pow 2)).continuousOn)
        ((continuous_const.mul (hpcont.fun_pow 2)).continuousOn)
    _ = cfc p C * C * cfc p C - u ^ 2 • (cfc p C * cfc p C) := by
      rw [← hpcCpc, ← hscale]

/-- **Cutting an operator to the low end of its spectrum leaves norm at most `u`.**

`cfc (1 - tailCutoff u) C`, for the Gram operator `C = S⋆S`, is the multiplier that keeps
the part of the spectrum at or below `u ^ 2`.  Composing `S` with it gives an operator whose own
Gram operator is `x * (1 - tailCutoff u x) ^ 2`, and the cutoff was chosen so that the
functional calculus bounds that by `u ^ 2`.

This is the smooth counterpart of `norm_apply_le_of_spectralCutoff_apply_eq_zero` above,
which splits by a kernel instead.  **A smooth multiplier is not a stylistic preference:** the
consumer is the real min--max theorem, which works on a complexification and needs its cutoff
to *descend to a real operator*, and only a continuous function of `C` is
conjugation-fixed. -/
theorem norm_comp_cfc_one_sub_tailCutoff_le
    (S : E →L[ℂ] F) {u : ℝ} (hu : 0 < u) :
    ‖S ∘L cfc (fun x => 1 - TauCeti.tailCutoff u x) (S.adjoint ∘L S)‖ ≤ u := by
  classical
  set Tc := S with hTc
  set C : E →L[ℂ] E := Tc.adjoint ∘L Tc with hCdef
  have hu0 : 0 < u := hu
  have hCnonneg : (0 : E →L[ℂ] E) ≤ C :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Tc)
  have hCspec_nonneg : ∀ x ∈ spectrum ℝ C, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg hCnonneg hx
  have hCsa : IsSelfAdjoint C :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self Tc).isSelfAdjoint
  set p : ℝ → ℝ := TauCeti.tailCutoff u with hp
  have hpcont : Continuous p := TauCeti.continuous_tailCutoff u hu0
  set q : ℝ → ℝ := fun x => 1 - p x with hq
  have hqcont : Continuous q := continuous_const.sub hpcont
  set Qc : E →L[ℂ] E := cfc q C with hQc
  have hQcSelfAdjoint : IsSelfAdjoint Qc := cfc_predicate q C
  have htailGram :
      (Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc) =
        cfc (fun x => x * (q x) ^ 2) C := by
    rw [ContinuousLinearMap.adjoint_comp, hQcSelfAdjoint.adjoint_eq]
    calc
      (Qc ∘L Tc.adjoint) ∘L (Tc ∘L Qc) =
          (Qc ∘L C) ∘L Qc := by
        simp only [C, ContinuousLinearMap.comp_assoc]
      _ = cfc (fun x => x * (q x) ^ 2) C :=
        cfc_mul_self_mul_eq_cfc_mul_sq hCsa hqcont
  -- and its Gram operator is `x * q x ^ 2`, which the cutoff bounds by `u ^ 2`.
  have htailCfcNorm :
      ‖cfc (fun x => x * (q x) ^ 2) C‖ ≤ u ^ 2 := by
    refine norm_cfc_le (f := fun x : ℝ => x * (q x) ^ 2) (a := C)
      (sq_nonneg u) ?_
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hbound := TauCeti.tailCutoff_tail_bound hu0 hx0
    change |x * (1 - TauCeti.tailCutoff u x) ^ 2| ≤ u ^ 2
    rw [abs_of_nonneg (mul_nonneg hx0 (sq_nonneg _))]
    exact hbound
  have htailComplex : ‖Tc ∘L Qc‖ ≤ u := by
    have hsq : ‖Tc ∘L Qc‖ ^ 2 ≤ u ^ 2 := by
      calc
        ‖Tc ∘L Qc‖ ^ 2 =
            ‖(Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc)‖ := by
              rw [sq, ContinuousLinearMap.norm_adjoint_comp_self]
        _ = ‖cfc (fun x => x * (q x) ^ 2) C‖ := by rw [htailGram]
        _ ≤ u ^ 2 := htailCfcNorm
    exact le_of_sq_le_sq hsq hu0.le
  exact htailComplex

/-- **On the high end of the spectrum the modulus is bounded below by `u`.**

The complement of the previous cutoff, `cfc (tailCutoff u) C`, lands where the Gram operator
is at least `u ^ 2`.  The quadratic form of `cfc ((x - u ^ 2) * tailCutoff u x ^ 2) C` is
nonnegative there, and reading that form through `S` is the stated inequality.

This is the smooth counterpart of `le_norm_apply_of_mem_orthogonal_ker_spectralCutoff`
above. -/
theorem mul_norm_cfc_tailCutoff_le_norm_apply
    (S : E →L[ℂ] F) {u : ℝ} (hu : 0 < u)
    (z : E) :
    u * ‖cfc (TauCeti.tailCutoff u) (S.adjoint ∘L S) z‖ ≤
      ‖S (cfc (TauCeti.tailCutoff u) (S.adjoint ∘L S) z)‖ := by
  classical
  set Tc := S with hTc
  set C : E →L[ℂ] E := Tc.adjoint ∘L Tc with hCdef
  have hu0 : 0 < u := hu
  have hCnonneg : (0 : E →L[ℂ] E) ≤ C :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Tc)
  have hCspec_nonneg : ∀ x ∈ spectrum ℝ C, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg hCnonneg hx
  have hCsa : IsSelfAdjoint C :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self Tc).isSelfAdjoint
  set p : ℝ → ℝ := TauCeti.tailCutoff u with hp
  have hpcont : Continuous p := TauCeti.continuous_tailCutoff u hu0
  set Pc : E →L[ℂ] E := cfc p C with hPc
  have hlowerCfcNonneg :
      (0 : E →L[ℂ] E) ≤
        cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C := by
    apply cfc_nonneg
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hcut := TauCeti.tailCutoff_lower_bound (x := x) hu0
    change 0 ≤ (x - u ^ 2) * (TauCeti.tailCutoff u x) ^ 2
    nlinarith
  have hlowerIdentity :
      cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
        Pc * C * Pc - u ^ 2 • (Pc * Pc) :=
    cfc_sub_sq_mul_eq_compression_sub_smul hCsa hpcont u
  have hPcLower : ∀ z : E, u * ‖Pc z‖ ≤ ‖Tc (Pc z)‖ := by
    intro z
    have hpositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hlowerCfcNonneg
    have hform := hpositive.re_inner_nonneg_left z
    rw [hlowerIdentity] at hform
    have henergy :
        u ^ 2 * ‖Pc z‖ ^ 2 ≤ ‖Tc (Pc z)‖ ^ 2 := by
      change 0 ≤
        RCLike.re ⟪(Pc * C * Pc - u ^ 2 • (Pc * Pc)) z, z⟫_ℂ at hform
      have hPcsa : IsSelfAdjoint Pc := cfc_predicate p C
      have h1 :
          RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ = ‖Tc (Pc z)‖ ^ 2 := by
        simp only [mul_apply_eq_comp]
        have hadj : ⟪Pc (C (Pc z)), z⟫_ℂ = ⟪C (Pc z), Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (C (Pc z)))
        rw [hadj]
        dsimp only [C]
        exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left Tc (Pc z)).symm
      have h2 :
          RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ =
            u ^ 2 * ‖Pc z‖ ^ 2 := by
        have hadj : ⟪Pc (Pc z), z⟫_ℂ = ⟪Pc z, Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (Pc z))
        simp only [smul_apply, mul_apply_eq_comp]
        rw [inner_smul_left_eq_smul, hadj, inner_self_eq_norm_sq_to_K,
          RCLike.smul_re, RCLike.re_ofReal_pow]
      have hform' :
          0 ≤ RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ -
            RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ := by
        simpa only [sub_apply, inner_sub_left, map_sub] using hform
      rw [h1, h2] at hform'
      linarith
    exact le_of_sq_le_sq (by simpa [mul_pow] using henergy) (norm_nonneg _)
  exact hPcLower z

end SmoothCutoff

end ContinuousLinearMap
