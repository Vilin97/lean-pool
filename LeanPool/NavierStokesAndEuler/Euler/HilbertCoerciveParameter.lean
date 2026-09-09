/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator

@[expose] public section

/-!
# Parameter regularity of the genuinely constructed coercive inverse

The positive lower-bound certificate may vary with the parameter and need not
be differentiable. The inverse itself is the actual operator inverse, so its
regularity depends only on the operator coefficients.
-/

noncomputable section

open scoped ContDiff

namespace EulerHilbertCoerciveParameter

open ContinuousLinearMap InnerProductSpace EulerCoerciveProjection EulerInverseRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Changing the coercivity certificate does not affect parameter regularity
of the actual inverse operator. -/
theorem contDiff_coerciveInverse_variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hA : ∀ x v, c x * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    {n : ℕ∞ω} (hreg : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => coerciveInverse (A x) (c x) (hc x) (hA x)) := by
  have hfun : (fun x => coerciveInverse (A x) (c x) (hc x) (hA x)) =
      fun x => (A x).inverse := by
    funext x
    exact coerciveInverse_eq_mapInverse (A x) (c x) (hc x) (hA x)
  rw [hfun, contDiff_iff_contDiffAt]
  intro x
  have he : (coerciveEquiv (A x) (c x) (hc x) (hA x) : E →L[ℝ] E) = A x := by
    ext v
    exact coerciveEquiv_apply (A x) (c x) (hc x) (hA x) v
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse (A x) := by
    rw [← he]
    exact contDiffAt_map_inverse (coerciveEquiv (A x) (c x) (hc x) (hA x))
  exact hinv.comp x hreg.contDiffAt

/-- The actual derivative of an inverse, even with a varying coercivity certificate. -/
theorem hasDerivAt_coerciveInverse_variable
    (A : ℝ → E →L[ℝ] E) (c : ℝ → ℝ) (hc : ∀ x, 0 < c x)
    (hA : ∀ x v, c x * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    (x : ℝ) (A₁ : E →L[ℝ] E) (hder : HasDerivAt A A₁ x) :
    HasDerivAt (fun r => coerciveInverse (A r) (c r) (hc r) (hA r))
      (-(coerciveInverse (A x) (c x) (hc x) (hA x)).comp
        (A₁.comp (coerciveInverse (A x) (c x) (hc x) (hA x)))) x := by
  let u : (E →L[ℝ] E)ˣ := (coerciveEquiv (A x) (c x) (hc x) (hA x)).toUnit
  have hu : (u : E →L[ℝ] E) = A x := by
    ext v
    exact coerciveEquiv_apply (A x) (c x) (hc x) (hA x) v
  have hui : (↑u⁻¹ : E →L[ℝ] E) = coerciveInverse (A x) (c x) (hc x) (hA x) := rfl
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hcomp := hi.comp_hasDerivAt x hder
  have hfun : (fun r => coerciveInverse (A r) (c r) (hc r) (hA r)) = Ring.inverse ∘ A := by
    funext r
    exact coerciveInverse_eq_ringInverse (A r) (c r) (hc r) (hA r)
  rw [hfun]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcomp

/-- Actual forcing-to-solution regularity for a parameterized coercive solve. -/
theorem contDiff_coerciveSolution_variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → E →L[ℝ] E) (c : P → ℝ) (hc : ∀ x, 0 < c x)
    (hA : ∀ x v, c x * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    (f : P → E) {n : ℕ∞ω} (hreg : ContDiff ℝ n A) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => coerciveInverse (A x) (c x) (hc x) (hA x) (f x)) :=
  (contDiff_coerciveInverse_variable A c hc hA hreg).clm_apply hf

end EulerHilbertCoerciveParameter
