/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Davis--Kahan 1970, Section 9: Schur-complement reduction

This file formalizes equations (9.9)--(9.11) independently of the numerical
free-beam realization.  The first section is algebraic and works for arbitrary
modules over a field: it says that the lower block equation determines the
complementary coordinate once a left inverse of `lam I - A₁` is available, and
that substituting it into the upper block gives the reduced eigenproblem.

The second section is the quantitative half, and it deliberately avoids ever
forming an inverse.  In the source's situation the lower block `A₁` is bounded
below by `β` in the quadratic-form sense while the eigenvalue `lam` sits below
`β`, and every estimate the argument needs follows from testing the lower block
equation against the complementary coordinate itself:

* `norm_lower_coordinate_le` — `(β - lam) ‖y‖ ≤ ‖B x‖`, which is equation
  (9.10) in the only form the estimates use;
* `schurCoefficient_nonneg` and `schurCoefficient_le` — the scalar
  `-re ⟪B x, y⟫` that the substituted upper block contributes is nonnegative
  and at most `‖B x‖² / (β - lam)`;
* `lower_coordinate_eq_zero_of_residual_eq_zero` — the nondegeneracy behind
  "`x ≠ 0`": a block eigenvector whose trial coordinate is annihilated by the
  residual has no complementary coordinate either.

Because the lower block never appears except through the vector `A₁ y`, these
statements carry no domain hypothesis and apply verbatim to an unbounded lower
block.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

section SchurComplement

variable {𝕜 E F : Type*}
variable [Field 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

variable (A₀ : E →ₗ[𝕜] E) (A₁ : F →ₗ[𝕜] F)
variable (B : E →ₗ[𝕜] F) (Bstar : F →ₗ[𝕜] E)
variable (C : F →ₗ[𝕜] F) (lam : 𝕜)

/-- The block operator in equation (9.9). -/
def blockOperator : (E × F) →ₗ[𝕜] (E × F) where
  toFun z := (A₀ z.1 + Bstar z.2, B z.1 + A₁ z.2)
  -- `simp` normalizes both sides to sums in a different association order,
  -- so each component needs an abelian-group rearrangement to close
  map_add' x y := by ext <;> simp <;> abel
  map_smul' c x := by ext <;> simp

/-- The block operator, unfolded to its two coordinates. -/
@[simp] lemma blockOperator_apply (x : E) (y : F) :
    blockOperator A₀ A₁ B Bstar (x, y) =
      (A₀ x + Bstar y, B x + A₁ y) := rfl

/-- Equation (9.9) is equivalent to its upper and lower block equations. -/
theorem block_eigenproblem_iff (x : E) (y : F) :
    blockOperator A₀ A₁ B Bstar (x, y) = lam • (x, y) ↔
      A₀ x + Bstar y = lam • x ∧ B x + A₁ y = lam • y := by
  simp [blockOperator]

/-- The shifted lower block `lam I - A₁`. -/
def lowerShift : F →ₗ[𝕜] F := lam • LinearMap.id - A₁

/-- The lower shift acts by moving each coordinate down one index. -/
lemma lowerShift_apply (y : F) :
    lowerShift A₁ lam y = lam • y - A₁ y := by
  rfl

/-- Equation (9.10): the lower block equation determines the complementary
coordinate after applying a left inverse of `lam I - A₁`. -/
theorem lower_coordinate_eq
    (x : E) (y : F)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    y = C (B x) := by
  have hshift : lowerShift A₁ lam y = B x := by
    rw [lowerShift_apply]
    exact (eq_sub_iff_add_eq.mpr hbottom).symm
  calc
    y = C (lowerShift A₁ lam y) := (hleft y).symm
    _ = C (B x) := congrArg C hshift

/-- Equation (9.11): substituting the complementary coordinate into the upper
block equation yields the reduced eigenproblem on the trial space. -/
theorem reduced_eigenproblem
    (x : E) (y : F)
    (htop : A₀ x + Bstar y = lam • x)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    A₀ x + Bstar (C (B x)) = lam • x := by
  have hy := lower_coordinate_eq A₁ B C lam x y hbottom hleft
  simpa [hy] using htop

/-- A bundled version of equations (9.10) and (9.11). -/
theorem schur_complement_reduction
    (x : E) (y : F)
    (htop : A₀ x + Bstar y = lam • x)
    (hbottom : B x + A₁ y = lam • y)
    (hleft : Function.LeftInverse C (lowerShift A₁ lam)) :
    y = C (B x) ∧ A₀ x + Bstar (C (B x)) = lam • x := by
  exact ⟨lower_coordinate_eq A₁ B C lam x y hbottom hleft,
    reduced_eigenproblem A₀ A₁ B Bstar C lam x y htop hbottom hleft⟩

end SchurComplement

section BlockEstimates

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The shifted lower-block quadratic form, computed.  `w` stands for `A₁ y`. -/
private lemma re_inner_sub_smul_self (w y : F) (lam : ℝ) :
    RCLike.re (inner 𝕜 (w - (lam : 𝕜) • y) y)
      = RCLike.re (inner 𝕜 w y) - lam * ‖y‖ ^ 2 := by
  have hyy : (inner 𝕜 y y : 𝕜) = ((‖y‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal, hyy, map_sub,
    ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The key one-line estimate: testing the lower block equation `B x + A₁ y =
lam y` against `y` and using the form lower bound `β` on the lower block. -/
private lemma lower_block_test {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y)) :
    (β - lam) * ‖y‖ ^ 2 ≤ -RCLike.re (inner 𝕜 b y) ∧
      -RCLike.re (inner 𝕜 b y) ≤ ‖b‖ * ‖y‖ := by
  have hsub : w - (lam : 𝕜) • y = -b := by
    rw [← hbottom]
    abel
  have hval : RCLike.re (inner 𝕜 w y) - lam * ‖y‖ ^ 2
      = -RCLike.re (inner 𝕜 b y) := by
    rw [← re_inner_sub_smul_self (𝕜 := 𝕜) w y lam, hsub, inner_neg_left, map_neg]
  refine ⟨by linarith [hval], ?_⟩
  have hcs : RCLike.re (inner 𝕜 (-b) y) ≤ ‖-b‖ * ‖y‖ :=
    re_inner_le_norm (𝕜 := 𝕜) (-b) y
  rw [inner_neg_left, map_neg, norm_neg] at hcs
  exact hcs

/-- **Equation (9.10), inverse-free.**  If the lower block equation
`B x + A₁ y = lam y` holds and the lower block has form lower bound `β > lam`,
then the complementary coordinate is small: `(β - lam) ‖y‖ ≤ ‖B x‖`.

The lower block enters only through the vector `w = A₁ y`, so no domain,
closedness, or self-adjointness hypothesis is needed. -/
theorem norm_lower_coordinate_le {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y))
    (_hlt : lam < β) :
    (β - lam) * ‖y‖ ≤ ‖b‖ := by
  obtain ⟨h1, h2⟩ := lower_block_test (𝕜 := 𝕜) hbottom hform
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
  · rw [← hy0, mul_zero]
    exact norm_nonneg b
  · have : (β - lam) * ‖y‖ ^ 2 ≤ ‖b‖ * ‖y‖ := le_trans h1 h2
    nlinarith

/-- **The Schur coefficient is nonnegative.**  The scalar that the substituted
upper block contributes, `-re ⟪B x, y⟫`, is the value of the positive form
`(A₁ - lam)⁻¹` at `B x`; it is nonnegative without ever forming that inverse. -/
theorem schurCoefficient_nonneg {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y))
    (hlt : lam < β) :
    0 ≤ -RCLike.re (inner 𝕜 b y) := by
  obtain ⟨h1, -⟩ := lower_block_test (𝕜 := 𝕜) hbottom hform
  have hbl : 0 ≤ (β - lam) * ‖y‖ ^ 2 :=
    mul_nonneg (sub_nonneg.2 hlt.le) (sq_nonneg _)
  linarith

/-- **The Schur coefficient is bounded by the Loewner constant.**  The
inequality `(β - lam) * (-re ⟪B x, y⟫) ≤ ‖B x‖²` is the conjugated resolvent
sandwich `B⋆ (A₁ - lam)⁻¹ B ≤ (β - lam)⁻¹ B⋆ B`, evaluated at `x` and proved
directly from the block equation. -/
theorem schurCoefficient_le {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y))
    (hlt : lam < β) :
    (β - lam) * (-RCLike.re (inner 𝕜 b y)) ≤ ‖b‖ ^ 2 := by
  obtain ⟨-, h2⟩ := lower_block_test (𝕜 := 𝕜) hbottom hform
  have hy := norm_lower_coordinate_le (𝕜 := 𝕜) hbottom hform hlt
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg b
  nlinarith

/-- **Nondegeneracy: the trial coordinate of a block eigenvector cannot
vanish.**  If `B x = 0` — in particular if `x = 0` — then the complementary
coordinate vanishes too, so the eigenvector is zero.  This is the step that
rules out an eigenvector living entirely in the complement, whose eigenvalue
would have to be at least `β`. -/
theorem lower_coordinate_eq_zero_of_residual_eq_zero {b w y : F} {lam β : ℝ}
    (hbottom : b + w = (lam : 𝕜) • y)
    (hform : β * ‖y‖ ^ 2 ≤ RCLike.re (inner 𝕜 w y))
    (hlt : lam < β) (hb : b = 0) :
    y = 0 := by
  have h := norm_lower_coordinate_le (𝕜 := 𝕜) hbottom hform hlt
  rw [hb, norm_zero] at h
  have : ‖y‖ ≤ 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.1 (le_antisymm this (norm_nonneg y))

end BlockEstimates

end Section9
end DavisKahan1970
end TauCeti
