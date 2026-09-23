/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module

/-!
# The rotation branching rule

This file proves `apd:eq:pauli_rotation_branch`, the elementary step of Pauli propagation, in an
arbitrary ℂ-algebra:

  `e^{i G dt/2} P e^{-i G dt/2} = P`                             if `[G,P] = 0`,
  `e^{i G dt/2} P e^{-i G dt/2} = cos(dt) P + i sin(dt) · G P`   if `{G,P} = 0`.

**This needs neither `exp` nor Pauli strings.** For any `G` with `G * G = 1` the exponential
series splits into even and odd parts and collapses to the closed form
`e^{i G θ/2} = cos(θ/2) · 1 + i sin(θ/2) · G`. Taking *that* as the definition (`rot`) reduces
the identity to algebra in a ℂ-algebra, and the file therefore sits beside `Lean4LPD.Ladder`
as a second piece of abstract, non-quantum infrastructure. The Pauli model (`Pauli/Basic.lean`,
`Pauli/Matrix.lean`, `Pauli/Branch.lean`) instantiates `A` at an operator algebra and supplies
`G * G = 1` from `G` being a *self-adjoint unitary* — Hermiticity alone would not give it — but
nothing here depends on that.

Mathlib has no "exponential of an involution" lemma — the `x² = +1` case is the missing sibling
of `Analysis/Normed/Algebra/QuaternionExponential.lean` (`q² = -‖q‖²`) and `TrivSqZeroExt`
(`ε² = 0`). `RotationExp.lean` proves that `rot` equals `NormedSpace.exp` of the generator
(`rot_eq_exp`) by splitting the exponential series, in a Hausdorff topological complex algebra;
no norm or completeness assumption is needed. This file keeps the algebraic closed form so that
its lemmas retain their purely algebraic signatures.

## Main definitions

* `rot G θ`: the closed form `cos(θ/2) · 1 + i sin(θ/2) · G` of the rotation `e^{i G θ/2}`.

## Main results

* `rot_mul_rot`: angle addition, `rot G θ₁ * rot G θ₂ = rot G (θ₁ + θ₂)`, for `G * G = 1`.
* `rot_mul_rot_neg`, `rot_neg_mul_rot`: `rot G (-θ)` is the two-sided inverse of `rot G θ`.
* `rot_conj_of_commute`: the commuting branch of `apd:eq:pauli_rotation_branch`.
* `rot_conj_of_anticommute`: the anticommuting branch.
* `rot_mem_unitary`: a rotation with a self-adjoint involutive generator is unitary.

## Conventions

The angle convention is the paper's half-angle convention (`apd:eq:pauli_rotation_branch`,
`apd:thm:local_flow_k_local`): the *conjugation angle* `dt` is primitive and the unitary is
`e^{-i G dt/2}`, so that conjugation by `e^{-i G dt/2}` rotates an anticommuting Pauli by `dt`.
A physical rotation `e^{-i α_l G_l τ}` therefore has `dt = 2 α_l τ`, and the factor `2` is
absorbed in `α := 2 max_l |α_l|`. Conjugation is in the Heisenberg picture, `U† P U` with
`U = e^{-i G dt/2}`, so the `+` exponent stands on the left and the new term is
`+i sin(dt) · G P` with the generator on the *left* of `P`. The half angle is part of the
statement, not notation: conjugation by the full-angle gate `e^{-i G dt}` would rotate by `2 dt`.

## Relation to the paper's three consequences

The paper draws three consequences from the identity: the transition is sparse in the Pauli
basis, the weight change is bounded by the locality of `G`, and the amplitude of the new term is
damped by `sin(dt)`. `rot_conj_of_anticommute` supplies the arithmetic underneath the first and
third — the image lies in `span {P, G * P}`, and the second term's coefficient is `I * sin(dt)`.
Each needs something further from the Pauli model, and it is *not the same thing*:

* *sparsity* needs a Pauli basis, with `P` and `G * P` proportional to basis elements — only
  proportional, since `Z * X = I * Y`. The span bound itself holds here unconditionally, and
  says nothing about a basis. The coefficient-level statement is `coeffVec_conj` in
  `Pauli/Flow.lean`.
* *damping* needs `P` and `G * P` linearly independent, so that the second term is a new
  transition rather than a rescaling of the first. Distinctness is not enough: `G = Z` and
  `P = E₁₀` in `Matrix (Fin 2) (Fin 2) ℂ` satisfy both hypotheses with `G * P = -P`. For Pauli
  strings linear independence is `PauliString.linearIndependent_toMatrix_mul_pair` in
  `Pauli/Matrix.lean`.

The second consequence, the weight bound, is proved in `Pauli/Weight.lean`.

## Implementation notes

Anticommutation is spelled `G * P = -(P * G)`; Mathlib has no `Anticommute` predicate. It is
`SemiconjBy G P (-P)` up to `neg_mul` — propositionally, not definitionally, since `SemiconjBy`
unfolds to `G * P = -P * G` — should that API ever be wanted. The involution hypothesis
is likewise written inline, following `Mathlib/Algebra/Star/CHSH.lean`. The Clifford-algebra
analogue of the anticommuting case is `CliffordAlgebra.ι_mul_ι_comm_of_isOrtho`, but routing
through it would cost more than the direct proof: the conjugator there is a vector, not a rotor.
-/

@[expose] public section

namespace Lean4LPD

variable {A : Type*} [Ring A] [Algebra ℂ A] {G P : A} {θ θ₁ θ₂ : ℝ}

/-- The rotation `e^{+ i G θ / 2}`, written in the closed form it takes when `G * G = 1`.

This is an algebraic definition. `Lean4LPD.rot_eq_exp` (in `RotationExp.lean`) proves that it
equals the exponential `NormedSpace.exp ((I * (θ / 2)) • G)` whenever `G * G = 1`, by summing
the even and odd parts of the series, and `PauliString.rot_toMatrix_eq_exp` specializes that to
Pauli matrices. Keeping the closed form here avoids adding analytic hypotheses to the algebraic
lemmas below. The paper's gate `e^{-i G dt/2}` is `rot G (-dt)`.

As a definition it is unconditional. When `G * G = 1` its two-sided inverse is `rot G (-θ)`,
and parity of `cos` and `sin` is what supplies that negative-angle expression, so no separate
inverse definition is needed. Drop the involution hypothesis and there need be no inverse at
all — `rot (0 : ℂ) π = 0`. -/
noncomputable def rot (G : A) (θ : ℝ) : A :=
  (Real.cos (θ / 2) : ℂ) • 1 + (Complex.I * Real.sin (θ / 2)) • G

/-- A zero-angle rotation is the identity. -/
@[simp]
lemma rot_zero : rot G 0 = 1 := by
  simp [rot]

/-- Products of `i`-scaled complex numbers, in the shape the expansion of `rot * rot` produces. -/
private lemma mul_I_mul_I (a b : ℂ) : Complex.I * a * (Complex.I * b) = -(a * b) := by
  rw [show Complex.I * a * (Complex.I * b) = Complex.I * Complex.I * (a * b) by ring,
    Complex.I_mul_I]
  ring

/-- **Angle addition.** The main computational lemma: both branches of the rotation rule are
corollaries of it. (Two others unfold the definition rather than following from this one —
`rot_mul_eq_mul_rot_neg` and `star_rot`.) This is where the double angle of
`apd:eq:pauli_rotation_branch` comes from — via `cos_add` and `sin_add` on the half angles,
rather than via `cos_two_mul'`. -/
lemma rot_mul_rot (hG : G * G = 1) : rot G θ₁ * rot G θ₂ = rot G (θ₁ + θ₂) := by
  have hhalf : (θ₁ + θ₂) / 2 = θ₁ / 2 + θ₂ / 2 := by ring
  have hc : ((Real.cos ((θ₁ + θ₂) / 2) : ℝ) : ℂ)
      = (Real.cos (θ₁ / 2) : ℂ) * (Real.cos (θ₂ / 2) : ℂ)
        - (Real.sin (θ₁ / 2) : ℂ) * (Real.sin (θ₂ / 2) : ℂ) := by
    rw [hhalf, Real.cos_add]; push_cast; ring
  have hs : ((Real.sin ((θ₁ + θ₂) / 2) : ℝ) : ℂ)
      = (Real.sin (θ₁ / 2) : ℂ) * (Real.cos (θ₂ / 2) : ℂ)
        + (Real.cos (θ₁ / 2) : ℂ) * (Real.sin (θ₂ / 2) : ℂ) := by
    rw [hhalf, Real.sin_add]; push_cast; ring
  simp only [rot, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hG, mul_I_mul_I, hc, hs]
  module

/-- `rot G (-θ)` is a right inverse. -/
lemma rot_mul_rot_neg (hG : G * G = 1) : rot G θ * rot G (-θ) = 1 := by
  rw [rot_mul_rot hG, add_neg_cancel, rot_zero]

/-- `rot G (-θ)` is a left inverse. -/
lemma rot_neg_mul_rot (hG : G * G = 1) : rot G (-θ) * rot G θ = 1 := by
  rw [rot_mul_rot hG, neg_add_cancel, rot_zero]

/-- A rotation commutes with everything its generator commutes with: `rot` is a linear
combination of `1` and `G`. -/
lemma commute_rot (h : Commute G P) : Commute (rot G θ) P :=
  ((Commute.one_left P).smul_left _).add_left (h.smul_left _)

/-- **Commuting branch** of `apd:eq:pauli_rotation_branch`: a rotation whose
generator commutes with `P` leaves `P` alone. No weight change, no new Pauli. -/
theorem rot_conj_of_commute (hG : G * G = 1) (h : Commute G P) :
    rot G θ * P * rot G (-θ) = P := by
  rw [(commute_rot h).eq, mul_assoc, rot_mul_rot_neg hG, mul_one]

/-- Anticommutation lets `P` move across a rotation at the cost of negating the angle.
Note this needs no hypothesis on `G * G`. -/
lemma rot_mul_eq_mul_rot_neg (h : G * P = -(P * G)) : rot G θ * P = P * rot G (-θ) := by
  have hPG : P * G = -(G * P) := by rw [h, neg_neg]
  simp only [rot, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    neg_div, Real.cos_neg, Real.sin_neg, hPG]
  push_cast
  module

/-- **Anticommuting branch** of `apd:eq:pauli_rotation_branch`:

  `e^{i G dt/2} P e^{-i G dt/2} = cos(dt) · P + i sin(dt) · G P`.

The hypotheses are `G * G = 1` and `G * P = -(P * G)`; nothing else about `G` or `P` is used.

Two of the three consequences the paper draws from the identity (sparsity and damping) sit under
this statement in arithmetic form: the image lies in `span {P, G * P}`, and the second term's
coefficient is `I * sin θ`.

At this level of generality neither is yet the statement about Pauli coefficients, and they are
short of different things. *Sparsity* needs a Pauli basis with `P` and `G * P` proportional to
basis elements; the span bound above is unconditional and says nothing about a basis. *Damping*
needs the two linearly independent, so that `I * sin θ` is the amplitude of a new transition and
not a rescaling of `P` — and mere distinctness does not give that: with `G = Z` and `P = E₁₀` in
`Matrix (Fin 2) (Fin 2) ℂ` both hypotheses hold and `G * P = -P`, collapsing the sum to
`(cos θ - I * sin θ) • P`.

Both are supplied for Pauli strings by `Pauli/Matrix.lean` and `Pauli/Flow.lean`, and the second
consequence, that the weight changes by at most `k_h - 1`, by `Pauli/Weight.lean`. -/
theorem rot_conj_of_anticommute (hG : G * G = 1) (h : G * P = -(P * G)) :
    rot G θ * P * rot G (-θ)
      = (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) := by
  rw [mul_assoc, ← rot_mul_eq_mul_rot_neg h, ← mul_assoc, rot_mul_rot hG]
  simp only [rot, add_mul, smul_mul_assoc, one_mul, show (θ + θ) / 2 = θ by ring]

section Star

variable [StarRing A] [StarModule ℂ A]

/-- Adjoining a rotation reverses its angle, when the generator is self-adjoint. -/
lemma star_rot (hG : star G = G) : star (rot G θ) = rot G (-θ) := by
  simp only [rot, star_add, star_smul, star_one, hG, neg_div, Real.cos_neg, Real.sin_neg,
    Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  module

/-- A rotation with a self-adjoint involutive generator is **unitary**. Since `unitary A` is a
submonoid, any finite product of rotations is unitary for free — including the paper's product
`U_g := ∏_{l ≤ g} e^{-i G_l dt/2}` of `apd:thm:local_flow_k_local`, which in this file's
convention is `∏ rot G_l (-dt)`, not `∏ rot G_l dt`: `rot G θ` is the `+` exponential.

This is unitarity only. The invariance of the Pauli 2-norm under conjugation (the `reservoir`
field of `Lean4LPD.Ladder`, used in the base case of `apd:cor:norm_cumulation_jump`) is a
statement about a norm this file deliberately does not carry; for Pauli rotations it is
`pauliNorm_conj` in `Pauli/Flow.lean`. -/
theorem rot_mem_unitary (hG₂ : G * G = 1) (hG : star G = G) : rot G θ ∈ unitary A :=
  Unitary.mem_iff.2
    ⟨by rw [star_rot hG]; exact rot_neg_mul_rot hG₂,
     by rw [star_rot hG]; exact rot_mul_rot_neg hG₂⟩

end Star

/-- The intended model: the `2^n × 2^n` matrix algebra — the operators on `n`
qubits, of ℂ-dimension `4^n` — where `G` and `P` will be Pauli strings.

Stated as an `example` because it adds no API: its only job is to check that
the `Ring` and `Algebra ℂ` instances fire without further hypotheses. -/
example (n : ℕ) (G P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (θ : ℝ)
    (hG : G * G = 1) (h : G * P = -(P * G)) :
    rot G θ * P * rot G (-θ)
      = (Real.cos θ : ℂ) • P + (Complex.I * Real.sin θ) • (G * P) :=
  rot_conj_of_anticommute hG h

end Lean4LPD
