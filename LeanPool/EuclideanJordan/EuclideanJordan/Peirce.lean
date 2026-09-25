/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination



/-!
# The Peirce decomposition at a single idempotent

It is natural to expect the Peirce decomposition to depend on the spectral theorem. **It does
not, in the direction that matters, and this file is the evidence.**
The Peirce decomposition at a *given* idempotent needs the Jordan identity and the
invertibility of `2`, and nothing else: no spectral theorem, no formal reality, no finite
dimension, no inner product, not even a unit.
★ The first draft of this sentence said "the Jordan identity and nothing else", which is
wrong — `peirce_poly` divides by `2` (`two_smul_eq_zero'`), which is why every statement below
it carries `Module ℝ J`. Only the *linearised identities* `two_lin1_raw`/`two_lin1_apply` are
genuinely torsion-free, and they are, deliberately: their factor of `2` is carried in the
statement rather than cancelled. Caught 2026-08-12 by reading the `omit` lines against this
paragraph. What the spectral theorem is needed for is *producing* idempotents — a Jordan frame —
    not for
decomposing at one that is already in hand. `EuclideanJordan/FrameExists.lean` does the
producing; this file does the decomposing.

## The mathematics

For an idempotent `c`, the multiplication operator `L_c : y ↦ c ∘ y` satisfies

  `2·L_c³ − 3·L_c² + L_c = 0`,   i.e.   `L_c (L_c − 1) (2L_c − 1) = 0`,

so its only possible eigenvalues are `0`, `1/2`, `1`, and the three Lagrange interpolants
at those roots are projections summing to the identity. That is the Peirce decomposition
`J = J₁(c) ⊕ J_{1/2}(c) ⊕ J₀(c)`.

The polynomial identity comes from **one** substitution into the linearised Jordan identity.
Writing `⁅·,·⁆` for the commutator of multiplication operators, polarising the Jordan
identity `⁅L_x, L_{x²}⁆ = 0` at `x = a ± b` and subtracting gives

  `⁅L_{a²}, L_b⁆ + 2⁅L_{ab}, L_a⁆ = 0`   (`two_lin1_raw`, up to a factor of 2),

and evaluating that at `a := c`, `b := y`, argument `:= c` collapses immediately to the
Peirce polynomial. Mathlib proves only the `a ↔ b` *symmetrised* consequence
(`two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add`), which is strictly weaker; the `a − b`
substitution is what separates the two halves, and it costs one extra line.

## What is here, and what is not

Here: the polynomial identity, the three projections, the resolution of the identity, the
three eigenvalue equations, existence and uniqueness of the decomposition, and the
trichotomy (`L_c` has no eigenvalue outside `{0, 1/2, 1}`).

**Not here:** the Faraut–Korányi *multiplication rules* between Peirce components
(`J_i ∘ J_j ⊆ …`), which are `EuclideanJordan/PeirceMul.lean`, and the decomposition relative
to a whole Jordan frame, which is `EuclideanJordan/FramePeirce.lean`. Nothing in this file
should be read as covering them.

## References

Mathlib's Jordan support (`Mathlib/Algebra/Jordan/Basic.lean`, 237 lines) is the classes
`IsJordan` / `IsCommJordan`, five operator-commutation lemmas and two linearised
identities. There is no idempotent theory, no Peirce decomposition and no spectral theory
in Mathlib; we are aware of none in any other proof assistant either, though we have not
searched them systematically.

* Faraut and Korányi, *Analysis on Symmetric Cones*, Prop. IV.1.1.
* McCrimmon, *A Taste of Jordan Algebras*, §II.8.
-/

@[expose] public section

namespace EuclideanJordan

local notation "L" => AddMonoid.End.mulLeft

/-! Applying an `AddMonoid.End` expression to an element is definitional in every constructor
we use, but Mathlib's corresponding lemmas are phrased for the `AddMonoidHom` coercion and do not
match the `AddMonoid.End` one.  Lean 4.28's simp set bridged this on its own; 4.30's does not, so
the four `rfl`s are stated here and passed to `simpa` explicitly. -/

private theorem L_apply {J : Type*} [NonUnitalNonAssocSemiring J] (a w : J) :
    (AddMonoid.End.mulLeft a) w = a * w := rfl

private theorem End_add_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f g : AddMonoid.End J) (w : J) : (f + g) w = f w + g w := rfl

private theorem End_mul_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f g : AddMonoid.End J) (w : J) : (f * g) w = f (g w) := rfl

private theorem End_neg_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f : AddMonoid.End J) (w : J) : (-f) w = -(f w) := rfl

section Linearisation

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J]

/-- **Twice the linearised Jordan identity.** Polarising `⁅L_x, L_{x²}⁆ = 0` at `x = a + b`
and at `x = a − b` and subtracting isolates the half that the symmetrised Mathlib version
(`two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add`) leaves fused.

Stated with the factor `2` carried rather than cancelled, so that this lemma needs no
torsion hypothesis and holds over any `NonUnitalNonAssocCommRing`. -/
theorem two_lin1_raw (a b : J) :
    (2 : ℕ) • ⁅L b, L (a * a)⁆ + (4 : ℕ) • ⁅L a, L (a * b)⁆ = 0 := by
  -- Mathlib's `LieRing.ofAssociativeRing` is only a `local instance` of its own file, so a ring's
  -- commutator carries `Ring.instBracket` but no `LieRing`, and `lie_add`/`add_lie`/`lie_sub`/
  -- `sub_lie` cannot fire on `AddMonoid.End J`.  Reinstating it here is what makes the `simp only`
  -- below distribute the bracket over the polarised sums.
  let _ : LieRing (AddMonoid.End J) := LieRing.ofAssociativeRing
  have hs := (commute_lmul_lmul_sq (a + b)).lie_eq
  have hd := (commute_lmul_lmul_sq (a - b)).lie_eq
  have ha := (commute_lmul_lmul_sq a).lie_eq
  have hb := (commute_lmul_lmul_sq b).lie_eq
  simp only [add_mul, mul_add, sub_mul, mul_sub, map_add, map_sub, lie_add, add_lie,
    lie_sub, sub_lie, mul_comm b a] at hs hd
  rw [ha, hb] at hs hd
  have h := sub_eq_zero_of_eq (hs.trans hd.symm)
  rw [← h]
  abel

/-- `two_lin1_raw` evaluated at an element. -/
theorem two_lin1_apply (a b w : J) :
    (2 : ℕ) • (b * (a * a * w) - a * a * (b * w))
      + (4 : ℕ) • (a * (a * b * w) - a * b * (a * w)) = 0 := by
  have h := congrArg (fun f : AddMonoid.End J => f w) (two_lin1_raw a b)
  simpa [Ring.lie_def, sub_eq_add_neg, L_apply, End_add_apply, End_mul_apply,
    End_neg_apply] using h

end Linearisation

section Projections

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]

/-- In a *commutative* algebra the scalar-tower rule already gives the `SMulCommClass`
rule, so only `IsScalarTower` has to be assumed — which is what the concrete carrier
`HermitianMat` supplies (`EuclideanJordan/Vendor/HermitianMat/Jordan.lean`). -/
theorem mul_smul_comm' (r : ℝ) (a b : J) : a * (r • b) = r • (a * b) := by
  rw [mul_comm, smul_mul_assoc, mul_comm]

/-- The Jordan multiplication operator `L_c : y ↦ c ∘ y`, as an `ℝ`-linear map. -/
def mulL (c : J) : J →ₗ[ℝ] J where
  toFun y := c * y
  map_add' := mul_add c
  map_smul' r y := mul_smul_comm' r c y

@[simp] theorem mulL_apply (c y : J) : mulL c y = c * y := rfl

/-- The Peirce projection onto the `1`-eigenspace of `L_c`: the Lagrange interpolant
`2L² − L`, which is `1` at `1` and `0` at `0` and `1/2`. -/
def peirceOne (c : J) : J →ₗ[ℝ] J := (2 : ℝ) • (mulL c ∘ₗ mulL c) - mulL c

/-- The Peirce projection onto the `1/2`-eigenspace of `L_c`: the Lagrange interpolant
`4L − 4L²`. -/
def peirceHalf (c : J) : J →ₗ[ℝ] J := (4 : ℝ) • mulL c - (4 : ℝ) • (mulL c ∘ₗ mulL c)

/-- The Peirce projection onto the `0`-eigenspace of `L_c`: the Lagrange interpolant
`1 − 3L + 2L²`. -/
def peirceZero (c : J) : J →ₗ[ℝ] J :=
  LinearMap.id - (3 : ℝ) • mulL c + (2 : ℝ) • (mulL c ∘ₗ mulL c)

@[simp] theorem peirceOne_apply (c y : J) :
    peirceOne c y = (2 : ℝ) • (c * (c * y)) - c * y := rfl

@[simp] theorem peirceHalf_apply (c y : J) :
    peirceHalf c y = (4 : ℝ) • (c * y) - (4 : ℝ) • (c * (c * y)) := rfl

@[simp] theorem peirceZero_apply (c y : J) :
    peirceZero c y = y - (3 : ℝ) • (c * y) + (2 : ℝ) • (c * (c * y)) := rfl

/-- **The resolution of the identity.** The three Lagrange interpolants sum to `1`.

★ This is pure polynomial arithmetic and holds for **every** `c`, idempotent or not — it is
the Jordan identity that makes the three summands land in the eigenspaces, not the
resolution itself. Keeping the two facts separate is what makes the failure mode visible:
a decomposition into three pieces is worthless without knowing what the pieces are. -/
theorem peirce_add_add (c y : J) : peirceOne c y + peirceHalf c y + peirceZero c y = y := by
  simp only [peirceOne_apply, peirceHalf_apply, peirceZero_apply]
  module

/-! ### How the projections act on the eigenspaces

These six lemmas are the "already an eigenvector" direction, and — like `peirce_add_add` —
they are polynomial arithmetic that needs no Jordan identity: they say what the Lagrange
interpolants do to something already known to satisfy `c ∘ y = μ • y`. -/

/-- On the `1`-eigenspace, `peirceOne` is the identity. -/
theorem peirceOne_of_eigen {c y : J} (h : c * y = y) : peirceOne c y = y := by
  simp only [peirceOne_apply, h]
  module

/-- `peirceOne` kills the `1/2`-eigenspace. -/
theorem peirceOne_of_eigen_half {c y : J} (h : c * y = (2 : ℝ)⁻¹ • y) :
    peirceOne c y = 0 := by
  simp only [peirceOne_apply, h, mul_smul_comm']
  module

/-- `peirceOne` kills the `0`-eigenspace. -/
theorem peirceOne_of_eigen_zero {c y : J} (h : c * y = 0) : peirceOne c y = 0 := by
  simp only [peirceOne_apply, h, mul_zero]
  module

/-- `peirceHalf` kills the `1`-eigenspace. -/
theorem peirceHalf_of_eigen {c y : J} (h : c * y = y) : peirceHalf c y = 0 := by
  simp only [peirceHalf_apply, h]
  module

/-- On the `1/2`-eigenspace, `peirceHalf` is the identity. -/
theorem peirceHalf_of_eigen_half {c y : J} (h : c * y = (2 : ℝ)⁻¹ • y) :
    peirceHalf c y = y := by
  simp only [peirceHalf_apply, h, mul_smul_comm']
  module

/-- `peirceHalf` kills the `0`-eigenspace. -/
theorem peirceHalf_of_eigen_zero {c y : J} (h : c * y = 0) : peirceHalf c y = 0 := by
  simp only [peirceHalf_apply, h, mul_zero]
  module

end Projections

section Peirce

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
private theorem two_smul_eq_zero' {x : J} (h : (2 : ℕ) • x = 0) : x = 0 := by
  have h2 : (2 : ℝ) • x = 0 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact h
  simpa using h2

omit [IsScalarTower ℝ J J] in
/-- **The Peirce polynomial identity.** For an idempotent `c`,

  `2·L_c³ − 3·L_c² + L_c = 0`,   i.e.   `L_c (L_c − 1) (2L_c − 1) = 0`.

Everything else in this file is a consequence. The proof is `two_lin1_apply` at
`a := c`, `b := y`, argument `:= c`, and nothing more: the hypotheses are the Jordan
identity and `c ∘ c = c`. -/
theorem peirce_poly {c : J} (hc : c * c = c) (y : J) :
    (2 : ℕ) • (c * (c * (c * y))) + c * y = (3 : ℕ) • (c * (c * y)) := by
  have h := two_lin1_apply c y c
  simp only [hc, mul_comm y c, mul_comm (c * y) c] at h
  refine sub_eq_zero.mp (two_smul_eq_zero' ?_)
  rw [← h]
  abel

omit [IsScalarTower ℝ J J] in
/-- `peirce_poly` solved for the cube, over `ℝ` — the form every consumer below uses. -/
theorem peirce_cube {c : J} (hc : c * c = c) (y : J) :
    c * (c * (c * y)) = (3 / 2 : ℝ) • (c * (c * y)) - (2 : ℝ)⁻¹ • (c * y) := by
  have h := peirce_poly hc y
  have h2 : (2 : ℝ) • (c * (c * (c * y))) + c * y = (3 : ℝ) • (c * (c * y)) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  have h3 : (2 : ℝ) • (c * (c * (c * y))) = (3 : ℝ) • (c * (c * y)) - c * y :=
    eq_sub_of_add_eq h2
  calc c * (c * (c * y)) = (2 : ℝ)⁻¹ • ((2 : ℝ) • (c * (c * (c * y)))) := by module
    _ = (2 : ℝ)⁻¹ • ((3 : ℝ) • (c * (c * y)) - c * y) := by rw [h3]
    _ = (3 / 2 : ℝ) • (c * (c * y)) - (2 : ℝ)⁻¹ • (c * y) := by module

/-- The image of `peirceOne c` lies in the `1`-eigenspace of `L_c`. -/
theorem mul_peirceOne {c : J} (hc : c * c = c) (y : J) :
    c * peirceOne c y = peirceOne c y := by
  simp only [peirceOne_apply, mul_sub, mul_smul_comm', peirce_cube hc y]
  module

/-- The image of `peirceHalf c` lies in the `1/2`-eigenspace of `L_c`. -/
theorem mul_peirceHalf {c : J} (hc : c * c = c) (y : J) :
    c * peirceHalf c y = (2 : ℝ)⁻¹ • peirceHalf c y := by
  simp only [peirceHalf_apply, mul_sub, mul_smul_comm', peirce_cube hc y]
  module

/-- The image of `peirceZero c` lies in the `0`-eigenspace of `L_c`. -/
theorem mul_peirceZero {c : J} (hc : c * c = c) (y : J) : c * peirceZero c y = 0 := by
  simp only [peirceZero_apply, mul_add, mul_sub, mul_smul_comm', peirce_cube hc y]
  module

/-- **The Peirce decomposition, existence half.** Every element of a real commutative
Jordan algebra splits, relative to any idempotent `c`, into a part fixed by `L_c`, a part
halved by it, and a part killed by it. -/
theorem exists_peirce_decomposition {c : J} (hc : c * c = c) (y : J) :
    ∃ y₁ yₕ y₀ : J, c * y₁ = y₁ ∧ c * yₕ = (2 : ℝ)⁻¹ • yₕ ∧ c * y₀ = 0
      ∧ y = y₁ + yₕ + y₀ :=
  ⟨peirceOne c y, peirceHalf c y, peirceZero c y, mul_peirceOne hc y, mul_peirceHalf hc y,
    mul_peirceZero hc y, (peirce_add_add c y).symm⟩

omit [IsCommJordan J] in
/-- **The Peirce decomposition, uniqueness half.** A vanishing sum of Peirce components is
componentwise zero — so the decomposition of `exists_peirce_decomposition` is unique, and
`J = J₁(c) ⊕ J_{1/2}(c) ⊕ J₀(c)` is a genuine direct sum.

The proof needs no independence-of-eigenspaces import: applying the two projections
`peirceOne` and `peirceHalf` to the relation reads off two of the three components, and
the third follows by subtraction. -/
theorem peirce_eq_zero_of_add_eq_zero {c y₁ yₕ y₀ : J} (h₁ : c * y₁ = y₁)
    (hₕ : c * yₕ = (2 : ℝ)⁻¹ • yₕ) (h₀ : c * y₀ = 0) (h : y₁ + yₕ + y₀ = 0) :
    y₁ = 0 ∧ yₕ = 0 ∧ y₀ = 0 := by
  have e1 : y₁ = 0 := by
    have := congrArg (peirceOne c) h
    rwa [map_add, map_add, peirceOne_of_eigen h₁, peirceOne_of_eigen_half hₕ,
      peirceOne_of_eigen_zero h₀, add_zero, add_zero, map_zero] at this
  have eh : yₕ = 0 := by
    have := congrArg (peirceHalf c) h
    rwa [map_add, map_add, peirceHalf_of_eigen h₁, peirceHalf_of_eigen_half hₕ,
      peirceHalf_of_eigen_zero h₀, add_zero, zero_add, map_zero] at this
  refine ⟨e1, eh, ?_⟩
  rw [e1, eh, zero_add, zero_add] at h
  exact h

/-- **The eigenvalue trichotomy.** `L_c` has no eigenvalue outside `{0, 1/2, 1}`: the
Peirce polynomial annihilates it, and its roots are exactly those three.

★ Stated for a *nonzero* eigenvector, which is the whole content — the equation
`c ∘ y = μ • y` is satisfied by `y = 0` for every `μ`. -/
theorem eigenvalue_trichotomy {c : J} (hc : c * c = c) {y : J} (hy : y ≠ 0) {μ : ℝ}
    (h : c * y = μ • y) : μ = 0 ∨ μ = (2 : ℝ)⁻¹ ∨ μ = 1 := by
  have hp : peirceOne c y = (2 * μ * μ - μ) • y := by
    simp only [peirceOne_apply, h, mul_smul_comm', smul_smul]
    module
  have key := mul_peirceOne hc y
  rw [hp, mul_smul_comm', h, smul_smul] at key
  have hs : ((2 * μ * μ - μ) * μ - (2 * μ * μ - μ)) • y = 0 := by
    rw [sub_smul, key]
    exact sub_self _
  have hz : (2 * μ * μ - μ) * μ - (2 * μ * μ - μ) = 0 :=
    (smul_eq_zero.mp hs).resolve_right hy
  have hfac : μ * (2 * μ - 1) * (μ - 1) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hfac with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

end Peirce

end EuclideanJordan
