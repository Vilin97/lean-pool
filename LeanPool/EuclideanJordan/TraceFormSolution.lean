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
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import LeanPool.EuclideanJordan.EuclideanJordan.TraceForm

/-!
# Solution: the Jordan trace form

Repeats the definitions and the four statements of `TraceFormChallenge.lean` verbatim and
discharges them from `EuclideanJordan/TraceForm.lean`.

The definitions here are syntactic copies of the library's `EuclideanJordan.mulL`,
`EuclideanJordan.mulLₗ`, `EuclideanJordan.jtr` and `EuclideanJordan.traceForm`, so they are
definitionally equal to them (the proof fields differ only up to proof irrelevance) and each
bridge is the library theorem applied on the nose.

The one piece of real work is formal reality. The challenge states it as a hypothesis over
`Fin k`, the shape `SpectralChallenge.lean` uses, while the library's
`EuclideanJordan.IsFormallyReal` is a class quantifying over an arbitrary `Finset`. The two differ
only by reindexing along `Finset.equivFin`, done inline in each of the two positivity proofs.
-/

namespace JordanTraceForm

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]

/-- In a *commutative* algebra the scalar-tower rule `(r • a) * b = r • (a * b)` already gives
the `SMulCommClass` rule on the other side, so only `IsScalarTower ℝ J J` has to be assumed. -/
theorem mul_smul_comm' (r : ℝ) (a b : J) : a * (r • b) = r • (a * b) := by
  rw [mul_comm, smul_mul_assoc, mul_comm]

/-- **The Jordan multiplication operator** `L_c : y ↦ c * y`, as an `ℝ`-linear map. Its
`ℝ`-linearity is exactly what the scalar tower buys, and it is what makes `L_c` traceable. -/
def mulL (c : J) : J →ₗ[ℝ] J where
  toFun y := c * y
  map_add' := mul_add c
  map_smul' r y := mul_smul_comm' r c y

@[simp] theorem mulL_apply (c y : J) : mulL c y = c * y := rfl

/-- `L_·` bundled as a linear map in the multiplier, which is what makes `jtr` linear. -/
def mulLₗ : J →ₗ[ℝ] J →ₗ[ℝ] J where
  toFun := mulL
  map_add' a b := by ext y; simp only [mulL_apply, LinearMap.add_apply, add_mul]
  map_smul' r a := by
    ext y
    simp only [mulL_apply, LinearMap.smul_apply, RingHom.id_apply, smul_mul_assoc]

@[simp] theorem mulLₗ_apply (a : J) : mulLₗ a = mulL a := rfl

/-- **The Jordan trace functional** `x ↦ tr(L_x)`, as an `ℝ`-linear form. Not normalised: see
the module docstring. -/
noncomputable def jtr : J →ₗ[ℝ] ℝ := (LinearMap.trace ℝ J).comp mulLₗ

@[simp] theorem jtr_apply (x : J) : jtr x = LinearMap.trace ℝ J (mulL x) := rfl

/-- **The Jordan trace form** `τ(x, y) = tr(L_{x * y})`, bundled as an `ℝ`-bilinear form.

Bilinearity is not a theorem below because it is the *type*: the four `mk₂` fields are additivity
and homogeneity in each argument, and they are immediate from linearity of `jtr` and
bilinearity of the product. -/
noncomputable def traceForm : J →ₗ[ℝ] J →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => jtr (x * y))
    (fun x x' y => by rw [add_mul, map_add])
    (fun r x y => by rw [smul_mul_assoc, map_smul, smul_eq_mul])
    (fun x y y' => by rw [mul_add, map_add])
    (fun r x y => by rw [mul_smul_comm' r x y, map_smul, smul_eq_mul])

@[simp] theorem traceForm_apply (x y : J) : traceForm x y = jtr (x * y) := rfl

/-- **The trace form is symmetric**: `τ(x, y) = τ(y, x)`.

No Jordan identity, no finite dimension, no formal reality: this is commutativity of the product
underneath `jtr`, and it is registered at that generality deliberately. -/
theorem traceForm_comm (x y : J) : traceForm x y = traceForm y x :=
  EuclideanJordan.traceForm_comm x y

/-- **The trace form is associative**: `τ(x * y, z) = τ(y, x * z)`.

This is the compatibility that the standard presentation of a Euclidean Jordan algebra *assumes*
of its inner product, here proved of a form manufactured from the multiplication alone. It is the
main theorem of this file.

Note the hypotheses, which are weaker than one expects. Beyond the commutative product and the
`ℝ`-module structure only `IsCommJordan` — the Jordan identity — is assumed: **no finite
dimension, no formal reality, no unit, no positivity, no idempotents, no spectral theory.**
`LinearMap.trace` is total, so the statement is meaningful (and true) even when `J` has no finite
basis and every trace in sight is `0`. -/
theorem traceForm_assoc [IsCommJordan J] (x y z : J) :
    traceForm (x * y) z = traceForm y (x * z) :=
  EuclideanJordan.traceForm_assoc x y z

/-- **The trace form is positive semidefinite**: `τ(x, x) ≥ 0`.

`hfr` is formal reality: a vanishing sum of squares has vanishing summands. With
`Module.Finite ℝ J` it yields a spectral resolution `x = ∑ᵢ λᵢ qᵢ` into orthogonal idempotents,
whence `x * x = ∑ᵢ λᵢ² qᵢ` and `τ(x, x) = ∑ᵢ λᵢ² tr(L_{qᵢ})`; and for an idempotent `c` the Peirce
split `L_c = P₁(c) + ½ P_{1/2}(c)` writes `tr(L_c)` as a nonnegative combination of traces of
idempotent endomorphisms, which are the ranks of their ranges.

Formal reality is essential: `ℂ` over `ℝ` is a finite-dimensional commutative associative Jordan
algebra with `τ(i, i) = -2`. See the module docstring, which is also honest about the weaker
role `Module.Finite ℝ J` plays in this particular statement. -/
theorem traceForm_self_nonneg [IsCommJordan J] [Module.Finite ℝ J]
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, f i * f i) = 0 → ∀ i, f i = 0) (x : J) :
    0 ≤ traceForm x x := by
  have : EuclideanJordan.IsFormallyReal J := by
    classical
    refine ⟨fun {ι} s f hsum i hi => ?_⟩
    have key : (∑ k : Fin s.card, f (s.equivFin.symm k) * f (s.equivFin.symm k)) = 0 := by
      rw [show (∑ k : Fin s.card, f (s.equivFin.symm k) * f (s.equivFin.symm k))
          = ∑ a : {y // y ∈ s}, f a * f a from
        Equiv.sum_comp s.equivFin.symm (fun a : {y // y ∈ s} => f a * f a),
        Finset.sum_coe_sort s (fun a => f a * f a)]
      exact hsum
    simpa using hfr s.card (fun k => f (s.equivFin.symm k)) key (s.equivFin ⟨i, hi⟩)
  exact EuclideanJordan.traceForm_self_nonneg x

/-- **The trace form is definite**: `τ(x, x) = 0 ↔ x = 0`.

Together with `traceForm_comm`, `traceForm_assoc` and `traceForm_self_nonneg` this is the whole
of the assertion that `τ` is a symmetric associative positive definite bilinear form — the
Euclidean form supplied by the multiplication itself. It is only the form: unitality, which a
Euclidean Jordan algebra also requires, is neither assumed nor concluded here.

The nontrivial direction is `→`. It rests on a sharpening of the estimate behind
`traceForm_self_nonneg`: for a **nonzero** idempotent `c` one has `tr(L_c) ≥ 1`, because
`P₁(c) c = c` makes the range of the Peirce projection `P₁(c)` nonzero, hence of rank at least
one. So a vanishing `∑ᵢ λᵢ² tr(L_{qᵢ})` kills every `λᵢ` whose idempotent is nonzero, and the
terms with `qᵢ = 0` contribute nothing to `x` anyway. -/
theorem traceForm_self_eq_zero_iff [IsCommJordan J] [Module.Finite ℝ J]
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, f i * f i) = 0 → ∀ i, f i = 0) (x : J) :
    traceForm x x = 0 ↔ x = 0 := by
  have : EuclideanJordan.IsFormallyReal J := by
    classical
    refine ⟨fun {ι} s f hsum i hi => ?_⟩
    have key : (∑ k : Fin s.card, f (s.equivFin.symm k) * f (s.equivFin.symm k)) = 0 := by
      rw [show (∑ k : Fin s.card, f (s.equivFin.symm k) * f (s.equivFin.symm k))
          = ∑ a : {y // y ∈ s}, f a * f a from
        Equiv.sum_comp s.equivFin.symm (fun a : {y // y ∈ s} => f a * f a),
        Finset.sum_coe_sort s (fun a => f a * f a)]
      exact hsum
    simpa using hfr s.card (fun k => f (s.equivFin.symm k)) key (s.equivFin ⟨i, hi⟩)
  exact EuclideanJordan.traceForm_self_eq_zero_iff x

end JordanTraceForm
