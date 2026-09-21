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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import LeanPool.EuclideanJordan.EuclideanJordan.Spectral

/-!
# Solution: the single-element spectral theorem for a Euclidean Jordan algebra

Repeats the statement of `SpectralChallenge.lean` verbatim and discharges it from
`EuclideanJordan.spectral_resolution_bilinear` in `EuclideanJordan/Spectral.lean`.

The delegation is a single application because the library theorem is stated in exactly this
vocabulary: the product enters as a bundled bilinear map, so no Jordan-algebra instance has to
exist before the statement elaborates. The instances the proof needs (a non-unital commutative
ring on `J`, `IsCommJordan`, `IsScalarTower ℝ J J`, `IsFormallyReal J`) are built inside the
library from `m`, `hcomm`, `hjordan` and `hfr`, and none of them escapes into the statement.
-/

namespace JordanSpectral

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- **The single-element spectral theorem for a Euclidean Jordan algebra.**

Let `J` be a finite-dimensional real vector space and `m : J →ₗ[ℝ] J →ₗ[ℝ] J` a bilinear
product on it which is commutative (`hcomm`), satisfies the Jordan identity (`hjordan`), is
formally real (`hfr` : a vanishing sum of squares has vanishing summands), and has a unit `e`
(`he`). Then every `x : J` admits a **spectral resolution**: a finite family of idempotents
`q i` for `m`, pairwise orthogonal, summing to the unit, with `x` a real combination of them.

This is Theorem III.1.1 of J. Faraut and A. Koranyi, *Analysis on Symmetric Cones*, Oxford
University Press (1994); the underlying classification is P. Jordan, J. von Neumann and
E. Wigner, *On an algebraic generalization of the quantum mechanical formalism*, Ann. of Math.
35 (1934) 29-64.

Everything the statement mentions is Mathlib: bilinear maps, `Finset.sum` over `Fin n`, real
scalar multiplication. In particular "idempotent", "orthogonal" and "complete" are written out
inline as `m (q i) (q i) = q i`, `i ≠ j → m (q i) (q j) = 0`, and `∑ i, q i = e`.

What is and is not assumed. No associativity, no power-associativity, no positivity of the
inner product against `m` (indeed no hypothesis at all connects `m` to `⟪·, ·⟫`), no ordering, no
trace, no Peirce decomposition, no simplicity. Finite-dimensionality is essential: `ℝ[X]` under
polynomial multiplication satisfies every other hypothesis and has only the idempotents `0` and
`1`. -/
theorem spectral_resolution_bilinear [FiniteDimensional ℝ J] (m : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, m (f i) (f i)) = 0 → ∀ i, f i = 0)
    (e : J) (he : ∀ y : J, m e y = y) (x : J) :
    ∃ (n : ℕ) (q : Fin n → J) (lam : Fin n → ℝ),
      (∀ i, m (q i) (q i) = q i) ∧
      (∀ i j, i ≠ j → m (q i) (q j) = 0) ∧
      (∑ i, q i) = e ∧
      x = ∑ i, lam i • q i :=
  EuclideanJordan.spectral_resolution_bilinear m hcomm hjordan hfr e he x

end JordanSpectral
