/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Schur Product Theorem

Proves the Schur product theorem (real, finite-index case): if `A` and `B` are positive
semidefinite Hermitian matrices, then their entrywise (Hadamard) product `D` with entries
`D i j = A i j * B i j` is also positive semidefinite. The proof reduces positivity of the
Hadamard form `x ᵀ (A ∘ B) x` to positivity of the Kronecker product `A ⊗ B` applied to
the diagonal embedding of `x` into `ι × ι`. Used in the OS3 reflection positivity argument
to transfer PSD properties through the matrix exponential via `HadamardExp.lean`.
-/


open scoped BigOperators
open scoped Kronecker

namespace OSforGFF

universe u

variable {ι : Type u}

/-- Notation alias for the Hadamard (entrywise) product from Mathlib. -/
notation:100 A "∘ₕ" B => Matrix.hadamard A B

/-- Auxiliary: diagonal embedding of a vector `x : ι → ℝ` into `ι×ι` used for the restriction
argument: only the diagonal entries are nonzero and equal to `x`.
-/
@[simp] noncomputable def diagEmbed (x : ι → ℝ) : ι × ι → ℝ := by
  classical
  exact fun p => if p.2 = p.1 then x p.1 else 0

lemma diagEmbed_ne_zero_of_ne_zero {x : ι → ℝ} (hx : x ≠ 0) : diagEmbed (ι:=ι) x ≠ 0 := by
  classical
  -- If diagEmbed x = 0 then all diagonal entries vanish, hence x = 0, contradiction.
  intro h
  apply hx
  funext i
  have := congrArg (fun f => f (i, i)) h
  simpa [diagEmbed] using this

/-- Finite sum over pairs equals iterated double sum over coordinates (binderless sums). -/
lemma sum_pairs_eq_double [Fintype ι] (g : ι × ι → ℝ) :
  (∑ p, g p) = ∑ i, ∑ j, g (i, j) := Fintype.sum_prod_type g

/-- Over `ℝ`, the Hadamard product of Hermitian matrices is Hermitian. -/
private lemma isHermitian_hadamard_real {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ∘ₕ B).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have hAij : A i j = A j i := by simpa using (Matrix.IsHermitian.apply hA i j).symm
  have hBij : B i j = B j i := by simpa using (Matrix.IsHermitian.apply hB i j).symm
  simp [Matrix.conjTranspose, Matrix.hadamard, hAij, hBij]

/-- Schur product theorem (real case, finite index):
If A B are positive definite matrices over ℝ, then the Hadamard product is positive definite.
-/
@[simp] theorem schur_product_posDef
  [Finite ι] (A B : Matrix ι ι ℝ)
  (hA : A.PosDef) (hB : B.PosDef) :
  (A ∘ₕ B).PosDef := by
  classical
  letI := Fintype.ofFinite ι
  -- Use the characterization via dotProduct_mulVec
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact isHermitian_hadamard_real (ι:=ι) hA.isHermitian hB.isHermitian
  · -- Positivity: diagonal restriction of the Kronecker form
    intro x hx
    -- Define diagonal embedding y from x
    let y : ι × ι → ℝ := diagEmbed (ι:=ι) x
    have hy : y ≠ 0 := diagEmbed_ne_zero_of_ne_zero (ι:=ι) hx
    -- Built-in Kronecker product is PosDef
    have hk : 0 < y ⬝ᵥ (A ⊗ₖ B).mulVec y :=
      (Matrix.PosDef.kronecker hA hB).dotProduct_mulVec_pos hy
    -- The quadratic forms coincide on diagonal-embedded vectors
    have hquad_eq : y ⬝ᵥ (A ⊗ₖ B).mulVec y = x ⬝ᵥ (A ∘ₕ B).mulVec x := by
      classical
      -- expand LHS to sums over pairs
      calc
        y ⬝ᵥ (A ⊗ₖ B).mulVec y
            = ∑ p, y p * ((A ⊗ₖ B).mulVec y) p := by
              simp [dotProduct]
        _ = ∑ i, ∑ j, y (i, j) * ((A ⊗ₖ B).mulVec y) (i, j) := by
              exact sum_pairs_eq_double (fun p => y p * ((A ⊗ₖ B).mulVec y p))
        _ = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) := by
              apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
              congr 1
              calc
                ((A ⊗ₖ B).mulVec y) (i, j)
                    = ∑ q, ((A ⊗ₖ B) (i, j) q) * y q := by
                        simp [Matrix.mulVec, dotProduct]
                _ = ∑ q, (A i q.1 * B j q.2) * y q := by
                        rfl
                _ = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
                        simpa using
                          (sum_pairs_eq_double (fun q => (A i q.1 * B j q.2) * y q))
        _ = ∑ i, ∑ k, x i * ((A i k * B i k) * x k) := by
              -- Kill off-diagonal terms using diagEmbed definition
              simp [y, diagEmbed, Finset.mul_sum, eq_comm]
        _ = x ⬝ᵥ (A ∘ₕ B).mulVec x := by
              -- expand RHS: Hadamard mulVec then dot
              simp [dotProduct, Matrix.mulVec, Matrix.hadamard, Finset.mul_sum, mul_comm,
                mul_left_comm]
    -- transport positivity
    simpa [hquad_eq] using hk

end OSforGFF
