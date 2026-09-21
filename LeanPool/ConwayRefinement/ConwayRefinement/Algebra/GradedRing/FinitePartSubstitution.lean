/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartDecomposition


/-!
# Values of the cofactors in the successor step

The successor step writes a relation as `F = ∑_t (∂F/∂X_t)(X_t + V_t)` with each `V_t` homogeneous
of degree `wt t` and free of the variables carrying the finite part. What it then needs is that
each `V_t` evaluates into the square of the ideal of positive degree.

The reason is that a monomial of degree `wt t` free of those variables cannot be a single variable:
if it were, that variable would carry the whole finite part, which the freeness forbids. So every
monomial splits into two factors of nonzero degree, and their product is decomposable.

Only two properties of the generators are used, that each sits in its own degree and that no degree
is zero, so they are taken directly rather than through a minimal-system structure.
-/

universe u v w z

open scoped NatOrdinal

open MvPolynomial

public noncomputable section

namespace OrdinalGraded

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]
variable {A : NatOrdinal.{z} → Submodule K R} [GradedAlgebra A]
variable {ι : Type w} {wt : ι → NatOrdinal.{z}} {x : ι → R}

/-- Multiplying a decomposable element by a homogeneous one keeps it decomposable, at the sum of
the degrees. -/
theorem mul_mem_decomposableAt_of_mem_decomposableAt {g β : NatOrdinal.{z}} {z y : R}
    (hz : z ∈ decomposableAt A g) (hy : y ∈ A β) : z * y ∈ decomposableAt A (g + β) := by
  have hle : decomposableAt A g ≤
      (decomposableAt A (g + β)).comap (LinearMap.mulRight K y) := by
    refine decomposableAt_le A fun i j hi hj hij ↦ ?_
    rw [Submodule.mul_le]
    intro a ha b hb
    rw [Submodule.mem_comap, LinearMap.mulRight_apply, mul_assoc]
    have hjβ : j + β ≠ 0 := fun h ↦ hj (le_antisymm (h ▸ NatOrdinal.le_add_right) zero_le)
    rw [← hij, add_assoc]
    exact mul_mem_decomposableAt A hi hjβ ha (SetLike.mul_mem_graded hb hy)
  exact hle hz

/-- **A cofactor evaluates into the square of the ideal of positive degree.** A homogeneous
polynomial of degree `g` with finite part `n ≥ 1`, free of the variables carrying that finite part,
has no monomial equal to a single variable, so each of its monomials splits into two factors of
nonzero degree. -/
theorem aeval_mem_decomposableAt_of_mem_supported
    (hmem : ∀ i, x i ∈ A (wt i)) (hne : ∀ i, wt i ≠ 0)
    {V : MvPolynomial ι K} {g : NatOrdinal.{z}}
    (hg : 0 < g.constantCoeff) (hV : IsWeightedHomogeneous wt V g)
    (hsupp : V ∈ supported K {i | (wt i).constantCoeff ≠ g.constantCoeff}) :
    aeval x V ∈ decomposableAt A g := by
  classical
  rw [V.as_sum, map_sum]
  refine sum_mem fun d hd ↦ ?_
  have hwd : Finsupp.weight wt d = g := hV (mem_support_iff.mp hd)
  -- the monomial has a variable `i` not carrying the finite part, and is not `X_i` alone
  have hdne : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hwd
    rw [← hwd, NatOrdinal.constantCoeff_zero] at hg
    exact lt_irrefl _ hg
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hdne
  have hik : (wt i).constantCoeff ≠ g.constantCoeff :=
    (mem_supported.mp hsupp) ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)
  obtain ⟨d', hd'def⟩ : ∃ d', d' = d - Finsupp.single i 1 := ⟨_, rfl⟩
  have hsplit : Finsupp.weight wt d' + wt i = g := by
    rw [hd'def, Finsupp.weight_sub_single_add (w := wt) (Finsupp.mem_support_iff.mp hi), hwd]
  have hd'ne : d' ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_add] at hsplit
    exact hik (by rw [hsplit])
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hd'ne
  have hwd' : Finsupp.weight wt d' ≠ 0 := fun h ↦ by
    have hle := Finsupp.le_weight_of_mem_support wt d' hj
    rw [h] at hle
    exact hne j (le_antisymm hle zero_le)
  -- `X^d = X^{d'} * X_i`
  have hmono : monomial d (coeff d V) = C (coeff d V) * (monomial d' 1 * X i) := by
    rw [X, monomial_mul, mul_one, C_mul_monomial, mul_one, hd'def,
      Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)]
  rw [hmono, map_mul, map_mul, ← algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  refine Submodule.smul_mem _ _ ?_
  have h1 : aeval x (monomial d' (1 : K)) ∈ A (Finsupp.weight wt d') :=
    aeval_mem_of_forall_mem hmem (isWeightedHomogeneous_monomial wt d' 1 rfl)
  rw [aeval_X, ← hsplit]
  exact mul_mem_decomposableAt A hwd' (hne i) h1 (hmem i)

end OrdinalGraded

end
