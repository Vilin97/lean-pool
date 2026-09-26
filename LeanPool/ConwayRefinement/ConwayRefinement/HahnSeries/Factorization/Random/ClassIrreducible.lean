/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.SuccessorStep
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.PrincipalIrreducible
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.OrdinalValueDegree

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.AssociatedGradedDivisibility

/-!
# Irreducible classes in $\widehat{\mathrm P}$

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Corollary 4.5, first clause, for `α = n < ω`: if `b ∈ P_n` is hereditarily `rv_J`-independent,
then `rv(b)` is irreducible. The class `rv(b)` is `rv_J(b) ∈ P_n ⊆ P̂`, and the statement is
irreducibility in `P̂`.

The argument is the one of the source's proof: a factorisation `rv_J(b) = X · Y` in `P̂` has
homogeneous factors, because `P̂` is a graded domain (Berarducci, Theorem 9.7); if both factors
have positive grade, `rv_J(b)` lies in the span `D_n` of such products, which `(*)_n` excludes
for a hereditarily `rv_J`-independent `b`; and a nonzero class of grade zero is a unit.
-/

open scoped DirectSum HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K] [CharZero K]

/-- A nonzero class of positive grade `n` outside `D_n` is irreducible in `P̂`. -/
theorem irreducible_of_notMem_decomposableSpan {n : NatOrdinal} (hn : 0 < n)
    {x : PrincipalComponent K n} (hx : x ≠ 0)
    (hmem : DirectSum.of (PrincipalComponent K) n x ∉ decomposableSpan K n) :
    Irreducible (DirectSum.of (PrincipalComponent K) n x) := by
  refine ⟨not_isUnit_of_grade_ne_zero hn.ne' x, fun A C hAC ↦ ?_⟩
  have hne : DirectSum.of (PrincipalComponent K) n x ≠ 0 := fun h ↦
    hx (DirectSum.of_injective n (by rw [h, map_zero]))
  have hA : A ≠ 0 := fun h ↦ hne (by rw [hAC, h, zero_mul])
  have hC : C ≠ 0 := fun h ↦ hne (by rw [hAC, h, mul_zero])
  have hhom : A * C ∈ (ordinalValueDegreeValuation K).homogeneousClasses := by
    rw [← hAC, MaxAddDegree.mem_homogeneousClasses_iff]
    exact Or.inr ⟨n, x, rfl⟩
  obtain ⟨hAhom, hChom⟩ :=
    (ordinalValueDegreeValuation K).mem_homogeneousClasses_of_mul_mem hA hC hhom
  rcases (MaxAddDegree.mem_homogeneousClasses_iff _ A).mp hAhom with rfl | ⟨β, y, rfl⟩
  · exact absurd rfl hA
  rcases (MaxAddDegree.mem_homogeneousClasses_iff _ C).mp hChom with rfl | ⟨γ, z, rfl⟩
  · exact absurd rfl hC
  have hy : y ≠ 0 := fun h ↦ hA (by rw [h, map_zero])
  have hz : z ≠ 0 := fun h ↦ hC (by rw [h, map_zero])
  -- The product of the homogeneous factors sits in grade `β + γ`, which must be `n`.
  have hgrade : n = β + γ := by
    by_contra hne'
    have hcomp := congrArg (fun w : PrincipalSubring K ↦ w (β + γ)) hAC
    simp only [DirectSum.of_mul_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne'),
      DirectSum.of_eq_same] at hcomp
    exact MaxAddDegree.componentMul_ne_zero (ordinalValueDegreeValuation K) y z hy hz hcomp.symm
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    exact Or.inl (isUnit_of_grade_zero y hy)
  rcases eq_or_ne γ 0 with hγ | hγ
  · subst hγ
    exact Or.inr (isUnit_of_grade_zero z hz)
  exfalso
  apply hmem
  rw [hAC, hgrade]
  exact of_mul_of_mem_decomposableSpan (pos_iff_ne_zero.mpr hβ) (pos_iff_ne_zero.mpr hγ) y z

/-- FLLM24, Corollary 4.5 (first clause) for `α = n ≥ 1`: the class `rv_J(b)` of a hereditarily
`rv_J`-independent series of ordinal-value degree `n` is irreducible in `P̂`. -/
theorem irreducible_rvJ_of_hereditarilyRVIndependent {n : ℕ} (hn : 1 ≤ n) {b : Series K}
    (hb : HereditarilyRVIndependent n (fun _ : Unit ↦ b)) : Irreducible (rvJ b) := by
  have hval : ordinalValue b = ω^ (n : NatOrdinal) := hb.ordinalValue_eq ()
  have hmem := rvJ_notMem_decomposableSpan (independentModuloDecomposable_of_pos hn) hb
  have hcut : ordinalValue b < ω^ ((n : NatOrdinal) + 1) := by
    rw [hval]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _)
  rw [rvJ_eq_gradeClass hval, gradeClass_of_lt hcut] at hmem ⊢
  refine irreducible_of_notMem_decomposableSpan (Nat.cast_pos.mpr hn) ?_ hmem
  rw [Ne, principalComponentMk_eq_zero_iff, hval]
  exact lt_irrefl _

end FLLM24

end
