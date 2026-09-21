/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.Faces
import LeanPool.ErdosGinzburgZiv.EGZ.Polynomial.HollowBound
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Bounding hollow rational polytopes

This module isolates the exact bridge from Proposition `wl` to boundedness of
the vertex counts defining `hollowPolytopeNumber`.  It also develops the
Smith-normal-form saturation lemma needed to prove that bridge.
-/

open scoped BigOperators

namespace EGZ

/-- The weakest consequence of Proposition `wl` needed for bounding one
hollow polytope: its vertices have a `p`-hollow reduction for at least one
prime. -/
def RationalPolytope.HasPrimeHollowReduction {d : ℕ}
    (P : RationalPolytope d) : Prop :=
  ∃ p : ℕ, p.Prime ∧
    AdmitsPHollowLength p d P.vertexSet.ncard

/-- Dimensionwise form of the reduction bridge.  Proposition `wl` proves a
stronger eventual-prime statement, while this existential form is all that
the polynomial bound needs. -/
def HollowReductionBridge (d : ℕ) : Prop :=
  ∀ P : RationalPolytope d,
    P.IsHollow → P.HasPrimeHollowReduction

/-- Conditional global boundedness of hollow-polytope vertex counts.  The
bound is exactly the prime-independent polynomial bound. -/
theorem bddAbove_hollowPolytopeVertexCount_of_reductionBridge {d : ℕ}
    (hd : 1 ≤ d) (hbridge : HollowReductionBridge d) :
    BddAbove {n : ℕ | AdmitsHollowPolytopeVertexCount d n} := by
  refine ⟨(2 * d - 1).choose d + 1, ?_⟩
  rintro n ⟨P, hP, hn⟩
  obtain ⟨p, hp, v, hv⟩ := hbridge P hP
  calc
    n = P.vertexSet.ncard := hn.symm
    _ ≤ (2 * d - 1).choose d + 1 :=
      hv.card_le_choose_add_one hp hd

end EGZ

namespace Module.Basis.SmithNormalForm

/-- If a scalar is nonzero and coprime to every diagonal coefficient in a
Smith normal form for `N`, then membership in `N` can be cancelled across
multiplication by that scalar.  This is the algebraic core of the
"all but finitely many primes are good" step in Proposition `wl`. -/
theorem mem_of_smul_mem_of_isCoprime
    {M : Type*} [AddCommGroup M]
    {N : Submodule ℤ M} {ι : Type*} {r : ℕ}
    (snf : SmithNormalForm N ι r) (c : ℤ) (hc : c ≠ 0)
    (hcoprime : ∀ i, IsCoprime (snf.a i) c)
    {x : M} (hx : c • x ∈ N) : x ∈ N := by
  classical
  let m : N := ⟨c • x, hx⟩
  have hdiv (i : Fin r) : snf.a i ∣ snf.bM.repr x (snf.f i) := by
    apply (hcoprime i).dvd_of_dvd_mul_left
    refine ⟨snf.bN.repr m i, ?_⟩
    have hrepr := snf.repr_apply_embedding_eq_repr_smul m (i := i)
    simpa only [m, map_smul, Finsupp.smul_apply, smul_eq_mul] using hrepr
  choose k hk using hdiv
  rw [snf.bN.mem_submodule_iff']
  refine ⟨k, ?_⟩
  apply snf.bM.ext_elem
  intro j
  by_cases hj : j ∈ Set.range snf.f
  · obtain ⟨i, rfl⟩ := hj
    rw [hk i]
    simp only [map_sum, map_smul, snf.snf, ← mul_smul,
      snf.bM.repr_self]
    rw [Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro l _ hli
      have hne : snf.f l ≠ snf.f i := fun h ↦ hli (snf.f.injective h)
      simp [hne]
    · simp
  · have hzero : snf.bM.repr x j = 0 := by
      have hz := snf.repr_eq_zero_of_notMem_range m hj
      have hz' : c * snf.bM.repr x j = 0 := by
        simpa only [m, map_smul, Finsupp.smul_apply, smul_eq_mul] using hz
      exact mul_eq_zero.mp hz' |>.resolve_left hc
    rw [hzero]
    simp only [map_sum, map_smul, snf.snf, ← mul_smul, snf.bM.repr_self]
    rw [Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : snf.f i ≠ j := fun h ↦ hj ⟨i, h⟩
    simp [hne]

/-- Every diagonal coefficient in a Smith normal form is nonzero. -/
theorem coeff_ne_zero
    {M : Type*} [AddCommGroup M]
    {N : Submodule ℤ M} {ι : Type*} {r : ℕ}
    (snf : SmithNormalForm N ι r) (i : Fin r) : snf.a i ≠ 0 := by
  intro hi
  apply snf.bN.ne_zero i
  ext
  simp [snf.snf, hi]

end Module.Basis.SmithNormalForm

namespace Submodule

/-- A submodule of a finite free abelian group is saturated with respect to
every sufficiently large prime.  The bound is the maximum absolute value of
the diagonal entries in a Smith normal form. -/
theorem exists_prime_saturation_bound
    {M : Type*} [AddCommGroup M] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ M) (N : Submodule ℤ M) :
    ∃ B : ℕ, ∀ {p : ℕ}, p.Prime → B < p →
      ∀ {x : M}, (p : ℤ) • x ∈ N → x ∈ N := by
  classical
  let ⟨r, snf⟩ := N.smithNormalForm b
  refine ⟨Finset.univ.sup (fun i : Fin r ↦ (snf.a i).natAbs), ?_⟩
  intro p hp hBp x hx
  apply snf.mem_of_smul_mem_of_isCoprime (p : ℤ)
    (Int.ofNat_ne_zero.mpr hp.ne_zero) _ hx
  intro i
  apply ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  have hnat : p ∣ (snf.a i).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hdvd)
  have hle : p ≤ (snf.a i).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (snf.coeff_ne_zero i)) hnat
  have haiBound : (snf.a i).natAbs ≤
      Finset.univ.sup (fun i : Fin r ↦ (snf.a i).natAbs) :=
    Finset.le_sup (s := Finset.univ) (f := fun i : Fin r ↦ (snf.a i).natAbs)
      (Finset.mem_univ i)
  exact (not_le_of_gt hBp) (hle.trans haiBound)

/-- A single threshold works simultaneously for a finite indexed family of
integer submodules.  This is the facewise `p`-saturation package needed after
assigning one homogenized lattice to every face of a polytope. -/
theorem exists_uniform_prime_saturation_bound
    {α M : Type*} [AddCommGroup M] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ M) (s : Finset α) (L : α → Submodule ℤ M) :
    ∃ B : ℕ, ∀ {p : ℕ}, p.Prime → B < p →
      ∀ a ∈ s, ∀ {x : M}, (p : ℤ) • x ∈ L a → x ∈ L a := by
  classical
  choose bound hbound using fun a ↦ (L a).exists_prime_saturation_bound b
  refine ⟨s.sup bound, ?_⟩
  intro p hp hBp a ha x hx
  exact hbound a hp (lt_of_le_of_lt (Finset.le_sup ha) hBp) hx

/-- Equivalent finite-bad-prime form of
`exists_uniform_prime_saturation_bound`. -/
theorem exists_finite_exceptional_primes
    {α M : Type*} [AddCommGroup M] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ M) (s : Finset α) (L : α → Submodule ℤ M) :
    ∃ bad : Finset ℕ, ∀ {p : ℕ}, p.Prime → p ∉ bad →
      ∀ a ∈ s, ∀ {x : M}, (p : ℤ) • x ∈ L a → x ∈ L a := by
  obtain ⟨B, hB⟩ := exists_uniform_prime_saturation_bound b s L
  refine ⟨Finset.range (B + 1), ?_⟩
  intro p hp hpbad
  apply hB hp
  apply Nat.lt_of_add_one_le
  simpa only [Finset.mem_range, not_lt] using hpbad

end Submodule
