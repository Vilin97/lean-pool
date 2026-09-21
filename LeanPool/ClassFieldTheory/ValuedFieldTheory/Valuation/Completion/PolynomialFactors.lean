/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Adjoin.PowerBasis
/-!
# Irreducible factors as conjugacy classes of roots

This file records the algebraic source lemma underlying
the extension-factor correspondence.  Multiplicities are deliberately discarded: extensions of a
valuation correspond to the *distinct* irreducible factors over the
completion.
-/

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace ValuationTheory
namespace Completion

universe u v

/-- The canonical monic normalization of polynomial factors over a field.
The normalization instances for an arbitrary field require a decidable
equality; this definition installs the classical one internally instead of
exposing it as an assumption of the extension-factor correspondence. -/
noncomputable def polynomialNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) : Multiset F[X] := by
  letI : DecidableEq F := Classical.decEq F
  letI : NormalizationMonoid F := inferInstance
  letI : NormalizationMonoid F[X] := Polynomial.instNormalizationMonoid
  exact normalizedFactors p

/-- The finite set underlying `polynomialNormalizedFactors`, with repeated
factors removed. -/
noncomputable def polynomialDistinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) : Finset F[X] := by
  classical
  exact (polynomialNormalizedFactors p).toFinset

/-- Associated polynomials have the same multiset of normalized irreducible factors. -/
theorem polynomialNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialNormalizedFactors p = polynomialNormalizedFactors q := by
  classical
  dsimp [polynomialNormalizedFactors]
  exact h.normalizedFactors_eq

/-- Associated polynomials have the same set of distinct normalized factors. -/
theorem polynomialDistinctNormalizedFactors_eq_of_associated
    {F : Type u} [Field F] {p q : F[X]} (h : Associated p q) :
    polynomialDistinctNormalizedFactors p =
      polynomialDistinctNormalizedFactors q := by
  classical
  dsimp [polynomialDistinctNormalizedFactors]
  rw [polynomialNormalizedFactors_eq_of_associated h]

/-- The distinct normalized irreducible factors of a nonzero polynomial.
Using `toFinset` removes the multiplicities retained by `normalizedFactors`.
-/
abbrev DistinctNormalizedFactors
    {F : Type u} [Field F] (p : F[X]) :=
  {g : F[X] // g ∈ polynomialDistinctNormalizedFactors p}

/-- The roots in `E` of a polynomial over the base field `F`. -/
abbrev PolynomialRootsIn
    {F : Type u} [Field F] (E : Type v) [Field E] [Algebra F E]
    (p : F[X]) :=
  {x : E // x ∈ p.rootSet E}

/-- Send a root to its monic minimal polynomial over the base field. -/
def rootMinpoly
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    (p : F[X]) : PolynomialRootsIn E p → F[X] :=
  fun x => minpoly F (x : E)

/-- Equality of the minimal polynomials of two roots.  Over a normal closure,
this is equivalently conjugacy under the absolute Galois group. -/
abbrev rootMinpolySetoid
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    (p : F[X]) : Setoid (PolynomialRootsIn E p) :=
  Setoid.ker (rootMinpoly p)

/-- The minimal polynomial of a root occurs among the normalized factors of the polynomial. -/
theorem rootMinpoly_mem_normalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] {p : F[X]} (hp : p ≠ 0)
    (x : PolynomialRootsIn E p) :
    rootMinpoly p x ∈ polynomialDistinctNormalizedFactors p := by
  classical
  dsimp [polynomialDistinctNormalizedFactors, polynomialNormalizedFactors]
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hp]
  have hxint : IsIntegral F (x : E) :=
    (Algebra.IsAlgebraic.isAlgebraic (x : E)).isIntegral
  refine ⟨minpoly.irreducible hxint, minpoly.monic hxint, ?_⟩
  exact minpoly.dvd F (x : E) (Polynomial.mem_rootSet.mp x.2).2

/-- Minimal polynomials of roots exhaust the distinct normalized factors. -/
theorem range_rootMinpoly_eq_distinctNormalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed E]
    {p : F[X]} (hp : p ≠ 0) :
    Set.range (rootMinpoly p : PolynomialRootsIn E p → F[X]) =
      {g : F[X] | g ∈ polynomialDistinctNormalizedFactors p} := by
  classical
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact rootMinpoly_mem_normalizedFactors hp x
  · intro hg
    have hg' : g ∈ normalizedFactors p := by
      simpa only [polynomialDistinctNormalizedFactors,
        polynomialNormalizedFactors, Multiset.mem_toFinset, Set.mem_ofPred_eq] using hg
    obtain ⟨hgirred, hgmonic, hgdvd⟩ :=
      (Polynomial.mem_normalizedFactors_iff hp).mp hg'
    have hgdegree : g.degree ≠ 0 :=
      (degree_pos_of_irreducible hgirred).ne'
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E g hgdegree
    have hxp : Polynomial.aeval x p = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero hgdvd hx
    have hxroot : x ∈ p.rootSet E := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hp, hxp⟩
    refine ⟨⟨x, hxroot⟩, ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hgirred hx hgmonic).symm

/-- Conjugacy classes of roots of `p` are in canonical bijection with the
distinct normalized irreducible factors of `p`. -/
noncomputable def rootClassesEquivDistinctNormalizedFactors
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed E]
    {p : F[X]} (hp : p ≠ 0) :
    Quotient (rootMinpolySetoid (E := E) p) ≃
      DistinctNormalizedFactors p :=
  (Setoid.quotientKerEquivRange (rootMinpoly p)).trans
    (Set.equivOfEq (range_rootMinpoly_eq_distinctNormalizedFactors hp))

/-- Two roots are equivalent precisely when they are conjugate roots. -/
theorem rootMinpolySetoid_rel_iff_isConjRoot
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {p : F[X]} (x y : PolynomialRootsIn E p) :
    (rootMinpolySetoid p).r x y ↔ IsConjRoot F (x : E) (y : E) :=
  Iff.rfl

/-- Minimal-polynomial equivalence of roots agrees with the Galois orbit relation. -/
theorem rootMinpolySetoid_rel_iff_orbitRel
    {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    [Normal F E] {p : F[X]} (x y : PolynomialRootsIn E p) :
    (rootMinpolySetoid p).r x y ↔
      MulAction.orbitRel Gal(E / F) E (x : E) (y : E) := by
  exact isConjRoot_iff_orbitRel

/-- For a simple finite extension `L = K(α)`, `K`-embeddings into an
extension of `K'` are the roots, in that extension, of the minimal polynomial
of `α` after base change from `K` to `K'`. -/
noncomputable def simpleEmbeddingsEquivMappedMinpolyRoots
    {K : Type u} {L : Type v} {K' E : Type*}
    [Field K] [Field L] [Field K'] [Field E]
    [Algebra K L] [Algebra K K'] [Algebra K E] [Algebra K' E]
    [IsScalarTower K K' E]
    (α : L) (hα : IsIntegral K α)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤) :
    (L →ₐ[K] E) ≃
      PolynomialRootsIn E
        ((minpoly K α).map (algebraMap K K')) := by
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hα hgen
  let p : K'[X] := (minpoly K α).map (algebraMap K K')
  have hpbgen : pb.gen = α := by simp [pb]
  have hp : p ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K K').injective).2
      (minpoly.ne_zero hα)
  have hroot (τ : L →ₐ[K] E) : τ α ∈ p.rootSet E := by
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    change Polynomial.aeval (τ α)
      ((minpoly K α).map (algebraMap K K')) = 0
    rw [aeval_map_algebraMap]
    rw [aeval_algHom_apply τ α (minpoly K α), minpoly.aeval, map_zero]
  have hbaseRoot (x : PolynomialRootsIn E p) :
      Polynomial.aeval (x : E) (minpoly K pb.gen) = 0 := by
    rw [hpbgen]
    exact (Polynomial.aeval_map_algebraMap K' (x : E) (minpoly K α)).symm.trans
      (Polynomial.mem_rootSet.mp x.2).2
  let toRoot : (L →ₐ[K] E) → PolynomialRootsIn E p :=
    fun τ => ⟨τ α, hroot τ⟩
  let fromRoot : PolynomialRootsIn E p → (L →ₐ[K] E) :=
    fun x => pb.lift (x : E) (hbaseRoot x)
  refine
    { toFun := toRoot
      invFun := fromRoot
      left_inv := ?_
      right_inv := ?_ }
  · intro τ
    apply pb.algHom_ext
    change pb.lift (τ α) _ pb.gen = τ pb.gen
    rw [pb.lift_gen, hpbgen]
  · intro x
    apply Subtype.ext
    change pb.lift (x : E) _ α = x
    calc
      pb.lift (x : E) _ α = pb.lift (x : E) _ pb.gen :=
        congrArg (pb.lift (x : E) (hbaseRoot x)) hpbgen.symm
      _ = x := pb.lift_gen (x : E) (hbaseRoot x)

end Completion
end ValuationTheory

end
