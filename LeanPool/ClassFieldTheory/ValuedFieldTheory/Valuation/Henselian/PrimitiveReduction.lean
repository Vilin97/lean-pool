/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Core
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.ContentIdeal
/-!
# Primitive polynomials detected by reduction

The construction calls a polynomial over a valuation ring primitive when its
reduction modulo the maximal ideal is nonzero.  The lemma below identifies
that condition with the divisibility notion used by mathlib's Gauss lemma.
-/

@[expose] public section

noncomputable
section

open Polynomial
open UniqueFactorizationMonoid

namespace DiscreteValuationField

/-- Over a local ring, a polynomial whose residue is nonzero is primitive in
the Gauss-lemma sense: every constant divisor is a unit. -/
theorem polynomial_isPrimitive_of_residue_ne_zero
    {R : Type*} [CommRing R] [IsLocalRing R]
    {f : Polynomial R}
    (hf : f.map (IsLocalRing.residue R) ≠ 0) :
    f.IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  apply (IsLocalRing.residue_ne_zero_iff_isUnit r).mp
  intro hrzero
  rcases hr with ⟨q, hq⟩
  apply hf
  rw [hq, Polynomial.map_mul]
  simp [hrzero]

/-- A primitive polynomial over a valuation subring has a unit coefficient.
The proof chooses a coefficient of maximal valuation; it divides every other
coefficient, so primitivity forces it to be a unit. -/
theorem exists_isUnit_coeff_of_isPrimitive
    {K : Type*} [Field K] (V : ValuationSubring K)
    {f : Polynomial V} (hf : f.IsPrimitive) :
    ∃ i : ℕ, IsUnit (f.coeff i) := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  obtain ⟨i, hi, himax⟩ :=
    f.support.exists_max_image
      (fun n => V.valuation ((f.coeff n : V) : K))
      (Polynomial.support_nonempty.mpr hf0)
  refine ⟨i, hf (f.coeff i) ?_⟩
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  by_cases hnzero : f.coeff n = 0
  · simp [hnzero]
  · have hn : n ∈ f.support :=
      Polynomial.mem_support_iff.mpr hnzero
    obtain ⟨z, hz⟩ :=
      (V.valuation_le_iff
        ((f.coeff n : V) : K) ((f.coeff i : V) : K)).mp
        (himax n hn)
    refine ⟨z, ?_⟩
    apply V.subtype_injective
    change ((f.coeff n : V) : K) =
      ((f.coeff i : V) : K) * (z : K)
    rw [mul_comm, hz]

/-- The reduction of a primitive polynomial over a valuation subring is
nonzero. -/
theorem polynomial_residue_ne_zero_of_isPrimitive
    {K : Type*} [Field K] (V : ValuationSubring K)
    {f : Polynomial V} (hf : f.IsPrimitive) :
    f.map (IsLocalRing.residue V) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_isUnit_coeff_of_isPrimitive V hf
  intro hzero
  have hcoeff := congrArg (fun p => p.coeff i) hzero
  change (f.map (IsLocalRing.residue V)).coeff i =
    (0 : Polynomial (IsLocalRing.ResidueField V)).coeff i at hcoeff
  rw [Polynomial.coeff_map] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit (f.coeff i)).2 hi) hcoeff

/-- Pointwise associated factors have associated multiset products. -/
theorem associated_multiset_map_prod_of_forall
    {I M : Type*} [CommMonoid M]
    (s : Multiset I) (f g : I → M)
    (h : ∀ i ∈ s, Associated (f i) (g i)) :
    Associated (s.map f).prod (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact Associated.refl 1
  | cons i s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (h i (by simp)).mul_mul
        (ih (fun j hj => h j (by simp [hj])))

/-- Gauss association descends through a valuation subring: primitive
polynomials that become associated over the fraction field are already
associated over the valuation ring. -/
theorem associated_of_isPrimitive_of_map_associated
    {K : Type*} [Field K] (V : ValuationSubring K)
    {f g : Polynomial V} (hf : f.IsPrimitive) (hg : g.IsPrimitive)
    (hassoc : Associated (f.map V.subtype) (g.map V.subtype)) :
    Associated f g := by
  classical
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨c, hcunit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hscalar :
      f.map V.subtype * Polynomial.C c = g.map V.subtype := by
    rw [hcu]
    exact hu
  obtain ⟨i, hfi⟩ := exists_isUnit_coeff_of_isPrimitive V hf
  obtain ⟨uf, huf⟩ := hfi
  let cV : V := (uf⁻¹ : Vˣ) * g.coeff i
  have hicoeff := congrArg (fun P : Polynomial K => P.coeff i) hscalar
  change (f.map V.subtype * Polynomial.C c).coeff i =
    (g.map V.subtype).coeff i at hicoeff
  rw [Polynomial.coeff_mul_C] at hicoeff
  simp only [Polynomial.coeff_map] at hicoeff
  change ((f.coeff i : V) : K) * c =
    ((g.coeff i : V) : K) at hicoeff
  have hcV : ((cV : V) : K) = c := by
    dsimp [cV]
    change (((uf⁻¹ : Vˣ) : V) : K) * ((g.coeff i : V) : K) = c
    rw [← hicoeff, ← huf]
    have hinvV : ((uf⁻¹ : Vˣ) : V) * (uf : V) = 1 := by simp
    have hinvK := congrArg V.subtype hinvV
    change (((uf⁻¹ : Vˣ) : V) : K) * ((uf : V) : K) = 1 at hinvK
    rw [← mul_assoc, hinvK, one_mul]
  obtain ⟨j, hgj⟩ := exists_isUnit_coeff_of_isPrimitive V hg
  have hjcoeff := congrArg (fun P : Polynomial K => P.coeff j) hscalar
  change (f.map V.subtype * Polynomial.C c).coeff j =
    (g.map V.subtype).coeff j at hjcoeff
  rw [Polynomial.coeff_mul_C] at hjcoeff
  simp only [Polynomial.coeff_map] at hjcoeff
  change ((f.coeff j : V) : K) * c =
    ((g.coeff j : V) : K) at hjcoeff
  have hjV : f.coeff j * cV = g.coeff j := by
    apply V.subtype_injective
    change ((f.coeff j : V) : K) * ((cV : V) : K) =
      ((g.coeff j : V) : K)
    rw [hcV]
    exact hjcoeff
  have hcVunit : IsUnit cV := by
    apply isUnit_of_mul_isUnit_right
    rw [hjV]
    exact hgj
  have hfg : f * Polynomial.C cV = g := by
    apply Polynomial.map_injective V.subtype V.subtype_injective
    rw [Polynomial.map_mul, Polynomial.map_C]
    change f.map V.subtype * Polynomial.C ((cV : V) : K) =
      g.map V.subtype
    rw [hcV]
    exact hscalar
  exact
    (associated_mul_unit_right f (Polynomial.C cV)
      (Polynomial.isUnit_C.mpr hcVunit)).trans
      (Associated.of_eq hfg)

/-- Gauss's product lemma for a valuation subring, stated without choosing a
`NormalizedGCDMonoid` structure. -/
theorem isPrimitive_mul_of_valuationSubring
    {K : Type*} [Field K] (V : ValuationSubring K)
    {f g : Polynomial V} (hf : f.IsPrimitive) (hg : g.IsPrimitive) :
    (f * g).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_contentIdeal_eq_top] at hf hg ⊢
  exact Polynomial.contentIdeal_mul_eq_top_of_contentIdeal_eq_top hf hg

/-- A finite product of primitive polynomials over a valuation subring is
primitive. -/
theorem isPrimitive_finset_prod_of_valuationSubring
    {K I : Type*} [Field K] (V : ValuationSubring K)
    (s : Finset I) (f : I → Polynomial V)
    (hf : ∀ i ∈ s, (f i).IsPrimitive) :
    (∏ i ∈ s, f i).IsPrimitive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact isPrimitive_mul_of_valuationSubring V
        (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Multiset form of the preceding primitive-product lemma, convenient for
unique-factorization multisets over `K[X]`. -/
theorem isPrimitive_multiset_prod_of_valuationSubring
    {K : Type*} [Field K] (V : ValuationSubring K)
    (s : Multiset (Polynomial V))
    (hs : ∀ f ∈ s, f.IsPrimitive) :
    s.prod.IsPrimitive := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons f s ih =>
      rw [Multiset.prod_cons]
      exact isPrimitive_mul_of_valuationSubring V
        (hs f (by simp))
        (ih (fun g hg => hs g (by simp [hg])))

/-- Every irreducible polynomial over the fraction field of a valuation
subring is associated to the image of a primitive irreducible polynomial
over the valuation subring.  This is the normalization step used when the
the construction factors a primitive polynomial over `K` and then rescales each
irreducible factor back into the valuation ring. -/
theorem exists_primitive_irreducible_lift_of_irreducible
    {K : Type*} [Field K] (V : ValuationSubring K)
    {p : Polynomial K} (hp : Irreducible p) :
    ∃ q : Polynomial V,
      q.IsPrimitive ∧ Irreducible q ∧
        Associated (q.map V.subtype) p := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨i, hi, himax⟩ :=
    p.support.exists_max_image (fun n => V.valuation (p.coeff n))
      (Polynomial.support_nonempty.mpr hp0)
  let a : K := p.coeff i
  have ha : a ≠ 0 := by
    simpa [a, Polynomial.mem_support_iff] using hi
  let coeffV : ℕ → V := fun n =>
    if hn : n ∈ p.support then
      ⟨p.coeff n / a, by
        obtain ⟨z, hz⟩ :=
          (V.valuation_le_iff (p.coeff n) a).mp (himax n hn)
        have hzdiv : p.coeff n / a = (z : K) := by
          rw [← hz]
          simp [ha]
        rw [hzdiv]
        exact z.2⟩
    else 0
  let q : Polynomial V :=
    ∑ n ∈ p.support, Polynomial.monomial n (coeffV n)
  have hqcoeffV (n : ℕ) : q.coeff n = coeffV n := by
    by_cases hn : n ∈ p.support
    · have hcoeffne : p.coeff n ≠ 0 :=
        Polynomial.mem_support_iff.mp hn
      simp [q, Polynomial.coeff_monomial, coeffV, hn, hcoeffne]
    · have hcoeffzero : p.coeff n = 0 :=
        Polynomial.notMem_support_iff.mp hn
      simp [q, Polynomial.coeff_monomial, coeffV, hn, hcoeffzero]
  have hqcoeff (n : ℕ) :
      ((q.coeff n : V) : K) = p.coeff n / a := by
    rw [hqcoeffV]
    by_cases hn : n ∈ p.support
    · have hcoeffne : p.coeff n ≠ 0 :=
        Polynomial.mem_support_iff.mp hn
      simp [coeffV, hcoeffne]
    · have hcoeffzero : p.coeff n = 0 :=
        Polynomial.notMem_support_iff.mp hn
      simp [coeffV, hcoeffzero]
  have hqcoeffi : q.coeff i = 1 := by
    apply V.subtype_injective
    simpa [a, ha] using hqcoeff i
  have hqprim : q.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    rcases hr with ⟨s, hs⟩
    apply IsUnit.of_mul_eq_one (s.coeff i)
    calc
      r * s.coeff i = (Polynomial.C r * s).coeff i := by
        simp
      _ = q.coeff i := by rw [← hs]
      _ = 1 := hqcoeffi
  have hqmap : q.map V.subtype = Polynomial.C a⁻¹ * p := by
    ext n
    rw [Polynomial.coeff_map]
    change ((q.coeff n : V) : K) = _
    rw [hqcoeff]
    simp [div_eq_mul_inv, mul_comm]
  have hunitC : IsUnit (Polynomial.C a⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero ha))
  have hqassoc : Associated (q.map V.subtype) p :=
    (Associated.of_eq hqmap).trans
      (associated_unit_mul_left p (Polynomial.C a⁻¹) hunitC)
  have hqirrMap : Irreducible (q.map V.subtype) :=
    hqassoc.symm.irreducible hp
  have hqirr : Irreducible q :=
    hqprim.irreducible_of_irreducible_map_of_injective
      V.subtype_injective hqirrMap
  exact ⟨q, hqprim, hqirr, hqassoc⟩

/-- A primitive polynomial over a valuation subring is, up to a unit over
that valuation subring, a finite product of primitive polynomials whose
fraction-field images are irreducible. -/
theorem primitive_associated_prod_primitive_irreducible_map_factors
    {K : Type*} [Field K] (V : ValuationSubring K)
    (f : Polynomial V) (hf : f.IsPrimitive) :
    ∃ factors : Multiset (Polynomial V),
      (∀ Q ∈ factors, Q.IsPrimitive ∧ Irreducible (Q.map V.subtype)) ∧
        Associated factors.prod f := by
  classical
  let fk : Polynomial K := f.map V.subtype
  have hfk0 : fk ≠ 0 :=
    (Polynomial.map_ne_zero_iff V.subtype_injective).2 hf.ne_zero
  let S : Multiset (Polynomial K) := normalizedFactors fk
  have hlift : ∀ q : Polynomial K, q ∈ S →
      ∃ Q : Polynomial V,
        Q.IsPrimitive ∧ Irreducible Q ∧ Associated (Q.map V.subtype) q := by
    intro q hq
    have hqS : q ∈ normalizedFactors fk := by simpa [S] using hq
    have hqirr : Irreducible q :=
      (Polynomial.mem_normalizedFactors_iff hfk0).1 hqS |>.1
    exact exists_primitive_irreducible_lift_of_irreducible V hqirr
  choose lift hlift_prim hlift_irr hlift_assoc using hlift
  let factors : Multiset (Polynomial V) :=
    S.attach.map (fun q => lift q.1 q.2)
  have hfactors : ∀ Q ∈ factors,
      Q.IsPrimitive ∧ Irreducible (Q.map V.subtype) := by
    intro Q hQ
    rcases Multiset.mem_map.mp hQ with ⟨q, hq, rfl⟩
    have hqmem : q.1 ∈ S := q.2
    have hqS : q.1 ∈ normalizedFactors fk := by
      simpa [S] using hqmem
    exact ⟨hlift_prim q.1 hqmem,
      (hlift_assoc q.1 hqmem).symm.irreducible
        ((Polynomial.mem_normalizedFactors_iff hfk0).1 hqS |>.1)⟩
  have hmapAssoc :
      Associated
        (factors.map (Polynomial.map V.subtype)).prod S.prod := by
    have h := associated_multiset_map_prod_of_forall S.attach
      (fun q => (lift q.1 q.2).map V.subtype) (fun q => q.1)
      (fun q _ => hlift_assoc q.1 q.2)
    simpa [factors] using h
  have hprodMapAssoc :
      Associated (factors.prod.map V.subtype) S.prod := by
    simpa only [Polynomial.map_multiset_prod] using hmapAssoc
  have hlc0 : fk.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hfk0
  have hCunit : IsUnit (Polynomial.C fk.leadingCoeff) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlc0)
  have hSprod :
      Polynomial.C fk.leadingCoeff * S.prod = fk := by
    simpa [S] using Polynomial.leadingCoeff_mul_prod_normalizedFactors fk
  have hSassoc : Associated S.prod fk :=
    (associated_unit_mul_right S.prod
      (Polynomial.C fk.leadingCoeff) hCunit).trans
      (Associated.of_eq hSprod)
  have hprodprim : factors.prod.IsPrimitive :=
    isPrimitive_multiset_prod_of_valuationSubring V factors
      (fun Q hQ => (hfactors Q hQ).1)
  refine ⟨factors, hfactors, ?_⟩
  exact associated_of_isPrimitive_of_map_associated
    V hprodprim hf (hprodMapAssoc.trans hSassoc)

end DiscreteValuationField

end
