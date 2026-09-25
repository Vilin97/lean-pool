/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamification
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom
/-!
# Quotient-depth identity over a general DVF

This file proves the orbit-polynomial ideal identity before normalization of
the fixed-field valuation.  It uses the literal fixed field and its literal
restricted valuation ring; no completeness or Henselian hypothesis occurs.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open scoped Polynomial

/-- A polynomial vanishing at every point of a finite set is divisible by
the product of the corresponding distinct linear factors. -/
theorem prod_X_sub_C_dvd_of_eval_eq_zero_dvf
    {R : Type*} [CommRing R] [IsDomain R]
    (s : Finset R) (p : Polynomial R)
    (hp : ∀ a ∈ s, p.eval a = 0) :
    (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) ∣ p := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert a s ha ih =>
      have hroot : p.IsRoot a := hp a (Finset.mem_insert_self a s)
      rcases Polynomial.dvd_iff_isRoot.mpr hroot with ⟨q, hq⟩
      have hqzero : ∀ z ∈ s, q.eval z = 0 := by
        intro z hz
        have hzroot : p.eval z = 0 := hp z (Finset.mem_insert_of_mem hz)
        have hmul : (z - a) * q.eval z = 0 := by
          rw [hq, Polynomial.eval_mul] at hzroot
          simpa using hzroot
        exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (by
          intro hza
          subst z
          exact ha hz))
      rcases ih q hqzero with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [hq, hr]
      simp only [Finset.prod_insert, ha, not_false_eq_true]
      ring

/-- States the theorem `fintype_prod_X_sub_C_dvd_of_eval_eq_zero_of_injective_dvf`. -/
theorem fintype_prod_X_sub_C_dvd_of_eval_eq_zero_of_injective_dvf
    {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι]
    (r : ι → R) (hr : Function.Injective r) (p : Polynomial R)
    (hp : ∀ i, p.eval (r i) = 0) :
    (∏ i, (Polynomial.X - Polynomial.C (r i))) ∣ p := by
  classical
  have hdiv := prod_X_sub_C_dvd_of_eval_eq_zero_dvf
    (Finset.univ.image r) p (by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
      exact hp i)
  have hprod :
      (∏ a ∈ Finset.univ.image r, (Polynomial.X - Polynomial.C a)) =
        ∏ i : ι, (Polynomial.X - Polynomial.C (r i)) := by
    rw [Finset.prod_image]
    intro i _hi j _hj hij
    exact hr hij
  rwa [hprod] at hdiv

/-- States the theorem `polynomial_eval_mem_ideal_of_coeff_mem_dvf`. -/
theorem polynomial_eval_mem_ideal_of_coeff_mem_dvf
    {R : Type*} [CommRing R] (I : Ideal R) (p : Polynomial R) (z : R)
    (hp : ∀ n, p.coeff n ∈ I) : p.eval z ∈ I := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  exact sum_mem fun n _hn => I.mul_mem_right (z ^ n) (hp n)

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A generator of the top valuation ring has a faithful Galois orbit. -/
theorem valuationSubringAutOfUniqueExtension_generator_injective
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {z : target.valuationSubring}
    (hz : Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) = ⊤) :
    Function.Injective
      (fun sigma : Gal(L/K) =>
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma z) := by
  intro sigma tau hst
  have hring :
      (valuationSubringAlgEquivOfUniqueExtension
        (base := base) (target := target) huniq sigma).toAlgHom =
      (valuationSubringAlgEquivOfUniqueExtension
        (base := base) (target := target) huniq tau).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hz
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hst
  have hfix (a : target.valuationSubring) :
      sigma (algebraMap target.valuationSubring L a) =
        tau (algebraMap target.valuationSubring L a) := by
    change sigma (a : L) = tau (a : L)
    have ha := congrArg Subtype.val (DFunLike.congr_fun hring a)
    change sigma (a : L) = tau (a : L) at ha
    exact ha
  apply AlgEquiv.ext
  intro a
  let : IsFractionRing target.valuationSubring L :=
    target.valuationSubring_isFractionRing
  obtain ⟨b, c, _hc, ha⟩ :=
    IsFractionRing.div_surjective (A := target.valuationSubring) a
  rw [← ha, map_div₀, map_div₀, hfix b, hfix c]

/-- The polynomial whose roots are the `H`-orbit of the top generator. -/
def subgroupOrbitPolynomialDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (z : target.valuationSubring) :
    Polynomial target.valuationSubring := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∏ tau : H,
    (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))

omit [IsGalois K L] in
/-- States the theorem `subgroupOrbitPolynomialDVF_map_aut`. -/
theorem subgroupOrbitPolynomialDVF_map_aut
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (z : target.valuationSubring) (rho : H) :
    (subgroupOrbitPolynomialDVF
        (base := base) (target := target) huniq H z).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq rho).toRingHom =
      subgroupOrbitPolynomialDVF
        (base := base) (target := target) huniq H z := by
  classical
  let : Fintype H := Fintype.ofFinite H
  change
    (∏ tau : H, (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq rho).toRingHom =
    ∏ tau : H, (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact Fintype.prod_equiv (Equiv.mulLeft rho)
    (fun tau : H => Polynomial.X - Polynomial.C
      ((valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq rho).toRingHom
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau z)))
    (fun tau : H => Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))
    (fun _ => by congr 2)

/-- Every orbit-polynomial coefficient, packaged in the literal restricted
valuation ring of the actual fixed field. -/
def subgroupOrbitPolynomialCoeffFixedFieldDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (z : target.valuationSubring) (n : ℕ) :
    fixedFieldValuationSubringDVF (K := K) (target := target) H := by
  let c := (subgroupOrbitPolynomialDVF
    (base := base) (target := target) huniq H z).coeff n
  refine ⟨⟨(c : L), ?_⟩, c.property⟩
  intro rho
  have hmap := congrArg
    (fun p : Polynomial target.valuationSubring => p.coeff n)
    (subgroupOrbitPolynomialDVF_map_aut
      (base := base) (target := target) huniq H z rho)
  exact congrArg Subtype.val (by simpa [c] using hmap)

/-- Product of generator displacements over the right coset `sigma H`. -/
def cosetGeneratorDisplacementProductDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    (z : target.valuationSubring) : target.valuationSubring := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact ∏ tau : H,
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq (sigma * tau) z - z)

omit [IsGalois K L] in
/-- States the theorem `subgroupOrbitPolynomialDVF_eval_self`. -/
theorem subgroupOrbitPolynomialDVF_eval_self
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (z : target.valuationSubring) :
    (subgroupOrbitPolynomialDVF
      (base := base) (target := target) huniq H z).eval z = 0 := by
  classical
  let : Fintype H := Fintype.ofFinite H
  simp only [subgroupOrbitPolynomialDVF, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨1, H.one_mem⟩ : H))
  simp

omit [IsGalois K L] in
/-- States the theorem `subgroupOrbitPolynomialDVF_map_eval_eq_sign_mul_cosetProduct`. -/
theorem subgroupOrbitPolynomialDVF_map_eval_eq_sign_mul_cosetProduct
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    (z : target.valuationSubring) :
    ((subgroupOrbitPolynomialDVF
        (base := base) (target := target) huniq H z).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma).toRingHom).eval z =
      (-1) ^ Nat.card H * cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let es := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq sigma
  simp only [subgroupOrbitPolynomialDVF, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  change (∏ tau : H,
    (z - es (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq tau z))) = _
  change (∏ tau : H,
      (z - es (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))) =
    (-1) ^ Nat.card H * ∏ tau : H,
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (sigma * tau) z - z)
  calc
    (∏ tau : H,
      (z - es (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau z))) =
        ∏ tau : H, -(valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) z - z) := by
      apply Finset.prod_congr rfl
      intro tau _
      rw [show es (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq tau z) =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) z by
        simp [es]]
      ring
    _ = (-1) ^ Nat.card H * ∏ tau : H,
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) z - z) := by
      simpa only [Nat.card_eq_fintype_card, Finset.card_univ] using
        (Finset.prod_neg (s := Finset.univ)
          (fun tau : H => valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (sigma * tau) z - z))

/-- Inclusion into `O_L` intertwines the quotient automorphism with any chosen top lift. -/
theorem fixedFieldToTarget_quotientAut_apply_dvf
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H
        (fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma) a) =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma
        (fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H a) := by
  rw [fixedFieldValuationSubringAutDVF_normalAutEquivQuotient]
  exact fixedFieldValuationSubringDVFToTarget_aut_apply
    (base := base) (target := target) huniq H sigma a

omit [IsGalois K L] in
/-- The coset product divides every top displacement coming from the actual
fixed valuation ring. -/
theorem cosetGeneratorDisplacementProductDVF_dvd_fixed_displacement
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) (sigma : Gal(L/K))
    {z : target.valuationSubring}
    (hz : Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) = ⊤)
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z ∣
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (fixedFieldValuationSubringDVFToTarget
            (K := K) (target := target) H a) -
        fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H a := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let aL := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H a
  have ha_adjoin : aL ∈ Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) := by rw [hz]; simp
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha_adjoin
  rcases ha_adjoin with ⟨g, hg⟩
  have hg' : Polynomial.aeval z g = aL := by simpa using hg
  let p : Polynomial target.valuationSubring :=
    g.map (algebraMap base.valuationSubring target.valuationSubring) -
      Polynomial.C aL
  let r : H → target.valuationSubring := fun tau =>
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq tau z
  have hr : Function.Injective r := by
    intro tau upsilon htu
    apply Subtype.ext
    exact valuationSubringAutOfUniqueExtension_generator_injective
      (base := base) (target := target) huniq hz htu
  have hp : ∀ tau : H, p.eval (r tau) = 0 := by
    intro tau
    have hmap :
        valuationSubringAlgEquivOfUniqueExtension
            (base := base) (target := target) huniq tau
            (Polynomial.aeval z g) =
          Polynomial.aeval
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq tau z) g := by
      calc
        valuationSubringAlgEquivOfUniqueExtension
              (base := base) (target := target) huniq tau
              (Polynomial.aeval z g) =
            Polynomial.aeval
              (valuationSubringAlgEquivOfUniqueExtension
                (base := base) (target := target) huniq tau z) g :=
          (Polynomial.aeval_algHom_apply
            (valuationSubringAlgEquivOfUniqueExtension
              (base := base) (target := target) huniq tau).toAlgHom z g).symm
        _ = Polynomial.aeval
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq tau z) g :=
          congrArg (fun t : target.valuationSubring => Polynomial.aeval t g)
            (show valuationSubringAlgEquivOfUniqueExtension
                (base := base) (target := target) huniq tau z =
              valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq tau z by rfl)
    have hfixed :
        valuationSubringAlgEquivOfUniqueExtension
            (base := base) (target := target) huniq tau aL = aL := by
      apply Subtype.ext
      exact (a : fixedFieldDVF (K := K) H).property tau
    simp only [p, r, Polynomial.eval_sub, Polynomial.eval_map_algebraMap,
      Polynomial.eval_C]
    change Polynomial.aeval
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq tau z) g - aL = 0
    rw [← hmap, hg', hfixed, sub_self]
  have horbit_dvd : subgroupOrbitPolynomialDVF
      (base := base) (target := target) huniq H z ∣ p :=
    fintype_prod_X_sub_C_dvd_of_eval_eq_zero_of_injective_dvf r hr p hp
  let es := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq sigma
  have hmap_dvd := Polynomial.map_dvd es.toRingHom horbit_dvd
  have heval_dvd := map_dvd (Polynomial.evalRingHom z) hmap_dvd
  have hproduct_dvd_eval :
      cosetGeneratorDisplacementProductDVF
          (base := base) (target := target) huniq H sigma z ∣
        (p.map es.toRingHom).eval z := by
    apply dvd_trans
      (b := (-1) ^ Nat.card H *
        cosetGeneratorDisplacementProductDVF
          (base := base) (target := target) huniq H sigma z)
    · exact dvd_mul_left _ _
    · rw [← subgroupOrbitPolynomialDVF_map_eval_eq_sign_mul_cosetProduct
        (base := base) (target := target) huniq H sigma z]
      exact heval_dvd
  have heval_p : (p.map es.toRingHom).eval z =
      -(valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma aL - aL) := by
    have hcoeffmap :
        (g.map (algebraMap base.valuationSubring target.valuationSubring)).map
            es.toRingHom =
          g.map (algebraMap base.valuationSubring target.valuationSubring) := by
      ext n
      simp [es]
    simp only [p, Polynomial.map_sub, hcoeffmap, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_map_algebraMap, Polynomial.eval_C]
    rw [hg']
    change aL - es aL = -(es aL - aL)
    ring
  rw [heval_p] at hproduct_dvd_eval
  exact dvd_neg.mp hproduct_dvd_eval

/-- The coset product belongs to the image of the actual fixed-field
displacement ideal. -/
theorem cosetGeneratorDisplacementProductDVF_mem_map_fixedFieldDisplacementIdeal
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) (z : target.valuationSubring) :
    cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z ∈
      Ideal.map (fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H)
        (fixedFieldDisplacementIdealDVF
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma)) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let f := subgroupOrbitPolynomialDVF
    (base := base) (target := target) huniq H z
  let es := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq sigma
  let q : Polynomial target.valuationSubring :=
    f.map es.toRingHom - f
  let I := Ideal.map (fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H)
    (fixedFieldDisplacementIdealDVF
      (base := base) (target := target) huniq H
      (IsGalois.normalAutEquivQuotient H sigma))
  have hcoeff : ∀ n, q.coeff n ∈ I := by
    intro n
    let c := subgroupOrbitPolynomialCoeffFixedFieldDVF
      (base := base) (target := target) huniq H z n
    have hgen :
        fixedFieldValuationSubringAutDVF
              (base := base) (target := target) huniq H
              (IsGalois.normalAutEquivQuotient H sigma) c - c ∈
          fixedFieldDisplacementIdealDVF
            (base := base) (target := target) huniq H
            (IsGalois.normalAutEquivQuotient H sigma) :=
      Ideal.subset_span ⟨c, rfl⟩
    have hmap := Ideal.mem_map_of_mem
      (fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H) hgen
    have hc :
        fixedFieldValuationSubringDVFToTarget
            (K := K) (target := target) H c =
          (subgroupOrbitPolynomialDVF
            (base := base) (target := target) huniq H z).coeff n :=
      rfl
    have hmap' :
        valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma
              (fixedFieldValuationSubringDVFToTarget
                (K := K) (target := target) H c) -
            fixedFieldValuationSubringDVFToTarget
              (K := K) (target := target) H c ∈
          Ideal.map (fixedFieldValuationSubringDVFToTarget
            (K := K) (target := target) H)
            (fixedFieldDisplacementIdealDVF
              (base := base) (target := target) huniq H
              (IsGalois.normalAutEquivQuotient H sigma)) := by
      simpa only [map_sub, fixedFieldToTarget_quotientAut_apply_dvf] using hmap
    rw [hc] at hmap'
    simpa [q, f, es, I, Polynomial.coeff_map] using hmap'
  have hqeval : q.eval z ∈ I :=
    polynomial_eval_mem_ideal_of_coeff_mem_dvf I q z hcoeff
  have hqeval_eq : q.eval z = (-1) ^ Nat.card H *
      cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z := by
    rw [show q = (subgroupOrbitPolynomialDVF
        (base := base) (target := target) huniq H z).map
          es.toRingHom -
        subgroupOrbitPolynomialDVF
          (base := base) (target := target) huniq H z by rfl]
    rw [Polynomial.eval_sub,
      subgroupOrbitPolynomialDVF_map_eval_eq_sign_mul_cosetProduct,
      subgroupOrbitPolynomialDVF_eval_self, sub_zero]
  have hsign : (-1) ^ Nat.card H *
      cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z ∈ I := by
    rwa [← hqeval_eq]
  exact (I.unit_mul_mem_iff_mem (by simp :
    IsUnit ((-1 : target.valuationSubring) ^ Nat.card H))).mp hsign

/-- The quotient-depth identity, ideal-level form. -/
theorem span_cosetGeneratorDisplacementProduct_eq_map_fixedFieldDisplacementIdeal
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) {z : target.valuationSubring}
    (hz : Algebra.adjoin base.valuationSubring
      ({z} : Set target.valuationSubring) = ⊤) :
    Ideal.span ({cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z} :
      Set target.valuationSubring) =
      Ideal.map (fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H)
        (fixedFieldDisplacementIdealDVF
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro d hd
    rw [Set.mem_singleton_iff] at hd
    subst d
    exact cosetGeneratorDisplacementProductDVF_mem_map_fixedFieldDisplacementIdeal
      (base := base) (target := target) huniq H sigma z
  · rw [Ideal.map_le_iff_le_comap]
    change Ideal.span
      {d | ∃ a : fixedFieldValuationSubringDVF
          (K := K) (target := target) H,
        d = fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma) a - a} ≤ _
    rw [Ideal.span_le]
    rintro d ⟨a, rfl⟩
    change fixedFieldValuationSubringDVFToTarget
        (K := K) (target := target) H
        (fixedFieldValuationSubringAutDVF
          (base := base) (target := target) huniq H
          (IsGalois.normalAutEquivQuotient H sigma) a - a) ∈
      Ideal.span ({cosetGeneratorDisplacementProductDVF
        (base := base) (target := target) huniq H sigma z} :
          Set target.valuationSubring)
    rw [map_sub, fixedFieldToTarget_quotientAut_apply_dvf]
    apply Ideal.mem_span_singleton.mpr
    exact cosetGeneratorDisplacementProductDVF_dvd_fixed_displacement
      (base := base) (target := target) huniq H sigma hz a

end Higher
end RamificationTheory.HilbertRamification
