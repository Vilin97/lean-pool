/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.UniqueRing
public import Mathlib.RingTheory.Polynomial.GaussLemma
/-!
# reduction of irreducible factors

This file develops the Galois/residue input in the converse direction.  A
monic polynomial over the base valuation ring whose roots lie in a splitting
field in fact splits over every extension valuation ring: its roots are
integral over the base and hence belong to that ring.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.Valuation renaming
  integralClosure_mem_valuationSubring_of_hasExtension →
    integralClosure_mem_valuationSubring_of_hasExtension


noncomputable section

open Polynomial
open UniqueFactorizationMonoid

namespace AlgebraicNumberTheory
namespace Valuations

open ValuationTheory.Valuations

universe u


/-- A monic polynomial over the base valuation ring that splits in the
extension field already splits over any extension valuation ring. -/
theorem monic_splits_in_extension_valuationSubring
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (F : Polynomial V) (hFmonic : F.Monic)
    (hsplit : (F.map ((algebraMap K L).comp V.subtype)).Splits) :
    (F.map (valuationSubringMapOfHasExtension V W hW)).Splits := by
  let ιVW : V →+* W := valuationSubringMapOfHasExtension V W hW
  let FW : Polynomial W := F.map ιVW
  have hmap : FW.map W.subtype =
      F.map ((algebraMap K L).comp V.subtype) := by
    ext i
    simp only [FW, Polynomial.coeff_map, Function.comp_apply,
      RingHom.coe_comp, ιVW]
    rfl
  have hsplit_map : (FW.map W.subtype).Splits := by
    rw [hmap]
    exact hsplit
  apply Polynomial.Splits.of_splits_map_of_injective W.subtype_injective hsplit_map
  intro α hα
  have hαroot : (F.map ((algebraMap K L).comp V.subtype)).eval α = 0 := by
    rw [← hmap]
    exact (Polynomial.mem_roots
      ((Polynomial.map_ne_zero_iff W.subtype_injective).2
        (hFmonic.map ιVW).ne_zero)).1 hα
  have hαint : IsIntegral V α := by
    refine ⟨F, hFmonic, ?_⟩
    have hVL : (algebraMap V L) =
        (algebraMap K L).comp V.subtype := by
      ext x
      rfl
    rw [hVL]
    rw [Polynomial.eval_map] at hαroot
    exact hαroot
  have hαmem : α ∈ W := by
    have hαint' : IsIntegral V.valuation.valuationSubring α := by
      rw [ValuationSubring.valuationSubring_valuation]
      exact hαint
    have hz : α ∈ W.valuation.valuationSubring :=
      integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) V.valuation W.valuation ⟨α, hαint'⟩
    simpa [ValuationSubring.valuationSubring_valuation] using hz
  exact ⟨⟨α, hαmem⟩, rfl⟩

/-- A monic polynomial over a valuation ring is a product of monic factors
whose images in the fraction field are irreducible.  Integrally closedness of
the valuation ring is what brings the normalized fraction-field factors back
to the valuation ring. -/
theorem monic_eq_prod_monic_irreducible_map_factors
    {K : Type*} [Field K] (V : ValuationSubring K)
    (f : Polynomial V) (hf : f.Monic) :
    ∃ factors : Multiset (Polynomial V),
      (∀ Q ∈ factors, Q.Monic ∧ Irreducible (Q.map V.subtype)) ∧
        factors.prod = f := by
  classical
  let fk : Polynomial K := f.map V.subtype
  let S : Multiset (Polynomial K) := normalizedFactors fk
  have hfk : fk.Monic := hf.map V.subtype
  have hlift : ∀ q : Polynomial K, q ∈ S →
      ∃ Q : Polynomial V, Q.Monic ∧ Q.map V.subtype = q := by
    intro q hq
    have hqdata := (Polynomial.mem_normalizedFactors_iff hfk.ne_zero).1 hq
    obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd
      (K := K) hf hqdata.2.2
    have hAlgebraMap : algebraMap V K = V.subtype := by
      ext x
      exact V.algebraMap_apply x
    have hQmap : Q.map V.subtype = q := by
      simpa [hAlgebraMap, hqdata.2.1] using hQ
    have hQmonic : Q.Monic := by
      apply (V.subtype_injective.monic_map_iff).2
      rw [hQmap]
      exact hqdata.2.1
    exact ⟨Q, hQmonic, hQmap⟩
  choose lift hlift_monic hlift_map using hlift
  let factors : Multiset (Polynomial V) :=
    S.attach.map (fun q => lift q.1 q.2)
  have hfactors : ∀ Q ∈ factors,
      Q.Monic ∧ Irreducible (Q.map V.subtype) := by
    intro Q hQ
    rcases Multiset.mem_map.mp hQ with ⟨q, hq, rfl⟩
    have hqmem : q.1 ∈ S := q.2
    refine ⟨hlift_monic q.1 hqmem, ?_⟩
    rw [hlift_map q.1 hqmem]
    exact (Polynomial.mem_normalizedFactors_iff hfk.ne_zero).1 hqmem |>.1
  have hmapFactors : factors.map (Polynomial.map V.subtype) = S := by
    simp [factors, hlift_map]
  have hSprod : S.prod = fk := by
    have hprod := Polynomial.leadingCoeff_mul_prod_normalizedFactors fk
    simpa [S, hfk.leadingCoeff] using hprod
  refine ⟨factors, hfactors, ?_⟩
  apply Polynomial.map_injective V.subtype V.subtype_injective
  rw [Polynomial.map_multiset_prod, hmapFactors, hSprod]

/-- The canonical residue-field map sends the residue of a base-ring element
to the residue of its image in the extension valuation ring. -/
theorem residueFieldMapOfHasExtension_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation) (x : V) :
    residueFieldMapOfHasExtension V W hW (IsLocalRing.residue V x) =
      IsLocalRing.residue W (valuationSubringMapOfHasExtension V W hW x) := by
  let : IsLocalHom (valuationSubringMapOfHasExtension V W hW) :=
    valuationSubringMapOfHasExtension_isLocalHom V W hW
  exact IsLocalRing.ResidueField.map_residue
    (valuationSubringMapOfHasExtension V W hW) x

/-- Reducing a monic split polynomial along an extension valuation ring gives
a split polynomial over the extension residue field. -/
theorem monic_reduction_splits_in_extension_residueField
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (F : Polynomial V) (hFmonic : F.Monic)
    (hsplit : (F.map ((algebraMap K L).comp V.subtype)).Splits) :
    ((F.map (IsLocalRing.residue V)).map
      (residueFieldMapOfHasExtension V W hW)).Splits := by
  have hsplitW :
      (F.map (valuationSubringMapOfHasExtension V W hW)).Splits :=
    monic_splits_in_extension_valuationSubring V W F hFmonic hsplit
  have hsplitResidue := hsplitW.map (IsLocalRing.residue W)
  have hpoly :
      (F.map (IsLocalRing.residue V)).map
          (residueFieldMapOfHasExtension V W hW) =
        (F.map (valuationSubringMapOfHasExtension V W hW)).map
          (IsLocalRing.residue W) := by
    ext i
    simp only [Polynomial.coeff_map]
    exact residueFieldMapOfHasExtension_residue V W hW (F.coeff i)
  rw [hpoly]
  exact hsplitResidue

/-- In a normal extension with a unique extension valuation ring, reductions
of two roots of one irreducible ground-field polynomial are conjugate under
the induced residue-field automorphism. -/
theorem residues_of_irreducible_roots_are_conjugate
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : V.valuation.HasExtension W.valuation)
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (F : Polynomial V)
    (hirr : Irreducible (F.map V.subtype))
    {a b : W}
    (ha : (F.map (valuationSubringMapOfHasExtension V W hW)).eval a = 0)
    (hb : (F.map (valuationSubringMapOfHasExtension V W hW)).eval b = 0) :
    ∃ σ : L ≃ₐ[K] L,
      residueFieldEquivOfUniqueExtension V W hW huniq σ
          (IsLocalRing.residue W b) =
        IsLocalRing.residue W a := by
  let p : Polynomial K := F.map V.subtype
  let ιVW : V →+* W := valuationSubringMapOfHasExtension V W hW
  have hmap :
      (F.map ιVW).map W.subtype =
        p.map (algebraMap K L) := by
    ext i
    simp only [Polynomial.coeff_map, p, ιVW]
    rfl
  have haL : (p.map (algebraMap K L)).eval (a : L) = 0 := by
    rw [← hmap]
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ W.subtype (W.subtype a) (F.map ιVW) = 0
    rw [Polynomial.eval₂_hom]
    exact congrArg W.subtype ha
  have hbL : (p.map (algebraMap K L)).eval (b : L) = 0 := by
    rw [← hmap]
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ W.subtype (W.subtype b) (F.map ιVW) = 0
    rw [Polynomial.eval₂_hom]
    exact congrArg W.subtype hb
  have haeval : (aeval (a : L)) p = 0 := by
    simpa [aeval_def, Polynomial.eval_map] using haL
  have hbeval : (aeval (b : L)) p = 0 := by
    simpa [aeval_def, Polynomial.eval_map] using hbL
  have hmin : minpoly K (a : L) = minpoly K (b : L) := by
    rw [← minpoly.eq_of_irreducible hirr haeval,
      ← minpoly.eq_of_irreducible hirr hbeval]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 hmin
  refine ⟨σ, ?_⟩
  rw [residueFieldEquivOfUniqueExtension_residue]
  congr 1
  ext
  exact hσ

/-- A monic irreducible factor over the ground field cannot acquire two
coprime positive-degree factors after reduction when the extension valuation
ring on its splitting field is unique.  This is the precise primary-reduction
input used in the proof of the unique-extension criterion. -/
theorem irreducible_monic_reduction_coprime_factor_degree_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (F : Polynomial V) (hFmonic : F.Monic)
    (hirr : Irreducible (F.map V.subtype))
    [IsSplittingField K L (F.map V.subtype)]
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hfactor : F.map (IsLocalRing.residue V) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    gbar.natDegree = 0 ∨ hbar.natDegree = 0 := by
  let : Normal K L := Normal.of_isSplittingField (F.map V.subtype)
  by_contra hdegrees
  push Not at hdegrees
  have hgpos : 0 < gbar.natDegree := Nat.pos_of_ne_zero hdegrees.1
  have hhpos : 0 < hbar.natDegree := Nat.pos_of_ne_zero hdegrees.2
  let k := IsLocalRing.ResidueField V
  let l := IsLocalRing.ResidueField W
  let φ : k →+* l := residueFieldMapOfHasExtension V W hW
  let Fbar : Polynomial k := F.map (IsLocalRing.residue V)
  let FW : Polynomial W := F.map (valuationSubringMapOfHasExtension V W hW)
  have hsplitL :
      (F.map ((algebraMap K L).comp V.subtype)).Splits := by
    have hs := IsSplittingField.splits L (F.map V.subtype)
    simpa [Polynomial.map_map] using hs
  have hsplitW : FW.Splits := by
    exact monic_splits_in_extension_valuationSubring V W F hFmonic hsplitL
  have hpolyResidue :
      Fbar.map φ = FW.map (IsLocalRing.residue W) := by
    ext i
    simp only [Fbar, FW, Polynomial.coeff_map, φ]
    exact residueFieldMapOfHasExtension_residue V W hW (F.coeff i)
  have hsplitBar : (Fbar.map φ).Splits := by
    rw [hpolyResidue]
    exact hsplitW.map (IsLocalRing.residue W)
  have hFbar0 : Fbar.map φ ≠ 0 :=
    (hFmonic.map (IsLocalRing.residue V)).map φ |>.ne_zero
  have hfactorMap : Fbar.map φ = gbar.map φ * hbar.map φ := by
    rw [← Polynomial.map_mul, ← hfactor]
  have hgSplit : (gbar.map φ).Splits :=
    hsplitBar.of_dvd hFbar0 (by
      rw [hfactorMap]
      exact dvd_mul_right _ _)
  have hhSplit : (hbar.map φ).Splits :=
    hsplitBar.of_dvd hFbar0 (by
      rw [hfactorMap]
      exact dvd_mul_left _ _)
  have hgRootsNe : (gbar.map φ).roots ≠ 0 := by
    intro hz
    have hc := hgSplit.natDegree_eq_card_roots
    rw [hz] at hc
    have : gbar.natDegree = 0 := by
      simpa [Polynomial.natDegree_map] using hc
    exact hdegrees.1 this
  have hhRootsNe : (hbar.map φ).roots ≠ 0 := by
    intro hz
    have hc := hhSplit.natDegree_eq_card_roots
    rw [hz] at hc
    have : hbar.natDegree = 0 := by
      simpa [Polynomial.natDegree_map] using hc
    exact hdegrees.2 this
  obtain ⟨γ, hγg⟩ := Multiset.exists_mem_of_ne_zero hgRootsNe
  obtain ⟨δ, hδh⟩ := Multiset.exists_mem_of_ne_zero hhRootsNe
  have hprod0 : gbar.map φ * hbar.map φ ≠ 0 := by
    rw [← hfactorMap]
    exact hFbar0
  have hg0 : gbar.map φ ≠ 0 := left_ne_zero_of_mul hprod0
  have hh0 : hbar.map φ ≠ 0 := right_ne_zero_of_mul hprod0
  have hγF : γ ∈ (Fbar.map φ).roots := by
    rw [hfactorMap, Polynomial.roots_mul hprod0]
    simp [hγg]
  have hδF : δ ∈ (Fbar.map φ).roots := by
    rw [hfactorMap, Polynomial.roots_mul hprod0]
    simp [hδh]
  have hγFW : γ ∈ (FW.map (IsLocalRing.residue W)).roots := by
    rwa [← hpolyResidue]
  have hδFW : δ ∈ (FW.map (IsLocalRing.residue W)).roots := by
    rwa [← hpolyResidue]
  have hrootsMap :
      FW.roots.map (IsLocalRing.residue W) =
        (FW.map (IsLocalRing.residue W)).roots :=
    (hFmonic.map (valuationSubringMapOfHasExtension V W hW)).roots_map_of_card_eq_natDegree
      (IsLocalRing.residue W) hsplitW.natDegree_eq_card_roots.symm
  rw [← hrootsMap] at hγFW hδFW
  obtain ⟨a, haRoot, haResidue⟩ := Multiset.mem_map.mp hγFW
  obtain ⟨b, hbRoot, hbResidue⟩ := Multiset.mem_map.mp hδFW
  have haEval : FW.eval a = 0 :=
    (Polynomial.mem_roots (hFmonic.map
      (valuationSubringMapOfHasExtension V W hW)).ne_zero).1 haRoot
  have hbEval : FW.eval b = 0 :=
    (Polynomial.mem_roots (hFmonic.map
      (valuationSubringMapOfHasExtension V W hW)).ne_zero).1 hbRoot
  obtain ⟨σ, hσres⟩ :=
    residues_of_irreducible_roots_are_conjugate V W hW huniq F hirr hbEval haEval
  let τ : l ≃+* l := residueFieldEquivOfUniqueExtension V W hW huniq σ
  have hτγδ : τ γ = δ := by
    dsimp [τ]
    rw [← haResidue, ← hbResidue]
    exact hσres
  have hτcoeff : (gbar.map φ).map τ.toRingHom = gbar.map φ := by
    ext i
    simp only [Polynomial.coeff_map, φ, τ]
    exact residueFieldEquivOfUniqueExtension_algebraMap
      V W huniq σ (gbar.coeff i)
  have hγeval : (gbar.map φ).eval γ = 0 :=
    (Polynomial.mem_roots hg0).1 hγg
  have hδg : (gbar.map φ).eval δ = 0 := by
    calc
      (gbar.map φ).eval δ = (gbar.map φ).eval (τ γ) := by rw [hτγδ]
      _ = ((gbar.map φ).map τ.toRingHom).eval (τ γ) := by rw [hτcoeff]
      _ = τ ((gbar.map φ).eval γ) := by
        change ((gbar.map φ).map τ.toRingHom).eval (τ.toRingHom γ) = _
        exact Polynomial.eval_map_apply (p := gbar.map φ) (f := τ.toRingHom) γ
      _ = 0 := by rw [hγeval, map_zero]
  have hδeval : (hbar.map φ).eval δ = 0 :=
    (Polynomial.mem_roots hh0).1 hδh
  have hcoprimeMap : IsCoprime (gbar.map φ) (hbar.map φ) := by
    simpa using hcoprime.map (Polynomial.mapRingHom φ)
  rcases hcoprimeMap with ⟨A, B, hbez⟩
  have hbezEval := congrArg (Polynomial.eval δ) hbez
  simp [hδg, hδeval] at hbezEval

/-- A reduced monic irreducible factor divides exactly one side of any
coprime residual product that it divides. -/
theorem irreducible_monic_reduction_dvd_left_or_right_of_coprime
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L)
    [hW : V.valuation.HasExtension W.valuation]
    (huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W)
    (Q : Polynomial V) (hQmonic : Q.Monic)
    (hQirr : Irreducible (Q.map V.subtype))
    [IsSplittingField K L (Q.map V.subtype)]
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hcoprime : IsCoprime gbar hbar)
    (hQdvd : Q.map (IsLocalRing.residue V) ∣ gbar * hbar) :
    Q.map (IsLocalRing.residue V) ∣ gbar ∨
      Q.map (IsLocalRing.residue V) ∣ hbar := by
  obtain ⟨q₁, q₂, hq₁g, hq₂h, hQfactor⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hQdvd
  have hqcoprime : IsCoprime q₁ q₂ := by
    rcases hcoprime with ⟨A, B, hbez⟩
    obtain ⟨g', hg'⟩ := hq₁g
    obtain ⟨h', hh'⟩ := hq₂h
    refine ⟨A * g', B * h', ?_⟩
    calc
      (A * g') * q₁ + (B * h') * q₂ =
          A * (q₁ * g') + B * (q₂ * h') := by ring
      _ = A * gbar + B * hbar := by rw [← hg', ← hh']
      _ = 1 := hbez
  have hdegrees :=
    irreducible_monic_reduction_coprime_factor_degree_zero
      V W huniq Q hQmonic hQirr q₁ q₂ hQfactor hqcoprime
  have hQbar0 : Q.map (IsLocalRing.residue V) ≠ 0 :=
    (hQmonic.map (IsLocalRing.residue V)).ne_zero
  have hqprod0 : q₁ * q₂ ≠ 0 := by
    rw [← hQfactor]
    exact hQbar0
  have hq₁0 : q₁ ≠ 0 := left_ne_zero_of_mul hqprod0
  have hq₂0 : q₂ ≠ 0 := right_ne_zero_of_mul hqprod0
  rcases hdegrees with hq₁deg | hq₂deg
  · right
    have hq₁unit : IsUnit q₁ := by
      rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree hq₁0, hq₁deg]
      rfl
    have hassoc : Associated (q₁ * q₂) q₂ := by
      exact associated_unit_mul_left q₂ q₁ hq₁unit
    rw [hQfactor]
    exact hassoc.dvd_iff_dvd_left.mpr hq₂h
  · left
    have hq₂unit : IsUnit q₂ := by
      rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree hq₂0, hq₂deg]
      rfl
    have hassoc : Associated (q₁ * q₂) q₁ := by
      exact associated_mul_unit_left q₁ q₂ hq₂unit
    rw [hQfactor]
    exact hassoc.dvd_iff_dvd_left.mpr hq₁g

/-- Partition a multiset of monic irreducible ground-field factors according
to a coprime factorization of the product of their reductions.  Unique
extendability supplies the all-or-nothing divisibility of each individual
reduced factor. -/
theorem partition_monic_irreducible_factors_along_coprime_reduction
    {K : Type u} [Field K] (V : ValuationSubring K)
    (hunique : ∀ (E : Type u) [Field E] [Algebra K E]
      [Algebra.IsAlgebraic K E],
        ∃! W : ValuationSubring E,
          V.valuation.HasExtension W.valuation)
    (factors : Multiset (Polynomial V))
    (hfactors : ∀ Q ∈ factors,
      Q.Monic ∧ Irreducible (Q.map V.subtype))
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hgmonic : gbar.Monic) (hhmonic : hbar.Monic)
    (hproduct :
      (factors.map (fun Q => Q.map (IsLocalRing.residue V))).prod =
        gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ G H : Polynomial V,
      G.Monic ∧ H.Monic ∧ factors.prod = G * H ∧
        G.map (IsLocalRing.residue V) = gbar ∧
          H.map (IsLocalRing.residue V) = hbar := by
  classical
  induction factors using Multiset.induction_on generalizing gbar hbar with
  | empty =>
      have hgh : gbar * hbar = 1 := by simpa using hproduct.symm
      have hgunit : IsUnit gbar :=
        isUnit_iff_exists_inv'.2 ⟨hbar, by simpa [mul_comm] using hgh⟩
      have hhunit : IsUnit hbar :=
        isUnit_iff_exists_inv'.2 ⟨gbar, hgh⟩
      have hg : gbar = 1 := hgmonic.isUnit_iff.1 hgunit
      have hh : hbar = 1 := hhmonic.isUnit_iff.1 hhunit
      subst gbar
      subst hbar
      exact ⟨1, 1, Polynomial.monic_one, Polynomial.monic_one, by simp, by simp, by simp⟩
  | cons Q factors ih =>
      have hQdata : Q.Monic ∧ Irreducible (Q.map V.subtype) :=
        hfactors Q (by simp)
      have htail : ∀ R ∈ factors,
          R.Monic ∧ Irreducible (R.map V.subtype) := by
        intro R hR
        exact hfactors R (by simp [hR])
      let qbar : Polynomial (IsLocalRing.ResidueField V) :=
        Q.map (IsLocalRing.residue V)
      have hQbarMonic : qbar.Monic := hQdata.1.map (IsLocalRing.residue V)
      have hproduct' :
          qbar * (factors.map
            (fun R => R.map (IsLocalRing.residue V))).prod = gbar * hbar := by
        simpa [qbar] using hproduct
      have hQdvd : qbar ∣ gbar * hbar := by
        rw [← hproduct']
        exact dvd_mul_right _ _
      let E : Type u := (Q.map V.subtype).SplittingField
      obtain ⟨W, hW, hWuniq⟩ := hunique E
      let : V.valuation.HasExtension W.valuation := hW
      have hside : qbar ∣ gbar ∨ qbar ∣ hbar :=
        irreducible_monic_reduction_dvd_left_or_right_of_coprime
          V W hWuniq Q hQdata.1 hQdata.2 gbar hbar hcoprime hQdvd
      rcases hside with hQg | hQh
      · obtain ⟨g', hg'⟩ := hQg
        have hg'monic : g'.Monic := by
          apply hQbarMonic.of_mul_monic_left
          rw [← hg']
          exact hgmonic
        have hg'coprime : IsCoprime g' hbar := by
          rcases hcoprime with ⟨A, B, hbez⟩
          refine ⟨A * qbar, B, ?_⟩
          calc
            (A * qbar) * g' + B * hbar =
                A * (qbar * g') + B * hbar := by ring
            _ = A * gbar + B * hbar := by rw [← hg']
            _ = 1 := hbez
        have hrest :
            (factors.map
              (fun R => R.map (IsLocalRing.residue V))).prod =
              g' * hbar := by
          apply mul_left_cancel₀ hQbarMonic.ne_zero
          calc
            qbar * (factors.map
                (fun R => R.map (IsLocalRing.residue V))).prod =
                gbar * hbar := hproduct'
            _ = (qbar * g') * hbar := by rw [← hg']
            _ = qbar * (g' * hbar) := by ring
        obtain ⟨G, H, hGmonic, hHmonic, hfactorGH, hGbar, hHbar⟩ :=
          ih htail g' hbar hg'monic hhmonic hrest hg'coprime
        refine ⟨Q * G, H, hQdata.1.mul hGmonic, hHmonic, ?_, ?_, hHbar⟩
        · simp only [Multiset.prod_cons, hfactorGH]
          ring
        · rw [Polynomial.map_mul, hGbar]
          exact hg'.symm
      · obtain ⟨h', hh'⟩ := hQh
        have hh'monic : h'.Monic := by
          apply hQbarMonic.of_mul_monic_left
          rw [← hh']
          exact hhmonic
        have hh'coprime : IsCoprime gbar h' := by
          rcases hcoprime with ⟨A, B, hbez⟩
          refine ⟨A, B * qbar, ?_⟩
          calc
            A * gbar + (B * qbar) * h' =
                A * gbar + B * (qbar * h') := by ring
            _ = A * gbar + B * hbar := by rw [← hh']
            _ = 1 := hbez
        have hrest :
            (factors.map
              (fun R => R.map (IsLocalRing.residue V))).prod =
              gbar * h' := by
          apply mul_left_cancel₀ hQbarMonic.ne_zero
          calc
            qbar * (factors.map
                (fun R => R.map (IsLocalRing.residue V))).prod =
                gbar * hbar := hproduct'
            _ = gbar * (qbar * h') := by rw [← hh']
            _ = qbar * (gbar * h') := by ring
        obtain ⟨G, H, hGmonic, hHmonic, hfactorGH, hGbar, hHbar⟩ :=
          ih htail gbar h' hgmonic hh'monic hrest hh'coprime
        refine ⟨G, Q * H, hGmonic, hQdata.1.mul hHmonic, ?_, hGbar, ?_⟩
        · simp only [Multiset.prod_cons, hfactorGH]
          ring
        · rw [Polynomial.map_mul, hHbar]
          exact hh'.symm

end Valuations
end AlgebraicNumberTheory

end
