/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
/-!
# Comparing exponential and canonical ramification indices

This module compares the exponential-valuation presentation of ramification
with the canonical complete-DVF presentation.  The comparison is independent
of any cyclotomic or Kronecker--Weber hypotheses.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace RamificationTheory

open ValuationTheory.DiscreteValuationField
open AlgebraicNumberTheory.Valuations

private theorem map_maximalIdeal_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  ext y
  rw [Ideal.mem_map_of_equiv e y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hy
    apply hx
    rw [← e.symm_apply_apply x]
    exact hy.map (e.symm : S →+* R)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hx
    apply hy
    rw [← e.apply_symm_apply y]
    exact hx.map (e : R →+* S)

private theorem ramificationIdx_eq_of_map_eq
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R S] [Algebra R' S]
    (p : Ideal R) (q : Ideal R') (P : Ideal S)
    (h : Ideal.map (algebraMap R S) p =
      Ideal.map (algebraMap R' S) q) :
    Ideal.ramificationIdx' p P = Ideal.ramificationIdx' q P := by
  unfold Ideal.ramificationIdx'
  rw [h]

/--
The ramification index computed from exponential value groups agrees with the
canonical ramification index of a finite complete-DVF extension when the two
presentations use the same valuation subrings.

This comparison only needs the valued-extension data and the equality of the
underlying valuation rings; it is independent of tameness, Henselianity, and
residue-field separability.
-/
theorem exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L]
    {base : CompleteDVF.{u, v} K} {target : CompleteDVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (vK : LubinTate.Valuations.ExponentialValuation K)
    (vL : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, vL (algebraMap K L a) = vK a)
    (hV : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vK =
      base.valuation.valuationSubring)
    (hW : LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vL =
      target.valuation.valuationSubring) :
    exponentialRamificationIndex vK vL =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF := by
  have hVSub : LubinTate.Valuations.exponentialValuationSubring vK =
      base.valuation.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring hV
  have hWSub : LubinTate.Valuations.exponentialValuationSubring vL =
      target.valuation.valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring hW
  let : IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring vK) := by
    rw [hVSub]
    exact base.valuationSubring_isDiscreteValuationRing
  let : IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring vL) := by
    rw [hWSub]
    exact target.valuationSubring_isDiscreteValuationRing
  have hvdisc : LubinTate.Valuations.DiscreteExponentialValuation vK :=
    discreteExponentialValuation_of_isDiscreteValuationRing vK
  rw [exponentialRamificationIndex_eq_ideal_ramificationIdx vK vL hExt hvdisc]
  let V := LubinTate.Valuations.exponentialValuationSubring vK
  let W := LubinTate.Valuations.exponentialValuationSubring vL
  let B := base.valuationSubring
  let T := target.valuationSubring
  let iValuationExtension := exponentialValuationRingMap vK vL hExt
  let iCan : B →+* T := algebraMap B T
  let eV : V ≃+* B := RingEquiv.subringCongr hVSub
  let eW : W ≃+* T := RingEquiv.subringCongr hWSub
  let g : V →+* T := iCan.comp eV.toRingHom
  let : Algebra V W := iValuationExtension.toAlgebra
  let : Algebra V T := g.toAlgebra
  let eWAlg : W ≃ₐ[V] T :=
    AlgEquiv.ofRingEquiv (f := eW) (by
      intro a
      apply Subtype.ext
      rfl)
  have htransport :=
    Ideal.ramificationIdx'_map_eq
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) eWAlg
  change Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
        (Ideal.map eW (IsLocalRing.maximalIdeal W)) =
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
        (IsLocalRing.maximalIdeal W) at htransport
  have hMaxW : Ideal.map eW (IsLocalRing.maximalIdeal W) =
      target.maximalIdeal :=
    map_maximalIdeal_ringEquiv eW
  rw [hMaxW] at htransport
  have hMaxV : Ideal.map eV (IsLocalRing.maximalIdeal V) =
      base.maximalIdeal :=
    map_maximalIdeal_ringEquiv eV
  have hMap : Ideal.map g (IsLocalRing.maximalIdeal V) =
      Ideal.map iCan base.maximalIdeal := by
    calc
      Ideal.map g (IsLocalRing.maximalIdeal V) =
          Ideal.map (iCan.comp eV.toRingHom)
            (IsLocalRing.maximalIdeal V) := rfl
      _ = Ideal.map iCan
            (Ideal.map eV (IsLocalRing.maximalIdeal V)) := by
            exact (Ideal.map_map eV.toRingHom iCan).symm
      _ = Ideal.map iCan base.maximalIdeal := by rw [hMaxV]
  calc
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
        (IsLocalRing.maximalIdeal W) =
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
          target.maximalIdeal := htransport.symm
    _ = Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal :=
      ramificationIdx_eq_of_map_eq
        (IsLocalRing.maximalIdeal V) base.maximalIdeal target.maximalIdeal hMap
    _ = ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF := rfl

end RamificationTheory

end
