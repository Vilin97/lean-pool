/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldValuationRing
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth
public import Mathlib.NumberTheory.RamificationInertia.Galois
/-!
# The ramification index of an actual fixed field over a general DVF

For `M = L ^ H`, this file defines `e(L/M)` from the literal inclusion
`O_M = O_L ∩ M → O_L`.  The definition and its comparison with the zeroth
depth subgroup require no completeness or Henselian hypothesis.
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory.NonarchimedeanDepth
  renaming
  depthLowerFiltration_lower →
    depthLowerFiltration_lower

open _root_.RamificationTheory.DiscreteValuationField.HerbrandGroupTheory.NonarchimedeanDepth
  renaming
  mem_depthLowerSubgroup_iff →
    mem_depthLowerSubgroup_iff


noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open scoped Pointwise

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The ramification index of `L/(L ^ H)`, formed from the literal inclusion
of the restricted fixed-field valuation ring into the top valuation ring. -/
def fixedFieldRamificationIndex
    (H : Subgroup Gal(L/K)) : ℕ := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let O := target.valuationSubring
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  letI : Algebra B O := j.toAlgebra
  exact Ideal.ramificationIdx' (IsLocalRing.maximalIdeal B)
    target.maximalIdeal

/-- The image of the fixed-field maximal ideal is the power of the top
maximal ideal indexed by the literal ramification index. -/
theorem map_fixedField_maximalIdeal_eq_pow_ramificationIndex
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Ideal.map
        (fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H)
        (IsLocalRing.maximalIdeal
          (fixedFieldValuationSubringDVF (K := K) (target := target) H)) =
      target.maximalIdeal ^
        fixedFieldRamificationIndex
          (target := target) H := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  let : Algebra B target.valuationSubring := j.toAlgebra
  let p := IsLocalRing.maximalIdeal B
  let P := target.maximalIdeal
  let : IsDiscreteValuationRing B :=
    fixedFieldValuationSubringDVF_isDiscreteValuationRing
      (base := base) (target := target) huniq H
  have hj : Function.Injective j :=
    fixedFieldValuationSubringDVFToTarget_injective
      (K := K) (target := target) H
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hmap0 : Ideal.map j p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hj).not.mpr hp0
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, hm⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hpi
  have hmapPow : Ideal.map j p = P ^ m := by
    rw [hm, show P = IsLocalRing.maximalIdeal target.valuationSubring from rfl,
      hpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hnot : ¬ Ideal.map j p ≤ P ^ (m + 1) := by
    rw [hmapPow]
    exact not_le_of_gt
      (Ideal.pow_succ_lt_pow
        (IsDiscreteValuationRing.not_a_field target.valuationSubring) m)
  have hjalg : algebraMap B target.valuationSubring = j := rfl
  have he : Ideal.ramificationIdx' p P = m :=
    Ideal.ramificationIdx'_spec
      (by rw [hjalg]; exact hmapPow.le)
      (by rw [hjalg]; exact hnot)
  change Ideal.map j p = P ^ Ideal.ramificationIdx' p P
  rw [he]
  exact hmapPow

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem isUnit_fixedFieldValuationSubringDVFToTarget_iff
    (H : Subgroup Gal(L/K))
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    IsUnit
        (fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H a) ↔
      IsUnit a := by
  let M := fixedFieldDVF (K := K) H
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  constructor
  · intro ha
    have haTop :
        algebraMap M L (a : M) ≠ 0 ∧
          (algebraMap M L (a : M))⁻¹ ∈
            target.valuation.valuationSubring := by
      simpa [M, j] using
        (Submonoid.isUnit_iff_and
          (S := target.valuation.valuationSubring) (a := j a)).mp ha
    rw [Submonoid.isUnit_iff_and (S := B) (a := a)]
    refine ⟨?_, ?_⟩
    · intro ha0
      apply haTop.1
      rw [ha0, map_zero]
    · change algebraMap M L ((a : M)⁻¹) ∈
        target.valuation.valuationSubring
      rw [map_inv₀]
      exact haTop.2
  · intro ha
    exact ha.map j

/-- States the theorem `fixedFieldRamificationIndex_ne_zero`. -/
theorem fixedFieldRamificationIndex_ne_zero
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    fixedFieldRamificationIndex
        (target := target) H ≠ 0 := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  let : IsDiscreteValuationRing B :=
    fixedFieldValuationSubringDVF_isDiscreteValuationRing
      (base := base) (target := target) huniq H
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hspan :
      Ideal.span ({j pi} : Set target.valuationSubring) =
        target.maximalIdeal ^
          fixedFieldRamificationIndex
            (target := target) H := by
    calc
      Ideal.span ({j pi} : Set target.valuationSubring) =
          Ideal.map j (Ideal.span ({pi} : Set B)) := by
            rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map j (IsLocalRing.maximalIdeal B) := by
            rw [hpi.maximalIdeal_eq]
      _ = target.maximalIdeal ^
          fixedFieldRamificationIndex
            (target := target) H :=
        map_fixedField_maximalIdeal_eq_pow_ramificationIndex
          (base := base) (target := target) huniq H
  intro he
  have hjpi : IsUnit (j pi) := by
    rw [← Ideal.span_singleton_eq_top]
    simpa [he] using hspan
  have hpiUnit : IsUnit pi :=
    (isUnit_fixedFieldValuationSubringDVFToTarget_iff
      (K := K) (target := target) H pi).mp hjpi
  exact hpi.not_isUnit hpiUnit

/-- The normalized additive valuation on the top valuation ring restricts
to the ramification index times the normalized additive valuation on the
literal fixed-field valuation ring. -/
theorem addVal_fixedFieldValuationSubringToTarget_eq_ramificationIndex_nsmul
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal]
    (a : fixedFieldValuationSubringDVF (K := K) (target := target) H) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (fixedFieldValuationSubringDVFToTarget
          (K := K) (target := target) H a) =
      fixedFieldRamificationIndex
          (target := target) H •
        (@IsDiscreteValuationRing.addVal
          (fixedFieldValuationSubringDVF (K := K) (target := target) H)
          inferInstance inferInstance
          (fixedFieldValuationSubringDVF_isDiscreteValuationRing
            (base := base) (target := target) huniq H)) a := by
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  let e := fixedFieldRamificationIndex
    (target := target) H
  let : IsDiscreteValuationRing B :=
    fixedFieldValuationSubringDVF_isDiscreteValuationRing
      (base := base) (target := target) huniq H
  have he_ne : e ≠ 0 :=
    fixedFieldRamificationIndex_ne_zero
      (base := base) (target := target) huniq H
  by_cases ha : a = 0
  · subst a
    have he_coe_ne : (e : ℕ∞) ≠ 0 := by
      exact_mod_cast he_ne
    rw [map_zero, IsDiscreteValuationRing.addVal_zero,
      IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul, ENat.mul_top he_coe_ne]
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨n, u, ha_decomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hpi
  have hspan :
      Ideal.span ({j pi} : Set target.valuationSubring) =
        Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
    calc
      Ideal.span ({j pi} : Set target.valuationSubring) =
          Ideal.map j (Ideal.span ({pi} : Set B)) := by
            rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map j (IsLocalRing.maximalIdeal B) := by
            rw [hpi.maximalIdeal_eq]
      _ = target.maximalIdeal ^ e :=
        map_fixedField_maximalIdeal_eq_pow_ramificationIndex
          (base := base) (target := target) huniq H
      _ = Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
            rw [show target.maximalIdeal =
                IsLocalRing.maximalIdeal target.valuationSubring from rfl,
              hvarpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hmap_uniformizer :
      IsDiscreteValuationRing.addVal target.valuationSubring (j pi) =
        (e : ℕ∞) := by
    calc
      IsDiscreteValuationRing.addVal target.valuationSubring (j pi) =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (varpi ^ e) :=
        (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
          (Ideal.span_singleton_eq_span_singleton.mp hspan)
      _ = (e : ℕ∞) := hvarpi.addVal_pow e
  rw [ha_decomp, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hmap_uniformizer,
    IsDiscreteValuationRing.addVal_def
      ((u : B) * pi ^ n) u hpi n rfl]
  have hmap_unit :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (u : B)) = 0 := by
    exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
      ((u.isUnit : IsUnit (u : B)).map j)
  rw [hmap_unit, zero_add]
  simp [e, nsmul_eq_mul, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
private noncomputable def fixedFieldTopValuationSubringActionHomDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) :
    H →* (target.valuationSubring ≃+* target.valuationSubring) where
  toFun tau := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq (tau : Gal(L/K))
  map_one' := by
    ext a
    simp
  map_mul' sigma tau := by
    ext a
    simp

private noncomputable def fixedFieldInertiaSubgroupDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) : Subgroup H := by
  letI : MulSemiringAction H target.valuationSubring :=
    MulSemiringAction.compHom (R := target.valuationSubring)
      (fixedFieldTopValuationSubringActionHomDVF
        (base := base) (target := target) huniq H)
  exact target.maximalIdeal.toAddSubgroup.inertia H

variable [Algebra.IsSeparable base.residueField target.residueField]

/-- The zeroth subgroup cut out by the canonical general-DVF depth is the
inertia subgroup for the action of H on the top valuation ring. -/
private theorem depthLowerFiltration_zero_eq_fixedFieldInertiaSubgroupDVF
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) :
    ((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H).lower 0 =
      fixedFieldInertiaSubgroupDVF
        (base := base) (target := target) huniq H := by
  let : MulSemiringAction H target.valuationSubring :=
    MulSemiringAction.compHom (R := target.valuationSubring)
      (fixedFieldTopValuationSubringActionHomDVF
        (base := base) (target := target) huniq H)
  change
    ((ramificationNumberDepthOfUniqueExtension
        (base := base) (target := target) huniq).depthLowerFiltration H).lower 0 =
      target.maximalIdeal.toAddSubgroup.inertia H
  ext tau
  rw [depthLowerFiltration_lower,
    mem_depthLowerSubgroup_iff]
  change
    (1 : ℕ∞) ≤ intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq (tau : Gal(L/K)) ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (tau : Gal(L/K)) a - a ∈
          target.maximalIdeal
  simpa using
    ((mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
        (base := base) (target := target) huniq 0 (tau : Gal(L/K))).symm.trans
      (mem_lowerRamificationGroup_nat_iff
        (base := base) (target := target) huniq 0 (tau : Gal(L/K))))

/-- Computes a decomposition-group stabilizer from inertia and residue degree
when the induced residue extension is separable. -/
private theorem card_stabilizer_eq_inertia_mul_inertiaDeg
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsPrime] [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (Ideal.inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra.IsSeparable p.ResidueField P.ResidueField :=
    Algebra.isSeparable_residueField_iff.mpr
      (inferInstance : Algebra.IsSeparable (R ⧸ p) (S ⧸ P))
  have heq :
      (algebraMap (S ⧸ P) P.ResidueField).comp
          (algebraMap (R ⧸ p) (S ⧸ P)) =
        (algebraMap p.ResidueField P.ResidueField).comp
          (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let :=
    ((algebraMap (S ⧸ P) P.ResidueField).comp
      (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField :=
    .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal
        G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant
      G p P p.ResidueField P.ResidueField
  have hindex :
      Subgroup.index (Ideal.inertia (MulAction.stabilizer G P) P) =
        Nat.card Gal(P.ResidueField/p.ResidueField) :=
    Nat.card_congr
      (IsFractionRing.stabilizerQuotientInertiaEquiv
        G p P p.ResidueField P.ResidueField).toEquiv
  have hsubgroup :
      (Ideal.inertia G P).subgroupOf (MulAction.stabilizer G P) =
        Ideal.inertia (MulAction.stabilizer G P) P :=
    AddSubgroup.subgroupOf_inertia P.toAddSubgroup
      (MulAction.stabilizer G P)
  have hcardInertia :
      Nat.card (Ideal.inertia (MulAction.stabilizer G P) P) =
        Nat.card (Ideal.inertia G P) := by
    rw [← hsubgroup]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv
  rw [Ideal.inertiaDeg_eq p P,
    ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField,
    ← hindex]
  calc
    Nat.card (MulAction.stabilizer G P) =
        Nat.card (Ideal.inertia (MulAction.stabilizer G P) P) *
          Subgroup.index (Ideal.inertia (MulAction.stabilizer G P) P) := by
      exact
        (Ideal.inertia
          (MulAction.stabilizer G P) P).card_mul_index.symm
    _ = Nat.card (Ideal.inertia G P) *
          Subgroup.index (Ideal.inertia (MulAction.stabilizer G P) P) := by
      rw [hcardInertia]

/-- Identifies the finite inertia cardinality with the ramification index
without assuming that the base residue field is perfect. -/
private theorem card_inertia_eq_ramificationIdxIn
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    [p.IsPrime] [p.IsMaximal] [P.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (Ideal.inertia G P) =
      Ideal.ramificationIdxIn p S := by
  have hstabilizer :=
    card_stabilizer_eq_inertia_mul_inertiaDeg
      (G := G) p P
  have hinertia :
      (p.primesOver S).ncard * Nat.card (Ideal.inertia G P) *
          P.inertiaDeg R =
        Nat.card G := by
    rw [mul_assoc, ← hstabilizer,
      ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
    simpa only [Nat.card_prod,
      Nat.card_coe_set_eq] using
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg p P G] at hinertia
  have htotal :
      (p.primesOver S).ncard *
          (Ideal.ramificationIdxIn p S * Ideal.inertiaDegIn p S) =
        Nat.card G := by
    exact
      Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have hmul :
      (p.primesOver S).ncard *
          (Nat.card (Ideal.inertia G P) * Ideal.inertiaDegIn p S) =
        (p.primesOver S).ncard *
          (Ideal.ramificationIdxIn p S * Ideal.inertiaDegIn p S) := by
    rw [← mul_assoc, hinertia, htotal]
  have hprimeCount : (p.primesOver S).ncard ≠ 0 := by
    grind [Nat.card_pos]
  have hinertiaDegree : Ideal.inertiaDegIn p S ≠ 0 :=
    Ideal.inertiaDegIn_ne_zero G
  have hcancelPrime :=
    Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero hprimeCount) hmul
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero hinertiaDegree) hcancelPrime

/-- The literal ramification index of L/(L^H) is the cardinality of the
zeroth subgroup induced on H by the canonical general-DVF depth. -/
theorem fixedFieldRamificationIndex_eq_card_depthLowerFiltration_zero
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (H : Subgroup Gal(L/K)) [H.Normal] :
    fixedFieldRamificationIndex
        (target := target) H =
      Nat.card
        (((ramificationNumberDepthOfUniqueExtension
          (base := base) (target := target) huniq).depthLowerFiltration H).lower 0) := by
  let M := fixedFieldDVF (K := K) H
  let B := fixedFieldValuationSubringDVF (K := K) (target := target) H
  let O := target.valuationSubring
  let j := fixedFieldValuationSubringDVFToTarget
    (K := K) (target := target) H
  let p := IsLocalRing.maximalIdeal B
  let P := target.maximalIdeal
  let : IsDiscreteValuationRing B :=
    fixedFieldValuationSubringDVF_isDiscreteValuationRing
      (base := base) (target := target) huniq H
  let algBM : Algebra B M := B.subtype.toAlgebra
  let : IsFractionRing B M := by
    apply
      isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    · intro z
      rcases B.mem_or_inv_mem z with hz | hz
      · exact ⟨⟨z, hz⟩, Or.inl rfl⟩
      · exact ⟨⟨z⁻¹, hz⟩, Or.inr rfl⟩
    · intro a b hab
      exact Subtype.ext hab
  let : Algebra B O := j.toAlgebra
  let algBL : Algebra B L :=
    ((algebraMap O L).comp j).toAlgebra
  let : IsScalarTower B O L := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let : IsScalarTower B M L := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let : IsScalarTower base.valuationSubring B L := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let : IsScalarTower base.valuationSubring B O := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    rfl
  let : Algebra.IsIntegral base.valuationSubring O :=
    target_valuationSubring_isIntegral_of_uniqueExtension
      (base := base) (target := target) huniq
  let : Algebra.IsIntegral base.valuationSubring B :=
    fixedFieldValuationSubringDVF_isIntegral
      (base := base) (target := target) huniq H
  let : Algebra.IsIntegral B O :=
    Algebra.IsIntegral.tower_top base.valuationSubring
  let : IsIntegralClosure O B L := by
    let : IsIntegralClosure O base.valuationSubring L :=
      target_valuationSubring_isIntegralClosure_of_uniqueExtension
        (base := base) (target := target) huniq
    exact IsIntegralClosure.tower_top
      (R := base.valuationSubring) (A := B) (B := L) (C := O)
  let : Module.Finite base.valuationSubring O :=
    target_valuationSubring_moduleFinite_of_uniqueExtension
      (base := base) (target := target) huniq
  let : Module.Finite B O :=
    Module.Finite.of_restrictScalars_finite base.valuationSubring B O
  let : FaithfulSMul B L :=
    FaithfulSMul.of_field_isFractionRing B L M L
  let : Module.IsTorsionFree B L :=
    FaithfulSMul.to_isTorsionFree (R := B) (A := L)
  let : Module.IsTorsionFree B O :=
    IsIntegralClosure.isTorsionFree B L
  let : IsLocalHom (algebraMap B O) := by
    refine ⟨?_⟩
    intro a ha
    exact
      (isUnit_fixedFieldValuationSubringDVFToTarget_iff
        (K := K) (target := target) H a).mp ha
  let : IsLocalHom (algebraMap base.valuationSubring B) := by
    apply (algebraMap_isIntegral_iff.mpr
      (show Algebra.IsIntegral base.valuationSubring B from inferInstance)).isLocalHom
    intro a b hab
    apply Subtype.ext
    apply (algebraMap K M).injective
    exact congrArg Subtype.val hab
  let : MulSemiringAction H O :=
    MulSemiringAction.compHom (R := O)
      (fixedFieldTopValuationSubringActionHomDVF
        (base := base) (target := target) huniq H)
  let : SMulDistribClass H O L :=
    { smul_distrib_smul := by
        intro tau a y
        change (tau : Gal(L/K)) ((a : L) * y) =
          ((tau : Gal(L/K)) (a : L)) * (tau : Gal(L/K)) y
        rw [map_mul] }
  let : IsGaloisGroup H M L := by
    change IsGaloisGroup H
      (FixedPoints.intermediateField H : IntermediateField K L) L
    infer_instance
  let : IsGaloisGroup H B O :=
    IsGaloisGroup.of_isFractionRing H B O M L
  let : P.LiesOver p := inferInstance
  let : Algebra.IsSeparable (IsLocalRing.ResidueField B)
      target.residueField :=
    Algebra.isSeparable_tower_top_of_isSeparable
      base.residueField (IsLocalRing.ResidueField B) target.residueField
  let : Algebra.IsSeparable (B ⧸ p) (O ⧸ P) := by
    change Algebra.IsSeparable (IsLocalRing.ResidueField B)
      target.residueField
    infer_instance
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  rw [depthLowerFiltration_zero_eq_fixedFieldInertiaSubgroupDVF
    (base := base) (target := target) huniq H]
  change
    Ideal.ramificationIdx' p P =
      Nat.card (P.toAddSubgroup.inertia H)
  symm
  calc
    Nat.card (P.toAddSubgroup.inertia H) =
        Ideal.ramificationIdxIn p O :=
      card_inertia_eq_ramificationIdxIn
        (G := H) p P
    _ = P.ramificationIdx B :=
      Ideal.ramificationIdxIn_eq_ramificationIdx p P H
    _ = Ideal.ramificationIdx' p P :=
      (Ideal.ramificationIdx'_eq_ramificationIdx p P hp0).symm

end Higher
end RamificationTheory.HilbertRamification

end
