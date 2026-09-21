/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.FinitePlaceDecomposition
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.RestrictionKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.BasePlaceSelection
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.CoordinatePlaces
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.PrimeSet
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.DecompositionFields
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.Conclusion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
/-!
# S-unit localization modulo local powers

This module constructs the localization map from an S-unit group to the
finite product of local unit power classes and proves its kernel and
surjectivity properties for the Kummer prime set.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The unit-valued localization map
`Kˢ → ∏ v ∈ T, U_v / U_vⁿ`.  Disjointness makes every `S`-unit an
integral unit at the places in `T`. -/
def sUnitLocalUnitPowerMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    SUnitGroup (K := K) S →*
      ∀ v : T,
        (v.1.adicCompletionIntegers K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v.1.adicCompletionIntegers K)ˣ →*
              (v.1.adicCompletionIntegers K)ˣ).range :=
  MonoidHom.pi fun v =>
    let localPrincipal :
        SUnitGroup (K := K) S →* (v.1.adicCompletion K)ˣ :=
      ((IdeleGroup.finiteComponent v.1).comp
        (IdeleGroup.principalIdele K)).comp
          (SUnitGroup (K := K) S).subtype
    let localPrincipalUnit :
        SUnitGroup (K := K) S →*
          (v.1.adicCompletionIntegers K).units :=
      localPrincipal.codRestrict
        (v.1.adicCompletionIntegers K).units
        (fun x => by
          have hvS : v.1 ∉ S := by
            intro hvS
            exact (Finset.disjoint_left.mp hST) hvS v.2
          rw [
            HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
          change
            Valued.v
                (((IdeleGroup.finiteComponent v.1
                    (IdeleGroup.principalIdele K (x : Kˣ)) :
                      (v.1.adicCompletion K)ˣ) :
                  v.1.adicCompletion K)) =
              1
          rw [IdeleGroup.finiteComponent_principalIdele,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
          exact
            (mem_SUnitGroup_iff (K := K) S x).mp
              x.2 v.1 hvS)
    (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletionIntegers K)ˣ →*
            (v.1.adicCompletionIntegers K)ˣ).range).comp
      ((v.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom.comp
        localPrincipalUnit)

/-- An integral unit in an adic completion is an `n`-th power among
integral units exactly when it is an `n`-th power among field units. -/
theorem mem_powMonoidHom_range_adicCompletionIntegers_iff
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ+)
    (x : (v.adicCompletionIntegers K)ˣ) :
    x ∈ (powMonoidHom (n : ℕ) :
          (v.adicCompletionIntegers K)ˣ →*
            (v.adicCompletionIntegers K)ˣ).range ↔
      Units.map
          (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K)).toMonoidHom x ∈
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletionIntegers K)ˣ)).mp hx
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine ⟨Units.map
      (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom y, ?_⟩
    rw [powMonoidHom_apply] at hy ⊢
    rw [← map_pow, hy]
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mp hx
    rw [powMonoidHom_apply] at hy
    have hxVal :
        Valued.v
            (((Units.map
              (algebraMap (v.adicCompletionIntegers K)
                (v.adicCompletion K)).toMonoidHom x :
                  (v.adicCompletion K)ˣ) :
                v.adicCompletion K)) =
          1 :=
      (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := K) (v := v)).mp x.isUnit
    have hyValPow :
        Valued.v (((y ^ (n : ℕ) : (v.adicCompletion K)ˣ) :
          v.adicCompletion K)) = 1 := by
      rw [hy]
      exact hxVal
    have hyValPow' :
        Valued.v ((y : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) ^ (n : ℕ) = 1 := by
      rw [Units.val_pow_eq_pow_val] at hyValPow
      rw [map_pow] at hyValPow
      exact hyValPow
    have hyVal :
        Valued.v ((y : (v.adicCompletion K)ˣ) :
            v.adicCompletion K) = 1 :=
      (pow_left_injective
        (M := WithZero (Multiplicative ℤ))
        (n := (n : ℕ)) n.ne_zero)
          (by simpa only [one_pow] using hyValPow')
    let yO : v.adicCompletionIntegers K :=
      ⟨(y : v.adicCompletion K), hyVal.le⟩
    have hyOUnit : IsUnit yO :=
      Valuation.Integers.isUnit_of_one'
        (HeightOneSpectrum.adicCompletionIntegers.integers K v) (by
          change
            Valued.v ((y : (v.adicCompletion K)ˣ) :
              v.adicCompletion K) = 1
          exact hyVal)
    obtain ⟨z, hz⟩ := hyOUnit
    have hzField :
        Units.map
            (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K)).toMonoidHom z =
          y := by
      apply Units.ext
      change ((z : v.adicCompletionIntegers K) :
        v.adicCompletion K) = (y : v.adicCompletion K)
      rw [hz]
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletionIntegers K)ˣ)).mpr
    refine ⟨z, ?_⟩
    rw [powMonoidHom_apply]
    apply Units.map_injective
      (f := (algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K)).toMonoidHom)
      (FaithfulSMul.algebraMap_injective
        (v.adicCompletionIntegers K)
        (v.adicCompletion K))
    rw [map_pow, hzField, hy]

/-- The unit-valued localization map and the field-valued localization map
defining `Δ` have the same kernel. -/
theorem sUnitLocalUnitPowerMap_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    (sUnitLocalUnitPowerMap (K := K) n S T hST).ker =
      sUnitLocalPowerKernel (K := K) n S T := by
  ext x
  let localUnit (v : T) :
      (v.1.adicCompletionIntegers K)ˣ :=
    (v.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
      ⟨IdeleGroup.finiteComponent v.1
          (IdeleGroup.principalIdele K (x : Kˣ)), by
        have hvS : v.1 ∉ S := by
          intro hvS
          exact (Finset.disjoint_left.mp hST) hvS v.2
        rw [
          HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
        rw [IdeleGroup.finiteComponent_principalIdele,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact
          (mem_SUnitGroup_iff (K := K) S x).mp
            x.2 v.1 hvS⟩
  have localUnit_toField (v : T) :
      Units.map
          (algebraMap (v.1.adicCompletionIntegers K)
            (v.1.adicCompletion K)).toMonoidHom (localUnit v) =
        Units.map
          (algebraMap K (v.1.adicCompletion K)).toMonoidHom
          (x : Kˣ) := by
    apply Units.ext
    rfl
  rw [mem_sUnitLocalPowerKernel_iff, MonoidHom.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    rw [Pi.one_apply] at hv
    change QuotientGroup.mk' _ (localUnit v) = 1 at hv
    have hvInteger :=
      (QuotientGroup.eq_one_iff (localUnit v)).mp hv
    have hvField :=
      (mem_powMonoidHom_range_adicCompletionIntegers_iff
        v.1 n (localUnit v)).mp hvInteger
    rw [localUnit_toField v] at hvField
    exact hvField
  · intro hx
    funext v
    rw [Pi.one_apply]
    change QuotientGroup.mk' _ (localUnit v) = 1
    apply (QuotientGroup.eq_one_iff (localUnit v)).mpr
    apply
      (mem_powMonoidHom_range_adicCompletionIntegers_iff
        v.1 n (localUnit v)).mpr
    rw [localUnit_toField v]
    exact hx v

/-- For the Kummer-selected primes, localization from the enlarged `S`-unit
group onto the product of integral-unit power quotients is
surjective.  The proof compares the actual Kummer radical quotient with
`Gal(E/K)` and uses the local unit-index formula only at the end. -/
theorem sUnitLocalUnitPowerMap_sUnitKummerPrimeSet_surjective
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S
    let T :=
      sUnitKummerPrimeSet
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
    let hST : Disjoint S' T :=
      (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S).symm
    Function.Surjective
      (sUnitLocalUnitPowerMap (K := K) n S' T hST) := by
  classical
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let T :=
    sUnitKummerPrimeSet
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let hST : Disjoint S' T :=
    (sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S).symm
  let LocalPowerTarget : Type :=
    ∀ w : T,
      (w.1.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom (n : ℕ) :
          (w.1.adicCompletionIntegers K)ˣ →*
            (w.1.adicCompletionIntegers K)ˣ).range
  let f : SUnitGroup (K := K) S' →* LocalPowerTarget :=
    sUnitLocalUnitPowerMap (K := K) n S' T hST
  let rangeF : Subgroup LocalPowerTarget :=
    MonoidHom.range
      (G := SUnitGroup (K := K) S') (N := LocalPowerTarget) f
  let SU : Subgroup Kˣ :=
    SUnitGroup (K := K) S'
  let Delta : Subgroup SU :=
    sUnitLocalPowerKernel (K := K) n S' T
  let P : Subgroup SU :=
    (powMonoidHom (n : ℕ) : SU →* SU).range
  let H : Subgroup Kˣ :=
    sUnitFiniteKummerRadical
      (K := K) (L := E) n S'
  let Npow : Subgroup Kˣ :=
    KummerTheory.unitNthPowersSubgroup K n
  let D :=
    KummerTheory.chosenFiniteKummerRadicalDatum
      (K := K) (L := E) n
  change Function.Surjective f
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hDeltaEq :
      Delta = H.subgroupOf SU := by
    change
      sUnitLocalPowerKernel (K := K) n S' T =
        (sUnitFiniteKummerRadical
          (K := K) (L := E) n S').comap
            (SUnitGroup (K := K) S').subtype
    exact
      sUnitLocalPowerKernel_sUnitKummerPrimeSet_eq_comap_sUnitFiniteKummerRadical
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S
  have hP :
      P = Npow.subgroupOf SU := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ :=
        (MonoidHom.mem_range
          (G := SU)).mp hx
      rw [powMonoidHom_apply] at hy
      change (x : Kˣ) ∈ Npow
      apply
        (KummerTheory.mem_unitNthPowersSubgroup_iff n).mpr
      refine ⟨(y : Kˣ), ?_⟩
      exact congrArg (fun z : SU => (z : Kˣ)) hy
    · intro hx
      change (x : Kˣ) ∈ Npow at hx
      obtain ⟨y, hy⟩ :=
        (KummerTheory.mem_unitNthPowersSubgroup_iff n).mp hx
      have hySU : y ∈ SU :=
        mem_sUnitGroup_of_pow_mem
          (K := K) S' n y (by
            rw [hy]
            exact x.property)
      let ySU : SU := ⟨y, hySU⟩
      apply
        (MonoidHom.mem_range
          (G := SU)).mpr
      refine ⟨ySU, ?_⟩
      rw [powMonoidHom_apply]
      apply Subtype.ext
      exact hy
  have hHle : H ≤ SU := by
    exact inf_le_left
  have hsup :
      H ⊔ Npow = D.carrier := by
    change
      (sUnitKummerSubgroup
        (K := K) (L := E) n S').1 =
          KummerTheory.finiteKummerRadicalSubgroup
            (K := K) (L := E) n
    exact
      enlargedSUnitKummerSubgroup_eq_finiteKummerRadicalSubgroup
        (K := K) (L := E) n hmu S
  let eDelta :
      Delta ⧸ P.subgroupOf Delta ≃*
        H.subgroupOf SU ⧸
          P.subgroupOf (H.subgroupOf SU) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      rfl hDeltaEq
  let ePower :
      H.subgroupOf SU ⧸
          P.subgroupOf (H.subgroupOf SU) ≃*
        H.subgroupOf SU ⧸
          (Npow.subgroupOf SU).subgroupOf
            (H.subgroupOf SU) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      hP rfl
  let eH :
      H.subgroupOf SU ≃* H :=
    Subgroup.subgroupOfEquivOfLe hHle
  have hmap :
      ((Npow.subgroupOf SU).subgroupOf
          (H.subgroupOf SU)).map eH =
        Npow.subgroupOf H := by
    rw [Subgroup.map_equiv_eq_comap_symm]
    rfl
  let eInside :
      H.subgroupOf SU ⧸
          (Npow.subgroupOf SU).subgroupOf
            (H.subgroupOf SU) ≃*
        H ⧸ Npow.subgroupOf H :=
    QuotientGroup.congr _ _ eH hmap
  let eSecond :
      H ⧸ Npow.subgroupOf H ≃*
        (H ⊔ Npow : Subgroup Kˣ) ⧸
          Npow.subgroupOf (H ⊔ Npow) :=
    QuotientGroup.quotientInfEquivProdNormalQuotient
      H Npow
  let eRadicalCarrier :
      (H ⊔ Npow : Subgroup Kˣ) ⧸
          Npow.subgroupOf (H ⊔ Npow) ≃*
        D.carrier ⧸ Npow.subgroupOf D.carrier :=
    QuotientGroup.equivQuotientSubgroupOfOfEq
      rfl hsup
  have hden :
      Npow.subgroupOf D.carrier =
        D.ambientNthPowersSubgroup := by
    rfl
  let eNamedRadical :
      D.carrier ⧸ Npow.subgroupOf D.carrier ≃*
        D.RadicalQuotient :=
    (QuotientGroup.quotientMulEquivOfEq hden).trans
      D.radicalQuotientMulEquiv.symm
  let : CommGroup Gal(E/K) := by
    infer_instance
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod
      (K := K) E n r eG
  let hbase :
      KummerTheory.NthRootsOfUnityInBase
        (K := K) (L := E) n :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := E) n hmu
  let eKummer :
      D.RadicalQuotient ≃*
        (Gal(E/K) →*
          KummerTheory.nthRootsSubgroup E (n : ℕ)) :=
    KummerTheory.finiteKummerCharacterEquiv
      n hbase
  let eDual :
      (Gal(E/K) →*
          KummerTheory.nthRootsSubgroup E (n : ℕ)) ≃*
        Gal(E/K) :=
    Classical.choice <|
      KummerTheory.finiteNthRootsCharacterDuality
        (G := Gal(E/K)) (K := K) (L := E)
        n hmu hexponentE
  let eQuotient :
      Delta ⧸ P.subgroupOf Delta ≃*
        Gal(E/K) :=
    eDelta.trans
      (ePower.trans
        (eInside.trans
          (eSecond.trans
            (eRadicalCarrier.trans
              (eNamedRadical.trans
                (eKummer.trans eDual))))))
  have hDeltaCard :
      Nat.card
          (Delta ⧸
            sUnitLocalPowerKernelNthPowers
              (K := K) n S' T) =
        (n : ℕ) ^ r := by
    change
      Nat.card (Delta ⧸ P.subgroupOf Delta) =
        (n : ℕ) ^ r
    calc
      Nat.card (Delta ⧸ P.subgroupOf Delta) =
          Nat.card Gal(E/K) :=
        Nat.card_congr eQuotient.toEquiv
      _ = (n : ℕ) ^ r := by
        rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
        simp
  have hPLe : P ≤ Delta :=
    nthPowerSubgroup_le_sUnitLocalPowerKernel
      (K := K) n S' T
  have hRel :
      P.relIndex Delta = (n : ℕ) ^ r := by
    change
      Nat.card
          (Delta ⧸
            sUnitLocalPowerKernelNthPowers
              (K := K) n S' T) =
        (n : ℕ) ^ r
    exact hDeltaCard
  have hPIndex :
      P.index =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    change
      Nat.card
          (SUnitGroup (K := K) S' ⧸
            (powMonoidHom (n : ℕ) :
              SUnitGroup (K := K) S' →*
                SUnitGroup (K := K) S').range) =
        (n : ℕ) ^ totalPlaceCard (K := K) S'
    exact
      card_sUnit_nthPowerQuotient
        (K := K) S' n hmu
  have hIndexFactor :
      (n : ℕ) ^ r * Delta.index =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    rw [← hRel, ← hPIndex]
    exact Subgroup.relIndex_mul_index hPLe
  have hr :
      r ≤ totalPlaceCard (K := K) S' :=
    galoisRank_le_totalPlaceCard_enlargedS
      (K := K) (Omega := Omega) E n hnOne hmu
      r eG S
  have hsplit :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hDeltaIndex :
      Delta.index =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    have hcancel :
        (n : ℕ) ^ r * Delta.index =
          (n : ℕ) ^ r *
            (n : ℕ) ^
              (totalPlaceCard (K := K) S' - r) :=
      hIndexFactor.trans hsplit
    exact
      Nat.eq_of_mul_eq_mul_left
        (pow_pos n.pos r) hcancel
  have hfker :
      f.ker = Delta := by
    change
      (sUnitLocalUnitPowerMap
        (K := K) n S' T hST).ker =
          sUnitLocalPowerKernel (K := K) n S' T
    exact
      sUnitLocalUnitPowerMap_ker
        (K := K) n S' T hST
  have hRangeCard :
      Nat.card rangeF =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    rw [← Subgroup.index_ker
      (G := SUnitGroup (K := K) S') (G' := LocalPowerTarget) f, hfker]
    exact hDeltaIndex
  have hLocalCard
      (w : T) :
      Nat.card
          ((w.1.adicCompletionIntegers K)ˣ ⧸
            (powMonoidHom (n : ℕ) :
              (w.1.adicCompletionIntegers K)ˣ →*
                (w.1.adicCompletionIntegers K)ˣ).range) =
        (n : ℕ) := by
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
        (Valued.v :
          Valuation (w.1.adicCompletion K)
            (WithZero (Multiplicative ℤ)))
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    have hnu : Function.Surjective
        (Valued.v :
          Valuation (w.1.adicCompletion K)
            (WithZero (Multiplicative ℤ))) :=
      w.1.valuedAdicCompletion_surjective K
    have hw :
        w.1 ∈
          sUnitKummerPrimeSet
            (K := K) (Omega := Omega) E n hmu
            p v hp hv hn r eG S :=
      w.2
    rw [sUnitKummerPrimeSet, Finset.mem_image] at hw
    obtain ⟨i, _hi, hi⟩ := hw
    have hnGlobal :
        w.1.valuation K ((n : ℕ) : K) = 1 := by
      rw [← hi]
      exact
        sUnitKummerChosenBasePlaces_valuation_natCast_eq_one
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i
    have hnatCast :
        (((n : ℕ) : K) : w.1.adicCompletion K) =
          ((n : ℕ) : w.1.adicCompletion K) := by
      change
        algebraMap K (w.1.adicCompletion K) ((n : ℕ) : K) =
          ((n : ℕ) : w.1.adicCompletion K)
      rw [map_natCast]
    have hnuN :
        Valued.v ((n : ℕ) : w.1.adicCompletion K) = 1 := by
      rw [← hnatCast,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hnGlobal
    have hnuNF :
        F.valuation ((n : ℕ) : w.1.adicCompletion K) = 1 := by
      dsimp only [F]
      unfold
        LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      unfold
        LocalFieldTheory.DiscreteValuationField.LocalField.coherentWithZeroMultiplicativeIntGroup
      exact hnuN
    have hpnd :
        ¬ F.residueCharacteristic ∣ (n : ℕ) := by
      rw [←
        F.valuation_natCast_lt_one_iff_residueCharacteristic_dvd]
      rw [hnuNF]
      exact lt_irrefl 1
    let :
        Fact
          (Nat.Coprime (n : ℕ)
            F.residueCharacteristic) :=
      ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr
        hpnd).symm⟩
    let eValuationSubringUnits :
        F.valuationSubringˣ ≃*
          (w.1.adicCompletionIntegers K)ˣ := by
      exact MulEquiv.refl ((w.1.adicCompletionIntegers K)ˣ)
    have hindexPackaged :
        Nat.card
            (F.valuationSubringˣ ⧸
              (powMonoidHom (n : ℕ) :
                F.valuationSubringˣ →* F.valuationSubringˣ).range) =
          Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) := by
      simpa only [F] using
        LocalFieldTheory.DiscreteValuationField.LocalField.mixed_unitIndex_of_coprime
          (Valued.v :
            Valuation (w.1.adicCompletion K)
              (WithZero (Multiplicative ℤ)))
          hnu (n := (n : ℕ))
    have hindex :
        Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
          Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) := by
      calc
        Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
            Nat.card
              (F.valuationSubringˣ ⧸
                (powMonoidHom (n : ℕ) :
                  F.valuationSubringˣ →* F.valuationSubringˣ).range) := by
          exact Nat.card_congr
            (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv
              (w.1.adicCompletionIntegers K)ˣ
              F.valuationSubringˣ
              (n : ℕ)
              eValuationSubringUnits.symm).toEquiv
        _ = Nat.card
              ((powMonoidHom (n : ℕ) :
                (w.1.adicCompletion K)ˣ →*
                  (w.1.adicCompletion K)ˣ).ker) :=
          hindexPackaged
    have hroots :
        Nat.card
            ((powMonoidHom (n : ℕ) :
              (w.1.adicCompletion K)ˣ →*
                (w.1.adicCompletion K)ˣ).ker) =
          (n : ℕ) := by
      rw [
        LocalFieldTheory.powMonoidHom_ker_units_eq_rootsOfUnity]
      obtain ⟨zeta, hzeta⟩ := hmu
      have hzetaPrimitive :
          IsPrimitiveRoot zeta (n : ℕ) :=
        (mem_primitiveRoots n.pos).mp hzeta
      exact
        (hzetaPrimitive.map_of_injective
          (algebraMap K
            (w.1.adicCompletion K)).injective).card_rootsOfUnity
    simpa only [hroots] using hindex
  have hTcard :
      T.card =
        sUnitKummerPrimeCount
          (K := K) E n hmu r S :=
    sUnitKummerPrimeSet_card
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  have hTargetCard :
      Nat.card
          (∀ w : T,
            (w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range) =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) := by
    rw [Nat.card_pi]
    calc
      (∏ w : T,
          Nat.card
            ((w.1.adicCompletionIntegers K)ˣ ⧸
              (powMonoidHom (n : ℕ) :
                (w.1.adicCompletionIntegers K)ˣ →*
                  (w.1.adicCompletionIntegers K)ˣ).range)) =
          ∏ _w : T, (n : ℕ) := by
        apply Finset.prod_congr rfl
        intro w _
        exact hLocalCard w
      _ = (n : ℕ) ^ T.card := by
        simp
      _ =
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
        rw [hTcard]
        rfl
  let : Finite rangeF :=
    Nat.finite_of_card_ne_zero (by
      rw [hRangeCard]
      exact pow_ne_zero _ n.ne_zero)
  have hRangeTop :
      rangeF = ⊤ :=
    Subgroup.eq_top_of_card_eq rangeF
      (hRangeCard.trans hTargetCard.symm)
  exact
    (MonoidHom.range_eq_top
      (G := SUnitGroup (K := K) S') (N := LocalPowerTarget) (f := f)).mp hRangeTop

end GlobalClassFieldTheory.ClassFieldAxiom
