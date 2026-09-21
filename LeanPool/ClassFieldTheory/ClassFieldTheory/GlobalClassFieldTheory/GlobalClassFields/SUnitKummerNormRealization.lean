/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormCore
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitKummerUnramified
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex
/-!
# Exact norm realization by the full S-unit Kummer extension

When the base field contains the required roots of unity, the full
S-unit Kummer extension realizes the canonical power-local-unit
subgroup exactly as its ordinary idele-class norm subgroup.  The forward
inclusion is the local norm theorem, using the actual unramifiedness of
the Kummer extension away from the canonical support.  Equality follows
from the independently computed quotient cardinal and the global
norm-residue index formula.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom
open KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- The full S-unit Kummer extension has ordinary idele-class norm range
equal to the canonical power-local-unit subgroup. -/
theorem fullSUnitKummerExtension_ideleClassNormRange_eq_powerLocalUnit
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    let S := sUnitKummerNormSupport (K := K) n seed
    let E :=
      KummerTheory.fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S
    letI : FiniteDimensional K E :=
      KummerTheory.fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n
        (by exact_mod_cast n.ne_zero) hmu S
    letI : IsGalois K E :=
      KummerTheory.fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S
    letI : NumberField E :=
      NumberField.of_module_finite K E
    (_root_.ideleClassNorm K E).range =
      ideleClassPowerLocalUnitSubgroup (K := K) n S ∅ := by
  classical
  dsimp only
  let S := sUnitKummerNormSupport (K := K) n seed
  let E :=
    KummerTheory.fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K E :=
    KummerTheory.fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S
  let : IsGalois K E :=
    KummerTheory.fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let : NumberField E :=
    NumberField.of_module_finite K E
  let r := totalPlaceCard (K := K) S
  let eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))) := by
    simpa only [E, r] using
      (KummerTheory.fullSUnitKummerExtensionGaloisEquivPiZMod
        (K := K) (Omega := Omega) n hnK hmu S)
  let : IsAbelianGalois K E :=
    { is_comm.comm := fun σ τ => by
        apply eG.injective
        simpa only [map_mul] using
          mul_comm (eG σ) (eG τ) }
  have harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal :=
    even_or_no_realInfinitePlace_of_primitiveRoots
      (K := K) n hmu hn
  have hAway :
      ∀ v, v ∉ S ∪ (∅ :
          Finset (HeightOneSpectrum (𝓞 K))) →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := E) v := by
    intro v hv
    have hvS : v ∉ S := by
      simpa only [Finset.union_empty] using hv
    have hnv :
        v.valuation K ((n : ℕ) : K) = 1 := by
      simpa only [S] using
        valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
          (K := K) n seed hvS
    simpa only [E] using
      (KummerTheory.fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
        (K := K) (Omega := Omega)
        n hnK hmu S v hvS hnv)
  have hPowerLeRelative :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅ ≤
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K E).range := by
    apply
      ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
        (K := K) (L := E) n r eG S ∅ harch
    · intro v hv
      simp at hv
    · exact hAway
  have hPowerLe :
      ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅ ≤
        (_root_.ideleClassNorm K E).range := by
    rw [
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := E)]
    exact hPowerLeRelative
  have hPowerIndex :
      (ideleClassPowerLocalUnitSubgroup
          (K := K) n S ∅).index =
        Module.finrank K E := by
    rw [Subgroup.index_eq_card]
    simpa only [S, E] using
      (card_ideleClassPowerLocalUnitQuotient_eq_finrank_fullSUnitKummerExtension
        (K := K) (Omega := Omega) n hmu seed)
  have hNormIndex :
      (_root_.ideleClassNorm K E).range.index =
        Module.finrank K E :=
    Reciprocity.ideleClassNorm_index_eq_finrank_abelian K E
  apply
    (LubinTate.subgroup_eq_of_le_of_index_eq_of_ne_zero
      hPowerLe (hPowerIndex.trans hNormIndex.symm)
      (by
        rw [hPowerIndex]
        exact Nat.ne_of_gt Module.finrank_pos)).symm

end GlobalClassFields
end GlobalClassFieldTheory
