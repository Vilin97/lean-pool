/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.DivisorialVisibleFrameCore
import LeanPool.Stafford38.Stafford38.Geometry.DivisorialVisibleFrameStage2
import LeanPool.Stafford38.Stafford38.Geometry.DivisorialVisibleFrameStage4
import LeanPool.Stafford38.Stafford38.Geometry.DivisorialVisibleFrameStage5

/-!
Assembly of the verified affine, residue-field, and valuation stages of a visible frame.
-/

open IsLocalRing Polynomial
open Stafford38.Geometry.NormalizationHeightOne

noncomputable section

universe u v

namespace Stafford38.Geometry.LaneC

theorem stage2_of_verified : Stage2Obligation.{u} := by
  intro k K _ _ _ _ r y i hgen hx
  exact DivisorialVisibleFrameStage2.stage2_exists_chart_normalization y i hgen hx

theorem stage4_of_verified : Stage4Obligation.{u, v} := by
  intro k K _ _ _ A p _ V _ _ _ hAV hp hsurj _ι c hc hint
  exact DivisorialVisibleFrameStage4.stage4_residueField_isAlgebraic_of_isIntegral
    A p V hAV hp hsurj c hc hint

theorem stage5_of_verified : Stage5Obligation.{u} := by
  intro k K _ _ _ A hAft p _ V _ hAV hp hsurj
  obtain ⟨E, hEV, hfin⟩ :=
    DivisorialVisibleFrameStage5.stage5_exists_coefficientField A p V hAV hp hsurj
  refine ⟨E, hEV, ?_⟩
  let scratch : Algebra E V.toSubring :=
    (DivisorialVisibleFrameStage5.coeffHom E V hEV).toAlgebra
  let lane : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
  have heq : scratch = lane := by
    apply Algebra.algebra_ext
    intro z
    rfl
  cases heq
  exact hfin

theorem divisorialVisibleFrameExistence : DivisorialVisibleFrameExistence.{u} := by
  intro k K _ _ _ _ r y i hgen hx
  let S2 := assembly_scaffold_of_obligations stage2_of_verified
    stage4_of_verified stage5_of_verified
  obtain ⟨j, s, A, hs, hjs, hnormA, hyA, hAft, hAic, hAfr, haint, hinvA⟩ :=
    S2.stage2 y i hgen hx
  let : Algebra.FiniteType k A := hAft
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsFractionRing A K := hAfr
  let : IsIntegrallyClosedIn A K := hAic
  let : IsIntegrallyClosed A :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr hAic
  let xA : A := ⟨y i, hyA⟩
  have hy0 : y i ≠ 0 := by
    intro h
    exact hx (h ▸ isAlgebraic_zero)
  have hxA0 : xA ≠ 0 := by
    intro h
    apply hy0
    exact congrArg Subtype.val h
  have hxAu : ¬ IsUnit xA := by
    intro hu
    obtain ⟨z, hz⟩ := (isUnit_iff_exists_inv.mp hu)
    have hzK : (y i) * (z : K) = 1 := by
      exact congrArg Subtype.val hz
    have hzInv : (y i)⁻¹ = (z : K) := by
      simpa using congrArg Inv.inv (eq_inv_of_mul_eq_one_left hzK)
    apply hinvA
    rw [hzInv]
    exact z.property
  obtain ⟨p, hp, hpheight, hxp, hplace⟩ :=
    stage3_exists_height_one_prime_valuation A xA hxA0 hxAu
  let : p.IsPrime := hp
  let V : ValuationSubring K := placeValuationSubring A p hplace
  let : IsLocalization.AtPrime (placeSubalgebra A p) p := by
    unfold placeSubalgebra
    infer_instance
  have hVdvr : IsDiscreteValuationRing V.toSubring := by
    change IsDiscreteValuationRing (placeSubalgebra A p).toSubring
    exact isDiscreteValuationRing_of_isLocalization_atPrime p hpheight
      (placeSubalgebra A p)
  let : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  have hAV : ∀ a : A, (a : K) ∈ V.toSubring :=
    fun a => ofField_mem_algebraMap_v A p hplace a
  have hpV : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈
      maximalIdeal V.toSubring ↔ a ∈ p :=
    fun a => ofField_mem_maximalIdeal_iff_v A p hplace a
  have hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ /
        residue V.toSubring ⟨b, hAV b⟩ :=
    fun z => ofField_residue_surjective_v A p hplace z
  have hxV : y i ∈ V.toSubring := by
    exact ofField_mem_algebraMap_v A p hplace xA
  have hxm : (⟨y i, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring := by
    apply (hpV xA).2
    exact hxp
  obtain ⟨E, hEV, hEfin⟩ := S2.stage5 A p V hAV hpV hsurj
  let : Algebra E V.toSubring := (coeffHom E V hEV).toAlgebra
  have htrans : Transcendental E (y i) :=
    stage6_transcendental_of_mem_maximalIdeal E V hEV (y i) hy0 hxV hxm
  have hk : ∀ c : k, algebraMap k K c ∈ (placeSubalgebra A p).toSubring :=
    fun c => by
      change algebraMap k K c ∈ V.toSubring
      have heq : algebraMap k K c =
          (algebraMap (↥A) K) (algebraMap k A c) :=
        (IsScalarTower.algebraMap_apply k A K c).symm
      rw [heq]
      exact hAV (algebraMap k A c)
  let cod : Algebra k V.toSubring :=
    ((algebraMap k K).codRestrict _ hk).toAlgebra
  let : Algebra k V.toSubring := cod
  have hkaehlerCod : Module.Finite V.toSubring
      (Ω[V.toSubring⁄k]) := by
    exact stage7_kaehler_finite_ofField A p hk
  let ground : Algebra k V.toSubring := (groundHom E V hEV).toAlgebra
  have hcod_ground : cod = ground := by
    apply Algebra.algebra_ext
    intro c
    apply Subtype.ext
    rfl
  let : Algebra k V.toSubring := ground
  let : IsScalarTower k V.toSubring K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k K c = algebraMap k K c
      rfl
  have hkaehler : Module.Finite V.toSubring
      (Ω[V.toSubring⁄k]) := by
    cases hcod_ground
    exact hkaehlerCod
  let c : Fin (r + 1) → V.toSubring := fun a =>
    ⟨(Fin.cases 1 y a : K) * s,
      hAV ⟨(Fin.cases 1 y a : K) * s, hnormA a⟩⟩
  have hc : ∀ a, (c a : K) = (Fin.cases 1 y a : K) * s :=
    fun a => rfl
  have hcj : c j = 1 := by
    apply Subtype.ext
    exact hjs
  have halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a => residue V.toSubring (c a)) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring) := by
    let c' : (Fin (r + 1) ⊕ Unit) → K := fun a =>
      match a with
      | Sum.inl b => (Fin.cases 1 y b : K) * s
      | Sum.inr _ => y i
    have hset : Set.range c' =
        Set.range (fun a : Fin (r + 1) => (Fin.cases 1 y a : K) * s) ∪ {y i} := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        cases a with
        | inl b => exact Or.inl ⟨b, rfl⟩
        | inr u => exact Or.inr (Set.mem_singleton _)
      · intro hz
        rcases hz with ⟨b, rfl⟩ | rfl
        · exact ⟨Sum.inl b, rfl⟩
        · exact ⟨Sum.inr (), rfl⟩
    have hBig : Algebra.IsAlgebraic
        (IntermediateField.adjoin k (Set.range fun a =>
          residue V.toSubring ⟨c' a, by
            cases a with
            | inl b => exact hAV ⟨c' (Sum.inl b), hnormA b⟩
            | inr _ => exact hAV xA⟩) :
          IntermediateField k (ResidueField V.toSubring))
        (ResidueField V.toSubring) := by
      apply S2.stage4 A p V hAV hpV hsurj c'
      · intro a
        cases a with
        | inl b => exact hnormA b
        | inr _ => exact hyA
      · intro a
        rw [hset]
        exact haint a
    have hyres : residue V.toSubring (⟨y i, hxV⟩ : V.toSubring) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 hxm
    have hEq : IntermediateField.adjoin k (Set.range fun a =>
          residue V.toSubring ⟨c' a, by
            cases a with
            | inl b => exact hAV ⟨c' (Sum.inl b), hnormA b⟩
            | inr _ => exact hAV xA⟩) =
        IntermediateField.adjoin k (Set.range fun a => residue V.toSubring (c a)) := by
      apply le_antisymm
      · apply IntermediateField.adjoin_le_iff.mpr
        rintro z ⟨a, rfl⟩
        cases a with
        | inl b => exact IntermediateField.subset_adjoin k _ ⟨b, rfl⟩
        | inr _ =>
          change residue V.toSubring (⟨y i, hxV⟩ : V.toSubring) ∈
            (IntermediateField.adjoin k
              (Set.range fun a => residue V.toSubring (c a)))
          rw [hyres]
          exact (IntermediateField.adjoin k
            (Set.range fun a => residue V.toSubring (c a))).zero_mem
      · apply IntermediateField.adjoin_le_iff.mpr
        rintro z ⟨b, rfl⟩
        exact IntermediateField.subset_adjoin k _ ⟨Sum.inl b, rfl⟩
    rw [← hEq]
    exact hBig
  refine ⟨E, V, hEV, hVdvr, hxV, htrans, hxm, hEfin, hkaehler, ?_⟩
  intro s' q hq hq1 hq0
  by_cases hj0 : j = 0
  · obtain ⟨j', hj'⟩ := hq1
    exfalso
    have hsone : s = 1 := by simpa [hj0] using hjs
    have hprod : ∀ a, q a = q 0 * c a := by
      intro a
      apply Subtype.ext
      change (q a : K) = (q 0 : K) * (c a : K)
      rw [hq a, hq 0, hc a]
      simp [hsone]
    have hq0res : residue V.toSubring (q 0) = 0 := by
      by_contra hnz
      exact hq0 ((residue_ne_zero_iff_isUnit _).1 hnz)
    have hqjres : residue V.toSubring (q j') = 0 := by
      rw [hprod j', map_mul, hq0res, zero_mul]
    have hqjunit : IsUnit (q j') := by rw [hj']; exact isUnit_one
    exact ((residue_ne_zero_iff_isUnit _).2 hqjunit) hqjres
  · exact DivisorialVisibleFrameStage4.stage4'_isAlgebraic_of_normalized_column
      V y j hj0 s c hc hcj halg
      s' q hq hq1 hq0

end Stafford38.Geometry.LaneC
