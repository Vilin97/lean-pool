/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
/-!
# The normalized cyclotomic idele value

For a number field `K`, the actual cyclotomic `ZHat`-extension is the
compositum of the embedded copy of `K` with the rational cyclotomic
`ZHat`-extension.  Its normalization factor is the actual intersection degree

`f_K = [K ∩ ℚ_tilde : ℚ]`,

constructed in `CyclotomicZHatBaseChange`.

This file first constructs the idele-level map

`(1 / f_K) v_ℚ ∘ N_{K/ℚ} : I_K → ZHat`.

The factor `f_K` is removed only after proving that the unnormalized
value lies in the actual subgroup `f_K ZHat`.  This file stops at that
idele-level construction.  Descent from `I_K` to `C_K`, together with
the resulting integer-value and norm-range identities, requires the
genuine cyclotomic principal-idele formula and is the next
source-producing frontier; no quotient projection or abstract valuation
hypothesis is substituted for it here.
-/

@[expose] public section

noncomputable
section

open scoped Topology

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The rational infinite Artin homomorphism in the canonical
`Multiplicative ZHat` coordinate supplied by the cyclotomic Galois equivalence. -/
noncomputable def rationalCyclotomicZHatIdeleValue :
    IdeleGroup ℚ →ₜ* Multiplicative ZHat :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    rationalCyclotomicZHatFieldGalEquivZHat).comp
      rationalCyclotomicZHatGlobalArtin

/-- Evaluating the rational cyclotomic idele value applies the fixed
Galois-to-`ZHat` equivalence to the rational global Artin image. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValue_apply
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      rationalCyclotomicZHatFieldGalEquivZHat
        (rationalCyclotomicZHatGlobalArtin a) :=
  rfl

/-- The rational cyclotomic value has dense image in `ZHat`. -/
theorem rationalCyclotomicZHatIdeleValue_denseRange :
    DenseRange rationalCyclotomicZHatIdeleValue := by
  change
    DenseRange
      (fun a =>
        rationalCyclotomicZHatFieldGalEquivZHat
          (rationalCyclotomicZHatGlobalArtin a))
  exact
    rationalCyclotomicZHatFieldGalEquivZHat.surjective.denseRange.comp
      rationalCyclotomicZHatGlobalArtin_denseRange
      rationalCyclotomicZHatFieldGalEquivZHat.continuous

/-- The norm-one rational ideles already have dense image in the actual
cyclotomic `ZHat` coordinate.  This is the compact source used for
surjectivity after descent to the idele class group. -/
theorem rationalCyclotomicZHatIdeleValue_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatIdeleValue b) := by
  change
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatFieldGalEquivZHat
          (rationalCyclotomicZHatGlobalArtin b))
  exact
    rationalCyclotomicZHatFieldGalEquivZHat.surjective.denseRange.comp
      rationalCyclotomicZHatGlobalArtin_normOne_denseRange
      rationalCyclotomicZHatFieldGalEquivZHat.continuous

variable (K : Type) [Field K] [NumberField K]

local instance
    (E : FiniteGaloisIntermediateField
      ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois ℚ E :=
  IsAbelianGalois.of_algHom E.toIntermediateField.val

/-- On the actual cyclotomic compositum over `K`, the chosen
local-factor product restricts to the rational cyclotomic Artin symbol
of the ordinary idele norm. -/
@[simp]
theorem
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom
    (a : IdeleGroup K) :
    numberFieldCyclotomicZHatCompositumRestriction K
        (infiniteGlobalArtinMonoidHom K
          (numberFieldCyclotomicZHatCompositum K) a) =
      rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a) := by
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  let E := Eop.unop
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let P :=
    numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum K E
  let : NumberField P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField K E
  let : Algebra E P :=
    rationalCyclotomicZHatFiniteLayerInCompositumAlgebra K E
  let : SMul E P :=
    rationalCyclotomicZHatFiniteLayerInCompositumSmul K E
  let : Module E P := Algebra.toModule
  let : IsScalarTower ℚ E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower K E
  let : IsAbelianGalois K P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  have hcomm :
      (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K P).comp
          (globalArtinMonoidHom
            (K := K) (L := P)) =
        (globalArtinMonoidHom
          (K := ℚ) (L := E)).comp
            (IdeleGroup.norm ℚ K) := by
    have hr :
        IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P =
          (AlgEquiv.restrictNormalHom E).comp
            (AlgEquiv.restrictScalarsHom ℚ) := by
      ext σ x
      exact rfl
    rw [hr]
    exact
      globalArtinMonoidHom_norm_restriction
        (K := ℚ) (L := E)
        (K' := K)
        (L' := P)
  have hPProjection :
      AlgEquiv.restrictNormalHom P
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a) =
        globalArtinMonoidHom (K := K) (L := P) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (numberFieldCyclotomicZHatCompositum K) a P
  have hQProjection :
      AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
    restrictNormalHom_rationalCyclotomicZHatGlobalArtin
      (IdeleGroup.norm ℚ K a) E
  change
    AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a)) =
      AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a))
  calc
    AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K
            (infiniteGlobalArtinMonoidHom K
              (numberFieldCyclotomicZHatCompositum K) a)) =
        IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K
          P
          (AlgEquiv.restrictNormalHom
            P
            (infiniteGlobalArtinMonoidHom K
              (numberFieldCyclotomicZHatCompositum K) a)) :=
      restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction
        K E
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a)
    _ = IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K
          P
          (globalArtinMonoidHom
            (K := K) (L := P) a) :=
      congrArg
        (IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K P)
        hPProjection
    _ = globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
      DFunLike.congr_fun hcomm a
    _ = AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) := by
      exact hQProjection.symm

/-- The rational normalization factor is one:
`[ℚ ∩ ℚ_tilde : ℚ] = 1`. -/
@[simp]
theorem cyclotomicZHatIntersectionDegree_rat :
    cyclotomicZHatIntersectionDegree ℚ = 1 :=
  Nat.dvd_one.mp (by
    simpa using
      (cyclotomicZHatIntersectionDegree_dvd_finrank ℚ))

/-- The unnormalized composite
`v_ℚ ∘ N_{K/ℚ}`, in additive notation. -/
noncomputable def cyclotomicZHatNormComposite :
    Additive (IdeleGroup K) →+ ZHat :=
  MonoidHom.toAdditive
    (rationalCyclotomicZHatIdeleValue.toMonoidHom.comp
      (IdeleGroup.norm ℚ K))

/-- The additive norm composite evaluates by taking the ordinary idele
norm and then the rational cyclotomic idele value. -/
@[simp]
theorem cyclotomicZHatNormComposite_apply
    (a : IdeleGroup K) :
    cyclotomicZHatNormComposite K (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K a)) :=
  rfl

/-- On the canonical inclusion of a rational idele into `I_K`, the
unnormalized value is multiplication by the absolute degree `[K : ℚ]`.
This is the determinant-norm formula for scalar extension, expressed in
the rational cyclotomic `ZHat` coordinate. -/
theorem cyclotomicZHatNormComposite_baseIdeleInclusion
    (a : IdeleGroup ℚ) :
    cyclotomicZHatNormComposite K
        (Additive.ofMul
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K a))) =
      Module.finrank ℚ K •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a) := by
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K
            (relativeIdeleBaseChangeMulEquiv
              (K := ℚ) (L := K)
              (RelativeIdeleGroup.inclusion ℚ K a)))) =
      Module.finrank ℚ K •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.norm_inclusion, map_pow,
    toAdd_pow]

/-- The image of the unnormalized value contains the absolute-degree
multiple of the rational cyclotomic value group. -/
theorem
    nsmulImage_rationalCyclotomicZHatIdeleValue_range_le_normComposite_range :
    nsmulImage
        ((AddEquiv.additiveMultiplicative ZHat).toAddMonoidHom.comp
          (MonoidHom.toAdditive
            rationalCyclotomicZHatIdeleValue.toMonoidHom)).range
        (Module.finrank ℚ K) ≤
      (cyclotomicZHatNormComposite K).range := by
  intro z hz
  rw [mem_nsmulImage_iff] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨a, rfl⟩ := hx
  refine
    ⟨Additive.ofMul
        (relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := K)
          (RelativeIdeleGroup.inclusion ℚ K
            (Additive.toMul a))),
      ?_⟩
  exact
    cyclotomicZHatNormComposite_baseIdeleInclusion
      K (Additive.toMul a)

/-- At every finite cyclotomic layer, the Artin image of norms from
`K` is exactly the image of restriction from the actual finite
compositum over `K`. -/
theorem finiteCyclotomicLayer_normArtin_range
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    let C :=
      numberFieldCyclotomicZHatFiniteCompositum K E
    ((globalArtinMonoidHom
        (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range =
      (IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E K C).range := by
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let r :
      (C ≃ₐ[K] C) →* (E ≃ₐ[ℚ] E) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ E K C
  have hcomm :
      r.comp
          (globalArtinMonoidHom
            (K := K) (L := C)) =
        (globalArtinMonoidHom
          (K := ℚ) (L := E)).comp
            (IdeleGroup.norm ℚ K) :=
    by
      have hr :
          r =
            (AlgEquiv.restrictNormalHom E).comp
              (AlgEquiv.restrictScalarsHom ℚ) := by
        ext σ x
        exact rfl
      rw [hr]
      exact
        globalArtinMonoidHom_norm_restriction
          (K := ℚ) (L := E) (K' := K) (L' := C)
  apply le_antisymm
  · rintro σ ⟨a, rfl⟩
    refine
      ⟨globalArtinMonoidHom
          (K := K) (L := C) a,
        ?_⟩
    exact DFunLike.congr_fun hcomm a
  · rintro σ ⟨τ, rfl⟩
    obtain ⟨a, ha⟩ :=
      globalArtinMonoidHom_surjective
        (K := K) (L := C) τ
    refine ⟨a, ?_⟩
    have h := DFunLike.congr_fun hcomm a
    change
      r (globalArtinMonoidHom (K := K) (L := C) a) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) at h
    calc
      globalArtinMonoidHom
            (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) =
          r (globalArtinMonoidHom (K := K) (L := C) a) := h.symm
      _ = r τ := congrArg r ha

/-- Finite-layer form of the norm-image calculation: the Artin image
of the norms from `K` is precisely the subgroup fixing the actual
intersection `K ∩ E`. -/
theorem finiteCyclotomicLayer_normArtin_range_eq_fixingSubgroup
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    ((globalArtinMonoidHom
        (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range =
      (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  rw [finiteCyclotomicLayer_normArtin_range K E]
  exact
    numberFieldCyclotomicZHatFiniteCompositum_restriction_range
      K E

/-- The ordinary norm `N_{K/ℚ}` factors through the determinant norm
from the actual intersection `K ∩ ℚ_tilde`.  This is determinant-norm
transitivity in the fixed-bottom-field tower presentation. -/
theorem
    ideleNorm_mem_cyclotomicZHatIntersection_relativeIdeleNorm_range
    (a : IdeleGroup K) :
    let hle :
        numberFieldCyclotomicZHatIntersection K ≤
          rationalCyclotomicZHatField :=
      inf_le_right
    let E :=
      (numberFieldCyclotomicZHatIntersection K).restrict hle
    letI : FiniteDimensional ℚ E :=
      (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    IdeleGroup.norm ℚ K a ∈
      (RelativeIdeleGroup.norm ℚ E).range := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let : FiniteDimensional ℚ E :=
    (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let eEK : E →ₐ[ℚ] K :=
    (numberFieldCyclotomicZHatIntersectionEmbedding K).comp
      (IntermediateField.restrictAlgEquiv hle).symm.toAlgHom
  let : Algebra E K :=
    eEK.toRingHom.toAlgebra
  let : IsScalarTower ℚ E K :=
    IsScalarTower.of_algebraMap_eq'
      eEK.comp_algebraMap.symm
  let : FiniteDimensional E K :=
    FiniteDimensional.right ℚ E K
  let b : RelativeIdeleGroup ℚ K :=
    (relativeIdeleBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm a
  let t : TowerRelativeIdeleGroup ℚ E K :=
    (towerRelativeIdeleEquiv ℚ E K).symm b
  refine
    ⟨TowerRelativeIdeleGroup.norm ℚ E K t,
      ?_⟩
  calc
    RelativeIdeleGroup.norm ℚ E
          (TowerRelativeIdeleGroup.norm
            ℚ E K t) =
        RelativeIdeleGroup.norm ℚ K
          (towerRelativeIdeleEquiv
            ℚ E K t) :=
      TowerRelativeIdeleGroup.norm_transitive_flatten ℚ E K t
    _ = RelativeIdeleGroup.norm ℚ K b := by
      rw [show
        towerRelativeIdeleEquiv ℚ E K t = b by
          simp [t]]
    _ = IdeleGroup.norm ℚ K
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) b) :=
      (IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv
        ℚ K b).symm
    _ = IdeleGroup.norm ℚ K a := by
      rw [show
        relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) b = a by
          simp [b]]

/-- The infinite rational Artin symbol of `N_{K/ℚ}(a)` fixes the actual
intersection `K ∩ ℚ_tilde`. -/
theorem
    rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
    (a : IdeleGroup K) :
    rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) ∈
      ((numberFieldCyclotomicZHatIntersection K).restrict
        (show
          numberFieldCyclotomicZHatIntersection K ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E₀ :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let : FiniteDimensional ℚ E₀ :=
    (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
  let : NumberField E₀ :=
    NumberField.of_module_finite ℚ E₀
  let : IsAbelianGalois ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField_isAbelianGalois
  let inclusion : E₀ →ₐ[ℚ] rationalCyclotomicZHatField :=
    E₀.val.toRingHom.toRatAlgHom
  let E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField :=
    { toIntermediateField := E₀
      finiteDimensional := inferInstance
      isGalois :=
        (IsAbelianGalois.of_algHom (K := ℚ) (L := E₀)
          (M := rationalCyclotomicZHatField) inclusion).toIsGalois }
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  have hnorm :
      IdeleGroup.norm ℚ K a ∈
        (RelativeIdeleGroup.norm ℚ E).range := by
    change
      IdeleGroup.norm ℚ K a ∈
        (RelativeIdeleGroup.norm ℚ E₀).range
    simpa only [E₀, hle] using
      ideleNorm_mem_cyclotomicZHatIntersection_relativeIdeleNorm_range
        K a
  obtain ⟨z, hz⟩ := hnorm
  let : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom (K := ℚ) (L := E)
      (M := rationalCyclotomicZHatField)
      (show E →ₐ[ℚ] rationalCyclotomicZHatField from
        E.toIntermediateField.val.toRingHom.toRatAlgHom)
  have hfinite :
      globalArtinMonoidHom
          (K := ℚ) (L := E)
          (IdeleGroup.norm ℚ K a) =
        1 := by
    rw [← hz]
    exact
      globalArtinMonoidHom_relativeIdeleNorm_eq_one
        (K := ℚ) (L := E) z
  change
    rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) ∈
      E.fixingSubgroup
  rw [
    FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
  calc
    AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a) E
    _ = 1 := hfinite

/-- The rational Artin symbols of norms from `K` are dense in the
subgroup fixing the actual intersection `K ∩ ℚ_tilde`.  At each finite
cyclotomic layer this is the exact restriction-image calculation above;
the Krull neighborhood basis then gives density in the inverse limit. -/
theorem
    rationalCyclotomicZHatGlobalArtin_norm_denseRange_in_intersection_fixingSubgroup :
    let hle :
        numberFieldCyclotomicZHatIntersection K ≤
          rationalCyclotomicZHatField :=
      inf_le_right
    let F :=
      (numberFieldCyclotomicZHatIntersection K).restrict hle
    DenseRange
      (fun a : IdeleGroup K =>
        (⟨rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ K a),
            rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
              K a⟩ :
          F.fixingSubgroup)) := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let F :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  change
    DenseRange
      (fun a : IdeleGroup K =>
        (⟨rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ K a),
            rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
              K a⟩ :
          F.fixingSubgroup))
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσU⟩
  rw [isOpen_induced_iff] at hU
  obtain ⟨U₀, hU₀open, hUeq⟩ := hU
  have hσU₀ :
      σ.1 ∈ U₀ := by
    have hσpre :
        σ ∈
          Subtype.val ⁻¹' U₀ := by
      exact hUeq.symm ▸ hσU
    exact hσpre
  let V :
      Set
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    (Homeomorph.mulLeft
      σ.1) ⁻¹' U₀
  have hVopen : IsOpen V :=
    hU₀open.preimage
      (Homeomorph.mulLeft
        σ.1).continuous
  have hVone : ((1 : F.fixingSubgroup).1) ∈ V := by
    change
      σ.1 * (1 : F.fixingSubgroup).1 ∈ U₀
    rw [show
      σ.1 * (1 : F.fixingSubgroup).1 = σ.1 by
        exact congrArg Subtype.val (mul_one σ)]
    exact hσU₀
  have hVnhds := hVopen.mem_nhds hVone
  have hkrull :=
    InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := ℚ) (K := rationalCyclotomicZHatField) V
  obtain ⟨E, hEV⟩ :=
    hkrull.mp hVnhds
  let hENumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let : NumberField E := hENumberField
  let hEAbelian : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  let : IsAbelianGalois ℚ E := hEAbelian
  have hσfix :
      ∀ x : rationalCyclotomicZHatField,
        x ∈ F →
          σ.1 x = x := by
    exact
      (IntermediateField.mem_fixingSubgroup_iff F σ.1).1
        σ.property
  have hrestrictFix :
      AlgEquiv.restrictNormalHom E
          σ.1 ∈
        (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply Subtype.ext
    have hxF :
        ((x : E) : rationalCyclotomicZHatField) ∈ F := by
      apply
        (IntermediateField.mem_restrict hle
          ((x : E) : rationalCyclotomicZHatField)).2
      exact
        numberFieldCyclotomicZHatFiniteIntersection_coe_mem_intersection
          K E x hx
    calc
      (((AlgEquiv.restrictNormalHom E
            σ.1) x : E) :
          rationalCyclotomicZHatField) =
          σ.1
            ((x : E) : rationalCyclotomicZHatField) :=
        AlgEquiv.restrictNormal_commutes
          σ.1 E x
      _ = ((x : E) : rationalCyclotomicZHatField) :=
        hσfix ((x : E) : rationalCyclotomicZHatField) hxF
  have hrestrictRange :
      AlgEquiv.restrictNormalHom E
          σ.1 ∈
        ((globalArtinMonoidHom
            (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range := by
    rw [
      finiteCyclotomicLayer_normArtin_range_eq_fixingSubgroup
        K E]
    exact hrestrictFix
  obtain ⟨a, ha⟩ := hrestrictRange
  let τ :
      F.fixingSubgroup :=
    ⟨rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a),
      rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
        K a⟩
  let δ : F.fixingSubgroup := σ⁻¹ * τ
  have hδ :
      δ.1 = (σ.1)⁻¹ * τ.1 :=
    rfl
  have hτ :
      τ.1 =
        rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) :=
    rfl
  have ha' :
      globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) =
        AlgEquiv.restrictNormalHom E σ.1 := by
    simpa only [MonoidHom.comp_apply] using ha
  have hτProjection :
      AlgEquiv.restrictNormalHom E τ.1 =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) := by
    rw [hτ]
    change
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom
            ℚ rationalCyclotomicZHatField
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a)
    exact
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
        (IdeleGroup.norm ℚ K a) E hENumberField hEAbelian
  have hrestrictEq :
      AlgEquiv.restrictNormalHom E τ.1 =
        AlgEquiv.restrictNormalHom E σ.1 :=
    hτProjection.trans ha'
  have hfixE :
      δ.1 ∈ E.fixingSubgroup := by
    apply
      (IntermediateField.mem_fixingSubgroup_iff
        E.toIntermediateField δ.1).2
    intro x hx
    have hrestrictedValue :=
      congrArg
        (fun f : E ≃ₐ[ℚ] E => f ⟨x, hx⟩)
        hrestrictEq
    have hτx : τ.1 x = σ.1 x := by
      calc
        τ.1 x =
            ((AlgEquiv.restrictNormalHom E τ.1)
              ⟨x, hx⟩ : E) :=
          (AlgEquiv.restrictNormal_commutes
            τ.1 E ⟨x, hx⟩).symm
        _ =
            ((AlgEquiv.restrictNormalHom E σ.1)
              ⟨x, hx⟩ : E) :=
          congrArg Subtype.val hrestrictedValue
        _ = σ.1 x :=
          AlgEquiv.restrictNormal_commutes
            σ.1 E ⟨x, hx⟩
    calc
      δ.1 x = ((σ.1)⁻¹ * τ.1) x :=
        congrArg (fun f => f x) hδ
      _ = (σ.1)⁻¹ (τ.1 x) := rfl
      _ = (σ.1)⁻¹ (σ.1 x) :=
        congrArg
          (fun y : rationalCyclotomicZHatField =>
            (σ.1)⁻¹ y)
          hτx
      _ = x := (σ.1).symm_apply_apply x
  have hmemV :
      δ.1 ∈ V :=
    hEV hfixE
  have hτU₀ :
      τ.1 ∈ U₀ := by
    change σ.1 * δ.1 ∈ U₀ at hmemV
    have hcancel : σ * δ = τ := by
      dsimp only [δ]
      exact mul_inv_cancel_left σ τ
    have hcancelVal := congrArg Subtype.val hcancel
    change σ.1 * δ.1 = τ.1 at hcancelVal
    rw [hcancelVal] at hmemV
    exact hmemV
  have hτU : τ ∈ U := by
    have hτpre : τ ∈ Subtype.val ⁻¹' U₀ :=
      hτU₀
    exact hUeq ▸ hτpre
  exact ⟨τ, hτU, ⟨a, rfl⟩⟩

/-- The unnormalized value `v_ℚ(N_{K/ℚ}(a))` lies in the actual
subgroup `f_K ZHat`. -/
theorem cyclotomicZHatNormComposite_mem_mulNat_range
    (a : Additive (IdeleGroup K)) :
    cyclotomicZHatNormComposite K a ∈
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range := by
  let σ :=
    rationalCyclotomicZHatGlobalArtin
      (IdeleGroup.norm ℚ K (Additive.toMul a))
  have hfix :
      σ ∈
        ((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup := by
    exact
      rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
        K (Additive.toMul a)
  have hmap :
      rationalCyclotomicZHatFieldGalEquivZHat σ ∈
        ((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom :=
    ⟨σ, hfix, rfl⟩
  have hadd :
      Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat σ) ∈
        Subgroup.toAddSubgroup'
          (((numberFieldCyclotomicZHatIntersection K).restrict
            (show
              numberFieldCyclotomicZHatIntersection K ≤
                rationalCyclotomicZHatField from
              inf_le_right)).fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom) := by
    rw [Subgroup.mem_toAddSubgroup']
    simpa using hmap
  rw [
    rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range
      K] at hadd
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat σ) ∈
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
  exact hadd

/-- Subgroup form of the upper image bound:
`v_ℚ(N_{K/ℚ}(I_K)) ⊆ f_K ZHat`. -/
theorem cyclotomicZHatNormComposite_range_le_mulNat_range :
    (cyclotomicZHatNormComposite K).range ≤
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range := by
  rintro _ ⟨a, rfl⟩
  exact cyclotomicZHatNormComposite_mem_mulNat_range K a

/-- The unnormalized composite, with codomain restricted to the actual
multiple subgroup `f_K ZHat`. -/
noncomputable def cyclotomicZHatNormCompositeInMulNatRange :
    Additive (IdeleGroup K) →+
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range :=
  (cyclotomicZHatNormComposite K).codRestrict
    (zHatMulNat
    (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
    (cyclotomicZHatNormComposite_mem_mulNat_range K)

/-- The unnormalized norm value is dense in its exact ambient subgroup
`f_K ℤ̂`.  This is the additive-coordinate form of the Krull-density
statement for norm Artin symbols. -/
theorem cyclotomicZHatNormCompositeInMulNatRange_denseRange :
    DenseRange
      (cyclotomicZHatNormCompositeInMulNatRange K) := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let F :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let H := F.fixingSubgroup
  let f := cyclotomicZHatIntersectionDegree K
  let R :=
    (zHatMulNat f).toAddMonoidHom.range
  let e :=
    rationalCyclotomicZHatFieldGalEquivZHat
  have himage :
      (H.map e.toMonoidHom).toAddSubgroup' = R := by
    simpa only [H, F, f, R, e] using
      (rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range
        K)
  let g : H → R :=
    fun σ =>
      ⟨Multiplicative.toAdd (e σ.1), by
        have hσ :
            Multiplicative.toAdd (e σ.1) ∈
              (H.map e.toMonoidHom).toAddSubgroup' := by
          rw [Subgroup.mem_toAddSubgroup']
          exact ⟨σ.1, σ.2, rfl⟩
        rw [himage] at hσ
        exact hσ⟩
  have hgContinuous : Continuous g := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun σ : H =>
          e σ.1)
    exact e.continuous.comp continuous_subtype_val
  have hgSurjective : Function.Surjective g := by
    intro z
    have hz :
        z.1 ∈
          (H.map e.toMonoidHom).toAddSubgroup' := by
      rw [himage]
      exact z.2
    rw [Subgroup.mem_toAddSubgroup'] at hz
    obtain ⟨σ, hσ, hσz⟩ := hz
    refine ⟨⟨σ, hσ⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hσz
  have hnormDense :
      DenseRange
        (fun a : IdeleGroup K =>
          (⟨rationalCyclotomicZHatGlobalArtin
                (IdeleGroup.norm ℚ K a),
              rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
                K a⟩ :
            H)) := by
    simpa only [H, F] using
      (rationalCyclotomicZHatGlobalArtin_norm_denseRange_in_intersection_fixingSubgroup
        K)
  have hcompDense :
      DenseRange
        (fun a : IdeleGroup K =>
          g
            (⟨rationalCyclotomicZHatGlobalArtin
                  (IdeleGroup.norm ℚ K a),
                rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
                  K a⟩ :
              H)) :=
    hgSurjective.denseRange.comp
      hnormDense hgContinuous
  apply hcompDense.mono
  rintro z ⟨a, rfl⟩
  refine ⟨Additive.ofMul a, ?_⟩
  apply Subtype.ext
  rfl

/-- The normalized cyclotomic value on ideles:
`(1 / f_K) v_ℚ ∘ N_{K/ℚ}`. -/
noncomputable def normalizedCyclotomicZHatIdeleValue :
    Additive (IdeleGroup K) →+ ZHat :=
  (zHatDivide
    (cyclotomicZHatIntersectionDegree K)
    (cyclotomicZHatIntersectionDegree_pos K)).toAddMonoidHom.comp
      (cyclotomicZHatNormCompositeInMulNatRange K)

/-- The normalized cyclotomic value has dense image in `ℤ̂`. -/
theorem normalizedCyclotomicZHatIdeleValue_denseRange :
    DenseRange (normalizedCyclotomicZHatIdeleValue K) := by
  change
    DenseRange
      (fun a =>
        zHatDivide
          (cyclotomicZHatIntersectionDegree K)
          (cyclotomicZHatIntersectionDegree_pos K)
          (cyclotomicZHatNormCompositeInMulNatRange K a))
  exact
    (zHatMulNatRangeEquiv
        (cyclotomicZHatIntersectionDegree K)
        (cyclotomicZHatIntersectionDegree_pos K)).symm.surjective.denseRange.comp
      (cyclotomicZHatNormCompositeInMulNatRange_denseRange K)
      (zHatDivide
        (cyclotomicZHatIntersectionDegree K)
        (cyclotomicZHatIntersectionDegree_pos K)).continuous

/-- The defining normalization identity
`f_K v_K(a) = v_ℚ(N_{K/ℚ}(a))` at the idele level. -/
theorem cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
    (a : Additive (IdeleGroup K)) :
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleValue K a =
      cyclotomicZHatNormComposite K a := by
  exact
    zHatMulNat_zHatDivide
      (cyclotomicZHatIntersectionDegree K)
      (cyclotomicZHatIntersectionDegree_pos K)
      (cyclotomicZHatNormCompositeInMulNatRange K a)

/-- On scalar extension of a rational idele, the normalized value is
multiplication by the relative factor `[K : ℚ] / f_K`. -/
theorem normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion
    (a : IdeleGroup ℚ) :
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K a))) =
      (Module.finrank ℚ K /
          cyclotomicZHatIntersectionDegree K) •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a) := by
  apply
    zHatMulNat_injective
      (cyclotomicZHatIntersectionDegree_pos K)
  rw [zHatMulNat_apply, zHatMulNat_apply,
    cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue,
    cyclotomicZHatNormComposite_baseIdeleInclusion,
    ← mul_nsmul,
    Nat.div_mul_cancel
      (cyclotomicZHatIntersectionDegree_dvd_finrank K)]

end Reciprocity
end GlobalClassFieldTheory
