/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationDensity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.ExtensionInvariants
public import Mathlib.FieldTheory.SeparableClosure
/-!
# Decomposition-field value and residue comparison

This file identifies the decomposition field with the literal intersection
`L ∩ K_v` inside the algebraic localization `L_w`.  It then records the
canonical residue-field isomorphism and equality of absolute-value ranges in
the nonarchimedean case.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.ResidueField renaming
  residue_eq_residue_iff_sub_mem_maximalIdeal →
    residue_eq_residue_iff_sub_mem_maximalIdeal


noncomputable section

universe u v

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section LocalizationGalois

variable [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
  (w : AbsoluteValueExtension vK L)

/-- The completion at the extended absolute value is a `K`-algebra through the original
extension. -/
local instance proposition98CompletionBaseAlgebra : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The action of `K` on the extended completion is induced by its completion algebra. -/
local instance proposition98CompletionBaseSMul : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul

/-- The completion at the extended absolute value is an algebra over the completed base field. -/
local instance proposition98CompletionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

private abbrev localization : IntermediateField vK.Completion w.1.Completion :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

private abbrev toLocalization : L →+* localization vK w :=
  AbsoluteValue.toAlgebraicLocalization vK w.1 w.2

/-- The algebraic localization is a `K`-algebra through the completed base field. -/
local instance proposition98LocalizationBaseAlgebra : Algebra K (localization vK w) :=
  ((algebraMap vK.Completion (localization vK w)).comp
    (algebraMap K vK.Completion)).toAlgebra

local instance proposition98LocalizationScalarTower :
    IsScalarTower K vK.Completion (localization vK w) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

/-- The dense copy of `L` in the localization, as a `K`-algebra embedding
for the scalar tower `K → K_v → L_w`. -/
def decompositionFieldToLocalizationAlgHom :
    L →ₐ[K] localization vK w where
  __ := toLocalization vK w
  commutes' x := AbsoluteValue.toAlgebraicLocalization_algebraMap vK w.1 w.2 x

omit [IsGalois K L] in
/-- The localization is generated over `K_v` by the subtype-valued copy of
`L`, not only by its ambient-completion representatives. -/
theorem decompositionField_localization_adjoin_range_eq_top :
    IntermediateField.adjoin vK.Completion
      (Set.range (toLocalization vK w)) = ⊤ := by
  let E := localization vK w
  apply IntermediateField.lift_injective E
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  change IntermediateField.adjoin vK.Completion
      (Subtype.val '' Set.range (toLocalization vK w)) =
    AbsoluteValue.algebraicLocalization vK w.1 w.2
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨toLocalization vK w x, ⟨x, rfl⟩, rfl⟩

omit hvK in
/-- Every generator coming from `L` is separable over `K_v`. -/
theorem decompositionField_toLocalization_isSeparable (x : L) :
    IsSeparable vK.Completion (toLocalization vK w x) := by
  have hx : IsSeparable K
      (decompositionFieldToLocalizationAlgHom vK w x) :=
    (Algebra.IsSeparable.isSeparable K x).map
      (decompositionFieldToLocalizationAlgHom vK w)
      (decompositionFieldToLocalizationAlgHom vK w).injective
  exact IsSeparable.tower_top vK.Completion hx

omit hvK in
/-- Every generator coming from `L` has its `K_v`-minimal polynomial split
inside the localization. -/
theorem decompositionField_toLocalization_minpoly_splits (x : L) :
    ((minpoly vK.Completion (toLocalization vK w x)).map
      (algebraMap vK.Completion (localization vK w))).Splits := by
  let i := decompositionFieldToLocalizationAlgHom vK w
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hsK : ((minpoly K x).map
      (algebraMap K (localization vK w))).Splits := by
    have hi : i.toRingHom.comp (algebraMap K L) =
        algebraMap K (localization vK w) := i.comp_algebraMap
    have hs := (Normal.splits (F := K) (K := L) inferInstance x).map
      i.toRingHom
    simpa only [Polynomial.map_map, hi] using hs
  have hsTower : (((minpoly K x).map (algebraMap K vK.Completion)).map
      (algebraMap vK.Completion (localization vK w))).Splits := by
    simpa only [Polynomial.map_map,
      IsScalarTower.algebraMap_eq K vK.Completion (localization vK w)] using hsK
  have hdvd : minpoly vK.Completion (toLocalization vK w x) ∣
      (minpoly K x).map (algebraMap K vK.Completion) := by
    have h := minpoly.dvd_map_of_isScalarTower K vK.Completion
      (toLocalization vK w x)
    have hmin : minpoly K (toLocalization vK w x) = minpoly K x :=
      minpoly.algHom_eq i i.injective x
    rwa [hmin] at h
  exact hsTower.of_dvd
    (Polynomial.map_ne_zero
      (Polynomial.map_ne_zero (minpoly.ne_zero hxint)))
    ((Polynomial.map_dvd_map' _).mpr hdvd)

omit hvK in
/-- The algebraic localization of a Galois extension is normal over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_normal :
    Normal vK.Completion (localization vK w) := by
  let : Algebra.IsAlgebraic vK.Completion (localization vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  rw [normal_iff]
  intro z
  refine ⟨Algebra.IsIntegral.isIntegral z, ?_⟩
  apply IntermediateField.splits_of_mem_adjoin
      (F := vK.Completion) (K := localization vK w)
      (L := localization vK w)
      (S := Set.range (toLocalization vK w))
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨(decompositionField_toLocalization_isSeparable vK w x).isIntegral,
      decompositionField_toLocalization_minpoly_splits vK w x⟩
  · rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial

omit hvK in
/-- The algebraic localization of a Galois extension is separable over the
completed base field, with no finite-degree hypothesis. -/
theorem decompositionField_localization_separable :
    Algebra.IsSeparable vK.Completion (localization vK w) := by
  let S := Set.range (toLocalization vK w)
  have hS : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable
      (F := vK.Completion) (E := localization vK w)).mpr fun y hy => by
      rcases hy with ⟨x, rfl⟩
      exact decompositionField_toLocalization_isSeparable vK w x
  let : Algebra.IsSeparable vK.Completion
      (IntermediateField.adjoin vK.Completion S) := hS
  refine ⟨fun z => ?_⟩
  have hz : z ∈ IntermediateField.adjoin vK.Completion S := by
    rw [decompositionField_localization_adjoin_range_eq_top vK w]
    trivial
  exact IntermediateField.isSeparable_of_mem_isSeparable vK.Completion
    (localization vK w) hz

omit hvK in
/-- The algebraic localization of a Galois extension is Galois over `K_v`.
This permits the fixed-field argument in infinite degree. -/
theorem algebraicLocalization_isGalois :
    IsGalois vK.Completion (localization vK w) :=
  isGalois_iff.mpr
    ⟨decompositionField_localization_separable vK w,
      decompositionField_localization_normal vK w⟩

/-- The copy of `K_v` as an actual subfield of the algebraic localization. -/
abbrev decompositionFieldCompletionImageSubfield :
    Subfield (localization vK w) :=
  (algebraMap vK.Completion (localization vK w)).fieldRange

include hvK

/-- The decomposition-field extension comparison, comap form: an element of `L` lies in the
decomposition field exactly when its image in `L_w` belongs to the embedded
copy of `K_v`. -/
theorem decompositionField_decompositionField_eq_completionImage_comap :
    (decompositionFieldCompletionImageSubfield vK w).comap
        (toLocalization vK w) =
      (absoluteValueDecompositionField K w.1).toSubfield := by
  let : IsGalois vK.Completion (localization vK w) :=
    algebraicLocalization_isGalois vK w
  ext x
  change toLocalization vK w x ∈
      Set.range (algebraMap vK.Completion (localization vK w)) ↔
    x ∈ absoluteValueDecompositionField K w.1
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed,
    mem_absoluteValueDecompositionField_iff]
  constructor
  · intro hfixed σ hσ
    let δ : absoluteValueDecompositionGroup K w.1 := ⟨σ, hσ⟩
    apply (toLocalization vK w).injective
    calc
      toLocalization vK w (σ x) =
          decompositionGroupEquivAlgebraicLocalizationAut vK hvK w δ
            (toLocalization vK w x) :=
        (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x).symm
      _ = toLocalization vK w x := hfixed _
  · intro hZ τ
    let δ : absoluteValueDecompositionGroup K w.1 :=
      (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm τ
    have hδ : ((δ : L ≃ₐ[K] L) x) = x := hZ δ δ.property
    calc
      τ (toLocalization vK w x) =
          decompositionGroupEquivAlgebraicLocalizationAut vK hvK w δ
            (toLocalization vK w x) := by
        rw [MulEquiv.apply_symm_apply]
      _ = toLocalization vK w ((δ : L ≃ₐ[K] L) x) :=
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization
          vK hvK w δ x
      _ = toLocalization vK w x := congrArg (toLocalization vK w) hδ

/-- The decomposition-field extension comparison, literal intersection form inside `L_w`:
the image of `Z_w` is the infimum of the images of `L` and `K_v`. -/
theorem decompositionField_decompositionField_image_eq_intersection :
    (toLocalization vK w).fieldRange ⊓
        decompositionFieldCompletionImageSubfield vK w =
      (absoluteValueDecompositionField K w.1).toSubfield.map
        (toLocalization vK w) := by
  calc
    (toLocalization vK w).fieldRange ⊓
        decompositionFieldCompletionImageSubfield vK w =
      decompositionFieldCompletionImageSubfield vK w ⊓
        (toLocalization vK w).fieldRange := by rw [inf_comm]
    _ = ((decompositionFieldCompletionImageSubfield vK w).comap
        (toLocalization vK w)).map (toLocalization vK w) :=
      (Subfield.map_comap_eq (toLocalization vK w)
        (decompositionFieldCompletionImageSubfield vK w)).symm
    _ = (absoluteValueDecompositionField K w.1).toSubfield.map
        (toLocalization vK w) := by
      rw [decompositionField_decompositionField_eq_completionImage_comap
        vK hvK w]

omit hvK

omit [IsGalois K L] in
/-- Nonarchimedeanness passes from the exact base valuation to its extension
`w`; this uses only the bounded-natural-number definition. -/
theorem absoluteValueExtension_nonarchimedean_of_base
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1 := by
  rcases hv with ⟨C, hC⟩
  refine ⟨C, fun n => ?_⟩
  have hext := w.2 (n : K)
  simpa using hext.trans_le (hC n)

omit [IsGalois K L] in
/-- Nonarchimedeanness also passes to the restriction of `w` to `Z_w`. -/
theorem decompositionField_decompositionField_nonarchimedean
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1
        (absoluteValueDecompositionField K w.1)) := by
  rcases absoluteValueExtension_nonarchimedean_of_base vK w hv with ⟨C, hC⟩
  exact ⟨C, fun n => by simpa using hC n⟩

/-- The norm absolute value on `K_v` is nonarchimedean whenever `v` is. -/
theorem decompositionField_completion_nonarchimedean
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (AbsoluteValue.completionAbsoluteValue vK) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (AbsoluteValue.completionAbsoluteValue vK)).1
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK
      ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv))

/-- Completion does not enlarge the range of a nonarchimedean absolute
value.  This provides the value-group equality used in the decomposition-field extension
  comparison. -/
theorem decompositionField_completionAbsoluteValue_range_eq
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    Set.range (AbsoluteValue.completionAbsoluteValue vK) = Set.range vK :=
  AbsoluteValue.completionAbsoluteValue_range_eq vK
    ((AbsoluteValue.isNonarchimedean_iff_bounded_nat vK).2 hv)

include hvK

/-- The decomposition-field extension comparison, value-group form: `w|Z_w` and `v` have literally
the same range in `ℝ`. -/
theorem decompositionField_decompositionField_valueRange_eq
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    Set.range
        (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1
          (absoluteValueDecompositionField K w.1)) =
      Set.range vK := by
  let Z := absoluteValueDecompositionField K w.1
  let wZ := AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1 Z
  let aE := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  apply Set.Subset.antisymm
  · rintro r ⟨z, rfl⟩
    have hz : (z : L) ∈ Z.toSubfield := z.property
    rw [← decompositionField_decompositionField_eq_completionImage_comap
      vK hvK w] at hz
    rcases hz with ⟨y, hy⟩
    have hvalue : wZ z = AbsoluteValue.completionAbsoluteValue vK y := by
      calc
        wZ z = aE (toLocalization vK w (z : L)) :=
          (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2
            (z : L)).symm
        _ = aE (algebraMap vK.Completion (localization vK w) y) := by
          rw [hy]
        _ = AbsoluteValue.completionAbsoluteValue vK y :=
          AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y
    rw [hvalue]
    exact (Set.ext_iff.mp
      (decompositionField_completionAbsoluteValue_range_eq vK hv)
      (AbsoluteValue.completionAbsoluteValue vK y)).mp ⟨y, rfl⟩
  · rintro r ⟨x, rfl⟩
    refine ⟨algebraMap K Z x, ?_⟩
    change w.1 (algebraMap Z L (algebraMap K Z x)) = vK x
    rw [← IsScalarTower.algebraMap_apply K Z L, w.2 x]

omit hvK

/-- The valuation subring of the nonarchimedean base absolute value. -/
abbrev decompositionFieldBaseValuationSubring
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    _root_.ValuationSubring K :=
  absoluteValueValuationSubring vK hv

/-- The valuation subring of `w|Z_w`. -/
abbrev decompositionFieldDecompositionFieldValuationSubring
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    _root_.ValuationSubring (absoluteValueDecompositionField K w.1) :=
  absoluteValueValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1
      (absoluteValueDecompositionField K w.1))
    (decompositionField_decompositionField_nonarchimedean vK w hv)

/-- The canonical local homomorphism between the two valuation subrings in
the decomposition-field extension comparison. -/
def decompositionFieldDecompositionFieldIntegerMap
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    decompositionFieldBaseValuationSubring vK hv →+*
      decompositionFieldDecompositionFieldValuationSubring vK w hv := by
  let Z := absoluteValueDecompositionField K w.1
  let AK := decompositionFieldBaseValuationSubring vK hv
  let AZ := decompositionFieldDecompositionFieldValuationSubring vK w hv
  apply RingHom.codRestrict ((algebraMap K Z).comp AK.subtype) AZ
  intro x
  rw [mem_absoluteValueValuationSubring_iff]
  change w.1 (algebraMap Z L (algebraMap K Z x)) ≤ 1
  rw [← IsScalarTower.algebraMap_apply K Z L, w.2]
  exact (mem_absoluteValueValuationSubring_iff
    vK hv x).mp x.property

omit [IsGalois K L] in
@[simp] theorem decompositionField_decompositionField_integerMap_apply
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK)
    (x : decompositionFieldBaseValuationSubring vK hv) :
    ((decompositionFieldDecompositionFieldIntegerMap vK w hv x :
        decompositionFieldDecompositionFieldValuationSubring vK w hv) :
      absoluteValueDecompositionField K w.1) =
      algebraMap K (absoluteValueDecompositionField K w.1) (x : K) :=
  rfl

/-- The valuation-ring map in the decomposition-field extension comparison is local. -/
instance decompositionField_decompositionField_integerMap_isLocalHom
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalHom (decompositionFieldDecompositionFieldIntegerMap vK w hv) where
  map_nonunit x hx := by
    rw [← IsLocalRing.notMem_maximalIdeal] at hx ⊢
    intro hxmax
    apply hx
    have hxabs : vK (x : K) < 1 :=
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        vK hv x).mp hxmax
    rw [absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]
    rw [decompositionField_decompositionField_integerMap_apply]
    change w.1 (algebraMap
      (absoluteValueDecompositionField K w.1) L
      (algebraMap K (absoluteValueDecompositionField K w.1) (x : K))) < 1
    rw [← IsScalarTower.algebraMap_apply K
      (absoluteValueDecompositionField K w.1) L, w.2]
    exact hxabs

/-- The induced canonical map of actual residue fields. -/
def decompositionFieldDecompositionFieldResidueMap
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalRing.ResidueField (decompositionFieldBaseValuationSubring vK hv) →+*
      IsLocalRing.ResidueField
        (decompositionFieldDecompositionFieldValuationSubring vK w hv) :=
  IsLocalRing.ResidueField.map
    (decompositionFieldDecompositionFieldIntegerMap vK w hv)

include hvK

/-- The canonical residue-field map in the decomposition-field extension comparison is surjective.
The proof chooses a representative in `K_v`, then approximates
it modulo the maximal ideal by an element of `K`. -/
theorem decompositionField_decompositionField_residueMap_surjective
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    Function.Surjective
      (decompositionFieldDecompositionFieldResidueMap vK w hv) := by
  let Z := absoluteValueDecompositionField K w.1
  let AK := decompositionFieldBaseValuationSubring vK hv
  let AZ := decompositionFieldDecompositionFieldValuationSubring vK w hv
  let f := decompositionFieldDecompositionFieldIntegerMap vK w hv
  let aK := AbsoluteValue.completionAbsoluteValue vK
  let aE := AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2
  let vId : AbsoluteValueExtension vK K := ⟨vK, fun _ => rfl⟩
  intro q
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective q
  have hzmem : ((z : Z) : L) ∈ Z.toSubfield := (z : Z).property
  rw [← decompositionField_decompositionField_eq_completionImage_comap
    vK hvK w] at hzmem
  rcases hzmem with ⟨y, hy⟩
  have hzle :
      (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1 Z)
        (z : Z) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      _ (decompositionField_decompositionField_nonarchimedean vK w hv) _).mp
        z.property
  have hyle : aK y ≤ 1 := by
    calc
      aK y = aE (algebraMap vK.Completion (localization vK w) y) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 y).symm
      _ = aE (toLocalization vK w ((z : Z) : L)) := by rw [hy]
      _ = w.1 ((z : Z) : L) :=
        AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _
      _ ≤ 1 := hzle
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion vId.1).exists_dist_lt
      y (show (0 : ℝ) < 1 by norm_num)
  have hclose : aK (y - algebraMap K vK.Completion x) < 1 := by
    change ‖y - AbsoluteValue.toCompletion vId.1 x‖ < 1
    simpa only [dist_eq_norm] using hx
  have hstrong : LubinTate.Valuations.StrongTriangle aK :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean aK
      (decompositionField_completion_nonarchimedean vK hv)
  have hxle : aK (algebraMap K vK.Completion x) ≤ 1 := by
    calc
      aK (algebraMap K vK.Completion x) =
          aK (y + -(y - algebraMap K vK.Completion x)) := by
        congr 1
        ring
      _ ≤ max (aK y) (aK (-(y - algebraMap K vK.Completion x))) :=
        hstrong _ _
      _ = max (aK y) (aK (y - algebraMap K vK.Completion x)) := by
        rw [AbsoluteValue.map_neg]
      _ ≤ 1 := max_le hyle hclose.le
  have hxbase : vK x ≤ 1 := by
    rw [← AbsoluteValue.completionAbsoluteValue_coe vK x]
    exact hxle
  let xA : AK :=
    ⟨x, (mem_absoluteValueValuationSubring_iff
      vK hv x).mpr hxbase⟩
  refine ⟨IsLocalRing.residue AK xA, ?_⟩
  change IsLocalRing.ResidueField.map f (IsLocalRing.residue AK xA) =
    IsLocalRing.residue AZ z
  rw [IsLocalRing.ResidueField.map_residue]
  rw [residue_eq_residue_iff_sub_mem_maximalIdeal]
  rw [absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one]
  calc
    (AlgebraicNumberTheory.Valuations.absoluteValueRestrictIntermediateField w.1 Z)
        (((f xA : AZ) : Z) - (z : Z)) =
      aE (toLocalization vK w
        ((((f xA : AZ) : Z) - (z : Z) : Z) : L)) :=
        (AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _).symm
    _ = aE (algebraMap vK.Completion (localization vK w)
        (algebraMap K vK.Completion x - y)) := by
      congr 1
      rw [map_sub (algebraMap vK.Completion (localization vK w))]
      dsimp [f]
      dsimp [xA]
      rw [map_sub, AbsoluteValue.toAlgebraicLocalization_algebraMap, ← hy]
    _ = aK (algebraMap K vK.Completion x - y) :=
      AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 _
    _ = aK (y - algebraMap K vK.Completion x) := by
      rw [← AbsoluteValue.map_neg]
      congr 1
      ring
    _ < 1 := hclose

/-- The decomposition-field extension comparison, residue-field form: the canonical residue map
is an
isomorphism of the actual residue fields. -/
def decompositionFieldDecompositionFieldResidueFieldEquiv
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK) :
    IsLocalRing.ResidueField (decompositionFieldBaseValuationSubring vK hv) ≃+*
      IsLocalRing.ResidueField
        (decompositionFieldDecompositionFieldValuationSubring vK w hv) :=
  ValuationTheory.DiscreteValuationField.ResidueField.ringEquivOfSurjective
    (decompositionFieldDecompositionFieldIntegerMap vK w hv)
    (decompositionField_decompositionField_residueMap_surjective vK hvK w hv)

@[simp] theorem decompositionField_decompositionField_residueFieldEquiv_apply
    (hv : LubinTate.Valuations.NonarchimedeanAbsoluteValue vK)
    (x : IsLocalRing.ResidueField
      (decompositionFieldBaseValuationSubring vK hv)) :
    decompositionFieldDecompositionFieldResidueFieldEquiv vK hvK w hv x =
      decompositionFieldDecompositionFieldResidueMap vK w hv x :=
  rfl

omit hvK

end LocalizationGalois

end HilbertRamification
