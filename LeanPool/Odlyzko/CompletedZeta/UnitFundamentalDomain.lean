/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
public import Mathlib.Algebra.Order.Floor.Ring

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Finset MeasureTheory Module NumberField NumberField.InfinitePlace
  NumberField.Units Set dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- An unit fundamental param set used in the Odlyzko-bound argument. -/
abbrev unitFundamentalParamSet (K : Type*) [Field K] [NumberField K] :
    Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.univ else Set.Ico 0 1

theorem measurableSet_unitFundamentalParamSet :
    MeasurableSet (unitFundamentalParamSet K) := by
  classical
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · simp
  · simp

theorem mem_unitFundamentalParamSet_iff
    (x : realSpace K) :
    x ∈ unitFundamentalParamSet K ↔
      ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by simp

open scoped Classical in
open scoped Classical in
open scoped Classical in
/-- An unit floor used in the Odlyzko-bound argument. -/
def unitFloor (x : realSpace K) : InfinitePlace K → ℤ :=
  fun w ↦ if w = w₀ then 0 else ⌊x w⌋

open scoped Classical in
/-- An unit coordinate shift used in the Odlyzko-bound argument. -/
def unitCoordinateShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : realSpace K :=
  fun w ↦ if hw : w = w₀ then 0 else z ⟨w, hw⟩

open scoped Classical in
/-- A fundamental unit for shift used in the Odlyzko-bound argument. -/
def fundamentalUnitForShift
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : (𝓞 K)ˣ :=
  ∏ i, fundSystem K (equivFinRank.symm i) ^ z i

theorem expMapBasis_add_unitCoordinateShift
    (x : realSpace K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    expMapBasis (x + unitCoordinateShift z) =
      (fun w ↦ w (fundamentalUnitForShift z)) * expMapBasis x := by
  classical
  ext w
  rw [expMapBasis_apply', expMapBasis_apply']
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have hradial :
      (x + unitCoordinateShift z) w₀ = x w₀ := by
    simp [unitCoordinateShift]
  have hcoord (i : {w : InfinitePlace K // w ≠ w₀}) :
      (x + unitCoordinateShift z) i = x i + (z i : ℝ) := by
    simp [unitCoordinateShift, i.prop]
  have hrpow (i : {w : InfinitePlace K // w ≠ w₀}) :
      w (fundSystem K (equivFinRank.symm i)) ^
          (x i + (z i : ℝ)) =
        w (fundSystem K (equivFinRank.symm i)) ^ x i *
          w (fundSystem K (equivFinRank.symm i)) ^ z i := by
    rw [Real.rpow_add_intCast]
    simp
  rw [hradial]
  simp_rw [hcoord, hrpow]
  rw [Finset.prod_mul_distrib]
  have hunit :
      w (fundamentalUnitForShift z) =
        ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ z i := by
    rw [fundamentalUnitForShift, Units.coe_prod, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases z i <;> simp [zpow_negSucc, map_inv₀]
  grind

open scoped Classical in
open scoped Classical in
/-- An unit fundamental translate used in the Odlyzko-bound argument. -/
def unitFundamentalTranslate
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) : Set (realSpace K) :=
  (fun x ↦ x - unitCoordinateShift z) ⁻¹' unitFundamentalParamSet K

theorem measurableSet_unitFundamentalTranslate
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    MeasurableSet (unitFundamentalTranslate z) :=
  (measurable_id.sub_const _)
    measurableSet_unitFundamentalParamSet

theorem mem_unitFundamentalTranslate_iff
    (x : realSpace K) (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    x ∈ unitFundamentalTranslate z ↔
      (fun i : {w : InfinitePlace K // w ≠ w₀} ↦ unitFloor x i) = z := by
  rw [unitFundamentalTranslate, Set.mem_preimage,
    mem_unitFundamentalParamSet_iff]
  constructor
  · intro hx
    funext i
    have hi := hx i i.prop
    have hi' : x i - (z i : ℝ) ∈ Set.Ico 0 1 := by
      simpa [unitCoordinateShift, i.prop] using hi
    have hfloor :
        ⌊x i - (z i : ℝ)⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr hi'
    simp only [Int.floor_sub_intCast] at hfloor
    simpa [unitFloor, i.prop] using sub_eq_zero.mp hfloor
  · intro hz w hw
    have hfloor := congr_fun hz ⟨w, hw⟩
    have hfloor' : ⌊x w⌋ = z ⟨w, hw⟩ := by
      simpa [unitFloor, hw] using hfloor
    have hshift :
        unitCoordinateShift z w = (z ⟨w, hw⟩ : ℝ) := by
      simp [unitCoordinateShift, hw]
    simp only [Pi.sub_apply, hshift]
    rw [← hfloor']
    simpa only [Int.fract] using
      (show Int.fract (x w) ∈ Set.Ico (0 : ℝ) 1 from
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)

theorem pairwise_disjoint_unitFundamentalTranslate :
    Pairwise fun (z z' : {w : InfinitePlace K // w ≠ w₀} → ℤ) ↦
      Disjoint (unitFundamentalTranslate z) (unitFundamentalTranslate z') := by
  intro z z' hne
  rw [Set.disjoint_left]
  intro x hx hx'
  have hz := (mem_unitFundamentalTranslate_iff x z).mp hx
  have hz' := (mem_unitFundamentalTranslate_iff x z').mp hx'
  simp_all

theorem iUnion_unitFundamentalTranslate :
    ⋃ z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
      unitFundamentalTranslate z = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i ↦ unitFloor x i,
    (mem_unitFundamentalTranslate_iff _ _).mpr rfl⟩

theorem unitFundamentalTranslate_eq_image
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitFundamentalTranslate z =
      (fun x ↦ x + unitCoordinateShift z) '' unitFundamentalParamSet K := by
  ext x
  constructor
  · intro hx
    refine ⟨x - unitCoordinateShift z, hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa [unitFundamentalTranslate] using hy

theorem setIntegral_unitFundamentalTranslate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E)
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    (∫ x in unitFundamentalTranslate z, f x) =
      ∫ x in unitFundamentalParamSet K,
        f (x + unitCoordinateShift z) := by
  rw [unitFundamentalTranslate_eq_image]
  let e : realSpace K ≃ᵐ realSpace K :=
    MeasurableEquiv.addRight (unitCoordinateShift z)
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by
      simpa [e] using
        (map_add_right_eq_self volume (unitCoordinateShift z))⟩
  exact he.setIntegral_image_emb e.measurableEmbedding f
    (unitFundamentalParamSet K)

theorem integral_eq_tsum_setIntegral_unitFundamentalTranslate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E) (hf : Integrable f) :
    (∫ x, f x) =
      ∑' z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
        ∫ x in unitFundamentalTranslate z, f x := by
  calc
    (∫ x, f x) =
        ∫ x in ⋃ z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
          unitFundamentalTranslate z, f x := by
      rw [iUnion_unitFundamentalTranslate, setIntegral_univ]
    _ = _ := integral_iUnion measurableSet_unitFundamentalTranslate
      pairwise_disjoint_unitFundamentalTranslate (by
        rw [iUnion_unitFundamentalTranslate]
        simp_all)

theorem integral_eq_tsum_setIntegral_add_unitCoordinateShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realSpace K → E) (hf : Integrable f) :
    (∫ x, f x) =
      ∑' z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
        ∫ x in unitFundamentalParamSet K,
          f (x + unitCoordinateShift z) := by
  rw [integral_eq_tsum_setIntegral_unitFundamentalTranslate f hf]
  congr 1
  funext z
  exact setIntegral_unitFundamentalTranslate f z

theorem integral_comp_expMapBasis_eq_tsum_unitSlab
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : realSpace K → E) (hg : Integrable (fun x ↦ g (expMapBasis x))) :
    (∫ x, g (expMapBasis x)) =
      ∑' z : {w : InfinitePlace K // w ≠ w₀} → ℤ,
        ∫ x in unitFundamentalParamSet K,
          g ((fun w ↦ w (fundamentalUnitForShift z)) *
            expMapBasis x) := by
  rw [integral_eq_tsum_setIntegral_add_unitCoordinateShift _ hg]
  congr 1
  funext z
  apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
  intro x _
  change g (expMapBasis (x + unitCoordinateShift z)) =
    g ((fun w ↦ w (fundamentalUnitForShift z)) * expMapBasis x)
  rw [expMapBasis_add_unitCoordinateShift]

open scoped Classical in
theorem setIntegral_expMapBasis_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (realSpace K)} (hs : MeasurableSet s)
    (f : realSpace K → E) :
    (∫ q in expMapBasis '' s, f q) =
      ∫ x in s,
        (Real.exp (x w₀ * Module.finrank ℚ K) *
          (∏ w : {w : InfinitePlace K // IsComplex w},
            expMapBasis x w.1)⁻¹ *
          2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * regulator K) •
            f (expMapBasis x) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt)
    (injective_expMapBasis K).injOn]
  apply setIntegral_congr_fun hs
  intro x _
  change |(fderiv_expMapBasis K x).det| • f (expMapBasis x) = _
  rw [abs_det_fderiv_expMapBasis]

open scoped Classical in
theorem integrableOn_expMapBasis_image_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (realSpace K)} (hs : MeasurableSet s)
    (f : realSpace K → E) :
    IntegrableOn f (expMapBasis '' s) ↔
      IntegrableOn
        (fun x ↦
          (Real.exp (x w₀ * Module.finrank ℚ K) *
            (∏ w : {w : InfinitePlace K // IsComplex w},
              expMapBasis x w.1)⁻¹ *
            2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K * regulator K) •
              f (expMapBasis x))
        s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt)
    (injective_expMapBasis K).injOn]
  apply integrableOn_congr_fun _ hs
  intro x _
  dsimp only
  rw [abs_det_fderiv_expMapBasis]

end NumberField.Odlyzko
