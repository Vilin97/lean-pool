/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.LpTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientSpatial

/-!
# Actual mixed spatial/angular translations on the cylinder

The parameter is the real covering space R³×R. Its action on ordinary
L²(R³×AddCircle) is the genuine measure-preserving translation, for arbitrary
Hilbert-valued fields. A spatial support condition is preserved under the
same qualitative margin as before; angular translation costs no margin.
-/

section

/-!
# Actual spatial translations between supported L² spaces

Translation is the genuine measure-preserving action on ordinary R³ L².
A compact support inside an open set has a translation neighborhood in
which the translated data lie in one fixed larger supported space. This
margin is qualitative and does not occur in any operator-norm constant.
-/

@[expose] public section

noncomputable section

namespace EulerLpSupportedTranslation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpSupportedSubspace
  EulerLpSupportedMultiplier EulerLpTranslation
open scoped BoundedContinuousFunction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The exact support set of a translated field. -/
def shiftedSet (a : Space) (S : Set Space) : Set Space := {x | x+a ∈ S}

/-- Translated supports remain measurable. -/
theorem shiftedSet_measurable (a : Space) (S : Set Space) (hS : MeasurableSet S) :
    MeasurableSet (shiftedSet a S) := hS.preimage (measurable_id.add measurable_const)

/-- Translation carries an actual supported L² field into its translated support set. -/
theorem translation_mem (a : Space) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ : MeasurableSet Ω)
    (hsub : shiftedSet a S ⊆ Ω) (u : supportedSpace (V := V) volume S hS) :
    translation a (u : L2Space V) ∈ supportedSpace volume Ω hΩ := by
  apply (mem_supportedSpace_ae volume Ω hΩ _).2
  have hu := (mem_supportedSpace_ae volume S hS (u : L2Space V)).1 u.property
  filter_upwards [translation_ae a (u : L2Space V),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae hu]
    with x hx hout hnot
  rw [hx]
  apply hout
  intro hs
  exact hnot (hsub hs)

/-- Actual isometric translation into a fixed larger supported space. -/
def intoLarger (a : Space) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ : MeasurableSet Ω)
    (hsub : shiftedSet a S ⊆ Ω) :
    supportedSpace (V := V) volume S hS →ₗᵢ[ℝ] supportedSpace (V := V) volume Ω hΩ where
  toLinearMap := ((translation (V := V) a).toLinearMap.comp (supportedSpace volume S
      hS).subtype).codRestrict
    (supportedSpace volume Ω hΩ) (translation_mem a S Ω hS hΩ hsub)
  norm_map' := fun u => (translation a).norm_map (u : L2Space V)

@[simp] theorem intoLarger_coe (a : Space) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ :
    MeasurableSet Ω)
    (hsub : shiftedSet a S ⊆ Ω) (u : supportedSpace (V := V) volume S hS) :
    (intoLarger a S Ω hS hΩ hsub u : L2Space V) = translation a (u : L2Space V) := rfl

/-- The translated coefficient is the literal original field at `x+a`. -/
def translatedField (A : Field (α := Space) (V := V)) (a : Space) : Field (α := Space) (V := V) :=
  EulerMeanCoefficients.translated A a

/-- Actual coefficient multiplication intertwines the support-changing translation. -/
theorem operator_intertwines (a : Space) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ :
    MeasurableSet Ω)
    (hsub : shiftedSet a S ⊆ Ω) (A : Field (α := Space) (V := V))
    (u : supportedSpace (V := V) volume S hS) :
    operator volume Ω hΩ (translatedField A a) (intoLarger a S Ω hS hΩ hsub u) =
      intoLarger a S Ω hS hΩ hsub (operator volume S hS A u) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [full_ae volume (translatedField A a) (translation a (u : L2Space V)),
    translation_ae a (u : L2Space V), translation_ae a (full volume A (u : L2Space V)),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (full_ae volume A (u : L2Space V))] with x hl hu hr ha
  change (full volume (translatedField A a) (translation a (u : L2Space V))) x =
    (translation a (full volume A (u : L2Space V))) x
  rw [hl, hu, hr, ha]
  rfl

/-- Compactly supported data have a qualitative translation neighborhood
inside any prescribed larger open support region. -/
theorem compact_support_translation_margin (K Ω : Set Space) (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hsub : K ⊆ Ω) : ∃ δ : ℝ, 0 < δ ∧ ∀ a : Space, ‖a‖ < δ → shiftedSet a K ⊆ Ω := by
  obtain ⟨δ,hδ,hinside⟩ := hK.exists_thickening_subset_open hΩ hsub
  refine ⟨δ,hδ,?_⟩
  intro a ha x hx
  apply hinside
  apply Metric.mem_thickening_iff.2
  refine ⟨x+a,hx,?_⟩
  simpa [dist_eq_norm, sub_add_eq_sub_sub] using ha

end EulerLpSupportedTranslation

end
end

end

@[expose] public section

noncomputable section

namespace EulerLpCylinderTranslation

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothLimit
  EulerLpSupportedSubspace
open scoped Topology BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

/-- Cylinder L²: an abbreviation for `Lp V 2 (liftMeasure period)`. -/
abbrev CylinderL2 (V : Type*) [NormedAddCommGroup V] := Lp V 2 (liftMeasure period)

section Translation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual translation by a real covering-space parameter. -/
def translate (a : LiftTangent) : CylinderL2 period V →ₗᵢ[ℝ] CylinderL2 period V :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain period => x+coveringMap period a)
    (measurePreserving_translation period (coveringMap period a))

theorem translate_ae (a : LiftTangent) (u : CylinderL2 period V) :
    translate period a u =ᵐ[liftMeasure period] fun x => u (x+coveringMap period a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_translation period (coveringMap period a))

@[simp] theorem translate_zero (u : CylinderL2 period V) : translate period 0 u = u := by
  apply Lp.ext
  filter_upwards [translate_ae period 0 u] with x hx
  simpa only [coveringMap, Prod.fst_zero, Prod.snd_zero, AddCircle.coe_zero, Prod.mk_zero_zero,
      add_zero] using hx

omit [Fact (0 < period)] in
theorem coveringMap_add (a b : LiftTangent) :
    coveringMap period (a+b) = coveringMap period a+coveringMap period b := by
  apply Prod.ext
  · rfl
  · simp only [coveringMap, Prod.snd_add, QuotientAddGroup.mk_add]

theorem translate_add (a b : LiftTangent) (u : CylinderL2 period V) :
    translate period a (translate period b u) = translate period (a+b) u := by
  apply Lp.ext
  filter_upwards [translate_ae period a (translate period b u), translate_ae period (a+b) u,
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae
      (translate_ae period b u)] with x ha hab hb
  rw [ha,hb,hab,coveringMap_add,add_assoc]

/-- This is an actual strongly continuous action on the full cylinder L². -/
theorem translate_continuous (u : CylinderL2 period V) :
    Continuous (fun a : LiftTangent => translate period a u) := by
  let g : LiftTangent → C(LiftDomain period,LiftDomain period) := fun a =>
    ⟨fun x => x+coveringMap period a, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add ((coveringMap_isOpenQuotient period).continuous.comp continuous_fst))
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_translation period (coveringMap period a)) (by norm_num)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The same mixed translation on actual continuous time paths. -/
def pathTranslate (a : LiftTangent) : C(K,CylinderL2 period V) →L[ℝ] C(K,CylinderL2 period V) :=
  (translate period a).toContinuousLinearMap.compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem pathTranslate_apply (a : LiftTangent) (u : C(K, CylinderL2 period V)) (t : K) :
    pathTranslate period a u t = translate period a (u t) := rfl

theorem pathTranslate_norm (a : LiftTangent) : ‖pathTranslate (K := K) (V := V) period a‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  change ‖translate period a (u t)‖ ≤ ‖u‖
  rw [LinearIsometry.norm_map]
  exact u.norm_coe_le_norm t

end Translation

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An angle-independent coefficient on the actual cylinder. -/
def fieldLift : (Space →ᵇ W) →L[ℝ] (LiftDomain period →ᵇ W) :=
  BoundedContinuousFunction.compContinuousCLM W ℝ ⟨Prod.fst,continuous_fst⟩

omit [Fact (0 < period)] in
@[simp] theorem fieldLift_apply (A : Space →ᵇ W) (x : LiftDomain period) :
    fieldLift period A x = A x.1 := rfl

omit [Fact (0 < period)] in
theorem fieldLift_norm : ‖fieldLift (W := W) period‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  exact A.norm_coe_le_norm x.1

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The bounded linear lift of an entire coefficient time path. -/
def fieldPathLift : C(K,Space →ᵇ W) →L[ℝ] C(K,LiftDomain period →ᵇ W) :=
  (fieldLift period).compLeftContinuous ℝ K

omit [CompactSpace K] [Fact (0 < period)] in
@[simp] theorem fieldPathLift_apply (A : C(K, Space →ᵇ W)) (t : K) (x : LiftDomain period) :
    fieldPathLift period A t x = A t x.1 := rfl

omit [Fact (0 < period)] in
theorem fieldPathLift_norm : ‖fieldPathLift (K := K) (W := W) period‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  exact ((A t).norm_coe_le_norm x.1).trans (A.norm_coe_le_norm t)

end Fields

/-- Support in a set of spatial labels, with arbitrary angular coordinate. -/
def spatialSet (S : Set Space) : Set (LiftDomain period) := Prod.fst ⁻¹' S

omit [Fact (0 < period)] in
theorem spatialSet_measurable (S : Set Space) (hS : MeasurableSet S) :
    MeasurableSet (spatialSet period S) := hS.preimage measurable_fst

section Supported

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The mixed translated field lies in the spatially enlarged supporting set. -/
theorem translate_mem (a : LiftTangent) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ :
    MeasurableSet Ω)
    (hsub : EulerLpSupportedTranslation.shiftedSet a.1 S ⊆ Ω)
    (u : supportedSpace (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable
        period S hS)) :
    translate period a (u : CylinderL2 period V) ∈
      supportedSpace (liftMeasure period) (spatialSet period Ω) (spatialSet_measurable period Ω hΩ)
          := by
  apply (mem_supportedSpace_ae _ _ _ _).2
  have hu := (mem_supportedSpace_ae _ _ _ (u : CylinderL2 period V)).1 u.property
  filter_upwards [translate_ae period a (u : CylinderL2 period V),
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae hu]
      with x hx hout hnot
  rw [hx]
  apply hout
  intro hs
  exact hnot (hsub hs)

/-- Actual isometric mixed translation into a fixed spatial support region. -/
def intoLarger (a : LiftTangent) (S Ω : Set Space) (hS : MeasurableSet S) (hΩ : MeasurableSet Ω)
    (hsub : EulerLpSupportedTranslation.shiftedSet a.1 S ⊆ Ω) :
    supportedSpace (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable
        period S hS) →ₗᵢ[ℝ]
      supportedSpace (V := V) (liftMeasure period) (spatialSet period Ω) (spatialSet_measurable
          period Ω hΩ) where
  toLinearMap := ((translate (V := V) period a).toLinearMap.comp
    (supportedSpace (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
        hS)).subtype).codRestrict
      (supportedSpace (liftMeasure period) (spatialSet period Ω) (spatialSet_measurable period Ω
          hΩ))
      (translate_mem period a S Ω hS hΩ hsub)
  norm_map' := fun u => (translate period a).norm_map (u : CylinderL2 period V)

end Supported

/-- Angular displacement costs no support margin; the spatial margin is purely qualitative. -/
theorem compact_support_mixed_margin (S Ω : Set Space) (hS : IsCompact S) (hΩ : IsOpen Ω) (hsub : S
    ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : LiftTangent, ‖a‖ < δ → EulerLpSupportedTranslation.shiftedSet a.1 S ⊆ Ω
        := by
  obtain ⟨δ,hδ,hm⟩ := EulerLpSupportedTranslation.compact_support_translation_margin S Ω hS hΩ hsub
  exact ⟨δ,hδ,fun a ha => hm a.1 ((norm_fst_le a).trans_lt ha)⟩

end EulerLpCylinderTranslation
