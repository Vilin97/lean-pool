/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.LpTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientSpatial

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
