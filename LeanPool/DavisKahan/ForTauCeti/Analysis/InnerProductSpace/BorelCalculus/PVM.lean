/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Multiplicative
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Projection-valued measures from the Borel calculus

Applying the bounded Borel functional calculus to indicator functions turns a
normal operator into a projection-valued measure.  The sets are indexed along an
arbitrary measurable *relabelling* `κ : spectrum ℂ a → ℝ`, because
`TauCeti.ProjValMeasure` is a measure on the Borel sets of `ℝ` while the
spectrum of a normal operator lives in `ℂ`; for a self-adjoint operator `κ` will
be the real part, and for the Cayley transform of an unbounded self-adjoint
operator it will be the inverse Cayley map.

## Sources

Applying a functional calculus to indicator functions to obtain a
projection-valued measure is the standard route to the spectral theorem for a
normal operator; see
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` for the
sources of the chain.  The relabelling parameter `κ` is this library's own, and is
there so that the unbounded Cayley case is an instance rather than a special case.

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`.
The target structure `TauCeti.ProjValMeasure` is Spectra's, ported in
`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`; the
construction filling it here is not.
-/

@[expose] public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- The indicator of a measurable set is an admissible symbol. -/
theorem isBddMeasurable_indicator {S : Set (spectrum ℂ a)} (hS : MeasurableSet S) :
    IsBddMeasurable (S.indicator (fun _ => (1 : ℂ))) := by
  refine ⟨measurable_const.indicator hS, 1, zero_le_one, fun x => ?_⟩
  by_cases hx : x ∈ S <;> simp [hx]

section Projections

variable (ha : IsStarNormal a) {κ : spectrum ℂ a → ℝ} (hκ : Measurable κ)

/-- The spectral projection attached to a Borel subset of `ℝ`, pulled back along
the relabelling `κ`. -/
-- `@[expose]` here is a recorded compromise, not a clean carve-out. Consumers in this
-- module rewrite by definition name (`rw [specProjection, spectralPVM, specProj]`) and
-- index subtypes by `.domain`, so the bodies must reduce. The rubric-clean fix is a
-- `_def` lemma per definition plus rewiring every call site, which is a larger refactor
-- than a conversion pass; it is recorded debt rather than an endorsement.
noncomputable def specProj (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  borelCalculus ha (isBddMeasurable_indicator (a := a) (hκ hB))

/-- Rewrite form of `specProj`, so a call site need not unfold the definition.

Added 2026-07-30 by `FTC-EXPOSE-SPECMEAS` slice 2. Consumers were doing
`rw [BorelCalculus.specProj]`, which needs the body exposed; this is the lemma the
`api-design` rubric asks for instead. -/
theorem specProj_def (B : Set ℝ) (hB : MeasurableSet B) :
    specProj (H := H) ha hκ B hB
      = borelCalculus ha (isBddMeasurable_indicator (a := a) (hκ hB)) := (rfl)

/-- The relabelled diagonal measure. -/
-- `@[expose]` for the same reason as `toProjValMeasure`, whose exposed body references
-- this one. Recorded debt, not an endorsement.
noncomputable def specDiag (κ' : spectrum ℂ a → ℝ) (ξ : H) : Measure ℝ :=
  Measure.map κ' (diagMeasure ha ξ)

/-- Rewrite form of `specDiag`, so a call site need not unfold the definition. -/
theorem specDiag_def (κ' : spectrum ℂ a → ℝ) (ξ : H) :
    specDiag ha κ' ξ = Measure.map κ' (diagMeasure ha ξ) := (rfl)

include hκ in
/-- The spectral diagonal measures are finite. -/
theorem isFiniteMeasure_specDiag (ξ : H) : IsFiniteMeasure (specDiag ha κ ξ) := by
  refine ⟨?_⟩
  rw [specDiag, Measure.map_apply hκ MeasurableSet.univ]
  exact measure_lt_top _ _

/-- The weld: the diagonal matrix element of a spectral projection is the mass
the relabelled diagonal measure gives to the set. -/
theorem inner_specProj_self (B : Set ℝ) (hB : MeasurableSet B) (ξ : H) :
    ⟪ξ, specProj ha hκ B hB ξ⟫_ℂ = (((specDiag ha κ ξ) B).toReal : ℂ) := by
  rw [specProj, inner_borelCalculus_self, integral_indicator_const _ (hκ hB),
    specDiag, Measure.map_apply hκ hB]
  simp [Complex.real_smul, MeasureTheory.measureReal_def]

/-- The whole line carries the identity. -/
theorem specProj_univ :
    specProj (H := H) ha hκ Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [inner_specProj_self]
  have hm : ((specDiag ha κ ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
    rw [specDiag, Measure.map_apply hκ MeasurableSet.univ, Set.preimage_univ,
      diagMeasure_univ_toReal]
  rw [hm]
  -- names the application so the norm bound applies to it directly.
  change (((‖ξ‖ ^ 2 : ℝ)) : ℂ) = ⟪ξ, ξ⟫_ℂ
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Multiplicativity: intersection of sets is composition of projections. -/
theorem specProj_inter (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    specProj (H := H) ha hκ B₁ hB₁ * specProj ha hκ B₂ hB₂
      = specProj ha hκ (B₁ ∩ B₂) (hB₁.inter hB₂) := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  have hprod : (fun x => (κ ⁻¹' B₁).indicator (fun _ => (1 : ℂ)) x *
        (κ ⁻¹' B₂).indicator (fun _ => (1 : ℂ)) x)
      = (κ ⁻¹' (B₁ ∩ B₂)).indicator (fun _ => (1 : ℂ)) := by
    ext x
    by_cases hx1 : x ∈ κ ⁻¹' B₁ <;> by_cases hx2 : x ∈ κ ⁻¹' B₂ <;>
      simp only [Set.mem_preimage] at hx1 hx2 <;>
      simp [Set.mem_preimage, Set.mem_inter_iff, hx1, hx2]
  have hL : ⟪ψ, (specProj (H := H) ha hκ B₁ hB₁ * specProj ha hκ B₂ hB₂) ξ⟫_ℂ
      = pair ha (fun x => (κ ⁻¹' B₁).indicator (fun _ => (1 : ℂ)) x *
          (κ ⁻¹' B₂).indicator (fun _ => (1 : ℂ)) x) ψ ξ :=
    (pair_mul_eq_inner_comp ha (isBddMeasurable_indicator (a := a) (hκ hB₁))
      (isBddMeasurable_indicator (a := a) (hκ hB₂)) ψ ξ).symm
  rw [hL, hprod, specProj, inner_borelCalculus]

/-- **The projection-valued measure of a normal operator**, indexed along a
measurable relabelling `κ` of its spectrum. -/
-- `@[expose]` for the same reason as `spectralPVM`, which is built from this and whose
-- exposed body cannot reference an unexposed one. Recorded debt, not an endorsement.
noncomputable def toProjValMeasure : TauCeti.ProjValMeasure H where
  proj := specProj ha hκ
  diag := specDiag ha κ
  diag_finite := isFiniteMeasure_specDiag ha hκ
  inner_proj := inner_specProj_self ha hκ
  proj_univ := specProj_univ ha hκ
  proj_inter := specProj_inter ha hκ

/-- The projections of the derived PVM are the spectral projections. -/
@[simp] theorem toProjValMeasure_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (toProjValMeasure (H := H) ha hκ).proj B hB = specProj ha hκ B hB := (rfl)
/-- Its diagonal measures are the spectral diagonal measures. -/
@[simp] theorem toProjValMeasure_diag (ξ : H) :
    (toProjValMeasure (H := H) ha hκ).diag ξ = specDiag ha κ ξ := (rfl)
end Projections

section Coordinate

variable (ha : IsStarNormal a)

/-- The coordinate symbol -- the inclusion of the spectrum into `ℂ` -- is an
admissible symbol. -/
theorem isBddMeasurable_coord :
    IsBddMeasurable (fun w : spectrum ℂ a => (w : ℂ)) :=
  IsBddMeasurable.of_continuous ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))

/-- **The Borel calculus of the coordinate symbol is the operator itself.**  It
extends the continuous functional calculus, where this is `cfcHom_id`. -/
theorem borelCalculus_coord :
    borelCalculus ha (isBddMeasurable_coord (a := a)) = a :=
  (borelCalculus_of_continuous ha ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
    (isBddMeasurable_coord (a := a))).trans (cfcHom_id ha)

/-- **Every value of the Borel calculus commutes with its operator.**  This is
the reason spectral subspaces reduce their operator, and it needs no spectral
theorem beyond multiplicativity: `a` is itself a value of the calculus. -/
theorem borelCalculus_comm_self {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    a * borelCalculus ha hf = borelCalculus ha hf * a := by
  have h := borelCalculus_comm ha (isBddMeasurable_coord (a := a)) hf
  rwa [borelCalculus_coord ha] at h

end Coordinate

section BoundedSelfAdjoint

variable {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)

/-- The real part, as a measurable relabelling of the spectrum of a bounded
self-adjoint operator.  Its spectrum is real, so this is a bijection onto the
spectrum and no Cayley detour is needed. -/
noncomputable def reCoord (w : spectrum ℂ T) : ℝ := (w : ℂ).re

omit [CompleteSpace H] in
/-- The real-part relabelling of the spectrum is measurable, which is what lets a PVM on `ℝ` be
pushed forward from one on the spectrum. -/
theorem measurable_reCoord : Measurable (reCoord (T := T)) :=
  Complex.measurable_re.comp measurable_subtype_coe

/-- **The spectral measure of a bounded self-adjoint operator**, indexed along
the real part of its spectrum. -/
noncomputable def boundedPVM : TauCeti.ProjValMeasure H :=
  toProjValMeasure hT.isStarNormal measurable_reCoord

omit [CompleteSpace H] in
/-- The real-part relabelling, unfolded.  Consumers outside this module cannot reduce
`reCoord` by definition, so this is the rewrite form.  Deliberately not `@[simp]`:
several existing proofs match on `reCoord` syntactically. -/
theorem reCoord_apply (w : spectrum ℂ T) : reCoord w = (w : ℂ).re := (rfl)

/-- The projections of `boundedPVM` are the Borel calculus of band indicators.  Rewrite
form for consumers outside this module, where the definition bodies are not exposed. -/
theorem boundedPVM_proj (B : Set ℝ) (hB : MeasurableSet B) :
    (boundedPVM hT).proj B hB =
      borelCalculus hT.isStarNormal
        (isBddMeasurable_indicator (a := T) (measurable_reCoord hB)) := by
  rw [boundedPVM, toProjValMeasure_proj, specProj_def]

/-- The diagonal measures of `boundedPVM` are the pushforwards of the diagonal measures
along the real-part relabelling.  Rewrite form for consumers outside this module. -/
theorem boundedPVM_diag (ξ : H) :
    (boundedPVM hT).diag ξ = Measure.map reCoord (diagMeasure hT.isStarNormal ξ) := by
  rw [boundedPVM, toProjValMeasure_diag, specDiag_def]

/-- **The bridge to the continuous functional calculus.**  A spectral projection
of a bounded self-adjoint operator is the continuous functional calculus of any
continuous symbol agreeing with the indicator on the spectrum — which is all the
bounded-operator lane ever needs from a Borel calculus. -/
theorem boundedPVM_proj_eq_cfcHom (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ T, ℂ))
    (hg : ∀ w, g w = (reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    (boundedPVM hT).proj s hs = cfcHom hT.isStarNormal g := by
  rw [boundedPVM, toProjValMeasure_proj, specProj,
    ← borelCalculus_of_continuous hT.isStarNormal g (IsBddMeasurable.of_continuous g)]
  exact borelCalculus_congr_ae _ _ _ fun η =>
    Filter.Eventually.of_forall fun w => (hg w).symm

/-- **A spectral projection of a bounded self-adjoint operator commutes with
it** -- so its range and the orthogonal complement of its range are both
invariant, i.e. every spectral subspace reduces the operator. -/
theorem boundedPVM_proj_comm (s : Set ℝ) (hs : MeasurableSet s) :
    T * (boundedPVM hT).proj s hs = (boundedPVM hT).proj s hs * T := by
  rw [boundedPVM, toProjValMeasure_proj, specProj]
  exact borelCalculus_comm_self hT.isStarNormal _

/-- **The real part of the quadratic form is the integral of the real
coordinate against the diagonal measure**, together with the integrability that
makes the integral meaningful.

Stated because the two half-line bounds below are mirror images — an upper bound
from `Ici` carrying no mass, a lower bound from `Iic` — and this fact is
common to both and has no direction in it.  It was written out twice, fifteen
identical lines each time; what genuinely differs between those theorems is
only the final `integral_mono_ae` and which half-line is null. -/
private theorem re_inner_eq_integral_reCoord
    (hT : IsSelfAdjoint T) (ξ : H) :
    (⟪T ξ, ξ⟫_ℂ).re =
      ∫ w, reCoord (T := T) w ∂(diagMeasure hT.isStarNormal ξ) := by
  have hcoord : IsBddMeasurable (fun w : spectrum ℂ T => (w : ℂ)) :=
    isBddMeasurable_coord (a := T)
  have hbc : ⟪ξ, borelCalculus hT.isStarNormal hcoord ξ⟫_ℂ =
      ∫ w, (w : ℂ) ∂(diagMeasure hT.isStarNormal ξ) :=
    inner_borelCalculus_self hT.isStarNormal hcoord ξ
  rw [borelCalculus_coord hT.isStarNormal] at hbc
  have hint : Integrable (fun w : spectrum ℂ T => (w : ℂ)) (diagMeasure hT.isStarNormal ξ) :=
    hcoord.integrable _
  have hre : (⟪ξ, T ξ⟫_ℂ).re = ∫ w, ((w : ℂ)).re ∂(diagMeasure hT.isStarNormal ξ) := by
    rw [hbc]
    simpa [RCLike.re_eq_complex_re] using (integral_re (𝕜 := ℂ) hint).symm
  rw [← inner_conj_symm, Complex.conj_re]
  exact hre

/-- The real coordinate is integrable against the diagonal measure. -/
private theorem integrable_reCoord (hT : IsSelfAdjoint T) (ξ : H) :
    Integrable (fun w : spectrum ℂ T => reCoord (T := T) w)
      (diagMeasure hT.isStarNormal ξ) := by
  have hcoord : IsBddMeasurable (fun w : spectrum ℂ T => (w : ℂ)) :=
    isBddMeasurable_coord (a := T)
  simpa [reCoord, RCLike.re_eq_complex_re] using (hcoord.integrable _).re

/-- **Form bound from a spectral half-line.**  If the spectral projection of
`[c, ∞)` kills `ξ`, then the quadratic form of `T` at `ξ` is at most `c ‖ξ‖²`.

The diagonal measure of `ξ` is exactly the pushforward of the spectral measure,
so killing the projection is the same as giving `[c, ∞)` no mass — and then the
quadratic form, which *is* the integral of the coordinate against that measure
(`borelCalculus_coord` plus `inner_borelCalculus_self`), is bounded by `c` times
the total mass `‖ξ‖²`. -/
theorem re_inner_le_of_boundedPVM_proj_Ici_eq_zero (c : ℝ) {ξ : H}
    (hξ : (boundedPVM hT).proj (Set.Ici c) measurableSet_Ici ξ = 0) :
    (⟪T ξ, ξ⟫_ℂ).re ≤ c * ‖ξ‖ ^ 2 := by
  set ha := hT.isStarNormal with hha
  set μ := diagMeasure ha ξ with hμ
  -- the diagonal measure gives the closed half-line no mass
  have hnull : μ (reCoord ⁻¹' Set.Ici c) = 0 := by
    have h := (boundedPVM hT).norm_sq_proj_apply (Set.Ici c) measurableSet_Ici ξ
    rw [hξ, norm_zero] at h
    have hmap : ((boundedPVM hT).diag ξ) (Set.Ici c) = μ (reCoord ⁻¹' Set.Ici c) := by
      rw [boundedPVM, toProjValMeasure_diag, specDiag,
        Measure.map_apply measurable_reCoord measurableSet_Ici]
    rw [hmap] at h
    exact (ENNReal.toReal_eq_zero_iff _).mp (by simpa using h.symm)
      |>.resolve_right (measure_ne_top _ _)
  -- almost every spectral point lies strictly below `c`
  have hae : ∀ᵐ w ∂μ, reCoord (T := T) w ≤ c := by
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) hnull
    exact not_lt.mp fun h => hw (le_of_lt h)
  -- the quadratic form is the integral of the coordinate
  have hform : (⟪T ξ, ξ⟫_ℂ).re = ∫ w, reCoord (T := T) w ∂μ :=
    re_inner_eq_integral_reCoord hT ξ
  rw [hform]
  have hintc : Integrable (fun w : spectrum ℂ T => reCoord (T := T) w) μ :=
    integrable_reCoord hT ξ
  calc ∫ w, reCoord (T := T) w ∂μ ≤ ∫ _w : spectrum ℂ T, c ∂μ :=
        integral_mono_ae hintc (integrable_const _) hae
    _ = c * ‖ξ‖ ^ 2 := by
        rw [integral_const, smul_eq_mul, measureReal_def, ← diagMeasure_univ_toReal ha ξ]
        ring

/-- **Form bound from a spectral half-line, the other side.**  If the spectral
projection of `(-∞, c]` kills `ξ`, the quadratic form of `T` at `ξ` is at least
`c ‖ξ‖²`.  Same argument as
`re_inner_le_of_boundedPVM_proj_Ici_eq_zero`, with the inequality reversed. -/
theorem le_re_inner_of_boundedPVM_proj_Iic_eq_zero (c : ℝ) {ξ : H}
    (hξ : (boundedPVM hT).proj (Set.Iic c) measurableSet_Iic ξ = 0) :
    c * ‖ξ‖ ^ 2 ≤ (⟪T ξ, ξ⟫_ℂ).re := by
  set ha := hT.isStarNormal with hha
  set μ := diagMeasure ha ξ with hμ
  have hnull : μ (reCoord ⁻¹' Set.Iic c) = 0 := by
    have h := (boundedPVM hT).norm_sq_proj_apply (Set.Iic c) measurableSet_Iic ξ
    rw [hξ, norm_zero] at h
    have hmap : ((boundedPVM hT).diag ξ) (Set.Iic c) = μ (reCoord ⁻¹' Set.Iic c) := by
      rw [boundedPVM, toProjValMeasure_diag, specDiag,
        Measure.map_apply measurable_reCoord measurableSet_Iic]
    rw [hmap] at h
    exact (ENNReal.toReal_eq_zero_iff _).mp (by simpa using h.symm)
      |>.resolve_right (measure_ne_top _ _)
  have hae : ∀ᵐ w ∂μ, c ≤ reCoord (T := T) w := by
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) hnull
    exact le_of_lt (not_le.mp hw)
  have hform : (⟪T ξ, ξ⟫_ℂ).re = ∫ w, reCoord (T := T) w ∂μ :=
    re_inner_eq_integral_reCoord hT ξ
  rw [hform]
  have hintc : Integrable (fun w : spectrum ℂ T => reCoord (T := T) w) μ :=
    integrable_reCoord hT ξ
  calc c * ‖ξ‖ ^ 2 = ∫ _w : spectrum ℂ T, c ∂μ := by
        rw [integral_const, smul_eq_mul, measureReal_def, ← diagMeasure_univ_toReal ha ξ]
        ring
    _ ≤ ∫ w, reCoord (T := T) w ∂μ :=
        integral_mono_ae (integrable_const _) hintc hae

end BoundedSelfAdjoint

end BorelCalculus
end TauCeti
