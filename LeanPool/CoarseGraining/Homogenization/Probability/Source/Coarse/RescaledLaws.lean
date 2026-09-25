/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.Scaling

/-!
# Triadically rescaled exact coarse-source laws

The normalized source law is the pushforward by the exact carrier rescaling
`a ↦ (x ↦ a (3^k x))`.
-/

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory

/-- Scale-normalize an exact coarse-source law by triadic rescaling. -/
noncomputable def scaleNormalizedLaw {d : ℕ} (k : ℕ) (P : Measure (Carrier d)) :
    Measure (Carrier d) :=
  Measure.map (Carrier.rescale k) P

/-- Triadic scale-normalization preserves probability laws. -/
theorem isProbabilityMeasure_scaleNormalizedLaw {d : ℕ} (k : ℕ) (P : Measure (Carrier d))
    [IsProbabilityMeasure P] :
    IsProbabilityMeasure (scaleNormalizedLaw k P) := by
  unfold scaleNormalizedLaw
  infer_instance

private theorem indep_map_measurableEquiv
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {m1 m2 : MeasurableSpace β}
    (h : @ProbabilityTheory.Indep α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      (MeasurableSpace.comap (fun x : α => e x) m2) mα μ) :
    @ProbabilityTheory.Indep β m1 m2 mβ
      (@Measure.map α β mα mβ (fun x : α => e x) μ) := by
  refine (ProbabilityTheory.Indep_iff
    (m₁ := m1) (m₂ := m2) (_mΩ := mβ)
    (μ := (@Measure.map α β mα mβ (fun x : α => e x) μ))).2 ?_
  intro s t hs ht
  have hemb : @MeasurableEmbedding α β mα mβ (fun x : α => e x) := by
    exact @MeasurableEquiv.measurableEmbedding α β mα mβ e
  have hIndep := (ProbabilityTheory.Indep_iff
    (m₁ := MeasurableSpace.comap (fun x : α => e x) m1)
    (m₂ := MeasurableSpace.comap (fun x : α => e x) m2)
    (_mΩ := mα) (μ := μ)).1 h
  have hsPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m1)
      ((fun x : α => e x) ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  have htPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m2)
      ((fun x : α => e x) ⁻¹' t) :=
    ⟨t, ht, rfl⟩
  have hst := hIndep ((fun x : α => e x) ⁻¹' s)
    ((fun x : α => e x) ⁻¹' t) hsPre htPre
  have hmapInter :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ (s ∩ t)
  have hmapS :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) s =
        μ ((fun x : α => e x) ⁻¹' s) :=
    @MeasurableEmbedding.map_apply α β mα mβ (fun x : α => e x) hemb μ s
  have hmapT :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) t =
        μ ((fun x : α => e x) ⁻¹' t) :=
    @MeasurableEmbedding.map_apply α β mα mβ (fun x : α => e x) hemb μ t
  calc
    (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t)
        = μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := hmapInter
    _ = μ (((fun x : α => e x) ⁻¹' s) ∩ ((fun x : α => e x) ⁻¹' t)) := rfl
    _ = μ ((fun x : α => e x) ⁻¹' s) * μ ((fun x : α => e x) ⁻¹' t) := hst
    _ = (@Measure.map α β mα mβ (fun x : α => e x) μ) s *
          (@Measure.map α β mα mβ (fun x : α => e x) μ) t := by
      rw [hmapS, hmapT]

namespace IsStationary

/-- Exact source stationarity is preserved by triadic scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : Measure (Carrier d)}
    (hP : IsStationary P) (k : ℕ) :
    IsStationary (scaleNormalizedLaw k P) := by
  intro z
  rw [scaleNormalizedLaw,
    Measure.map_map (measurable_translate_globalSigma z) (measurable_rescale_globalSigma k),
    Carrier.translate_comp_rescale k z,
    ← Measure.map_map (measurable_rescale_globalSigma k)
      (measurable_translate_globalSigma (triadicScaleIntShift k z)),
    hP (triadicScaleIntShift k z)]

end IsStationary

namespace IsUnitRangeDependent

/-- Exact source unit-range dependence is preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : Measure (Carrier d)}
    (hP : IsUnitRangeDependent P) (k : ℕ) :
    IsUnitRangeDependent (scaleNormalizedLaw k P) := by
  intro U V hU hV hUV
  let hDU : MeasurableSet (triadicDilateSet k U) :=
    measurableSet_triadicDilateSet k hU
  let hDV : MeasurableSet (triadicDilateSet k V) :=
    measurableSet_triadicDilateSet k hV
  let e := Carrier.rescaleMeasurableEquiv (d := d) k
  have hIndepDilated : ProbabilityTheory.Indep
      (localSigma (triadicDilateSet k U) hDU)
      (localSigma (triadicDilateSet k V) hDV) P :=
    hP (triadicDilateSet k U) (triadicDilateSet k V) hDU hDV
      (EuclideanUnitSeparated.triadicDilateSet hUV k)
  have hUle : MeasurableSpace.comap
      (fun a : Carrier d => Carrier.rescale k a) (localSigma U hU) ≤
      localSigma (triadicDilateSet k U) hDU := by
    simpa [hDU] using (measurable_rescale_localSigma (d := d) k U hU).comap_le
  have hVle : MeasurableSpace.comap
      (fun a : Carrier d => Carrier.rescale k a) (localSigma V hV) ≤
      localSigma (triadicDilateSet k V) hDV := by
    simpa [hDV] using (measurable_rescale_localSigma (d := d) k V hV).comap_le
  have hComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun a : Carrier d => Carrier.rescale k a) (localSigma U hU))
      (MeasurableSpace.comap (fun a : Carrier d => Carrier.rescale k a) (localSigma V hV)) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hIndepDilated hUle) hVle
  have hMap := indep_map_measurableEquiv (μ := P) e hComap
  simpa [scaleNormalizedLaw, e] using! hMap

end IsUnitRangeDependent

namespace IsIsotropicAndAdjointInvariant

/-- Exact source isotropy and adjoint invariance are preserved by triadic
scale-normalization. -/
theorem scaleNormalized {d : ℕ} {P : Measure (Carrier d)}
    (hP : IsIsotropicAndAdjointInvariant P) (k : ℕ) :
    IsIsotropicAndAdjointInvariant (scaleNormalizedLaw k P) := by
  constructor
  · intro R hR
    rw [scaleNormalizedLaw,
      Measure.map_map (measurable_rotate_globalSigma R hR) (measurable_rescale_globalSigma k),
      Carrier.rotate_comp_rescale R hR k,
      ← Measure.map_map (measurable_rescale_globalSigma k)
        (measurable_rotate_globalSigma R hR),
      hP.1 R hR]
  · rw [scaleNormalizedLaw,
      Measure.map_map measurable_adjoint_globalSigma (measurable_rescale_globalSigma k),
      Carrier.adjoint_comp_rescale k,
      ← Measure.map_map (measurable_rescale_globalSigma k) measurable_adjoint_globalSigma,
      hP.2]

end IsIsotropicAndAdjointInvariant

end Homogenization.Source.Coarse
