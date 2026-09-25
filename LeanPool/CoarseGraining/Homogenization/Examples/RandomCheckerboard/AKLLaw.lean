/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Examples.RandomCheckerboard.Basic
public import LeanPool.CoarseGraining.Homogenization.Probability.Source.AKL.Laws
public import LeanPool.CoarseGraining.Homogenization.Probability.Source.AKL.RegQuotientAdapter
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.RestrictionBridge

/-!
# The AKL Bernoulli checkerboard law

The Bernoulli checkerboard, viewed through AKL's a.e.-quotient carrier.  The
regular checkerboard is only used in the forward, measurable direction supplied
by `regularToAKL`; no quotient representative is chosen here.
-/

@[expose] public section

namespace Homogenization.Examples.RandomCheckerboard.AKL

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The regular checkerboard realization with the fixed `(1, Θ)` a.e.
ellipticity witness required to enter AKL's quotient carrier. -/
private def regularCheckerCarrier {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    Sample d → Source.AKL.RegularAKLCarrier d Θ :=
  fun ω => ⟨checkerRegField 1 Θ ω, Filter.Eventually.of_forall fun x =>
    scalarMatrix_isEllipticMatrix_between (d := d) one_pos hΘ
      (scalarAt_eq_lam_or_Lam (lam := (1 : ℝ)) (Lam := Θ) ω x)⟩

/-- The literal AKL quotient-carrier realization of a checkerboard sample. -/
def checkerCarrier {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    Sample d → Source.AKL.Carrier d Θ :=
  Source.AKL.regularToAKL ∘ regularCheckerCarrier hΘ

private theorem measurable_regularCheckerCarrier_local {d : ℕ} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (U : Source.AKL.BorelRegion d) :
    @Measurable (Sample d) (Source.AKL.RegularAKLCarrier d Θ)
      (sampleCellsSigma (cellsMeeting U.1)) (Source.AKL.regularLocalSigma U)
      (regularCheckerCarrier hΘ) := by
  have hregular : @Measurable (Sample d) (RegCoeffField d)
      (sampleCellsSigma (cellsMeeting U.1)) (LocalSigmaR U.1)
      (checkerRegField 1 Θ) :=
    (measurable_checkerRegField_restrictionSigmaR 1 Θ U.1 U.2).mono le_rfl
      (localSigmaR_le_restrictionSigmaR U.1 U.2)
  rw [measurable_iff_comap_le, Source.AKL.regularLocalSigma]
  have hcomp :
      MeasurableSpace.comap (regularCheckerCarrier hΘ)
        (MeasurableSpace.comap
          (Subtype.val : Source.AKL.RegularAKLCarrier d Θ → RegCoeffField d)
          (LocalSigmaR U.1)) =
      MeasurableSpace.comap
        ((Subtype.val : Source.AKL.RegularAKLCarrier d Θ → RegCoeffField d) ∘
          regularCheckerCarrier hΘ)
        (LocalSigmaR U.1) :=
    MeasurableSpace.comap_comp
  rw [hcomp]
  exact hregular.comap_le

private theorem measurable_checkerCarrier_local {d : ℕ} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (U : Source.AKL.BorelRegion d) :
    @Measurable (Sample d) (Source.AKL.Carrier d Θ)
      (sampleCellsSigma (cellsMeeting U.1)) (Source.AKL.localSigma U)
      (checkerCarrier hΘ) := by
  exact (Source.AKL.regularToAKL_measurable_local U).comp
    (measurable_regularCheckerCarrier_local hΘ U)

private theorem measurable_checkerCarrier {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    @Measurable (Sample d) (Source.AKL.Carrier d Θ) inferInstance
      (Source.AKL.globalSigma d Θ) (checkerCarrier hΘ) := by
  simpa only [Source.AKL.globalSigma] using!
    (measurable_checkerCarrier_local hΘ
      (⟨Set.univ, MeasurableSet.univ⟩ : Source.AKL.BorelRegion d)).mono
        (sampleCellsSigma_le _) le_rfl

/-- The AKL law obtained by pushing the Bernoulli product measure forward
through the exact quotient carrier. -/
def law (d : ℕ) (Θ : ℝ) (hΘ : 1 ≤ Θ) (p : ℝ≥0) (hp : p ≤ 1) :
    Source.AKL.Law d Θ :=
  letI : MeasurableSpace (Source.AKL.Carrier d Θ) := Source.AKL.globalSigma d Θ
  Measure.map (checkerCarrier hΘ) (sampleMeasure d p hp)

instance instIsProbabilityMeasure_law (d : ℕ) (Θ : ℝ) (hΘ : 1 ≤ Θ)
    (p : ℝ≥0) (hp : p ≤ 1) :
    @IsProbabilityMeasure (Source.AKL.Carrier d Θ) (Source.AKL.globalSigma d Θ)
      (law d Θ hΘ p hp) := by
  let : MeasurableSpace (Source.AKL.Carrier d Θ) := Source.AKL.globalSigma d Θ
  rw [law]
  infer_instance

theorem isProbabilityMeasure_law (d : ℕ) (Θ : ℝ) (hΘ : 1 ≤ Θ)
    (p : ℝ≥0) (hp : p ≤ 1) :
    @IsProbabilityMeasure (Source.AKL.Carrier d Θ) (Source.AKL.globalSigma d Θ)
      (law d Θ hΘ p hp) :=
  inferInstance

private theorem translate_checkerCarrier {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    (z : Fin d → ℤ) (ω : Sample d) :
    Source.AKL.translate z (checkerCarrier hΘ ω) =
      checkerCarrier hΘ (shiftSample z ω) := by
  apply Subtype.ext
  apply AEEqFun.ext
  have hregular_shift : ∀ᵐ x ∂volume,
      (checkerCarrier hΘ ω).1 (x + Source.AKL.intTranslation z) =
        (regularCheckerCarrier hΘ ω).1 (x + Source.AKL.intTranslation z) :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
      (Source.AKL.regularToAKL_ae_eq (regularCheckerCarrier hΘ ω))
  filter_upwards [Source.AKL.translateField_ae z (checkerCarrier hΘ ω).1,
    hregular_shift,
    Source.AKL.regularToAKL_ae_eq (regularCheckerCarrier hΘ (shiftSample z ω))]
      with x htranslate hregular hshift
  change Source.AKL.translateField z (checkerCarrier hΘ ω).1 x =
    (checkerCarrier hΘ (shiftSample z ω)).1 x
  rw [htranslate]
  calc
    (checkerCarrier hΘ ω).1 (x + Source.AKL.intTranslation z) =
        (regularCheckerCarrier hΘ ω).1 (x + Source.AKL.intTranslation z) := hregular
    _ = (regularCheckerCarrier hΘ (shiftSample z ω)).1 x :=
      congrArg (fun a : RegCoeffField d => a x)
        (translateReg_checkerRegField (lam := (1 : ℝ)) (Lam := Θ) z ω)
    _ = (Source.AKL.regularToAKL (regularCheckerCarrier hΘ (shiftSample z ω))).1 x :=
      hshift.symm
    _ = (checkerCarrier hΘ (shiftSample z ω)).1 x := rfl

/-- The AKL quotient checkerboard law is invariant under integer translations. -/
theorem stationary_law {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    (p : ℝ≥0) (hp : p ≤ 1) : Source.AKL.Stationary (law d Θ hΘ p hp) := by
  let : MeasurableSpace (Source.AKL.Carrier d Θ) := Source.AKL.globalSigma d Θ
  intro z
  rw [law]
  calc
    Measure.map (Source.AKL.translate z)
        (Measure.map (checkerCarrier hΘ) (sampleMeasure d p hp)) =
        Measure.map (fun ω : Sample d => Source.AKL.translate z (checkerCarrier hΘ ω))
          (sampleMeasure d p hp) := by
      simpa [Function.comp] using! Measure.map_map
        (Source.AKL.measurable_translate_global z) (measurable_checkerCarrier hΘ)
        (μ := sampleMeasure d p hp)
    _ = Measure.map (fun ω : Sample d => checkerCarrier hΘ (shiftSample z ω))
          (sampleMeasure d p hp) := by
      congr 1
      funext ω
      exact translate_checkerCarrier hΘ z ω
    _ = Measure.map (checkerCarrier hΘ)
          (Measure.map (shiftSample z) (sampleMeasure d p hp)) := by
      symm
      simpa [Function.comp] using! Measure.map_map (measurable_checkerCarrier hΘ)
        (measurable_shiftSample z) (μ := sampleMeasure d p hp)
    _ = Measure.map (checkerCarrier hΘ) (sampleMeasure d p hp) := by
      rw [sampleMeasure_map_shiftSample z p hp]

/-- The AKL quotient checkerboard law has unit range for AKL's sup-metric
separation relation. -/
theorem unitRangeDependent_law {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    (p : ℝ≥0) (hp : p ≤ 1) : Source.AKL.UnitRangeDependent (law d Θ hΘ p hp) := by
  let : MeasurableSpace (Source.AKL.Carrier d Θ) := Source.AKL.globalSigma d Θ
  intro U V hUV
  rw [law]
  have hcells : Disjoint (cellsMeeting U.1) (cellsMeeting V.1) :=
    disjoint_cellsMeeting_of_areUnitSeparated (by
      intro x y hx hy
      simpa only [Source.AKL.unitSeparated, Source.AKL.supDist, dist_eq_norm] using
        hUV hx hy)
  have hIndCells : Indep (sampleCellsSigma (cellsMeeting U.1))
      (sampleCellsSigma (cellsMeeting V.1)) (sampleMeasure d p hp) :=
    indep_sampleCellsSigma_of_disjoint hcells p hp
  rw [Indep_iff]
  intro s t hs ht
  have hmeas := measurable_checkerCarrier (d := d) hΘ
  have hs_ambient : @MeasurableSet (Source.AKL.Carrier d Θ)
      (Source.AKL.globalSigma d Θ) s :=
    (Source.AKL.localSigma_mono (Set.subset_univ _)) s hs
  have ht_ambient : @MeasurableSet (Source.AKL.Carrier d Θ)
      (Source.AKL.globalSigma d Θ) t :=
    (Source.AKL.localSigma_mono (Set.subset_univ _)) t ht
  have hst_ambient : @MeasurableSet (Source.AKL.Carrier d Θ)
      (Source.AKL.globalSigma d Θ) (s ∩ t) := hs_ambient.inter ht_ambient
  have hs_pre : @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting U.1))
      (checkerCarrier hΘ ⁻¹' s) :=
    (measurable_checkerCarrier_local hΘ U) hs
  have ht_pre : @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting V.1))
      (checkerCarrier hΘ ⁻¹' t) :=
    (measurable_checkerCarrier_local hΘ V) ht
  have hpre_ind := (Indep_iff
      (sampleCellsSigma (cellsMeeting U.1)) (sampleCellsSigma (cellsMeeting V.1))
      (sampleMeasure d p hp)).1 hIndCells (checkerCarrier hΘ ⁻¹' s)
        (checkerCarrier hΘ ⁻¹' t) hs_pre ht_pre
  rw [Measure.map_apply hmeas hst_ambient, Measure.map_apply hmeas hs_ambient,
    Measure.map_apply hmeas ht_ambient]
  simpa [Set.preimage_inter] using hpre_ind

/-- The exact AKL probability package for the Bernoulli checkerboard. -/
theorem probabilisticAssumptions {d : ℕ} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    (p : ℝ≥0) (hp : p ≤ 1) : Source.AKL.ProbabilisticAssumptions (law d Θ hΘ p hp) where
  stationary := stationary_law hΘ p hp
  unitRange := unitRangeDependent_law hΘ p hp

end

end Homogenization.Examples.RandomCheckerboard.AKL
