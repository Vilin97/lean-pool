/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileSpectralCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.EntranceAlignedBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStressWeights

/-!
# The spectral cone of the actual aligned modulated base

This module binds the generic profile and physical-shear identities to the
same finite modulation, aligned coefficient family, and covariance target.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AlignedProfileSpectralCone

open Set Function Filter ProfileHistories ProfileSpectralCone
open scoped ContDiff Topology InnerProductSpace

/-! ## The same finite modulated profile and aligned slow coefficients -/

section Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness d)

theorem modulated_fields_radial_germ {p : Point} (hX : 0 < p.1) (heta : |p.2| ≤ 1) :
    ((fun X => (EntranceAlignedBase.modulatedCoefficients H v).phi 0 (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X => W.axis.normalization * v.profiles.f (X, p.2))) ∧
    ((fun X => (EntranceAlignedBase.modulatedCoefficients H v).axial 0 (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X => v.profiles.U (X, p.2))) := by
  constructor
  · filter_upwards [Ioi_mem_nhds hX] with X hXp
    exact (EntranceAlignedBase.modulated_zero_fields H v (p := (X, p.2)) hXp.le heta).1
  · filter_upwards [Ioi_mem_nhds hX] with X hXp
    exact (EntranceAlignedBase.modulated_zero_fields H v (p := (X, p.2)) hXp.le heta).2.1

theorem modulated_frequency_eq {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p =
      (BaseChartJets.normalizedCoordinates F.data.h p).1 ^ (-CoordinateAlgebra.A F.data.h - 1 / 2) *
        v.profiles.f (BaseChartJets.normalizedCoordinates F.data.h p).2 := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hX := normalized_X_pos hh hh1 hT hR
  have heta := BaseChartJets.normalizedCoordinates_eta hh hh1 hT
  rw [BaseChartJets.leadingFrequency_eq hh hh1 hT hR,
    (EntranceAlignedBase.modulated_zero_fields H v hX.le heta.le).1]
  field_simp [W.axis.normalization_pos.ne']

theorem modulated_frequency_pos {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v) p := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  rw [modulated_frequency_eq H v hT hR]
  exact mul_pos (Real.rpow_pos_of_pos (BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT) _)
    (v.positive_f (normalized_X_pos hh hh1 hT hR)
      (abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le))

theorem modulated_shear_eq {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    PhaseEstimates.shearVector
        (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
          (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p =
      BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p •
          !₂[-ModulatedCone.angularShear v.profiles.E (BaseChartJets.normalizedCoordinates F.data.h
              p).2,
            -ModulatedCone.signedAxialShear v.profiles.E v.profiles.U
              (BaseChartJets.normalizedCoordinates F.data.h p).2] := by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hX := normalized_X_pos hh hh1 hT hR
  have heta := (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le
  have hg := modulated_fields_radial_germ H v hX heta
  exact leading_shear_eq_profile v.profiles hh hh1 W.axis.normalization_pos.ne'
    (EntranceAlignedBase.modulated_smooth H v) hT hR
    (d.domain_nonnegative hX.le (d.parameters_contains (abs_le.mp heta)))
    (v.positive_f hX (abs_le.mp heta)).ne' hg.1 hg.2

/-- The primitive true-cone conclusion of the actual finite modulation is
converted into the two spectral cones for its own leading fields. -/
theorem modulated_spectral_cones
    (hcone : ∀ w : Point, NominalConeAssembly.activeLeft W < w.1 →
      w.1 < NominalConeAssembly.activeRight W → w.2 ∈ Icc (-1 : ℝ) 1 →
      TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne v.profiles F.data.h w)
        (ActivationStocks.profileStockTwo v.profiles F.data.h w)
        (ModulatedCone.angularShear v.profiles.E w)
        (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U w))
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hl : NominalConeAssembly.activeLeft W < (BaseChartJets.normalizedCoordinates F.data.h p).2.1)
    (hr : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 < NominalConeAssembly.activeRight W)
        :
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)
    let G₀ := BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)
    PrimaryRepresentatives.ReferenceCone (F₀ p) (PhaseEstimates.shearVector F₀ G₀ p) ∧
      PrimaryRepresentatives.TargetCone (F₀ p) (PhaseEstimates.shearVector F₀ G₀ p)
        (stressVector v.profiles F.data.h (BaseChartJets.normalizedCoordinates F.data.h p).2) := by
  dsimp only
  rw [modulated_shear_eq H v hT hR]
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hX := normalized_X_pos hh hh1 hT hR
  have heta := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le
  exact profile_spectral_cones v.profiles F.data.h
    (d.domain_nonnegative hX.le (d.parameters_contains heta)) hX (v.positive_f hX heta)
    (modulated_frequency_pos H v hT hR) (hcone _ hl hr heta)

/-- The literal covariance target is a positive chart rescaling of the
same actual zeroth stress coefficients. -/
theorem modulated_chartTarget_cones
    (hcone : ∀ w : Point, NominalConeAssembly.activeLeft W < w.1 →
      w.1 < NominalConeAssembly.activeRight W → w.2 ∈ Icc (-1 : ℝ) 1 →
      TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne v.profiles F.data.h w)
        (ActivationStocks.profileStockTwo v.profiles F.data.h w)
        (ModulatedCone.angularShear v.profiles.E w)
        (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U w))
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hl : NominalConeAssembly.activeLeft W < (BaseChartJets.normalizedCoordinates F.data.h p).2.1)
    (hr : (BaseChartJets.normalizedCoordinates F.data.h p).2.1 < NominalConeAssembly.activeRight W)
    {q : ℝ} (hq : 0 < q) (N : ℕ) (U : PartitionedCovariance.UnsignedLabel) :
    let coeff := EntranceAlignedBase.modulatedCoefficients H v
    let w := (BaseChartJets.normalizedCoordinates F.data.h p).2
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization coeff
    let G₀ := BaseChartJets.leadingAxial F.data.h coeff
    let T := PartitionedCovariance.chartTarget F.data.h q N
      ![coeff.stressTheta 0 w, coeff.stressAxial 0 w] U
    PrimaryRepresentatives.ReferenceCone (F₀ p) (PhaseEstimates.shearVector F₀ G₀ p) ∧
      PrimaryRepresentatives.TargetCone (F₀ p) (PhaseEstimates.shearVector F₀ G₀ p) !₂[T 0, T 1] :=
          by
  have hbase := modulated_spectral_cones H v hcone hT hR hl hr
  have hX := normalized_X_pos (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hT hR
  have heta := (BaseChartJets.normalizedCoordinates_eta (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hT).le
  have he := EntranceAlignedBase.modulated_leading_stress_eq H v hX.le heta
  dsimp only
  refine ⟨hbase.1, ?_⟩
  have ht := hbase.2.pos_smul (Real.rpow_pos_of_pos
    (div_pos (ChartScales.Q_pos (U.1 + N)) hq)
    (PartitionedCovariance.velocityExponent F.data.h + 1 / 2))
  convert! ht using 1
  ext i
  fin_cases i <;> simp [PartitionedCovariance.chartTarget, stressVector, he.1, he.2]

/-- Continuity of the actual leading frequency, actual radial shear, and
actual leading stress follows from the constructed smooth profile. -/
theorem modulated_continuousOn {K : Set Slow}
    (hpos : ∀ p ∈ K, 0 < p.2.2 ∧ 0 < p.1) :
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)
    let G₀ := BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)
    ContinuousOn F₀ K ∧ ContinuousOn (PhaseEstimates.shearVector F₀ G₀) K ∧
      ContinuousOn (fun p => stressVector v.profiles F.data.h
        (BaseChartJets.normalizedCoordinates F.data.h p).2) K := by
  dsimp only
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hd := EntranceAlignedBase.modulated_smooth H v
  have hF : ContinuousOn (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)) K :=
    fun p hp => (leadingFrequency_smoothAt hh hh1 hd (hpos p hp).1 (hpos p
        hp).2).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun p => ActivationContinuation.shearA v.profiles
      (BaseChartJets.normalizedCoordinates F.data.h p).2) K := by
    intro p hp
    have hx := normalized_X_pos hh hh1 (hpos p hp).1 (hpos p hp).2
    have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 (hpos p hp).1).le
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative hx.le (d.parameters_contains he)) hx (v.positive_f hx he).ne'
    exact (hs.1.continuousAt.comp_of_eq
      (BaseChartJets.normalizedCoordinates_smoothAt hh hh1 (hpos p hp).1).snd.continuousAt
          rfl).continuousWithinAt
  have hC : ContinuousOn (fun p => ActivationContinuation.shearB v.profiles
      (BaseChartJets.normalizedCoordinates F.data.h p).2) K := by
    intro p hp
    have hx := normalized_X_pos hh hh1 (hpos p hp).1 (hpos p hp).2
    have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 (hpos p hp).1).le
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative hx.le (d.parameters_contains he)) hx (v.positive_f hx he).ne'
    exact (hs.2.continuousAt.comp_of_eq
      (BaseChartJets.normalizedCoordinates_smoothAt hh hh1 (hpos p hp).1).snd.continuousAt
          rfl).continuousWithinAt
  refine ⟨hF, ?_, ?_⟩
  · apply (signedShear_continuousOn hF hA hC).congr
    intro p hp
    have hx := normalized_X_pos hh hh1 (hpos p hp).1 (hpos p hp).2
    have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 (hpos p hp).1).le
    have hs := NominalConeAssembly.modulated_shears_eq v.profiles
      (d.domain_nonnegative hx.le (d.parameters_contains he)) hx (v.positive_f hx he).ne'
    rw [modulated_shear_eq H v (hpos p hp).1 (hpos p hp).2, hs.1, hs.2]
  · apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    change ContinuousOn (fun p => (![LeadingStress.theta v.profiles F.data.h
        (BaseChartJets.normalizedCoordinates F.data.h p).2,
      LeadingStress.axial v.profiles F.data.h (BaseChartJets.normalizedCoordinates F.data.h p).2] :
          Fin 2 → ℝ)) K
    have hS (p : Slow) (hp : p ∈ K) := by
      have hx := normalized_X_pos hh hh1 (hpos p hp).1 (hpos p hp).2
      have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 (hpos p hp).1).le
      have hdom := d.domain_nonnegative hx.le (d.parameters_contains he)
      have hL : CoordinateAlgebra.L F.data.h (BaseChartJets.normalizedCoordinates F.data.h p).2.2 ≠
          0 :=
        (NaturalAxisData.L_pos W.axis.small he).ne'
      exact And.intro (LeadingStress.theta_smoothAt v.profiles F.data.h hdom hx.ne'
        (v.positive_f hx he).ne' hL) (LeadingStress.axial_smoothAt v.profiles F.data.h hdom hx.ne'
            hL)
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact fun p hp => ((hS p hp).1.continuousAt.comp_of_eq
        (BaseChartJets.normalizedCoordinates_smoothAt hh hh1 (hpos p hp).1).snd.continuousAt
            rfl).continuousWithinAt
    · exact fun p hp => ((hS p hp).2.continuousAt.comp_of_eq
        (BaseChartJets.normalizedCoordinates_smoothAt hh hh1 (hpos p hp).1).snd.continuousAt
            rfl).continuousWithinAt

/-- Uniform reference bounds and one mixed target margin for any compact
positive-time subset of the actual active annulus. -/
theorem modulated_compact_bounds (hcone : LeadingStressWeights.FullTrueCone v)
    {K : Set Slow} (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < p.2.2 ∧ 0 < p.1)
    (hactive : ∀ p ∈ K, NominalConeAssembly.activeLeft W <
      (BaseChartJets.normalizedCoordinates F.data.h p).2.1 ∧
      (BaseChartJets.normalizedCoordinates F.data.h p).2.1 < NominalConeAssembly.activeRight W) :
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)
    let G₀ := BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)
    let g₀ := PhaseEstimates.shearVector F₀ G₀
    let T₀ := fun p => stressVector v.profiles F.data.h (BaseChartJets.normalizedCoordinates
        F.data.h p).2
    ∃ M u eta delta : ℝ, 1 ≤ M ∧ 0 < u ∧ 0 < eta ∧ 0 < delta ∧
      (∀ p ∈ K, PrimaryRepresentatives.ParameterBounds M p.1 (F₀ p) (g₀ p)) ∧
      ∀ p₀ ∈ K, ∀ p ∈ K, dist p p₀ < delta →
        ⟪T₀ p, PrimaryRepresentatives.normalDirection (g₀ p₀)⟫_ℝ ≤ -eta ∧
        |PrimaryRepresentatives.c0 (F₀ p₀) (g₀ p₀) *
          ⟪T₀ p, PrimaryRepresentatives.transverseDirection (g₀ p₀)⟫_ℝ /
          ⟪T₀ p, PrimaryRepresentatives.normalDirection (g₀ p₀)⟫_ℝ| + eta ≤
          PrimaryRepresentatives.slopeRatio u := by
  dsimp only
  have hc := modulated_continuousOn H v hpos
  have hs (p : Slow) (hp : p ∈ K) := modulated_spectral_cones H v hcone
    (hpos p hp).1 (hpos p hp).2 (hactive p hp).1 (hactive p hp).2
  obtain ⟨M, hM, hb⟩ := PrimaryRepresentatives.compact_parameter_bounds hK hc.1 hc.2.1
    (fun p hp => (hpos p hp).2) (fun p hp => (hs p hp).1)
  obtain ⟨u, eta, delta, hu, he, hd, hm⟩ :=
    PrimaryRepresentatives.compact_mixed_target_margin hK hc.1 hc.2.1 hc.2.2
      (fun p hp => (hs p hp).1) (fun p hp => (hs p hp).2)
  exact ⟨M, u, eta, delta, hM, hu, he, hd, hb, hm⟩

end Modulated

/-! ## A single Euclidean direction through both zero-amplitude edges -/

/-- Plane of pair, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def planeOfPair : (ℝ × ℝ) →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => !₂[p.1, p.2]
    map_add' := by intro p q; ext i; fin_cases i <;> simp
    map_smul' := by intro c p; ext i; fin_cases i <;> simp }

theorem planeOfPair_injective : Injective planeOfPair := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun z : Plane => z 0) h
  · exact congrArg (fun z : Plane => z 1) h

/-- Plane edge factor, bundling `coefficient`, `order`, `width`, `width_pos` and the required
compatibility proofs. -/
noncomputable def planeEdgeFactor {J : Set ℝ} {c : ℝ} {S : (ℝ × ℝ) → ℝ × ℝ}
    (F : ActiveAnnulusWeight.EdgeFactor J c S) :
    ActiveAnnulusWeight.EdgeFactor J c (fun p => planeOfPair (S p)) where
  coefficient := fun p => planeOfPair (F.coefficient p)
  order := F.order
  width := F.width
  width_pos := F.width_pos
  domain := F.domain
  domain_open := F.domain_open
  boundary_mem := F.boundary_mem
  smooth := planeOfPair.contDiff.comp_contDiffOn F.smooth
  boundary_ne_zero := by
    intro eta heta hz
    apply F.boundary_ne_zero eta heta
    apply planeOfPair_injective
    simpa only [map_zero] using hz
  identity := by
    intro eta heta x hx hxw
    rw [F.identity eta heta x hx hxw, map_smul]

theorem normalDirection_pos_smul (T : Plane) {c : ℝ} (hc : 0 < c) :
    PrimaryRepresentatives.normalDirection (c • T) = PrimaryRepresentatives.normalDirection T := by
  simp only [PrimaryRepresentatives.normalDirection, norm_smul,
    Real.norm_of_nonneg hc.le, mul_inv_rev, smul_smul]
  rw [mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

private theorem normalDirection_continuousAt {S : (ℝ × ℝ) → Plane} {p : ℝ × ℝ}
    (hS : ContinuousAt S p) (hne : S p ≠ 0) :
    ContinuousAt (fun q => PrimaryRepresentatives.normalDirection (S q)) p :=
  (hS.norm.inv₀ (norm_ne_zero_iff.mpr hne)).smul hS

/-- In the interior this is the actual stress normalized in the Euclidean
norm. At the two endpoints it uses the corresponding genuine flat factor. -/
noncomputable def gluedDirection (a b : ℝ) (S BL BR : (ℝ × ℝ) → Plane)
    (p : ℝ × ℝ) : Plane :=
  if p.2 ≤ a then PrimaryRepresentatives.normalDirection (BL (p.1, p.2 - a))
  else if b ≤ p.2 then PrimaryRepresentatives.normalDirection (BR (p.1, b - p.2))
  else PrimaryRepresentatives.normalDirection (S p)

theorem gluedDirection_interior {a b : ℝ} (S BL BR : (ℝ × ℝ) → Plane) {p : ℝ × ℝ}
    (hp : p.2 ∈ Ioo a b) : gluedDirection a b S BL BR p = PrimaryRepresentatives.normalDirection (S
        p) := by
  simp [gluedDirection, not_le.mpr hp.1, not_le.mpr hp.2]

private theorem gluedDirection_left_germ {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    {eta : ℝ} (_heta : eta ∈ J) :
    gluedDirection a b S FL.coefficient FR.coefficient =ᶠ[𝓝[J ×ˢ Icc a b] (eta, a)]
      (fun q => PrimaryRepresentatives.normalDirection (FL.coefficient (q.1, q.2 - a))) := by
  have hw : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, a), q.2 < a + FL.width :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds (by linarith [FL.width_pos]))
  have hb : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, a), q.2 < b :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds hab)
  filter_upwards [self_mem_nhdsWithin, hw.filter_mono nhdsWithin_le_nhds,
    hb.filter_mono nhdsWithin_le_nhds] with q hq hqw hqb
  by_cases hqa : q.2 ≤ a
  · simp only [gluedDirection, ite_eq_left hqa]
  · simp only [gluedDirection, ite_eq_right hqa, ite_eq_right (not_le.mpr hqb)]
    have hx : 0 < q.2 - a := sub_pos.mpr (lt_of_not_ge hqa)
    have he := FL.identity q.1 hq.1 (q.2 - a) hx (by linarith)
    simp only [ActiveAnnulusWeight.leftChart] at he
    rw [show a + (q.2 - a) = q.2 by ring] at he
    change S q = _ at he
    rw [he, normalDirection_pos_smul _ (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _))]

private theorem gluedDirection_right_germ {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    {eta : ℝ} (_heta : eta ∈ J) :
    gluedDirection a b S FL.coefficient FR.coefficient =ᶠ[𝓝[J ×ˢ Icc a b] (eta, b)]
      (fun q => PrimaryRepresentatives.normalDirection (FR.coefficient (q.1, b - q.2))) := by
  have hw : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, b), b - FR.width < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds (by linarith [FR.width_pos]))
  have ha : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, b), a < q.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hab)
  filter_upwards [self_mem_nhdsWithin, hw.filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds] with q hq hqw hqa
  simp only [gluedDirection, ite_eq_right (not_le.mpr hqa)]
  by_cases hqb : b ≤ q.2
  · simp only [ite_eq_left hqb]
  · simp only [ite_eq_right hqb]
    have hx : 0 < b - q.2 := sub_pos.mpr (lt_of_not_ge hqb)
    have he := FR.identity q.1 hq.1 (b - q.2) hx (by linarith)
    simp only [ActiveAnnulusWeight.rightChart] at he
    rw [show b - (b - q.2) = q.2 by ring] at he
    change S q = _ at he
    rw [he, normalDirection_pos_smul _ (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _))]

theorem gluedDirection_continuousOn {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    (hS : ∀ p ∈ J ×ˢ Ioo a b, ContinuousAt S p)
    (hne : ∀ p ∈ J ×ˢ Ioo a b, S p ≠ 0) :
    ContinuousOn (gluedDirection a b S FL.coefficient FR.coefficient) (J ×ˢ Icc a b) := by
  rintro ⟨eta, y⟩ ⟨heta, hy⟩
  by_cases hl : y = a
  · subst y
    have hB : ContinuousAt FL.coefficient (eta, 0) := FL.smooth.continuousOn.continuousAt
      (FL.domain_open.mem_nhds (FL.boundary_mem ⟨heta, rfl⟩))
    have hn := normalDirection_continuousAt hB (FL.boundary_ne_zero eta heta)
    have hm : ContinuousAt (fun q : ℝ × ℝ => (q.1, q.2 - a)) (eta, a) :=
      continuous_fst.continuousAt.prodMk (continuous_snd.continuousAt.sub continuousAt_const)
    have hc := hn.comp_of_eq hm (by simp)
    exact hc.continuousWithinAt.congr_of_eventuallyEq_of_mem
      (gluedDirection_left_germ hab FL FR heta) ⟨heta, hy⟩
  by_cases hr : y = b
  · subst y
    have hB : ContinuousAt FR.coefficient (eta, 0) := FR.smooth.continuousOn.continuousAt
      (FR.domain_open.mem_nhds (FR.boundary_mem ⟨heta, rfl⟩))
    have hn := normalDirection_continuousAt hB (FR.boundary_ne_zero eta heta)
    have hm : ContinuousAt (fun q : ℝ × ℝ => (q.1, b - q.2)) (eta, b) :=
      continuous_fst.continuousAt.prodMk (continuousAt_const.sub continuous_snd.continuousAt)
    have hc := hn.comp_of_eq hm (by simp)
    exact hc.continuousWithinAt.congr_of_eventuallyEq_of_mem
      (gluedDirection_right_germ hab FL FR heta) ⟨heta, hy⟩
  have hmid : y ∈ Ioo a b := ⟨lt_of_le_of_ne hy.1 (Ne.symm hl), lt_of_le_of_ne hy.2 hr⟩
  have hn := normalDirection_continuousAt (hS (eta, y) ⟨heta, hmid⟩) (hne (eta, y) ⟨heta, hmid⟩)
  apply (hn.continuousWithinAt (s := J ×ˢ Icc a b)).congr_of_eventuallyEq_of_mem _ ⟨heta, hy⟩
  have hm : ∀ᶠ q : ℝ × ℝ in 𝓝 (eta, y), q.2 ∈ Ioo a b :=
    continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds hmid)
  filter_upwards [hm.filter_mono nhdsWithin_le_nhds] with q hq
  exact gluedDirection_interior S FL.coefficient FR.coefficient hq

theorem gluedDirection_norm {J : Set ℝ} {a b cL cR : ℝ}
    {S : (ℝ × ℝ) → Plane} (_hab : a < b)
    (FL : ActiveAnnulusWeight.EdgeFactor J cL (ActiveAnnulusWeight.leftChart a S))
    (FR : ActiveAnnulusWeight.EdgeFactor J cR (ActiveAnnulusWeight.rightChart b S))
    (hne : ∀ p ∈ J ×ˢ Ioo a b, S p ≠ 0) {p : ℝ × ℝ} (hp : p ∈ J ×ˢ Icc a b) :
    ‖gluedDirection a b S FL.coefficient FR.coefficient p‖ = 1 := by
  by_cases hl : p.2 ≤ a
  · have he : p.2 = a := le_antisymm hl hp.2.1
    rw [gluedDirection, ite_eq_left hl, he, sub_self]
    exact PrimaryRepresentatives.normalDirection_unit (FL.boundary_ne_zero p.1 hp.1)
  by_cases hr : b ≤ p.2
  · have he : p.2 = b := le_antisymm hp.2.2 hr
    rw [gluedDirection, ite_eq_right hl, ite_eq_left hr, he, sub_self]
    exact PrimaryRepresentatives.normalDirection_unit (FR.boundary_ne_zero p.1 hp.1)
  rw [gluedDirection_interior S FL.coefficient FR.coefficient ⟨lt_of_not_ge hl, lt_of_not_ge hr⟩]
  exact PrimaryRepresentatives.normalDirection_unit (hne p ⟨hp.1, lt_of_not_ge hl, lt_of_not_ge hr⟩)


private theorem referenceCone_of_speed {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) := by
  apply PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha
  have he : a * (a * (1 + (c / a) ^ 2)) = a ^ 2 + c ^ 2 := by
    field_simp
  have hm := mul_lt_mul_of_pos_left hv ha
  nlinarith

private theorem normalized_target_of_tilt {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (B : ℝ × ℝ) (hB : 0 < B.1)
    (hin : 0 < 1 + (c / a) * (B.2 / B.1))
    (hgap : 0 < 2 * (1 + (c / a) * (B.2 / B.1)) ^ 2 -
      (a * (1 + (c / a) ^ 2) - 2) * (B.2 / B.1 - c / a) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c])
      (PrimaryRepresentatives.normalDirection (planeOfPair B)) := by
  have hne : planeOfPair B ≠ 0 := by
    intro hz
    have hb := congrArg (fun z : Plane => z 0) hz
    change B.1 = 0 at hb
    exact hB.ne' hb
  exact (targetCone_of_tilt hF ha hv (planeOfPair B) hB hin hgap).pos_smul
    (inv_pos.mpr (norm_pos_iff.mpr hne))

section ClosedDirection

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

/-- Log shear, given by `omega • !₂[-LeadingStressWeights.logShearA v.profiles p,
-LeadingStressWeights.logShearB v.profiles p]`. -/
noncomputable def logShear (omega : ℝ) (p : ℝ × ℝ) : Plane :=
  omega • !₂[-LeadingStressWeights.logShearA v.profiles p,
    -LeadingStressWeights.logShearB v.profiles p]

/-- A single actual unit direction, continuous through both flat edges,
with the strict spectral target cone on the entire closed annulus. -/
theorem exists_closed_direction (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ D : (ℝ × ℝ) → Plane,
      ContinuousOn D (Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W)
          (LeadingStressWeights.rightEdge W)) ∧
      (∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W)
          (LeadingStressWeights.rightEdge W), ‖D p‖ = 1) ∧
      (∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Ioo (LeadingStressWeights.leftEdge W)
          (LeadingStressWeights.rightEdge W),
        D p = PrimaryRepresentatives.normalDirection
          (planeOfPair (LeadingStressWeights.logStress v.profiles F.data.h p))) ∧
      ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge
          W),
        ∀ omega : ℝ, 0 < omega → PrimaryRepresentatives.ReferenceCone omega (logShear v omega p) ∧
          PrimaryRepresentatives.TargetCone omega (logShear v omega p) (D p) := by
  obtain ⟨FL, hFL, hDL⟩ := LeadingStressWeights.inner_direction_positive v hcone
  obtain ⟨FR, hFR, hDR⟩ := LeadingStressWeights.outer_direction_positive v
  let S : (ℝ × ℝ) → Plane := fun p => planeOfPair (LeadingStressWeights.logStress v.profiles
      F.data.h p)
  let L : ActiveAnnulusWeight.EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
      (ActiveAnnulusWeight.leftChart (LeadingStressWeights.leftEdge W) S) := planeEdgeFactor FL
  let R : ActiveAnnulusWeight.EdgeFactor (Icc (-1 : ℝ) 1) 4
      (ActiveAnnulusWeight.rightChart (LeadingStressWeights.rightEdge W) S) := planeEdgeFactor FR
  let D : (ℝ × ℝ) → Plane := gluedDirection (LeadingStressWeights.leftEdge W)
      (LeadingStressWeights.rightEdge W)
    S L.coefficient R.coefficient
  have hab := LeadingStressWeights.edges_ordered W
  have hS (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)) : ContinuousAt S p
          := by
    have hm := LeadingStressWeights.logStress_mem v (p := p) hp.1
    exact planeOfPair.continuous.continuousAt.comp_of_eq
      ((LeadingStressWeights.logStress_smooth v.profiles F.data.h).continuousOn.continuousAt
        ((LeadingStressWeights.logStressDomain_open v.profiles F.data.h).mem_nhds hm)) rfl
  have hne (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)) : S p ≠ 0 := by
    intro hz
    apply LeadingStressWeights.logStress_ne_zero v hcone hp.1 hp.2
    apply planeOfPair_injective
    simpa only [map_zero] using hz
  refine ⟨D, gluedDirection_continuousOn hab L R hS hne,
    (fun p hp => gluedDirection_norm hab L R hne hp),
    (fun p hp => gluedDirection_interior S L.coefficient R.coefficient hp.2), ?_⟩
  rintro ⟨eta, y⟩ ⟨heta, hy⟩ omega homega
  have hspeed := LeadingStressWeights.closed_shear_positive v hcone heta hy
  have href : PrimaryRepresentatives.ReferenceCone omega (logShear v omega (eta, y)) :=
    referenceCone_of_speed homega hspeed.1 hspeed.2
  refine ⟨href, ?_⟩
  by_cases hl : y = LeadingStressWeights.leftEdge W
  · subst y
    obtain ⟨dl, el, O, hdl, _, hel, _, _, _, hmargin, _⟩ := hDL.1
    have hm := hmargin eta heta 0 ⟨le_rfl, hdl.le⟩
    have hin := hel.trans_le hm.1
    have hgap := hel.trans_le hm.2
    simp only [ActiveAnnulusWeight.leftChart, add_zero,
      ActiveAnnulusWeight.directionProjection, ActiveAnnulusWeight.directionGap,
      ActiveAnnulusWeight.tilt, LeadingStressWeights.logSlope,
      LeadingStressWeights.logSpeed, ActivationContinuation.shearSize] at hin hgap
    have ht := normalized_target_of_tilt homega hspeed.1 hspeed.2
      (FL.coefficient (eta, 0)) (hFL eta heta) hin hgap
    simpa only [D, gluedDirection, ite_eq_left le_rfl, sub_self, L, planeEdgeFactor,
      logShear] using ht
  by_cases hr : y = LeadingStressWeights.rightEdge W
  · subst y
    obtain ⟨dr, er, O, hdr, _, her, _, _, _, hmargin, _⟩ := hDR.1
    have hm := hmargin eta heta 0 ⟨le_rfl, hdr.le⟩
    have hin := her.trans_le hm.1
    have hgap := her.trans_le hm.2
    simp only [ActiveAnnulusWeight.rightChart, sub_zero,
      ActiveAnnulusWeight.directionProjection, ActiveAnnulusWeight.directionGap,
      ActiveAnnulusWeight.tilt, LeadingStressWeights.logSlope,
      LeadingStressWeights.logSpeed, ActivationContinuation.shearSize] at hin hgap
    have ht := normalized_target_of_tilt homega hspeed.1 hspeed.2
      (FR.coefficient (eta, 0)) (hFR eta heta) hin hgap
    simpa only [D, gluedDirection, ite_eq_right (not_le.mpr hab), ite_eq_left le_rfl,
      sub_self, R, planeEdgeFactor, logShear] using ht
  have hmid : y ∈ Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W) :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hl), lt_of_le_of_ne hy.2 hr⟩
  have hx : 0 < Real.exp y := Real.exp_pos _
  have hleft : NominalConeAssembly.activeLeft W < Real.exp y :=
    (Real.log_lt_iff_lt_exp (NominalConeAssembly.activeLeft_pos W)).mp hmid.1
  have hright : Real.exp y < NominalConeAssembly.activeRight W :=
    (Real.lt_log_iff_exp_lt (LeadingStressWeights.activeRight_pos W)).mp hmid.2
  have hdom := d.domain_nonnegative (p := (Real.exp y, eta)) hx.le (d.parameters_contains heta)
  have hf := v.positive_f (p := (Real.exp y, eta)) hx heta
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles hdom hx hf.ne'
  have ht := (profile_spectral_cones v.profiles F.data.h hdom hx hf homega
    (hcone (Real.exp y, eta) hleft hright heta)).2
  rw [hs.1, hs.2] at ht
  have he : S (eta, y) = stressVector v.profiles F.data.h (Real.exp y, eta) := rfl
  have ht' := ht.pos_smul (inv_pos.mpr (norm_pos_iff.mpr (hne (eta, y) ⟨heta, hmid⟩)))
  change PrimaryRepresentatives.TargetCone omega _ (D (eta, y))
  rw [show D (eta, y) = PrimaryRepresentatives.normalDirection (S (eta, y)) from
    gluedDirection_interior S L.coefficient R.coefficient hmid]
  simpa only [logShear, LeadingStressWeights.logShearA, LeadingStressWeights.logShearB,
    LeadingStressWeights.logPoint, PrimaryRepresentatives.normalDirection, he] using ht'

end ClosedDirection

/-- Reference set, given by `PrimaryRepresentatives.referenceCompact F.data.h
(NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)`. -/
noncomputable def referenceSet {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : Set
    Slow :=
  PrimaryRepresentatives.referenceCompact F.data.h (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W)

/-- Reference log point, given by `((PositiveRepresentatives.stableInner F.data.h p).2, Real.log
(PositiveRepresentatives.stableInner F.data.h p).1)`. -/
noncomputable def referenceLogPoint {F : OutgoingProfile.Profile} (_W : NominalProfile.Witness F)
    (p : Slow) : ℝ × ℝ :=
  ((PositiveRepresentatives.stableInner F.data.h p).2,
    Real.log (PositiveRepresentatives.stableInner F.data.h p).1)

/-- Reference point data, collecting `stable`, `radius`, `scalar`, `inner_pos`, `parameter`,
`log_mem`. -/
structure ReferencePointData {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (p : Slow) : Prop where
  stable : p ∈ PositiveRepresentatives.stableDomain F.data.h
  radius : 0 < p.1
  scalar : 0 < PositiveRepresentatives.stableQ F.data.h p
  inner_pos : 0 < (PositiveRepresentatives.stableInner F.data.h p).1
  parameter : (PositiveRepresentatives.stableInner F.data.h p).2 ∈ Icc (-1 : ℝ) 1
  log_mem : referenceLogPoint W p ∈ Icc (-1 : ℝ) 1 ×ˢ
    Icc (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W)

private theorem active_order {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    NominalConeAssembly.activeLeft W < NominalConeAssembly.activeRight W := by
  have he := Real.exp_lt_exp.mpr (LeadingStressWeights.edges_ordered W)
  simpa only [LeadingStressWeights.leftEdge, LeadingStressWeights.rightEdge,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W),
    Real.exp_log (LeadingStressWeights.activeRight_pos W)] using he

theorem referenceSet_compact {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    IsCompact (referenceSet W) :=
  PrimaryRepresentatives.referenceCompact_isCompact (ConstructedSlowBase.height_pos W).le
    (ConstructedSlowBase.height_lt_half W) (NominalConeAssembly.activeLeft_pos W) (active_order
        W).le

theorem reference_point {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {p : Slow} (hp : p ∈ referenceSet W) : ReferencePointData W p := by
  have hh := (ConstructedSlowBase.height_pos W).le
  have hh1 := ConstructedSlowBase.height_lt_half W
  have ha := NominalConeAssembly.activeLeft_pos W
  have hab := (active_order W).le
  have hs := PositiveRepresentatives.referenceCompact_subset_stableDomain hh hh1 ha hab hp
  have hX := (PositiveRepresentatives.stableQ_bounds_reference hh hh1 ha hab hp).2
  have he := PositiveRepresentatives.stableEta_mem_reference hh hh1 ha hab hp
  have hx : 0 < (PositiveRepresentatives.stableInner F.data.h p).1 := ha.trans_le hX.1
  refine ⟨hs, hs.1, (PositiveRepresentatives.stableQ_spec hs).1, hx, he, he, ?_, ?_⟩
  · exact Real.log_le_log ha hX.1
  · exact Real.log_le_log hx hX.2

section ReferenceFunctions

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

/-- Reference frequency, given by `PositiveRepresentatives.stablePullback F.data.h
(-CoordinateAlgebra.A F.data.h - 1 / 2) v.profiles.f`. -/
noncomputable def referenceFrequency : Slow → ℝ :=
  PositiveRepresentatives.stablePullback F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2)
      v.profiles.f

/-- Reference shear, constructed using `referenceFrequency`. -/
noncomputable def referenceShear (p : Slow) : Plane :=
  referenceFrequency v p • !₂[-ActivationContinuation.shearA v.profiles
      (PositiveRepresentatives.stableInner F.data.h p),
    -ActivationContinuation.shearB v.profiles (PositiveRepresentatives.stableInner F.data.h p)]

theorem referenceFrequency_pos {p : Slow} (hp : p ∈ referenceSet W) : 0 < referenceFrequency v p :=
    by
  have h := reference_point W hp
  exact mul_pos (Real.rpow_pos_of_pos h.scalar _) (v.positive_f h.inner_pos h.parameter)

theorem reference_continuous : ContinuousOn (referenceFrequency v) (referenceSet W) ∧
    ContinuousOn (referenceShear v) (referenceSet W) ∧ ContinuousOn (referenceLogPoint W)
        (referenceSet W) := by
  have hh := (ConstructedSlowBase.height_pos W).le
  have hh1 := (ConstructedSlowBase.height_lt_half W).le
  have hF : ContinuousOn (referenceFrequency v) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    exact (PositiveRepresentatives.stablePullback_smoothAt hh hh1 _ h.stable
      (v.profiles.f_smooth.contDiffAt (d.domain.isOpen.mem_nhds
        (d.domain_nonnegative h.inner_pos.le (d.parameters_contains
            h.parameter))))).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun p => ActivationContinuation.shearA v.profiles
      (PositiveRepresentatives.stableInner F.data.h p)) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative h.inner_pos.le (d.parameters_contains h.parameter)) h.inner_pos
      (v.positive_f h.inner_pos h.parameter).ne'
    exact (hs.1.comp p (PositiveRepresentatives.stableInner_smoothAt hh hh1
        h.stable)).continuousAt.continuousWithinAt
  have hC : ContinuousOn (fun p => ActivationContinuation.shearB v.profiles
      (PositiveRepresentatives.stableInner F.data.h p)) (referenceSet W) := by
    intro p hp
    have h := reference_point W hp
    have hs := NominalConeAssembly.shears_smoothAt v.profiles
      (d.domain_nonnegative h.inner_pos.le (d.parameters_contains h.parameter)) h.inner_pos
      (v.positive_f h.inner_pos h.parameter).ne'
    exact (hs.2.comp p (PositiveRepresentatives.stableInner_smoothAt hh hh1
        h.stable)).continuousAt.continuousWithinAt
  refine ⟨hF, signedShear_continuousOn hF hA hC, ?_⟩
  intro p hp
  have h := reference_point W hp
  have hs := (PositiveRepresentatives.stableInner_smoothAt hh hh1 h.stable).continuousAt
  exact (hs.snd.prodMk (hs.fst.log h.inner_pos.ne')).continuousWithinAt

theorem stableInner_eq_normalized (W : NominalProfile.Witness F) {p : Slow} (hT : 0 < p.2.2) :
    PositiveRepresentatives.stableInner F.data.h p = (BaseChartJets.normalizedCoordinates F.data.h
        p).2 := by
  rw [PositiveRepresentatives.stableInner_eq_chartInner (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hT, BaseChartJets.normalizedCoordinates_eq]
  rfl

theorem referenceFrequency_eq_actual (H : NominalConeAssembly.Certificate W)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    referenceFrequency v p = BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v) p := by
  rw [modulated_frequency_eq H v hT hR]
  unfold referenceFrequency PositiveRepresentatives.stablePullback
  rw [stableInner_eq_normalized W hT, PositiveRepresentatives.stableQ_eq_chartQ
    (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W) hT,
    BaseChartJets.normalizedCoordinates_eq]

theorem referenceShear_eq_actual (H : NominalConeAssembly.Certificate W)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) : referenceShear v p =
      PhaseEstimates.shearVector (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p :=
            by
  have hh := ConstructedSlowBase.height_pos W
  have hh1 := ConstructedSlowBase.height_lt_half W
  have hx := normalized_X_pos hh hh1 hT hR
  have he := abs_le.mp (BaseChartJets.normalizedCoordinates_eta hh hh1 hT).le
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative hx.le (d.parameters_contains he)) hx (v.positive_f hx he).ne'
  rw [referenceShear, referenceFrequency_eq_actual v H hT hR, stableInner_eq_normalized W hT,
    modulated_shear_eq H v hT hR, hs.1, hs.2]

theorem referenceLogPoint_profile {p : Slow} (hp : p ∈ referenceSet W) :
    LeadingStressWeights.logPoint (referenceLogPoint W p) = PositiveRepresentatives.stableInner
        F.data.h p := by
  have h := reference_point W hp
  apply Prod.ext
  · exact Real.exp_log h.inner_pos
  · rfl

theorem reference_cone (hcone : LeadingStressWeights.FullTrueCone v)
    {p : Slow} (hp : p ∈ referenceSet W) :
    PrimaryRepresentatives.ReferenceCone (referenceFrequency v p) (referenceShear v p) := by
  have h := reference_point W hp
  obtain ⟨ha, hv⟩ := LeadingStressWeights.closed_shear_positive v hcone h.parameter h.log_mem.2
  change 0 < LeadingStressWeights.logShearA v.profiles (referenceLogPoint W p) at ha
  change 2 < LeadingStressWeights.logSpeed v.profiles (referenceLogPoint W p) at hv
  simp only [LeadingStressWeights.logShearA, LeadingStressWeights.logShearB,
    LeadingStressWeights.logSpeed, referenceLogPoint_profile hp] at ha hv
  exact referenceCone_of_speed (referenceFrequency_pos v hp) ha hv

theorem modulated_positive_reference_cone (H : NominalConeAssembly.Certificate W)
    (hcone : LeadingStressWeights.FullTrueCone v) {p : Slow}
    (hp : p ∈ PositiveRepresentatives.positivePart (referenceSet W)) :
    PrimaryRepresentatives.ReferenceCone
      (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v) p)
      (PhaseEstimates.shearVector (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
        (EntranceAlignedBase.modulatedCoefficients H v))
        (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)) p) :=
            by
  have h := reference_cone v hcone hp.1
  rwa [referenceFrequency_eq_actual v H hp.2 (reference_point W hp.1).radius,
    referenceShear_eq_actual v H hp.2 (reference_point W hp.1).radius] at h

/-- The global normalized direction is pulled back by the genuine stable
similarity branch. This includes the regular zero-time boundary. -/
theorem exists_reference_direction (hcone : LeadingStressWeights.FullTrueCone v) :
    ∃ T : Slow → Plane, ContinuousOn T (referenceSet W) ∧
      ∀ p ∈ referenceSet W, ‖T p‖ = 1 ∧
        PrimaryRepresentatives.ReferenceCone (referenceFrequency v p) (referenceShear v p) ∧
        PrimaryRepresentatives.TargetCone (referenceFrequency v p) (referenceShear v p) (T p) ∧
        ((PositiveRepresentatives.stableInner F.data.h p).1 ∈
          Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
          T p = PrimaryRepresentatives.normalDirection
            (stressVector v.profiles F.data.h (PositiveRepresentatives.stableInner F.data.h p))) :=
                by
  obtain ⟨D, hDc, hDn, hDi, hDs⟩ := exists_closed_direction v hcone
  let T : Slow → Plane := fun p => D (referenceLogPoint W p)
  refine ⟨T, hDc.comp (reference_continuous v).2.2 (fun p hp => (reference_point W hp).log_mem), ?_⟩
  intro p hp
  have h := reference_point W hp
  have hs := hDs (referenceLogPoint W p) h.log_mem (referenceFrequency v p) (referenceFrequency_pos
      v hp)
  have hshear : logShear v (referenceFrequency v p) (referenceLogPoint W p) = referenceShear v p :=
      by
    unfold logShear referenceShear LeadingStressWeights.logShearA LeadingStressWeights.logShearB
    rw [referenceLogPoint_profile hp]
  rw [hshear] at hs
  refine ⟨hDn _ h.log_mem, hs.1, hs.2, ?_⟩
  intro hinner
  have hlog : (referenceLogPoint W p).2 ∈
      Ioo (LeadingStressWeights.leftEdge W) (LeadingStressWeights.rightEdge W) := by
    constructor
    · exact Real.log_lt_log (NominalConeAssembly.activeLeft_pos W) hinner.1
    · exact Real.log_lt_log h.inner_pos hinner.2
  have he := hDi (referenceLogPoint W p) ⟨h.parameter, hlog⟩
  change T p = _ at he
  rw [he]
  change PrimaryRepresentatives.normalDirection (stressVector v.profiles F.data.h
    (LeadingStressWeights.logPoint (referenceLogPoint W p))) = _
  rw [referenceLogPoint_profile hp]

/-- All reference parameters and the mixed target margin are now derived
for the actual positive-time representatives of the same aligned base.
The constants and one threshold precede every active band and label. -/
theorem modulated_representative_bounds (H : NominalConeAssembly.Certificate W)
    (hcone : LeadingStressWeights.FullTrueCone v) :
    let K := referenceSet W
    let F₀ := BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)
    let G₀ := BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)
    let g₀ := PhaseEstimates.shearVector F₀ G₀
    ∃ (T : Slow → Plane) (M u eta : ℝ), 1 ≤ M ∧ 0 < u ∧ 0 < eta ∧
      ContinuousOn T K ∧ (∀ p ∈ K, ‖T p‖ = 1) ∧
      (∀ p ∈ K, (PositiveRepresentatives.stableInner F.data.h p).1 ∈
        Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
        T p = PrimaryRepresentatives.normalDirection
          (stressVector v.profiles F.data.h (PositiveRepresentatives.stableInner F.data.h p))) ∧
      (∀ L : PositiveRepresentatives.ActiveLabel K,
        PrimaryRepresentatives.ParameterBounds M (PositiveRepresentatives.representative K L).1
          (F₀ (PositiveRepresentatives.representative K L))
          (g₀ (PositiveRepresentatives.representative K L))) ∧
      ∃ N : ℕ, ∀ L : PositiveRepresentatives.ActiveLabel K, N ≤ L.val.1 →
        ∀ p ∈ PositiveRepresentatives.positivePart K,
          p ∈ PrimaryRepresentatives.gridBox L.val.1 L.val.2 2 →
          ⟪T p, PrimaryRepresentatives.normalDirection (g₀ (PositiveRepresentatives.representative
              K L))⟫_ℝ ≤ -eta ∧
          |PrimaryRepresentatives.c0 (F₀ (PositiveRepresentatives.representative K L))
              (g₀ (PositiveRepresentatives.representative K L)) *
            ⟪T p, PrimaryRepresentatives.transverseDirection (g₀
                (PositiveRepresentatives.representative K L))⟫_ℝ /
            ⟪T p, PrimaryRepresentatives.normalDirection (g₀
                (PositiveRepresentatives.representative K L))⟫_ℝ| + eta ≤
            PrimaryRepresentatives.slopeRatio u := by
  dsimp only
  obtain ⟨T, hT, hspec⟩ := exists_reference_direction v hcone
  have hcont := reference_continuous v
  have hF : EqOn (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
      (EntranceAlignedBase.modulatedCoefficients H v)) (referenceFrequency v)
      (PositiveRepresentatives.positivePart (referenceSet W)) := by
    intro p hp
    exact (referenceFrequency_eq_actual v H hp.2 (reference_point W hp.1).radius).symm
  have hg : EqOn (PhaseEstimates.shearVector
      (BaseChartJets.leadingFrequency F.data.h W.axis.normalization
          (EntranceAlignedBase.modulatedCoefficients H v))
      (BaseChartJets.leadingAxial F.data.h (EntranceAlignedBase.modulatedCoefficients H v)))
      (referenceShear v) (PositiveRepresentatives.positivePart (referenceSet W)) := by
    intro p hp
    exact (referenceShear_eq_actual v H hp.2 (reference_point W hp.1).radius).symm
  obtain ⟨M, hM, hMb⟩ := PositiveRepresentatives.representative_parameter_bounds
    (referenceSet_compact W) hcont.1 hcont.2.1 (fun p hp => (reference_point W hp).radius)
      (fun p hp => (hspec p hp).2.1) hF hg
  obtain ⟨u, eta, hu, he, N, hNb⟩ := PositiveRepresentatives.representative_target_margin
    (T := T) (Text := T) (referenceSet_compact W) hcont.1 hcont.2.1 hT
      (fun p hp => (hspec p hp).2.1) (fun p hp => (hspec p hp).2.2.1)
        hF hg (fun _ _ => rfl)
  exact ⟨T, M, u, eta, hM, hu, he, hT, fun p hp => (hspec p hp).1,
    fun p hp => (hspec p hp).2.2.2, hMb, N, hNb⟩

end ReferenceFunctions

end NavierStokes.AlignedProfileSpectralCone
