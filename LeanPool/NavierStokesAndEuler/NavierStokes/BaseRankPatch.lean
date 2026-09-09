/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseChartJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanRankUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean

@[expose] public section

/-!
# The reserved mean-rank patch of the actual summed base

The positive-order repair patch precedes the mean patch.  The selected
global profiles retain their seed values beyond the repair patch; the seeds
have already been cut off there.  The full summed tangential base therefore
has the exact shaped power required by the five-row mean inverse.
-/

noncomputable section

namespace NavierStokes.BaseRankPatch

open Set Filter Function BaseChartJets
open scoped ContDiff Topology BigOperators

abbrev Slow := PhaseCalculus.Slow

theorem positive_before_mean (F : OutgoingProfile.Profile) {XR : ℝ} (hXR : 0 < XR) :
    ReservedPatches.right F XR .positive < ReservedPatches.left F XR .mean := by
  apply ReservedPatches.radius_strictMono XR hXR
  simp only [ReservedPatches.rightClock, ReservedPatches.leftClock,
    ReservedPatches.rightOffset, ReservedPatches.leftOffset]
  linarith

section Leading

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The finite modulation also ends before the later mean patch. -/
theorem modulation_before_mean :
    (ModulatedProfileAssembly.repairPatch W).right <
      ReservedPatches.left F W.controls.radius .mean :=
  (ModulatedProfileAssembly.repairPatch_before_positive W).trans
    ((ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos .positive).trans
      (positive_before_mean F W.controls.radius_pos))

theorem nominal_mean_fields {p : Inner}
    (hp : p.1 ∈ ReservedPatches.window F W.controls.radius .mean) (heta : |p.2| ≤ 1) :
    W.U p = 0 ∧ W.E p = ReservedPatches.xAmplitude F W.controls.radius p.2 *
      p.1 ^ (-(1 / 2 + F.data.core.lam)) := by
  have hmatch := AssembledSlowBase.matching_before_window W .mean hp
  have hh := W.heat_agreement (p := p) (W.controls.heatJoin_lt_radius.trans hmatch)
    (abs_le.mp heta)
  have hc := ReservedPatches.heated_fields F W.controls.radius W.controls.radius_pos
    W.heat.physical.coefficients (s := .mean) (by decide) p.2 hp
  exact ⟨hh.1.trans hc.1, hh.2.1.trans hc.2⟩

theorem modulated_mean_fields {p : Inner}
    (hp : p.1 ∈ ReservedPatches.window F W.controls.radius .mean) (heta : |p.2| ≤ 1) :
    v.profiles.U p = 0 ∧
      v.profiles.E p = ReservedPatches.xAmplitude F W.controls.radius p.2 *
        p.1 ^ (-(1 / 2 + F.data.core.lam)) := by
  have hpos := ReservedPatches.mem_window_pos F W.controls.radius W.controls.radius_pos .mean hp
  have hout : p.1 ∉ Ioo ld.modulation.left (ModulatedProfileAssembly.repairPatch W).right := by
    intro hh
    exact (not_lt_of_ge ((modulation_before_mean (W := W)).trans hp.1).le) hh.2
  have hv := v.fields_outside hout
  have hn := nominal_mean_fields (W := W) hp heta
  refine ⟨hv.2.trans hn.1, ?_⟩
  change Real.sqrt (2 * p.1) * v.profiles.f p = _
  rw [hv.1]
  exact (W.E_eq_sqrt_f hpos).symm.trans hn.2

theorem modulated_radial_mean_fields {R eta : ℝ}
    (hR : R ∈ ReservedPatches.radialWindow F W.controls.radius .mean)
    (heta : |eta| ≤ 1) :
    v.profiles.U (R ^ 2 / 2, eta) = 0 ∧
      v.profiles.E (R ^ 2 / 2, eta) =
        FiveRowRank.background F.data.core.lam
          (ReservedPatches.radialAmplitude F W.controls.radius eta) R := by
  have hx := ReservedPatches.radial_mem_window F W.controls.radius W.controls.radius_pos .mean hR
  have hp := (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .mean).trans
    hR.1
  have hf := modulated_mean_fields v (p := (R ^ 2 / 2, eta)) hx heta
  refine ⟨hf.1, ?_⟩
  rw [hf.2, ReservedPatches.square_half_power _ _ hp]
  simp only [FiveRowRank.background, ReservedPatches.radialAmplitude, mul_assoc]

end Leading

/-- Pointwise vanishing of every positive coefficient eliminates the
entire actual infinite sum, for any cutoff schedule and any scale. -/
theorem slowSum_eq_leading {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℕ → ℕ) (h : ℝ) (f : ℕ → Inner → V) (y : Chart)
    (hf : ∀ n, 0 < n → f n y.2 = 0) :
    SlowBorelBase.slowSum a h f y = f 0 y.2 := by
  have hs (n : ℕ) : SlowBorelBase.slowStage a h f n y = 0 := by
    by_cases hn : n = 0
    · subst n
      simp
    · simp only [SlowBorelBase.slowStage, SolenoidalDiagonal.cutStage,
        SlowBorelBase.positiveCoefficient, hn, ite_false, SlowBorelBase.powerCoefficient,
        hf n (Nat.pos_of_ne_zero hn), smul_zero]
  have hz : SlowBorelBase.positiveSum a h f y = 0 := by
    change (∑' n, SlowBorelBase.slowStage a h f n y) = 0
    simp only [hs, tsum_zero]
  simp only [SlowBorelBase.slowSum, hz, add_zero]

section RankParameters

/-- The slow variables here have the physical rank convention `(T,Z)`. -/
noncomputable def rankScale (h : ℝ) (s : ℝ × ℝ) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) s

noncomputable def rankEta (h : ℝ) (s : ℝ × ℝ) : ℝ :=
  SimilarityCoordinates.coordinateEta (2 * h) s

noncomputable def rankCoefficient (F : OutgoingProfile.Profile) (XR : ℝ) (s : ℝ × ℝ) : ℝ :=
  MeanRankUpdate.shapedAmplitude (ReservedPatches.radialAmplitude F XR 0) (rankEta F.data.h s)

noncomputable def rankLength (h : ℝ) (s : ℝ × ℝ) : ℝ :=
  Real.sqrt (rankScale h s)

noncomputable def rankVelocity (h : ℝ) (s : ℝ × ℝ) : ℝ :=
  rankScale h s ^ (-CoordinateAlgebra.A h)

theorem rankLength_eq_qLength (h : ℝ) : rankLength h = VariableGaugeMean.qLength (2 * h) := rfl

theorem rankScale_eq_chartQ (h R : ℝ) (s Y : ℝ × ℝ) :
    rankScale h s = MeanRankUpdate.chartQ (2 * h) (R, (s, Y)) := rfl

theorem rankEta_eq_chartEta (h R : ℝ) (s Y : ℝ × ℝ) :
    rankEta h s = MeanRankUpdate.chartEta (2 * h) (R, (s, Y)) := rfl

theorem coordinates_rankScale (h R : ℝ) (s : ℝ × ℝ) :
    (normalizedCoordinates h (R, (s.2, s.1))).1 = rankScale h s := by
  rw [normalizedCoordinates_eq]
  rfl

theorem coordinates_rankEta (h R : ℝ) (s : ℝ × ℝ) :
    (normalizedCoordinates h (R, (s.2, s.1))).2.2 = rankEta h s := by
  rw [normalizedCoordinates_eq]
  rfl

theorem rankScale_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {s : ℝ × ℝ} (hs : 0 < s.1) : 0 < rankScale h s :=
  (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) hs).1

theorem rankLength_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {s : ℝ × ℝ} (hs : 0 < s.1) : 0 < rankLength h s :=
  Real.sqrt_pos.mpr (rankScale_pos hh hh1 hs)

theorem rankVelocity_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {s : ℝ × ℝ} (hs : 0 < s.1) : 0 < rankVelocity h s :=
  Real.rpow_pos_of_pos (rankScale_pos hh hh1 hs) _

theorem rankCoefficient_pos (F : OutgoingProfile.Profile) (XR : ℝ) (s : ℝ × ℝ) :
    0 < rankCoefficient F XR s :=
  div_pos (ReservedPatches.radialAmplitude_pos F XR 0) (by positivity)

theorem rank_parameters_smooth (F : OutgoingProfile.Profile) (XR : ℝ) :
    ContDiffOn ℝ ∞ (rankCoefficient F XR) {s | 0 < s.1} ∧
      ContDiffOn ℝ ∞ (rankLength F.data.h) {s | 0 < s.1} ∧
      ContDiffOn ℝ ∞ (rankVelocity F.data.h) {s | 0 < s.1} := by
  have hh : 0 < 2 * F.data.h := by linarith [F.data.h_pos]
  have hh1 : 2 * F.data.h < 1 := by linarith [F.data.h_lt_half]
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ((MeanRankUpdate.shapedAmplitude_contDiff _).contDiffAt.comp s
      (SimilarityCoordinates.coordinateEta_smooth hh hh1 hs)).contDiffWithinAt
  · exact VariableGaugeMean.qLength_contDiffOn hh hh1
  · intro s hs
    exact ((SimilarityCoordinates.coordinateQ_smooth hh hh1 hs).rpow_const_of_ne
      (rankScale_pos F.data.h_pos F.data.h_lt_half hs).ne').contDiffWithinAt

theorem coordinates_radius_sq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {s : ℝ × ℝ} (hs : 0 < s.1) (R : ℝ) :
    (R / rankLength h s) ^ 2 / 2 =
      (normalizedCoordinates h (R, (s.2, s.1))).2.1 := by
  unfold rankLength
  rw [div_pow, Real.sq_sqrt (rankScale_pos hh hh1 hs).le, normalizedCoordinates_eq]
  unfold SimilarityHomogeneity.chartX SimilarityCoordinates.coordinateX
    SimilarityHomogeneity.chartQ rankScale
  ring

end RankParameters

section SummedBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- Every positive angular and axial coefficient vanishes past the actual
positive-order repair patch.  The selected witness retains this support. -/
theorem positive_fields_zero {n : ℕ} (hn : 0 < n) {p : Inner}
    (hp : ReservedPatches.right F W.controls.radius .positive ≤ p.1) (heta : |p.2| ≤ 1) :
    (FinalSlowBase.coefficients H v).phi n p = 0 ∧
      (FinalSlowBase.coefficients H v).axial n p = 0 := by
  let s := EntranceAlignedBase.modulatedScheme H v
  have hX : 0 < p.1 :=
    (ReservedPatches.right_pos F W.controls.radius W.controls.radius_pos .positive).trans_le hp
  have hR : s.b ≤ Real.sqrt (2 * p.1) := by
    change Real.sqrt (2 * ReservedPatches.right F W.controls.radius .positive) ≤ _
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hstop : EntranceAlignedBase.cutoffStop W H ld.modulation.left ≤
      (Real.sqrt (2 * p.1)) ^ 2 / 2 := by
    have hc := EntranceAlignedBase.cutoffStop_lt_patch W H ld.after_initial
    rw [ReservedPatches.radialLeft, Real.sq_sqrt (mul_nonneg (by norm_num)
      (ReservedPatches.left_pos F W.controls.radius W.controls.radius_pos .positive).le)] at hc
    rw [Real.sq_sqrt (by positivity)]
    have hl := ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos .positive
    linarith
  have hzphi : s.seedPhi n (Real.sqrt (2 * p.1), p.2) = 0 := by
    dsimp only [s, EntranceAlignedBase.modulatedScheme, EntranceAlignedBase.scheme,
      GlobalSlowProfiles.schemeFromHierarchy]
    exact GlobalSlowProfiles.cutoffLift_zero _ _ _ _ _ _ _ hstop
  have hzaxial : s.seedAxial n (Real.sqrt (2 * p.1), p.2) = 0 := by
    dsimp only [s, EntranceAlignedBase.modulatedScheme, EntranceAlignedBase.scheme,
      GlobalSlowProfiles.schemeFromHierarchy]
    exact GlobalSlowProfiles.cutoffLift_zero _ _ _ _ _ _ _ hstop
  constructor
  · change (EntranceAlignedBase.modulatedCoefficients H v).phi n p = 0
    rw [EntranceAlignedBase.modulated_phi_eq_extended H v n,
      AssembledSlowBase.extendedCoefficient_eq _ _ n 0 hX.le heta]
    change (GlobalSlowProfiles.profiles s n).phi (Real.sqrt (2 * p.1), p.2) = 0
    rw [GlobalSlowProfiles.profiles_outer_phi s hn hR, hzphi]
  · change (EntranceAlignedBase.modulatedCoefficients H v).axial n p = 0
    rw [EntranceAlignedBase.modulated_axial_eq_extended H v n,
      AssembledSlowBase.extendedCoefficient_eq _ _ n 1 hX.le heta]
    change (GlobalSlowProfiles.profiles s n).axial (Real.sqrt (2 * p.1), p.2) = 0
    rw [GlobalSlowProfiles.profiles_outer_axial s hn hR, hzaxial]

/-- The complete summed tangential fields on the mean patch, for every
cutoff schedule and expansion scale. -/
theorem normalized_mean_fields (a : ℕ → ℕ) (q : ℝ) {p : Inner}
    (hp : p.1 ∈ ReservedPatches.window F W.controls.radius .mean) (heta : |p.2| ≤ 1) :
    SlowBorelBase.normalizedSwirl a F.data.h W.axis.normalization
        (FinalSlowBase.coefficients H v) (q, p) =
      ReservedPatches.xAmplitude F W.controls.radius p.2 * p.1 ^ (-(1 / 2 + F.data.core.lam)) ∧
      SlowBorelBase.slowSum a F.data.h (FinalSlowBase.coefficients H v).axial (q, p) = 0 := by
  have hX := ReservedPatches.mem_window_pos F W.controls.radius W.controls.radius_pos .mean hp
  have hpos : ReservedPatches.right F W.controls.radius .positive ≤ p.1 :=
    ((positive_before_mean F W.controls.radius_pos).trans hp.1).le
  have hphi := slowSum_eq_leading a F.data.h (FinalSlowBase.coefficients H v).phi (q, p)
    (fun n hn => (positive_fields_zero H v (p := p) hn hpos heta).1)
  have haxial := slowSum_eq_leading a F.data.h (FinalSlowBase.coefficients H v).axial (q, p)
    (fun n hn => (positive_fields_zero H v (p := p) hn hpos heta).2)
  have hzero := EntranceAlignedBase.modulated_zero_fields H v (p := p) hX.le heta
  have hfields := modulated_mean_fields v (p := p) hp heta
  constructor
  · change Real.sqrt (2 * p.1) / W.axis.normalization *
      SlowBorelBase.slowSum a F.data.h (FinalSlowBase.coefficients H v).phi (q, p) = _
    rw [hphi]
    change Real.sqrt (2 * p.1) / W.axis.normalization *
      (EntranceAlignedBase.modulatedCoefficients H v).phi 0 p = _
    rw [hzero.1, ← hfields.2]
    change Real.sqrt (2 * p.1) / W.axis.normalization *
      (W.axis.normalization * v.profiles.f p) = Real.sqrt (2 * p.1) * v.profiles.f p
    field_simp [W.axis.normalization_pos.ne']
  · rw [haxial]
    exact hzero.2.1.trans hfields.1

/-- The literal normalized angular and axial slices of the final base. -/
noncomputable def angularSlice (upper : ℝ) (B : ℕ) (Q : ℝ) (s : ℝ × ℝ) (R : ℝ) : ℝ :=
  R * frequency (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
    (FinalSlowBase.coefficients H v) Q (R, (s.2, s.1))

noncomputable def axialSlice (upper : ℝ) (B : ℕ) (Q : ℝ) (s : ℝ × ℝ) (R : ℝ) : ℝ :=
  axial (FinalSlowBase.scales H v upper B) F.data.h
    (FinalSlowBase.coefficients H v) Q (R, (s.2, s.1))

theorem angularSlice_physical (upper : ℝ) (B : ℕ) {Q : ℝ} (hQ : 0 < Q)
    {s : ℝ × ℝ} (hs : 0 < s.1) {R : ℝ} (hR : 0 < R) :
    angularSlice H v upper B Q s R = Q ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (bandPoint F.data.h Q (R, (s.2, s.1))) 1 := by
  unfold angularSlice
  rw [frequency_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half hQ (FinalSlowBase.coefficients_smooth H v) hs hR]
  unfold FinalSlowBase.velocity
  change R * (_ / R) = _
  field_simp [hR.ne']

theorem axialSlice_physical (upper : ℝ) (B : ℕ) {Q : ℝ} (hQ : 0 < Q)
    {s : ℝ × ℝ} (hs : 0 < s.1) (R : ℝ) :
    axialSlice H v upper B Q s R = Q ^ CoordinateAlgebra.A F.data.h *
      FinalSlowBase.velocity H v upper B (bandPoint F.data.h Q (R, (s.2, s.1))) 2 :=
  axial_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half hQ (FinalSlowBase.coefficients_smooth H v) hs

/-- The actual background identities required by the local rank inverse.
All scales and amplitudes are fixed by the original profile. -/
theorem rank_fields (upper : ℝ) (B : ℕ) (Q : ℝ)
    {s : ℝ × ℝ} (hs : 0 < s.1) {R : ℝ}
    (hR : R ∈ Ioo
      (rankLength F.data.h s * ReservedPatches.radialSupportLeft F W.controls.radius .mean)
      (rankLength F.data.h s * ReservedPatches.radialSupportRight F W.controls.radius .mean)) :
    angularSlice H v upper B Q s R =
      MeanRankUpdate.background F.data.core.lam (rankCoefficient F W.controls.radius s)
        (rankLength F.data.h s) (rankVelocity F.data.h s) R ∧
      axialSlice H v upper B Q s R = 0 := by
  have hell := rankLength_pos F.data.h_pos F.data.h_lt_half hs
  have hRp : 0 < R :=
    (mul_pos hell (ReservedPatches.radialSupportLeft_pos F W.controls.radius
      W.controls.radius_pos .mean)).trans hR.1
  have hr : R / rankLength F.data.h s ∈ ReservedPatches.radialWindow F W.controls.radius .mean := by
    apply ReservedPatches.radial_closedPatch_subset F W.controls.radius W.controls.radius_pos .mean
    exact ⟨(le_div_iff₀ hell).mpr (by nlinarith [hR.1]),
      (div_le_iff₀ hell).mpr (by nlinarith [hR.2])⟩
  have hx := ReservedPatches.radial_mem_window F W.controls.radius W.controls.radius_pos .mean hr
  rw [coordinates_radius_sq F.data.h_pos F.data.h_lt_half hs R] at hx
  have heta := (normalizedCoordinates_eta F.data.h_pos F.data.h_lt_half
    (p := (R, (s.2, s.1))) hs).le
  have hv := normalized_mean_fields H v (FinalSlowBase.scales H v upper B)
    (Q * rankScale F.data.h s) (p := (normalizedCoordinates F.data.h (R, (s.2, s.1))).2) hx heta
  have he : SlowBorelBase.normalizedSwirl (FinalSlowBase.scales H v upper B) F.data.h
      W.axis.normalization (FinalSlowBase.coefficients H v)
      (SlowBorelBase.scaleMap Q (normalizedCoordinates F.data.h (R, (s.2, s.1)))) =
      FiveRowRank.background F.data.core.lam (rankCoefficient F W.controls.radius s)
        (R / rankLength F.data.h s) := by
    simp only [SlowBorelBase.scaleMap_apply, coordinates_rankScale]
    rw [hv.1, coordinates_rankEta, ← coordinates_radius_sq F.data.h_pos F.data.h_lt_half hs R,
      ReservedPatches.square_half_power _ _ (div_pos hRp hell)]
    rw [← mul_assoc]
    change ReservedPatches.radialAmplitude F W.controls.radius (rankEta F.data.h s) * _ = _
    rw [ReservedPatches.radialAmplitude_shape]
    rfl
  constructor
  · unfold angularSlice frequency frequencyFactor axialFactor
    rw [coordinates_rankScale, he]
    change R * (rankVelocity F.data.h s / R * _) = rankVelocity F.data.h s * _
    field_simp [hRp.ne']
  · unfold axialSlice axial axialFactor
    simp only [SlowBorelBase.scaleMap_apply, coordinates_rankScale]
    rw [hv.2, mul_zero]

/-- Five exact physical rows for the full final base, with the original
mean-patch radii and the actual similarity length and velocity scales. -/
theorem five_rows (upper : ℝ) (B : ℕ) (Q : ℝ)
    {s : ℝ × ℝ} (hs : 0 < s.1) (debt : MeanRankUpdate.Debt) :
    FiveRowRank.FiveRows (angularSlice H v upper B Q s) (axialSlice H v upper B Q s) debt
      (MeanRankUpdate.angularIncrement F.data.core.lam (rankCoefficient F W.controls.radius s)
        (ReservedPatches.radialSupportLeft F W.controls.radius .mean)
        (ReservedPatches.radialSupportRight F W.controls.radius .mean)
        (rankLength F.data.h s) (rankVelocity F.data.h s) debt)
      (MeanRankUpdate.desiredAxialIncrement F.data.core.lam (rankCoefficient F W.controls.radius s)
        (ReservedPatches.radialSupportLeft F W.controls.radius .mean)
        (ReservedPatches.radialSupportRight F W.controls.radius .mean)
        (rankLength F.data.h s) (rankVelocity F.data.h s) debt) :=
  MeanRankUpdate.physical_rows_on_patch F.data.core.lam_pos
    (rankCoefficient_pos F W.controls.radius s).ne'
    (ReservedPatches.radialSupportLeft_pos F W.controls.radius W.controls.radius_pos .mean)
    (ReservedPatches.radial_support_margins F W.controls.radius W.controls.radius_pos .mean).2.1
    (rankLength_pos F.data.h_pos F.data.h_lt_half hs)
    (rankVelocity_pos F.data.h_pos F.data.h_lt_half hs).ne' debt _ _
    (fun _ hR => (rank_fields H v upper B Q hs hR).1)
    (fun _ hR => (rank_fields H v upper B Q hs hR).2)

end SummedBase

end NavierStokes.BaseRankPatch
