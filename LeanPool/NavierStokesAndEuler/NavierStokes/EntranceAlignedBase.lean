/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ConstructedSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedProfileAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.FirstOrderBaseEdge
public import LeanPool.NavierStokesAndEuler.NavierStokes.ZerothStressIdentity
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStressWeights

@[expose] public section

/-!
# A slow base whose cutoffs are aligned with the natural entrance

The retained local hierarchy extends strictly beyond the natural entrance.
Its cutoff transition lies inside the proved initial true-cone collar and
before the finite modulation begins.  The same finite base, local hierarchy,
and five-row exterior repair are used throughout.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.EntranceAlignedBase

open GlobalSlowProfiles AssembledSlowBase

section Geometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (H : NominalConeAssembly.Certificate W)

noncomputable def trueWidth : ℝ := H.initial.choose

theorem trueWidth_pos : 0 < trueWidth W H := H.initial.choose_spec.1

theorem trueWidth_spec {y eta : ℝ} (hy : 0 < y) (ht : y ≤ trueWidth W H)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    NominalConeAssembly.IsTrue W.profiles F.data.h
      (NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)) :=
  H.initial.choose_spec.2.2 y eta hy ht heta

noncomputable def analyticEnd : ℝ :=
  NominalConeAssembly.activeLeft W * Real.exp W.controls.referenceWidth

noncomputable def windowCap (lo : ℝ) : ℝ :=
  min lo (min (NominalConeAssembly.activeLeft W * Real.exp (trueWidth W H)) (analyticEnd W))

noncomputable def zeroEnd (lo : ℝ) : ℝ :=
  NominalConeAssembly.activeLeft W + (windowCap W H lo - NominalConeAssembly.activeLeft W) / 4

noncomputable def cutoffInner (lo : ℝ) : ℝ :=
  NominalConeAssembly.activeLeft W + (windowCap W H lo - NominalConeAssembly.activeLeft W) / 2

noncomputable def cutoffStop (lo : ℝ) : ℝ :=
  NominalConeAssembly.activeLeft W + 3 * (windowCap W H lo - NominalConeAssembly.activeLeft W) / 4

theorem entrance_lt_cap {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    NominalConeAssembly.activeLeft W < windowCap W H lo := by
  have ha := NominalConeAssembly.activeLeft_pos W
  have ht := Real.one_lt_exp_iff.mpr (trueWidth_pos W H)
  have hr := Real.one_lt_exp_iff.mpr W.controls.referenceWidth_pos
  apply lt_min hlo
  apply lt_min
  · nlinarith
  · dsimp [analyticEnd]
    nlinarith

theorem window_order {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    NominalConeAssembly.activeLeft W < zeroEnd W H lo ∧
    zeroEnd W H lo < cutoffInner W H lo ∧
    cutoffInner W H lo < cutoffStop W H lo ∧ cutoffStop W H lo < windowCap W H lo := by
  have hm := entrance_lt_cap W H hlo
  dsimp [zeroEnd, cutoffInner, cutoffStop]
  constructor <;> [skip; constructor] <;> [skip; skip; constructor] <;> linarith

theorem cutoffStop_lt_lo {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    cutoffStop W H lo < lo :=
  (window_order W H hlo).2.2.2.trans_le (min_le_left _ _)

theorem cutoffStop_lt_trueEnd {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    cutoffStop W H lo < NominalConeAssembly.activeLeft W * Real.exp (trueWidth W H) :=
  (window_order W H hlo).2.2.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))

theorem cutoffStop_lt_analyticEnd {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    cutoffStop W H lo < analyticEnd W :=
  (window_order W H hlo).2.2.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))

theorem cutoffInner_pos {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    0 < cutoffInner W H lo :=
  (NominalConeAssembly.activeLeft_pos W).trans ((window_order W H hlo).1.trans (window_order W H
    hlo).2.1)

theorem zeroEnd_pos {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    0 < zeroEnd W H lo := (NominalConeAssembly.activeLeft_pos W).trans (window_order W H hlo).1

theorem analyticEnd_lt_radius : analyticEnd W < nominalRadius W ^ 2 :=
  ActualSlowAxis.collar_lt_square W.axis.referenceInput W.controls.referenceWidth

theorem analyticEnd_lt_patch :
    analyticEnd W < (ReservedPatches.radialLeft F W.controls.radius .positive) ^ 2 / 2 := by
  have hleft : W.controls.radius < ReservedPatches.left F W.controls.radius .positive := by
    have hc := F.data.core.holdStart_pos.trans (ReservedPatches.clock_inside_wait F .positive).1
    have hs := ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hc
    simpa only [OutgoingDilation.radius, Real.exp_zero, mul_one, ReservedPatches.left] using hs
  have hb := W.controls.activation_collar_le_Xi.trans_lt
    (((W.controls.Xi_lt_heatJoin W.separated).trans W.controls.heatJoin_lt_radius).trans hleft)
  rw [ReservedPatches.radialLeft, Real.sq_sqrt
    (mul_nonneg (by norm_num) (ReservedPatches.left_pos F W.controls.radius W.controls.radius_pos
      .positive).le)]
  dsimp [analyticEnd, NominalConeAssembly.activeLeft]
  linarith

theorem cutoffStop_lt_radius {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    cutoffStop W H lo < nominalRadius W ^ 2 :=
  (cutoffStop_lt_analyticEnd W H hlo).trans (analyticEnd_lt_radius W)

theorem cutoffStop_lt_patch {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo) :
    cutoffStop W H lo < (ReservedPatches.radialLeft F W.controls.radius .positive) ^ 2 / 2 :=
  (cutoffStop_lt_analyticEnd W H hlo).trans (analyticEnd_lt_patch W)

/-- The whole cutoff transition is inside the actual initial true collar. -/
theorem cutoff_transition_true {lo : ℝ} (hlo : NominalConeAssembly.activeLeft W < lo)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc (cutoffInner W H lo) (cutoffStop W H lo))
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    NominalConeAssembly.IsTrue W.profiles F.data.h p := by
  have ha := NominalConeAssembly.activeLeft_pos W
  have hleft := ((window_order W H hlo).1.trans (window_order W H hlo).2.1).trans_le hp.1
  have hy : 0 < Real.log (p.1 / NominalConeAssembly.activeLeft W) := by
    apply Real.log_pos
    exact (one_lt_div ha).mpr hleft
  have ht := NominalConeAssembly.log_chart_lt ha (ha.trans hleft)
    (hp.2.trans_lt (cutoffStop_lt_trueEnd W H hlo))
  have hc := trueWidth_spec W H hy ht.le heta
  rwa [NominalConeAssembly.chart_log ha (ha.trans hleft)] at hc

end Geometry

section Scheme

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (H : NominalConeAssembly.Certificate W)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
    (hlo : NominalConeAssembly.activeLeft W < lo)

/-- A new actual global recursion, retaining the same local hierarchy
through the entrance and changing only its common seed cutoff. -/
noncomputable def scheme : Scheme S F.data.h W.axis.normalization :=
  schemeFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (modifiedDomain W Q M) (fun _ he => (M.subset he).2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (window_order W H hlo).2.2.1
    (cutoffStop_lt_radius W H hlo) (cutoffStop_lt_patch W H hlo)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (modifiedBaseData W Q M)

theorem localization : Localization (scheme W H Q M hlo) (nominalHierarchy W) (cutoffInner W H lo)
  :=
  localizationFromHierarchy (nominalHierarchy W) (ActualSlowAxis.axisRadius_pos _ _)
    (nominalComplexDomain_open W) (modifiedDomain W Q M) (fun _ he => (M.subset he).2)
    W.axis.normalization_pos.ne' F.data.core.lam_pos (cutoffInner_pos W H hlo)
    (window_order W H hlo).2.2.1 (cutoffStop_lt_radius W H hlo) (cutoffStop_lt_patch W H hlo)
    (ReservedPatches.radialLeft_pos F W.controls.radius W.controls.radius_pos .positive)
    (ReservedPatches.radial_left_lt_right F W.controls.radius W.controls.radius_pos .positive)
    (nominal_patch_before_outer W).le (modifiedBaseData W Q M)

theorem scheme_base : (scheme W H Q M hlo).base = (modifiedScheme W Q M).base := rfl

theorem scheme_outer : (scheme W H Q M hlo).B = nominalOuterRadius W := rfl

theorem scheme_base_beta : (scheme W H Q M hlo).base.beta =
    betaFromU (scheme W H Q M hlo).domain 0 (scheme W H Q M hlo).base.axial := rfl

/-- The actual nominal fields agree with the ACT fields throughout the
analytic collar, rather than only on the smaller natural core. -/
theorem nominal_ACT_fields {X eta : ℝ} (hX : 0 ≤ X) (hc : X ≤ analyticEnd W)
    (heta : eta ∈ ReferencePath.parameterInterval) :
    W.profiles.f (X, eta) = (nominalACT W).f (X, eta) ∧
    W.profiles.U (X, eta) = (nominalACT W).U (X, eta) := by
  have hn := W.seed_agreement (p := (X, eta)) hX (hc.trans W.controls.activation_collar_le_Xi)
  have ha := W.controls.seed_activation (p := (X, eta)) heta hc
  exact ⟨hn.1.trans ha.1, hn.2.1.trans ha.2⟩

include M hlo in
theorem modified_ACT_fields {p : ℝ × ℝ} (hX : 0 ≤ p.1) (hc : p.1 < cutoffInner W H lo)
    (heta : p.2 ∈ S) :
    Q.f p = (nominalACT W).f p ∧ Q.U p = (nominalACT W).U p := by
  have hl : p.1 ≤ lo := (hc.trans ((window_order W H hlo).2.2.1.trans (cutoffStop_lt_lo W H
    hlo))).le
  have he := M.fields p hX heta (Or.inl hl)
  have ha := nominal_ACT_fields W hX
    (hc.trans ((window_order W H hlo).2.2.1.trans (cutoffStop_lt_analyticEnd W H hlo))).le
    (nominalParameters_reference W (M.subset heta))
  exact ⟨he.1.trans ha.1, he.2.trans ha.2⟩

include M hlo in
theorem modified_ACT_pressure {p : ℝ × ℝ} (hX : 0 ≤ p.1) (hc : p.1 < cutoffInner W H lo)
    (heta : p.2 ∈ S) : Q.pressure p = (nominalACT W).pressure p := by
  apply (ActualSlowAxis.histories_congr_below Q (nominalACT W) hX
    (congrFun M.pressure0 p.2) _ _).2
  · intro X hXX
    exact (modified_ACT_fields W H Q M hlo (p := (X, p.2)) hXX.1 (hXX.2.trans_lt hc) heta).1
  · intro X hXX
    exact (modified_ACT_fields W H Q M hlo (p := (X, p.2)) hXX.1 (hXX.2.trans_lt hc) heta).2

theorem base_phi_axial_pressure {p : ℝ × ℝ} (hX : 0 ≤ p.1) (hc : p.1 < cutoffInner W H lo)
    (heta : p.2 ∈ S) :
    xProfile (scheme W H Q M hlo).base.phi p =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 0) p ∧
    xProfile (scheme W H Q M hlo).base.axial p =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 1) p ∧
    xProfile (scheme W H Q M hlo).base.pressure p =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 3) p := by
  have hv := ActualSlowAxis.hierarchy_base_values (nominalTube W) W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum_contDiff W.axis.normalization hX (nominalParameters_reference W (M.subset heta))
  have hf := modified_ACT_fields W H Q M hlo hX hc heta
  have hp := modified_ACT_pressure W H Q M hlo hX hc heta
  refine ⟨?_, ?_, ?_⟩
  · change xProfile (baseFields (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane).phi p = _
    rw [baseFields_phi _ _ _ _ hX, hf.1]
    exact hv.1.symm
  · change xProfile (baseFields (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane).axial p
    = _
    rw [baseFields_axial _ _ _ _ hX, hf.2]
    exact hv.2.1.symm
  · change xProfile (baseFields (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane).pressure
    p = _
    rw [baseFields_pressure _ _ _ _ hX, hp]
    exact hv.2.2.2.symm

theorem base_beta_pos {p : ℝ × ℝ} (hX : 0 < p.1) (hc : p.1 < cutoffInner W H lo)
    (heta : p.2 ∈ S) :
    xProfile (scheme W H Q M hlo).base.beta p =
      SlowRecursion.profile ((nominalHierarchy W).coefficients 0 4) p := by
  have hr : p.1 < nominalRadius W ^ 2 :=
    hc.trans ((window_order W H hlo).2.2.1.trans (cutoffStop_lt_radius W H hlo))
  have hf := NaturalCoefficientBridge.hierarchy_flux_zero (nominalTube W)
    W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum_contDiff W.axis.normalization ⟨hX, hr⟩ (M.subset heta).2
  change p.1 * SlowRecursion.profile ((nominalHierarchy W).coefficients 0 4) p =
    SlowDivergence.radialFlux F.data.h 0 (nominalACT W).U p at hf
  have hu : EqOn Q.U (nominalACT W).U (Ico 0 (cutoffInner W H lo) ×ˢ S) := by
    intro y hy
    exact (modified_ACT_fields W H Q M hlo hy.1.1 hy.1.2 hy.2).2
  have he := local_flux_eq (modifiedDomain W Q M) Q (nominalACT W) hu hX hc heta
  change xProfile (baseFields (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane).beta p = _
  rw [baseFields_beta_value _ _ _ _ hX heta, he]
  exact ((eq_div_iff hX.ne').mpr (by simpa only [mul_comm] using hf)).symm

theorem base_beta_axis {eta : ℝ} (heta : eta ∈ S) :
    (scheme W H Q M hlo).base.beta (0, eta) =
      localExtension (localization W H Q M hlo) 0 4 (0, eta) := by
  have hs : 0 < Real.sqrt (cutoffInner W H lo) := Real.sqrt_pos.mpr (cutoffInner_pos W H hlo)
  have he : EqOn (fun R => (scheme W H Q M hlo).base.beta (R, eta))
      (fun R => localExtension (localization W H Q M hlo) 0 4 (R, eta))
      (Ioo 0 (Real.sqrt (cutoffInner W H lo))) := by
    intro R hR
    have hc : R ^ 2 / 2 < cutoffInner W H lo := by
      have hh := (sq_lt_sq₀ hR.1.le hs.le).2 hR.2
      rw [Real.sq_sqrt (cutoffInner_pos W H hlo).le] at hh
      linarith [sq_nonneg R]
    dsimp only
    rw [← xProfile_radius (scheme W H Q M hlo).base.beta hR.1.le eta,
      base_beta_pos W H Q M hlo (div_pos (sq_pos_of_pos hR.1) (by norm_num)) hc heta,
      localExtension_radial (localization W H Q M hlo) 0 4 hR.1.le hc.le]
  have hc := he.closure (slice_smooth (scheme W H Q M hlo).base.beta.smooth heta).continuous
    (slice_smooth (localExtension (localization W H Q M hlo) 0 4).smooth heta).continuous
  apply hc
  rw [closure_Ioo hs.ne]
  exact ⟨le_rfl, hs.le⟩

theorem baseAgreement : BaseAgreement (scheme W H Q M hlo) (nominalHierarchy W) (cutoffInner W H
  lo) := by
  constructor
  · intro p hx hc he
    exact (base_phi_axial_pressure W H Q M hlo hx hc he).1
  · intro p hx hc he
    exact (base_phi_axial_pressure W H Q M hlo hx hc he).2.1
  · intro p hx hc he
    by_cases h0 : p.1 = 0
    · have hp : p = (0, p.2) := Prod.ext h0 rfl
      rw [hp]
      simpa only [xProfile, mul_zero, Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0), zero_div] using
        (base_beta_axis W H Q M hlo he).trans
          (localExtension_radial (localization W H Q M hlo) 0 4 le_rfl
            (by simpa using (cutoffInner_pos W H hlo).le))
    · exact base_beta_pos W H Q M hlo (lt_of_le_of_ne hx (Ne.symm h0)) hc he

theorem small_lt_entrance : nominalInner W < NominalConeAssembly.activeLeft W := by
  have hp := NominalConeAssembly.activeLeft_pos W
  change NominalConeAssembly.activeLeft W / 4 < NominalConeAssembly.activeLeft W
  linarith

include hlo in
theorem small_lt_cutoffInner : nominalInner W < cutoffInner W H lo :=
  (small_lt_entrance W).trans ((window_order W H hlo).1.trans (window_order W H hlo).2.1)

/-- The extension constructor may use a small natural core independently
of the larger radius retained by the actual seed cutoff. -/
theorem smallLocalization : Localization (scheme W H Q M hlo) (nominalHierarchy W) (nominalInner W)
  := by
  let L := localization W H Q M hlo
  refine ⟨L.radius_pos, L.parameter_open, L.parameter_embedding, nominalInner_pos W,
    (small_lt_cutoffInner W H hlo).trans L.inner_radius,
    (small_lt_cutoffInner W H hlo).trans L.inner_patch, ?_, ?_⟩
  · intro n p hp hi
    exact L.axial_seed n p hp (hi.trans (small_lt_cutoffInner W H hlo).le)
  · intro n p hp hi
    exact L.phi_seed n p hp (hi.trans (small_lt_cutoffInner W H hlo).le)

theorem smallBaseAgreement : BaseAgreement (scheme W H Q M hlo) (nominalHierarchy W) (nominalInner
  W) := by
  let B := baseAgreement W H Q M hlo
  exact ⟨fun p hp hi he => B.phi p hp (hi.trans (small_lt_cutoffInner W H hlo)) he,
    fun p hp hi he => B.axial p hp (hi.trans (small_lt_cutoffInner W H hlo)) he,
    fun p hp hi he => B.beta p hp (hi.trans (small_lt_cutoffInner W H hlo)) he⟩

/-- The order-zero equations hold on the full natural core, up to the
entrance from below.  They are obtained from the actual natural solution. -/
theorem zero_coefficients {p : ℝ × ℝ} (hX : 0 < p.1)
    (he : p.1 < NominalConeAssembly.activeLeft W) (heta : p.2 ∈ S) :
    SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) 0 p = 0
      ∧
    SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) 0 p = 0
      := by
  let s := scheme W H Q M hlo
  let f := asSlowProfiles s
  let g := SlowResidualMatching.hierarchyProfiles (nominalHierarchy W)
  have hc : p.1 < cutoffInner W H lo :=
    he.trans ((window_order W H hlo).1.trans (window_order W H hlo).2.1)
  have hz := NaturalCoefficientBridge.fromNatural_coefficients_zero
    (SchedulePressure.admissible F.data) (nominalPressure_eq (F := F)) W.axis.natural.profile
    W.axis.scale_pos W.axis.small W.axis.preparation.sigma_pos W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    (p := p) ⟨⟨hX, he⟩, nominalParameters_reference W (M.subset heta)⟩ (M.subset heta).2
  change SlowExpansionResidual.angularCoefficient F.data.h g 0 p = 0 ∧
    SlowExpansionResidual.axialCoefficient F.data.h g 0 p = 0 at hz
  have hphi : ∀ j ≤ 0, f.phi j =ᶠ[𝓝 p] g.phi j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact profiles_x_phi_germ (localization W H Q M hlo) (baseAgreement W H Q M hlo) 0 hX hc heta
  have hu : ∀ j ≤ 0, f.axial j =ᶠ[𝓝 p] g.axial j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact profiles_x_axial_germ (localization W H Q M hlo) (baseAgreement W H Q M hlo) 0 hX hc heta
  have hv : ∀ j ≤ 0, f.flux j =ᶠ[𝓝 p] g.flux j := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    filter_upwards [profiles_x_beta_germ (localization W H Q M hlo) (baseAgreement W H Q M hlo) 0
      hX hc heta]
      with q hq
    exact congrArg (q.1 * ·) hq
  have hp : f.pressure 0 =ᶠ[𝓝 p] g.pressure 0 := by
    filter_upwards [(isOpen_Ioo.prod M.isOpen).mem_nhds ⟨⟨hX, hc⟩, heta⟩] with q hq
    change xProfile (profiles s 0).pressure q = _
    rw [profiles_zero]
    exact (base_phi_axial_pressure W H Q M hlo hq.1.1.le hq.1.2 hq.2).2.2
  exact ⟨(SlowResidualMatching.angularCoefficient_congr_germ F.data.h 0 hv hu hphi).trans hz.1,
    (SlowResidualMatching.axialCoefficient_congr_germ F.data.h 0 hv hu hp).trans hz.2⟩

theorem smallZeroOrder : ZeroOrderSolved (scheme W H Q M hlo) (nominalInner W) :=
  ⟨fun _ hx hi he => (zero_coefficients W H Q M hlo hx (hi.trans (small_lt_entrance W)) he).1,
   fun _ hx hi he => (zero_coefficients W H Q M hlo hx (hi.trans (small_lt_entrance W)) he).2⟩

noncomputable def alignedCoefficients : SlowBorelBase.Coefficients :=
  coefficients (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
    (smallZeroOrder W H Q M hlo) M.contains

theorem aligned_smooth : SlowBorelBase.SmoothCoefficients (alignedCoefficients W H Q M hlo) :=
  coefficients_smooth (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
    (smallZeroOrder W H Q M hlo) M.contains

theorem aligned_coefficientMatches :
    BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization
      (alignedCoefficients W H Q M hlo) (asSlowProfiles (scheme W H Q M hlo)) :=
  ConstructedSlowBase.repaired_coefficientMatches (smallLocalization W H Q M hlo)
    (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo) M.contains rfl

theorem positive_coefficients_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hX : 0 < p.1) (hc : p.1 < cutoffInner W H lo) (heta : p.2 ∈ S) :
    SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) n p = 0
      ∧
    SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) n p = 0 :=
  profiles_inner_tangential (localization W H Q M hlo) (baseAgreement W H Q M hlo) hn hX hc heta

theorem positive_densities_zero {n : ℕ} (hn : 0 < n) {R eta : ℝ}
    (hR : R ∈ Icc 0 (Real.sqrt (2 * zeroEnd W H lo))) (heta : eta ∈ S) :
    SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) n (R, eta) = 0 ∧
    SlowResidualMatching.zDensity F.data.h (asSlowProfiles (scheme W H Q M hlo)) n (R, eta) = 0 :=
      by
  by_cases hR0 : R = 0
  · simp [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity, hR0]
  · have hs : R ^ 2 ≤ 2 * zeroEnd W H lo := by
      calc
        R ^ 2 ≤ (Real.sqrt (2 * zeroEnd W H lo)) ^ 2 := (sq_le_sq₀ hR.1 (Real.sqrt_nonneg _)).2 hR.2
        _ = 2 * zeroEnd W H lo := Real.sq_sqrt (mul_nonneg (by norm_num) (zeroEnd_pos W H hlo).le)
    have hc : R ^ 2 / 2 < cutoffInner W H lo := by linarith [(window_order W H hlo).2.1]
    have hz := positive_coefficients_zero W H Q M hlo hn (p := (R ^ 2 / 2, eta))
      (div_pos (sq_pos_of_ne_zero hR0) (by norm_num)) hc heta
    simp only [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity,
      SlowResidualMatching.radiusPoint, hz.1, hz.2, mul_zero, and_self]

theorem positive_raw_stresses_zero {n : ℕ} (hn : 0 < n) {R eta : ℝ}
    (hR : R ≤ Real.sqrt (2 * zeroEnd W H lo)) (heta : eta ∈ S) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) n) (R, eta) = 0 ∧
    SlowStressSupport.stress 1 (SlowResidualMatching.zDensity F.data.h
      (asSlowProfiles (scheme W H Q M hlo)) n) (R, eta) = 0 :=
  ⟨SlowStressSupport.stress_inner 2
      (fun _ he _ hr => (positive_densities_zero W H Q M hlo hn hr he).1) hR heta,
   SlowStressSupport.stress_inner 1
      (fun _ he _ hr => (positive_densities_zero W H Q M hlo hn hr he).2) hR heta⟩

/-- Continuity supplies the natural entrance endpoint itself. -/
theorem natural_densities_zero {R eta : ℝ}
    (hR : R ∈ Icc 0 (Real.sqrt (2 * NominalConeAssembly.activeLeft W))) (heta : eta ∈ S) :
    SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) 0 (R, eta) = 0 ∧
    SlowResidualMatching.zDensity F.data.h (asSlowProfiles (scheme W H Q M hlo)) 0 (R, eta) = 0 :=
      by
  let f := asSlowProfiles (scheme W H Q M hlo)
  let b := Real.sqrt (2 * NominalConeAssembly.activeLeft W)
  have hb : 0 < b := Real.sqrt_pos.mpr (mul_pos (by norm_num) (NominalConeAssembly.activeLeft_pos
    W))
  have hzero : ∀ r ∈ Ioo (0 : ℝ) b,
      SlowResidualMatching.thetaDensity F.data.h W.axis.normalization f 0 (r, eta) = 0 ∧
      SlowResidualMatching.zDensity F.data.h f 0 (r, eta) = 0 := by
    intro r hr
    have hs : r ^ 2 < 2 * NominalConeAssembly.activeLeft W := by
      have hsq := (sq_lt_sq₀ hr.1.le hb.le).2 hr.2
      dsimp only [b] at hsq
      rwa [Real.sq_sqrt (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)] at hsq
    have he : r ^ 2 / 2 < NominalConeAssembly.activeLeft W := by linarith
    have hz := zero_coefficients W H Q M hlo (p := (r ^ 2 / 2, eta))
      (div_pos (sq_pos_of_pos hr.1) (by norm_num)) he heta
    dsimp only [f]
    simp only [SlowResidualMatching.thetaDensity, SlowResidualMatching.zDensity,
      SlowResidualMatching.radiusPoint, hz.1, hz.2, mul_zero, and_self]
  have ht : EqOn (fun r => SlowResidualMatching.thetaDensity F.data.h W.axis.normalization f 0 (r,
    eta))
      (fun _ => (0 : ℝ)) (Ioo 0 b) := fun r hr => (hzero r hr).1
  have hz : EqOn (fun r => SlowResidualMatching.zDensity F.data.h f 0 (r, eta))
      (fun _ => (0 : ℝ)) (Ioo 0 b) := fun r hr => (hzero r hr).2
  have ht' := ht.closure (SlowStressSupport.slice_smooth
    (thetaDensity_smooth (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
      (smallZeroOrder W H Q M hlo) 0) heta).continuous continuous_const
  have hz' := hz.closure (SlowStressSupport.slice_smooth
    (zDensity_smooth (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
      (smallZeroOrder W H Q M hlo) 0) heta).continuous continuous_const
  rw [closure_Ioo hb.ne] at ht' hz'
  exact ⟨ht' hR, hz' hR⟩

theorem natural_raw_stresses_zero {R eta : ℝ}
    (hR : R ≤ Real.sqrt (2 * NominalConeAssembly.activeLeft W)) (heta : eta ∈ S) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) 0) (R, eta) = 0 ∧
    SlowStressSupport.stress 1 (SlowResidualMatching.zDensity F.data.h
      (asSlowProfiles (scheme W H Q M hlo)) 0) (R, eta) = 0 :=
  ⟨SlowStressSupport.stress_inner 2
      (fun _ he _ hr => (natural_densities_zero W H Q M hlo hr he).1) hR heta,
   SlowStressSupport.stress_inner 1
      (fun _ he _ hr => (natural_densities_zero W H Q M hlo hr he).2) hR heta⟩

/-- The positive half-plane extension preserves a zero radial prefix for
all parameters, including those handled by the fixed parameter retraction. -/
theorem extendCoreZero_zero_prefix {T : Set ℝ} (w : ParametricRadialExtension.ParameterWindow T)
    {core bound : ℝ} (hcore : 0 < core) (f : EvenProfile T)
    (hz : ∀ eta ∈ T, ∀ R ∈ Icc 0 (Real.sqrt (2 * bound)), f (R, eta) = 0)
    {p : ℝ × ℝ} (hp : p.1 ≤ bound) : extendCoreZero w core f p = 0 := by
  by_cases hx : 0 ≤ p.1
  · rw [extendCoreZero, extendEven, ParametricRadialExtension.extension,
      ParametricRadialExtension.halfPlaneExtension_eq _ hx]
    change _ * (w.bump p.2 * f (Real.sqrt (2 * p.1), w.parameterMap p.2)) = 0
    rw [hz _ (w.parameterMap_mem _) _ ⟨Real.sqrt_nonneg _,
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hp (by norm_num))⟩, mul_zero, mul_zero]
  · exact extendCoreZero_zero_left w hcore f (by linarith)

/-- Every positive stress coefficient vanishes strictly past the natural
entrance, with one order-independent endpoint. -/
theorem aligned_positive_stress_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : p.1 ≤ zeroEnd W H lo) :
    (alignedCoefficients W H Q M hlo).stressTheta n p = 0 ∧
    (alignedCoefficients W H Q M hlo).stressAxial n p = 0 := by
  constructor
  · apply extendCoreZero_zero_prefix _ (nominalInner_pos W) _ _ hp
    intro eta he R hR
    rw [thetaEven_eq _ _ _ _ hR.1]
    exact (positive_raw_stresses_zero W H Q M hlo hn hR.2 he).1
  · apply extendCoreZero_zero_prefix _ (nominalInner_pos W) _ _ hp
    intro eta he R hR
    rw [zEven_eq _ _ _ _ hR.1]
    exact (positive_raw_stresses_zero W H Q M hlo hn hR.2 he).2

theorem aligned_natural_stress_zero {p : ℝ × ℝ}
    (hp : p.1 ≤ NominalConeAssembly.activeLeft W) :
    (alignedCoefficients W H Q M hlo).stressTheta 0 p = 0 ∧
    (alignedCoefficients W H Q M hlo).stressAxial 0 p = 0 := by
  constructor
  · apply extendCoreZero_zero_prefix _ (nominalInner_pos W) _ _ hp
    intro eta he R hR
    rw [thetaEven_eq _ _ _ _ hR.1]
    exact (natural_raw_stresses_zero W H Q M hlo hR.2 he).1
  · apply extendCoreZero_zero_prefix _ (nominalInner_pos W) _ _ hp
    intro eta he R hR
    rw [zEven_eq _ _ _ _ hR.1]
    exact (natural_raw_stresses_zero W H Q M hlo hR.2 he).2

/-- The entire actual coefficient family is stress-free through the
entrance.  No support conclusion is an input to this theorem. -/
theorem aligned_stress_zero_left (n : ℕ) {p : ℝ × ℝ}
    (hp : p.1 ≤ NominalConeAssembly.activeLeft W) :
    (alignedCoefficients W H Q M hlo).stressTheta n p = 0 ∧
    (alignedCoefficients W H Q M hlo).stressAxial n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact aligned_natural_stress_zero W H Q M hlo hp
  · exact aligned_positive_stress_zero W H Q M hlo hn (hp.trans (window_order W H hlo).1.le)

theorem aligned_stressZeroCore :
    BaseResidual.StressZeroCore (alignedCoefficients W H Q M hlo) (NominalConeAssembly.activeLeft
      W) :=
  fun n _ hX _ _ => aligned_stress_zero_left W H Q M hlo n hX.2.le

theorem aligned_stress_zero_right {n : ℕ} (hn : 2 ≤ n) {p : ℝ × ℝ}
    (hp : nominalOuterX W ≤ p.1) :
    (alignedCoefficients W H Q M hlo).stressTheta n p = 0 ∧
    (alignedCoefficients W H Q M hlo).stressAxial n p = 0 := by
  have hs := GlobalStressSupport.raw_stresses_exterior (scheme W H Q M hlo) rfl hn
  apply coefficients_stress_zero_right (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M
    hlo)
    (smallZeroOrder W H Q M hlo) M.contains n (nominalOuterRadius_pos W).le hs.1 hs.2
  simpa only [nominalOuterRadius_square] using hp

theorem aligned_higher_support {n : ℕ} (hn : 2 ≤ n) :
    tsupport (fun p => ((alignedCoefficients W H Q M hlo).stressTheta n p,
      (alignedCoefficients W H Q M hlo).stressAxial n p)) ⊆
      Icc (zeroEnd W H lo) (nominalOuterX W) ×ˢ
        Icc (-(commonWindow (scheme W H Q M hlo) M.contains).outer)
          (commonWindow (scheme W H Q M hlo) M.contains).outer := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  have hne : ((alignedCoefficients W H Q M hlo).stressTheta n p,
      (alignedCoefficients W H Q M hlo).stressAxial n p) ≠ 0 := hp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra hh
    have hz := aligned_positive_stress_zero W H Q M hlo (by omega : 0 < n) (le_of_not_ge hh)
    exact hne (Prod.ext hz.1 hz.2)
  · by_contra hh
    have hz := aligned_stress_zero_right W H Q M hlo hn (le_of_not_ge hh)
    exact hne (Prod.ext hz.1 hz.2)
  · apply abs_le.mp
    by_contra hh
    have hz := coefficients_stress_zero_parameter (smallLocalization W H Q M hlo)
      (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo) M.contains n (le_of_not_ge hh)
    exact hne (Prod.ext hz.1 hz.2)

theorem aligned_higherInteriorSupport :
    BaseResidual.HigherInteriorSupport (alignedCoefficients W H Q M hlo)
      (Real.log (NominalConeAssembly.activeLeft W)) (ConstructedSlowBase.activeRight W) := by
  intro n hn
  have hs := aligned_higher_support W H Q M hlo hn
  have hz {p : ℝ × ℝ} (hp : p.1 ∉ Icc (zeroEnd W H lo) (nominalOuterX W)) :
      ((alignedCoefficients W H Q M hlo).stressTheta n p,
        (alignedCoefficients W H Q M hlo).stressAxial n p) = 0 := by
    by_contra hh
    exact hp (hs (subset_closure hh)).1
  refine ⟨zeroEnd W H lo, nominalOuterX W, ?_, ?_, ?_⟩
  · intro X hX
    rw [Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
    exact ⟨(window_order W H hlo).1.trans_le hX.1,
      hX.2.trans_lt (ConstructedSlowBase.outer_before_upper W)⟩
  · intro eta _ X hX
    exact congrArg Prod.fst (hz hX)
  · intro eta _ X hX
    exact congrArg Prod.snd (hz hX)

theorem zero_fields_eq :
    (asSlowProfiles (scheme W H Q M hlo)).phi 0 = (asSlowProfiles (modifiedScheme W Q M)).phi 0 ∧
    (asSlowProfiles (scheme W H Q M hlo)).axial 0 = (asSlowProfiles (modifiedScheme W Q M)).axial 0
      ∧
    (asSlowProfiles (scheme W H Q M hlo)).flux 0 = (asSlowProfiles (modifiedScheme W Q M)).flux 0 ∧
    (asSlowProfiles (scheme W H Q M hlo)).pressure 0 = (asSlowProfiles (modifiedScheme W Q
      M)).pressure 0 := by
  simp only [asSlowProfiles, SlowResidualMatching.ofBeta, profiles_zero, scheme_base, and_self]

theorem zero_residuals_eq (p : ℝ × ℝ) :
    SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) 0 p =
      SlowExpansionResidual.angularCoefficient F.data.h (asSlowProfiles (modifiedScheme W Q M)) 0 p
        ∧
    SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (scheme W H Q M hlo)) 0 p =
      SlowExpansionResidual.axialCoefficient F.data.h (asSlowProfiles (modifiedScheme W Q M)) 0 p
        := by
  have hf := zero_fields_eq W H Q M hlo
  have hv : ∀ j ≤ 0, (asSlowProfiles (scheme W H Q M hlo)).flux j =ᶠ[𝓝 p]
      (asSlowProfiles (modifiedScheme W Q M)).flux j := by
    intro j hj
    have h0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact Filter.Eventually.of_forall (fun y => congrFun hf.2.2.1 y)
  have hu : ∀ j ≤ 0, (asSlowProfiles (scheme W H Q M hlo)).axial j =ᶠ[𝓝 p]
      (asSlowProfiles (modifiedScheme W Q M)).axial j := by
    intro j hj
    have h0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact Filter.Eventually.of_forall (fun y => congrFun hf.2.1 y)
  have hphi : ∀ j ≤ 0, (asSlowProfiles (scheme W H Q M hlo)).phi j =ᶠ[𝓝 p]
      (asSlowProfiles (modifiedScheme W Q M)).phi j := by
    intro j hj
    have h0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact Filter.Eventually.of_forall (fun y => congrFun hf.1 y)
  exact ⟨SlowResidualMatching.angularCoefficient_congr_germ F.data.h 0 hv hu hphi,
    SlowResidualMatching.axialCoefficient_congr_germ F.data.h 0 hv hu
      (Filter.Eventually.of_forall (fun y => congrFun hf.2.2.2 y))⟩

theorem zero_raw_stresses_eq (R eta : ℝ) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) 0) (R, eta) =
      SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h W.axis.normalization
        (asSlowProfiles (modifiedScheme W Q M)) 0) (R, eta) ∧
    SlowStressSupport.stress 1 (SlowResidualMatching.zDensity F.data.h
      (asSlowProfiles (scheme W H Q M hlo)) 0) (R, eta) =
      SlowStressSupport.stress 1 (SlowResidualMatching.zDensity F.data.h
        (asSlowProfiles (modifiedScheme W Q M)) 0) (R, eta) := by
  constructor
  · apply SlowResidualMatching.primitive_stress_congr_slice
    intro r
    simp only [SlowResidualMatching.thetaDensity, (zero_residuals_eq W H Q M hlo _).1]
  · apply SlowResidualMatching.primitive_stress_congr_slice
    intro r
    simp only [SlowResidualMatching.zDensity, (zero_residuals_eq W H Q M hlo _).2]

/-- Moving the positive-order cutoff preserves the leading stress itself,
including its actual integration constant. -/
theorem aligned_zero_stresses_eq {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (alignedCoefficients W H Q M hlo).stressTheta 0 p = (modifiedCoefficients W Q M).stressTheta 0
      p ∧
    (alignedCoefficients W H Q M hlo).stressAxial 0 p = (modifiedCoefficients W Q M).stressAxial 0
      p := by
  have h1 := coefficients_stress_eq (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
    (smallZeroOrder W H Q M hlo) M.contains 0 hX heta
  have h2 := coefficients_stress_eq (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains 0 hX heta
  have he := zero_raw_stresses_eq W H Q M hlo (Real.sqrt (2 * p.1)) p.2
  exact ⟨h1.1.trans (he.1.trans h2.1.symm), h1.2.trans (he.2.trans h2.2.symm)⟩

theorem leading_histories_eq :
    EqOn (GlobalStressSupport.angularHistory (scheme W H Q M hlo) 0)
      (GlobalStressSupport.angularHistory (modifiedScheme W Q M) 0) (univ ×ˢ S) ∧
    EqOn (GlobalStressSupport.axialHistory (scheme W H Q M hlo) 0)
      (GlobalStressSupport.axialHistory (modifiedScheme W Q M) 0) (univ ×ˢ S) := by
  constructor
  · intro p hp
    rw [GlobalStressSupport.angularHistory_eq _ _ hp.2, GlobalStressSupport.angularHistory_eq _ _
      hp.2,
      profiles_zero, profiles_zero, scheme_base]
  · intro p hp
    rw [GlobalStressSupport.axialHistory_eq _ _ hp.2, GlobalStressSupport.axialHistory_eq _ _ hp.2,
      profiles_zero, profiles_zero, scheme_base]

/-- The physical leading velocity and pressure are unchanged. -/
theorem aligned_zero_fields {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (alignedCoefficients W H Q M hlo).phi 0 p = W.axis.normalization * Q.f p ∧
    (alignedCoefficients W H Q M hlo).axial 0 p = Q.U p ∧
    (alignedCoefficients W H Q M hlo).pressure 0 p = Q.pressure p := by
  have he := coefficients_fields_eq (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
    (smallZeroOrder W H Q M hlo) M.contains 0 hX heta
  have hf := zero_fields_eq W H Q M hlo
  have ho := coefficients_fields_eq (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains 0 hX heta
  have hv := modifiedCoefficients_zero_fields W Q M hX heta
  exact ⟨he.1.trans ((congrFun hf.1 p).trans (ho.1.symm.trans hv.1)),
    he.2.1.trans ((congrFun hf.2.1 p).trans (ho.2.1.symm.trans hv.2.1)),
    he.2.2.trans ((congrFun hf.2.2.2 p).trans (ho.2.2.symm.trans hv.2.2))⟩

theorem aligned_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (alignedCoefficients W H Q M hlo).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  rw [(aligned_zero_fields W H Q M hlo (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1]
  rw [← (modifiedCoefficients_zero_fields W Q M (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1]
  exact ConstructedSlowBase.modified_leading_axis W Q M heta

theorem aligned_positive_axis {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : |eta| ≤ 1) :
    (alignedCoefficients W H Q M hlo).phi n (0, eta) = 0 ∧
    (alignedCoefficients W H Q M hlo).axial n (0, eta) = 0 ∧
    (alignedCoefficients W H Q M hlo).pressure n (0, eta) = 0 :=
  ⟨extendedCoefficient_axis (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
    M.contains hn 0 heta,
   extendedCoefficient_axis (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
     M.contains hn 1 heta,
   extendedCoefficient_axis (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo)
     M.contains hn 3 heta⟩

theorem aligned_moments_zero {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : eta ∈ S) :
    PositiveOrderMoments.moments n
      (PositiveOrderMoments.slice (GlobalStressSupport.axialHistory (scheme W H Q M hlo)) eta)
      (PositiveOrderMoments.slice (GlobalStressSupport.angularHistory (scheme W H Q M hlo)) eta)
      (fun R => GlobalStressSupport.previousOmega (scheme W H Q M hlo) n (R, eta)) = 0 :=
  GlobalStressSupport.moments_zero (scheme W H Q M hlo) hn heta

theorem aligned_mass_primitive_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.primitive ((alignedCoefficients W H Q M hlo).axial n) p = 0 := by
  apply extended_axial_primitive_zero (scheme W H Q M hlo) M.contains hn _ heta
  change nominalOuterRadius W ^ 2 / 2 ≤ p.1
  rwa [nominalOuterRadius_square]

theorem pressureCoefficient_zero (n : ℕ) {p : ℝ × ℝ} (hX : 0 < p.1) (heta : p.2 ∈ S) :
    SlowExpansionResidual.pressureCoefficient F.data.h W.axis.normalization
      (asSlowProfiles (scheme W H Q M hlo)) n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hf := zero_fields_eq W H Q M hlo
    simpa only [SlowExpansionResidual.pressureCoefficient, SlowExpansionResidual.previous,
      SlowExpansionResidual.convolution, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hf.1,
        hf.2.2.2] using
      modified_pressureCoefficient W Q M 0 hX heta
  · exact profiles_pressureCoefficient (scheme W H Q M hlo) hn hX heta

theorem aligned_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization
      (alignedCoefficients W H Q M hlo) (asSlowProfiles (scheme W H Q M hlo)) := by
  apply ConstructedSlowBase.repaired_finiteIdentities (smallLocalization W H Q M hlo)
    (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo) M.contains
    W.axis.small.h_pos (by linarith [W.axis.small.h_le]) rfl
  intro n p hp
  exact pressureCoefficient_zero W H Q M hlo n hp.1 (M.contains ⟨hp.2.1.le, hp.2.2.le⟩)

include hlo in
theorem zeroEnd_lt_outer : zeroEnd W H lo < nominalOuterX W := by
  have ha : analyticEnd W < nominalOuterX W :=
    W.controls.activation_collar_le_Xi.trans_lt
      (((W.controls.Xi_lt_heatJoin W.separated).trans W.controls.heatJoin_lt_radius).trans
        (nominalOuterX_gt_radius W))
  exact (window_order W H hlo).2.1.trans
    ((window_order W H hlo).2.2.1.trans ((cutoffStop_lt_analyticEnd W H hlo).trans ha))

include hlo in
theorem zeroEnd_lt_outer_collar :
    zeroEnd W H lo < Real.exp (FirstOrderBaseEdge.terminalShift W + 2) :=
  (zeroEnd_lt_outer W H hlo).trans (ConstructedSlowBase.outer_before_collar W)

theorem log_entrance_lt_outer_collar :
    Real.log (NominalConeAssembly.activeLeft W) < FirstOrderBaseEdge.terminalShift W + 2 := by
  apply Real.exp_lt_exp.mp
  rw [Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
  apply lt_trans _ (ConstructedSlowBase.outer_before_collar W)
  exact (nominalInitial_le_Xi W).trans_lt
    (((W.controls.Xi_lt_heatJoin W.separated).trans W.controls.heatJoin_lt_radius).trans
      (nominalOuterX_gt_radius W))

theorem aligned_first_pair_eq
    (hrow : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta)) :
    EqOn (BaseResidual.stressPair (alignedCoefficients W H Q M hlo) 1)
      (fun p => (SlowFirstOrderEdge.stressX (FirstOrderBaseEdge.terminalAmplitude W) F.data
        (FirstOrderBaseEdge.terminalShift W) p, 0))
      (Ioi (FirstOrderBaseEdge.terminalInner W) ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p hp
  have he := leading_histories_eq W H Q M hlo
  exact (FirstOrderBaseEdge.coefficients_first_pair_eq_modified W Q M
    (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo)
    M.contains rfl le_rfl he.1 he.2 (FirstOrderBaseEdge.terminalInner_full W hp.1).1
    (abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩)).trans
      (FirstOrderBaseEdge.modified_first_pair_eq W Q M hrow hp)

theorem aligned_first_edgeJets
    (hrow : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {c : ℝ} (hc : 0 < c) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (ConstructedSlowBase.activeRight W - 1))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.activeZeta c (Real.log (NominalConeAssembly.activeLeft W))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.activeDelta (Real.log (NominalConeAssembly.activeLeft W))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.stressPair (alignedCoefficients W H Q M hlo) 1) := by
  have he := leading_histories_eq W H Q M hlo
  exact FirstOrderBaseEdge.coefficients_first_edgeJets W Q M
    (smallLocalization W H Q M hlo) (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo)
    M.contains rfl le_rfl he.1 he.2 hrow hc (log_entrance_lt_outer_collar W)

theorem aligned_first_stress_zero_right
    (hrow : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {p : ℝ × ℝ} (hp : Real.exp (ConstructedSlowBase.activeRight W) ≤ p.1)
    (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    (alignedCoefficients W H Q M hlo).stressTheta 1 p = 0 ∧
    (alignedCoefficients W H Q M hlo).stressAxial 1 p = 0 := by
  have hs := aligned_smooth W H Q M hlo
  have hz := FirstOrderBaseEdge.first_pair_zero_right W
    ((hs.stressTheta 1).prodMk (hs.stressAxial 1)) (aligned_first_pair_eq W H Q M hlo hrow) hp heta
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩

theorem aligned_leading_stress_eq {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1)
    (hf : ∀ X, 0 < X → X ≤ p.1 → Q.f (X, p.2) ≠ 0) :
    (alignedCoefficients W H Q M hlo).stressTheta 0 p = LeadingStress.theta Q F.data.h p ∧
    (alignedCoefficients W H Q M hlo).stressAxial 0 p = LeadingStress.axial Q F.data.h p :=
  ZerothStressIdentity.coefficients_stress_zero_eq Q (smallLocalization W H Q M hlo)
    (smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo) M.contains M.halfPlane rfl hX
      heta hf

end Scheme

section Clocks

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- The unchanged terminal clock agrees exactly with the cone annulus. -/
theorem exp_right_eq_cone :
    Real.exp (ConstructedSlowBase.activeRight W) = NominalConeAssembly.activeRight W := by
  have he : ConstructedSlowBase.activeRight W =
      Real.log W.controls.radius + OutgoingTail.tailEnd F.data := by
    simp only [ConstructedSlowBase.activeRight, ConstructedSlowBase.terminalShift,
      TerminalHistoryBridge.shift, OutgoingDilation.switchRadius_eq,
      Real.log_mul W.controls.radius_pos.ne' (Real.exp_ne_zero _), Real.log_exp,
        OutgoingTail.tailEnd]
    ring
  rw [he, Real.exp_add, Real.exp_log W.controls.radius_pos]
  rfl

theorem exp_left_eq_cone :
    Real.exp (Real.log (NominalConeAssembly.activeLeft W)) = NominalConeAssembly.activeLeft W :=
  Real.exp_log (NominalConeAssembly.activeLeft_pos W)

end Clocks

section Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness d)

/-- The actual finite modulation already supplies the required positive
entrance margin; it is not an additional hypothesis on the final witness. -/
theorem modulation_after_entrance : NominalConeAssembly.activeLeft W < d.modulation.left :=
  d.after_initial

noncomputable def modulatedScheme : Scheme v.slowParameters F.data.h W.axis.normalization :=
  scheme W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

noncomputable def modulatedCoefficients : SlowBorelBase.Coefficients :=
  alignedCoefficients W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

theorem modulated_base_eq :
    (modulatedScheme H v).base = (modifiedScheme W v.profiles v.finiteModification).base := rfl

theorem modulated_baseFields_eq :
    (modulatedScheme H v).base = baseFields (modulatedScheme H v).domain
      W.axis.normalization v.profiles v.finiteModification.halfPlane := rfl

theorem modulated_outer : (modulatedScheme H v).B = nominalOuterRadius W := rfl

theorem modulated_phi_eq_extended (n : ℕ) :
    (modulatedCoefficients H v).phi n = extendedCoefficient (modulatedScheme H v)
      v.finiteModification.contains n 0 := rfl

theorem modulated_axial_eq_extended (n : ℕ) :
    (modulatedCoefficients H v).axial n = extendedCoefficient (modulatedScheme H v)
      v.finiteModification.contains n 1 := rfl

theorem modulated_pressure_eq_extended (n : ℕ) :
    (modulatedCoefficients H v).pressure n = extendedCoefficient (modulatedScheme H v)
      v.finiteModification.contains n 3 := rfl

theorem modulated_smooth : SlowBorelBase.SmoothCoefficients (modulatedCoefficients H v) :=
  aligned_smooth W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

theorem modulated_stressZeroCore :
    BaseResidual.StressZeroCore (modulatedCoefficients H v) (NominalConeAssembly.activeLeft W) :=
  aligned_stressZeroCore W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

theorem modulated_positive_stress_zero {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : p.1 ≤ zeroEnd W H d.modulation.left) :
    (modulatedCoefficients H v).stressTheta n p = 0 ∧ (modulatedCoefficients H v).stressAxial n p =
      0 :=
  aligned_positive_stress_zero W H v.profiles v.finiteModification (modulation_after_entrance (d :=
    d)) hn hp

theorem modulated_higherInteriorSupport :
    BaseResidual.HigherInteriorSupport (modulatedCoefficients H v)
      (Real.log (NominalConeAssembly.activeLeft W)) (ConstructedSlowBase.activeRight W) :=
  aligned_higherInteriorSupport W H v.profiles v.finiteModification (modulation_after_entrance (d
    := d))

theorem modulated_zero_fields {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (modulatedCoefficients H v).phi 0 p = W.axis.normalization * v.profiles.f p ∧
    (modulatedCoefficients H v).axial 0 p = v.profiles.U p ∧
    (modulatedCoefficients H v).pressure 0 p = v.profiles.pressure p :=
  aligned_zero_fields W H v.profiles v.finiteModification (modulation_after_entrance (d := d)) hX
    heta

theorem modulated_leading_stress_eq {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    (modulatedCoefficients H v).stressTheta 0 p = LeadingStress.theta v.profiles F.data.h p ∧
    (modulatedCoefficients H v).stressAxial 0 p = LeadingStress.axial v.profiles F.data.h p :=
  aligned_leading_stress_eq W H v.profiles v.finiteModification (modulation_after_entrance (d :=
    d)) hX heta
    (fun X hXp _ => (v.positive_f (p := (X, p.2)) hXp (abs_le.mp heta)).ne')

theorem modulated_leading_pair_eq {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    BaseResidual.stressPair (modulatedCoefficients H v) 0 p =
      (LeadingStress.theta v.profiles F.data.h p, LeadingStress.axial v.profiles F.data.h p) := by
  have he := modulated_leading_stress_eq H v hX heta
  exact Prod.ext he.1 he.2

theorem modulated_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (modulatedCoefficients H v).axial 0 (0, eta) = 4 * eta + W.axis.j :=
  aligned_leading_axis W H v.profiles v.finiteModification (modulation_after_entrance (d := d)) heta

theorem modulated_positive_axis {n : ℕ} (hn : 0 < n) {eta : ℝ} (heta : |eta| ≤ 1) :
    (modulatedCoefficients H v).phi n (0, eta) = 0 ∧
    (modulatedCoefficients H v).axial n (0, eta) = 0 ∧
    (modulatedCoefficients H v).pressure n (0, eta) = 0 :=
  aligned_positive_axis W H v.profiles v.finiteModification (modulation_after_entrance (d := d)) hn
    heta

theorem modulated_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization (modulatedCoefficients H v)
      (asSlowProfiles (modulatedScheme H v)) :=
  aligned_finiteIdentities W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

theorem modulated_first_edgeJets {c : ℝ} (hc : 0 < c) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (ConstructedSlowBase.activeRight W - 1))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.activeZeta c (Real.log (NominalConeAssembly.activeLeft W))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.activeDelta (Real.log (NominalConeAssembly.activeLeft W))
        (ConstructedSlowBase.activeRight W))
      (BaseResidual.stressPair (modulatedCoefficients H v) 1) :=
  aligned_first_edgeJets W H v.profiles v.finiteModification (modulation_after_entrance (d := d))
    (fun _ he => v.slow_outer_angular he) hc

theorem modulated_positive_stress_zero_right {n : ℕ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : NominalConeAssembly.activeRight W ≤ p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    (modulatedCoefficients H v).stressTheta n p = 0 ∧ (modulatedCoefficients H v).stressAxial n p =
      0 := by
  have hp' : Real.exp (ConstructedSlowBase.activeRight W) ≤ p.1 := by
    rwa [exp_right_eq_cone W]
  by_cases h1 : n = 1
  · subst n
    exact aligned_first_stress_zero_right W H v.profiles v.finiteModification
      (modulation_after_entrance (d := d))
      (fun _ he => v.slow_outer_angular he) hp' heta
  · exact aligned_stress_zero_right W H v.profiles v.finiteModification (modulation_after_entrance
    (d := d))
      (by omega) ((ConstructedSlowBase.outer_before_upper W).le.trans hp')

theorem modulated_positive_radialSupport {n : ℕ} (hn : 0 < n) :
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1) (zeroEnd W H d.modulation.left)
      (NominalConeAssembly.activeRight W) ((modulatedCoefficients H v).stressTheta n) ∧
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1) (zeroEnd W H d.modulation.left)
      (NominalConeAssembly.activeRight W) ((modulatedCoefficients H v).stressAxial n) := by
  have hz (eta : ℝ) (heta : eta ∈ Icc (-1 : ℝ) 1) (X : ℝ)
      (hX : X ∉ Icc (zeroEnd W H d.modulation.left) (NominalConeAssembly.activeRight W)) :
      (modulatedCoefficients H v).stressTheta n (X, eta) = 0 ∧
      (modulatedCoefficients H v).stressAxial n (X, eta) = 0 := by
    by_cases hl : X ≤ zeroEnd W H d.modulation.left
    · exact modulated_positive_stress_zero H v hn hl
    · have hr : NominalConeAssembly.activeRight W ≤ X := by
        by_contra hh
        exact hX ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hh).le⟩
      exact modulated_positive_stress_zero_right H v hn hr heta
  exact ⟨fun eta he X hX => (hz eta he X hX).1, fun eta he X hX => (hz eta he X hX).2⟩

theorem modulated_stress_zero_right (n : ℕ) {p : ℝ × ℝ}
    (hp : NominalConeAssembly.activeRight W ≤ p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    (modulatedCoefficients H v).stressTheta n p = 0 ∧ (modulatedCoefficients H v).stressAxial n p =
      0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hX : 0 ≤ p.1 := (LeadingStressWeights.activeRight_pos W).le.trans hp
    have he := modulated_leading_pair_eq H v hX (abs_le.mpr heta)
    have hz := he.trans (LeadingStressWeights.stress_zero_after v hp heta)
    exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  · exact modulated_positive_stress_zero_right H v hn hp heta

/-- Every actual coefficient, including orders zero and one, has support
in the same true-cone annulus on the closed physical parameter band. -/
theorem modulated_all_stress_support (n : ℕ) :
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1) (NominalConeAssembly.activeLeft W)
      (NominalConeAssembly.activeRight W) ((modulatedCoefficients H v).stressTheta n) ∧
    SlowStressSupport.radialSupport (Icc (-1 : ℝ) 1) (NominalConeAssembly.activeLeft W)
      (NominalConeAssembly.activeRight W) ((modulatedCoefficients H v).stressAxial n) := by
  have hz (eta : ℝ) (heta : eta ∈ Icc (-1 : ℝ) 1) (X : ℝ)
      (hX : X ∉ Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
      (modulatedCoefficients H v).stressTheta n (X, eta) = 0 ∧
      (modulatedCoefficients H v).stressAxial n (X, eta) = 0 := by
    by_cases hl : X ≤ NominalConeAssembly.activeLeft W
    · exact aligned_stress_zero_left W H v.profiles v.finiteModification
        (modulation_after_entrance (d := d)) n hl
    · have hr : NominalConeAssembly.activeRight W ≤ X := by
        by_contra hh
        exact hX ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hh).le⟩
      exact modulated_stress_zero_right H v n hr heta
  exact ⟨fun eta he X hX => (hz eta he X hX).1, fun eta he X hX => (hz eta he X hX).2⟩

/-- The entire summed normalized tensor has the same support, for every
cutoff schedule and every value of the expansion parameter. -/
theorem modulated_normalizedTensor_zero (a : ℕ → ℕ) (q : ℝ) {p : ℝ × ℝ}
    (hp : p.1 ∉ Icc (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W))
    (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    BaseResidual.normalizedTensor a F.data.h (modulatedCoefficients H v) (q, p) = 0 := by
  apply BaseResidual.slowSum_zero_of_all
  intro n
  have hs := modulated_all_stress_support H v n
  exact Prod.ext (hs.1 p.2 heta p.1 hp) (hs.2 p.2 heta p.1 hp)

/-- The transition lies in the true cone of the same final modulated
profile, with its actual restored histories. -/
theorem modulated_transition_true {p : ℝ × ℝ}
    (hp : p.1 ∈ Icc (cutoffInner W H d.modulation.left) (cutoffStop W H d.modulation.left))
    (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    TrueConeLoop.InTrueCone
      (ActivationStocks.profileStockOne v.profiles F.data.h p)
      (ActivationStocks.profileStockTwo v.profiles F.data.h p)
      (ModulatedCone.angularShear v.profiles.E p)
      (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p) := by
  have hx : 0 < p.1 := (cutoffInner_pos W H (modulation_after_entrance (d := d))).trans_le hp.1
  have hf := NominalConeAssembly.Witness.f_positive W hx heta
  apply v.true_cone_from_nominal hx (d.parameters_contains heta) hf.ne'
  intro _
  have hc := (NominalConeAssembly.isTrue_iff_loop W.profiles F.data.h p).mp
    (cutoff_transition_true W H (modulation_after_entrance (d := d)) hp heta)
  have hs := NominalConeAssembly.modulated_shears_eq W.profiles (W.domain_contains hx.le heta) hx
    hf.ne'
  simpa only [NominalConeAssembly.p1_eq_stock, NominalConeAssembly.p2_eq_stock, hs.1, hs.2] using hc

theorem modulated_quotients_smooth {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (modulatedCoefficients H v)
      (BaseResidual.activeZeta c (Real.log (NominalConeAssembly.activeLeft W))
        (ConstructedSlowBase.activeRight W)) n) :=
  BaseResidual.higherStressQuotient_smooth_of_support (modulated_smooth H v) hc
    (modulated_higherInteriorSupport H v) n

/-- The weighted estimate uses the true entrance, together with the
proved interior support and the actual first-order terminal jets. -/
theorem modulated_weighted_on_actual_scales {a : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    {K : Set SlowBorelBase.Inner} (hK : IsCompact K)
    (hWK : BaseResidual.activeWindow (Real.log (NominalConeAssembly.activeLeft W))
      (ConstructedSlowBase.activeRight W) ⊆ K)
    (ha : SlowBorelBase.AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (modulatedCoefficients H v)
        (BaseResidual.activeZeta c (Real.log (NominalConeAssembly.activeLeft W))
          (ConstructedSlowBase.activeRight W))) K a) :
    ConstructedSlowBase.WeightedStressBound a F.data.h (modulatedCoefficients H v)
      c (Real.log (NominalConeAssembly.activeLeft W)) (ConstructedSlowBase.activeRight W) := by
  apply ConstructedSlowBase.weighted_on_actual_scales W.axis.small.h_pos (modulated_smooth H v) hc
    (inner := zeroEnd W H d.modulation.left)
    (cut := Real.exp (ConstructedSlowBase.activeRight W - 1))
  · rw [Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
    exact (window_order W H (modulation_after_entrance (d := d))).1
  · have hz := zeroEnd_lt_outer_collar W H (modulation_after_entrance (d := d))
    have he : ConstructedSlowBase.activeRight W - 1 = FirstOrderBaseEdge.terminalShift W + 2 := by
      change FirstOrderBaseEdge.terminalShift W + 3 - 1 = _
      ring
    rw [he]
    exact hz.le
  · exact Real.exp_lt_exp.mpr (by linarith)
  · exact modulated_higherInteriorSupport H v
  · intro p hp
    have hz := modulated_positive_stress_zero H v (by decide : 0 < 1) hp.le
    exact Prod.ext hz.1 hz.2
  · exact modulated_first_edgeJets H v hc
  · exact hK
  · exact hWK
  · exact ha

open SlowBorelBase BaseResidual in
/-- One common schedule is chosen after rebuilding the aligned coefficient
family.  It controls both the ordinary base and its weighted stress sum. -/
noncomputable def scales (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (modulated_smooth H v) (modulated_quotients_smooth H v hc)
      W.axis.normalization) W.axis.small.h_pos (innerBox_isCompact 0
        (ConstructedSlowBase.scaleUpper W upper)) B)

open SlowBorelBase BaseResidual in
theorem scales_spec (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    B ≤ scales H v c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (modulatedCoefficients H v)
        (activeZeta c (Real.log (NominalConeAssembly.activeLeft W))
          (ConstructedSlowBase.activeRight W)))
      (innerBox 0 (ConstructedSlowBase.scaleUpper W upper)) (scales H v c hc upper B) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (modulated_smooth H v) (modulated_quotients_smooth H v hc)
      W.axis.normalization) W.axis.small.h_pos (innerBox_isCompact 0
        (ConstructedSlowBase.scaleUpper W upper)) B)

open SlowBorelBase BaseResidual in
theorem scales_admissible (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (modulatedCoefficients H v))
      (innerBox 0 (ConstructedSlowBase.scaleUpper W upper)) (scales H v c hc upper B) :=
  weightedBundle_base_scales (modulated_smooth H v) (modulated_quotients_smooth H v hc)
    (scales_spec H v c hc upper B).2

theorem scales_strictMono (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    StrictMono (scales H v c hc upper B) := (scales_spec H v c hc upper B).2.strictMono

theorem scales_weighted (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ConstructedSlowBase.WeightedStressBound (scales H v c hc upper B) F.data.h
      (modulatedCoefficients H v)
      c (Real.log (NominalConeAssembly.activeLeft W)) (ConstructedSlowBase.activeRight W) := by
  apply modulated_weighted_on_actual_scales H v hc
    (SlowBorelBase.innerBox_isCompact 0 (ConstructedSlowBase.scaleUpper W upper)) _ (scales_spec H
      v c hc upper B).2
  intro p hp
  exact ⟨⟨(Real.exp_pos _).le.trans hp.1.1.le,
    hp.1.2.le.trans (le_max_right _ _)⟩, hp.2⟩

end Modulated

end NavierStokes.EntranceAlignedBase
