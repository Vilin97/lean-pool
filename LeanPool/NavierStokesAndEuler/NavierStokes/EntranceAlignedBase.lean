/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ConstructedSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.FirstOrderBaseEdge
import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStressWeights
import LeanPool.NavierStokesAndEuler.NavierStokes.ZerothStressIdentity
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveRepresentatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.BasePhaseGeometry
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Related estimates used together by the same construction modules. -/

section

/-!
# A slow base whose cutoffs are aligned with the natural entrance

The retained local hierarchy extends strictly beyond the natural entrance.
Its cutoff transition lies inside the proved initial true-cone collar and
before the finite modulation begins.  The same finite base, local hierarchy,
and five-row exterior repair are used throughout.
-/

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.EntranceAlignedBase

open GlobalSlowProfiles AssembledSlowBase

section Geometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (H : NominalConeAssembly.Certificate W)

/-- True width, given by `H.initial.choose`. -/
noncomputable def trueWidth : ℝ := H.initial.choose

theorem trueWidth_pos : 0 < trueWidth W H := H.initial.choose_spec.1

theorem trueWidth_spec {y eta : ℝ} (hy : 0 < y) (ht : y ≤ trueWidth W H)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    NominalConeAssembly.IsTrue W.profiles F.data.h
      (NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)) :=
  H.initial.choose_spec.2.2 y eta hy ht heta

/-- Analytic end, given by `NominalConeAssembly.activeLeft W * Real.exp
W.controls.referenceWidth`. -/
noncomputable def analyticEnd : ℝ :=
  NominalConeAssembly.activeLeft W * Real.exp W.controls.referenceWidth

/-- Window cap, given by `min lo (min (NominalConeAssembly.activeLeft W * Real.exp (trueWidth W
H)) (analyticEnd W))`. -/
noncomputable def windowCap (lo : ℝ) : ℝ :=
  min lo (min (NominalConeAssembly.activeLeft W * Real.exp (trueWidth W H)) (analyticEnd W))

/-- Zero end, given by `NominalConeAssembly.activeLeft W + (windowCap W H lo -
NominalConeAssembly.activeLeft W) / 4`. -/
noncomputable def zeroEnd (lo : ℝ) : ℝ :=
  NominalConeAssembly.activeLeft W + (windowCap W H lo - NominalConeAssembly.activeLeft W) / 4

/-- Cutoff inner, given by `NominalConeAssembly.activeLeft W + (windowCap W H lo -
NominalConeAssembly.activeLeft W) / 2`. -/
noncomputable def cutoffInner (lo : ℝ) : ℝ :=
  NominalConeAssembly.activeLeft W + (windowCap W H lo - NominalConeAssembly.activeLeft W) / 2

/-- Cutoff stop, given by `NominalConeAssembly.activeLeft W + 3 * (windowCap W H lo -
NominalConeAssembly.activeLeft W) / 4`. -/
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
    (mul_nonneg (by
        norm_num) (ReservedPatches.left_pos F W.controls.radius W.controls.radius_pos
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

/-- Aligned coefficients, given by `coefficients (smallLocalization W H Q M hlo)
(smallBaseAgreement W H Q M hlo) (smallZeroOrder W H Q M hlo) M.contains`. -/
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
  have hb : 0 < b := Real.sqrt_pos.mpr (mul_pos (by
      norm_num) (NominalConeAssembly.activeLeft_pos W))
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

/-- Modulated scheme, given by `scheme W H v.profiles v.finiteModification
(modulation_after_entrance (d := d))`. -/
noncomputable def modulatedScheme : Scheme v.slowParameters F.data.h W.axis.normalization :=
  scheme W H v.profiles v.finiteModification (modulation_after_entrance (d := d))

/-- Modulated coefficients, given by `alignedCoefficients W H v.profiles v.finiteModification
(modulation_after_entrance (d := d))`. -/
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

end
end

end

section

/-!
# From the actual profile cone to the primary spectral cone

The signed axial shear in the profile cone is `c = -2 X U_X / E`.
Consequently the physical shear vector is `F * (-a,-c)`, while the
leading stress is a positive multiple of `(p₁-a,p₂-c)`.  The results
below derive the primary spectral and target cones from these identities.
-/

section

/-!
# Actual summed base fields in normalized band charts

All coordinate derivatives are taken at strictly positive backward time.
The constants remain uniform as that time approaches zero while the
normalized positive branch stays in a fixed annulus.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.BaseChartJets

open Set Filter Function PhaseJetBounds PrimaryPulseBounds
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow
/-- Chart: an abbreviation for `SlowBorelBase.Chart`. -/
abbrev Chart := SlowBorelBase.Chart
/-- Inner: an abbreviation for `SlowBorelBase.Inner`. -/
abbrev Inner := SlowBorelBase.Inner

/-- One domain, bundling `scale`, `carrier`, `isOpen`, `one_le_scale`. -/
noncomputable def oneDomain (ι : Type*) {E : Type*} [NormedAddCommGroup E]
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) : Domain ι E where
  scale _ := 1
  carrier := U
  isOpen := hU
  one_le_scale _ := le_rfl

theorem uniform_polynomial {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) {f : ι → E → F}
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ U i → ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C) :
    PolynomialJets (oneDomain ι U hU) f := by
  classical
  choose C hC hbound using hb
  refine ⟨hs, fun N => ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, ?_, 0, ?_⟩⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => (hC j).le))
  · intro i j hj x hx
    have hsum := Finset.single_le_sum (fun k _ => (hC k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa only [oneDomain, pow_zero, mul_one] using (hbound j i x hx).trans (by linarith)

theorem uniform_envelope {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set E} (hU : ∀ i, IsOpen (U i)) {f : ι → E → F} {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (U i))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i x, x ∈ U i →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * w i) :
    EnvelopeJets (oneDomain ι U hU) (fun i _ => w i) f := by
  classical
  choose C hC hbound using hb
  refine ⟨fun i _ _ => hw i, hs, fun N => ⟨1 + ∑ j ∈ Finset.range (N + 1), C j, ?_, 0, ?_⟩⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => (hC j).le))
  · intro i x hx j hj
    have hsum := Finset.single_le_sum (fun k _ => (hC k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa only [oneDomain, pow_zero, mul_one] using (hbound j i x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith) (hw i))

/-- Sum region, given by `Ioi 0 ×ˢ (Ioi 0 ×ˢ univ)`. -/
noncomputable def sumRegion : Set Chart := Ioi 0 ×ˢ (Ioi 0 ×ˢ univ)

theorem sumRegion_open : IsOpen sumRegion := isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_univ)

theorem scaleMap_norm_le {c M : ℝ} (hM : 1 ≤ M) (hc : |c| ≤ M) :
    ‖SlowBorelBase.scaleMap c‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hM)
  intro x
  change max ‖c * x.1‖ ‖x.2‖ ≤ M * ‖x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact max_le (mul_le_mul hc (norm_fst_le x) (norm_nonneg _) (zero_le_one.trans hM))
    ((norm_snd_le x).trans (le_mul_of_one_le_left (norm_nonneg x) hM))

/-- Recenter the frozen q-rescaling at the actual point `q=Q*rho`.
Only the bounded inverse of `rho`, not `Q⁻¹`, appears in this estimate. -/
theorem scaled_jet_from_blown {f : Chart → ℝ}
    (hf : ContDiffOn ℝ ∞ f sumRegion) {Q rho M : ℝ} {w : Inner}
    (hQ : 0 < Q) (hrho : 0 < rho) (hw : 0 < w.1)
    (hM : 1 ≤ M) (hi : 1 / rho ≤ M) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ SlowBorelBase.scaleMap Q) (rho, w)‖ ≤
      ‖SlowBorelBase.blownJet j f (Q * rho, w)‖ * M ^ j := by
  have hs : ContDiffOn ℝ ∞ (f ∘ SlowBorelBase.scaleMap (Q * rho)) sumRegion :=
    hf.comp (SlowBorelBase.scaleMap (Q * rho)).contDiff.contDiffOn
      (fun y hy => ⟨mul_pos (mul_pos hQ hrho) hy.1, hy.2⟩)
  have heq : f ∘ SlowBorelBase.scaleMap Q =
      (f ∘ SlowBorelBase.scaleMap (Q * rho)) ∘ SlowBorelBase.scaleMap rho⁻¹ := by
    funext y
    change f (Q * y.1, y.2) = f (Q * rho * (rho⁻¹ * y.1), y.2)
    congr 1
    apply Prod.ext
    · change Q * y.1 = Q * rho * (rho⁻¹ * y.1)
      field_simp
    · rfl
  have hx : SlowBorelBase.scaleMap rho⁻¹ (rho, w) ∈ sumRegion := by
    have hw' : ((1 : ℝ), w) ∈ sumRegion := ⟨by norm_num, hw, mem_univ _⟩
    simpa only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne'] using
      hw'
  have hb := norm_jet_comp_linear sumRegion_open hs (SlowBorelBase.scaleMap rho⁻¹) hx j
  have hnorm : ‖SlowBorelBase.scaleMap rho⁻¹‖ ≤ M :=
    scaleMap_norm_le hM (by simpa only [abs_of_pos (inv_pos.mpr hrho), one_div] using hi)
  rw [← heq] at hb
  apply hb.trans
  have hpoint : SlowBorelBase.scaleMap rho⁻¹ (rho, w) = (1, w) := by
    simp only [SlowBorelBase.scaleMap_apply, inv_mul_cancel₀ hrho.ne']
  rw [hpoint]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm j) (norm_nonneg _)

/-- Inner region, given by `Ioo qlo qhi ×ˢ (Ioo lo hi ×ˢ Ioo (-1) 1)`. -/
noncomputable def innerRegion (qlo qhi lo hi : ℝ) : Set Chart :=
  Ioo qlo qhi ×ˢ (Ioo lo hi ×ˢ Ioo (-1) 1)

theorem innerRegion_open (qlo qhi lo hi : ℝ) : IsOpen (innerRegion qlo qhi lo hi) :=
  isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

theorem normalized_error_envelope {ι : Type*} {h qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hsmall : ∀ i, Q i * qhi ≤ 1)
    (f : Chart → ℝ) (hf : ContDiffOn ℝ ∞ f sumRegion)
    (hb : ∀ j : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ w ∈ SlowBorelBase.innerBox lo hi,
        ‖SlowBorelBase.blownJet j f (q, w)‖ ≤ B * q ^ (2 * h)) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => f ∘ SlowBorelBase.scaleMap (Q i)) := by
  apply uniform_envelope _ (fun i => (Real.rpow_pos_of_pos (hQ i) _).le)
  · intro i
    apply hf.comp (SlowBorelBase.scaleMap (Q i)).contDiff.contDiffOn
    intro y hy
    exact ⟨mul_pos (hQ i) (hqlo.trans hy.1.1), hlo.trans hy.2.1.1, mem_univ _⟩
  · intro j
    obtain ⟨B, hB, hb⟩ := hb j
    let K := max 1 (1 / qlo)
    have hK : 1 ≤ K := le_max_left _ _
    refine ⟨B * qhi ^ (2 * h) * K ^ j, by positivity, ?_⟩
    intro i y hy
    have hrho : 0 < y.1 := hqlo.trans hy.1.1
    have hinv : 1 / y.1 ≤ K :=
      (one_div_le_one_div_of_le hqlo hy.1.1.le).trans (le_max_right _ _)
    have hscaled := scaled_jet_from_blown hf (hQ i) hrho (hlo.trans hy.2.1.1) hK hinv j
    have hw : y.2 ∈ SlowBorelBase.innerBox lo hi :=
      ⟨⟨hy.2.1.1.le, hy.2.1.2.le⟩, hy.2.2.1.le, hy.2.2.2.le⟩
    have hs : Q i * y.1 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hy.1.2.le (hQ i).le).trans (hsmall i)
    have hr : y.1 ^ (2 * h) ≤ qhi ^ (2 * h) :=
      Real.rpow_le_rpow hrho.le hy.1.2.le (by linarith)
    calc
      _ ≤ ‖SlowBorelBase.blownJet j f (Q i * y.1, y.2)‖ * K ^ j := hscaled
      _ ≤ (B * (Q i * y.1) ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right (hb _ (mul_pos (hQ i) hrho) hs _ hw) (by positivity)
      _ = (B * Q i ^ (2 * h) * y.1 ^ (2 * h)) * K ^ j := by
        rw [Real.mul_rpow (hQ i).le hrho.le]
        ring
      _ ≤ (B * Q i ^ (2 * h) * qhi ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (mul_nonneg hB.le (Real.rpow_nonneg (hQ i).le _))) (by
              positivity)
      _ = _ := by ring

/-- Swirl error, given by `SlowBorelBase.normalizedSwirl a h C d y - SlowBorelBase.leadingSwirl
C d y.2`. -/
noncomputable def swirlError (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) (y : Chart) : ℝ
    :=
  SlowBorelBase.normalizedSwirl a h C d y - SlowBorelBase.leadingSwirl C d y.2

/-- Axial error, given by `SlowBorelBase.slowSum a h d.axial y - d.axial 0 y.2`. -/
noncomputable def axialError (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients) (y : Chart) : ℝ :=
  SlowBorelBase.slowSum a h d.axial y - d.axial 0 y.2

theorem errors_smooth {a : ℕ → ℕ} (ha : StrictMono a) (h C : ℝ)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d) :
    ContDiffOn ℝ ∞ (swirlError a h C d) sumRegion ∧
    ContDiffOn ℝ ∞ (axialError a h d) sumRegion := by
  constructor
  · intro y hy
    have hX : 0 < y.2.1 := hy.2.1
    have hr : ContDiffAt ℝ ∞ (fun z : Chart => Real.sqrt (2 * z.2.1) / C) y :=
      ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (by
          positivity : (2 : ℝ) * y.2.1 ≠ 0)).div_const C
    have hs := SlowBorelBase.slowSum_smoothAt ha hd.phi h hy.1
    have h0 := (hd.phi 0).contDiffAt.comp y contDiffAt_snd
    exact ((hr.mul hs).sub (hr.mul h0)).contDiffWithinAt
  · intro y hy
    exact ((SlowBorelBase.slowSum_smoothAt ha hd.axial h hy.1).sub
      ((hd.axial 0).contDiffAt.comp y contDiffAt_snd)).contDiffWithinAt

theorem actual_error_envelopes {ι : Type*} {a : ℕ → ℕ} {h C qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hsmall : ∀ i, Q i * qhi ≤ 1) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => swirlError a h C d ∘ SlowBorelBase.scaleMap (Q i)) ∧
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => axialError a h d ∘ SlowBorelBase.scaleMap (Q i)) := by
  have hs := errors_smooth ha.strictMono h C hd
  constructor
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ hsmall _ hs.1
    intro j
    obtain ⟨B, hB, hb⟩ := SlowBorelBase.normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq hq1 w hw => (hb q hq hq1 w hw).1⟩
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ hsmall _ hs.2
    intro j
    obtain ⟨B, hB, hb⟩ := SlowBorelBase.normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq hq1 w hw => (hb q hq hq1 w hw).2⟩

/-- Physical input, given by `(1 - p.2.2, (p.1 ^ 2 / 2, p.2.1))`. -/
noncomputable def physicalInput (p : Slow) : Chart := (1 - p.2.2, (p.1 ^ 2 / 2, p.2.1))

theorem physicalInput_smooth : ContDiff ℝ ∞ physicalInput :=
  (contDiff_const.sub contDiff_snd.snd).prodMk
    (((contDiff_fst.pow 2).div_const 2).prodMk contDiff_snd.fst)

/-- Normalized coordinates, given by `SlowBorelBase.physicalChart h (physicalInput p)`. -/
noncomputable def normalizedCoordinates (h : ℝ) (p : Slow) : Chart :=
  SlowBorelBase.physicalChart h (physicalInput p)

theorem normalizedCoordinates_eq (h : ℝ) (p : Slow) :
    normalizedCoordinates h p =
      (SimilarityHomogeneity.chartQ h p,
        (SimilarityHomogeneity.chartX h p, SimilarityHomogeneity.chartEta h p)) := by
  simp only [normalizedCoordinates, physicalInput, SlowBorelBase.physicalChart,
    PhysicalCoordinateBounds.physicalQ, PhysicalCoordinateBounds.physicalX,
    PhysicalCoordinateBounds.physicalEta, PhysicalCoordinateBounds.timeShift,
    Function.comp_apply, PhysicalCoordinateBounds.qCoord, PhysicalCoordinateBounds.xCoord,
    PhysicalCoordinateBounds.etaCoord, SimilarityHomogeneity.chartQ,
    SimilarityHomogeneity.chartX, SimilarityHomogeneity.chartEta,
    SimilarityCoordinates.coordinateX, SimilarityCoordinates.coordinateEta,
    PhysicalCoordinateBounds.D]
  congr 2 <;> ring_nf

theorem normalizedCoordinates_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : ContDiffAt ℝ ∞ (normalizedCoordinates h) p :=
  (SlowBorelBase.physicalChart_smoothAt hh hh1 (show (physicalInput p).1 < 1 by
    dsimp [physicalInput]; linarith)).comp p physicalInput_smooth.contDiffAt

theorem normalizedCoordinates_q_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : 0 < (normalizedCoordinates h p).1 :=
  SlowBorelBase.physicalChart_positive hh hh1 (show (physicalInput p).1 < 1 by
    dsimp [physicalInput]; linarith)

theorem normalizedCoordinates_eta {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) : |(normalizedCoordinates h p).2.2| < 1 :=
  PhysicalCoordinateBounds.physicalEta_abs_lt_one (by linarith) (by linarith)
    (show (physicalInput p).1 < 1 by dsimp [physicalInput]; linarith)

/-- These are only pointwise geometric restrictions on the actual chart,
not coordinate-derivative or base-field estimates. -/
structure GeometryBounds {ι : Type*} (D : Domain ι Slow)
    (h r M qlo qhi lo hi : ℝ) : Prop where
  time : ∀ i p, p ∈ D.carrier i → 0 < p.2.2
  radius : ∀ i p, p ∈ D.carrier i → r ≤ p.1
  bounded : ∀ i p, p ∈ D.carrier i → ‖p‖ ≤ M
  q_range : ∀ i p, p ∈ D.carrier i →
    qlo < (normalizedCoordinates h p).1 ∧ (normalizedCoordinates h p).1 < qhi
  x_range : ∀ i p, p ∈ D.carrier i →
    lo < (normalizedCoordinates h p).2.1 ∧ (normalizedCoordinates h p).2.1 < hi

/-- Unit scale, given by `oneDomain ι D.carrier D.isOpen`. -/
noncomputable def unitScale {ι E : Type*} [NormedAddCommGroup E] (D : Domain ι E) : Domain ι E :=
  oneDomain ι D.carrier D.isOpen

private theorem iteratedFDeriv_pair {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E} {j : ℕ}
    (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x) :
    iteratedFDeriv ℝ j (fun y => (f y, g y)) x =
      (iteratedFDeriv ℝ j f x).prod (iteratedFDeriv ℝ j g x) := by
  have h1 := (ContinuousLinearMap.fst ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  have h2 := (ContinuousLinearMap.snd ℝ F G).iteratedFDeriv_comp_left (hf.prodMk hg) le_rfl
  apply ContinuousMultilinearMap.ext
  intro v
  apply Prod.ext
  · exact (congrArg (fun M => M v) h1).symm
  · exact (congrArg (fun M => M v) h2).symm

/-- The actual inverse coordinate jets are bounded for any fixed upper
q bound.  The proof uses the normalized inverse-Jacobian expressions,
which are regular at the limiting forward parameters. -/
theorem physicalChart_jet_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (lo hi qhi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Chart, p.1 < 1 →
      (SlowBorelBase.physicalChart h p).1 ≤ qhi →
      (SlowBorelBase.physicalChart h p).2.1 ∈ Icc lo hi →
      ‖iteratedFDeriv ℝ j (SlowBorelBase.physicalChart h) p‖ ≤
        C * (SlowBorelBase.physicalChart h p).1 ^ (-(j : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := PhysicalCoordinateBounds.physical_coordinate_derivative_bounds
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) lo hi qhi j
  refine ⟨C, hC, fun p hp hq hX => ?_⟩
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  have hqj := (PhysicalCoordinateBounds.physicalQ_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  have hxj := (PhysicalCoordinateBounds.physicalX_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  have hej := (PhysicalCoordinateBounds.physicalEta_contDiffAt
    (show 0 < 2 * h by linarith) (show 2 * h < 1 by linarith) hp).of_le hj
  obtain ⟨bq, be, bx⟩ := hb p hp hq hX
  change ‖iteratedFDeriv ℝ j (fun y => (PhysicalCoordinateBounds.physicalQ (2 * h) y,
    (PhysicalCoordinateBounds.physicalX (2 * h) y, PhysicalCoordinateBounds.physicalEta (2 * h)
        y))) p‖ ≤ _
  rw [iteratedFDeriv_pair hqj (hxj.prodMk hej), iteratedFDeriv_pair hxj hej,
    ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  exact max_le bq (max_le bx be)

/-- Uniform jets of `(rho,X,eta)` on strictly positive time.  No lower
bound on time is imposed, and no derivative at time zero is used. -/
theorem normalizedCoordinates_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hqlo : 0 < qlo)
    (H : GeometryBounds D h r M qlo qhi lo hi) :
    PolynomialJets (unitScale D) (fun _ => normalizedCoordinates h) := by
  apply uniform_polynomial D.isOpen
  · intro i p hp
    exact (normalizedCoordinates_smoothAt hh hh1 (H.time i p hp)).contDiffWithinAt
  · intro N
    classical
    choose C hC hb using fun j => physicalChart_jet_bound hh hh1 lo hi qhi j
    obtain ⟨B, hB, hBj⟩ := compact_jet_bound isOpen_univ physicalInput_smooth.contDiffOn
      (isCompact_closedBall (0 : Slow) M) (subset_univ _) N
    let A := 1 + ∑ j ∈ Finset.range (N + 1), C j * qlo ^ (-(j : ℝ))
    have hA : 0 < A := by
      dsimp [A]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (hC j).le (Real.rpow_nonneg hqlo.le _)))
    refine ⟨(N.factorial : ℝ) * A * B ^ N, by positivity, ?_⟩
    intro i p hp
    have hT := H.time i p hp
    have hphys : (physicalInput p).1 < 1 := by dsimp [physicalInput]; linarith
    have hq := normalizedCoordinates_q_pos hh hh1 hT
    have houter (j : ℕ) (hj : j ≤ N) :
        ‖iteratedFDeriv ℝ j (SlowBorelBase.physicalChart h) (physicalInput p)‖ ≤ A := by
      have hhj := hb j (physicalInput p) hphys (H.q_range i p hp).2.le
        ⟨(H.x_range i p hp).1.le, (H.x_range i p hp).2.le⟩
      have hpow : (normalizedCoordinates h p).1 ^ (-(j : ℝ)) ≤ qlo ^ (-(j : ℝ)) := by
        rw [Real.rpow_neg hq.le, Real.rpow_neg hqlo.le, Real.rpow_natCast, Real.rpow_natCast]
        exact inv_anti₀ (pow_pos hqlo j) (pow_le_pow_left₀ hqlo.le (H.q_range i p hp).1.le j)
      have hsum := Finset.single_le_sum (fun j _ =>
        mul_nonneg (hC j).le (Real.rpow_nonneg hqlo.le (-(j : ℝ))))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      exact (hhj.trans (mul_le_mul_of_nonneg_left hpow (hC j).le)).trans (by dsimp [A]; linarith)
    let U : Set Slow := {p | 0 < p.2.2}
    let V : Set Chart := Iio 1 ×ˢ univ
    have hU : IsOpen U := isOpen_lt continuous_const continuous_snd.snd
    have hV : IsOpen V := isOpen_Iio.prod isOpen_univ
    have hF : ContDiffOn ℝ ∞ (SlowBorelBase.physicalChart h) V :=
      fun q hq => (SlowBorelBase.physicalChart_smoothAt hh hh1 hq.1).contDiffWithinAt
    have hmap : MapsTo physicalInput U V := by
      intro q hq
      have ht : 0 < q.2.2 := hq
      exact ⟨by change 1 - q.2.2 < 1; linarith, mem_univ _⟩
    have hpnorm : p ∈ Metric.closedBall (0 : Slow) M := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using H.bounded i p hp
    have hchain := norm_iteratedFDerivWithin_comp_le hF physicalInput_smooth.contDiffOn
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl N) hV.uniqueDiffOn hU.uniqueDiffOn hmap hT
      (C := A) (D := B) (fun j hj => ?_) (fun j hj1 hj => ?_)
    · simp only [iteratedFDerivWithin_of_isOpen N hU hT]
        at hchain
      exact hchain
    · rw [iteratedFDerivWithin_of_isOpen j hV (hmap hT)]
      exact houter j hj
    · rw [iteratedFDerivWithin_of_isOpen j hU hT]
      exact (hBj j hj p hpnorm).trans (by simpa only [pow_one] using pow_le_pow_right₀ hB hj1)

/-- Axial factor, given by `(normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h)`. -/
noncomputable def axialFactor (h : ℝ) (p : Slow) : ℝ :=
  (normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h)

/-- Frequency factor, given by `axialFactor h p / p.1`. -/
noncomputable def frequencyFactor (h : ℝ) (p : Slow) : ℝ := axialFactor h p / p.1

/-- The actual `Q^A`-normalized angular velocity divided by the normalized
radius.  The factor `1/R` is retained in the definition. -/
noncomputable def frequency (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  frequencyFactor h p * SlowBorelBase.normalizedSwirl a h C d
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

/-- Axial, given by `axialFactor h p * SlowBorelBase.slowSum a h d.axial (SlowBorelBase.scaleMap
Q (normalizedCoordinates h p))`. -/
noncomputable def axial (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  axialFactor h p * SlowBorelBase.slowSum a h d.axial
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

/-- Leading frequency, given by `frequencyFactor h p * SlowBorelBase.leadingSwirl C d
(normalizedCoordinates h p).2`. -/
noncomputable def leadingFrequency (h C : ℝ) (d : SlowBorelBase.Coefficients) (p : Slow) : ℝ :=
  frequencyFactor h p * SlowBorelBase.leadingSwirl C d (normalizedCoordinates h p).2

/-- Leading axial, given by `axialFactor h p * d.axial 0 (normalizedCoordinates h p).2`. -/
noncomputable def leadingAxial (h : ℝ) (d : SlowBorelBase.Coefficients) (p : Slow) : ℝ :=
  axialFactor h p * d.axial 0 (normalizedCoordinates h p).2

theorem geometry_factors_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo)
    (H : GeometryBounds D h r M qlo qhi lo hi) :
    PolynomialJets (unitScale D) (fun _ => frequencyFactor h) ∧
    PolynomialJets (unitScale D) (fun _ => axialFactor h) := by
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hq := hc.clm (ContinuousLinearMap.fst ℝ ℝ Inner)
  have hp : PolynomialJets (unitScale D) (fun _ => axialFactor h) := by
    apply hq.compact_comp isOpen_Ioi
      (show ContDiffOn ℝ ∞ (fun x : ℝ => x ^ (-CoordinateAlgebra.A h)) (Ioi 0) from
        fun x hx => (contDiffAt_id.rpow_const_of_ne hx.ne').contDiffWithinAt)
      isCompact_Icc (fun x hx => hqlo.trans_le hx.1)
    · intro i p hp
      exact ⟨(H.q_range i p hp).1.le, (H.q_range i p hp).2.le⟩
  have hR : PolynomialJets (unitScale D) (fun _ p => p.1) := by
    have hrange (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : |p.1| ≤ M := by
      simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans (H.bounded i p hp)
    simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one] using
      (PolynomialJets.affine (D := unitScale D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) hM (by
          simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one, Real.norm_eq_abs]
              using hrange))
  have hRi := hR.inv hr (fun i p hp => by
      rw [abs_of_pos (hr.trans_le (H.radius i p hp))]
      exact H.radius i p hp)
    (fun i p hp => by
      simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans (H.bounded i p hp))
  refine ⟨?_, hp⟩
  have he := hp.mul hRi
  exact he

theorem leading_fields_polynomial {ι : Type*} {D : Domain ι Slow}
    {h r M qlo qhi lo hi C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d) :
    PolynomialJets (unitScale D) (fun _ => leadingFrequency h C d) ∧
    PolynomialJets (unitScale D) (fun _ => leadingAxial h d) := by
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hcinner := hc.clm (ContinuousLinearMap.snd ℝ ℝ Inner)
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : (normalizedCoordinates h p).2 ∈
      SlowBorelBase.innerBox lo hi := by
    have he := normalizedCoordinates_eta hh hh1 (H.time i p hp)
    exact ⟨⟨(H.x_range i p hp).1.le, (H.x_range i p hp).2.le⟩,
      (abs_lt.mp he).1.le, (abs_lt.mp he).2.le⟩
  have hs : ContDiffOn ℝ ∞ (SlowBorelBase.leadingSwirl C d) {w : Inner | 0 < w.1} := by
    intro w hw
    have hX : 0 < w.1 := hw
    exact ((((contDiffAt_const.mul contDiffAt_fst).sqrt
      (by positivity : (2 : ℝ) * w.1 ≠ 0)).div_const C).mul (hd.phi 0).contDiffAt).contDiffWithinAt
  have hv := hcinner.compact_comp (isOpen_lt continuous_const continuous_fst) hs
    (SlowBorelBase.innerBox_isCompact lo hi) (fun _ hx => hlo.trans_le hx.1.1) hmap
  have hg := hcinner.compact_comp isOpen_univ (hd.axial 0).contDiffOn
    (SlowBorelBase.innerBox_isCompact lo hi) (subset_univ _) hmap
  have hf := geometry_factors_polynomial hh hh1 hr hM hqlo H
  exact ⟨hf.1.mul hv, hf.2.mul hg⟩

/-- All quantities in this conclusion are literal summed-field formulas. -/
structure Estimates {ι : Type*} (D : Domain ι Slow) (Q : ι → ℝ)
    (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients) : Prop where
  frequency_error : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
    (fun i p => frequency a h C d (Q i) p - leadingFrequency h C d p)
  axial_error : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
    (fun i p => axial a h d (Q i) p - leadingAxial h d p)
  leading_frequency : PolynomialJets (unitScale D) (fun _ => leadingFrequency h C d)
  leading_axial : PolynomialJets (unitScale D) (fun _ => leadingAxial h d)
  frequency_jets : PolynomialJets (unitScale D) (fun i => frequency a h C d (Q i))
  axial_jets : PolynomialJets (unitScale D) (fun i => axial a h d (Q i))

theorem actual_estimates {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) : Estimates D Q a h C d := by
  have he := actual_error_envelopes hh hqlo hqhi hlo hd ha Q hQ hsmall
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : normalizedCoordinates h p ∈
      innerRegion qlo qhi lo hi := by
    have heta := abs_lt.mp (normalizedCoordinates_eta hh hh1 (H.time i p hp))
    exact ⟨H.q_range i p hp, H.x_range i p hp, heta⟩
  have hev := he.1.comp hc (fun _ => rfl) hmap
  have heg := he.2.comp hc (fun _ => rfl) hmap
  have hf := geometry_factors_polynomial hh hh1 hr hM hqlo H
  have h0 := leading_fields_polynomial (C := C) hh hh1 hr hM hqlo hlo H hd
  have hF : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => frequency a h C d (Q i) p - leadingFrequency h C d p) := by
    apply (hev.polynomial_smul hf.1).congr
    intro i p _
    simp only [frequency, leadingFrequency, swirlError, Function.comp_apply, smul_eq_mul, mul_sub,
        SlowBorelBase.scaleMap_apply]
  have hG : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => axial a h d (Q i) p - leadingAxial h d p) := by
    apply (heg.polynomial_smul hf.2).congr
    intro i p _
    simp only [axial, leadingAxial, axialError, Function.comp_apply, smul_eq_mul, mul_sub,
        SlowBorelBase.scaleMap_apply]
  have hw i p (_hp : p ∈ (unitScale D).carrier i) : Q i ^ (2 * h) ≤ 1 :=
    Real.rpow_le_one (hQ i).le (hQ1 i) (by linarith)
  refine ⟨hF, hG, h0.1, h0.2, ?_, ?_⟩
  · exact ((hF.to_polynomial hw).add h0.1).congr (fun _ _ _ => sub_add_cancel _ _)
  · exact ((hG.to_polynomial hw).add h0.2).congr (fun _ _ _ => sub_add_cancel _ _)

/-- With unit bookkeeping scale, polynomial bounds are uniform bounds. -/
theorem polynomial_unit_bound {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F}
    (hf : PolynomialJets (unitScale D) f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i j, j ≤ N → ∀ x ∈ D.carrier i,
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  exact ⟨C, hC, fun i j hj x hx => by
      simpa only [unitScale, oneDomain, one_pow, mul_one] using hm i j hj x hx⟩

theorem envelope_unit_bound {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F} {w : ι → E → ℝ}
    (hf : EnvelopeJets (unitScale D) w f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i x, x ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * w i x := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  exact ⟨C, hC, fun i x hx j hj => by
      simpa only [unitScale, oneDomain, one_pow, mul_one] using hm i x hx j hj⟩

theorem polynomial_of_unit {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {D : Domain ι E} {f : ι → E → F}
    (hf : PolynomialJets (unitScale D) f) : PolynomialJets D f := by
  refine ⟨hf.smooth, fun N => ?_⟩
  obtain ⟨C, hC, hb⟩ := polynomial_unit_bound hf N
  exact ⟨C, hC, 0, fun i j hj x hx => by simpa only [pow_zero, mul_one] using hb i j hj x hx⟩

theorem norm_fderiv_eq_jet_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0))

theorem norm_second_fderiv_eq_jet_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [norm_fderiv_eq_jet_one, norm_iteratedFDeriv_fderiv]

theorem Estimates.polynomial_fields {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients} (H : Estimates D Q a h C d) :
    PolynomialJets D (fun i => frequency a h C d (Q i)) ∧
    PolynomialJets D (fun i => axial a h d (Q i)) :=
  ⟨polynomial_of_unit H.frequency_jets, polynomial_of_unit H.axial_jets⟩

/-- The actual all-order error estimates supply the precise C1/C2 input
of `BasePhaseGeometry`. The constant is chosen before the band or label. -/
theorem Estimates.localBaseBounds {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (H : Estimates D Q a h C d) (hh : 0 ≤ h)
    (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hconvex : ∀ i, Convex ℝ (D.carrier i)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds (frequency a h C d (Q i)) (axial a h d (Q i))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B (Q i ^ h) := by
  obtain ⟨CF, hCF, hEF⟩ := envelope_unit_bound H.frequency_error 1
  obtain ⟨CG, hCG, hEG⟩ := envelope_unit_bound H.axial_error 1
  obtain ⟨BF, hBF, hBFj⟩ := polynomial_unit_bound H.leading_frequency 2
  obtain ⟨BG, hBG, hBGj⟩ := polynomial_unit_bound H.leading_axial 2
  let K := CF + CG + BF + BG + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hCFK : CF ≤ K := by dsimp [K]; linarith
  have hCGK : CG ≤ K := by dsimp [K]; linarith
  have hBFK : BF ≤ K := by dsimp [K]; linarith
  have hBGK : BG ≤ K := by dsimp [K]; linarith
  refine ⟨2 * K, by linarith, fun i => ?_⟩
  have hsquare : (Q i ^ h) ^ 2 = Q i ^ (2 * h) := by
    rw [← Real.rpow_mul_natCast (hQ i).le]
    congr 1
    ring
  have hsmall : (Q i ^ h) ^ 2 ≤ 1 := by
    rw [hsquare]
    exact Real.rpow_le_one (hQ i).le (hQ1 i) (mul_nonneg (by norm_num) hh)
  have hF (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.frequency_jets.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hG (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.axial_jets.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hF0 (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.leading_frequency.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  have hG0 (x : Slow) (hx : x ∈ D.carrier i) :=
    (H.leading_axial.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)
  apply BasePhaseGeometry.localBase_of_normalized_error (zero_le_one.trans hK) hsmall (hconvex i)
    (fun x hx => (hF x hx).differentiableAt (by simp))
    (fun x hx => (hG x hx).differentiableAt (by simp))
    (fun x hx => (hF0 x hx).differentiableAt (by simp))
    (fun x hx => (hG0 x hx).differentiableAt (by simp))
    (fun x hx => ((hF0 x hx).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by
        simp)).differentiableAt (by simp))
    (fun x hx => ((hG0 x hx).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by
        simp)).differentiableAt (by simp))
  · intro x hx
    rw [norm_fderiv_eq_jet_one]
    exact (hBFj i 1 (by norm_num) x hx).trans hBFK
  · intro x hx
    rw [norm_fderiv_eq_jet_one]
    exact (hBGj i 1 (by norm_num) x hx).trans hBGK
  · intro x hx
    rw [norm_second_fderiv_eq_jet_two]
    exact (hBFj i 2 le_rfl x hx).trans hBFK
  · intro x hx
    rw [norm_second_fderiv_eq_jet_two]
    exact (hBGj i 2 le_rfl x hx).trans hBGK
  · intro x hx
    have he := hEF i x hx 0 (by norm_num)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCFK (Real.rpow_nonneg (hQ i).le _))
  · intro x hx
    have he := hEF i x hx 1 le_rfl
    rw [← norm_fderiv_eq_jet_one, fderiv_fun_sub ((hF x hx).differentiableAt (by simp))
      ((hF0 x hx).differentiableAt (by simp))] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCFK (Real.rpow_nonneg (hQ i).le _))
  · intro x hx
    have he := hEG i x hx 1 le_rfl
    rw [← norm_fderiv_eq_jet_one, fderiv_fun_sub ((hG x hx).differentiableAt (by simp))
      ((hG0 x hx).differentiableAt (by simp))] at he
    rw [hsquare]
    exact he.trans (mul_le_mul_of_nonneg_right hCGK (Real.rpow_nonneg (hQ i).le _))

/-- Primitive summed-coefficient hypotheses, not supplied base estimates,
produce both interfaces needed by the actual phase construction. -/
theorem actual_localBase_and_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets D (fun i => frequency a h C d (Q i)) ∧
    PolynomialJets D (fun i => axial a h d (Q i)) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds (frequency a h C d (Q i)) (axial a h d (Q i))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B (Q i ^ h) := by
  have he := actual_estimates hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall
  exact ⟨he.polynomial_fields.1, he.polynomial_fields.2,
    he.localBaseBounds hh.le hQ hQ1 hconvex⟩

/-- Exact homogeneity of the actual inverse chart under the physical band
rescaling. The frozen summation variable is `Q*rho`. -/
theorem physicalChart_band {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    SlowBorelBase.physicalChart h
      (SimilarityHomogeneity.physicalScale h Q (physicalInput p)) =
      SlowBorelBase.scaleMap Q (normalizedCoordinates h p) := by
  have hp : (physicalInput p).1 < 1 := by dsimp [physicalInput]; linarith
  simp only [SlowBorelBase.physicalChart_eq, SimilarityHomogeneity.q_physicalScale hh hh1 hQ hp,
    SimilarityHomogeneity.inner_physicalScale hh hh1 hQ hp,
    SlowBorelBase.scaleMap_apply, normalizedCoordinates]

/-- Cancelling the physical `Q^A` normalization leaves precisely `rho^(-A)`. -/
theorem normalized_power {Q rho A : ℝ} (hQ : 0 < Q) (hrho : 0 < rho) :
    Q ^ A * (Q * rho) ^ (-A) = rho ^ (-A) := by
  rw [Real.mul_rpow hQ.le hrho.le, ← mul_assoc, ← Real.rpow_add hQ]
  simp

/-- The leading angular frequency retains the `1/R` factor; simplifying it
uses the actual relation `X=R²/(2*rho)`. -/
theorem leadingFrequency_eq {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    leadingFrequency h C d p =
      (normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 (normalizedCoordinates h p).2 := by
  have hrho := normalizedCoordinates_q_pos hh hh1 hT
  have hX : 2 * (normalizedCoordinates h p).2.1 =
      p.1 ^ 2 / (normalizedCoordinates h p).1 := by
    rw [normalizedCoordinates_eq]
    simp only [SimilarityHomogeneity.chartX, SimilarityCoordinates.coordinateX,
      SimilarityHomogeneity.chartQ]
    ring
  unfold leadingFrequency frequencyFactor axialFactor SlowBorelBase.leadingSwirl
  rw [hX, Real.sqrt_div (sq_nonneg p.1), Real.sqrt_sq hR.le,
    Real.sqrt_eq_rpow, Real.rpow_sub hrho]
  calc
    _ = (p.1 / p.1) * (((normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) /
        (normalizedCoordinates h p).1 ^ (1 / 2 : ℝ)) / C * d.phi 0 (normalizedCoordinates h p).2)
            := by
            ring
    _ = _ := by rw [div_self hR.ne', one_mul]

/-- Band point, given by `(1 - Q * p.2.2, !₂[Real.sqrt Q * p.1, 0, Q ^ CoordinateAlgebra.D h *
p.2.1])`. -/
noncomputable def bandPoint (h Q : ℝ) (p : Slow) : ProblemStatement.SpaceTime :=
  (1 - Q * p.2.2, !₂[Real.sqrt Q * p.1, 0, Q ^ CoordinateAlgebra.D h * p.2.1])

theorem bandPoint_time {h Q : ℝ} (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    (bandPoint h Q p).1 < 1 := by
  change 1 - Q * p.2.2 < 1
  linarith [mul_pos hQ hT]

theorem bandPoint_profile {h Q : ℝ} (hQ : 0 ≤ Q) (p : Slow) :
    AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2 =
      SimilarityHomogeneity.physicalScale h Q (physicalInput p) := by
  apply Prod.ext
  · change 1 - Q * p.2.2 = 1 - Q * (1 - (1 - p.2.2))
    ring
  · apply Prod.ext
    · change ((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2 = Q * (p.1 ^ 2 / 2)
      rw [mul_pow, Real.sq_sqrt hQ]
      ring
    · rfl

theorem bandPoint_chart {h Q : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hQ : 0 < Q) {p : Slow} (hT : 0 < p.2.2) :
    SlowBorelBase.cartesianChart h (bandPoint h Q p) =
      SlowBorelBase.scaleMap Q (normalizedCoordinates h p) := by
  unfold SlowBorelBase.cartesianChart
  rw [bandPoint_profile hQ.le, physicalChart_band hh hh1 hQ hT]

/-- Literal equality with the axial component of the constructed curl base. -/
theorem axial_eq_normalized_velocity {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    axial a h d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 2 := by
  rw [SlowBorelBase.baseVelocity_axial ha hh hh1 hd C (bandPoint_time (h := h) hQ hT)]
  unfold SlowBorelBase.physicalProfile
  rw [bandPoint_profile hQ.le, physicalChart_band hh hh1 hQ hT]
  simp only [SlowBorelBase.scaleMap_apply, smul_eq_mul]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  rfl

/-- Literal equality with `Q^A` times the constructed angular velocity,
divided by the normalized radius. -/
theorem frequency_eq_normalized_velocity {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    frequency a h C d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 1 / p.1 := by
  have hm := SlowBorelBase.angularMoment_eq_normalizedSwirl ha hh hh1 hd C
    (bandPoint_time (h := h) hQ hT) (bandPoint h Q p).2
  have hr : 0 < Real.sqrt Q * p.1 := mul_pos (Real.sqrt_pos.2 hQ) hR
  have hsqrt : Real.sqrt (2 * AxisymmetricFields.radialEnergy (bandPoint h Q p).2) =
      Real.sqrt Q * p.1 := by
    change Real.sqrt (2 * (((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2)) = _
    rw [show 2 * (((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2) = (Real.sqrt Q * p.1) ^ 2 by ring,
      Real.sqrt_sq hr.le]
  rw [hsqrt, bandPoint_chart hh hh1 hQ hT] at hm
  change -0 * _ + (Real.sqrt Q * p.1) * _ = _ at hm
  simp only [neg_zero, zero_mul, zero_add] at hm
  have hv : SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 1 =
      (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)).1 ^ (-CoordinateAlgebra.A h) *
        SlowBorelBase.normalizedSwirl a h C d (SlowBorelBase.scaleMap Q (normalizedCoordinates h
            p)) := by
    apply mul_left_cancel₀ hr.ne'
    simpa only [mul_assoc] using hm
  rw [hv]
  unfold frequency frequencyFactor axialFactor
  simp only [SlowBorelBase.scaleMap_apply]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  ring

/-- The physical scale restriction is chosen after the fixed chart bounds
and before any band, label, or derivative order. -/
theorem exists_dyadic_cutoff {qhi : ℝ} (hqhi : 0 < qhi) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧ ∀ n ≥ N, ChartScales.Q n * qhi ≤ 1 := by
  obtain ⟨N, hN⟩ := ChartScales.exists_slow_power_epsilon_cutoff 1 (by norm_num)
    0 1 (1 / qhi) (by norm_num) (by positivity)
  refine ⟨max N0 N, le_max_left _ _, fun n hn => ?_⟩
  have hb := hN n ((le_max_right N0 N).trans hn)
  simp only [ChartScales.epsilon, Real.rpow_zero, Real.rpow_one, one_mul] at hb
  exact ((lt_div_iff₀ hqhi).mp hb).le

/-- Actual dyadic input interface. Indices may include every active label
of every band above the one fixed cutoff. -/
theorem dyadic_actual_bounds {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (band : ι → ℕ) {N : ℕ} (hN : ∀ n ≥ N, ChartScales.Q n * qhi ≤ 1)
    (hband : ∀ i, N ≤ band i) :
    PolynomialJets D (fun i => frequency a h C d (ChartScales.Q (band i))) ∧
    PolynomialJets D (fun i => axial a h d (ChartScales.Q (band i))) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds
        (frequency a h C d (ChartScales.Q (band i)))
        (axial a h d (ChartScales.Q (band i)))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B
        (ChartScales.epsilon h (band i)) :=
  actual_localBase_and_polynomial hh hh1 hr hM hqlo hqhi hlo H hconvex hd ha
    (fun i => ChartScales.Q (band i)) (fun i => ChartScales.Q_pos (band i))
    (fun i => ChartScales.Q_le_one (band i)) (fun i => hN (band i) (hband i))

/-- The already selected enlarged-bundle schedule of the nominal base
instantiates the chart theorem without any additional schedule choice. -/
theorem nominal_estimates {ι : Type*} {D : Domain ι Slow}
    {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ ConstructedSlowBase.scaleUpper W upper)
    (H : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    Estimates D Q (ConstructedSlowBase.nominalScales W c hc upper B)
      F.data.h W.axis.normalization (AssembledSlowBase.nominalCoefficients W) :=
  actual_estimates (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W)
    hr hM hqlo hqhi hlo H (AssembledSlowBase.nominalCoefficients_smooth W)
    (ConstructedSlowBase.nominalScales_admissible_on W c hc upper B hlo.le hhi)
    Q hQ hQ1 hsmall

/-- The same conclusion for the actual solved finite modulation and its
single common weighted/ordinary Borel schedule. -/
theorem modulated_estimates {ι : Type*} {D : Domain ι Slow}
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ ConstructedSlowBase.scaleUpper W upper)
    (H : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    Estimates D Q (ConstructedSlowBase.Modulated.scales v c hc upper B)
      F.data.h W.axis.normalization (ConstructedSlowBase.Modulated.coefficients v) := by
  have ha := ConstructedSlowBase.admissibleScales_mono
    (ConstructedSlowBase.Modulated.scales_admissible v c hc upper B)
    (show SlowBorelBase.innerBox lo hi ⊆
      SlowBorelBase.innerBox 0 (ConstructedSlowBase.scaleUpper W upper) from
        fun w hw => ⟨⟨hlo.le.trans hw.1.1, hw.1.2.trans hhi⟩, hw.2⟩)
  exact actual_estimates (ConstructedSlowBase.height_pos W) (ConstructedSlowBase.height_lt_half W)
    hr hM hqlo hqhi hlo H (ConstructedSlowBase.Modulated.coefficients_smooth v) ha Q hQ hQ1 hsmall

/-- A direct paired all-jet form, with constants uniform over every index
of the chart family. -/
theorem Estimates.uniform_errors {ι : Type*} {D : Domain ι Slow} {Q : ι → ℝ}
    {a : ℕ → ℕ} {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (H : Estimates D Q a h C d) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ i x, x ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun p => frequency a h C d (Q i) p - leadingFrequency h C d p) x‖ ≤
        K * Q i ^ (2 * h) ∧
      ‖iteratedFDeriv ℝ j (fun p => axial a h d (Q i) p - leadingAxial h d p) x‖ ≤
        K * Q i ^ (2 * h) := by
  obtain ⟨CF, hCF, hF⟩ := envelope_unit_bound H.frequency_error N
  obtain ⟨CG, hCG, hG⟩ := envelope_unit_bound H.axial_error N
  refine ⟨max CF CG, hCF.trans (le_max_left _ _), fun i x hx j hj => ?_⟩
  have hw := H.frequency_error.nonneg i x hx
  exact ⟨(hF i x hx j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw),
    (hG i x hx j hj).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)⟩

/-- Every actual positive active label above a single fixed band. -/
noncomputable def CellIndex (h lo hi : ℝ) (N : ℕ) :=
  {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) //
    N ≤ L.val.1}

/-- Cell band, given by `L.val.val.1`. -/
noncomputable def cellBand {h lo hi : ℝ} {N : ℕ} (L : CellIndex h lo hi N) : ℕ := L.val.val.1

/-- The actual convex positive-time three-mesh cells. The slow scale is
precisely the manuscript's `S_n`; it is not a replacement coordinate. -/
noncomputable def positiveCellDomain (h lo hi : ℝ) (N : ℕ) : Domain (CellIndex h lo hi N) Slow where
  scale L := ChartScales.S (cellBand L)
  carrier L := PositiveRepresentatives.positiveCell L.val.val.1 L.val.val.2
  isOpen L := PositiveRepresentatives.positiveCell_open _ _
  one_le_scale L := by
    have hn : (1 : ℝ) ≤ L.val.val.1 := by exact_mod_cast L.val.property.1
    change 1 ≤ (L.val.val.1 : ℝ) ^ 2
    nlinarith

theorem positiveCellDomain_convex (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    Convex ℝ ((positiveCellDomain h lo hi N).carrier L) :=
  PositiveRepresentatives.positiveCell_convex _ _

theorem positiveCellDomain_representative (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    PositiveRepresentatives.representative (PrimaryRepresentatives.referenceCompact h lo hi) L.val ∈
      (positiveCellDomain h lo hi N).carrier L :=
  PositiveRepresentatives.representative_mem_cell _ L.val

theorem positiveCellDomain_covers (h lo hi : ℝ) (N : ℕ) (L : CellIndex h lo hi N) :
    PrimaryRepresentatives.gridBox L.val.val.1 L.val.val.2 2 ∩ PositiveRepresentatives.positiveTime
        ⊆
      (positiveCellDomain h lo hi N).carrier L :=
  PositiveRepresentatives.enlarged_positive_subset_cell L.val.property.1 _

/-- Full actual-input conclusion. The fixed annular profile and one
admissible Borel schedule give all-order estimates and a single local-base
constant on every actual enlarged positive-time cell above one band.
No representative proximity, inverse-coordinate jets, or local-base
estimates are hypotheses of this theorem. -/
theorem exists_actual_positive_charts {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hlo : 0 < lo) (hhi : lo ≤ hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox (lo / 2) (2 * hi)) a) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧
      Estimates (positiveCellDomain h lo hi N) (fun L => ChartScales.Q (cellBand L)) a h C d ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ L : CellIndex h lo hi N,
        PhaseEstimates.LocalBaseBounds
          (frequency a h C d (ChartScales.Q (cellBand L)))
          (axial a h d (ChartScales.Q (cellBand L)))
          (leadingFrequency h C d) (leadingAxial h d)
          ((positiveCellDomain h lo hi N).carrier L) B (ChartScales.epsilon h (cellBand L)) := by
  obtain ⟨Nc, hNc⟩ := PositiveRepresentatives.exists_positive_reference_charts hh hh1 hlo hhi
  obtain ⟨N, hN, hs⟩ := exists_dyadic_cutoff (qhi := 4) (by norm_num) (max N0 Nc)
  have hNNc : Nc ≤ N := (le_max_right _ _).trans hN
  have hb (L : CellIndex h lo hi N) : N ≤ cellBand L := L.property
  have hc (L : CellIndex h lo hi N) (p : Slow)
      (hp : p ∈ (positiveCellDomain h lo hi N).carrier L) :=
    (hNc L.val (hNNc.trans L.property)).2.2.2.2 p hp
  have hgeom : GeometryBounds (positiveCellDomain h lo hi N) h (Real.sqrt lo / 2)
      (PositiveRepresentatives.cellBound hi) (1 / 4) 4 (lo / 2) (2 * hi) := by
    refine ⟨fun L p hp => (hc L p hp).2.2.2.1,
      fun L p hp => (hc L p hp).2.1,
      fun L p hp => (hc L p hp).2.2.1, ?_, ?_⟩
    · intro L p hp
      simp only [normalizedCoordinates_eq]
      exact (hc L p hp).2.2.2.2.1
    · intro L p hp
      simp only [normalizedCoordinates_eq]
      exact (hc L p hp).2.2.2.2.2
  have hM : 1 ≤ PositiveRepresentatives.cellBound hi :=
    (show (1 : ℝ) ≤ 3 by norm_num).trans (le_max_right _ _)
  have he := actual_estimates hh hh1 (half_pos (Real.sqrt_pos.mpr hlo)) hM
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 4) (half_pos hlo)
    hgeom hd ha (fun L => ChartScales.Q (cellBand L))
    (fun L => ChartScales.Q_pos (cellBand L)) (fun L => ChartScales.Q_le_one (cellBand L))
    (fun L => hs _ (hb L))
  refine ⟨N, (le_max_left _ _).trans hN, he, ?_⟩
  exact he.localBaseBounds hh.le (fun L => ChartScales.Q_pos (cellBand L))
    (fun L => ChartScales.Q_le_one (cellBand L)) (positiveCellDomain_convex h lo hi N)

/-- Actual modulated base, actual common schedule, and actual positive
active cells, combined in one theorem. The only annular restriction is
that the selected schedule controls the enlarged fixed inner box. -/
theorem exists_modulated_positive_charts
    {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B0 : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (hbox : 2 * hi ≤ ConstructedSlowBase.scaleUpper W upper) (N0 : ℕ) :
    let a := ConstructedSlowBase.Modulated.scales v c hc upper B0
    let d := ConstructedSlowBase.Modulated.coefficients v
    ∃ N : ℕ, N0 ≤ N ∧
      Estimates (positiveCellDomain F.data.h lo hi N)
        (fun L => ChartScales.Q (cellBand L)) a F.data.h W.axis.normalization d ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ L : CellIndex F.data.h lo hi N,
        PhaseEstimates.LocalBaseBounds
          (frequency a F.data.h W.axis.normalization d (ChartScales.Q (cellBand L)))
          (axial a F.data.h d (ChartScales.Q (cellBand L)))
          (leadingFrequency F.data.h W.axis.normalization d) (leadingAxial F.data.h d)
          ((positiveCellDomain F.data.h lo hi N).carrier L) B
          (ChartScales.epsilon F.data.h (cellBand L)) := by
  dsimp only
  have ha := ConstructedSlowBase.admissibleScales_mono
    (ConstructedSlowBase.Modulated.scales_admissible v c hc upper B0)
    (show SlowBorelBase.innerBox (lo / 2) (2 * hi) ⊆
      SlowBorelBase.innerBox 0 (ConstructedSlowBase.scaleUpper W upper) from
      fun w hw => ⟨⟨(half_pos hlo).le.trans hw.1.1, hw.1.2.trans hbox⟩, hw.2⟩)
  exact exists_actual_positive_charts (ConstructedSlowBase.height_pos W)
    (ConstructedSlowBase.height_lt_half W) hlo hhi
    (ConstructedSlowBase.Modulated.coefficients_smooth v) ha N0

end NavierStokes.BaseChartJets

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ProfileSpectralCone

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace

/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

private theorem shear_size_mul {a c : ℝ} (ha : a ≠ 0) :
    a * (a * (1 + (c / a) ^ 2)) = a ^ 2 + c ^ 2 := by
  field_simp

theorem referenceCone_of_trueCone {F p₁ p₂ a c : ℝ} (hF : 0 < F)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) := by
  apply PrimaryRepresentatives.referenceCone_of_shear_coordinates hF h.1
  have he := shear_size_mul (c := c) h.1.ne'
  have hm := mul_lt_mul_of_pos_left h.2.1 h.1
  nlinarith

/-- The square of the actual unstable eigenvector slope. -/
theorem c0_sq_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) :
    PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 = (a * (1 + (c / a) ^ 2) - 2) / 2 := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hn0 : ‖F • !₂[-a, -c]‖ ≠ 0 := norm_ne_zero_iff.mpr hr.shear_ne_zero
  have hn : ‖F • !₂[-a, -c]‖ ^ 2 = F ^ 2 * (a ^ 2 + c ^ 2) := by
    have hh := ViscousPropagator.plane_norm_sq (F • !₂[-a, -c])
    change ‖F • !₂[-a, -c]‖ ^ 2 = (F * -a) ^ 2 + (F * -c) ^ 2 at hh
    rw [hh]
    ring
  have he : PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 =
      -(PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) + ‖F • !₂[-a, -c]‖) /
        PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) := by
    rw [PrimaryRepresentatives.c0, div_pow, hr.lambda0_sq]
    field_simp [hr.coupling_neg.ne]
  rw [he, PrimaryRepresentatives.coupling_eq]
  change -((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖ + ‖F • !₂[-a, -c]‖) /
      ((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖) = _
  field_simp [hF.ne', ha.ne', hn0]
  nlinarith [hn]

/-- Projection of the actual stress coordinates onto the normal. -/
theorem stress_inner_normal (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(τ * F * a / ‖F • !₂[-a, -c]‖) *
        (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) := by
  have he : a * (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) =
      a * p₁ + c * p₂ - a ^ 2 - c ^ 2 := by
    field_simp; ring
  calc
    _ = -(τ * F / ‖F • !₂[-a, -c]‖) *
        (a * p₁ + c * p₂ - a ^ 2 - c ^ 2) := by
      simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

/-- Projection onto the fixed transverse orientation `-quarterTurn N`. -/
theorem stress_inner_transverse (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (τ * F * a / ‖F • !₂[-a, -c]‖) * (p₂ - p₁ * (c / a)) := by
  have he : a * (p₂ - p₁ * (c / a)) = a * p₂ - c * p₁ := by
    field_simp
  calc
    _ = (τ * F / ‖F • !₂[-a, -c]‖) * (a * p₂ - c * p₁) := by
      simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
        MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

private theorem cancel_signed_scale (q k j d : ℝ) (hk : k ≠ 0) :
    q * (k * j) / (-k * d) = -(q * j / d) := by
  rw [neg_mul, div_neg]
  congr 1
  calc
    q * (k * j) / (k * d) = k * (q * j) / (k * d) := by ring
    _ = _ := mul_div_mul_left _ _ hk

/-- The true profile cone implies both primary cones, without assuming
an eigenvector or target-cone inequality. -/
theorem spectral_cones_of_trueCone {F τ p₁ p₂ a c : ℝ} (hF : 0 < F) (hτ : 0 < τ)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) ∧
      PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) (τ • !₂[p₁ - a, p₂ - c]) := by
  have hr := referenceCone_of_trueCone hF h
  have hq := (ConeAlgebra.true_cone_iff h.2.1).mp h.2.2
  have hn := norm_pos_iff.mpr hr.shear_ne_zero
  have hk : 0 < τ * F * a / ‖F • !₂[-a, -c]‖ :=
    div_pos (mul_pos (mul_pos hτ hF) h.1) hn
  have hd : 0 < p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := sub_pos.mpr hq.1
  have hc := c0_sq_signedShear hF h.1 h.2.1
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))) ^ 2 <
      (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) ^ 2 := by
    rw [mul_pow, hc]
    nlinarith [hq.2]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))| <
      p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a)))]
  refine ⟨hr, ⟨?_, ?_⟩⟩
  · rw [stress_inner_normal F τ p₁ p₂ a c h.1.ne']
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hd
  · rw [PrimaryRepresentatives.targetRatio, stress_inner_normal F τ p₁ p₂ a c h.1.ne',
      stress_inner_transverse F τ p₁ p₂ a c h.1.ne']
    rw [cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hd]
    exact (div_lt_one hd).mpr habs

theorem stress_coordinates_ne_zero {p₁ p₂ a c : ℝ}
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) : (!₂[p₁ - a, p₂ - c] : Plane) ≠ 0 := by
  have ht := (spectral_cones_of_trueCone (F := 1) (τ := 1) (by norm_num) (by norm_num) h).2
  intro hz
  simpa only [one_smul, hz, inner_zero_left, lt_self_iff_false] using ht.inward

/-- A scalar criterion for any direction, including a nonzero smooth
edge factor when the actual stress itself vanishes. -/
theorem targetCone_of_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane)
    (hin : 0 < a * T 0 + c * T 1)
    (hquad : (a * (1 + (c / a) ^ 2) - 2) * (a * T 1 - c * T 0) ^ 2 <
      2 * (a * T 0 + c * T 1) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hk : 0 < F / ‖F • !₂[-a, -c]‖ :=
    div_pos hF (norm_pos_iff.mpr hr.shear_ne_zero)
  have hN : ⟪T, PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(F / ‖F • !₂[-a, -c]‖) * (a * T 0 + c * T 1) := by
    simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hK : ⟪T, PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (F / ‖F • !₂[-a, -c]‖) * (a * T 1 - c * T 0) := by
    simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
      MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)) ^ 2 <
      (a * T 0 + c * T 1) ^ 2 := by
    rw [mul_pow, c0_sq_signedShear hF ha hv]
    nlinarith only [hquad]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)| <
      a * T 0 + c * T 1 := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0))]
  constructor
  · rw [hN]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hin
  · rw [PrimaryRepresentatives.targetRatio, hN, hK,
      cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hin]
    exact (div_lt_one hin).mpr habs

/-- The edge-collar convention uses the target tilt `T₁ / T₀` and the
signed shear tilt `c / a`. Its two strict scalar margins imply the
primary target cone. -/
theorem targetCone_of_tilt {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane) (hT : 0 < T 0)
    (hin : 0 < 1 + (c / a) * (T 1 / T 0))
    (hgap : 0 < 2 * (1 + (c / a) * (T 1 / T 0)) ^ 2 -
      (a * (1 + (c / a) ^ 2) - 2) * (T 1 / T 0 - c / a) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have hi : a * T 0 + c * T 1 = a * T 0 * (1 + (c / a) * (T 1 / T 0)) := by
    field_simp [ha.ne', hT.ne']
  have ht : a * T 1 - c * T 0 = a * T 0 * (T 1 / T 0 - c / a) := by
    field_simp [ha.ne', hT.ne']
  apply targetCone_of_signedShear hF ha hv T
  · rw [hi]
    exact mul_pos (mul_pos ha hT) hin
  · rw [hi, ht]
    have hm := mul_pos (sq_pos_of_pos (mul_pos ha hT)) hgap
    nlinarith only [hm]

/-! ## The actual profile histories and stresses -/

open ProfileHistories

/-- The two actual leading stress coefficients, in the Euclidean plane
used by the primary ODE. -/
noncomputable def stressVector {D : RadialDomain} (P : Profiles D) (h : ℝ)
    (p : Point) : Plane := !₂[LeadingStress.theta P h p, LeadingStress.axial P h p]

/-- Both entries use the actual integral-history stocks; the axial sign
agrees with the modulation convention. -/
theorem stressVector_eq_stocks {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stressVector P h p = P.f p •
      !₂[ActivationStocks.profileStockOne P h p - ModulatedCone.angularShear P.E p,
        ActivationStocks.profileStockTwo P h p - ModulatedCone.signedAxialShear P.E P.U p] := by
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  ext i
  fin_cases i
  · change LeadingStress.theta P h p = P.f p * _
    rw [LeadingStress.theta_eq_lag_minus_slope P h hf, hs.1]
    rfl
  · change LeadingStress.axial P h p = P.f p * _
    rw [LeadingStress.axial_eq_lag_plus_slope P h hX hf, hs.2]
    unfold ActivationStocks.profileStockTwo LeadingStress.slopeB ActivationContinuation.shearB
    change P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) +
      2 * p.1 * radialPartial P.U p / P.E p) =
      P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) -
        -2 * p.1 * radialPartial P.U p / P.E p)
    ring

/-- The actual leading stress belongs to the primary target cone whenever
the actual five-history profile has the true cone. -/
theorem profile_spectral_cones {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : 0 < P.f p) {F : ℝ} (hF : 0 < F)
    (hc : TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne P h p)
      (ActivationStocks.profileStockTwo P h p) (ModulatedCone.angularShear P.E p)
      (ModulatedCone.signedAxialShear P.E P.U p)) :
    PrimaryRepresentatives.ReferenceCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p]) ∧
      PrimaryRepresentatives.TargetCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p])
        (stressVector P h p) := by
  rw [stressVector_eq_stocks P h hp hX hf.ne']
  exact spectral_cones_of_trueCone hF hf hc

theorem profile_stress_ne_zero {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : 0 < P.f p)
    (hc : TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne P h p)
      (ActivationStocks.profileStockTwo P h p) (ModulatedCone.angularShear P.E p)
      (ModulatedCone.signedAxialShear P.E P.U p)) : stressVector P h p ≠ 0 := by
  have ht := (profile_spectral_cones P h hp hX hf (F := 1) (by norm_num) hc).2
  intro hz
  simpa only [hz, inner_zero_left, lt_self_iff_false] using ht.inward

/-! ## Genuine radial derivatives of the normalized leading fields -/

theorem normalizedCoordinates_radial (h : ℝ) (p : Slow) (R : ℝ) :
    BaseChartJets.normalizedCoordinates h (R, p.2) =
      ((BaseChartJets.normalizedCoordinates h p).1,
        ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
  simp only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartQ,
    SimilarityHomogeneity.chartX, SimilarityHomogeneity.chartEta,
    SimilarityCoordinates.coordinateX]

private theorem slowR_hasDerivAt {f : Slow → ℝ} {p : Slow}
    (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun R => f (R, p.2)) (PhaseCalculus.slowR f p) p.1 :=
  hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

private theorem radial_composition_hasDerivAt {f : Point → ℝ} {rho eta R : ℝ}
    (hf : DifferentiableAt ℝ f ((R ^ 2 / 2) / rho, eta)) :
    HasDerivAt (fun r => f ((r ^ 2 / 2) / rho, eta))
      (R / rho * SimilarityProfile.partialX f ((R ^ 2 / 2) / rho, eta)) R := by
  have hx : HasDerivAt (fun r : ℝ => (r ^ 2 / 2) / rho) (R / rho) R := by
    convert! (((hasDerivAt_id R).pow 2).div_const 2).div_const rho using 1
    simp
  convert! (LeadingStress.partialX_hasDerivAt hf).comp R hx using 1
  ring

theorem leadingFrequency_germ {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseChartJets.leadingFrequency h C d =ᶠ[𝓝 p]
      (fun q => (BaseChartJets.normalizedCoordinates h q).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 (BaseChartJets.normalizedCoordinates h q).2) := by
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hR),
    continuous_snd.snd.continuousAt.eventually (Ioi_mem_nhds hT)] with q hqR hqT
  exact BaseChartJets.leadingFrequency_eq hh hh1 hqT hqR

theorem leadingFrequency_smoothAt {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingFrequency h C d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (((hs.fst.rpow_const_of_ne hn.ne').div_const C).mul
    ((hd.phi 0).contDiffAt.comp p hs.snd)).congr_of_eventuallyEq
      (leadingFrequency_germ hh hh1 hT hR)

theorem leadingAxial_smoothAt {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingAxial h d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (hs.fst.rpow_const_of_ne hn.ne').mul ((hd.axial 0).contDiffAt.comp p hs.snd)

/-- This is the Fréchet radial derivative of the actual leading angular
frequency, with all chart scale factors retained. -/
theorem leadingFrequency_slowR {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.phi 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.phi 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C)
  have he : (fun R => BaseChartJets.leadingFrequency h C d (R, p.2)) =ᶠ[𝓝 p.1]
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    filter_upwards [Ioi_mem_nhds hR] with R hRp
    rw [BaseChartJets.leadingFrequency_eq (p := (R, p.2)) hh hh1 hT hRp,
      normalizedCoordinates_radial]
  rw [← hp] at hr
  exact (slowR_hasDerivAt ((leadingFrequency_smoothAt hh hh1 hd hT hR).differentiableAt
    (by simp))).unique (hr.congr_of_eventuallyEq he)

theorem leadingAxial_slowR {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.axial 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.axial 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h))
  have he : (fun R => BaseChartJets.leadingAxial h d (R, p.2)) =
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        d.axial 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    funext R
    simp only [BaseChartJets.leadingAxial, BaseChartJets.axialFactor, normalizedCoordinates_radial]
  rw [← hp] at hr
  rw [← he] at hr
  exact (slowR_hasDerivAt ((leadingAxial_smoothAt hh hh1 hd hT).differentiableAt
    (by simp))).unique hr

theorem normalized_X_eq (h : ℝ) (p : Slow) :
    (BaseChartJets.normalizedCoordinates h p).2.1 =
      p.1 ^ 2 / (2 * (BaseChartJets.normalizedCoordinates h p).1) := by
  rw [BaseChartJets.normalizedCoordinates_eq]
  unfold SimilarityHomogeneity.chartX SimilarityCoordinates.coordinateX
    SimilarityHomogeneity.chartQ
  ring

theorem normalized_X_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < (BaseChartJets.normalizedCoordinates h p).2.1 := by
  rw [normalized_X_eq]
  exact div_pos (sq_pos_of_pos hR)
    (mul_pos (by norm_num) (BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT))

/-- Value and radial-germ agreement with a profile suffice to identify the
genuine shear vector of the coefficient-defined leading fields. -/
theorem leading_shear_eq_profile {D : RadialDomain} (P : Profiles D)
    {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hC : C ≠ 0) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hp : (BaseChartJets.normalizedCoordinates h p).2 ∈ D.carrier)
    (hf : P.f (BaseChartJets.normalizedCoordinates h p).2 ≠ 0)
    (hphi : (fun X => d.phi 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2))
      =ᶠ[𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => C * P.f (X, (BaseChartJets.normalizedCoordinates h p).2.2)))
    (hU : (fun X => d.axial 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2))
      =ᶠ[𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => P.U (X, (BaseChartJets.normalizedCoordinates h p).2.2))) :
    PhaseEstimates.shearVector (BaseChartJets.leadingFrequency h C d) (BaseChartJets.leadingAxial h
        d) p =
      BaseChartJets.leadingFrequency h C d p •
        !₂[-ModulatedCone.angularShear P.E (BaseChartJets.normalizedCoordinates h p).2,
          -ModulatedCone.signedAxialShear P.E P.U (BaseChartJets.normalizedCoordinates h p).2] := by
  let w := (BaseChartJets.normalizedCoordinates h p).2
  let rho := (BaseChartJets.normalizedCoordinates h p).1
  have hrho : 0 < rho := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  have hX : 0 < w.1 := normalized_X_pos hh hh1 hT hR
  have hphi0 : d.phi 0 w = C * P.f w := hphi.eq_of_nhds
  have hfx := LeadingStress.partialX_hasDerivAt
    ((P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hux := LeadingStress.partialX_hasDerivAt
    ((P.U_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hphiX : SimilarityProfile.partialX (d.phi 0) w = C * SimilarityProfile.partialX P.f w :=
    (LeadingStress.partialX_hasDerivAt ((hd.phi 0).differentiable (by simp) w)).unique
      ((hfx.const_mul C).congr_of_eventuallyEq hphi)
  have hUX : SimilarityProfile.partialX (d.axial 0) w = SimilarityProfile.partialX P.U w :=
    (LeadingStress.partialX_hasDerivAt ((hd.axial 0).differentiable (by simp) w)).unique
      (hux.congr_of_eventuallyEq hU)
  have hF : BaseChartJets.leadingFrequency h C d p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w := by
    rw [BaseChartJets.leadingFrequency_eq hh hh1 hT hR, hphi0]
    dsimp only [rho]
    field_simp
  have hFX : PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * SimilarityProfile.partialX P.f w) := by
    rw [leadingFrequency_slowR hh hh1 hd hT hR, hphiX]
    dsimp only [rho]
    field_simp
  have hGX : PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * SimilarityProfile.partialX P.U w) := by
    rw [leadingAxial_slowR hh hh1 hd hT, hUX]
  have hw : w.1 = p.1 ^ 2 / (2 * rho) := normalized_X_eq h p
  have hsqrt : Real.sqrt (2 * w.1) = p.1 / Real.sqrt rho := by
    have he : 2 * w.1 = p.1 ^ 2 / rho := by rw [hw]; ring
    rw [he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hR.le]
  have hpow : rho ^ (-CoordinateAlgebra.A h - 1 / 2) =
      rho ^ (-CoordinateAlgebra.A h) / Real.sqrt rho := by
    rw [Real.rpow_sub hrho, Real.sqrt_eq_rpow]
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  rw [hs.1, hs.2]
  ext i
  fin_cases i
  · change p.1 * PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearA P w)
    rw [hFX, hF]
    unfold ActivationContinuation.shearA
    change p.1 * (rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * radialPartial P.f w)) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w * (-(-2 * w.1 * radialPartial P.f w / P.f w))
    rw [hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne']
  · change PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearB P w)
    rw [hGX, hF]
    unfold ActivationContinuation.shearB Profiles.E
    change rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * radialPartial P.U w) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w *
        (-(-2 * w.1 * radialPartial P.U w / (Real.sqrt (2 * w.1) * P.f w)))
    rw [hpow, hsqrt, hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne', hR.ne', (Real.sqrt_pos.mpr hrho).ne']

/-! ## Uniform choices on a compact reference set -/

theorem signedShear_continuousOn {K : Set Slow} {F a c : Slow → ℝ}
    (hF : ContinuousOn F K) (ha : ContinuousOn a K) (hc : ContinuousOn c K) :
    ContinuousOn (fun p => F p • !₂[-a p, -c p]) K := by
  apply hF.smul
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  change ContinuousOn (fun p => (![-a p, -c p] : Fin 2 → ℝ)) K
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact ha.neg
  · exact hc.neg

/-- Scalar shear and direction margins on a compact set produce all
reference bounds and one mixed-point target margin. All constants are
chosen before a band or label is selected. `T` can be an extended edge
direction: no positive lower bound for a separate amplitude is used. -/
theorem compact_signedShear_bounds {K : Set Slow} (hK : IsCompact K)
    {F a c : Slow → ℝ} {T : Slow → Plane}
    (hF : ContinuousOn F K) (ha : ContinuousOn a K) (hc : ContinuousOn c K)
    (hT : ContinuousOn T K) (hR : ∀ p ∈ K, 0 < p.1)
    (hFp : ∀ p ∈ K, 0 < F p) (hap : ∀ p ∈ K, 0 < a p)
    (hv : ∀ p ∈ K, 2 < a p * (1 + (c p / a p) ^ 2))
    (hin : ∀ p ∈ K, 0 < a p * T p 0 + c p * T p 1)
    (hquad : ∀ p ∈ K, (a p * (1 + (c p / a p) ^ 2) - 2) *
      (a p * T p 1 - c p * T p 0) ^ 2 < 2 * (a p * T p 0 + c p * T p 1) ^ 2) :
    ∃ M u eta delta : ℝ, 1 ≤ M ∧ 0 < u ∧ 0 < eta ∧ 0 < delta ∧
      (∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (F p) (F p • !₂[-a p, -c p]) ∧
        PrimaryRepresentatives.TargetCone (F p) (F p • !₂[-a p, -c p]) (T p) ∧
        PrimaryRepresentatives.ParameterBounds M p.1 (F p) (F p • !₂[-a p, -c p])) ∧
      ∀ p₀ ∈ K, ∀ p ∈ K, dist p p₀ < delta →
        ⟪T p, PrimaryRepresentatives.normalDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ ≤ -eta ∧
        |PrimaryRepresentatives.c0 (F p₀) (F p₀ • !₂[-a p₀, -c p₀]) *
          ⟪T p, PrimaryRepresentatives.transverseDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ /
          ⟪T p, PrimaryRepresentatives.normalDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ| + eta ≤
          PrimaryRepresentatives.slopeRatio u := by
  have hRef : ∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (F p) (F p • !₂[-a p, -c p]) := by
    intro p hp
    apply PrimaryRepresentatives.referenceCone_of_shear_coordinates (hFp p hp) (hap p hp)
    have he := shear_size_mul (c := c p) (hap p hp).ne'
    have hm := mul_lt_mul_of_pos_left (hv p hp) (hap p hp)
    nlinarith
  have hTar : ∀ p ∈ K, PrimaryRepresentatives.TargetCone (F p) (F p • !₂[-a p, -c p]) (T p) :=
    fun p hp => targetCone_of_signedShear (hFp p hp) (hap p hp) (hv p hp) (T p)
      (hin p hp) (hquad p hp)
  have hg := signedShear_continuousOn hF ha hc
  obtain ⟨M, hM, hMb⟩ := PrimaryRepresentatives.compact_parameter_bounds hK hF hg hR hRef
  obtain ⟨u, eta, delta, hu, he, hd, hb⟩ :=
    PrimaryRepresentatives.compact_mixed_target_margin hK hF hg hT hRef hTar
  exact ⟨M, u, eta, delta, hM, hu, he, hd,
    fun p hp => ⟨hRef p hp, hTar p hp, hMb p hp⟩, hb⟩

/-- A vanishing nonnegative amplitude preserves the linear inward
margin; where it is positive it cancels exactly from the target ratio. -/
theorem weighted_target_margin {F eta u zeta : ℝ} {g T : Plane}
    (hz : 0 ≤ zeta)
    (hin : ⟪T, PrimaryRepresentatives.normalDirection g⟫_ℝ ≤ -eta)
    (hratio : PrimaryRepresentatives.targetRatio F g T + eta ≤ PrimaryRepresentatives.slopeRatio u)
        :
    ⟪zeta • T, PrimaryRepresentatives.normalDirection g⟫_ℝ ≤ -eta * zeta ∧
      (0 < zeta → PrimaryRepresentatives.targetRatio F g (zeta • T) + eta ≤
        PrimaryRepresentatives.slopeRatio u) := by
  constructor
  · rw [real_inner_smul_left]
    simpa only [mul_comm zeta (-eta)] using mul_le_mul_of_nonneg_left hin hz
  · intro hz'
    rw [PrimaryRepresentatives.targetRatio_smul F g T hz'.ne']
    exact hratio

end NavierStokes.ProfileSpectralCone

end
end

end
