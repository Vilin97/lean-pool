/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularAuxiliary
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.NominalProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReservedPatches
public import LeanPool.NavierStokesAndEuler.NavierStokes.NominalConeAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.AssembledSlowBase

@[expose] public section

/-!
# Modulation of one actual nominal profile

The regular fields `f,U` are extended from the closed positive half-plane
without changing them there.  Consequently their actual histories from the
axis, including the pressure constant, are preserved.  The separate angular
field used by the periodic-loop construction is clamped only away from the
modulation annulus.  Finally only the supported edits are transplanted back
to the original nominal profile.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff
open NavierStokes.ProfileHistories

namespace NavierStokes.ModulatedProfileAssembly


/-- Restrict parameters without changing any radial segment or any field. -/
noncomputable def restrictDomain (D : RadialDomain) (S : Set ℝ) (hS : IsOpen S) :
    RadialDomain where
  carrier := D.carrier ∩ (univ ×ˢ S)
  isOpen := D.isOpen.inter (isOpen_univ.prod hS)
  scale_mem := fun p hp t ht => ⟨D.scale_mem p hp.1 t ht, mem_univ _, hp.2.2⟩

theorem rows_eq_of_nonnegative {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (h0 : P.pressure0 = Q.pressure0) {X eta : ℝ} (hX : 0 ≤ X)
    (hf : ∀ x ∈ Icc (0 : ℝ) X, P.f (x, eta) = Q.f (x, eta))
    (hu : ∀ x ∈ Icc (0 : ℝ) X, P.U (x, eta) = Q.U (x, eta)) :
    ModulatedHistories.profileRows P (X, eta) = ModulatedHistories.profileRows Q (X, eta) := by
  rw [ModulatedHistories.profileRows_eq_axisHistory, ModulatedHistories.profileRows_eq_axisHistory,
    h0]
  congr 1
  unfold ModulatedHistories.axisHistory
  funext i
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hX] at hx
  simp only [ModulatedHistories.density, hf x hx, hu x hx]

theorem histories_eq_of_nonnegative {D D' : RadialDomain}
    (P : Profiles D) (Q : Profiles D') (h0 : P.pressure0 = Q.pressure0)
    {X eta : ℝ} (hX : 0 ≤ X)
    (hf : ∀ x ∈ Icc (0 : ℝ) X, P.f (x, eta) = Q.f (x, eta))
    (hu : ∀ x ∈ Icc (0 : ℝ) X, P.U (x, eta) = Q.U (x, eta))
    (r : StressActivation.HistoryRow) :
    StressActivation.profileHistory P r (X, eta) =
      StressActivation.profileHistory Q r (X, eta) := by
  apply ActivationStocks.profileHistory_congr_across P Q r hX _ hf hu
  cases r <;> simp only [StressActivation.profileInitial, h0]

/-- This is genuine available domain data of a fixed nominal witness. -/
structure ParameterData {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) where
  parameters : Set ℝ
  isOpen : IsOpen parameters
  contains : Icc (-1 : ℝ) 1 ⊆ parameters
  nonnegative : ∀ X : ℝ, 0 ≤ X → ∀ eta ∈ parameters, (X, eta) ∈ W.domain.carrier

theorem exists_parameterData {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    Nonempty (ParameterData W) := by
  obtain ⟨a, ha, _, hd⟩ := W.exists_parameter_interval
  exact ⟨⟨Ioo (-a) a, isOpen_Ioo, by
    intro eta heta
    constructor <;> linarith [heta.1, heta.2], hd⟩⟩

namespace ParameterData

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F} (d : ParameterData W)

noncomputable def window : ParametricRadialExtension.ParameterWindow d.parameters :=
  ParametricRadialExtension.parameterWindow d.isOpen d.contains

noncomputable def target : Set ℝ := Ioo (-d.window.inner) d.window.inner

theorem target_open : IsOpen d.target := isOpen_Ioo

theorem target_contains : Icc (-1 : ℝ) 1 ⊆ d.target := d.window.unit_subset

theorem target_subset : d.target ⊆ d.parameters := d.window.target_subset

noncomputable def parameterized (f : Field) (p : Point) : ℝ :=
  f (p.1, d.window.parameterMap p.2)

theorem parameterized_smooth {f : Field} (hf : ContDiffOn ℝ ∞ f W.domain.carrier) :
    ContDiffOn ℝ ∞ (d.parameterized f) (Ici 0 ×ˢ (univ : Set ℝ)) := by
  apply hf.comp (contDiff_fst.prodMk
    (d.window.parameterMap_contDiff.comp contDiff_snd)).contDiffOn
  intro p hp
  exact d.nonnegative p.1 hp.1 _ (d.window.parameterMap_mem p.2)

noncomputable def extended (f : Field) (hf : ContDiffOn ℝ ∞ f W.domain.carrier) : Field :=
  ParametricRadialExtension.halfPlaneExtension (d.parameterized f) (d.parameterized_smooth hf)

theorem extended_smooth (f : Field) (hf : ContDiffOn ℝ ∞ f W.domain.carrier) :
    ContDiff ℝ ∞ (d.extended f hf) := ParametricRadialExtension.halfPlaneExtension_contDiff _

theorem extended_eq (f : Field) (hf : ContDiffOn ℝ ∞ f W.domain.carrier)
    {p : Point} (hX : 0 ≤ p.1) (heta : |p.2| ≤ d.window.inner) :
    d.extended f hf p = f p := by
  rw [extended, ParametricRadialExtension.halfPlaneExtension_eq _ hX]
  simp only [parameterized, d.window.parameterMap_eq heta, Prod.eta]

theorem extended_germ (f : Field) (hf : ContDiffOn ℝ ∞ f W.domain.carrier)
    {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ d.target) :
    d.extended f hf =ᶠ[𝓝 p] f := by
  filter_upwards [(isOpen_Ioi.prod d.target_open).mem_nhds ⟨hX, heta⟩] with q hq
  exact d.extended_eq f hf hq.1.le (abs_lt.mpr hq.2).le

noncomputable def f : Field := d.extended W.profiles.f W.profiles.f_smooth
noncomputable def U : Field := d.extended W.profiles.U W.profiles.U_smooth

theorem f_smooth : ContDiff ℝ ∞ d.f := d.extended_smooth _ _
theorem U_smooth : ContDiff ℝ ∞ d.U := d.extended_smooth _ _

theorem fields_eq {p : Point} (hX : 0 ≤ p.1) (heta : p.2 ∈ d.target) :
    d.f p = W.profiles.f p ∧ d.U p = W.profiles.U p :=
  ⟨d.extended_eq _ _ hX (abs_lt.mpr heta).le,
    d.extended_eq _ _ hX (abs_lt.mpr heta).le⟩

noncomputable def profiles : Profiles (ModulatedHistories.stripDomain univ isOpen_univ) :=
  ModulatedHistories.profiles univ isOpen_univ d.f d.U F.axisDatum d.f_smooth.contDiffOn
    d.U_smooth.contDiffOn
    F.axisDatum_contDiff.contDiffOn

theorem pressure0_eq : d.profiles.pressure0 = W.profiles.pressure0 := rfl

/-- These are absolute histories, not the histories of a radially clamped field. -/
theorem rows_eq {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ d.target) :
    ModulatedHistories.profileRows d.profiles (X, eta) = ModulatedHistories.profileRows W.profiles
      (X, eta) := by
  exact rows_eq_of_nonnegative d.profiles W.profiles rfl hX
    (fun _ hx => (d.fields_eq hx.1 heta).1) (fun _ hx => (d.fields_eq hx.1 heta).2)

theorem histories_eq {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ d.target)
    (r : StressActivation.HistoryRow) :
    StressActivation.profileHistory d.profiles r (X, eta) =
      StressActivation.profileHistory W.profiles r (X, eta) :=
  histories_eq_of_nonnegative d.profiles W.profiles rfl hX
    (fun _ hx => (d.fields_eq hx.1 heta).1) (fun _ hx => (d.fields_eq hx.1 heta).2) r

theorem stocks_eq {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ d.target)
    (hf : W.profiles.f p ≠ 0) :
    ActivationStocks.profileStockOne d.profiles F.data.h p =
        ActivationStocks.profileStockOne W.profiles F.data.h p ∧
      ActivationStocks.profileStockTwo d.profiles F.data.h p =
        ActivationStocks.profileStockTwo W.profiles F.data.h p := by
  exact ActivationStocks.profiles_stocks_congr d.profiles W.profiles F.data.h
    d.target_open heta ⟨mem_univ _, mem_univ _⟩
    (d.nonnegative p.1 hX.le _ (d.target_subset heta)) hX
    (d.fields_eq hX.le heta).1 hf (d.fields_eq hX.le heta).2
    (fun r eta he => d.histories_eq hX.le he r)

/-- Clamp only the auxiliary angular field. The history-bearing `f,U`
above are unchanged on the entire positive half-plane. -/
noncomputable def E (a : ℝ) (p : Point) : ℝ :=
  Real.sqrt (2 * AnnularAuxiliary.positiveMap a p.1) *
    d.f (AnnularAuxiliary.positiveMap a p.1, p.2)

theorem E_smooth {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (d.E a) := by
  have hm : ContDiff ℝ ∞ (fun p : Point => AnnularAuxiliary.positiveMap a p.1) :=
    (AnnularAuxiliary.positiveMap_contDiff a).comp contDiff_fst
  exact ((contDiff_const.mul hm).sqrt (fun p => by
    exact ne_of_gt (mul_pos (by norm_num) (AnnularAuxiliary.positiveMap_pos ha p.1)))).mul
    (d.f_smooth.comp (hm.prodMk contDiff_snd))

theorem E_eq {a : ℝ} (ha : 0 < a) {p : Point} (hX : a ≤ p.1) :
    d.E a p = d.profiles.E p := by
  simp only [E, AnnularAuxiliary.positiveMap_eq ha hX, Profiles.E, profiles,
    ModulatedHistories.profiles, Prod.eta]

theorem E_germ {a : ℝ} (ha : 0 < a) {p : Point} (hX : a < p.1) :
    d.E a =ᶠ[𝓝 p] d.profiles.E := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hX] with q hq
  exact d.E_eq ha hq.le

theorem E_nominal_germ {a : ℝ} (ha : 0 < a) {p : Point} (hX : a < p.1)
    (heta : p.2 ∈ d.target) : d.E a =ᶠ[𝓝 p] W.profiles.E := by
  filter_upwards [d.E_germ ha hX, d.extended_germ W.profiles.f W.profiles.f_smooth
    (ha.trans hX) heta] with q hq hf
  exact hq.trans (congrArg (fun z => Real.sqrt (2 * q.1) * z) hf)

end ParameterData

/-- The first reserved five-row patch, belonging to the very same outgoing
schedule and physical dilation as the nominal witness. -/
noncomputable def repairPatch {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    FiveProfileMoments.Patch :=
  ReservedPatches.momentPatch F W.controls.radius W.controls.radius_pos .modulation

theorem repairPatch_before_positive {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    (repairPatch W).right < ReservedPatches.left F W.controls.radius .positive := by
  have hm := (ReservedPatches.support_margins F W.controls.radius W.controls.radius_pos
    .modulation).2.2
  have hh : ReservedPatches.right F W.controls.radius .modulation <
      ReservedPatches.left F W.controls.radius .positive := by
    apply ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos
    simp only [ReservedPatches.rightClock, ReservedPatches.leftClock,
      ReservedPatches.rightOffset, ReservedPatches.leftOffset]
    linarith
  exact hm.trans hh

theorem nominal_patch_fields {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (eta : ℝ) {X : ℝ} (hX : X ∈ Ioo (repairPatch W).left (repairPatch W).right) :
    W.profiles.U (X, eta) = 0 ∧ W.profiles.E (X, eta) =
      ReservedPatches.xAmplitude F W.controls.radius eta * X ^ (-1 / 2 - F.data.core.lam) := by
  have hw : X ∈ ReservedPatches.window F W.controls.radius .modulation :=
    ReservedPatches.closedPatch_subset F W.controls.radius W.controls.radius_pos .modulation
      ⟨hX.1.le, hX.2.le⟩
  have hr : W.controls.radius < ReservedPatches.left F W.controls.radius .modulation := by
    have hh := F.data.core.holdStart_pos.trans
      (ReservedPatches.clock_inside_wait F .modulation).1
    simpa only [ReservedPatches.left, OutgoingDilation.radius, Real.exp_zero, mul_one] using
      ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hh
  have hrX : W.controls.radius < X := hr.trans hw.1
  have hpatch : X ≤ OutgoingDilation.patchRadius F W.controls.radius := by
    have hh : ReservedPatches.right F W.controls.radius .modulation =
        ReservedPatches.left F W.controls.radius .heat := by
      simp only [ReservedPatches.right, ReservedPatches.left, ReservedPatches.rightClock,
        ReservedPatches.leftClock, ReservedPatches.rightOffset, ReservedPatches.leftOffset]
    rw [← ReservedPatches.heat_left, ← hh]
    exact hw.2.le
  obtain ⟨hu, he⟩ := ReservedPatches.clean_fields F W.controls.radius W.controls.radius_pos
    .modulation eta hw
  constructor
  · exact (W.U_outgoing (W.controls.heatJoin_lt_radius.trans hrX)).trans hu
  · have hpos : 0 < X := W.controls.radius_pos.trans hrX
    change Real.sqrt (2 * X) * W.f (X, eta) = _
    rw [← W.E_eq_sqrt_f (p := (X, eta)) hpos,
      W.E_outgoing_before_patch hrX.le hpatch, he]
    congr 2
    ring

/-- The original nominal profile plus a supported difference. Its axis
pressure is retained literally. -/
noncomputable def transplantProfiles {D D' : RadialDomain} (Q : Profiles D)
    (R : Profiles D') (f U : Field) (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsOpen S)
    (hD : (restrictDomain D S hS).carrier ⊆ D'.carrier) :
    Profiles (restrictDomain D S hS) where
  f := AnnularAuxiliary.transplant Q.f f R.f
  U := AnnularAuxiliary.transplant Q.U U R.U
  f_smooth := (Q.f_smooth.mono inter_subset_left).add
    ((R.f_smooth.mono hD).sub hf.contDiffOn)
  U_smooth := (Q.U_smooth.mono inter_subset_left).add
    ((R.U_smooth.mono hD).sub hU.contDiffOn)
  pressure0 := Q.pressure0
  pressure0_smooth := fun _ hp => Q.pressure0_smooth _ hp.1

theorem transplantProfiles_fields {D D' : RadialDomain} (Q : Profiles D)
    (R : Profiles D') (f U : Field) (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsOpen S) (hD : (restrictDomain D S hS).carrier ⊆ D'.carrier)
    {p : Point} (hfp : f p = Q.f p) (hUp : U p = Q.U p) :
    (transplantProfiles Q R f U hf hU S hS hD).f p = R.f p ∧
      (transplantProfiles Q R f U hf hU S hS hD).U p = R.U p :=
  ⟨AnnularAuxiliary.transplant_inside hfp.symm,
    AnnularAuxiliary.transplant_inside hUp.symm⟩

noncomputable def band (a : ℝ) : Set ℝ := Icc (-a) a

noncomputable def modulationRegion (v : ModulatedHistories.Window) (a : ℝ) : Set Point :=
  Icc v.left v.right ×ˢ band a

noncomputable def followingRegion {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (v : ModulatedHistories.Window) (a : ℝ) : Set Point :=
  Icc v.right (repairPatch W).right ×ˢ band a

noncomputable def fullRegion {F : OutgoingProfile.Profile}
    (W : NominalProfile.Witness F) (v : ModulatedHistories.Window) (a : ℝ) : Set Point :=
  Icc v.left (repairPatch W).right ×ˢ band a

noncomputable def boundaryRegion (v : ModulatedHistories.Window) (a : ℝ) : Set Point :=
  ({v.left, v.right} : Set ℝ) ×ˢ band a

/-- Only nominal data are premises. The loop, modulation frequency and
nonlinear repair are constructed later. Each supplied smooth coordinate is
identified with an actual stock or shear of this particular `W`. -/
structure LoopData {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) where
  parameter : ParameterData W
  etaRadius : ℝ
  one_lt_etaRadius : 1 < etaRadius
  etaRadius_lt_target : etaRadius < parameter.window.inner
  modulation : ModulatedHistories.Window
  after_initial : 4 / W.axis.scale < modulation.left
  before_repair : modulation.right < (repairPatch W).left
  a : Field
  m : Field
  p₁ : Field
  p₂ : Field
  a_smooth : ContDiff ℝ ∞ a
  m_smooth : ContDiff ℝ ∞ m
  p₁_smooth : ContDiff ℝ ∞ p₁
  p₂_smooth : ContDiff ℝ ∞ p₂
  angular_eq : ∀ p ∈ fullRegion W modulation etaRadius,
    a p = ModulatedCone.angularShear W.profiles.E p
  axial_eq : ∀ p ∈ fullRegion W modulation etaRadius,
    a p * m p = ModulatedCone.signedAxialShear W.profiles.E W.profiles.U p
  stock₁_eq : ∀ p ∈ fullRegion W modulation etaRadius,
    p₁ p = ActivationStocks.profileStockOne W.profiles F.data.h p
  stock₂_eq : ∀ p ∈ fullRegion W modulation etaRadius,
    p₂ p = ActivationStocks.profileStockTwo W.profiles F.data.h p
  positive_f : ∀ p ∈ fullRegion W modulation etaRadius, 0 < W.profiles.f p
  positive_a : ∀ p ∈ fullRegion W modulation etaRadius, 0 < a p
  nonzero_L : ∀ p ∈ fullRegion W modulation etaRadius, NaturalAxisData.L F.data.h p.2 ≠ 0
  projection : ∀ p ∈ modulationRegion modulation etaRadius, 2 < p₁ p + p₂ p * m p
  relaxed : ∀ p ∈ modulationRegion modulation etaRadius,
    TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p)
  true_boundary : ∀ p ∈ boundaryRegion modulation etaRadius,
    2 < TrueConeLoop.nominalSpeed (a p) (m p)
  true_following : ∀ p ∈ followingRegion W modulation etaRadius,
    TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p)

namespace LoopData

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F} (d : LoopData W)

noncomputable def parameters : Set ℝ := Ioo (-d.etaRadius) d.etaRadius

theorem parameters_open : IsOpen d.parameters := isOpen_Ioo

theorem parameters_contains : Icc (-1 : ℝ) 1 ⊆ d.parameters := by
  intro eta heta
  constructor <;> linarith [d.one_lt_etaRadius, heta.1, heta.2]

theorem band_target : band d.etaRadius ⊆ d.parameter.target := by
  intro eta heta
  constructor <;> linarith [d.etaRadius_lt_target, heta.1, heta.2]

theorem parameters_target : d.parameters ⊆ d.parameter.target :=
  Subset.trans Ioo_subset_Icc_self d.band_target

theorem union_full : modulationRegion d.modulation d.etaRadius ∪
    followingRegion W d.modulation d.etaRadius ⊆ fullRegion W d.modulation d.etaRadius := by
  intro p hp
  rcases hp with hp | hp
  · exact ⟨⟨hp.1.1, hp.1.2.trans (d.before_repair.trans (repairPatch W).ordered).le⟩, hp.2⟩
  · exact ⟨⟨d.modulation.ordered.le.trans hp.1.1, hp.1.2⟩, hp.2⟩

theorem full_positive {p : Point} (hp : p ∈ fullRegion W d.modulation d.etaRadius) : 0 < p.1 :=
  d.modulation.left_pos.trans_le hp.1.1

theorem boundary_subset : boundaryRegion d.modulation d.etaRadius ⊆
    modulationRegion d.modulation d.etaRadius := by
  rintro p ⟨hp, he⟩
  rcases Set.mem_insert_iff.mp hp with hp | hp
  · exact ⟨⟨hp.ge, hp.le.trans d.modulation.ordered.le⟩, he⟩
  · have hp := Set.mem_singleton_iff.mp hp
    exact ⟨⟨d.modulation.ordered.le.trans hp.ge, hp.le⟩, he⟩

theorem exists_realization : Nonempty (ParametricModulation.TrueConeRealization d.a d.m d.p₁ d.p₂
    (modulationRegion d.modulation d.etaRadius) (boundaryRegion d.modulation d.etaRadius)) := by
  apply ParametricModulation.exists_trueConeRealization _ _ _ _ _ _
    (isCompact_Icc.prod isCompact_Icc)
    ((isCompact_singleton.insert _).prod isCompact_Icc)
    d.a_smooth d.m_smooth d.p₁_smooth d.p₂_smooth
    (fun p hp => d.positive_a p (d.union_full (Or.inl hp))) d.projection d.true_boundary

abbrev Realization := ParametricModulation.TrueConeRealization d.a d.m d.p₁ d.p₂
  (modulationRegion d.modulation d.etaRadius) (boundaryRegion d.modulation d.etaRadius)

noncomputable def angularAux : Field := d.parameter.E (d.modulation.left / 2)

theorem angularAux_smooth : ContDiff ℝ ∞ d.angularAux :=
  d.parameter.E_smooth (half_pos d.modulation.left_pos)

theorem auxiliary_shears {p : Point} (hp : p ∈ fullRegion W d.modulation d.etaRadius) :
    ModulatedCone.angularShear d.angularAux p = ModulatedCone.angularShear W.profiles.E p ∧
      ModulatedCone.signedAxialShear d.angularAux d.parameter.U p =
        ModulatedCone.signedAxialShear W.profiles.E W.profiles.U p := by
  have hx : d.modulation.left / 2 < p.1 := by linarith [d.modulation.left_pos, hp.1.1]
  have ht : Tendsto (fun X : ℝ => (X, p.2)) (𝓝 p.1) (𝓝 p) :=
    continuousAt_id.prodMk continuousAt_const
  exact ModulatedCone.shears_eq_of_radial_eventuallyEq
    ((d.parameter.E_nominal_germ (half_pos d.modulation.left_pos) hx
      (d.band_target hp.2)).comp_tendsto ht)
    ((d.parameter.extended_germ W.profiles.U W.profiles.U_smooth
      (d.full_positive hp) (d.band_target hp.2)).comp_tendsto ht)

noncomputable def domain : RadialDomain := restrictDomain W.domain d.parameters d.parameters_open

theorem domain_nonnegative {p : Point} (hX : 0 ≤ p.1) (heta : p.2 ∈ d.parameters) :
    p ∈ d.domain.carrier :=
  ⟨d.parameter.nonnegative p.1 hX _ (d.parameter.target_subset (d.parameters_target heta)),
    mem_univ _, heta⟩

noncomputable def outputF (r : d.Realization) (N : ℕ)
    (c : ℝ → ModulatedHistories.Coeff) : Field :=
  AnnularAuxiliary.transplant W.profiles.f d.parameter.f
    (ModulatedHistories.applyRepairF (repairPatch W)
      (ReservedPatches.xAmplitude F W.controls.radius) c
      (ModulatedHistories.localizedF d.modulation r d.parameter.f N))

noncomputable def outputU (r : d.Realization) (N : ℕ)
    (c : ℝ → ModulatedHistories.Coeff) : Field :=
  AnnularAuxiliary.transplant W.profiles.U d.parameter.U
    (ModulatedHistories.applyRepairU (repairPatch W)
      (ReservedPatches.xAmplitude F W.controls.radius) c
      (ModulatedHistories.localizedU d.modulation r d.angularAux d.parameter.U N))

theorem output_outside (r : d.Realization) (N : ℕ) (c : ℝ → ModulatedHistories.Coeff)
    {p : Point} (hp : p.1 ∉ Ioo d.modulation.left (repairPatch W).right) :
    d.outputF r N c p = W.profiles.f p ∧ d.outputU r N c p = W.profiles.U p := by
  have hpatch : p.1 ∉ Ioo (repairPatch W).left (repairPatch W).right := by
    intro hp'
    exact hp ⟨(d.modulation.ordered.trans d.before_repair).trans hp'.1, hp'.2⟩
  have hrep := ModulatedHistories.repair_preserves_outside (repairPatch W)
    (ReservedPatches.xAmplitude F W.controls.radius) c
    (ModulatedHistories.localizedF d.modulation r d.parameter.f N)
    (ModulatedHistories.localizedU d.modulation r d.angularAux d.parameter.U N) hpatch
  have hbase : ModulatedHistories.localizedF d.modulation r d.parameter.f N p = d.parameter.f p ∧
      ModulatedHistories.localizedU d.modulation r d.angularAux d.parameter.U N p = d.parameter.U p
        := by
    by_cases hlo : p.1 ≤ d.modulation.left
    · exact ⟨ModulatedHistories.splice_eq_before _ _ _ hlo,
        ModulatedHistories.splice_eq_before _ _ _ hlo⟩
    · have hhi : (repairPatch W).right ≤ p.1 := le_of_not_gt (fun hhi => hp ⟨lt_of_not_ge hlo, hhi⟩)
      have hv : d.modulation.right < p.1 :=
        (d.before_repair.trans (repairPatch W).ordered).trans_le hhi
      exact ⟨ModulatedHistories.splice_eq_after _ _ _ hv,
        ModulatedHistories.splice_eq_after _ _ _ hv⟩
  exact ⟨AnnularAuxiliary.transplant_outside (hrep.1.trans hbase.1),
    AnnularAuxiliary.transplant_outside (hrep.2.trans hbase.2)⟩

end LoopData

/-- A finite, actually solved modulation of `W`, on an open parameter
neighborhood of the complete physical band. -/
structure Witness {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (d : LoopData W) where
  realization : d.Realization
  frequency : ℕ
  frequency_pos : 0 < frequency
  coefficients : ℝ → ModulatedHistories.Coeff
  coefficients_smooth : ContDiff ℝ ∞ coefficients
  profiles : Profiles d.domain
  f_formula : profiles.f = d.outputF realization frequency coefficients
  U_formula : profiles.U = d.outputU realization frequency coefficients
  pressure0 : profiles.pressure0 = W.profiles.pressure0
  restored : ∀ eta ∈ d.parameters, ∀ X : ℝ, (repairPatch W).right ≤ X →
    ModulatedHistories.profileRows profiles (X, eta) = ModulatedHistories.profileRows W.profiles
      (X, eta)
  true_cone : ∀ p ∈ Icc d.modulation.left (repairPatch W).right ×ˢ d.parameters,
    0 < profiles.f p ∧ TrueConeLoop.InTrueCone
      (ActivationStocks.profileStockOne profiles F.data.h p)
      (ActivationStocks.profileStockTwo profiles F.data.h p)
      (ModulatedCone.angularShear profiles.E p) (ModulatedCone.signedAxialShear profiles.E
        profiles.U p)

theorem exists_witness {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (d : LoopData W) : Nonempty (Witness d) := by
  classical
  obtain ⟨r⟩ := d.exists_realization
  have hends : ∀ eta ∈ band d.etaRadius,
      (d.modulation.left, eta) ∈ boundaryRegion d.modulation d.etaRadius ∧
      (d.modulation.right, eta) ∈ boundaryRegion d.modulation d.etaRadius := by
    intro eta heta
    exact ⟨⟨by simp, heta⟩, ⟨by simp, heta⟩⟩
  obtain ⟨Ω, hΩ, hJΩ, P, hP, _⟩ := ModulatedCone.Localized.exists_profile_family
    d.modulation r d.parameter.f d.angularAux d.parameter.U F.axisDatum
    d.a_smooth d.m_smooth d.p₂_smooth d.parameter.f_smooth d.angularAux_smooth d.parameter.U_smooth
    F.axisDatum_contDiff (band d.etaRadius) d.boundary_subset hends
  have htarget : ∀ p ∈ modulationRegion d.modulation d.etaRadius ∪
      followingRegion W d.modulation d.etaRadius, p.2 ∈ d.parameter.target :=
    fun p hp => d.band_target (d.union_full hp).2
  have hphys : ∀ p ∈ modulationRegion d.modulation d.etaRadius ∪
      followingRegion W d.modulation d.etaRadius,
      d.angularAux =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * d.parameter.f q := by
    intro p hp
    apply d.parameter.E_germ (half_pos d.modulation.left_pos)
    linarith [d.modulation.left_pos, (d.union_full hp).1.1]
  have hstock (p : Point) (hp : p ∈ modulationRegion d.modulation d.etaRadius ∪
      followingRegion W d.modulation d.etaRadius) :=
    d.parameter.stocks_eq (d.full_positive (d.union_full hp)) (htarget p hp)
      (d.positive_f p (d.union_full hp)).ne'
  have hpatchU : ∀ eta ∈ band d.etaRadius, ∀ X ∈ Ioo (repairPatch W).left (repairPatch W).right,
      d.parameter.U (X, eta) = (fun _ : ℝ => (0 : ℝ)) eta := by
    intro eta heta X hX
    exact ((d.parameter.fields_eq ((repairPatch W).left_pos.trans hX.1).le
      (d.band_target heta)).2).trans (nominal_patch_fields W eta hX).1
  have hpatchE : ∀ eta ∈ band d.etaRadius, ∀ X ∈ Ioo (repairPatch W).left (repairPatch W).right,
      Real.sqrt (2 * X) * d.parameter.f (X, eta) =
        ReservedPatches.xAmplitude F W.controls.radius eta * X ^ (-1 / 2 - F.data.core.lam) := by
    intro eta heta X hX
    rw [(d.parameter.fields_eq ((repairPatch W).left_pos.trans hX.1).le (d.band_target heta)).1]
    exact (nominal_patch_fields W eta hX).2
  obtain ⟨N, c, hc, hN, hcone, hrows, _⟩ := ModulatedCone.Repaired.exists_with_moment_repair
    d.modulation r d.parameter.f d.angularAux d.parameter.U
    (isCompact_Icc.prod isCompact_Icc) (fun _ hp => hp.1)
    d.a_smooth d.m_smooth d.p₁_smooth d.p₂_smooth
    d.parameter.f_smooth d.angularAux_smooth d.parameter.U_smooth
    (fun p hp => d.positive_a p (d.union_full (Or.inl hp)))
    (followingRegion W d.modulation d.etaRadius) (isCompact_Icc.prod isCompact_Icc)
    (fun _ hp => hp.1.1)
    (fun p hp => (d.angular_eq p (d.union_full hp)).trans (d.auxiliary_shears (d.union_full
      hp)).1.symm)
    (fun p hp => (d.axial_eq p (d.union_full hp)).trans (d.auxiliary_shears (d.union_full
      hp)).2.symm)
    d.relaxed d.true_following P d.parameter.profiles
    (fun n => (hP n).1) (fun n => (hP n).2.1) rfl rfl (fun n => (hP n).2.2)
    (band d.etaRadius) isCompact_Icc (fun _ hp => (d.union_full hp).2)
    (fun _ hp => ⟨mem_univ _, hJΩ (d.union_full hp).2⟩)
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    F.data.h (fun p hp => d.nonzero_L p (d.union_full hp))
    (fun p hp => by
      change 0 < d.parameter.f p
      rw [(d.parameter.fields_eq (d.full_positive (d.union_full hp)).le (htarget p hp)).1]
      exact d.positive_f p (d.union_full hp))
    (fun p hp => (d.stock₁_eq p (d.union_full hp)).trans (hstock p hp).1.symm)
    (fun p hp => (d.stock₂_eq p (d.union_full hp)).trans (hstock p hp).2.symm)
    d.boundary_subset hends hphys (repairPatch W) d.before_repair
    (ReservedPatches.xAmplitude F W.controls.radius) (fun _ => 0)
    (ReservedPatches.xAmplitude_contDiff F W.controls.radius) contDiff_const
    (ReservedPatches.xAmplitude_pos F W.controls.radius)
    (fun _ hp => hp) (fun _ hp => hp)
    (-1 / 2 - F.data.core.lam) (FiveProfileMoments.good_outgoing _ F.data.core.lam_pos)
    hpatchU hpatchE
  let R := ModulatedCone.Repaired.profileRepair (P N) (repairPatch W)
    (ReservedPatches.xAmplitude F W.controls.radius) c
    (ReservedPatches.xAmplitude_contDiff F W.controls.radius) hc
  have hD : d.domain.carrier ⊆ (ModulatedHistories.stripDomain Ω hΩ).carrier := by
    intro p hp
    exact ⟨mem_univ _, hJΩ ⟨hp.2.2.1.le, hp.2.2.2.le⟩⟩
  let Q : Profiles d.domain := transplantProfiles W.profiles R d.parameter.f d.parameter.U
    d.parameter.f_smooth d.parameter.U_smooth d.parameters d.parameters_open hD
  have hQf : Q.f = d.outputF r N c := by
    change AnnularAuxiliary.transplant _ _
      (ModulatedHistories.applyRepairF _ _ _ (P N).f) = _
    rw [(hP N).1]
    rfl
  have hQU : Q.U = d.outputU r N c := by
    change AnnularAuxiliary.transplant _ _
      (ModulatedHistories.applyRepairU _ _ _ (P N).U) = _
    rw [(hP N).2.1]
    rfl
  have hQR : ∀ p : Point, 0 ≤ p.1 → p.2 ∈ d.parameters → Q.f p = R.f p ∧ Q.U p = R.U p := by
    intro p hx he
    exact transplantProfiles_fields W.profiles R d.parameter.f d.parameter.U
      d.parameter.f_smooth d.parameter.U_smooth d.parameters d.parameters_open hD
      (d.parameter.fields_eq hx (d.parameters_target he)).1
      (d.parameter.fields_eq hx (d.parameters_target he)).2
  have h0 : Q.pressure0 = R.pressure0 := (hP N).2.2.symm
  have hhist : ∀ X : ℝ, 0 ≤ X → ∀ eta ∈ d.parameters, ∀ row : StressActivation.HistoryRow,
      StressActivation.profileHistory Q row (X, eta) = StressActivation.profileHistory R row (X,
        eta) := by
    intro X hx eta he row
    exact histories_eq_of_nonnegative Q R h0 hx (fun _ hx => (hQR _ hx.1 he).1)
      (fun _ hx => (hQR _ hx.1 he).2) row
  refine ⟨⟨r, N, hN, c, hc, Q, hQf, hQU, rfl, ?_, ?_⟩⟩
  · intro eta he X hx
    have hXp : 0 ≤ X := (repairPatch W).left_pos.le.trans ((repairPatch W).ordered.le.trans hx)
    calc
      ModulatedHistories.profileRows Q (X, eta) = ModulatedHistories.profileRows R (X, eta) :=
        rows_eq_of_nonnegative Q R h0 hXp (fun _ hx => (hQR _ hx.1 he).1)
          (fun _ hx => (hQR _ hx.1 he).2)
      _ = ModulatedHistories.profileRows d.parameter.profiles (X, eta) := hrows eta ⟨he.1.le,
        he.2.le⟩ X hx
      _ = ModulatedHistories.profileRows W.profiles (X, eta) :=
        d.parameter.rows_eq hXp (d.parameters_target he)
  · intro p hp
    have hx : 0 < p.1 := d.modulation.left_pos.trans_le hp.1.1
    have hp' : p ∈ Icc d.modulation.left (repairPatch W).right ×ˢ band d.etaRadius :=
      ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
    have hcR := hcone p hp'
    have he := hQR p hx.le hp.2
    have hs := ActivationStocks.profiles_stocks_congr Q R F.data.h d.parameters_open hp.2
      (d.domain_nonnegative hx.le hp.2) ⟨mem_univ _, hJΩ hp'.2⟩ hx he.1 hcR.1.ne' he.2
      (fun row eta he => hhist p.1 hx.le eta he row)
    have hgF : (fun X => Q.E (X, p.2)) =ᶠ[𝓝 p.1] fun X => R.E (X, p.2) := by
      filter_upwards [lt_mem_nhds hx] with X hX
      exact congrArg (fun z => Real.sqrt (2 * X) * z) (hQR (X, p.2) hX.le hp.2).1
    have hgU : (fun X => Q.U (X, p.2)) =ᶠ[𝓝 p.1] fun X => R.U (X, p.2) := by
      filter_upwards [lt_mem_nhds hx] with X hX
      exact (hQR (X, p.2) hX.le hp.2).2
    have hsh := ModulatedCone.shears_eq_of_radial_eventuallyEq hgF hgU
    refine ⟨he.1.symm ▸ hcR.1, ?_⟩
    rw [hs.1, hs.2, hsh.1, hsh.2]
    exact hcR.2

namespace Witness

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : LoopData W} (v : Witness d)

theorem same_axis_pressure : v.profiles.pressure0 = F.axisDatum := v.pressure0

theorem fields_outside {p : Point} (hp : p.1 ∉ Ioo d.modulation.left (repairPatch W).right) :
    v.profiles.f p = W.profiles.f p ∧ v.profiles.U p = W.profiles.U p := by
  rw [v.f_formula, v.U_formula]
  exact d.output_outside v.realization v.frequency v.coefficients hp

theorem rows_before {X eta : ℝ} (hX : 0 ≤ X) (hbefore : X ≤ d.modulation.left) :
    ModulatedHistories.profileRows v.profiles (X, eta) =
      ModulatedHistories.profileRows W.profiles (X, eta) := by
  apply rows_eq_of_nonnegative v.profiles W.profiles v.pressure0 hX
  · intro x hx
    exact (v.fields_outside (by intro hc; linarith [hx.2, hc.1])).1
  · intro x hx
    exact (v.fields_outside (by intro hc; linarith [hx.2, hc.1])).2

theorem exterior_pressure {X eta : ℝ} (heta : eta ∈ d.parameters)
    (hX : (repairPatch W).right ≤ X) :
    v.profiles.pressure (X, eta) = W.profiles.pressure (X, eta) := by
  exact congrArg (fun rows => rows 4) (v.restored eta heta X hX)

theorem exterior_mass {X eta : ℝ} (heta : eta ∈ d.parameters)
    (hX : (repairPatch W).right ≤ X) : v.profiles.M (X, eta) = W.profiles.M (X, eta) := by
  exact congrArg (fun rows => rows 0) (v.restored eta heta X hX)

theorem exterior_angular {X eta : ℝ} (heta : eta ∈ d.parameters)
    (hX : (repairPatch W).right ≤ X) : v.profiles.I (X, eta) = W.profiles.I (X, eta) := by
  exact congrArg (fun rows => rows 1) (v.restored eta heta X hX)

theorem exterior_transport {X eta : ℝ} (heta : eta ∈ d.parameters)
    (hX : (repairPatch W).right ≤ X) : v.profiles.J (X, eta) = W.profiles.J (X, eta) := by
  exact congrArg (fun rows => rows 2) (v.restored eta heta X hX)

theorem exterior_energy {X eta : ℝ} (heta : eta ∈ d.parameters)
    (hX : (repairPatch W).right ≤ X) : v.profiles.S (X, eta) = W.profiles.S (X, eta) := by
  exact congrArg (fun rows => rows 3) (v.restored eta heta X hX)

theorem rows_outside {X eta : ℝ} (hX : 0 ≤ X) (heta : eta ∈ d.parameters)
    (hout : X ∉ Ioo d.modulation.left (repairPatch W).right) :
    ModulatedHistories.profileRows v.profiles (X, eta) =
      ModulatedHistories.profileRows W.profiles (X, eta) := by
  by_cases hl : X ≤ d.modulation.left
  · exact v.rows_before hX hl
  · exact v.restored eta heta X (le_of_not_gt (fun hr => hout ⟨lt_of_not_ge hl, hr⟩))

theorem stocks_outside {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ d.parameters)
    (hout : p.1 ∉ Ioo d.modulation.left (repairPatch W).right) (hf : W.profiles.f p ≠ 0) :
    ActivationStocks.profileStockOne v.profiles F.data.h p =
        ActivationStocks.profileStockOne W.profiles F.data.h p ∧
      ActivationStocks.profileStockTwo v.profiles F.data.h p =
        ActivationStocks.profileStockTwo W.profiles F.data.h p := by
  have he := v.fields_outside hout
  apply ActivationStocks.profiles_stocks_congr v.profiles W.profiles F.data.h
    d.parameters_open heta (d.domain_nonnegative hX.le heta)
    (d.domain_nonnegative hX.le heta).1 hX he.1 hf he.2
  intro row eta he
  rw [ModulatedCone.Localized.profileHistory_eq_row, ModulatedCone.Localized.profileHistory_eq_row,
    v.rows_outside hX.le he hout]

theorem shears_outside {p : Point}
    (hout : p.1 < d.modulation.left ∨ (repairPatch W).right < p.1) :
    ModulatedCone.angularShear v.profiles.E p = ModulatedCone.angularShear W.profiles.E p ∧
      ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p =
        ModulatedCone.signedAxialShear W.profiles.E W.profiles.U p := by
  have hn : ∀ᶠ X in 𝓝 p.1, X ∉ Ioo d.modulation.left (repairPatch W).right := by
    rcases hout with hl | hr
    · filter_upwards [gt_mem_nhds hl] with X hX
      exact fun h => (not_lt_of_ge hX.le) h.1
    · filter_upwards [lt_mem_nhds hr] with X hX
      exact fun h => (not_lt_of_ge hX.le) h.2
  apply ModulatedCone.shears_eq_of_radial_eventuallyEq
  · filter_upwards [hn] with X hX
    exact congrArg (fun z => Real.sqrt (2 * X) * z) (v.fields_outside (p := (X, p.2)) hX).1
  · filter_upwards [hn] with X hX
    exact (v.fields_outside (p := (X, p.2)) hX).2

/-- Outside the finite modulation interval the original true cone is
preserved with its actual stocks; inside it the constructed loop supplies
the true cone. This can be applied on the entire nominal annulus. -/
theorem true_cone_from_nominal {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ d.parameters)
    (hf : W.profiles.f p ≠ 0)
    (houtside : p.1 < d.modulation.left ∨ (repairPatch W).right < p.1 →
      TrueConeLoop.InTrueCone
        (ActivationStocks.profileStockOne W.profiles F.data.h p)
        (ActivationStocks.profileStockTwo W.profiles F.data.h p)
        (ModulatedCone.angularShear W.profiles.E p)
        (ModulatedCone.signedAxialShear W.profiles.E W.profiles.U p)) :
    TrueConeLoop.InTrueCone
      (ActivationStocks.profileStockOne v.profiles F.data.h p)
      (ActivationStocks.profileStockTwo v.profiles F.data.h p)
      (ModulatedCone.angularShear v.profiles.E p)
      (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p) := by
  by_cases hp : p.1 ∈ Icc d.modulation.left (repairPatch W).right
  · exact (v.true_cone p ⟨hp, heta⟩).2
  · have hout : p.1 < d.modulation.left ∨ (repairPatch W).right < p.1 := by
      simpa only [mem_Icc, not_and_or, not_le] using hp
    have hn : p.1 ∉ Ioo d.modulation.left (repairPatch W).right :=
      fun hx => hp ⟨hx.1.le, hx.2.le⟩
    have hs := v.stocks_outside hX heta hn hf
    have ha := v.shears_outside hout
    rw [hs.1, hs.2, ha.1, ha.2]
    exact houtside hout

end Witness

/-! ## Construction of the loop inputs from actual nominal cone bounds -/

theorem exists_smooth_extension {K O : Set Point} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (f : Field) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ g : Field, ContDiff ℝ ∞ g ∧ EqOn g f K := by
  obtain ⟨chi⟩ := ParametricModulation.exists_compactCutoff K O hK hO hKO
  refine ⟨fun p => chi.value p * f p, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro p
    by_cases hp : p ∈ O
    · exact chi.smooth.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds hp))
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point => (0 : ℝ)) p).congr_of_eventuallyEq
      filter_upwards [chi.zero_near p hp] with q hq
      rw [hq, zero_mul]
  · intro p hp
    dsimp only
    rw [chi.one_on p (chi.contains hp), one_mul]

noncomputable def regularDomain {D : RadialDomain} (P : Profiles D) (h : ℝ) : Set Point :=
  {p | p ∈ D.carrier ∧ 0 < p.1 ∧ 0 < P.f p ∧
    0 < ActivationContinuation.shearA P p ∧ NaturalAxisData.L h p.2 ≠ 0}

theorem regularDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (regularDomain P h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hf := (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp.1)).continuousAt
  have ha := (NominalConeAssembly.shears_smoothAt P hp.1 hp.2.1 hp.2.2.1.ne').1.continuousAt
  have hL : Continuous (fun q : Point => NaturalAxisData.L h q.2) := by
    exact continuous_const.sub ((continuous_const.mul continuous_const).mul (continuous_snd.pow 2))
  filter_upwards [D.isOpen.mem_nhds hp.1,
    continuous_fst.continuousAt.eventually (lt_mem_nhds hp.2.1),
    hf.eventually (lt_mem_nhds hp.2.2.1), ha.eventually (lt_mem_nhds hp.2.2.2.1),
    (isOpen_ne.preimage hL).mem_nhds hp.2.2.2.2] with q hq hx hqf hqa hqL
  exact ⟨hq, hx, hqf, hqa, hqL⟩

theorem coordinates_smooth {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    ContDiffOn ℝ ∞ (ActivationContinuation.shearA P) (regularDomain P h) ∧
      ContDiffOn ℝ ∞ (NominalConeAssembly.tilt P) (regularDomain P h) ∧
      ContDiffOn ℝ ∞ (ReferenceBounds.p1 P h) (regularDomain P h) ∧
      ContDiffOn ℝ ∞ (ReferenceBounds.p2 P h) (regularDomain P h) := by
  have hs : ∀ p ∈ regularDomain P h,
      ContDiffAt ℝ ∞ (ActivationContinuation.shearA P) p ∧
      ContDiffAt ℝ ∞ (NominalConeAssembly.tilt P) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p1 P h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 P h) p := by
    intro p hp
    exact NominalConeAssembly.cone_coordinates_smoothAt P h hp.1 hp.2.1 hp.2.2.1.ne'
      hp.2.2.2.1.ne' hp.2.2.2.2
  exact ⟨fun p hp => (hs p hp).1.contDiffWithinAt,
    fun p hp => (hs p hp).2.1.contDiffWithinAt,
    fun p hp => (hs p hp).2.2.1.contDiffWithinAt,
    fun p hp => (hs p hp).2.2.2.contDiffWithinAt⟩

noncomputable def relaxedDomain {D : RadialDomain} (P : Profiles D) (h : ℝ) : Set Point :=
  {p | p ∈ regularDomain P h ∧ ActivationContinuation.IsRelaxed P h p}

theorem relaxedDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (relaxedDomain P h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hs := NominalConeAssembly.cone_coordinates_smoothAt P h hp.1.1 hp.1.2.1
    hp.1.2.2.1.ne' hp.1.2.2.2.1.ne' hp.1.2.2.2.2
  have ha := hs.1.continuousAt
  have hm := hs.2.1.continuousAt
  have h₁ := hs.2.2.1.continuousAt
  have h₂ := hs.2.2.2.continuousAt
  have hproj := h₁.add (h₂.mul hm)
  have htrans := h₂.sub (h₁.mul hm)
  have hspeed := ha.mul ((continuousAt_const (y := (1 : ℝ))).add (hm.pow 2))
  have hbound := (hproj.add ((htrans.pow 2).div_const 4)).sub
    (htrans.abs.mul ((((hproj.sub (continuousAt_const (y := (2 : ℝ)))).div_const 2).add
      ((htrans.pow 2).div_const 16)).sqrt))
  have hpr : 2 < ReferenceBounds.p1 P h p + ReferenceBounds.p2 P h p * NominalConeAssembly.tilt P p
    :=
    hp.2.projection_positive
  have hsp : ActivationContinuation.shearA P p * (1 + NominalConeAssembly.tilt P p ^ 2) <
      ConeAlgebra.coneBound (ReferenceBounds.p1 P h p + ReferenceBounds.p2 P h p *
        NominalConeAssembly.tilt P p)
        (ReferenceBounds.p2 P h p - ReferenceBounds.p1 P h p * NominalConeAssembly.tilt P p) :=
          hp.2.cone
  filter_upwards [(regularDomain_open P h).mem_nhds hp.1,
    continuousAt_const.eventually_lt hproj hpr,
    hspeed.eventually_lt hbound hsp] with q hq hqpr hqsp
  exact ⟨hq, ⟨hq.2.2.2.1, hqpr, hqsp⟩⟩

noncomputable def trueDomain {D : RadialDomain} (P : Profiles D) (h : ℝ) : Set Point :=
  {p | p ∈ relaxedDomain P h ∧ NominalConeAssembly.IsTrue P h p}

theorem trueDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (trueDomain P h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hs := NominalConeAssembly.cone_coordinates_smoothAt P h hp.1.1.1 hp.1.1.2.1
    hp.1.1.2.2.1.ne' hp.1.1.2.2.2.1.ne' hp.1.1.2.2.2.2
  have hspeed := hs.1.continuousAt.mul
    ((continuousAt_const (y := (1 : ℝ))).add (hs.2.1.continuousAt.pow 2))
  have hsp : 2 < ActivationContinuation.shearA P p * (1 + NominalConeAssembly.tilt P p ^ 2) :=
    hp.2.2
  filter_upwards [(relaxedDomain_open P h).mem_nhds hp.1,
    continuousAt_const.eventually_lt hspeed hsp] with q hq hqs
  exact ⟨hq, hq.2, hqs⟩

/-- The remaining analytic input is stated entirely for the given nominal
profile and the physical band. No loop, repair, extension or modified
profile is assumed. -/
structure NominalBounds {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) where
  modulation : ModulatedHistories.Window
  after_initial : 4 / W.axis.scale < modulation.left
  before_repair : modulation.right < (repairPatch W).left
  relaxed : ∀ p ∈ fullRegion W modulation 1, ActivationContinuation.IsRelaxed W.profiles F.data.h p
  true_boundary : ∀ p ∈ boundaryRegion modulation 1, NominalConeAssembly.IsTrue W.profiles F.data.h
    p
  true_following : ∀ p ∈ followingRegion W modulation 1, NominalConeAssembly.IsTrue W.profiles
    F.data.h p

namespace NominalBounds

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F} (b : NominalBounds W)

theorem regular_of_relaxed {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ band 1)
    (hc : ActivationContinuation.IsRelaxed W.profiles F.data.h p) :
    p ∈ regularDomain W.profiles F.data.h :=
  ⟨W.domain_contains hX.le heta, hX, NominalConeAssembly.Witness.f_positive W hX heta,
    hc.first_positive, (NaturalAxisData.L_pos W.axis.small heta).ne'⟩

theorem exists_loopData : ∃ d : LoopData W, d.modulation = b.modulation := by
  classical
  obtain ⟨pd⟩ := exists_parameterData W
  have hfull : Icc b.modulation.left (repairPatch W).right ×ˢ band 1 ⊆
      relaxedDomain W.profiles F.data.h := by
    intro p hp
    exact ⟨regular_of_relaxed (b.modulation.left_pos.trans_le hp.1.1) hp.2 (b.relaxed p hp),
      b.relaxed p hp⟩
  obtain ⟨_, V₁, _, hV₁, hI₁, hJ₁, hprod₁⟩ := generalized_tube_lemma isCompact_Icc isCompact_Icc
    (relaxedDomain_open W.profiles F.data.h) hfull
  have hbdy : ({b.modulation.left, b.modulation.right} : Set ℝ) ×ˢ band 1 ⊆
      trueDomain W.profiles F.data.h := by
    intro p hp
    have hx : 0 < p.1 := by
      rcases Set.mem_insert_iff.mp hp.1 with h | h
      · simpa only [h] using b.modulation.left_pos
      · rw [Set.mem_singleton_iff] at h
        simpa only [h] using b.modulation.left_pos.trans b.modulation.ordered
    have hc := b.true_boundary p hp
    exact ⟨⟨regular_of_relaxed hx hp.2 hc.1, hc.1⟩, hc⟩
  obtain ⟨_, V₂, _, hV₂, hI₂, hJ₂, hprod₂⟩ := generalized_tube_lemma
    (isCompact_singleton.insert _) isCompact_Icc (trueDomain_open W.profiles F.data.h) hbdy
  have hfol : Icc b.modulation.right (repairPatch W).right ×ˢ band 1 ⊆
      trueDomain W.profiles F.data.h := by
    intro p hp
    have hc := b.true_following p hp
    exact ⟨⟨regular_of_relaxed ((b.modulation.left_pos.trans b.modulation.ordered).trans_le hp.1.1)
      hp.2 hc.1, hc.1⟩, hc⟩
  obtain ⟨_, V₃, _, hV₃, hI₃, hJ₃, hprod₃⟩ := generalized_tube_lemma isCompact_Icc isCompact_Icc
    (trueDomain_open W.profiles F.data.h) hfol
  let V := V₁ ∩ V₂ ∩ V₃ ∩ pd.target
  have hV : IsOpen V := ((hV₁.inter hV₂).inter hV₃).inter pd.target_open
  have hJV : Icc (-1 : ℝ) 1 ⊆ V := fun _ he => ⟨⟨⟨hJ₁ he, hJ₂ he⟩, hJ₃ he⟩, pd.target_contains he⟩
  obtain ⟨w⟩ := ParametricRadialExtension.exists_parameterWindow hV hJV
  have hband : band w.inner ⊆ V := by
    intro eta heta
    apply w.outer_subset
    constructor <;> linarith [heta.1, heta.2, w.inner_lt_outer]
  have hT : fullRegion W b.modulation w.inner ⊆ relaxedDomain W.profiles F.data.h := by
    intro p hp
    exact hprod₁ ⟨hI₁ hp.1, (hband hp.2).1.1.1⟩
  have hB : boundaryRegion b.modulation w.inner ⊆ trueDomain W.profiles F.data.h := by
    intro p hp
    exact hprod₂ ⟨hI₂ hp.1, (hband hp.2).1.1.2⟩
  have hS : followingRegion W b.modulation w.inner ⊆ trueDomain W.profiles F.data.h := by
    intro p hp
    exact hprod₃ ⟨hI₃ hp.1, (hband hp.2).1.2⟩
  have hcompact : IsCompact (fullRegion W b.modulation w.inner) := isCompact_Icc.prod isCompact_Icc
  have hTO : fullRegion W b.modulation w.inner ⊆ regularDomain W.profiles F.data.h := fun _ hp =>
    (hT hp).1
  have hcoords := coordinates_smooth W.profiles F.data.h
  obtain ⟨a, ha, hea⟩ := exists_smooth_extension hcompact (regularDomain_open W.profiles F.data.h)
    hTO _ hcoords.1
  obtain ⟨m, hm, hem⟩ := exists_smooth_extension hcompact (regularDomain_open W.profiles F.data.h)
    hTO _ hcoords.2.1
  obtain ⟨p₁, h₁, he₁⟩ := exists_smooth_extension hcompact (regularDomain_open W.profiles F.data.h)
    hTO _ hcoords.2.2.1
  obtain ⟨p₂, h₂, he₂⟩ := exists_smooth_extension hcompact (regularDomain_open W.profiles F.data.h)
    hTO _ hcoords.2.2.2
  have hKT : modulationRegion b.modulation w.inner ⊆ fullRegion W b.modulation w.inner := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (b.before_repair.trans (repairPatch W).ordered).le⟩, hp.2⟩
  have hST : followingRegion W b.modulation w.inner ⊆ fullRegion W b.modulation w.inner := by
    intro p hp
    exact ⟨⟨b.modulation.ordered.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
  have hBT : boundaryRegion b.modulation w.inner ⊆ fullRegion W b.modulation w.inner := by
    intro p hp
    apply hKT
    rcases Set.mem_insert_iff.mp hp.1 with hx | hx
    · exact ⟨⟨hx.ge, hx.le.trans b.modulation.ordered.le⟩, hp.2⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨⟨b.modulation.ordered.le.trans hx.ge, hx.le⟩, hp.2⟩
  have ham : ∀ p ∈ fullRegion W b.modulation w.inner,
      a p * m p = ActivationContinuation.shearB W.profiles p := by
    intro p hp
    rw [hea hp, hem hp, NominalConeAssembly.tilt]
    exact mul_div_cancel₀ _ (hT hp).2.first_positive.ne'
  refine ⟨{
    parameter := pd
    etaRadius := w.inner
    one_lt_etaRadius := w.one_lt_inner
    etaRadius_lt_target := (hband (show w.inner ∈ band w.inner from ⟨by linarith [w.inner_pos],
      le_rfl⟩)).2.2
    modulation := b.modulation
    after_initial := b.after_initial
    before_repair := b.before_repair
    a := a
    m := m
    p₁ := p₁
    p₂ := p₂
    a_smooth := ha
    m_smooth := hm
    p₁_smooth := h₁
    p₂_smooth := h₂
    angular_eq := ?_
    axial_eq := ?_
    stock₁_eq := ?_
    stock₂_eq := ?_
    positive_f := fun p hp => (hTO hp).2.2.1
    positive_a := ?_
    nonzero_L := fun p hp => (hTO hp).2.2.2.2
    projection := ?_
    relaxed := ?_
    true_boundary := ?_
    true_following := ?_ }, rfl⟩
  · intro p hp
    exact (hea hp).trans (NominalConeAssembly.modulated_shears_eq W.profiles
      (hTO hp).1 (hTO hp).2.1 (hTO hp).2.2.1.ne').1.symm
  · intro p hp
    exact (ham p hp).trans (NominalConeAssembly.modulated_shears_eq W.profiles
      (hTO hp).1 (hTO hp).2.1 (hTO hp).2.2.1.ne').2.symm
  · intro p hp
    exact (he₁ hp).trans (NominalConeAssembly.p1_eq_stock _ _ _)
  · intro p hp
    exact (he₂ hp).trans (NominalConeAssembly.p2_eq_stock _ _ _)
  · intro p hp
    rw [hea hp]
    exact (hT hp).2.first_positive
  · intro p hp
    rw [he₁ (hKT hp), he₂ (hKT hp), hem (hKT hp)]
    exact (hT (hKT hp)).2.projection_positive
  · intro p hp
    rw [hea (hKT hp), he₁ (hKT hp), he₂ (hKT hp), hem (hKT hp)]
    exact (hT (hKT hp)).2.cone
  · intro p hp
    rw [hea (hBT hp), hem (hBT hp)]
    exact (hB hp).2.2
  · intro p hp
    rw [he₁ (hST hp), he₂ (hST hp), ham p (hST hp), hea (hST hp)]
    exact (NominalConeAssembly.isTrue_iff_loop _ _ _).mp (hS hp).2

theorem exists_modulated : ∃ d : LoopData W, d.modulation = b.modulation ∧ Nonempty (Witness d) :=
  by
  obtain ⟨d, hd⟩ := b.exists_loopData
  exact ⟨d, hd, exists_witness d⟩

end NominalBounds

namespace Witness

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : LoopData W} (v : Witness d)

noncomputable def slowParameters (_v : Witness d) : Set ℝ :=
  d.parameters ∩ AssembledSlowBase.nominalParameters W

/-- The consumer certificate is proved for this actual finite profile.
The slow hierarchy can therefore be reconstructed from the same `W`. -/
theorem finiteModification : AssembledSlowBase.FiniteModification W v.profiles v.slowParameters
    d.modulation.left (repairPatch W).right where
  isOpen := d.parameters_open.inter (AssembledSlowBase.nominalParameters_open W)
  contains := fun _ h => ⟨d.parameters_contains h, AssembledSlowBase.nominalParameters_contains W h⟩
  subset := inter_subset_right
  halfPlane := fun _ hX _ he => d.domain_nonnegative hX he.1
  inner := by
    have hpos : 0 < 4 / W.axis.scale := div_pos (by norm_num) W.axis.scale_pos
    change (4 / W.axis.scale) / 4 ≤ d.modulation.left
    linarith [d.after_initial]
  ordered := d.modulation.ordered.trans (d.before_repair.trans (repairPatch W).ordered)
  outer := (repairPatch_before_positive W).le
  pressure0 := v.pressure0
  fields := by
    intro p _ _ hp
    apply v.fields_outside
    intro hi
    rcases hp with hp | hp
    · exact (not_lt_of_ge hp) hi.1
    · exact (not_lt_of_ge hp) hi.2
  mass := by
    intro eta he
    apply v.exterior_mass he.1
    exact (repairPatch_before_positive W).le.trans
      ((ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos .positive).le.trans
        (AssembledSlowBase.nominalOuterX_gt_patch W).le)

/-- The additional angular anchor needed by the first-order exterior
stress argument is retained alongside the finite-modification certificate. -/
theorem slow_outer_angular {eta : ℝ} (heta : eta ∈ v.slowParameters) :
    v.profiles.I (AssembledSlowBase.nominalOuterX W, eta) =
      W.profiles.I (AssembledSlowBase.nominalOuterX W, eta) := by
  apply v.exterior_angular heta.1
  exact (repairPatch_before_positive W).le.trans
    ((ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos .positive).le.trans
      (AssembledSlowBase.nominalOuterX_gt_patch W).le)

theorem positive_f {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    0 < v.profiles.f p := by
  by_cases hp : p.1 ∈ Icc d.modulation.left (repairPatch W).right
  · exact (v.true_cone p ⟨hp, d.parameters_contains heta⟩).1
  · have hn : p.1 ∉ Ioo d.modulation.left (repairPatch W).right :=
      fun hx => hp ⟨hx.1.le, hx.2.le⟩
    rw [(v.fields_outside hn).1]
    exact NominalConeAssembly.Witness.f_positive W hX heta

theorem positive_E {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    0 < v.profiles.E p :=
  mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) hX)) (v.positive_f hX heta)

end Witness

/-! ## Bind the constructed profile to the completed nominal cone theorem -/

noncomputable def holdRadius {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : ℝ :=
  W.controls.radius * Real.exp F.data.core.holdStart

theorem holdRadius_gt_radius {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    W.controls.radius < holdRadius W := by
  have he := Real.one_lt_exp_iff.mpr F.data.core.holdStart_pos
  have h := mul_lt_mul_of_pos_left he W.controls.radius_pos
  simp only [mul_one] at h
  exact h

theorem holdRadius_before_repair {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    holdRadius W < (repairPatch W).left :=
  (ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos
    (ReservedPatches.clock_inside_wait F .modulation).1).trans
      (ReservedPatches.support_margins F W.controls.radius W.controls.radius_pos .modulation).1

theorem repairPatch_before_activeRight {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  :
    (repairPatch W).right < NominalConeAssembly.activeRight W := by
  have hclock : ReservedPatches.rightClock F .modulation < OutgoingTail.tailEnd F.data := by
    have h₀ := (ReservedPatches.clock_inside_wait F .modulation).2
    have h₁ := OutgoingTail.flattenEnd_gt_core F.data
    have h₂ := OutgoingTail.releaseStart_gt_flattenEnd F.data
    have h₃ := OutgoingTail.tailStart_gt_release F.data
    dsimp only [OutgoingSchedule.Parameters.endpoint] at h₁
    dsimp only [OutgoingTail.tailEnd]
    linarith [F.data.core.pulseLength_pos]
  exact (ReservedPatches.support_margins F W.controls.radius W.controls.radius_pos
    .modulation).2.2.trans
    (ReservedPatches.radius_strictMono W.controls.radius W.controls.radius_pos hclock)

theorem nominalBounds_of_certificate {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (hW : NominalConeAssembly.Certificate W) :
    ∃ b : NominalBounds W, ∀ p : Point,
      NominalConeAssembly.activeLeft W < p.1 → p.1 < NominalConeAssembly.activeRight W →
      p.2 ∈ Icc (-1 : ℝ) 1 →
      (p.1 < b.modulation.left ∨ (repairPatch W).right < p.1) →
      NominalConeAssembly.IsTrue W.profiles F.data.h p := by
  obtain ⟨t, ht, htact, hinit⟩ := hW.initial
  let lo := NominalConeAssembly.activeLeft W * Real.exp (t / 2)
  have hx₀ := NominalConeAssembly.activeLeft_pos W
  have hlo : NominalConeAssembly.activeLeft W < lo := by
    have he := Real.one_lt_exp_iff.mpr (half_pos ht)
    simpa only [lo, mul_one] using mul_lt_mul_of_pos_left he hx₀
  have hloXi : lo ≤ NominalProfile.Xi := by
    apply le_trans _ W.controls.activation_collar_le_Xi
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hx₀.le
    linarith [W.controls.activationTime_le]
  have hlor : lo < holdRadius W :=
    (hloXi.trans_lt (W.controls.Xi_lt_heatJoin W.separated)).trans
      (W.controls.heatJoin_lt_radius.trans (holdRadius_gt_radius W))
  let v : ModulatedHistories.Window := ⟨lo, holdRadius W, hx₀.trans hlo, hlor⟩
  have hgap : v.right < (repairPatch W).left := holdRadius_before_repair W
  have htrue_after (p : Point) (hp : holdRadius W ≤ p.1)
      (hr : p.1 < NominalConeAssembly.activeRight W) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
      NominalConeAssembly.IsTrue W.profiles F.data.h p := by
    have hx : 0 < p.1 := (W.controls.radius_pos.trans (holdRadius_gt_radius W)).trans_le hp
    have hy : F.data.core.holdStart ≤ Real.log (p.1 / W.controls.radius) := by
      apply (Real.le_log_iff_exp_le (div_pos hx W.controls.radius_pos)).mpr
      apply (le_div_iff₀ W.controls.radius_pos).mpr
      simpa only [holdRadius, mul_comm] using hp
    have hy' := NominalConeAssembly.log_chart_lt W.controls.radius_pos hx hr
    have hc := hW.outgoing _ p.2 hy hy' heta
    rwa [NominalConeAssembly.chart_log W.controls.radius_pos hx] at hc
  let b : NominalBounds W := {
    modulation := v
    after_initial := hlo
    before_repair := hgap
    relaxed := fun p hp => hW.relaxed p (hlo.trans_le hp.1.1)
      (hp.1.2.trans_lt (repairPatch_before_activeRight W)) hp.2
    true_boundary := by
      intro p hp
      rcases Set.mem_insert_iff.mp hp.1 with h | h
      · have hc := hinit (t / 2) p.2 (half_pos ht) (by linarith) hp.2
        convert! hc using 1
        apply Prod.ext
        · exact h
        · rfl
      · rw [Set.mem_singleton_iff] at h
        exact htrue_after p h.ge
          (h.le.trans_lt (hgap.trans ((repairPatch W).ordered.trans (repairPatch_before_activeRight
            W)))) hp.2
    true_following := fun p hp => htrue_after p hp.1.1
      (hp.1.2.trans_lt (repairPatch_before_activeRight W)) hp.2 }
  refine ⟨b, ?_⟩
  intro p hl hr heta hout
  rcases hout with hleft | hright
  · have hx := hx₀.trans hl
    have hy : 0 < Real.log (p.1 / NominalConeAssembly.activeLeft W) := by
      apply NominalConeAssembly.lt_log_chart hx₀
      simpa only [Real.exp_zero, mul_one] using hl
    have hy' : Real.log (p.1 / NominalConeAssembly.activeLeft W) ≤ t :=
      (NominalConeAssembly.log_chart_lt hx₀ hx hleft).le.trans (by linarith)
    have hc := hinit _ p.2 hy hy' heta
    rwa [NominalConeAssembly.chart_log hx₀ hx] at hc
  · exact htrue_after p (hgap.le.trans ((repairPatch W).ordered.le.trans hright.le)) hr heta

/-- One actual modulated physical profile of the fixed nominal witness,
with the true cone on its whole active annulus. The nominal certificate
constructs every input of the finite modulation theorem. -/
theorem exists_of_certificate {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (hW : NominalConeAssembly.Certificate W) :
    ∃ (d : LoopData W) (v : Witness d), ∀ p : Point,
      NominalConeAssembly.activeLeft W < p.1 → p.1 < NominalConeAssembly.activeRight W →
      p.2 ∈ Icc (-1 : ℝ) 1 →
      TrueConeLoop.InTrueCone
        (ActivationStocks.profileStockOne v.profiles F.data.h p)
        (ActivationStocks.profileStockTwo v.profiles F.data.h p)
        (ModulatedCone.angularShear v.profiles.E p)
        (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p) := by
  obtain ⟨b, hb⟩ := nominalBounds_of_certificate W hW
  obtain ⟨d, hd, ⟨v⟩⟩ := b.exists_modulated
  refine ⟨d, v, ?_⟩
  intro p hl hr heta
  have hx := (NominalConeAssembly.activeLeft_pos W).trans hl
  have hf := NominalConeAssembly.Witness.f_positive W hx heta
  apply v.true_cone_from_nominal hx (d.parameters_contains heta) hf.ne'
  intro hout
  have hc := (NominalConeAssembly.isTrue_iff_loop W.profiles F.data.h p).mp
    (hb p hl hr heta (by simpa only [hd] using hout))
  have hs := NominalConeAssembly.modulated_shears_eq W.profiles (W.domain_contains hx.le heta) hx
    hf.ne'
  simpa only [NominalConeAssembly.p1_eq_stock, NominalConeAssembly.p2_eq_stock, hs.1, hs.2] using hc

/-- The already constructed nominal cone theorem supplies a concrete
profile, its actual finite modulation, and the full active true cone. -/
theorem exists_modulated_profile :
    ∃ (F : OutgoingProfile.Profile) (W : NominalProfile.Witness F)
      (d : LoopData W) (v : Witness d), ∀ p : Point,
      NominalConeAssembly.activeLeft W < p.1 → p.1 < NominalConeAssembly.activeRight W →
      p.2 ∈ Icc (-1 : ℝ) 1 →
      TrueConeLoop.InTrueCone
        (ActivationStocks.profileStockOne v.profiles F.data.h p)
        (ActivationStocks.profileStockTwo v.profiles F.data.h p)
        (ModulatedCone.angularShear v.profiles.E p)
        (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p) := by
  obtain ⟨F, W, hW⟩ := NominalConeAssembly.exists_nominal_cone
  obtain ⟨d, v, hv⟩ := exists_of_certificate W hW
  exact ⟨F, W, d, v, hv⟩

end NavierStokes.ModulatedProfileAssembly
