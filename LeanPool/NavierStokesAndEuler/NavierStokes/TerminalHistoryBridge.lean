/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalCone
import LeanPool.NavierStokesAndEuler.NavierStokes.HeatTailHistoryLimits
import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStress
import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalHeatCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatSwitchCone

/-!
# The same compensated histories and the terminal backward stress

All forward histories in this file use the supplied compensation witness.
The base outgoing energy identity is kept explicit; zero changes alone do
not imply a zero total energy moment.
-/

section

/-!
# Derivatives of the actual compensated heat histories

The first radial identities come from the actual finite integrals. Joint
smoothness and parameter differentiation of those integrals then give the
mixed identities on the open physical parameter band.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology
open NavierStokes.OutgoingProfile (Profile)
open NavierStokes.HeatSwitchCone

namespace NavierStokes.HeatSwitchHistoryDerivatives

/-- Interior domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
noncomputable def interiorDomain : ProfileHistories.RadialDomain where
  carrier := univ ×ˢ Ioo (-1) 1
  isOpen := isOpen_univ.prod isOpen_Ioo
  scale_mem := fun _ hp _ _ => ⟨mem_univ _, hp.2⟩

theorem interior_to_band {eta : ℝ} (heta : eta ∈ Ioo (-1) 1) :
    eta ∈ HeatedOutgoing.parameterDomain := ⟨heta.1.le, heta.2.le⟩

theorem realize_contDiffOn {f : Raw → ℝ} (hf : ContDiff ℝ ∞ f) (delta : ℝ)
    {c : ℝ → Coeff} (hc : ContDiffOn ℝ ∞ c HeatedOutgoing.parameterDomain) :
    ContDiffOn ℝ ∞ (realize f delta c) interiorDomain.carrier := by
  have hc' : ContDiffOn ℝ ∞ (fun p : Point => c p.2) interiorDomain.carrier :=
    hc.comp contDiffOn_snd (fun p hp => interior_to_band hp.2)
  have hg : ContDiffOn ℝ ∞ (fun p : Point => ((delta, c p.2), p)) interiorDomain.carrier :=
    (contDiffOn_const.prodMk hc').prodMk contDiffOn_id
  exact hf.comp_contDiffOn hg

theorem logE_contDiffOn (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (logE F XR w.coefficients) interiorDomain.carrier :=
  (realize_contDiffOn (freeE_contDiff F) (1 / XR) w.smooth).congr
    (fun p hp => logE_eq_realize F XR w.coefficients w.radius_pos p (interior_to_band hp.2))

theorem logI_contDiffOn (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (logI F XR w.coefficients) interiorDomain.carrier :=
  (realize_contDiffOn (freeI_contDiff F) (1 / XR) w.smooth).congr
    (fun p hp => logI_eq_realize F XR w.coefficients w.radius_pos p (interior_to_band hp.2))

theorem logS_contDiffOn (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (logS F XR w.coefficients) interiorDomain.carrier :=
  (realize_contDiffOn (freeS_contDiff F) (1 / XR) w.smooth).congr
    (fun p hp => logS_eq_realize F XR w.coefficients w.radius_pos p (interior_to_band hp.2))

theorem logPi_contDiffOn (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (logPi F XR w.coefficients) interiorDomain.carrier :=
  (realize_contDiffOn (freePi_contDiff F) (1 / XR) w.smooth).congr
    (fun p hp => logPi_eq_realize F XR w.coefficients w.radius_pos p (interior_to_band hp.2))

theorem integral_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a y : ℝ) :
    HasDerivAt (fun y => ∫ t in a..y, f t) (f y) y :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a y)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem logI_hasDerivAt (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    HasDerivAt (fun y => logI F XR w.coefficients (y, p.2))
      (Real.exp (3 * p.1 / 2) * logE F XR w.coefficients p) p.1 := by
  have he : Continuous (fun t : ℝ => Real.exp (3 * t / 2)) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)
  have hc : Continuous (fun t => Real.exp (3 * t / 2) *
      (logE F XR w.coefficients (t, p.2) - F.logE (t, p.2))) :=
    he.mul ((logE_continuous_radial F w.radius_pos w.coefficients hp).sub
      (F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)))
  have hd := (OutgoingHistories.I_hasDerivAt F.reset p).add
    (integral_hasDerivAt hc (OutgoingDilation.patchClock F) p.1)
  change HasDerivAt (fun y => logI F XR w.coefficients (y, p.2)) _ p.1 at hd
  convert! hd using 1
  rw [show OutgoingHistories.X p * OutgoingHistories.H F.reset p =
      Real.exp (3 * p.1 / 2) * F.logE p from OutgoingHistories.angularWeight_eq F.reset p]
  simp only [Prod.mk.eta]
  ring

theorem logS_hasDerivAt (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    HasDerivAt (fun y => logS F XR w.coefficients (y, p.2))
      (Real.exp p.1 * (F.logU p ^ 2 - logE F XR w.coefficients p ^ 2 / 2)) p.1 := by
  have hc : Continuous (fun t => Real.exp t *
      (logE F XR w.coefficients (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2)) :=
    Real.continuous_exp.mul (((logE_continuous_radial F w.radius_pos w.coefficients hp).pow 2).sub
      ((F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2))
  have hd := (OutgoingHistories.S_hasDerivAt F.reset F.amp_contDiff p).sub
    ((integral_hasDerivAt hc (OutgoingDilation.patchClock F) p.1).const_mul (1 / 2 : ℝ))
  change HasDerivAt (fun y => logS F XR w.coefficients (y, p.2)) _ p.1 at hd
  convert! hd using 1
  simp only [OutgoingHistories.X, OutgoingHistories.energyDensity, OutgoingHistories.U,
    OutgoingHistories.E, OutgoingProfile.Profile.logU, OutgoingProfile.Profile.logE, Prod.mk.eta]
  ring

theorem logPi_hasDerivAt (F : Profile) {XR C : ℝ} (w : HeatedOutgoing.CompensationWitness F XR C)
    (p : Point) (hp : p.2 ∈ HeatedOutgoing.parameterDomain) :
    HasDerivAt (fun y => logPi F XR w.coefficients (y, p.2))
      (logE F XR w.coefficients p ^ 2 / 2) p.1 := by
  have hc : Continuous (fun t => logE F XR w.coefficients (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2) :=
    ((logE_continuous_radial F w.radius_pos w.coefficients hp).pow 2).sub
      ((F.logE_contDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
  have hd := (OutgoingHistories.Pi_hasDerivAt F.reset p).add
    ((integral_hasDerivAt hc (OutgoingDilation.patchClock F) p.1).const_mul (1 / 2 : ℝ))
  change HasDerivAt (fun y => logPi F XR w.coefficients (y, p.2)) _ p.1 at hd
  convert! hd using 1
  simp only [OutgoingHistories.E, OutgoingProfile.Profile.logE, Prod.mk.eta]
  ring

/-- Angular weight, given by `Real.exp (3 * p.1 / 2) * logE F XR c p`. -/
noncomputable def angularWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  Real.exp (3 * p.1 / 2) * logE F XR c p
/-- Energy weight, given by `Real.exp p.1 * (F.logU p ^ 2 - logE F XR c p ^ 2 / 2)`. -/
noncomputable def energyWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  Real.exp p.1 * (F.logU p ^ 2 - logE F XR c p ^ 2 / 2)
/-- Pressure weight, given by `logE F XR c p ^ 2 / 2`. -/
noncomputable def pressureWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  logE F XR c p ^ 2 / 2

theorem angularWeight_contDiffOn (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (angularWeight F XR w.coefficients) interiorDomain.carrier :=
  (((contDiffOn_const.mul contDiffOn_fst).div_const 2).exp).mul (logE_contDiffOn F w)
theorem energyWeight_contDiffOn (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (energyWeight F XR w.coefficients) interiorDomain.carrier :=
  contDiffOn_fst.exp.mul ((F.logU_contDiff.contDiffOn.pow 2).sub
    (((logE_contDiffOn F w).pow 2).div_const 2))
theorem pressureWeight_contDiffOn (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) :
    ContDiffOn ℝ ∞ (pressureWeight F XR w.coefficients) interiorDomain.carrier :=
  ((logE_contDiffOn F w).pow 2).div_const 2

theorem history_primitive_representation {H G : Point → ℝ}
    (hG : ContDiffOn ℝ ∞ G interiorDomain.carrier)
    (hH : ∀ p ∈ interiorDomain.carrier,
      HasDerivAt (fun y => H (y, p.2)) (G p) p.1)
    {p : Point} (hp : p ∈ interiorDomain.carrier) :
    H p = H (0, p.2) + ProfileHistories.primitive G p := by
  have hg : ContDiff ℝ ∞ (fun y => G (y, p.2)) :=
    hG.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun y => ⟨mem_univ _, hp.2⟩)
  have hd (t : ℝ) : HasDerivAt (fun y => H (y, p.2)) (G (t, p.2)) t :=
    hH (t, p.2) ⟨mem_univ _, hp.2⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := p.1)
    (fun t _ => hd t) (hg.continuous.intervalIntegrable 0 p.1)
  change H p = H (0, p.2) + ∫ t in (0 : ℝ)..p.1, G (t, p.2)
  simpa only [sub_eq_iff_eq_add, add_comm, Prod.mk.eta] using hi.symm

/-- Mixed differentiation of a genuine smooth history. The radial identity
in this helper is supplied below by the just-proved fundamental-theorem
identities for the actual three histories. -/
theorem history_parameter_mixed {H G : Point → ℝ}
    (hH : ContDiffOn ℝ ∞ H interiorDomain.carrier)
    (hG : ContDiffOn ℝ ∞ G interiorDomain.carrier)
    (hODE : ∀ p ∈ interiorDomain.carrier,
      HasDerivAt (fun y => H (y, p.2)) (G p) p.1)
    {p : Point} (hp : p ∈ interiorDomain.carrier) :
    HasDerivAt (fun y => ProfileHistories.parameterPartial H (y, p.2))
      (ProfileHistories.parameterPartial G p) p.1 := by
  have hprim := ProfileHistories.primitive_smooth interiorDomain hG
  have he (y : ℝ) : ProfileHistories.parameterPartial H (y, p.2) =
      ProfileHistories.parameterPartial H (0, p.2) +
        ProfileHistories.parameterPartial (ProfileHistories.primitive G) (y, p.2) := by
    have hd0 := ProfileHistories.parameterPartial_hasDerivAt interiorDomain hH
      (show (0, p.2) ∈ interiorDomain.carrier from ⟨mem_univ _, hp.2⟩)
    have hd1 := ProfileHistories.parameterPartial_hasDerivAt interiorDomain hprim
      (show (y, p.2) ∈ interiorDomain.carrier from ⟨mem_univ _, hp.2⟩)
    have hd := hd0.add hd1
    have heq : (fun eta => H (y, eta)) =ᶠ[𝓝 p.2]
        (fun eta => H (0, eta) + ProfileHistories.primitive G (y, eta)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hp.2] with eta heta
      exact history_primitive_representation hG hODE ⟨mem_univ _, heta⟩
    exact (ProfileHistories.parameterPartial_hasDerivAt interiorDomain hH
      (show (y, p.2) ∈ interiorDomain.carrier from ⟨mem_univ _, hp.2⟩)).unique
        (hd.congr_of_eventuallyEq heq)
  have hd := (ProfileHistories.parameterPartial_primitive_hasDerivAt interiorDomain hG hp).const_add
    (ProfileHistories.parameterPartial H (0, p.2))
  have hfun : (fun y => ProfileHistories.parameterPartial H (y, p.2)) =
      (fun y => ProfileHistories.parameterPartial H (0, p.2) +
        ProfileHistories.parameterPartial (ProfileHistories.primitive G) (y, p.2)) := funext he
  rw [hfun]
  simpa only [zero_add] using hd

theorem within_parameter_eq {H : Point → ℝ}
    (hH : ContDiffOn ℝ ∞ H interiorDomain.carrier)
    {p : Point} (hp : p ∈ interiorDomain.carrier) :
    derivWithin (fun eta => H (p.1, eta)) HeatedOutgoing.parameterDomain p.2 =
      ProfileHistories.parameterPartial H p :=
  (ProfileHistories.parameterPartial_hasDerivAt interiorDomain hH hp).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (by norm_num) p.2 (interior_to_band hp.2))

theorem ordinary_parameter_eq {H : Point → ℝ}
    (hH : ContDiffOn ℝ ∞ H interiorDomain.carrier)
    {p : Point} (hp : p ∈ interiorDomain.carrier) :
    deriv (fun eta => H (p.1, eta)) p.2 = ProfileHistories.parameterPartial H p :=
  (ProfileHistories.parameterPartial_hasDerivAt interiorDomain hH hp).deriv

theorem history_parameter_mixed_within {H G : Point → ℝ}
    (hH : ContDiffOn ℝ ∞ H interiorDomain.carrier)
    (hG : ContDiffOn ℝ ∞ G interiorDomain.carrier)
    (hODE : ∀ p ∈ interiorDomain.carrier,
      HasDerivAt (fun y => H (y, p.2)) (G p) p.1)
    {p : Point} (hp : p ∈ interiorDomain.carrier) :
    HasDerivAt (fun y => derivWithin (fun eta => H (y, eta)) HeatedOutgoing.parameterDomain p.2)
      (ProfileHistories.parameterPartial G p) p.1 := by
  have he : (fun y => derivWithin (fun eta => H (y, eta)) HeatedOutgoing.parameterDomain p.2) =
      (fun y => ProfileHistories.parameterPartial H (y, p.2)) := by
    funext y
    exact within_parameter_eq hH (p := (y, p.2)) ⟨mem_univ _, hp.2⟩
  rw [he]
  exact history_parameter_mixed hH hG hODE hp

theorem angularWeight_parameter (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p ∈ interiorDomain.carrier) :
    ProfileHistories.parameterPartial (angularWeight F XR w.coefficients) p =
      Real.exp (3 * p.1 / 2) * derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
        HeatedOutgoing.parameterDomain p.2 := by
  rw [within_parameter_eq (logE_contDiffOn F w) hp]
  exact (ProfileHistories.parameterPartial_hasDerivAt interiorDomain
    (angularWeight_contDiffOn F w) hp).unique
      ((ProfileHistories.parameterPartial_hasDerivAt interiorDomain (logE_contDiffOn F w)
          hp).const_mul
        (Real.exp (3 * p.1 / 2)))

theorem energyWeight_parameter (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p ∈ interiorDomain.carrier) :
    ProfileHistories.parameterPartial (energyWeight F XR w.coefficients) p =
      Real.exp p.1 * (2 * F.logU p * OutgoingHistories.dEta F.logU p -
        logE F XR w.coefficients p *
          derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
            HeatedOutgoing.parameterDomain p.2) := by
  rw [within_parameter_eq (logE_contDiffOn F w) hp]
  have hu := OutgoingHistories.dEta_hasDerivAt F.logU_contDiff p
  have he := ProfileHistories.parameterPartial_hasDerivAt interiorDomain (logE_contDiffOn F w) hp
  have hd := ((hu.pow 2).sub ((he.pow 2).div_const 2)).const_mul (Real.exp p.1)
  have hh := (ProfileHistories.parameterPartial_hasDerivAt interiorDomain
    (energyWeight_contDiffOn F w) hp).unique hd
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at hh
  exact hh.trans (by ring)

theorem pressureWeight_parameter (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) {p : Point}
    (hp : p ∈ interiorDomain.carrier) :
    ProfileHistories.parameterPartial (pressureWeight F XR w.coefficients) p =
      logE F XR w.coefficients p *
        derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
          HeatedOutgoing.parameterDomain p.2 := by
  rw [within_parameter_eq (logE_contDiffOn F w) hp]
  have he := ProfileHistories.parameterPartial_hasDerivAt interiorDomain (logE_contDiffOn F w) hp
  have hh := (ProfileHistories.parameterPartial_hasDerivAt interiorDomain
    (pressureWeight_contDiffOn F w) hp).unique ((he.pow 2).div_const 2)
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at hh
  exact hh.trans (by ring)

/-- The mixed derivative uses the actual parameter derivative already
appearing in the stress formula. -/
theorem logI_eta_hasDerivAt (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) (p : Point) (hp : p.2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun y => derivWithin (fun eta => logI F XR w.coefficients (y, eta))
      HeatedOutgoing.parameterDomain p.2)
      (Real.exp (3 * p.1 / 2) * derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
        HeatedOutgoing.parameterDomain p.2) p.1 := by
  have hmem : p ∈ interiorDomain.carrier := ⟨mem_univ _, hp⟩
  have hd := history_parameter_mixed_within (logI_contDiffOn F w) (angularWeight_contDiffOn F w)
    (fun p hp => logI_hasDerivAt F w p (interior_to_band hp.2)) hmem
  rw [angularWeight_parameter F w hmem] at hd
  exact hd

theorem logS_eta_hasDerivAt (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) (p : Point) (hp : p.2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun y => derivWithin (fun eta => logS F XR w.coefficients (y, eta))
      HeatedOutgoing.parameterDomain p.2)
      (Real.exp p.1 * (2 * F.logU p * OutgoingHistories.dEta F.logU p -
        logE F XR w.coefficients p *
          derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
            HeatedOutgoing.parameterDomain p.2)) p.1 := by
  have hmem : p ∈ interiorDomain.carrier := ⟨mem_univ _, hp⟩
  have hd := history_parameter_mixed_within (logS_contDiffOn F w) (energyWeight_contDiffOn F w)
    (fun p hp => logS_hasDerivAt F w p (interior_to_band hp.2)) hmem
  rw [energyWeight_parameter F w hmem] at hd
  exact hd

theorem logPi_eta_hasDerivAt (F : Profile) {XR C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR C) (p : Point) (hp : p.2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun y => derivWithin (fun eta => logPi F XR w.coefficients (y, eta))
      HeatedOutgoing.parameterDomain p.2)
      (logE F XR w.coefficients p *
        derivWithin (fun eta => logE F XR w.coefficients (p.1, eta))
          HeatedOutgoing.parameterDomain p.2) p.1 := by
  have hmem : p ∈ interiorDomain.carrier := ⟨mem_univ _, hp⟩
  have hd := history_parameter_mixed_within (logPi_contDiffOn F w) (pressureWeight_contDiffOn F w)
    (fun p hp => logPi_hasDerivAt F w p (interior_to_band hp.2)) hmem
  rw [pressureWeight_parameter F w hmem] at hd
  exact hd

end NavierStokes.HeatSwitchHistoryDerivatives

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.TerminalHistoryBridge

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open OutgoingProfile (Profile)
open HeatedOutgoing (CompensationWitness Coeff)

private theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-- Angular history, given by `∫ u in Ioc 0 X, HeatedOutgoing.H F XR c (u,η)`. -/
noncomputable def angularHistory (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (η X : ℝ) : ℝ := ∫ u in Ioc 0 X, HeatedOutgoing.H F XR c (u,η)

/-- Energy history, given by `∫ u in Ioc 0 X, HeatedOutgoing.energyDensity F XR c η u`. -/
noncomputable def energyHistory (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (η X : ℝ) : ℝ := ∫ u in Ioc 0 X, HeatedOutgoing.energyDensity F XR c η u

/-- Power history, given by `∫ u in Ioc 0 X, OutgoingDilation.powerH F XR u`. -/
noncomputable def powerHistory (F : Profile) (XR X : ℝ) : ℝ :=
  ∫ u in Ioc 0 X, OutgoingDilation.powerH F XR u

theorem split_positive_integral {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {X : ℝ} (hX : 0 ≤ X) :
    (∫ u in Ioc 0 X, f u) + (∫ u in Ioi X, f u) = ∫ u in Ioi 0, f u := by
  simpa only [Ioc_union_Ioi_eq_Ioi hX] using
    (setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf.mono_set Ioc_subset_Ioi_self) (hf.mono_set (Ioi_subset_Ioi hX))).symm

theorem angularHistory_integrable {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η X : ℝ}
    (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    IntegrableOn (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) (Ioc 0 X) := by
  have hi := (OutgoingDilation.I_integrable F XR η X w.radius_pos hX).add
    ((w.changeRow_integrable η 2 hη).mono_set Ioc_subset_Ioi_self)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioc
  intro u hu
  change Real.sqrt (2*u) * OutgoingDilation.E F XR (u,η) +
    Real.sqrt (2*u) * (HeatedOutgoing.E F XR w.coefficients (u,η) - OutgoingDilation.E F XR (u,η)) =
    Real.sqrt (2*u) * HeatedOutgoing.E F XR w.coefficients (u,η)
  ring

/-- The exact renormalized angular moment determines the forward history
from the future, for the very same supplied compensation coefficients. -/
theorem angularHistory_eq_power_sub_future {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η X : ℝ}
    (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : 0 < X) :
    angularHistory F XR w.coefficients η X = powerHistory F XR X -
      ∫ u in Ioi X, HeatedOutgoing.H F XR w.coefficients (u,η) -
        OutgoingDilation.powerH F XR u := by
  have hi := angularHistory_integrable w hη hX
  have hr : IntegrableOn (fun u => HeatedOutgoing.H F XR w.coefficients (u,η) -
      OutgoingDilation.powerH F XR u) (Ioc 0 X) :=
    (w.renormalized_integrable η hη).mono_set Ioc_subset_Ioi_self
  have hp : IntegrableOn (OutgoingDilation.powerH F XR) (Ioc 0 X) := by
    apply IntegrableOn.congr_fun (hi.sub hr) _ measurableSet_Ioc
    intro u hu
    dsimp
    ring
  have hsplit := split_positive_integral (w.renormalized_integrable η hη) hX.le
  rw [w.renormalized_zero η hη,integral_sub hi hp] at hsplit
  unfold angularHistory powerHistory
  linarith

theorem energyHistory_eq_neg_future {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : 0 ≤ X) :
    energyHistory F XR w.coefficients η X =
      -(∫ u in Ioi X, HeatedOutgoing.energyDensity F XR w.coefficients η u) := by
  have hs := split_positive_integral (w.energy_integrable η hη) hX
  have hz := w.energy_zero hF η hη
  unfold HeatedOutgoing.totalS at hz
  rw [hz] at hs
  unfold energyHistory
  linarith

theorem square_integrable_after_switch {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) {η X : ℝ}
    (hη : η ∈ HeatedOutgoing.parameterDomain) (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    IntegrableOn (fun u => HeatedOutgoing.E F XR w.coefficients (u,η)^2) (Ioi X) := by
  have hXp : 0 < X := (OutgoingDilation.switchRadius_pos F XR w.radius_pos).trans_le hX
  have hi := ((w.energy_integrable η hη).mono_set (Ioi_subset_Ioi hXp.le)).const_mul (-2)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [HeatedOutgoing.energyDensity,
    HeatedOutgoing.U_after_switch F XR η u w.radius_pos (hX.trans hu.le)]
  ring

theorem energyHistory_eq_square_future {F : Profile} {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η X : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain)
    (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    energyHistory F XR w.coefficients η X =
      (1/2 : ℝ) * ∫ u in Ioi X, HeatedOutgoing.E F XR w.coefficients (u,η)^2 := by
  have hXp : 0 < X := (OutgoingDilation.switchRadius_pos F XR w.radius_pos).trans_le hX
  rw [energyHistory_eq_neg_future hF w hη hXp.le]
  have he : (∫ u in Ioi X, HeatedOutgoing.energyDensity F XR w.coefficients η u) =
      ∫ u in Ioi X, -(HeatedOutgoing.E F XR w.coefficients (u,η)^2/2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    rw [HeatedOutgoing.energyDensity,
      HeatedOutgoing.U_after_switch F XR η u w.radius_pos (hX.trans hu.le)]
    ring
  rw [he,integral_neg,integral_div]
  ring

theorem transport_histories_zero_after_switch {F : Profile} {XR C : ℝ}
    (w : CompensationWitness F XR C) (η : ℝ) {X : ℝ}
    (hX : OutgoingDilation.switchRadius F XR ≤ X) :
    HeatedOutgoing.U F XR (X,η) = 0 ∧ HeatedOutgoing.M F XR η X = 0 ∧
      HeatedOutgoing.J F XR w.coefficients η X = 0 :=
  w.after_pulse η X ((OutgoingDilation.switchRadius_pos F XR w.radius_pos).trans_le hX)
    ((HeatedOutgoing.pulseEnd_le_switch F XR w.radius_pos).trans hX)

/-- Normalization, given by `TerminalPressure.releasedNormalization F.data
(OutgoingDilation.switchRadius F XR)`. -/
noncomputable def normalization (F : Profile) (XR : ℝ) : ℝ :=
  TerminalPressure.releasedNormalization F.data (OutgoingDilation.switchRadius F XR)

/-- Shift, given by `Real.log (OutgoingDilation.switchRadius F XR) - 1/5`. -/
noncomputable def shift (F : Profile) (XR : ℝ) : ℝ :=
  Real.log (OutgoingDilation.switchRadius F XR) - 1/5

/-- Physical angular, given by `SimilarityProfile.pullback F.data.h
(-TerminalPressure.amplitudeExponent F.data.h) (HeatedOutgoing.E F XR c)`. -/
noncomputable def physicalAngular (F : Profile) (XR : ℝ) (c : ℝ → Coeff) :
    SimilarityProfile.PhysicalProfile :=
  SimilarityProfile.pullback F.data.h (-TerminalPressure.amplitudeExponent F.data.h)
    (HeatedOutgoing.E F XR c)

/-- Physical pressure, given by `SimilarityProfile.pullback F.data.h
(-2*TerminalPressure.amplitudeExponent F.data.h) (HeatedOutgoing.Pi F XR c)`. -/
noncomputable def physicalPressure (F : Profile) (XR : ℝ) (c : ℝ → Coeff) :
    SimilarityProfile.PhysicalProfile :=
  SimilarityProfile.pullback F.data.h (-2*TerminalPressure.amplitudeExponent F.data.h)
    (HeatedOutgoing.Pi F XR c)

theorem physicalAngular_eq_terminal (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → Coeff) {p : SimilarityProfile.PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    physicalAngular F XR c p =
      TerminalStress.physicalHeat (normalization F XR) (1+F.data.h) p *
        TerminalPressure.outgoingTaper F.data (shift F XR) (Real.log (SimilarityProfile.X F.data.h
            p)) := by
  have hK := OutgoingDilation.switchRadius_pos F XR hXR
  have hX := div_pos hs (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht)
  unfold physicalAngular SimilarityProfile.pullback SimilarityProfile.inner
  rw [HeatedOutgoing.E_after_switch F XR c (SimilarityProfile.eta F.data.h p)
    (SimilarityProfile.X F.data.h p) hXR (HeatedOutgoing.full_switch_above_radius hK hX hfull)]
  exact TerminalPressure.physicalEdit_eq_released_carrier F.data hK ht hs hfull

theorem full_switch_radial {F : Profile} {XR : ℝ} (hXR : 0 < XR)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) {u : ℝ} (hu : p.2.1 ≤ u) :
    1/2 ≤ Real.log (SimilarityProfile.X F.data.h (p.1,(u,p.2.2)) /
      OutgoingDilation.switchRadius F XR) + 1/5 := by
  have hq := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have hK := OutgoingDilation.switchRadius_pos F XR hXR
  have hX : 0 < SimilarityProfile.X F.data.h p := div_pos hs hq
  have hle : SimilarityProfile.X F.data.h p ≤ SimilarityProfile.X F.data.h (p.1,(u,p.2.2)) := by
    change p.2.1 / SimilarityProfile.q F.data.h p ≤ u / SimilarityProfile.q F.data.h p
    exact div_le_div_of_nonneg_right hu hq.le
  have hlog := Real.log_le_log (div_pos hX hK) (div_le_div_of_nonneg_right hle hK.le)
  linarith

/-- Exact physical canonical pressure, with its required `q^(-2A)` factor.
This is a change of variables in the actual improper integral. -/
theorem physicalPressure_eq_terminal (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → Coeff) {p : SimilarityProfile.PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 ≤ Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    physicalPressure F XR c p =
      TerminalPressure.outgoingPressure (normalization F XR) F.data (shift F XR) p := by
  let q := SimilarityProfile.q F.data.h p
  let η := SimilarityProfile.eta F.data.h p
  let A := TerminalPressure.amplitudeExponent F.data.h
  have hq : 0 < q := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have hpow : (q^(-A))^2 = q^(-2*A) := by
    rw [pow_two,← Real.rpow_add hq]
    congr 1
    ring
  have heq : ∀ u ∈ Ioi p.2.1,
      TerminalStress.swirlCoefficient (normalization F XR) F.data.h
          (TerminalPressure.outgoingTaper F.data (shift F XR)) (p.1,(u,p.2.2)) ^ 2 =
        (q^(-2*A)/(2*q)) * HeatedOutgoing.canonicalKernel F XR c η (u/q) := by
    intro u hu
    have hup : 0 < u := hs.trans hu
    have ha := physicalAngular_eq_terminal F hXR c (p := (p.1,(u,p.2.2))) ht hup
      (full_switch_radial hXR ht hs hfull (u := u) hu.le)
    change q^(-A) * HeatedOutgoing.E F XR c (u/q,η) = _ at ha
    change ((TerminalStress.physicalHeat (normalization F XR) (1+F.data.h) (p.1,(u,p.2.2)) *
      TerminalPressure.outgoingTaper F.data (shift F XR)
        (Real.log (SimilarityProfile.X F.data.h (p.1,(u,p.2.2))))) / Real.sqrt (2*u))^2 = _
    rw [← ha,div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*u),hpow]
    unfold HeatedOutgoing.canonicalKernel
    field_simp [hq.ne',hup.ne']
  have hi := setIntegral_congr_fun (μ := volume) measurableSet_Ioi heq
  change q^(-2*A) * (-(1/2 : ℝ) * ∫ u in Ioi (p.2.1/q),
      HeatedOutgoing.canonicalKernel F XR c η u) =
    -(∫ u in Ioi p.2.1, TerminalStress.swirlCoefficient (normalization F XR) F.data.h
      (TerminalPressure.outgoingTaper F.data (shift F XR)) (p.1,(u,p.2.2))^2)
  rw [hi,integral_const_mul,OutgoingDilation.integral_dilate_Ioi
    (HeatedOutgoing.canonicalKernel F XR c η) q p.2.1 hq]
  field_simp [hq.ne']

/-! ## The actual forward stress on the switched tail -/

/-- Forward theta, constructed using `HeatSwitchCone.logE`. -/
noncomputable def forwardTheta (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (p : ℝ × ℝ) : ℝ :=
  HeatSwitchCone.logE F XR c p / Real.sqrt (2 * XR * Real.exp p.1) *
    (XR * Real.exp p.1 * HeatSwitchCone.Qs F XR c p /
      CoordinateAlgebra.L F.data.h p.2 - HeatSwitchCone.radialA F XR c p)

/-- Forward axial, given by `XR * Real.exp p.1 * HeatSwitchCone.Ns F XR c p /
(CoordinateAlgebra.L F.data.h p.2 * Real.sqrt (2 * XR * Real.exp p.1))`. -/
noncomputable def forwardAxial (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    (p : ℝ × ℝ) : ℝ :=
  XR * Real.exp p.1 * HeatSwitchCone.Ns F XR c p /
    (CoordinateAlgebra.L F.data.h p.2 * Real.sqrt (2 * XR * Real.exp p.1))

theorem terminalStart_after_endpoint (F : Profile) :
    F.data.core.endpoint < TerminalCone.terminalStart F.data := by
  have hr := OutgoingTail.releaseStart_gt_flattenEnd F.data
  have ht := OutgoingTail.tailStart_gt_release F.data
  dsimp only [TerminalCone.terminalStart]
  have hf := OutgoingTail.flattenEnd_gt_core F.data
  linarith

theorem Qs_after_endpoint (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    {p : ℝ × ℝ} (hp : F.data.core.endpoint ≤ p.1) :
    HeatSwitchCone.Qs F XR c p = -1 +
      ((1-F.data.h)*HeatSwitchCone.logI F XR c p -
        StressAlgebra.axialExponent F.data.h * p.2 *
        derivWithin (fun η => HeatSwitchCone.logI F XR c (p.1,η))
          HeatedOutgoing.parameterDomain p.2) /
        (Real.exp (3*p.1/2)*HeatSwitchCone.logE F XR c p) := by
  simp only [HeatSwitchCone.Qs,
    OutgoingHistories.W_after_endpoint F.data F.amp_contDiff p.2 hp,
    OutgoingHistories.J_after_endpoint F.reset F.amp p.2 hp,
    OutgoingHistories.dEta_J_after_endpoint F.reset F.amp_contDiff p.2 hp,
    mul_zero, sub_zero, add_zero]

theorem Ns_after_endpoint (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    {p : ℝ × ℝ} (hp : F.data.core.endpoint ≤ p.1) :
    HeatSwitchCone.Ns F XR c p =
      (4*F.data.h*p.2*HeatSwitchCone.logS F XR c p -
        StressAlgebra.coordinateFactor p.2 *
        derivWithin (fun η => HeatSwitchCone.logS F XR c (p.1,η))
          HeatedOutgoing.parameterDomain p.2) / Real.exp p.1 +
      4*StressAlgebra.velocityExponent F.data.h*p.2*HeatSwitchCone.logPi F XR c p -
        StressAlgebra.coordinateFactor p.2 *
        derivWithin (fun η => HeatSwitchCone.logPi F XR c (p.1,η))
          HeatedOutgoing.parameterDomain p.2 := by
  simp only [HeatSwitchCone.Ns, OutgoingHistories.M_after_endpoint F.data F.amp p.2 hp,
    OutgoingHistories.dEta_M_after_endpoint F.data F.amp_contDiff p.2 hp,
    show F.logU p = 0 from F.logU_after p.2 hp,
    mul_zero, sub_zero, zero_div, add_zero, zero_add]

theorem radialB_after_endpoint (F : Profile) (XR : ℝ) (c : ℝ → Coeff)
    {p : ℝ × ℝ} (hp : F.data.core.endpoint < p.1) :
    HeatSwitchCone.radialB F XR c p = 0 := by
  have he : (fun y => F.logU (y,p.2)) =ᶠ[𝓝 p.1] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hp] with y hy
    exact F.logU_after p.2 hy.le
  rw [HeatSwitchCone.radialB, OutgoingHistories.dY_eq_deriv F.logU_contDiff,
    he.deriv_eq, deriv_const, mul_zero, zero_div]

theorem radialA_eq_profileSpeed (F : Profile) {XR C : ℝ}
    (w : CompensationWitness F XR C) {y η : ℝ}
    (hy : TerminalCone.terminalStart F.data < y)
    (hη : η ∈ HeatedOutgoing.parameterDomain) :
    HeatSwitchCone.radialA F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
        (TerminalCone.profilePoint F y η) := by
  let g : ℝ → ℝ := fun v => TerminalEdgeFactor.profileAngularVelocity
    (normalization F XR) F.data (shift F XR) (η,OutgoingTail.tailEnd F.data-v)
  have he : (fun v => HeatSwitchCone.logE F XR w.coefficients (v,η)) =ᶠ[𝓝 y] g := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact TerminalCone.E_eq_profileAngularVelocity F w.coefficients w.radius_pos hv.le hη
  have hd := ((TerminalEdgeFactor.profileAngularVelocity_hasDerivAt_edge
    (normalization F XR) F.data (shift F XR) η (OutgoingTail.tailEnd F.data-y)).comp y
      ((hasDerivAt_id y).const_sub (OutgoingTail.tailEnd F.data)))
  have hC : 0 < normalization F XR := TerminalPressure.releasedNormalization_pos F.data
    (OutgoingDilation.switchRadius_pos F XR w.radius_pos)
  have hev : HeatSwitchCone.logE F XR w.coefficients (y,η) = g y := he.self_of_nhds
  change HeatSwitchCone.radialA F XR w.coefficients (y,η) =
    TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
      (η,OutgoingTail.tailEnd F.data-y)
  rw [HeatSwitchCone.radialA, he.deriv_eq, hev,
    TerminalEdgeFactor.profileSpeed_eq_log_deriv hC F.data (shift F XR) η
      (OutgoingTail.tailEnd F.data-y) hη,
    (TerminalEdgeFactor.profileAngularVelocity_hasDerivAt_edge
      (normalization F XR) F.data (shift F XR) η (OutgoingTail.tailEnd F.data-y)).deriv]
  change 1-2*deriv g y/g y = _
  have hdg : deriv g y = _ := hd.deriv
  rw [hdg]
  dsimp only [g, Function.comp_def, TerminalCone.profilePoint, TerminalCone.edgeDistance]
  ring

theorem forward_normalization (F : Profile) {XR C : ℝ}
    (w : CompensationWitness F XR C) {p : ℝ × ℝ}
    (hp : F.data.core.endpoint < p.1)
    (hη : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hQ : HeatSwitchCone.Qs F XR w.coefficients p ≠ 0) :
    HeatSwitchCone.normalP F XR w.coefficients p =
      HeatSwitchCone.radialA F XR w.coefficients p +
        forwardTheta F XR w.coefficients p /
          (HeatSwitchCone.logE F XR w.coefficients p / Real.sqrt (2*XR*Real.exp p.1)) ∧
    HeatSwitchCone.normalJ F XR w.coefficients p =
      forwardAxial F XR w.coefficients p /
        (HeatSwitchCone.logE F XR w.coefficients p / Real.sqrt (2*XR*Real.exp p.1)) := by
  have hE : HeatSwitchCone.logE F XR w.coefficients p ≠ 0 :=
    (w.positive p.2 (XR*Real.exp p.1) hη (mul_pos w.radius_pos (Real.exp_pos _))).ne'
  have hR : Real.sqrt (2*XR*Real.exp p.1) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) w.radius_pos) (Real.exp_pos _))).ne'
  have hL : CoordinateAlgebra.L F.data.h p.2 ≠ 0 :=
    (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half
      (TerminalEdgeFactor.eta_sq_le_one hη)).ne'
  simp only [HeatSwitchCone.normalP,HeatSwitchCone.normalJ,HeatSwitchCone.sourceC,
    HeatSwitchCone.sourceJ, radialB_after_endpoint F XR w.coefficients hp,
    zero_mul,zero_div,sub_zero,mul_one,add_zero]
  unfold forwardTheta forwardAxial HeatSwitchCone.stressScale HeatSwitchCone.ratio
  generalize Real.sqrt (2*XR*Real.exp p.1) = r at *
  constructor <;> field_simp [hE,hR,hL,hQ] ; ring

/-! ## Exact change from logarithmic to physical histories -/

theorem integral_log_radius (f : ℝ → ℝ) {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    (∫ u in Ioc 0 (XR*Real.exp y), f u) =
      XR * ∫ t in Iic y, Real.exp t * f (XR*Real.exp t) := by
  calc
    _ = ∫ u in Ioc 0 (XR*Real.exp y), (fun v => f (XR*v)) (u/XR) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [mul_div_cancel₀ u hXR.ne']
    _ = XR * ∫ v in Ioc 0 (Real.exp y), f (XR*v) := by
      simpa only [mul_div_cancel_left₀ _ hXR.ne'] using
        OutgoingDilation.integral_dilate_Ioc (fun v => f (XR*v)) XR (XR*Real.exp y) hXR
    _ = _ := by
      rw [← ReleaseMoments.image_exp_Iic,
        integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
          (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
      simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul]

theorem sqrt_radius_exp {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    Real.sqrt (2*(XR*Real.exp y)) = Real.sqrt (2*XR)*Real.exp (y/2) := by
  rw [← mul_assoc,Real.sqrt_mul (by positivity : 0 ≤ 2*XR)]
  congr 1
  exact (Real.exp_half y).symm

theorem angularHistory_eq_logI (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → Coeff) {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (y : ℝ) :
    angularHistory F XR c η (XR*Real.exp y) =
      (XR*Real.sqrt (2*XR))*HeatSwitchCone.logI F XR c (y,η) := by
  unfold angularHistory
  rw [integral_log_radius _ hXR, (HeatSwitchCone.logI_eq_past_integral F hXR c hη y).2]
  have he : (∫ t in Iic y, Real.exp t * HeatedOutgoing.H F XR c (XR*Real.exp t,η)) =
      Real.sqrt (2*XR) * ∫ t in Iic y,
        Real.exp (3*t/2)*HeatSwitchCone.logE F XR c (t,η) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    dsimp only
    rw [HeatedOutgoing.H,sqrt_radius_exp hXR]
    unfold HeatSwitchCone.logE
    rw [show 3*t/2=t+t/2 by ring,Real.exp_add]
    ring
  rw [he]
  ring

theorem energyHistory_eq_logS (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (c : ℝ → Coeff) {η : ℝ} (hη : η ∈ HeatedOutgoing.parameterDomain) (y : ℝ) :
    energyHistory F XR c η (XR*Real.exp y) = XR*HeatSwitchCone.logS F XR c (y,η) := by
  unfold energyHistory
  rw [integral_log_radius _ hXR, (HeatSwitchCone.logS_eq_past_integral F hXR c hη y).2]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t ht
  simp only [HeatedOutgoing.energyDensity,HeatSwitchCone.logE,HeatedOutgoing.U,
    OutgoingDilation.U,OutgoingProfile.Profile.U,mul_div_cancel_left₀ _ hXR.ne',Real.log_exp]

open HeatSwitchCone (logE logI logS logPi)
open ProfileHistories (radialPartial parameterPartial)

/-- Eta derivative, given by `derivWithin (fun η => G (p.1,η)) HeatedOutgoing.parameterDomain
p.2`. -/
noncomputable def etaDerivative (G : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ :=
  derivWithin (fun η => G (p.1,η)) HeatedOutgoing.parameterDomain p.2

/-- Theta stock as an element of `ℝ`. -/
noncomputable def thetaStock (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  (1-F.data.h)*logI F XR c p - StressAlgebra.axialExponent F.data.h*p.2 *
    etaDerivative (logI F XR c) p - Real.exp (3*p.1/2)*logE F XR c p

/-- Theta weight as an element of `ℝ`. -/
noncomputable def thetaWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  (XR*Real.sqrt (2*XR))*thetaStock F XR c p / CoordinateAlgebra.L F.data.h p.2 +
    Real.sqrt (2*XR)*Real.exp (p.1/2) *
      (2*radialPartial (logE F XR c) p-logE F XR c p)

/-- Axial weight as an element of `ℝ`. -/
noncomputable def axialWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  (XR*(4*F.data.h*p.2*logS F XR c p - StressAlgebra.coordinateFactor p.2 *
    etaDerivative (logS F XR c) p) + XR*Real.exp p.1 *
    (4*StressAlgebra.velocityExponent F.data.h*p.2*logPi F XR c p -
      StressAlgebra.coordinateFactor p.2*etaDerivative (logPi F XR c) p)) /
        CoordinateAlgebra.L F.data.h p.2

/-- Angular residual as an element of `ℝ`. -/
noncomputable def angularResidual (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  (StressAlgebra.velocityExponent F.data.h*logE F XR c p +
    StressAlgebra.axialExponent F.data.h*p.2*etaDerivative (logE F XR c) p +
    radialPartial (logE F XR c) p) / CoordinateAlgebra.L F.data.h p.2 -
      (2*radialPartial (radialPartial (logE F XR c)) p-logE F XR c p/2) / (XR*Real.exp p.1)

/-- Axial residual as an element of `ℝ`. -/
noncomputable def axialResidual (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  (-4*StressAlgebra.velocityExponent F.data.h*p.2*logPi F XR c p +
    StressAlgebra.coordinateFactor p.2*etaDerivative (logPi F XR c) p -
    p.2*logE F XR c p^2) / CoordinateAlgebra.L F.data.h p.2

theorem thetaStock_hasDerivAt (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hp : p.2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun y => thetaStock F XR w.coefficients (y,p.2))
      (-Real.exp (3*p.1/2)*(StressAlgebra.velocityExponent F.data.h*logE F XR w.coefficients p +
        StressAlgebra.axialExponent F.data.h*p.2*etaDerivative (logE F XR w.coefficients) p +
        radialPartial (logE F XR w.coefficients) p)) p.1 := by
  have hi := HeatSwitchHistoryDerivatives.logI_hasDerivAt F w p ⟨hp.1.le,hp.2.le⟩
  have him := HeatSwitchHistoryDerivatives.logI_eta_hasDerivAt F w p hp
  have he := ProfileHistories.radialPartial_hasDerivAt
    HeatSwitchHistoryDerivatives.interiorDomain (HeatSwitchHistoryDerivatives.logE_contDiffOn F w)
      (show p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hp⟩)
  have hex := (((hasDerivAt_id p.1).const_mul (3 : ℝ)).div_const 2).exp
  have hd := ((hi.const_mul (1-F.data.h)).sub
    (him.const_mul (StressAlgebra.axialExponent F.data.h*p.2))).sub (hex.mul he)
  convert! hd using 1
  dsimp only [thetaStock,etaDerivative,StressAlgebra.velocityExponent,id_eq]
  ring

theorem thetaWeight_hasDerivAt (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hp : p.2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun y => thetaWeight F XR w.coefficients (y,p.2))
      (-(XR*Real.exp p.1)*Real.sqrt (2*(XR*Real.exp p.1))*angularResidual F XR w.coefficients p)
          p.1 := by
  have hm : p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier := ⟨mem_univ _,hp⟩
  have hs := HeatSwitchHistoryDerivatives.logE_contDiffOn F w
  have he := ProfileHistories.radialPartial_hasDerivAt HeatSwitchHistoryDerivatives.interiorDomain
      hs hm
  have he' := ProfileHistories.radialPartial_hasDerivAt HeatSwitchHistoryDerivatives.interiorDomain
    (ProfileHistories.radialPartial_smooth HeatSwitchHistoryDerivatives.interiorDomain hs) hm
  have hx := ((hasDerivAt_id p.1).div_const 2).exp
  have hd := (((thetaStock_hasDerivAt F w hp).const_mul (XR*Real.sqrt (2*XR))).div_const
    (CoordinateAlgebra.L F.data.h p.2)).fun_add
      ((hx.const_mul (Real.sqrt (2*XR))).fun_mul ((he'.const_mul 2).fun_sub he))
  convert! hd using 1
  dsimp only [thetaWeight,angularResidual,id_eq]
  rw [sqrt_radius_exp w.radius_pos,
    show 3*p.1/2=p.1+p.1/2 by ring,Real.exp_add]
  have hX : XR*Real.exp p.1 ≠ 0 := mul_ne_zero w.radius_pos.ne' (Real.exp_ne_zero _)
  have hL : CoordinateAlgebra.L F.data.h p.2 ≠ 0 :=
    (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half
      (TerminalEdgeFactor.eta_sq_le_one ⟨hp.1.le,hp.2.le⟩)).ne'
  field_simp [hX,hL,w.radius_pos.ne',Real.exp_ne_zero]; ring

theorem axialWeight_hasDerivAt (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hp : p.2 ∈ Ioo (-1) 1) (hy : F.data.core.endpoint ≤ p.1) :
    HasDerivAt (fun y => axialWeight F XR w.coefficients (y,p.2))
      (-(XR*Real.exp p.1)*axialResidual F XR w.coefficients p) p.1 := by
  have hs := HeatSwitchHistoryDerivatives.logS_hasDerivAt F w p ⟨hp.1.le,hp.2.le⟩
  have hsm := HeatSwitchHistoryDerivatives.logS_eta_hasDerivAt F w p hp
  have hP := HeatSwitchHistoryDerivatives.logPi_hasDerivAt F w p ⟨hp.1.le,hp.2.le⟩
  have hPm := HeatSwitchHistoryDerivatives.logPi_eta_hasDerivAt F w p hp
  have hd := ((((hs.const_mul (4*F.data.h*p.2)).fun_sub
    (hsm.const_mul (StressAlgebra.coordinateFactor p.2))).const_mul XR).fun_add
    (((Real.hasDerivAt_exp p.1).const_mul XR).fun_mul
      ((hP.const_mul (4*StressAlgebra.velocityExponent F.data.h*p.2)).fun_sub
        (hPm.const_mul (StressAlgebra.coordinateFactor p.2))))).div_const
          (CoordinateAlgebra.L F.data.h p.2)
  convert! hd using 1
  dsimp only [axialWeight,axialResidual,etaDerivative]
  rw [F.logU_after p.2 hy]
  unfold StressAlgebra.velocityExponent
  ring

theorem thetaWeight_eq_forward (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hp : p.2 ∈ Ioo (-1) 1) (hy : F.data.core.endpoint ≤ p.1) :
    thetaWeight F XR w.coefficients p =
      2*(XR*Real.exp p.1)*forwardTheta F XR w.coefficients p := by
  have he := ProfileHistories.radialPartial_hasDerivAt
    HeatSwitchHistoryDerivatives.interiorDomain (HeatSwitchHistoryDerivatives.logE_contDiffOn F w)
      (show p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hp⟩)
  have hE : logE F XR w.coefficients p ≠ 0 :=
    (w.positive p.2 (XR*Real.exp p.1) ⟨hp.1.le,hp.2.le⟩ (mul_pos w.radius_pos (Real.exp_pos _))).ne'
  have hL : CoordinateAlgebra.L F.data.h p.2 ≠ 0 :=
    (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half
      (TerminalEdgeFactor.eta_sq_le_one ⟨hp.1.le,hp.2.le⟩)).ne'
  have hR : Real.sqrt (2*XR) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos (by norm_num) w.radius_pos)).ne'
  have hR2 := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) w.radius_pos.le)
  unfold thetaWeight forwardTheta HeatSwitchCone.radialA thetaStock etaDerivative
  rw [Qs_after_endpoint F XR w.coefficients hy,he.deriv,
    show 2*XR*Real.exp p.1=2*(XR*Real.exp p.1) by ring,sqrt_radius_exp w.radius_pos,
    show 3*p.1/2=p.1+p.1/2 by ring,Real.exp_add]
  generalize Real.sqrt (2*XR) = r at *
  field_simp [hE,hL,hR,Real.exp_ne_zero]
  have hx : XR=r^2/2 := by linarith [hR2]
  have hex : Real.exp p.1 = Real.exp (p.1/2)^2 := by
    rw [pow_two,← Real.exp_add,add_halves]
  generalize logE F XR w.coefficients p = e
  generalize radialPartial (logE F XR w.coefficients) p = ey
  generalize logI F XR w.coefficients p = i
  generalize derivWithin (fun η => logI F XR w.coefficients (p.1,η))
    HeatedOutgoing.parameterDomain p.2 = im
  rw [hx,hex]
  ring

theorem axialWeight_eq_forward (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hy : F.data.core.endpoint ≤ p.1) :
    axialWeight F XR w.coefficients p =
      Real.sqrt (2*XR*Real.exp p.1)*forwardAxial F XR w.coefficients p := by
  have hR : Real.sqrt (2*XR*Real.exp p.1) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) w.radius_pos) (Real.exp_pos _))).ne'
  unfold axialWeight forwardAxial etaDerivative
  rw [Ns_after_endpoint F XR w.coefficients hy]
  generalize Real.sqrt (2*XR*Real.exp p.1) = r at *
  by_cases hL : CoordinateAlgebra.L F.data.h p.2 = 0
  · simp [hL]
  field_simp [hR,hL,Real.exp_ne_zero]; ring

/-! ## Genuine physical derivatives of logarithmic profiles -/

/-- Log point, given by `(Real.log (p.1/XR),p.2)`. -/
noncomputable def logPoint (XR : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Real.log (p.1/XR),p.2)
/-- Radial lift, given by `G (logPoint XR p)`. -/
noncomputable def radialLift (XR : ℝ) (G : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : ℝ := G (logPoint XR p)

theorem logPoint_contDiffAt {XR : ℝ} (hXR : 0 < XR) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (logPoint XR) p :=
  ((contDiffAt_fst.div_const XR).log (div_pos hp hXR).ne').prodMk contDiffAt_snd

theorem radialLift_contDiffAt {XR : ℝ} (hXR : 0 < XR) {G : (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G HeatSwitchHistoryDerivatives.interiorDomain.carrier)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hη : p.2 ∈ Ioo (-1) 1) :
    ContDiffAt ℝ ∞ (radialLift XR G) p :=
  (hG.contDiffAt (HeatSwitchHistoryDerivatives.interiorDomain.isOpen.mem_nhds
    (show logPoint XR p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from
      ⟨mem_univ _,hη⟩))).comp p (logPoint_contDiffAt hXR hp)

theorem log_radius_hasDerivAt {XR X : ℝ} (hXR : 0 < XR) (hX : 0 < X) :
    HasDerivAt (fun x => Real.log (x/XR)) (1/X) X := by
  convert! ((hasDerivAt_id X).div_const XR).log (div_pos hX hXR).ne' using 1
  simp only [id_eq]
  field_simp [hXR.ne',hX.ne']

theorem radialLift_partialX {XR : ℝ} (hXR : 0 < XR) {G : (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G HeatSwitchHistoryDerivatives.interiorDomain.carrier)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hη : p.2 ∈ Ioo (-1) 1) :
    SimilarityProfile.partialX (radialLift XR G) p = radialPartial G (logPoint XR p)/p.1 := by
  have hg := (hG.contDiffAt (HeatSwitchHistoryDerivatives.interiorDomain.isOpen.mem_nhds
    (show logPoint XR p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from
      ⟨mem_univ _,hη⟩))).differentiableAt (by simp)
  have hd := hg.hasFDerivAt.comp_hasDerivAt p.1
    ((log_radius_hasDerivAt hXR hp).prodMk (hasDerivAt_const p.1 p.2))
  have hh := LeadingStress.partialX_hasDerivAt ((radialLift_contDiffAt hXR hG hp
      hη).differentiableAt (by
      simp))
  have he := hh.unique hd
  rw [SimilarityProfile.fderiv_inner_apply] at he
  simp only [mul_zero,add_zero,mul_one_div] at he
  exact he

theorem radialLift_partialEta {XR : ℝ} (hXR : 0 < XR) {G : (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G HeatSwitchHistoryDerivatives.interiorDomain.carrier)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hη : p.2 ∈ Ioo (-1) 1) :
    SimilarityProfile.partialEta (radialLift XR G) p = parameterPartial G (logPoint XR p) := by
  have hg := (hG.contDiffAt (HeatSwitchHistoryDerivatives.interiorDomain.isOpen.mem_nhds
    (show logPoint XR p ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from
      ⟨mem_univ _,hη⟩))).differentiableAt (by simp)
  have hd := hg.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 (Real.log (p.1/XR))).prodMk (hasDerivAt_id p.2))
  have hh := ((radialLift_contDiffAt hXR hG hp hη).differentiableAt (by
      simp)).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have he := hh.unique hd
  simpa only [SimilarityProfile.partialEta,parameterPartial] using he

theorem radialLift_partialXX {XR : ℝ} (hXR : 0 < XR) {G : (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G HeatSwitchHistoryDerivatives.interiorDomain.carrier)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hη : p.2 ∈ Ioo (-1) 1) :
    SimilarityProfile.partialX (SimilarityProfile.partialX (radialLift XR G)) p =
      (radialPartial (radialPartial G) (logPoint XR p)-radialPartial G (logPoint XR p))/p.1^2 := by
  have hG' := ProfileHistories.radialPartial_smooth HeatSwitchHistoryDerivatives.interiorDomain hG
  have hl := radialLift_contDiffAt hXR hG hp hη
  have he : (fun x => SimilarityProfile.partialX (radialLift XR G) (x,p.2)) =ᶠ[𝓝 p.1]
      fun x => radialLift XR (radialPartial G) (x,p.2)/x := by
    filter_upwards [Ioi_mem_nhds hp] with x hx
    exact radialLift_partialX hXR hG hx hη
  have hd := ((LeadingStress.partialX_hasDerivAt
    ((radialLift_contDiffAt hXR hG' hp hη).differentiableAt (by simp))).div
      (hasDerivAt_id p.1) hp.ne').congr_of_eventuallyEq he
  have hder := LeadingStress.partialX_hasDerivAt
    ((SimilarityProfile.partialX_smoothAt hl (m := ∞) (by simp)).differentiableAt (by simp))
  rw [radialLift_partialX hXR hG' hp hη] at hd
  have hh := hder.unique hd
  exact hh.trans (by dsimp [radialLift]; field_simp [hp.ne'])

theorem logE_radialLift (F : Profile) {XR : ℝ} (hXR : 0 < XR) (c : ℝ → Coeff)
    {p : ℝ × ℝ} (hp : 0 < p.1) : radialLift XR (logE F XR c) p = HeatedOutgoing.E F XR c p := by
  unfold radialLift logPoint logE
  dsimp only
  rw [Real.exp_log (div_pos hp hXR),mul_div_cancel₀ _ hXR.ne',Prod.mk.eta]

theorem logPi_radialLift (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : ℝ × ℝ} (hp : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    radialLift XR (logPi F XR w.coefficients) p = HeatedOutgoing.Pi F XR w.coefficients p := by
  unfold radialLift
  rw [HeatSwitchCone.logPi_eq_canonical F w (logPoint XR p) hη]
  dsimp only [logPoint]
  rw [Real.exp_log (div_pos hp w.radius_pos),mul_div_cancel₀ _ w.radius_pos.ne',Prod.mk.eta]

/-- Physical log, given by `SimilarityProfile.pullback h b (radialLift XR G)`. -/
noncomputable def physicalLog (h b XR : ℝ) (G : (ℝ × ℝ) → ℝ) : SimilarityProfile.PhysicalProfile :=
  SimilarityProfile.pullback h b (radialLift XR G)

/-- Amplitude operator, constructed using `SimilarityProfile.partialT`. -/
noncomputable def amplitudeOperator (V : SimilarityProfile.PhysicalProfile)
    (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  SimilarityProfile.partialT V p - 2*p.2.1*SimilarityProfile.partialS (SimilarityProfile.partialS
      V) p -
    2*SimilarityProfile.partialS V p + V p/(2*p.2.1)

theorem physicalLog_amplitudeOperator {h b XR : ℝ} (hh : 0 < h) (hh' : h < 1 / 2) (hXR : 0 < XR)
    {G : (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G HeatSwitchHistoryDerivatives.interiorDomain.carrier)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    amplitudeOperator (physicalLog h b XR G) p =
      SimilarityProfile.q h p^(b-1) *
        (((-b)*G (logPoint XR (SimilarityProfile.inner h p)) +
          CoordinateAlgebra.D h*SimilarityProfile.eta h p*parameterPartial G (logPoint XR
              (SimilarityProfile.inner h p)) +
          radialPartial G (logPoint XR (SimilarityProfile.inner h p))) /
            CoordinateAlgebra.L h (SimilarityProfile.eta h p) -
          (2*radialPartial (radialPartial G) (logPoint XR (SimilarityProfile.inner h p)) -
            G (logPoint XR (SimilarityProfile.inner h p))/2)/SimilarityProfile.X h p) := by
  have hq := SimilarityProfile.q_pos hh hh' ht
  have hx : 0 < (SimilarityProfile.inner h p).1 := div_pos hs hq
  have heta : (SimilarityProfile.inner h p).2 ∈ Ioo (-1) 1 := by
    change SimilarityProfile.eta h p ∈ Ioo (-1) 1
    have he := SimilarityProfile.eta_sq_lt_one hh hh' ht
    constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta h p+1),sq_nonneg
        (SimilarityProfile.eta h p-1)]
  have hd := radialLift_contDiffAt hXR hG hx heta
  have hL := SimilarityProfile.L_pos hh hh' ht
  unfold amplitudeOperator physicalLog
  rw [SimilarityProfile.partialT_pullback hh hh' ht (hd.differentiableAt (by simp)),
    SimilarityProfile.partialS_partialS_pullback hh hh' ht (hd.of_le two_le_infty),
    SimilarityProfile.partialS_pullback hh hh' ht (hd.differentiableAt (by simp))]
  simp only [SimilarityProfile.pullback,SimilarityProfile.T,CoordinateAlgebra.timeCoeff]
  rw [radialLift_partialX hXR hG hx heta,radialLift_partialEta hXR hG hx heta,
    radialLift_partialXX hXR hG hx heta]
  simp only [radialLift,SimilarityProfile.inner]
  rw [show b-2=(b-1)-1 by ring]
  simp only [Real.rpow_sub_one hq.ne']
  rw [← SlowExpansionResidual.q_mul_X hh hh' ht]
  dsimp only [SimilarityProfile.inner] at hx ⊢
  field_simp [hq.ne',hx.ne',hL.ne']; ring

theorem physicalLog_angularResidual (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    amplitudeOperator (physicalLog F.data.h (-TerminalPressure.amplitudeExponent F.data.h)
      XR (logE F XR w.coefficients)) p =
      SimilarityProfile.q F.data.h p^(-TerminalPressure.amplitudeExponent F.data.h-1) *
        angularResidual F XR w.coefficients (logPoint XR (SimilarityProfile.inner F.data.h p)) := by
  rw [physicalLog_amplitudeOperator F.data.h_pos F.data.h_lt_half w.radius_pos
    (HeatSwitchHistoryDerivatives.logE_contDiffOn F w) ht hs]
  have hx : 0 < SimilarityProfile.X F.data.h p :=
    div_pos hs (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht)
  have heta : SimilarityProfile.eta F.data.h p ∈ Ioo (-1) 1 := by
    have he := SimilarityProfile.eta_sq_lt_one F.data.h_pos F.data.h_lt_half ht
    constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta F.data.h p+1),sq_nonneg
        (SimilarityProfile.eta F.data.h p-1)]
  have hp : logPoint XR (SimilarityProfile.inner F.data.h p) ∈
      HeatSwitchHistoryDerivatives.interiorDomain.carrier :=
    ⟨mem_univ _,heta⟩
  unfold angularResidual etaDerivative
  rw [HeatSwitchHistoryDerivatives.within_parameter_eq
      (HeatSwitchHistoryDerivatives.logE_contDiffOn F w) hp]
  simp only [logPoint,SimilarityProfile.inner,Real.exp_log (div_pos hx w.radius_pos),
    mul_div_cancel₀ _
        w.radius_pos.ne',TerminalPressure.amplitudeExponent,StressAlgebra.velocityExponent,
    StressAlgebra.axialExponent,CoordinateAlgebra.D,neg_neg]

theorem physicalLog_axialResidual (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SimilarityProfile.partialZ (physicalLog F.data.h (-2*TerminalPressure.amplitudeExponent
        F.data.h)
      XR (logPi F XR w.coefficients)) p =
      SimilarityProfile.q F.data.h p^(-TerminalPressure.amplitudeExponent F.data.h-1) *
        axialResidual F XR w.coefficients (logPoint XR (SimilarityProfile.inner F.data.h p)) := by
  have hq := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have hx : 0 < (SimilarityProfile.inner F.data.h p).1 := div_pos hs hq
  have heta : (SimilarityProfile.inner F.data.h p).2 ∈ Ioo (-1) 1 := by
    change SimilarityProfile.eta F.data.h p ∈ Ioo (-1) 1
    have he := SimilarityProfile.eta_sq_lt_one F.data.h_pos F.data.h_lt_half ht
    constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta F.data.h p+1),sq_nonneg
        (SimilarityProfile.eta F.data.h p-1)]
  have hm : logPoint XR (SimilarityProfile.inner F.data.h p) ∈
      HeatSwitchHistoryDerivatives.interiorDomain.carrier :=
    ⟨mem_univ _,heta⟩
  have hg := HeatSwitchHistoryDerivatives.logPi_contDiffOn F w
  have hd := radialLift_contDiffAt w.radius_pos hg hx heta
  have hp := HeatSwitchHistoryDerivatives.logPi_hasDerivAt F w
    (logPoint XR (SimilarityProfile.inner F.data.h p)) ⟨heta.1.le,heta.2.le⟩
  have hpd := ProfileHistories.radialPartial_hasDerivAt HeatSwitchHistoryDerivatives.interiorDomain
      hg hm
  have hpy := hpd.unique hp
  unfold physicalLog
  rw [SimilarityProfile.partialZ_pullback F.data.h_pos F.data.h_lt_half ht (hd.differentiableAt (by
      simp))]
  simp only [SimilarityProfile.pullback,SimilarityProfile.Z,CoordinateAlgebra.axialCoeff]
  rw [radialLift_partialX w.radius_pos hg hx heta,radialLift_partialEta w.radius_pos hg hx heta,hpy]
  unfold axialResidual etaDerivative
  rw [HeatSwitchHistoryDerivatives.within_parameter_eq hg hm]
  have hexp : -2*TerminalPressure.amplitudeExponent F.data.h-CoordinateAlgebra.D F.data.h =
      -TerminalPressure.amplitudeExponent F.data.h-1 := by
    unfold TerminalPressure.amplitudeExponent CoordinateAlgebra.D
    ring
  rw [hexp]
  simp only [radialLift,logPoint,SimilarityProfile.inner,StressAlgebra.coordinateFactor,
    StressAlgebra.velocityExponent,TerminalPressure.amplitudeExponent,CoordinateAlgebra.d]
  dsimp only [SimilarityProfile.inner] at hx
  have hL := SimilarityProfile.L_pos F.data.h_pos F.data.h_lt_half ht
  field_simp [hx.ne',hL.ne']; ring

theorem amplitudeOperator_congr {V W : SimilarityProfile.PhysicalProfile}
    {p : SimilarityProfile.PhysicalPoint} (he : V =ᶠ[𝓝 p] W) :
    amplitudeOperator V p = amplitudeOperator W p := by
  have hS : SimilarityProfile.partialS V =ᶠ[𝓝 p] SimilarityProfile.partialS W := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun A : SimilarityProfile.PhysicalPoint →L[ℝ] ℝ => A (0,(1,0))) hz
  have hSS : SimilarityProfile.partialS (SimilarityProfile.partialS V) p =
      SimilarityProfile.partialS (SimilarityProfile.partialS W) p :=
    congrArg (fun A : SimilarityProfile.PhysicalPoint →L[ℝ] ℝ => A (0,(1,0))) hS.fderiv_eq
  unfold amplitudeOperator
  rw [hSS]
  unfold SimilarityProfile.partialT SimilarityProfile.partialS
  rw [he.fderiv_eq,he.self_of_nhds]

/-- Terminal amplitude, given by `TerminalStress.physicalHeat C (1+d.h) p *
TerminalStress.flattening d.h (TerminalPressure.outgoingTaper d y0) p`. -/
noncomputable def terminalAmplitude (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    (p : SimilarityProfile.PhysicalPoint) : ℝ :=
  TerminalStress.physicalHeat C (1+d.h) p * TerminalStress.flattening d.h
    (TerminalPressure.outgoingTaper d y0) p

theorem terminalAmplitude_operator (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    amplitudeOperator (terminalAmplitude C d y0) (TerminalStress.radiusPoint t r z) =
      TerminalStress.leadingResidual C d.h (TerminalPressure.outgoingTaper d y0) t r z := by
  have hp : (TerminalStress.radiusPoint t r z).1 < 1 := ht
  have hs : 0 < (TerminalStress.radiusPoint t r z).2.1 := by
    dsimp [TerminalStress.radiusPoint]
    positivity
  have hf : ContDiffAt ℝ 2 (TerminalPressure.outgoingTaper d y0)
      (Real.log (SimilarityProfile.X d.h (TerminalStress.radiusPoint t r z))) :=
    (TerminalPressure.outgoingTaper_contDiff d y0).contDiffAt.of_le two_le_infty
  have hA : ContDiffAt ℝ 2 (terminalAmplitude C d y0) (TerminalStress.radiusPoint t r z) :=
    ((TerminalStress.physicalHeat_contDiffAt C (by
        linarith [d.h_pos]) hp hs).of_le two_le_infty).mul
      (TerminalStress.flattening_contDiffAt d.h_pos d.h_lt_half hp hs hf)
  have he := TerminalStress.terminal_radial_residual C d.h_pos d.h_lt_half ht hr hf
  change deriv (fun u => terminalAmplitude C d y0 (TerminalStress.radiusPoint u r z)) t -
    (deriv (deriv (TerminalStress.radialSlice (terminalAmplitude C d y0) t z)) r +
      deriv (TerminalStress.radialSlice (terminalAmplitude C d y0) t z) r/r -
      terminalAmplitude C d y0 (TerminalStress.radiusPoint t r z)/r^2) =
        TerminalStress.leadingResidual C d.h (TerminalPressure.outgoingTaper d y0) t r z at he
  have htd : deriv (fun u => terminalAmplitude C d y0 (TerminalStress.radiusPoint u r z)) t =
      SimilarityProfile.partialT (terminalAmplitude C d y0) (TerminalStress.radiusPoint t r z) :=
    (TerminalStress.timeSlice_hasDerivAt (hA.differentiableAt (by norm_num))).deriv
  rw [htd,
    TerminalStress.radialSlice_second hA,
    (TerminalStress.radialSlice_hasDerivAt (hA.differentiableAt (by norm_num))).deriv] at he
  apply Eq.trans _ he
  unfold amplitudeOperator
  dsimp only [TerminalStress.radiusPoint]
  field_simp [hr.ne']; ring

theorem terminal_germs (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    physicalLog F.data.h (-TerminalPressure.amplitudeExponent F.data.h) XR (logE F XR
        w.coefficients)
        =ᶠ[𝓝 p] terminalAmplitude (normalization F XR) F.data (shift F XR) ∧
    physicalLog F.data.h (-2*TerminalPressure.amplitudeExponent F.data.h) XR (logPi F XR
        w.coefficients)
        =ᶠ[𝓝 p] TerminalPressure.outgoingPressure (normalization F XR) F.data (shift F XR) := by
  have hX := div_pos hs (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht)
  have hK := OutgoingDilation.switchRadius_pos F XR w.radius_pos
  have hc : ContinuousAt (fun q => Real.log (SimilarityProfile.X F.data.h q /
      OutgoingDilation.switchRadius F XR) + 1/5) p :=
    ((((SimilarityProfile.inner_smoothAt F.data.h_pos F.data.h_lt_half
        ht).continuousAt.fst).div_const _).log
      (div_pos hX hK).ne').add_const _
  have hev : ∀ᶠ q in 𝓝 p, q.1 < 1 ∧ 0 < q.2.1 ∧
      1/2 < Real.log (SimilarityProfile.X F.data.h q / OutgoingDilation.switchRadius F XR)+1/5 := by
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds ht),
      continuousAt_snd.fst.eventually (Ioi_mem_nhds hs),hc.eventually (Ioi_mem_nhds hfull)] with q
          hqt hqs hqf
    exact ⟨hqt,hqs,hqf⟩
  constructor
  · filter_upwards [hev] with q hq
    have hx := div_pos hq.2.1 (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half hq.1)
    unfold physicalLog SimilarityProfile.pullback
    rw [logE_radialLift F w.radius_pos w.coefficients hx]
    exact physicalAngular_eq_terminal F w.radius_pos w.coefficients hq.1 hq.2.1 hq.2.2.le
  · filter_upwards [hev] with q hq
    have hx := div_pos hq.2.1 (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half hq.1)
    have heta : SimilarityProfile.eta F.data.h q ∈ HeatedOutgoing.parameterDomain := by
      have he := SimilarityProfile.eta_sq_lt_one F.data.h_pos F.data.h_lt_half hq.1
      constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta F.data.h q+1),sq_nonneg
          (SimilarityProfile.eta F.data.h q-1)]
    unfold physicalLog SimilarityProfile.pullback
    rw [logPi_radialLift F w hx heta]
    exact physicalPressure_eq_terminal F w.radius_pos w.coefficients hq.1 hq.2.1 hq.2.2.le

theorem terminal_angularResidual (F : Profile) {XR C t r z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) (hr : 0 < r)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z) /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    TerminalStress.leadingResidual (normalization F XR) F.data.h
      (TerminalPressure.outgoingTaper F.data (shift F XR)) t r z =
      SimilarityProfile.q F.data.h (TerminalStress.radiusPoint t r
          z)^(-TerminalPressure.amplitudeExponent F.data.h-1) *
        angularResidual F XR w.coefficients
          (logPoint XR (SimilarityProfile.inner F.data.h (TerminalStress.radiusPoint t r z))) := by
  have hs : 0 < (TerminalStress.radiusPoint t r z).2.1 := by
    dsimp [TerminalStress.radiusPoint]
    positivity
  rw [← terminalAmplitude_operator (normalization F XR) F.data (shift F XR) ht hr,
    ← amplitudeOperator_congr (terminal_germs F w ht hs hfull).1]
  exact physicalLog_angularResidual F w ht hs

theorem terminal_axialResidual (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    SimilarityProfile.partialZ (TerminalPressure.outgoingPressure (normalization F XR) F.data
        (shift F XR)) p =
      SimilarityProfile.q F.data.h p^(-TerminalPressure.amplitudeExponent F.data.h-1) *
        axialResidual F XR w.coefficients (logPoint XR (SimilarityProfile.inner F.data.h p)) := by
  have he := (terminal_germs F w ht hs hfull).2
  unfold SimilarityProfile.partialZ
  rw [← he.fderiv_eq]
  exact physicalLog_axialResidual F w ht hs

/-! ## Vanishing constants at infinity, obtained from the actual moments -/

theorem powerHistory_identity (F : Profile) {XR X : ℝ} (hXR : 0 < XR) (hX : 0 < X) :
    (1-F.data.h)*powerHistory F XR X = X*OutgoingDilation.powerH F XR X := by
  have he : powerHistory F XR X = HeatTailHistoryLimits.angularAmplitude F XR *
      ∫ u in Ioc 0 X, u^(-F.data.h) := by
    unfold powerHistory
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    exact HeatTailHistoryLimits.powerH_eq F hXR hu.1
  rw [he,HeatTailHistoryLimits.powerH_eq F hXR hX,
    ← intervalIntegral.integral_of_le hX.le,
    integral_rpow (Or.inl (by linarith [F.data.h_lt_half] : -1 < -F.data.h)),
    Real.zero_rpow (by linarith [F.data.h_lt_half] : -F.data.h+1 ≠ 0),sub_zero,
    Real.rpow_add_one hX.ne']
  rw [show -F.data.h+1=1-F.data.h by ring]
  field_simp [F.data.one_sub_h_pos.ne']

theorem logPoint_radius {XR : ℝ} (hXR : 0 < XR) (y η : ℝ) :
    logPoint XR (XR*Real.exp y,η) = (y,η) := by
  simp only [logPoint,mul_div_cancel_left₀ _ hXR.ne',Real.log_exp]

theorem angularHistory_eta_eq_logI (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    deriv (fun t => angularHistory F XR w.coefficients t (XR*Real.exp y)) η =
      (XR*Real.sqrt (2*XR))*etaDerivative (logI F XR w.coefficients) (y,η) := by
  have hg := HeatSwitchHistoryDerivatives.logI_contDiffOn F w
  have hd := (ProfileHistories.parameterPartial_hasDerivAt
      HeatSwitchHistoryDerivatives.interiorDomain hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ
        _,hη⟩)).const_mul
      (XR*Real.sqrt (2*XR))
  have he : (fun t => angularHistory F XR w.coefficients t (XR*Real.exp y)) =ᶠ[𝓝 η]
      fun t => (XR*Real.sqrt (2*XR))*logI F XR w.coefficients (y,t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hη] with t ht
    exact angularHistory_eq_logI F w.radius_pos w.coefficients ⟨ht.1.le,ht.2.le⟩ y
  rw [(hd.congr_of_eventuallyEq he).deriv]
  rw [etaDerivative,HeatSwitchHistoryDerivatives.within_parameter_eq hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hη⟩)]

theorem energyHistory_eta_eq_logS (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    deriv (fun t => energyHistory F XR w.coefficients t (XR*Real.exp y)) η =
      XR*etaDerivative (logS F XR w.coefficients) (y,η) := by
  have hg := HeatSwitchHistoryDerivatives.logS_contDiffOn F w
  have hd := (ProfileHistories.parameterPartial_hasDerivAt
      HeatSwitchHistoryDerivatives.interiorDomain hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ
        _,hη⟩)).const_mul XR
  have he : (fun t => energyHistory F XR w.coefficients t (XR*Real.exp y)) =ᶠ[𝓝 η]
      fun t => XR*logS F XR w.coefficients (y,t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hη] with t ht
    exact energyHistory_eq_logS F w.radius_pos w.coefficients ⟨ht.1.le,ht.2.le⟩ y
  rw [(hd.congr_of_eventuallyEq he).deriv]
  rw [etaDerivative,HeatSwitchHistoryDerivatives.within_parameter_eq hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hη⟩)]

theorem pressure_eta_eq_logPi (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    deriv (fun t => HeatedOutgoing.Pi F XR w.coefficients (XR*Real.exp y,t)) η =
      etaDerivative (logPi F XR w.coefficients) (y,η) := by
  have hg := HeatSwitchHistoryDerivatives.logPi_contDiffOn F w
  have hd := ProfileHistories.parameterPartial_hasDerivAt
      HeatSwitchHistoryDerivatives.interiorDomain hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hη⟩)
  have he : (fun t => HeatedOutgoing.Pi F XR w.coefficients (XR*Real.exp y,t)) =ᶠ[𝓝 η]
      fun t => logPi F XR w.coefficients (y,t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hη] with t ht
    exact (HeatSwitchCone.logPi_eq_canonical F w (y,t) ⟨ht.1.le,ht.2.le⟩).symm
  rw [(hd.congr_of_eventuallyEq he).deriv]
  rw [etaDerivative,HeatSwitchHistoryDerivatives.within_parameter_eq hg
    (show (y,η) ∈ HeatSwitchHistoryDerivatives.interiorDomain.carrier from ⟨mem_univ _,hη⟩)]

theorem H_log_derivative (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    (XR*Real.exp y)*deriv (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) (XR*Real.exp y) =
      Real.sqrt (2*XR)*Real.exp (y/2) *
        (radialPartial (logE F XR w.coefficients) (y,η)+logE F XR w.coefficients (y,η)/2) := by
  let X := XR*Real.exp y
  have hX : 0 < X := mul_pos w.radius_pos (Real.exp_pos _)
  have hg := HeatSwitchHistoryDerivatives.logE_contDiffOn F w
  have he := LeadingStress.partialX_hasDerivAt
    ((radialLift_contDiffAt w.radius_pos hg (p := (X,η)) hX hη).differentiableAt (by simp))
  rw [radialLift_partialX w.radius_pos hg hX hη] at he
  have hd := ((Real.hasDerivAt_sqrt (show 2*X ≠ 0 by positivity)).comp X
    ((hasDerivAt_id X).const_mul 2)).fun_mul he
  have hev : (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) =ᶠ[𝓝 X]
      fun u => Real.sqrt (2*u)*radialLift XR (logE F XR w.coefficients) (u,η) := by
    filter_upwards [Ioi_mem_nhds hX] with u hu
    rw [logE_radialLift F w.radius_pos w.coefficients (p := (u,η)) hu]
    rfl
  rw [(hd.congr_of_eventuallyEq hev).deriv]
  change X*(_*radialLift XR (logE F XR w.coefficients) (X,η) +
    Real.sqrt (2*X)*(radialPartial (logE F XR w.coefficients) (logPoint XR (X,η))/X)) = _
  rw [radialLift,logPoint_radius w.radius_pos y η]
  have hr : Real.sqrt (2*X) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hr2 : Real.sqrt (2*X)^2 = 2*X := Real.sq_sqrt (by positivity)
  rw [← sqrt_radius_exp w.radius_pos y]
  change X*(_*logE F XR w.coefficients (y,η) +
    Real.sqrt (2*X)*(radialPartial (logE F XR w.coefficients) (y,η)/X)) =
      Real.sqrt (2*X)*(radialPartial (logE F XR w.coefficients) (y,η)+logE F XR w.coefficients
          (y,η)/2)
  generalize Real.sqrt (2*X) = r at *
  field_simp [hX.ne',hr]
  linear_combination -logE F XR w.coefficients (y,η)*hr2

theorem thetaWeight_eq_moments (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    thetaWeight F XR w.coefficients (y,η) =
      ((1-F.data.h)*(angularHistory F XR w.coefficients η (XR*Real.exp y)-powerHistory F XR
          (XR*Real.exp y)) -
        StressAlgebra.axialExponent F.data.h*η *
          deriv (fun t => angularHistory F XR w.coefficients t (XR*Real.exp y)) η -
        (XR*Real.exp y)*(HeatedOutgoing.H F XR w.coefficients (XR*Real.exp y,η) -
          OutgoingDilation.powerH F XR (XR*Real.exp y))) / CoordinateAlgebra.L F.data.h η -
        2*HeatedOutgoing.H F XR w.coefficients (XR*Real.exp y,η) +
        2*((XR*Real.exp y)*deriv (fun u => HeatedOutgoing.H F XR w.coefficients (u,η)) (XR*Real.exp
            y)) := by
  have hpower := powerHistory_identity F w.radius_pos (mul_pos w.radius_pos (Real.exp_pos y))
  rw [angularHistory_eq_logI F w.radius_pos w.coefficients ⟨hη.1.le,hη.2.le⟩,
    angularHistory_eta_eq_logI F w hη,H_log_derivative F w hη]
  simp only [HeatedOutgoing.H,sqrt_radius_exp w.radius_pos]
  unfold thetaWeight thetaStock
  simp only [show 3*y/2=y+y/2 by ring,Real.exp_add]
  unfold logE
  have hL : CoordinateAlgebra.L F.data.h η ≠ 0 :=
    (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half
      (TerminalEdgeFactor.eta_sq_le_one ⟨hη.1.le,hη.2.le⟩)).ne'
  field_simp [hL]
  linear_combination hpower

theorem axialWeight_eq_moments (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) (y : ℝ) :
    axialWeight F XR w.coefficients (y,η) =
      (4*F.data.h*η*energyHistory F XR w.coefficients η (XR*Real.exp y) -
        StressAlgebra.coordinateFactor η*deriv (fun t => energyHistory F XR w.coefficients t
            (XR*Real.exp y)) η +
        4*StressAlgebra.velocityExponent F.data.h*η*((XR*Real.exp y)*HeatedOutgoing.Pi F XR
            w.coefficients (XR*Real.exp y,η)) -
        StressAlgebra.coordinateFactor η*((XR*Real.exp y)*deriv (fun t => HeatedOutgoing.Pi F XR
            w.coefficients
          (XR*Real.exp y,t)) η)) / CoordinateAlgebra.L F.data.h η := by
  rw [energyHistory_eq_logS F w.radius_pos w.coefficients ⟨hη.1.le,hη.2.le⟩,
    energyHistory_eta_eq_logS F w hη,pressure_eta_eq_logPi F w hη,
    ← HeatSwitchCone.logPi_eq_canonical F w (y,η) ⟨hη.1.le,hη.2.le⟩]
  unfold axialWeight
  ring

theorem thetaWeight_tendsto_zero (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) :
    Tendsto (fun y => thetaWeight F XR w.coefficients (y,η)) atTop (𝓝 0) := by
  have hb : η ∈ HeatedOutgoing.parameterDomain := ⟨hη.1.le,hη.2.le⟩
  have hI := HeatTailHistoryLimits.angularHistory_sub_power_tendsto_zero w hb
  have hIm := HeatTailHistoryLimits.angularHistory_eta_tendsto_zero w hη
  have hH := HeatTailHistoryLimits.H_tendsto_zero F w.radius_pos w.coefficients hb
  have hHx := HeatTailHistoryLimits.mul_H_deriv_tendsto_zero F w.radius_pos w.coefficients hb
  have hHd := HeatTailHistoryLimits.mul_H_sub_powerH_tendsto_zero F w.radius_pos w.coefficients hb
  have hh := (((((hI.const_mul (1-F.data.h)).sub (hIm.const_mul (StressAlgebra.axialExponent
      F.data.h*η))).sub hHd).div_const
    (CoordinateAlgebra.L F.data.h η)).sub (hH.const_mul 2)).add (hHx.const_mul 2)
  have hr : Tendsto (fun y => XR*Real.exp y) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop w.radius_pos
  have ht := hh.comp hr
  simp only [mul_zero,sub_zero,zero_div,add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun y => (thetaWeight_eq_moments F w hη y).symm

theorem axialWeight_tendsto_zero (F : Profile) {XR C B : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    {η : ℝ} (hη : η ∈ Ioo (-1) 1) :
    Tendsto (fun y => axialWeight F XR w.coefficients (y,η)) atTop (𝓝 0) := by
  have hb : η ∈ HeatedOutgoing.parameterDomain := ⟨hη.1.le,hη.2.le⟩
  have hS := HeatTailHistoryLimits.energyHistory_tendsto_zero hF w hb
  have hSm := HeatTailHistoryLimits.energyHistory_eta_tendsto_zero hF w hη
  have hP := HeatTailHistoryLimits.mul_pressure_tendsto_zero F w.radius_pos w.coefficients hb
  have hPm := HeatTailHistoryLimits.mul_pressure_eta_tendsto_zero F w.radius_pos w.coefficients hη
  have hh := (((hS.const_mul (4*F.data.h*η)).sub (hSm.const_mul (StressAlgebra.coordinateFactor
      η))).add
    (hP.const_mul (4*StressAlgebra.velocityExponent F.data.h*η))).sub (hPm.const_mul
        (StressAlgebra.coordinateFactor η))
    |>.div_const (CoordinateAlgebra.L F.data.h η)
  have hr : Tendsto (fun y => XR*Real.exp y) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop w.radius_pos
  have ht := hh.comp hr
  simp only [mul_zero,sub_zero,zero_div,add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun y => (axialWeight_eq_moments F w hη y).symm

theorem eta_mem_interior {h : ℝ} (hh : 0 < h) (hh' : h < 1 / 2)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) :
    SimilarityProfile.eta h p ∈ Ioo (-1) 1 := by
  have he := SimilarityProfile.eta_sq_lt_one hh hh' ht
  constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta h p+1),sq_nonneg
      (SimilarityProfile.eta h p-1)]

theorem full_switch_late (F : Profile) {XR X : ℝ} (hXR : 0 < XR) (hX : 0 < X)
    (hfull : 1 / 2 ≤ Real.log (X / OutgoingDilation.switchRadius F XR) + 1 / 5) :
    TerminalCone.terminalStart F.data ≤ Real.log (X/XR) := by
  have he := TerminalCone.tailTime_clock F hXR (Real.log (X/XR))
  rw [Real.exp_log (div_pos hX hXR),mul_div_cancel₀ _ hXR.ne'] at he
  unfold TerminalCone.terminalStart
  linarith

theorem full_switch_radial_strict {F : Profile} {XR : ℝ} (hXR : 0 < XR)
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) {u : ℝ} (hu : p.2.1 ≤ u) :
    1/2 < Real.log (SimilarityProfile.X F.data.h (p.1,(u,p.2.2)) /
      OutgoingDilation.switchRadius F XR)+1/5 := by
  have hq := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have hK := OutgoingDilation.switchRadius_pos F XR hXR
  have hx : 0 < SimilarityProfile.X F.data.h p := div_pos hs hq
  have hle : SimilarityProfile.X F.data.h p ≤ SimilarityProfile.X F.data.h (p.1,(u,p.2.2)) :=
    div_le_div_of_nonneg_right hu hq.le
  exact hfull.trans_le (add_le_add_left
    (Real.log_le_log (div_pos hx hK) (div_le_div_of_nonneg_right hle hK.le)) _)

/-- Regular clock, given by `Real.log ((s/q)/XR)`. -/
noncomputable def regularClock (q XR s : ℝ) : ℝ := Real.log ((s/q)/XR)
/-- Radius clock, given by `regularClock q XR (r^2/2)`. -/
noncomputable def radiusClock (q XR r : ℝ) : ℝ := regularClock q XR (r^2/2)

theorem regularClock_hasDerivAt {q XR s : ℝ} (hq : 0 < q) (hXR : 0 < XR) (hs : 0 < s) :
    HasDerivAt (regularClock q XR) (1/s) s := by
  convert! (log_radius_hasDerivAt hXR (div_pos hs hq)).comp s ((hasDerivAt_id s).div_const q) using
      1
  field_simp [hq.ne',hs.ne']

theorem radiusClock_hasDerivAt {q XR r : ℝ} (hq : 0 < q) (hXR : 0 < XR) (hr : 0 < r) :
    HasDerivAt (radiusClock q XR) (2/r) r := by
  convert! (regularClock_hasDerivAt hq hXR (by positivity : 0 < r^2/2)).comp r
    (RadialHeatProfile.radiusSquared_hasDerivAt r) using 1
  field_simp [hr.ne']

theorem exp_regularClock {q XR s : ℝ} (hq : 0 < q) (hXR : 0 < XR) (hs : 0 < s) :
    XR*Real.exp (regularClock q XR s) = s/q := by
  rw [regularClock,Real.exp_log (div_pos (div_pos hs hq) hXR),mul_div_cancel₀ _ hXR.ne']

theorem regularClock_tendsto {q XR : ℝ} (hq : 0 < q) (hXR : 0 < XR) :
    Tendsto (regularClock q XR) atTop atTop :=
  Real.tendsto_log_atTop.comp ((tendsto_id.atTop_div_const hq).atTop_div_const hXR)

theorem radiusClock_tendsto {q XR : ℝ} (hq : 0 < q) (hXR : 0 < XR) :
    Tendsto (radiusClock q XR) atTop atTop :=
  (regularClock_tendsto hq hXR).comp ((tendsto_pow_atTop (by
      decide : (2:ℕ) ≠ 0)).atTop_div_const (by norm_num))

theorem sqrt_radius_quotient {q r : ℝ} (_hq : 0 < q) (hr : 0 < r) :
    Real.sqrt (2*(r^2/2/q)) = r/Real.sqrt q := by
  rw [show 2*(r^2/2/q)=r^2/q by ring,Real.sqrt_div (sq_nonneg r),Real.sqrt_sq hr.le]

theorem theta_power_identity {q : ℝ} (hq : 0 < q) (h : ℝ) :
    q^(-h) = q^(-TerminalPressure.amplitudeExponent h-1)*q*Real.sqrt q := by
  calc
    _ = q^((-TerminalPressure.amplitudeExponent h-1)+1+1/2) := by
      congr 1
      unfold TerminalPressure.amplitudeExponent
      ring
    _ = _ := by rw [Real.rpow_add hq,Real.rpow_add hq,Real.rpow_one,Real.sqrt_eq_rpow]

/-- Physical theta weight as an element of `ℝ`. -/
noncomputable def physicalThetaWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (t z r : ℝ) : ℝ :=
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  q^(-F.data.h)*thetaWeight F XR c (radiusClock q XR r,η)

/-- Physical axial weight as an element of `ℝ`. -/
noncomputable def physicalAxialWeight (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (t z s : ℝ) : ℝ :=
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  q^(-TerminalPressure.amplitudeExponent F.data.h)*axialWeight F XR c (regularClock q XR s,η)

theorem physicalThetaWeight_hasDerivAt (F : Profile) {XR C t r z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) (hr : 0 < r)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z) /
      OutgoingDilation.switchRadius F XR) +
 1 / 5) :
    HasDerivAt (physicalThetaWeight F XR w.coefficients t z)
      (-(r^2*TerminalStress.leadingResidual (normalization F XR) F.data.h
        (TerminalPressure.outgoingTaper F.data (shift F XR)) t r z)) r := by
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  have hq : 0 < q := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have heta : η ∈ Ioo (-1) 1 := eta_mem_interior F.data.h_pos F.data.h_lt_half ht
  have hd := ((thetaWeight_hasDerivAt F w (p := (radiusClock q XR r,η)) heta).comp r
    (radiusClock_hasDerivAt hq w.radius_pos hr)).const_mul (q^(-F.data.h))
  apply hd.congr_deriv
  rw [terminal_angularResidual F w ht hr hfull]
  change q^(-F.data.h) *
    ((-(XR*Real.exp (radiusClock q XR r))*Real.sqrt (2*(XR*Real.exp (radiusClock q XR r))) *
      angularResidual F XR w.coefficients (radiusClock q XR r,η))*(2/r)) =
    -(r^2*(q^(-TerminalPressure.amplitudeExponent F.data.h-1) *
      angularResidual F XR w.coefficients (radiusClock q XR r,η)))
  rw [radiusClock,exp_regularClock hq w.radius_pos (by positivity : 0 < r^2/2),
    sqrt_radius_quotient hq hr,theta_power_identity hq F.data.h]
  field_simp [hq.ne',hr.ne',(Real.sqrt_pos.mpr hq).ne']

theorem physicalAxialWeight_hasDerivAt (F : Profile) {XR C t s z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) (hs : 0 < s)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (t, (s, z)) /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    HasDerivAt (physicalAxialWeight F XR w.coefficients t z)
      (-SimilarityProfile.partialZ (TerminalPressure.outgoingPressure (normalization F XR) F.data
          (shift F XR)) (t,(s,z))) s := by
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  have hq : 0 < q := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have heta : η ∈ Ioo (-1) 1 := eta_mem_interior F.data.h_pos F.data.h_lt_half ht
  have hx : 0 < s/q := div_pos hs hq
  have hy : F.data.core.endpoint ≤ regularClock q XR s :=
    (terminalStart_after_endpoint F).le.trans (full_switch_late F w.radius_pos hx hfull.le)
  have hd := ((axialWeight_hasDerivAt F w (p := (regularClock q XR s,η)) heta hy).comp s
    (regularClock_hasDerivAt hq w.radius_pos hs)).const_mul (q^(-TerminalPressure.amplitudeExponent
        F.data.h))
  apply hd.congr_deriv
  rw [terminal_axialResidual F w ht hs hfull]
  change q^(-TerminalPressure.amplitudeExponent F.data.h) *
    ((-(XR*Real.exp (regularClock q XR s))*axialResidual F XR w.coefficients (regularClock q XR
        s,η))*(1/s)) =
    -(q^(-TerminalPressure.amplitudeExponent F.data.h-1)*axialResidual F XR w.coefficients
        (regularClock q XR s,η))
  rw [exp_regularClock hq w.radius_pos hs,Real.rpow_sub_one hq.ne']
  field_simp [hq.ne',hs.ne']

theorem physicalThetaWeight_tendsto_zero (F : Profile) {XR C t z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) :
    Tendsto (physicalThetaWeight F XR w.coefficients t z) atTop (𝓝 0) := by
  have hq := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half (p := (t,(0,z))) ht
  have heta := eta_mem_interior F.data.h_pos F.data.h_lt_half (p := (t,(0,z))) ht
  have h := ((thetaWeight_tendsto_zero F w heta).comp (radiusClock_tendsto hq
      w.radius_pos)).const_mul
    (SimilarityProfile.q F.data.h (t,(0,z))^(-F.data.h))
  simp only [mul_zero] at h
  exact h

theorem physicalAxialWeight_tendsto_zero (F : Profile) {XR C B t z : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C) (ht : t < 1) :
    Tendsto (physicalAxialWeight F XR w.coefficients t z) atTop (𝓝 0) := by
  have hq := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half (p := (t,(0,z))) ht
  have heta := eta_mem_interior F.data.h_pos F.data.h_lt_half (p := (t,(0,z))) ht
  have h := ((axialWeight_tendsto_zero F hF w heta).comp (regularClock_tendsto hq
      w.radius_pos)).const_mul
    (SimilarityProfile.q F.data.h (t,(0,z))^(-TerminalPressure.amplitudeExponent F.data.h))
  simp only [mul_zero] at h
  exact h

theorem terminal_angular_integrable (C : ℝ) (d : OutgoingTail.TailData) (y0 : ℝ)
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r) :
    IntegrableOn (fun u => u^2*TerminalStress.leadingResidual C d.h
      (TerminalPressure.outgoingTaper d y0) t u z) (Ioi r) := by
  have hi := TerminalPressure.terminal_forcing_integrable C (z := z) d.h_pos d.h_lt_half ht hr
    (TerminalPressure.outgoingTaper_contDiff d y0) (TerminalPressure.outgoingTaper_plateau d y0)
  apply IntegrableOn.congr_fun (hi.2.2.add hi.1) _ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [TerminalStress.leadingResidual_eq_time_add,mul_add]
  rfl

theorem terminal_axial_integrable {C : ℝ} (hC : 0 < C) (d : OutgoingTail.TailData) (y0 : ℝ)
    {t s z : ℝ} (ht : t < 1) (hs : 0 < s) :
    IntegrableOn (fun u => SimilarityProfile.partialZ
      (TerminalPressure.outgoingPressure C d y0) (t,(u,z))) (Ioi s) := by
  have hr : 0 < Real.sqrt (2*s) := Real.sqrt_pos.mpr (by positivity)
  have hev := (TerminalStress.logX_radial_tendsto (z := z) d.h_pos d.h_lt_half ht).eventually
    (eventually_ge_atTop (y0+3))
  obtain ⟨R,hY,hR⟩ := (hev.and (eventually_ge_atTop (Real.sqrt (2*s)))).exists
  have hi := (TerminalPressure.axialBackwardStress_bound hC d.h_pos d.h_lt_half ht hr hR
    (TerminalPressure.outgoingTaper_contDiff d y0) (TerminalPressure.outgoingTaper_bounds d y0)
    (TerminalPressure.outgoingTaper_deriv_nonneg d y0) (TerminalPressure.outgoingTaper_plateau d
        y0) hY).1
  simpa only [TerminalPressure.outgoingPressure,Real.sq_sqrt (by positivity : 0 ≤ 2*s),
    mul_div_cancel_left₀ s (by norm_num : (2:ℝ)≠0)] using hi

theorem physicalThetaWeight_eq_tail (F : Profile) {XR C t r z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) (hr : 0 < r)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z) /
      OutgoingDilation.switchRadius F XR) +
 1 / 5) :
    physicalThetaWeight F XR w.coefficients t z r =
      ∫ u in Ioi r, u^2*TerminalStress.leadingResidual (normalization F XR) F.data.h
        (TerminalPressure.outgoingTaper F.data (shift F XR)) t u z := by
  have hd : ∀ u ∈ Ici r, HasDerivAt (physicalThetaWeight F XR w.coefficients t z)
      (-(u^2*TerminalStress.leadingResidual (normalization F XR) F.data.h
        (TerminalPressure.outgoingTaper F.data (shift F XR)) t u z)) u := by
    intro u hu
    change r ≤ u at hu
    apply physicalThetaWeight_hasDerivAt F w ht (hr.trans_le hu)
    have hh := full_switch_radial_strict w.radius_pos ht
      (show 0 < (TerminalStress.radiusPoint t r z).2.1 by
          dsimp [TerminalStress.radiusPoint]; positivity)
      hfull (u := u^2/2) (by dsimp [TerminalStress.radiusPoint]; nlinarith)
    exact hh
  have hi := terminal_angular_integrable (normalization F XR) F.data (shift F XR) (z := z) ht hr
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi.neg (physicalThetaWeight_tendsto_zero F w
      ht)
  rw [integral_neg] at hh
  linarith

theorem physicalAxialWeight_eq_tail (F : Profile) {XR C B t s z : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    (ht : t < 1) (hs : 0 < s)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (t, (s, z)) /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    physicalAxialWeight F XR w.coefficients t z s =
      ∫ u in Ioi s, SimilarityProfile.partialZ
        (TerminalPressure.outgoingPressure (normalization F XR) F.data (shift F XR)) (t,(u,z)) := by
  have hd : ∀ u ∈ Ici s, HasDerivAt (physicalAxialWeight F XR w.coefficients t z)
      (-SimilarityProfile.partialZ
        (TerminalPressure.outgoingPressure (normalization F XR) F.data (shift F XR)) (t,(u,z))) u
            := by
    intro u hu
    exact physicalAxialWeight_hasDerivAt F w ht (hs.trans_le hu)
      (full_switch_radial_strict w.radius_pos ht hs hfull hu)
  have hC : 0 < normalization F XR := TerminalCone.normalization_pos F w.radius_pos
  have hi := terminal_axial_integrable hC F.data (shift F XR) (z := z) ht hs
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi.neg (physicalAxialWeight_tendsto_zero F
      hF w ht)
  rw [integral_neg] at hh
  linarith

/-- The actual forward angular stress equals the independently defined
backward physical stress.  Its similarity factor is `q^(-A-1/2)`. -/
theorem physical_forwardTheta_eq_terminal (F : Profile) {XR C t r z : ℝ}
    (w : CompensationWitness F XR C) (ht : t < 1) (hr : 0 < r)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z) /
      OutgoingDilation.switchRadius F XR) +
 1 / 5) :
    SimilarityProfile.q F.data.h (TerminalStress.radiusPoint t r
        z)^(-TerminalPressure.amplitudeExponent F.data.h-1/2) *
      forwardTheta F XR w.coefficients (logPoint XR (SimilarityProfile.inner F.data.h
          (TerminalStress.radiusPoint t r z))) =
        TerminalStress.terminalStress (normalization F XR) F.data.h
          (TerminalPressure.outgoingTaper F.data (shift F XR)) t z r := by
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  have hq : 0 < q := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have heta : η ∈ Ioo (-1) 1 := eta_mem_interior F.data.h_pos F.data.h_lt_half ht
  have hx : 0 < r^2/2/q := div_pos (by positivity) hq
  have hy : F.data.core.endpoint ≤ radiusClock q XR r :=
    (terminalStart_after_endpoint F).le.trans (full_switch_late F w.radius_pos hx hfull.le)
  have hw := thetaWeight_eq_forward F w (p := (radiusClock q XR r,η)) heta hy
  have he := physicalThetaWeight_eq_tail F w ht hr hfull
  change q^(-F.data.h)*thetaWeight F XR w.coefficients (radiusClock q XR r,η) = _ at he
  unfold TerminalStress.terminalStress TerminalStress.backwardStress
  rw [← he,hw]
  change q^(-TerminalPressure.amplitudeExponent F.data.h-1/2) *
    forwardTheta F XR w.coefficients (radiusClock q XR r,η) =
    q^(-F.data.h)*(2*(XR*Real.exp (radiusClock q XR r))*forwardTheta F XR w.coefficients
        (radiusClock q XR r,η))/r^2
  rw [show -TerminalPressure.amplitudeExponent F.data.h-1/2=-F.data.h-1 by
    unfold TerminalPressure.amplitudeExponent
    ring,Real.rpow_sub_one hq.ne',radiusClock,exp_regularClock hq w.radius_pos (by
        positivity : 0 < r^2/2)]
  field_simp [hq.ne',hr.ne']

/-- The same witness and the original zero-energy identity also fix the
axial integration constant; the pressure is the actual canonical pressure. -/
theorem physical_forwardAxial_eq_terminal (F : Profile) {XR C B t r z : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C) (ht : t < 1) (hr : 0
        < r)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z) /
      OutgoingDilation.switchRadius F XR) +
 1 / 5) :
    SimilarityProfile.q F.data.h (TerminalStress.radiusPoint t r
        z)^(-TerminalPressure.amplitudeExponent F.data.h-1/2) *
      forwardAxial F XR w.coefficients (logPoint XR (SimilarityProfile.inner F.data.h
          (TerminalStress.radiusPoint t r z))) =
        TerminalPressure.axialBackwardStress (normalization F XR) F.data.h
          (TerminalPressure.outgoingTaper F.data (shift F XR)) t z r := by
  let q := SimilarityProfile.q F.data.h (t,(0,z))
  let η := SimilarityProfile.eta F.data.h (t,(0,z))
  have hq : 0 < q := SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht
  have hx : 0 < r^2/2/q := div_pos (by positivity) hq
  have hy : F.data.core.endpoint ≤ radiusClock q XR r :=
    (terminalStart_after_endpoint F).le.trans (full_switch_late F w.radius_pos hx hfull.le)
  have hw := axialWeight_eq_forward F w (p := (radiusClock q XR r,η)) hy
  have he := physicalAxialWeight_eq_tail F hF w ht (by positivity : 0 < r^2/2) hfull
  change q^(-TerminalPressure.amplitudeExponent F.data.h)*axialWeight F XR w.coefficients
      (radiusClock q XR r,η) = _ at he
  unfold TerminalPressure.axialBackwardStress
  change _ = (∫ u in Ioi (r^2/2), SimilarityProfile.partialZ
    (TerminalPressure.outgoingPressure (normalization F XR) F.data (shift F XR)) (t,(u,z)))/r
  rw [← he,hw]
  change q^(-TerminalPressure.amplitudeExponent F.data.h-1/2) *
    forwardAxial F XR w.coefficients (radiusClock q XR r,η) =
    q^(-TerminalPressure.amplitudeExponent F.data.h) *
      (Real.sqrt (2*XR*Real.exp (radiusClock q XR r))*forwardAxial F XR w.coefficients (radiusClock
          q XR r,η))/r
  rw [show 2*XR*Real.exp (radiusClock q XR r)=2*(XR*Real.exp (radiusClock q XR r)) by ring,
    radiusClock,exp_regularClock hq w.radius_pos (by
        positivity : 0 < r^2/2),sqrt_radius_quotient hq hr,
    Real.rpow_sub hq,← Real.sqrt_eq_rpow]
  field_simp [hr.ne',(Real.sqrt_pos.mpr hq).ne']

theorem normalized_inner (F : Profile) {XR : ℝ} (hXR : 0 < XR) (y : ℝ)
    {η : ℝ} (hη : η ^ 2 < 1) :
    SimilarityProfile.q F.data.h (TerminalStress.radiusPoint (η^2)
      (TerminalEdgeFactor.profileRadius (shift F XR) (TerminalCone.edgeDistance F y)) η) = 1 ∧
    SimilarityProfile.inner F.data.h (TerminalStress.radiusPoint (η^2)
      (TerminalEdgeFactor.profileRadius (shift F XR) (TerminalCone.edgeDistance F y)) η) =
          (XR*Real.exp y,η) := by
  let r := TerminalEdgeFactor.profileRadius (shift F XR) (TerminalCone.edgeDistance F y)
  have hq : SimilarityProfile.q F.data.h (TerminalStress.radiusPoint (η^2) r η) = 1 :=
    PhysicalHeatCoordinates.q_normalizedSection F.data.h_pos F.data.h_lt_half hη (r^2/2)
  have he : SimilarityProfile.eta F.data.h (TerminalStress.radiusPoint (η^2) r η) = η :=
    PhysicalHeatCoordinates.eta_normalizedSection F.data.h_pos F.data.h_lt_half hη (r^2/2)
  refine ⟨hq,?_⟩
  change (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint (η^2) r η),
    SimilarityProfile.eta F.data.h (TerminalStress.radiusPoint (η^2) r η)) = _
  rw [he]
  unfold SimilarityProfile.X
  rw [hq,div_one]
  change (r^2/2,η) = _
  have hr2 : r^2 = 2*(XR*Real.exp y) := by
    rw [TerminalEdgeFactor.profileRadius_square]
    change 2*TerminalEdgeFactor.profileS (TerminalCone.shift F XR) (TerminalCone.edgeDistance F y)
        = _
    rw [TerminalCone.profileS_clock F hXR]
  rw [hr2]
  congr 1
  ring

/-- Exact profile stress agreement on the open parameter interval.  The
closed endpoints are handled below by the actual continuous representatives. -/
theorem forward_stresses_eq_profile_interior (F : Profile) {XR C B y η : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    (hy : TerminalCone.terminalStart F.data < y) (hη : η ∈ Ioo (-1) 1) :
    forwardTheta F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileAngularStress (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) ∧
    forwardAxial F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileAxialStress (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
  have he2 : η^2 < 1 := TerminalCone.eta_sq_lt_one hη
  let r := TerminalEdgeFactor.profileRadius (shift F XR) (TerminalCone.edgeDistance F y)
  have hr : 0 < r := TerminalEdgeFactor.profileRadius_pos _ _
  have hn := normalized_inner F w.radius_pos y he2
  have hfull : 1/2 < Real.log (SimilarityProfile.X F.data.h (TerminalStress.radiusPoint (η^2) r η)/
      OutgoingDilation.switchRadius F XR)+1/5 := by
    have hx := congrArg Prod.fst hn.2
    change SimilarityProfile.X F.data.h (TerminalStress.radiusPoint (η^2) r η) = XR*Real.exp y at hx
    rw [hx,TerminalCone.tailTime_clock F w.radius_pos y]
    unfold TerminalCone.terminalStart at hy
    linarith
  have ht := physical_forwardTheta_eq_terminal F w he2 hr hfull
  have hz := physical_forwardAxial_eq_terminal F hF w he2 hr hfull
  rw [hn.1,hn.2,logPoint_radius w.radius_pos,Real.one_rpow,one_mul,
    TerminalCone.normalized_angularStress _ F.data _ _ he2] at ht
  rw [hn.1,hn.2,logPoint_radius w.radius_pos,Real.one_rpow,one_mul,
    TerminalCone.normalized_axialStress _ F.data _ _ he2] at hz
  exact ⟨ht,hz⟩

/-- Closed log domain, given by `univ ×ˢ HeatedOutgoing.parameterDomain`. -/
noncomputable def closedLogDomain : Set (ℝ × ℝ) := univ ×ˢ HeatedOutgoing.parameterDomain

theorem controls_continuousOn (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C) :
    ContinuousOn (HeatSwitchCone.controls F w) HeatedOutgoing.parameterDomain := by
  have hd := w.smooth.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num : (-1:ℝ)<1))
    (by exact WithTop.coe_le_coe.mpr le_top)
  exact continuousOn_const.prodMk (w.smooth.continuousOn.prodMk hd)

theorem scalar_fields_continuousOn (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C) :
    ContinuousOn (logE F XR w.coefficients) closedLogDomain ∧
    ContinuousOn (HeatSwitchCone.Qs F XR w.coefficients) closedLogDomain ∧
    ContinuousOn (HeatSwitchCone.Ns F XR w.coefficients) closedLogDomain ∧
    ContinuousOn (HeatSwitchCone.radialA F XR w.coefficients) closedLogDomain := by
  let G : (ℝ × ℝ) → HeatSwitchCone.Control × (ℝ × ℝ) := fun p => (HeatSwitchCone.controls F w p.2,p)
  have hc : ContinuousOn G closedLogDomain :=
    ((controls_continuousOn F w).comp continuousOn_snd (fun _ hp => hp.2)).prodMk continuousOn_id
  have he : ContinuousOn (fun p => HeatSwitchCone.value (HeatSwitchCone.freeE F) (G p))
      closedLogDomain :=
    (HeatSwitchCone.value_contDiff (HeatSwitchCone.freeE_contDiff F)).continuous.comp_continuousOn
        hc
  have heq (p : ℝ × ℝ) (hp : p ∈ closedLogDomain) :
      logE F XR w.coefficients p = HeatSwitchCone.value (HeatSwitchCone.freeE F) (G p) :=
    HeatSwitchCone.logE_eq_realize F XR w.coefficients w.radius_pos p hp.2
  have hen (p : ℝ × ℝ) (hp : p ∈ closedLogDomain) :
      HeatSwitchCone.value (HeatSwitchCone.freeE F) (G p) ≠ 0 := by
    rw [← heq p hp]
    exact (w.positive p.2 (XR*Real.exp p.1) hp.2 (mul_pos w.radius_pos (Real.exp_pos _))).ne'
  have hq : ContinuousOn (fun p => HeatSwitchCone.familyQ F (G p)) closedLogDomain :=
    ((HeatSwitchCone.angularNumerator_contDiff F).continuous.comp_continuousOn hc).div
      (((continuousOn_const.mul continuousOn_fst).div_const 2).rexp.mul he)
      (fun p hp => mul_ne_zero (Real.exp_ne_zero _) (hen p hp))
  have hn : ContinuousOn (fun p => HeatSwitchCone.familyN F (G p)) closedLogDomain :=
    (HeatSwitchCone.familyN_contDiff F).continuous.comp_continuousOn hc
  have ha : ContinuousOn (fun p => HeatSwitchCone.familyA F (G p)) closedLogDomain :=
    ((HeatSwitchCone.radialNumerator_contDiff F).continuous.comp_continuousOn hc).div he hen
  exact ⟨he.congr heq,hq.congr (fun p hp => HeatSwitchCone.Qs_eq_family F w hp.2),
    hn.congr (fun p hp => HeatSwitchCone.Ns_eq_family F w hp.2),
    ha.congr (fun p hp => HeatSwitchCone.radialA_eq_family F w hp.2)⟩

theorem forward_fields_continuousOn (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C) :
    ContinuousOn (forwardTheta F XR w.coefficients) closedLogDomain ∧
    ContinuousOn (forwardAxial F XR w.coefficients) closedLogDomain := by
  obtain ⟨he,hq,hn,ha⟩ := scalar_fields_continuousOn F w
  have hx : ContinuousOn (fun p : ℝ × ℝ => XR*Real.exp p.1) closedLogDomain :=
    continuousOn_const.mul continuousOn_fst.rexp
  have hr : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt (2*XR*Real.exp p.1)) closedLogDomain :=
    ((continuousOn_const.mul continuousOn_const).mul continuousOn_fst.rexp).sqrt
  have hrn (p : ℝ × ℝ) : Real.sqrt (2*XR*Real.exp p.1) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) w.radius_pos) (Real.exp_pos _))).ne'
  have hl : ContinuousOn (fun p : ℝ × ℝ => CoordinateAlgebra.L F.data.h p.2) closedLogDomain :=
    continuousOn_const.sub (continuousOn_const.mul (continuousOn_snd.pow 2))
  have hln (p : ℝ × ℝ) (hp : p ∈ closedLogDomain) : CoordinateAlgebra.L F.data.h p.2 ≠ 0 :=
    (CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half (TerminalEdgeFactor.eta_sq_le_one
        hp.2)).ne'
  exact ⟨(he.div hr (fun p _ => hrn p)).mul (((hx.mul hq).div hl hln).sub ha),
    (hx.mul hn).div (hl.mul hr) (fun p hp => mul_ne_zero (hln p hp) (hrn p))⟩

/-- Terminal map, given by `(p.2,OutgoingTail.tailEnd F.data-p.1)`. -/
noncomputable def terminalMap (F : Profile) (p : ℝ × ℝ) : ℝ × ℝ := (p.2,OutgoingTail.tailEnd
    F.data-p.1)

theorem terminalMap_continuous (F : Profile) : Continuous (terminalMap F) :=
  continuous_snd.prodMk (continuous_const.sub continuous_fst)

theorem terminal_speed_continuousOn (F : Profile) {XR C : ℝ} (w : CompensationWitness F XR C) :
    ContinuousOn (fun p => TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
        (terminalMap F p))
      closedLogDomain := by
  apply (TerminalEdgeFactor.profileSpeed_contDiffOn (normalization F XR) F.data (shift F
      XR)).continuousOn.comp
    (terminalMap_continuous F).continuousOn
  intro p hp
  exact TerminalEdgeFactor.profileDomain_contains_closed (TerminalCone.normalization_pos F
      w.radius_pos)
    F.data (shift F XR) ⟨hp.2,mem_univ _⟩

/-- Joint closure in log radius and parameter includes the switch-attachment
point and both parameter endpoints, without evaluating physical coordinates
at the singular time `t=1`. -/
theorem forward_stresses_eq_profile (F : Profile) {XR C B y η : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hη : η ∈ HeatedOutgoing.parameterDomain) :
    forwardTheta F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileAngularStress (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) ∧
    forwardAxial F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileAxialStress (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) ∧
    HeatSwitchCone.radialA F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
  let S : Set (ℝ × ℝ) := Ioi (TerminalCone.terminalStart F.data) ×ˢ Ioo (-1) 1
  let T : Set (ℝ × ℝ) := Ici (TerminalCone.terminalStart F.data) ×ˢ HeatedOutgoing.parameterDomain
  have hST : S ⊆ T := by
    intro p hp
    change TerminalCone.terminalStart F.data < p.1 ∧ -1 < p.2 ∧ p.2 < 1 at hp
    change TerminalCone.terminalStart F.data ≤ p.1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1
    exact ⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have hTc : T ⊆ closedLogDomain := fun p hp => ⟨mem_univ _,hp.2⟩
  have hTS : T ⊆ closure S := by
    simp only [S,T,HeatedOutgoing.parameterDomain,closure_prod_eq,closure_Ioi,
      closure_Ioo (by norm_num : (-1:ℝ)≠1),subset_refl]
  have hs := (TerminalEdgeFactor.profileStress_contDiff (normalization F XR) F.data (shift F
      XR)).continuous.comp
    (terminalMap_continuous F)
  have heΘ : EqOn (forwardTheta F XR w.coefficients)
      (fun p => TerminalEdgeFactor.profileAngularStress (normalization F XR) F.data (shift F XR)
          (terminalMap F p)) S := by
    intro p hp
    exact (forward_stresses_eq_profile_interior F hF w hp.1 hp.2).1
  have heZ : EqOn (forwardAxial F XR w.coefficients)
      (fun p => TerminalEdgeFactor.profileAxialStress (normalization F XR) F.data (shift F XR)
          (terminalMap F p)) S := by
    intro p hp
    exact (forward_stresses_eq_profile_interior F hF w hp.1 hp.2).2
  have heA : EqOn (HeatSwitchCone.radialA F XR w.coefficients)
      (fun p => TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
          (terminalMap F p)) S := by
    intro p hp
    exact radialA_eq_profileSpeed F w hp.1 ⟨hp.2.1.le,hp.2.2.le⟩
  have hΘ := heΘ.of_subset_closure ((forward_fields_continuousOn F w).1.mono hTc)
      hs.fst.continuousOn hST hTS
  have hZ := heZ.of_subset_closure ((forward_fields_continuousOn F w).2.mono hTc)
      hs.snd.continuousOn hST hTS
  have hA := heA.of_subset_closure ((scalar_fields_continuousOn F w).2.2.2.mono hTc)
    ((terminal_speed_continuousOn F w).mono hTc) hST hTS
  exact ⟨hΘ (show (y,η) ∈ T from ⟨hy,hη⟩),
    hZ (show (y,η) ∈ T from ⟨hy,hη⟩),hA (show (y,η) ∈ T from ⟨hy,hη⟩)⟩

theorem logSwirl_eq_profile (F : Profile) {XR C y η : ℝ} (w : CompensationWitness F XR C)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hη : η ∈ HeatedOutgoing.parameterDomain) :
    logE F XR w.coefficients (y,η)/Real.sqrt (2*XR*Real.exp y) =
      TerminalEdgeFactor.profileSwirlCoefficient (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
  have he := TerminalCone.E_eq_profileAngularVelocity F w.coefficients w.radius_pos hy hη
  have hr : Real.sqrt (2*XR*Real.exp y) =
      TerminalEdgeFactor.profileRadius (shift F XR) (TerminalCone.edgeDistance F y) := by
    have hs := TerminalEdgeFactor.profileRadius_square (shift F XR) (TerminalCone.edgeDistance F y)
    change TerminalEdgeFactor.profileRadius (TerminalCone.shift F XR) (TerminalCone.edgeDistance F
        y)^2 =
      2*TerminalEdgeFactor.profileS (TerminalCone.shift F XR) (TerminalCone.edgeDistance F y) at hs
    rw [TerminalCone.profileS_clock F w.radius_pos] at hs
    rw [show 2*XR*Real.exp y=2*(XR*Real.exp y) by ring,← hs,
      Real.sqrt_sq (TerminalEdgeFactor.profileRadius_pos _ _).le]
    rfl
  rw [hr]
  exact congrArg (fun a => a/TerminalEdgeFactor.profileRadius (shift F XR)
      (TerminalCone.edgeDistance F y)) he

theorem normalP_eq_profile (F : Profile) {XR C B y η : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hη : η ∈ HeatedOutgoing.parameterDomain) :
    HeatSwitchCone.normalP F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
  have hafter := (terminalStart_after_endpoint F).trans_le hy
  have he := forward_stresses_eq_profile F hF w hy hη
  have hsw := logSwirl_eq_profile F w hy hη
  have hE : logE F XR w.coefficients (y,η)/Real.sqrt (2*XR*Real.exp y) ≠ 0 := by
    rw [hsw]
    exact (TerminalEdgeFactor.profileSwirlCoefficient_pos (TerminalCone.normalization_pos F
        w.radius_pos)
      F.data (shift F XR) (y := TerminalCone.profilePoint F y η) hη).ne'
  simp only [HeatSwitchCone.normalP,HeatSwitchCone.sourceC,
    radialB_after_endpoint F XR w.coefficients (p := (y,η)) hafter,
    zero_mul,zero_div,sub_zero,mul_one]
  rw [TerminalEdgeFactor.profileP,← he.2.2,← he.1,← hsw]
  change HeatSwitchCone.stressScale F XR w.coefficients (y,η) = _
  unfold forwardTheta
  dsimp only
  rw [mul_div_cancel_left₀ _ hE]
  unfold HeatSwitchCone.stressScale
  ring

theorem terminal_forward_cone (F : Profile) {XR C B y η : ℝ}
    (hF : OutgoingProfile.Specification F B) (w : CompensationWitness F XR C)
    (hsmall : TerminalCone.SmallTail F.data) (hXR : TerminalCone.radiusThreshold F ≤ XR)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data)
    (hη : η ∈ HeatedOutgoing.parameterDomain) :
    HeatSwitchCone.TrueAt F XR w.coefficients (y,η) ∧
    HeatSwitchCone.normalP F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileP (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) ∧
    HeatSwitchCone.normalJ F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileJ (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
  have hafter := (terminalStart_after_endpoint F).trans_le hy
  have hB := radialB_after_endpoint F XR w.coefficients (p := (y,η)) hafter
  have he := forward_stresses_eq_profile F hF w hy hη
  have hP := normalP_eq_profile F hF w hy hη
  have htrue := TerminalCone.full_interval_true_cone F hsmall hXR hy hy' hη
  have hspeed := (TerminalCone.full_interval_direction_margin F hsmall hXR hy hy'.le hη).1
  change 2+F.data.h < TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
    (TerminalCone.profilePoint F y η) at hspeed
  have hP2 : 2 < HeatSwitchCone.normalP F XR w.coefficients (y,η) := by rw [hP]; exact htrue.1
  have hscale : HeatSwitchCone.normalP F XR w.coefficients (y,η) =
      XR*Real.exp y*HeatSwitchCone.Qs F XR w.coefficients (y,η)/CoordinateAlgebra.L F.data.h η := by
    simp only [HeatSwitchCone.normalP,HeatSwitchCone.sourceC,hB,zero_mul,zero_div,sub_zero,mul_one,
      HeatSwitchCone.stressScale]
  have hL : 0 < CoordinateAlgebra.L F.data.h η :=
    CoordinateAlgebra.L_pos F.data.h_pos.le F.data.h_lt_half (TerminalEdgeFactor.eta_sq_le_one hη)
  have hQ : 0 < HeatSwitchCone.Qs F XR w.coefficients (y,η) := by
    have hp0 : 0 < XR*Real.exp y*HeatSwitchCone.Qs F XR w.coefficients (y,η)/CoordinateAlgebra.L
        F.data.h η := by
      rw [← hscale]
      linarith
    exact (mul_pos_iff_of_pos_left (mul_pos w.radius_pos (Real.exp_pos y))).mp
      ((div_pos_iff_of_pos_right hL).mp hp0)
  have hJ := (forward_normalization F w (p := (y,η)) hafter hη hQ.ne').2
  rw [he.2.1,logSwirl_eq_profile F w hy hη] at hJ
  have hJ' : HeatSwitchCone.normalJ F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileJ (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := hJ
  have hV : HeatSwitchCone.normalV F XR w.coefficients (y,η) =
      TerminalEdgeFactor.profileSpeed (normalization F XR) F.data (shift F XR)
          (TerminalCone.profilePoint F y η) := by
    simp only [HeatSwitchCone.normalV,hB,zero_div,zero_pow (by decide : (2:ℕ)≠0),add_zero,mul_one]
    exact he.2.2
  have ha2 : 2 < HeatSwitchCone.radialA F XR w.coefficients (y,η) := by
    rw [he.2.2]
    linarith [F.data.h_pos]
  refine ⟨?_,hP,hJ'⟩
  unfold HeatSwitchCone.TrueAt
  refine ⟨hQ,by linarith,?_,hP2,?_⟩
  · rw [hV]
    linarith [F.data.h_pos]
  · rw [hV,hP,hJ']
    exact htrue.2

end NavierStokes.TerminalHistoryBridge

end
