/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatSwitchCone

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
