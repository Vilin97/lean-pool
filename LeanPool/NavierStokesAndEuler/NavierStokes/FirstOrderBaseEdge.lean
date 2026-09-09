/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GlobalStressSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowFirstOrderEdge
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalHistoryBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedProfileAssembly

@[expose] public section

/-!
# The first stress coefficient on the terminal collar

The first coefficient is the canonical primitive of the actual repaired
residual.  The order-zero moment retained below is essential: exterior
agreement of velocities alone does not fix the constant of integration.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.FirstOrderBaseEdge

open GlobalSlowProfiles GlobalStressSupport AssembledSlowBase


theorem exterior_mono {S : Set ℝ} {f : SlowStressSupport.Field} {a b : ℝ}
    (hf : SlowStressSupport.exterior a S f) (hab : a ≤ b) : SlowStressSupport.exterior b S f :=
  fun eta heta R hR => hf eta heta R (hab.trans hR)

theorem moment_eq_of_exterior {S : Set ℝ} {f : SlowStressSupport.Field} {a b eta : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hf : SlowStressSupport.exterior a S f) (heta : eta ∈ S)
    (m : ℕ) : SlowStressSupport.moment b m f eta = SlowStressSupport.moment a m f eta := by
  rw [SlowStressSupport.moment_eq_positive (ha.trans hab) (exterior_mono hf hab) heta,
    SlowStressSupport.moment_eq_positive ha hf heta]

/-- The four conservative moments at every radius beyond the actual repair
patch follow from the five constructed rows. -/
theorem conservative_moments_at {S : Set ℝ} {h C R : ℝ} (s : Scheme S h C)
    {n : ℕ} (hn : 0 < n) (hR : s.B ≤ R) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment R 1 (axialHistory s n) eta = 0 ∧
    SlowStressSupport.moment R 2 (angularHistory s n) eta = 0 ∧
    SlowStressSupport.moment R 2 (SlowStressSupport.conv n (axialHistory s) (angularHistory s)) eta
      = 0 ∧
    SlowStressSupport.moment R 1
      (fun w => SlowStressSupport.conv n (axialHistory s) (axialHistory s) w + pressureField s n w)
        eta = 0 := by
  have hf : SlowStressSupport.exterior s.B S
      (fun w => SlowStressSupport.conv n (axialHistory s) (axialHistory s) w + pressureField s n w)
        := by
    intro z hz r hr
    dsimp only
    rw [SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j) z hz r hr,
      pressureField_exterior s hn z hz r hr, zero_add]
  rw [moment_eq_of_exterior s.B_pos.le hR (axialHistory_exterior s n) heta,
    moment_eq_of_exterior s.B_pos.le hR (angularHistory_exterior s hn) heta,
    moment_eq_of_exterior s.B_pos.le hR
      (SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j)) heta,
    moment_eq_of_exterior s.B_pos.le hR hf heta]
  exact conservative_moments_zero s hn heta

/-- The exact first angular primitive, with its order-zero viscosity moment
still displayed.  This is derived from the repaired rows, not prescribed as
a stress boundary condition. -/
theorem first_angular_balance {S : Set ℝ} {h C R : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hR : s.B ≤ R) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) 1) (R,
      eta) =
      SlowStressSupport.moment R 2 (SlowStressSupport.axialOp2 h (SlowStressSupport.orderExponent h
        0) (angularHistory s 0)) eta / R ^ 2 := by
  have hRp : 0 < R := s.B_pos.trans_le hR
  have hb := SlowStressSupport.angular_integral_balance s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (fun j _ => angularHistory_smooth s j) h R s.domain.denominator
    (exterior_mono (angularHistory_exterior s (by decide : 0 < 1)) hR)
    (fun j _ => exterior_mono (fluxHistory_exterior s j) hR)
    (fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.1)
    (fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.2.1)
    (exterior_mono (SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j))
      hR) heta
  have he : ProfileHistories.primitive (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) 1)
    (R, eta) =
      SlowStressSupport.moment R 0 (SlowStressSupport.angularDensity h 1 (fluxHistory s)
        (axialHistory s) (angularHistory s)) eta := by
    apply intervalIntegral.integral_congr
    intro r _
    simp only [pow_zero, one_mul]
    exact thetaDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩
  rw [SlowStressSupport.stress_of_pos 2 _ hRp, he, hb]
  simp

/-- At order one the axial primitive vanishes outside the repair patch as
soon as the actual base mass is zero there. -/
theorem first_axial_exterior {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hmass : ∀ eta ∈ S, SlowStressSupport.moment s.B 1 (axialHistory s 0) eta = 0) :
    SlowStressSupport.exterior s.B S (SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h
      (asSlowProfiles s) 1)) := by
  have hmoment : ∀ eta ∈ S,
      SlowStressSupport.moment s.B 0 (SlowStressSupport.axialDensity h 1 (fluxHistory s)
        (axialHistory s) (pressureField s 1)) eta = 0 := by
    intro eta heta
    apply SlowStressSupport.axial_integral_zero s.domain.isOpen
      (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
      (pressureField_smooth s 1) h s.B s.domain.denominator
      (axialHistory_exterior s 1) (fun j _ => fluxHistory_exterior s j)
    · intro z hz
      simp only [SlowStressSupport.conv, fluxHistory_axis s _ hz, zero_mul, Finset.sum_const_zero]
    · exact fun _ he => (conservative_moments_zero s (by decide : 0 < 1) he).1
    · exact fun _ he => (conservative_moments_zero s (by decide : 0 < 1) he).2.2.2
    · intro z hz
      rw [SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j) z hz s.B
        le_rfl,
        pressureField_exterior s (by decide : 0 < 1) z hz s.B le_rfl, zero_add]
    · exact axialHistory_exterior s 0
    · exact hmass
    · exact heta
  have hsrc : SlowStressSupport.exterior s.B S
      (SlowStressSupport.axialDensity h 1 (fluxHistory s) (axialHistory s) (pressureField s 1)) :=
    SlowStressSupport.exterior_axialDensity s.domain.isOpen
      (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
      (pressureField_smooth s 1) h s.B
      (fun j _ => fluxHistory_exterior s j) (fun j _ => axialHistory_exterior s j)
      (pressureField_exterior s (by decide : 0 < 1))
      (SlowStressSupport.exterior_axialOp2 s.domain.isOpen (axialHistory_smooth s 0)
        (axialHistory_exterior s 0) h _ s.domain.denominator)
  have hd : SlowStressSupport.exterior s.B S (SlowResidualMatching.zDensity h (asSlowProfiles s) 1)
    := by
    intro eta heta R hR
    rw [zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ R, heta⟩]
    exact hsrc eta heta R hR
  have hm : ∀ eta ∈ S,
      SlowStressSupport.moment s.B 0 (SlowResidualMatching.zDensity h (asSlowProfiles s) 1) eta = 0
        := by
    intro eta heta
    rw [← hmoment eta heta]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [pow_zero, one_mul]
    exact zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩
  exact fun eta heta R hR => SlowStressSupport.stress_exterior 1 s.B_pos.le hd hm hR heta

/-! ## The literal physical viscosity and its zero total moment -/

theorem physical_angular_germ (F : OutgoingProfile.Profile) {XR cost L : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR cost) {E : ℝ × ℝ → ℝ}
    (hmatch : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, L ≤ X →
      E (X, eta) = HeatedOutgoing.E F XR w.coefficients (X, eta))
    {p : SimilarityProfile.PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1)
    (hL : L < SimilarityProfile.X F.data.h p)
    (hfull : 1 / 2 < Real.log (SimilarityProfile.X F.data.h p /
      OutgoingDilation.switchRadius F XR) + 1 / 5) :
    SimilarityProfile.pullback F.data.h (-CoordinateAlgebra.A F.data.h) E =ᶠ[𝓝 p]
      SlowFirstOrderEdge.physicalAngular (TerminalHistoryBridge.normalization F XR)
        F.data (TerminalHistoryBridge.shift F XR) := by
  have hX := div_pos hs (SimilarityProfile.q_pos F.data.h_pos F.data.h_lt_half ht)
  have hK := OutgoingDilation.switchRadius_pos F XR w.radius_pos
  have hx := (SimilarityProfile.inner_smoothAt F.data.h_pos F.data.h_lt_half ht).continuousAt.fst
  have hc : ContinuousAt (fun q => Real.log (SimilarityProfile.X F.data.h q /
      OutgoingDilation.switchRadius F XR) + 1 / 5) p :=
    ((hx.div_const _).log (div_pos hX hK).ne').add_const _
  filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds ht),
    continuousAt_snd.fst.eventually (Ioi_mem_nhds hs),
    hx.eventually (Ioi_mem_nhds hL), hc.eventually (Ioi_mem_nhds hfull)] with q hqt hqs hqL hqf
  have heta := TerminalHistoryBridge.eta_mem_interior F.data.h_pos F.data.h_lt_half hqt
  change L < SimilarityProfile.X F.data.h q at hqL
  have he := TerminalHistoryBridge.physicalAngular_eq_terminal F w.radius_pos w.coefficients hqt
    hqs hqf.le
  change SimilarityProfile.q F.data.h q ^ (-CoordinateAlgebra.A F.data.h) *
      E (SimilarityProfile.X F.data.h q, SimilarityProfile.eta F.data.h q) = _
  rw [hmatch _ heta _ hqL.le]
  exact he

/-- On the switched tail the actual second axial derivative is the source
used in the independently constructed flat terminal primitive. -/
theorem actual_viscosity_eq_terminal (F : OutgoingProfile.Profile) {XR cost L : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR cost) {E G : ℝ × ℝ → ℝ}
    (hG : SlowStressSupport.Smooth (Ioo (-1) 1) G)
    (hGE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1, G (R, eta) = E (R ^ 2 / 2, eta))
    (hmatch : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, L ≤ X →
      E (X, eta) = HeatedOutgoing.E F XR w.coefficients (X, eta))
    {R eta : ℝ} (hR : 0 < R) (heta : eta ∈ Ioo (-1 : ℝ) 1)
    (hL : L < R ^ 2 / 2)
    (hfull : 1 / 2 < Real.log ((R ^ 2 / 2) / OutgoingDilation.switchRadius F XR) + 1 / 5) :
    SlowStressSupport.axialOp2 F.data.h (SlowStressSupport.orderExponent F.data.h 0) G (R, eta) =
      -SlowFirstOrderEdge.radialSource (TerminalHistoryBridge.normalization F XR)
        F.data (TerminalHistoryBridge.shift F XR) eta R := by
  obtain ⟨ht, hq, he⟩ := RenormalizedHeatMoment.normalized_coordinates F.data.h_pos
    F.data.h_lt_half heta
  let p : SimilarityProfile.PhysicalPoint := (eta ^ 2, (R ^ 2 / 2, eta))
  have hqp : SimilarityProfile.q F.data.h p = 1 := hq
  have hep : SimilarityProfile.eta F.data.h p = eta := he
  have hxp : SimilarityProfile.X F.data.h p = R ^ 2 / 2 := by
    simp only [SimilarityProfile.X, hqp, div_one, p]
  have hg := physical_angular_germ F w hmatch (p := p) ht (by dsimp [p]; positivity)
    (by simpa only [hxp] using hL) (by simpa only [hxp] using hfull)
  have hc : ContinuousAt (fun z : ℝ => (eta ^ 2, (R ^ 2 / 2, z))) eta :=
    continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)
  have hg' := hg.comp_tendsto hc
  have hu : RenormalizedHeatMoment.uTheta F.data.h E (eta ^ 2) R =ᶠ[𝓝 eta]
      (fun z => SlowFirstOrderEdge.physicalAngular (TerminalHistoryBridge.normalization F XR)
        F.data (TerminalHistoryBridge.shift F XR) (eta ^ 2, (R ^ 2 / 2, z))) := by
    filter_upwards [hg'] with z hz
    rw [RenormalizedHeatMoment.uTheta_eq_similarity_pullback]
    exact hz
  have hd := hu.deriv.deriv_eq
  have hv := SlowResidualMatching.normalized_axial_viscosity F.data.h_pos F.data.h_lt_half hG hGE
    heta hR
  have hf := SlowFirstOrderEdge.physicalSource_radial_scaled (TerminalHistoryBridge.normalization F
    XR)
    F.data (TerminalHistoryBridge.shift F XR) (t := eta ^ 2) (z := eta) ht hR
  have hscale : SlowFirstOrderEdge.physicalScale F.data (eta ^ 2) eta = 1 := hq
  have heta' : SlowFirstOrderEdge.physicalEta F.data (eta ^ 2) eta = eta := he
  rw [hscale, heta', Real.one_rpow, Real.sqrt_one, div_one, one_mul] at hf
  change -deriv (deriv (fun z => SlowFirstOrderEdge.physicalAngular
      (TerminalHistoryBridge.normalization F XR) F.data (TerminalHistoryBridge.shift F XR)
      (eta ^ 2, (R ^ 2 / 2, z)))) eta = _ at hf
  rw [← hd, hv] at hf
  have hexp : SlowStressSupport.orderExponent F.data.h 0 = -CoordinateAlgebra.A F.data.h := by
    simp [SlowStressSupport.orderExponent, SlowExpansionResidual.slowOrder,
      PositiveAxisSystem.a, CoordinateAlgebra.A]
  rw [hexp]
  linarith

theorem actual_viscosity_total_zero (F : OutgoingProfile.Profile) {XR cost L : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR cost) {E G : ℝ × ℝ → ℝ}
    (hG : SlowStressSupport.Smooth (Ioo (-1) 1) G)
    (hGE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1, G (R, eta) = E (R ^ 2 / 2, eta))
    (hmatch : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, L ≤ X →
      E (X, eta) = HeatedOutgoing.E F XR w.coefficients (X, eta))
    (hreset : ∀ eta ∈ Ioo (-1 : ℝ) 1,
      (∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) * E (X, eta) - OutgoingDilation.powerH F XR X) =
      ∫ X in Ioi (0 : ℝ), HeatedOutgoing.H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F
        XR X)
    {eta : ℝ} (heta : eta ∈ Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun R => R ^ 2 *
      SlowStressSupport.axialOp2 F.data.h (SlowStressSupport.orderExponent F.data.h 0) G (R, eta))
        (Ioi 0) ∧
    (∫ R in Ioi (0 : ℝ), R ^ 2 *
      SlowStressSupport.axialOp2 F.data.h (SlowStressSupport.orderExponent F.data.h 0) G (R, eta))
        = 0 := by
  obtain ⟨ht, _, _⟩ := RenormalizedHeatMoment.normalized_coordinates F.data.h_pos F.data.h_lt_half
    heta
  have hz := RenormalizedHeatMoment.heated_nominal_axial_viscosity F w F.data.h_lt_half ht L
    hG hGE hmatch hreset eta
  have he : EqOn (fun R => R ^ 2 * deriv (deriv (RenormalizedHeatMoment.uTheta F.data.h E (eta ^ 2)
    R)) eta)
      (fun R => R ^ 2 * SlowStressSupport.axialOp2 F.data.h
        (SlowStressSupport.orderExponent F.data.h 0) G (R, eta)) (Ioi 0) := by
    intro R hR
    dsimp only
    rw [SlowResidualMatching.normalized_axial_viscosity F.data.h_pos F.data.h_lt_half hG hGE heta
      hR]
    simp [SlowStressSupport.orderExponent, SlowExpansionResidual.slowOrder,
      PositiveAxisSystem.a, CoordinateAlgebra.A]
  exact ⟨hz.1.congr_fun he measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi he).symm.trans hz.2⟩

theorem full_switch_monotone (F : OutgoingProfile.Profile) {XR R r : ℝ}
    (hXR : 0 < XR) (hR : 0 < R) (hr : R ≤ r)
    (hf : 1 / 2 < Real.log ((R ^ 2 / 2) / OutgoingDilation.switchRadius F XR) + 1 / 5) :
    1 / 2 < Real.log ((r ^ 2 / 2) / OutgoingDilation.switchRadius F XR) + 1 / 5 := by
  have hK := OutgoingDilation.switchRadius_pos F XR hXR
  have hp : 0 < (R ^ 2 / 2) / OutgoingDilation.switchRadius F XR := by positivity
  have hs : R ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hR.le (hR.le.trans hr)).mpr hr
  have hl := Real.log_le_log hp (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hs (by norm_num)) hK.le)
  linarith

/-- The forward first-order primitive equals the backward terminal one.
The total viscosity moment is derived from the same original reset row. -/
theorem first_angular_eq_backward (F : OutgoingProfile.Profile) {XR cost L C : ℝ}
    (w : HeatedOutgoing.CompensationWitness F XR cost) {S : Set ℝ} (s : Scheme S F.data.h C)
    (hS : Ioo (-1 : ℝ) 1 ⊆ S)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) {E : ℝ × ℝ → ℝ}
    (hGE : ∀ R : ℝ, 0 < R → ∀ eta ∈ Ioo (-1 : ℝ) 1,
      angularHistory s 0 (R, eta) = E (R ^ 2 / 2, eta))
    (hmatch : ∀ eta ∈ Ioo (-1 : ℝ) 1, ∀ X : ℝ, L ≤ X →
      E (X, eta) = HeatedOutgoing.E F XR w.coefficients (X, eta))
    (hreset : ∀ eta ∈ Ioo (-1 : ℝ) 1,
      (∫ X in Ioi (0 : ℝ), Real.sqrt (2 * X) * E (X, eta) - OutgoingDilation.powerH F XR X) =
      ∫ X in Ioi (0 : ℝ), HeatedOutgoing.H F XR w.coefficients (X, eta) - OutgoingDilation.powerH F
        XR X)
    {R eta : ℝ} (hR : s.B ≤ R) (heta : eta ∈ Ioo (-1 : ℝ) 1)
    (hL : L < R ^ 2 / 2)
    (hfull : 1 / 2 < Real.log ((R ^ 2 / 2) / OutgoingDilation.switchRadius F XR) + 1 / 5) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity F.data.h C (asSlowProfiles s) 1)
      (R, eta) =
      SlowFirstOrderEdge.radialStress (TerminalHistoryBridge.normalization F XR)
        F.data (TerminalHistoryBridge.shift F XR) eta R := by
  have hRp : 0 < R := s.B_pos.trans_le hR
  have hG : SlowStressSupport.Smooth (Ioo (-1) 1) (angularHistory s 0) :=
    (angularHistory_smooth s 0).mono (prod_mono_right hS)
  obtain ⟨hi, hz⟩ := actual_viscosity_total_zero F w hG hGE hmatch hreset heta
  have hsplit := TerminalHistoryBridge.split_positive_integral hi hRp.le
  rw [hz] at hsplit
  have he : (∫ r in Ioi R, r ^ 2 * SlowFirstOrderEdge.radialSource
      (TerminalHistoryBridge.normalization F XR) F.data (TerminalHistoryBridge.shift F XR) eta r) =
      -(∫ r in Ioi R, r ^ 2 * SlowStressSupport.axialOp2 F.data.h
        (SlowStressSupport.orderExponent F.data.h 0) (angularHistory s 0) (r, eta)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have hsq : R ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hRp.le (hRp.trans hr).le).mpr hr.le
    have hv := actual_viscosity_eq_terminal F w hG hGE hmatch (hRp.trans hr) heta
      (hL.trans_le (div_le_div_of_nonneg_right hsq (by norm_num)))
      (full_switch_monotone F w.radius_pos hRp hr.le hfull)
    rw [hv]
    ring
  rw [first_angular_balance s hbase hR (hS heta)]
  unfold SlowFirstOrderEdge.radialStress TerminalStress.backwardStress
  rw [he]
  congr 1
  unfold SlowStressSupport.moment
  rw [intervalIntegral.integral_of_le hRp.le]
  linarith

/-! ## Identifying the common extension with its actual radial primitive -/

theorem coefficients_stress_eq_window {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ)
    {p : ℝ × ℝ} (hX : 0 ≤ p.1) (heta : |p.2| ≤ (commonWindow s hI).inner) :
    (coefficients L B0 Z0 hI).stressTheta n p = SlowResidualMatching.thetaStress h C
      (asSlowProfiles s) n p ∧
    (coefficients L B0 Z0 hI).stressAxial n p = SlowResidualMatching.zStress h (asSlowProfiles s) n
      p := by
  constructor
  · change extendCoreZero _ _ _ p = _
    rw [extendCoreZero_eq _ L.inner_pos _ (fun _ he _ hr => thetaEven_zero L B0 Z0 n hr he) hX heta]
    exact thetaEven_eq L B0 Z0 n (Real.sqrt_nonneg _)
  · change extendCoreZero _ _ _ p = _
    rw [extendCoreZero_eq _ L.inner_pos _ (fun _ he _ hr => zEven_zero L B0 Z0 n hr he) hX heta]
    exact zEven_eq L B0 Z0 n (Real.sqrt_nonneg _)

theorem coefficients_stress_germ {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S) (n : ℕ)
    {p : ℝ × ℝ} (hX : 0 < p.1) (heta : |p.2| ≤ 1) :
    (fun q => ((coefficients L B0 Z0 hI).stressTheta n q, (coefficients L B0 Z0 hI).stressAxial n
      q)) =ᶠ[𝓝 p]
      (fun q => (SlowResidualMatching.thetaStress h C (asSlowProfiles s) n q,
        SlowResidualMatching.zStress h (asSlowProfiles s) n q)) := by
  have he : |p.2| < (commonWindow s hI).inner := heta.trans_lt (commonWindow s hI).one_lt_inner
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hX, abs_lt.mp he⟩] with q hq
  have hh := coefficients_stress_eq_window L B0 Z0 hI n hq.1.le (abs_lt.mpr hq.2).le
  exact Prod.ext hh.1 hh.2

section Nominal

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

theorem nominal_angular_zero_eq {R eta : ℝ} (hR : 0 < R) (heta : eta ∈ nominalParameters W) :
    angularHistory (nominalScheme W) 0 (R, eta) = W.E (R ^ 2 / 2, eta) := by
  rw [angularHistory_eq _ _ heta, profiles_zero]
  have hh := baseFields_angular (nominalDomain W) W.axis.normalization W.profiles
    (nominalParameters_domain W) W.axis.normalization_pos.ne' (eta := eta) hR.le
  change angularField W.axis.normalization
      (baseFields (nominalDomain W) W.axis.normalization W.profiles (nominalParameters_domain
        W)).phi (R, eta) = _
  exact hh.trans (W.E_eq_sqrt_f (p := (R ^ 2 / 2, eta)) (by positivity)).symm

theorem nominal_axial_mass_zero {eta : ℝ} (heta : eta ∈ nominalParameters W) :
    SlowStressSupport.moment (nominalScheme W).B 1 (axialHistory (nominalScheme W) 0) eta = 0 := by
  have he : SlowStressSupport.moment (nominalScheme W).B 1 (axialHistory (nominalScheme W) 0) eta =
      PositiveOrderMoments.massHistory (nominalScheme W).base.axial ((nominalScheme W).B, eta) := by
    apply intervalIntegral.integral_congr
    intro R _
    dsimp only
    rw [axialHistory_eq _ _ heta, profiles_zero]
    simp only [pow_one, PositiveOrderMoments.weightedAxial]
  rw [he]
  change PositiveOrderMoments.massHistory
    (baseFields (nominalDomain W) W.axis.normalization W.profiles (nominalParameters_domain
      W)).axial
      (nominalOuterRadius W, eta) = 0
  rw [baseFields_mass _ _ _ _ (nominalOuterRadius_pos W).le heta]
  exact nominal_mass_exterior W (nominalParameters_domain W) eta heta

theorem nominal_first_axial_zero {p : ℝ × ℝ} (hX : nominalOuterX W ≤ p.1) :
    (nominalCoefficients W).stressAxial 1 p = 0 := by
  have hz := first_axial_exterior (nominalScheme W) (nominal_base_beta W)
    (fun _ he => nominal_axial_mass_zero W he)
  change extendCoreZero _ _ _ p = 0
  apply extendCoreZero_zero_right _ _ _ (nominalOuterRadius_pos W).le _
    (by simpa only [nominalOuterRadius_square] using hX)
  intro eta heta R hR
  rw [zEven_eq _ _ _ _ ((nominalOuterRadius_pos W).le.trans hR)]
  exact hz eta heta R hR

theorem nominal_first_angular_eq {p : ℝ × ℝ} (hX : nominalOuterX W < p.1)
    (heta : p.2 ∈ Ioo (-1 : ℝ) 1)
    (hfull : 1 / 2 < Real.log (p.1 / OutgoingDilation.switchRadius F W.controls.radius) + 1 / 5) :
    (nominalCoefficients W).stressTheta 1 p =
      SlowFirstOrderEdge.stressX (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) p := by
  have hp : 0 < p.1 := (nominalOuterX_pos W).trans hX
  have he : p.2 ∈ Icc (-1 : ℝ) 1 := ⟨heta.1.le, heta.2.le⟩
  rw [(nominalCoefficients_stress_eq W hp.le (abs_le.mpr he) 1).1,
    SlowFirstOrderEdge.stressX_eq_radialStress _ _ _ hp]
  change SlowStressSupport.stress 2 _ (Real.sqrt (2 * p.1), p.2) = _
  have hs : (Real.sqrt (2 * p.1)) ^ 2 / 2 = p.1 := by rw [Real.sq_sqrt (by positivity)]; ring
  apply first_angular_eq_backward F W.heat.physical (nominalScheme W)
    (fun _ ht => nominalParameters_contains W ⟨ht.1.le, ht.2.le⟩) (nominal_base_beta W)
    (E := W.E) (L := nominalOuterX W)
  · intro R hR eta heta
    exact nominal_angular_zero_eq W hR (nominalParameters_contains W ⟨heta.1.le, heta.2.le⟩)
  · intro eta heta X hX
    exact (W.heat_agreement
      (W.controls.heatJoin_lt_radius.trans ((nominalOuterX_gt_radius W).trans_le hX))
      ⟨heta.1.le, heta.2.le⟩).2.1
  · intro eta heta
    rw [(W.five_moments ⟨heta.1.le, heta.2.le⟩).angular_zero,
      W.heat.physical.renormalized_zero eta ⟨heta.1.le, heta.2.le⟩]
  · change nominalOuterRadius W ≤ Real.sqrt (2 * p.1)
    rw [← Real.sqrt_sq (nominalOuterRadius_pos W).le]
    apply Real.sqrt_le_sqrt
    have hb := nominalOuterRadius_square W
    linarith
  · exact heta
  · rwa [hs]
  · rwa [hs]

end Nominal

/-! ## Closed-parameter derivative tensors and the weighted collar estimate -/

theorem iteratedFDeriv_eq_closed_parameter {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : (ℝ × ℝ) → V} {cut : ℝ} (hcut : 0 ≤ cut)
    (hf : ∀ p : ℝ × ℝ, 0 < p.1 → ContDiffAt ℝ ∞ f p)
    (hg : ∀ p : ℝ × ℝ, 0 < p.1 → ContDiffAt ℝ ∞ g p)
    (he : EqOn f g (Ioi cut ×ˢ Ioo (-1 : ℝ) 1))
    (m : ℕ) {p : ℝ × ℝ} (hp : cut < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m g p := by
  have hj : EqOn (fun eta => iteratedFDeriv ℝ m f (p.1, eta))
      (fun eta => iteratedFDeriv ℝ m g (p.1, eta)) (Ioo (-1 : ℝ) 1) := by
    intro eta heta
    have hfg : f =ᶠ[𝓝 (p.1, eta)] g := by
      filter_upwards [(isOpen_Ioi.prod isOpen_Ioo).mem_nhds
        (show (p.1, eta) ∈ Ioi cut ×ˢ Ioo (-1 : ℝ) 1 from ⟨hp, heta⟩)] with q hq
      exact he hq
    have hh : f =ᶠ[𝓝[univ] (p.1, eta)] g := by simpa only [nhdsWithin_univ] using hfg
    simpa only [iteratedFDerivWithin_univ] using
      hh.iteratedFDerivWithin_eq (𝕜 := ℝ) hfg.self_of_nhds m
  have hc (u : (ℝ × ℝ) → V) (hu : ∀ p : ℝ × ℝ, 0 < p.1 → ContDiffAt ℝ ∞ u p) :
      Continuous (fun eta => iteratedFDeriv ℝ m u (p.1, eta)) := by
    apply continuous_iff_continuousAt.mpr
    intro eta
    have hs : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ m u) (p.1, eta) :=
      (hu (p.1, eta) (hcut.trans_lt hp)).iteratedFDeriv_right (WithTop.coe_le_coe.mpr le_top)
    exact hs.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  apply hj.closure (hc f hf) (hc g hg)
  simpa only [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using heta

noncomputable def terminalAmplitude {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
  ℝ :=
  TerminalHistoryBridge.normalization F W.controls.radius

noncomputable def terminalShift {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : ℝ :=
  TerminalHistoryBridge.shift F W.controls.radius

noncomputable def terminalInner {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) : ℝ :=
  Real.exp (terminalShift W + 1)

theorem terminalInner_pos {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    0 < terminalInner W := Real.exp_pos _

theorem switch_lt_terminalInner {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    OutgoingDilation.switchRadius F W.controls.radius < terminalInner W := by
  have hK := OutgoingDilation.switchRadius_pos F W.controls.radius W.controls.radius_pos
  rw [terminalInner, ← Real.exp_log hK]
  apply Real.exp_lt_exp.mpr
  unfold terminalShift TerminalHistoryBridge.shift
  linarith

theorem terminalInner_full {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {X : ℝ} (hX : terminalInner W < X) :
    nominalOuterX W < X ∧
      1 / 2 < Real.log (X / OutgoingDilation.switchRadius F W.controls.radius) + 1 / 5 := by
  have hK := OutgoingDilation.switchRadius_pos F W.controls.radius W.controls.radius_pos
  have hp : 0 < X := (terminalInner_pos W).trans hX
  refine ⟨(nominalOuterX_lt_switch W).trans ((switch_lt_terminalInner W).trans hX), ?_⟩
  have hl : terminalShift W + 1 < Real.log X := (Real.lt_log_iff_exp_lt hp).mpr hX
  rw [Real.log_div hp.ne' hK.ne']
  unfold terminalShift TerminalHistoryBridge.shift at hl
  linarith

theorem nominal_first_pair_eq {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F) :
    EqOn (BaseResidual.stressPair (nominalCoefficients W) 1)
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p hp
  have hc := terminalInner_full W hp.1
  exact Prod.ext (nominal_first_angular_eq W hc.1 hp.2 hc.2) (nominal_first_axial_zero W hc.1.le)

/-- The scalar terminal factor has the same entire derivative tensor as the
actual stress through both physical parameter endpoints.  The proof uses
continuity of each tensor, without identifying different outside extensions. -/
theorem edgeJets_of_interior_equality {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {f : (ℝ × ℝ) → ℝ × ℝ} (hf : ContDiff ℝ ∞ f)
    (he : EqOn f
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1))
    {c left : ℝ} (hc : 0 < c) (hl : left < terminalShift W + 2) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (terminalShift W + 3 - 1)) (terminalShift W + 3))
      (BaseResidual.activeZeta c left (terminalShift W + 3))
      (BaseResidual.activeDelta left (terminalShift W + 3)) f := by
  have hs := BaseResidual.firstOrder_pair_outer_edgeJets
    (terminalAmplitude W) F.data (terminalShift W) hc (by norm_num : (0 : ℝ) < 1)
    (by linarith : left < terminalShift W + 3 - 1)
    (F := fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
    (fun _ _ => Filter.EventuallyEq.rfl)
  intro m
  obtain ⟨A, hA, N, hb⟩ := hs m
  refine ⟨A, hA, N, ?_⟩
  intro p hp
  have hpi : terminalInner W < p.1 := by
    apply lt_of_lt_of_le _ hp.1.1
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [iteratedFDeriv_eq_closed_parameter (terminalInner_pos W).le
    (fun _ _ => hf.contDiffAt)
    (fun q hq => ((SlowFirstOrderEdge.stressX_contDiffOn (terminalAmplitude W) F.data
      (terminalShift W)).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hq)).prodMk contDiffAt_const)
    he m hpi hp.2]
  exact hb p hp

theorem nominal_first_edgeJets {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {c left : ℝ} (hc : 0 < c) (hl : left < terminalShift W + 2) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (terminalShift W + 3 - 1)) (terminalShift W + 3))
      (BaseResidual.activeZeta c left (terminalShift W + 3))
      (BaseResidual.activeDelta left (terminalShift W + 3))
      (BaseResidual.stressPair (nominalCoefficients W) 1) := by
  have hs := nominalCoefficients_smooth W
  exact edgeJets_of_interior_equality W ((hs.stressTheta 1).prodMk (hs.stressAxial 1))
    (nominal_first_pair_eq W) hc hl

/-! ## Transfer through a finite modification with the restored angular row -/

theorem moment_axialOp_congr {S : Set ℝ} (hS : IsOpen S) {f g : SlowStressSupport.Field}
    (hf : SlowStressSupport.Smooth S f) (hg : SlowStressSupport.Smooth S g)
    (h b R : ℝ) (m : ℕ)
    (hm : ∀ eta ∈ S, SlowStressSupport.moment R m f eta = SlowStressSupport.moment R m g eta)
    (hb : ∀ eta ∈ S, f (R, eta) = g (R, eta)) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment R m (SlowStressSupport.axialOp h b f) eta =
      SlowStressSupport.moment R m (SlowStressSupport.axialOp h b g) eta := by
  have he : SlowStressSupport.moment R m f =ᶠ[𝓝 eta] SlowStressSupport.moment R m g := by
    filter_upwards [hS.mem_nhds heta] with z hz
    exact hm z hz
  have hd := he.deriv_eq
  rw [(SlowStressSupport.moment_hasDerivAt hS hf R m heta).deriv,
    (SlowStressSupport.moment_hasDerivAt hS hg R m heta).deriv] at hd
  rw [SlowStressSupport.moment_axialOp hS hf h b R m heta,
    SlowStressSupport.moment_axialOp hS hg h b R m heta, hm eta heta, hb eta heta, hd]

theorem moment_axialOp2_congr {S : Set ℝ} (hS : IsOpen S) {f g : SlowStressSupport.Field}
    (hf : SlowStressSupport.Smooth S f) (hg : SlowStressSupport.Smooth S g)
    (h b R : ℝ) (m : ℕ) (hL : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hm : ∀ eta ∈ S, SlowStressSupport.moment R m f eta = SlowStressSupport.moment R m g eta)
    (hfg : ∀ eta ∈ S, f =ᶠ[𝓝 (R, eta)] g) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment R m (SlowStressSupport.axialOp2 h b f) eta =
      SlowStressSupport.moment R m (SlowStressSupport.axialOp2 h b g) eta := by
  apply moment_axialOp_congr hS (SlowStressSupport.smooth_axialOp hS hf h b hL)
    (SlowStressSupport.smooth_axialOp hS hg h b hL) h (b - PositiveAxisSystem.dScale h) R m
  · exact fun z hz => moment_axialOp_congr hS hf hg h b R m hm
      (fun z hz => (hfg z hz).self_of_nhds) hz
  · intro z hz
    have he := hfg z hz
    simp only [SlowStressSupport.axialOp, SlowStressSupport.de, SlowStressSupport.dr,
      ProfileHistories.parameterPartial, ProfileHistories.radialPartial, he.fderiv_eq,
        he.self_of_nhds]
  · exact heta

theorem angular_moment_of_baseFields {S : Set ℝ} {h C : ℝ} {D : ProfileHistories.RadialDomain}
    (d : Domain S h) (P : ProfileHistories.Profiles D)
    (hD : ∀ X, 0 ≤ X → ∀ eta ∈ S, (X, eta) ∈ D.carrier) (hC : C ≠ 0)
    {R eta : ℝ} (hR : 0 ≤ R) (heta : eta ∈ S) :
    SlowStressSupport.moment R 2 (angularField C (baseFields d C P hD).phi) eta =
      P.I (R ^ 2 / 2, eta) := by
  let H := radialPullback P.H P.H_smooth hD
  have he : SlowStressSupport.moment R 2 (angularField C (baseFields d C P hD).phi) eta =
      PositiveOrderMoments.massHistory H (R, eta) := by
    apply intervalIntegral.integral_congr
    intro r _
    change r ^ 2 * (r / C * (C * P.f (r ^ 2 / 2, eta))) = r * (2 * (r ^ 2 / 2) * P.f (r ^ 2 / 2,
      eta))
    field_simp
  rw [he]
  apply massHistory_of_composition H P.H hR
  · exact P.H_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun X hX => hD X hX.1 eta heta)
  · exact fun _ _ => rfl

theorem scheme_angular_moment_zero {S : Set ℝ} {h C R eta : ℝ} (s : Scheme S h C)
    (heta : eta ∈ S) :
    SlowStressSupport.moment R 2 (angularHistory s 0) eta =
      SlowStressSupport.moment R 2 (angularField C s.base.phi) eta := by
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [angularHistory_eq s 0 heta, profiles_zero]

theorem history_equal_after {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D') {R X eta : ℝ}
    (hR : 0 ≤ R) (hX : R ≤ X)
    (hP : ∀ x ∈ Icc 0 X, (x, eta) ∈ D.carrier)
    (hQ : ∀ x ∈ Icc 0 X, (x, eta) ∈ D'.carrier)
    (hI : P.I (R, eta) = Q.I (R, eta))
    (he : ∀ x ∈ Icc R X, P.f (x, eta) = Q.f (x, eta)) :
    P.I (X, eta) = Q.I (X, eta) := by
  have hcP : ContinuousOn (fun x => P.H (x, eta)) (Icc 0 X) :=
    P.H_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hP
  have hcQ : ContinuousOn (fun x => Q.H (x, eta)) (Icc 0 X) :=
    Q.H_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hQ
  have iP0 := (hcP.mono (Icc_subset_Icc le_rfl hX)).intervalIntegrable_of_Icc (μ := volume) hR
  have iQ0 := (hcQ.mono (Icc_subset_Icc le_rfl hX)).intervalIntegrable_of_Icc (μ := volume) hR
  have iPR := (hcP.mono (Icc_subset_Icc hR le_rfl)).intervalIntegrable_of_Icc (μ := volume) hX
  have iQR := (hcQ.mono (Icc_subset_Icc hR le_rfl)).intervalIntegrable_of_Icc (μ := volume) hX
  have heI : (∫ x in R..X, P.H (x, eta)) = ∫ x in R..X, Q.H (x, eta) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hX] at hx
    simp only [ProfileHistories.Profiles.H, he x hx]
  change (∫ x in (0 : ℝ)..R, P.H (x, eta)) = ∫ x in (0 : ℝ)..R, Q.H (x, eta) at hI
  change (∫ x in (0 : ℝ)..X, P.H (x, eta)) = ∫ x in (0 : ℝ)..X, Q.H (x, eta)
  rw [← intervalIntegral.integral_add_adjacent_intervals iP0 iPR,
    ← intervalIntegral.integral_add_adjacent_intervals iQ0 iQR, hI, heI]

section Modified

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M

theorem modified_angular_history
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {X eta : ℝ} (hX : nominalOuterX W ≤ X) (heta : eta ∈ S) :
    Q.I (X, eta) = W.profiles.I (X, eta) := by
  apply history_equal_after Q W.profiles (nominalOuterX_pos W).le hX
    (fun x hx => M.halfPlane x hx.1 eta heta)
    (fun x hx => modified_original_domain W Q M x hx.1 eta heta) (hI eta heta)
  intro x hx
  exact (M.fields (x, eta) ((nominalOuterX_pos W).le.trans hx.1) heta
    (Or.inr ((modification_before_outer W Q M).le.trans hx.1))).1

theorem modified_angular_moment_eq
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {R eta : ℝ} (hR : nominalOuterRadius W ≤ R) (heta : eta ∈ S) :
    SlowStressSupport.moment R 2 (angularHistory (modifiedScheme W Q M) 0) eta =
      SlowStressSupport.moment R 2 (angularHistory (nominalScheme W) 0) eta := by
  have hRp := (nominalOuterRadius_pos W).le.trans hR
  rw [scheme_angular_moment_zero _ heta, scheme_angular_moment_zero _ (M.subset heta)]
  change SlowStressSupport.moment R 2
      (angularField W.axis.normalization (baseFields (modifiedDomain W Q M) W.axis.normalization Q
        M.halfPlane).phi) eta =
    SlowStressSupport.moment R 2
      (angularField W.axis.normalization (baseFields (nominalDomain W) W.axis.normalization
        W.profiles
        (nominalParameters_domain W)).phi) eta
  rw [angular_moment_of_baseFields _ _ _ W.axis.normalization_pos.ne' hRp heta,
    angular_moment_of_baseFields _ _ _ W.axis.normalization_pos.ne' hRp (M.subset heta)]
  apply modified_angular_history W Q M hI _ heta
  have hb := nominalOuterRadius_square W
  have hs := (sq_le_sq₀ (nominalOuterRadius_pos W).le hRp).mpr hR
  linarith

theorem modified_angular_zero_eq {R eta : ℝ} (hR : 0 ≤ R) (heta : eta ∈ S) :
    angularHistory (modifiedScheme W Q M) 0 (R, eta) = Q.E (R ^ 2 / 2, eta) := by
  rw [angularHistory_eq _ _ heta, profiles_zero]
  exact baseFields_angular (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane
    W.axis.normalization_pos.ne' hR

theorem modified_angular_zero_germ {R eta : ℝ} (hR : nominalOuterRadius W < R) (heta : eta ∈ S) :
    angularHistory (modifiedScheme W Q M) 0 =ᶠ[𝓝 (R, eta)] angularHistory (nominalScheme W) 0 := by
  filter_upwards [(isOpen_Ioi.prod M.isOpen).mem_nhds
    (show (R, eta) ∈ Ioi (nominalOuterRadius W) ×ˢ S from ⟨hR, heta⟩)] with p hp
  have hRp := (nominalOuterRadius_pos W).trans hp.1
  have hX : nominalOuterX W < p.1 ^ 2 / 2 := by
    have hh := (sq_lt_sq₀ (nominalOuterRadius_pos W).le hRp.le).mpr hp.1
    rw [← nominalOuterRadius_square W]
    linarith
  rw [modified_angular_zero_eq W Q M hRp.le hp.2,
    nominal_angular_zero_eq W hRp (M.subset hp.2)]
  change Real.sqrt (2 * (p.1 ^ 2 / 2)) * Q.f (p.1 ^ 2 / 2, p.2) = _
  rw [(M.fields (p.1 ^ 2 / 2, p.2) (by positivity) hp.2
    (Or.inr ((modification_before_outer W Q M).le.trans hX.le))).1]
  exact (W.E_eq_sqrt_f (p := (p.1 ^ 2 / 2, p.2)) (by positivity)).symm

theorem modified_viscosity_moment_eq
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {R eta : ℝ} (hR : nominalOuterRadius W < R) (heta : eta ∈ S) :
    SlowStressSupport.moment R 2 (SlowStressSupport.axialOp2 F.data.h
      (SlowStressSupport.orderExponent F.data.h 0) (angularHistory (modifiedScheme W Q M) 0)) eta =
    SlowStressSupport.moment R 2 (SlowStressSupport.axialOp2 F.data.h
      (SlowStressSupport.orderExponent F.data.h 0) (angularHistory (nominalScheme W) 0)) eta := by
  apply moment_axialOp2_congr M.isOpen (angularHistory_smooth (modifiedScheme W Q M) 0)
    ((angularHistory_smooth (nominalScheme W) 0).mono (prod_mono_right M.subset))
    F.data.h _ R 2 (modifiedDomain W Q M).denominator
    (fun _ he => modified_angular_moment_eq W Q M hI hR.le he)
    (fun _ he => modified_angular_zero_germ W Q M hR he) heta

omit M in
theorem outerRadius_lt_sqrt {X : ℝ} (hX : nominalOuterX W < X) :
    nominalOuterRadius W < Real.sqrt (2 * X) := by
  have hp : 0 < X := (nominalOuterX_pos W).trans hX
  have hs := Real.sq_sqrt (show 0 ≤ 2 * X by positivity)
  have hb := nominalOuterRadius_square W
  nlinarith [Real.sqrt_nonneg (2 * X), nominalOuterRadius_pos W]

theorem modified_first_theta_eq_nominal
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {p : ℝ × ℝ} (hX : nominalOuterX W < p.1) (heta : |p.2| ≤ 1) :
    (modifiedCoefficients W Q M).stressTheta 1 p = (nominalCoefficients W).stressTheta 1 p := by
  have hp := (nominalOuterX_pos W).trans hX
  have hη := M.contains (abs_le.mp heta)
  have hR := outerRadius_lt_sqrt W hX
  have hm := (coefficients_stress_eq (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains 1 hp.le heta).1
  change (modifiedCoefficients W Q M).stressTheta 1 p = _ at hm
  rw [hm,
    (nominalCoefficients_stress_eq W hp.le heta 1).1]
  change SlowStressSupport.stress 2 _ (Real.sqrt (2 * p.1), p.2) =
    SlowStressSupport.stress 2 _ (Real.sqrt (2 * p.1), p.2)
  rw [first_angular_balance (modifiedScheme W Q M) rfl hR.le hη,
    first_angular_balance (nominalScheme W) (nominal_base_beta W) hR.le (M.subset hη),
    modified_viscosity_moment_eq W Q M hI hR hη]

theorem modified_axial_mass_zero {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment (modifiedScheme W Q M).B 1 (axialHistory (modifiedScheme W Q M) 0) eta
      = 0 := by
  have he : SlowStressSupport.moment (modifiedScheme W Q M).B 1 (axialHistory (modifiedScheme W Q
    M) 0) eta =
      PositiveOrderMoments.massHistory (modifiedScheme W Q M).base.axial ((modifiedScheme W Q M).B,
        eta) := by
    apply intervalIntegral.integral_congr
    intro R _
    dsimp only
    rw [axialHistory_eq _ _ heta, profiles_zero]
    simp only [pow_one, PositiveOrderMoments.weightedAxial]
  rw [he]
  change PositiveOrderMoments.massHistory
    (baseFields (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane).axial
      (nominalOuterRadius W, eta) = 0
  rw [baseFields_mass _ _ _ _ (nominalOuterRadius_pos W).le heta]
  exact modified_mass_zero W Q M eta heta

theorem modified_first_axial_zero {p : ℝ × ℝ} (hX : nominalOuterX W ≤ p.1) :
    (modifiedCoefficients W Q M).stressAxial 1 p = 0 := by
  have hz := first_axial_exterior (modifiedScheme W Q M) rfl
    (fun _ he => modified_axial_mass_zero W Q M he)
  change extendCoreZero _ _ _ p = 0
  apply extendCoreZero_zero_right _ _ _ (nominalOuterRadius_pos W).le _
    (by simpa only [nominalOuterRadius_square] using hX)
  intro eta heta R hR
  rw [zEven_eq _ _ _ _ ((nominalOuterRadius_pos W).le.trans hR)]
  exact hz eta heta R hR

theorem modified_first_pair_eq
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta)) :
    EqOn (BaseResidual.stressPair (modifiedCoefficients W Q M) 1)
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p hp
  have hc := terminalInner_full W hp.1
  have he : |p.2| ≤ 1 := abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩
  exact Prod.ext ((modified_first_theta_eq_nominal W Q M hI hc.1 he).trans
    (nominal_first_angular_eq W hc.1 hp.2 hc.2)) (modified_first_axial_zero W Q M hc.1.le)

theorem modified_first_edgeJets
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {c left : ℝ} (hc : 0 < c) (hl : left < terminalShift W + 2) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (terminalShift W + 3 - 1)) (terminalShift W + 3))
      (BaseResidual.activeZeta c left (terminalShift W + 3))
      (BaseResidual.activeDelta left (terminalShift W + 3))
      (BaseResidual.stressPair (modifiedCoefficients W Q M) 1) := by
  have hs := modifiedCoefficients_smooth W Q M
  exact edgeJets_of_interior_equality W ((hs.stressTheta 1).prodMk (hs.stressAxial 1))
    (modified_first_pair_eq W Q M hI) hc hl

end Modified

/-! ## Changing the hierarchy cutoff while retaining the same leading fields -/

theorem first_axial_balance {S : Set ℝ} {h C R : ℝ} (s : Scheme S h C)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hR : s.B ≤ R) {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h (asSlowProfiles s) 1) (R, eta) =
      SlowStressSupport.moment R 1
        (SlowStressSupport.axialOp2 h (SlowStressSupport.orderExponent h 0) (axialHistory s 0)) eta
          / R := by
  have hRp := s.B_pos.trans_le hR
  have haxis : ∀ eta ∈ S, SlowStressSupport.conv 1 (fluxHistory s) (axialHistory s) (0, eta) = 0 :=
    by
    intro z hz
    simp only [SlowStressSupport.conv, fluxHistory_axis s _ hz, zero_mul, Finset.sum_const_zero]
  have hflux : ∀ eta ∈ S,
      SlowStressSupport.conv 1 (axialHistory s) (axialHistory s) (R, eta) + pressureField s 1 (R,
        eta) = 0 := by
    intro z hz
    rw [SlowStressSupport.exterior_conv_left (fun j _ => axialHistory_exterior s j) z hz R hR,
      pressureField_exterior s (by decide : 0 < 1) z hz R hR, zero_add]
  have hb := SlowStressSupport.axial_integral_balance s.domain.isOpen
    (fun j _ => fluxHistory_smooth s j) (fun j _ => axialHistory_smooth s j)
    (pressureField_smooth s 1) h R s.domain.denominator
    (exterior_mono (axialHistory_exterior s 1) hR)
    (fun j _ => exterior_mono (fluxHistory_exterior s j) hR) haxis
    (fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).1)
    (fun _ he => (conservative_moments_at s (by decide : 0 < 1) hR he).2.2.2) hflux heta
  have he : ProfileHistories.primitive (SlowResidualMatching.zDensity h (asSlowProfiles s) 1) (R,
    eta) =
      SlowStressSupport.moment R 0
        (SlowStressSupport.axialDensity h 1 (fluxHistory s) (axialHistory s) (pressureField s 1))
          eta := by
    apply intervalIntegral.integral_congr
    intro r _
    simp only [pow_zero, one_mul]
    exact zDensity_eq s hbase (by decide : 0 < 1) ⟨mem_univ r, heta⟩
  rw [SlowStressSupport.stress_of_pos 1 _ hRp, he, hb]
  simp

theorem moment_axialOp2_eq_of_eqOn {S : Set ℝ} (hS : IsOpen S) {f g : SlowStressSupport.Field}
    (hf : SlowStressSupport.Smooth S f) (hg : SlowStressSupport.Smooth S g)
    (he : EqOn f g ((univ : Set ℝ) ×ˢ S))
    (h b R : ℝ) (m : ℕ) (hL : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    {eta : ℝ} (heta : eta ∈ S) :
    SlowStressSupport.moment R m (SlowStressSupport.axialOp2 h b f) eta =
      SlowStressSupport.moment R m (SlowStressSupport.axialOp2 h b g) eta := by
  apply moment_axialOp2_congr hS hf hg h b R m hL
  · intro z hz
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [he ⟨mem_univ r, hz⟩]
  · intro z hz
    filter_upwards [(isOpen_univ.prod hS).mem_nhds
      (show (R, z) ∈ (univ : Set ℝ) ×ˢ S from ⟨mem_univ R, hz⟩)] with p hp
    exact he hp
  · exact heta

/-- The first stress outside both repair regions depends only on the actual
order-zero angular and axial fields.  It is unchanged by moving the common
hierarchy cutoff or by rebuilding the positive-order repair. -/
theorem first_stresses_eq_of_leading {S : Set ℝ} {h C C' R eta : ℝ}
    (s : Scheme S h C) (t : Scheme S h C')
    (hs : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (ht : t.base.beta = betaFromU t.domain 0 t.base.axial)
    (he : EqOn (angularHistory s 0) (angularHistory t 0) ((univ : Set ℝ) ×ˢ S))
    (hu : EqOn (axialHistory s 0) (axialHistory t 0) ((univ : Set ℝ) ×ˢ S))
    (hRs : s.B ≤ R) (hRt : t.B ≤ R) (heta : eta ∈ S) :
    SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C (asSlowProfiles s) 1) (R,
      eta) =
      SlowStressSupport.stress 2 (SlowResidualMatching.thetaDensity h C' (asSlowProfiles t) 1) (R,
        eta) ∧
    SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h (asSlowProfiles s) 1) (R, eta) =
      SlowStressSupport.stress 1 (SlowResidualMatching.zDensity h (asSlowProfiles t) 1) (R, eta) :=
        by
  constructor
  · rw [first_angular_balance s hs hRs heta, first_angular_balance t ht hRt heta,
      moment_axialOp2_eq_of_eqOn s.domain.isOpen (angularHistory_smooth s 0)
        (angularHistory_smooth t 0) he h _ R 2 s.domain.denominator heta]
  · rw [first_axial_balance s hs hRs heta, first_axial_balance t ht hRt heta,
      moment_axialOp2_eq_of_eqOn s.domain.isOpen (axialHistory_smooth s 0)
        (axialHistory_smooth t 0) hu h _ R 1 s.domain.denominator heta]

section Aligned

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
  {C rho inner : ℝ} {U : Set ℂ} {base : Fin 5 → SimilarityProfile.InnerProfile}
  {s : Scheme S F.data.h C} {A : SlowRecursion.LocalHierarchy rho U F.data.h C base}
  (L : Localization s A inner) (B0 : BaseAgreement s A inner) (Z0 : ZeroOrderSolved s inner)
  (hI : Icc (-1 : ℝ) 1 ⊆ S)
  (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
  (hB : s.B ≤ nominalOuterRadius W)
  (he : EqOn (angularHistory s 0) (angularHistory (modifiedScheme W Q M) 0) ((univ : Set ℝ) ×ˢ S))
  (hu : EqOn (axialHistory s 0) (axialHistory (modifiedScheme W Q M) 0) ((univ : Set ℝ) ×ˢ S))

include M hbase hB he hu

theorem coefficients_first_pair_eq_modified {p : ℝ × ℝ}
    (hp : nominalOuterX W < p.1) (heta : |p.2| ≤ 1) :
    BaseResidual.stressPair (coefficients L B0 Z0 hI) 1 p =
      BaseResidual.stressPair (modifiedCoefficients W Q M) 1 p := by
  have hxp := (nominalOuterX_pos W).trans hp
  have hR := (outerRadius_lt_sqrt W hp).le
  have hh := first_stresses_eq_of_leading s (modifiedScheme W Q M) hbase rfl he hu
    (hB.trans hR) hR (hI (abs_le.mp heta))
  have h1 := coefficients_stress_eq L B0 Z0 hI 1 hxp.le heta
  have h2 := coefficients_stress_eq (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains 1 hxp.le heta
  exact Prod.ext (h1.1.trans (hh.1.trans h2.1.symm)) (h1.2.trans (hh.2.trans h2.2.symm))

theorem coefficients_first_edgeJets
    (hrow : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta))
    {c left : ℝ} (hc : 0 < c) (hl : left < terminalShift W + 2) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (terminalShift W + 3 - 1)) (terminalShift W + 3))
      (BaseResidual.activeZeta c left (terminalShift W + 3))
      (BaseResidual.activeDelta left (terminalShift W + 3))
      (BaseResidual.stressPair (coefficients L B0 Z0 hI) 1) := by
  have hf := coefficients_smooth L B0 Z0 hI
  apply edgeJets_of_interior_equality W ((hf.stressTheta 1).prodMk (hf.stressAxial 1)) _ hc hl
  intro p hp
  exact (coefficients_first_pair_eq_modified W Q M L B0 Z0 hI hbase hB he hu
    (terminalInner_full W hp.1).1 (abs_le.mpr ⟨hp.2.1.le, hp.2.2.le⟩)).trans
      (modified_first_pair_eq W Q M hrow hp)

end Aligned

/-- Every ambient derivative tensor of the actual pair agrees with the
terminal factor on the closed physical parameter interval. -/
theorem first_pair_jets_of_interior_equality {F : OutgoingProfile.Profile} (W :
  NominalProfile.Witness F)
    {f : (ℝ × ℝ) → ℝ × ℝ} (hf : ContDiff ℝ ∞ f)
    (he : EqOn f
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1))
    (m : ℕ) {p : ℝ × ℝ} (hp : terminalInner W < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m
      (fun q => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) q, 0)) p
        :=
  iteratedFDeriv_eq_closed_parameter (terminalInner_pos W).le (fun _ _ => hf.contDiffAt)
    (fun _ hq => ((SlowFirstOrderEdge.stressX_contDiffOn (terminalAmplitude W) F.data
      (terminalShift W)).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hq)).prodMk contDiffAt_const) he m hp
        heta

theorem first_pair_zero_right {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {f : (ℝ × ℝ) → ℝ × ℝ} (hf : ContDiff ℝ ∞ f)
    (he : EqOn f
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1))
    {p : ℝ × ℝ} (hp : Real.exp (terminalShift W + 3) ≤ p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    f p = 0 := by
  have hi : terminalInner W < p.1 :=
    (Real.exp_lt_exp.mpr (by linarith : terminalShift W + 1 < terminalShift W + 3)).trans_le hp
  have hj := first_pair_jets_of_interior_equality W hf he 0 hi heta
  have heq := congrArg (fun T => T 0) hj
  simp only [iteratedFDeriv_zero_apply] at heq
  rw [heq]
  rw [SlowFirstOrderEdge.stressX_zero_outside _ _ _ hp]
  rfl

/-- The tensor scale is the exact first slow-order scale
`q^(-A-1/2+2h)`, and the angular term is the actual physical backward
primitive of minus the second axial derivative. -/
theorem physical_first_pair {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {f : (ℝ × ℝ) → ℝ × ℝ}
    (he : EqOn f
      (fun p => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) p, 0))
      (Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1))
    {t r z : ℝ} (ht : t < 1) (hr : 0 < r)
    (hX : terminalInner W < SimilarityProfile.X F.data.h (TerminalStress.radiusPoint t r z)) :
    SimilarityProfile.q F.data.h (TerminalStress.radiusPoint t r z) ^
        (-CoordinateAlgebra.A F.data.h - 1 / 2 + 2 * F.data.h) •
        f (SimilarityProfile.inner F.data.h (TerminalStress.radiusPoint t r z)) =
      (SlowFirstOrderEdge.physicalStress (terminalAmplitude W) F.data (terminalShift W) t z r, 0)
        := by
  have heta := TerminalHistoryBridge.eta_mem_interior F.data.h_pos F.data.h_lt_half
    (p := TerminalStress.radiusPoint t r z) ht
  rw [he (show SimilarityProfile.inner F.data.h (TerminalStress.radiusPoint t r z) ∈
      Ioi (terminalInner W) ×ˢ Ioo (-1 : ℝ) 1 from ⟨hX, heta⟩)]
  rw [SlowFirstOrderEdge.physicalStress_scaled (terminalAmplitude W) F.data (terminalShift W) ht hr]
  apply Prod.ext
  · rfl
  · simp

theorem nominal_first_jets {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (m : ℕ) {p : ℝ × ℝ} (hp : terminalInner W < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    iteratedFDeriv ℝ m (BaseResidual.stressPair (nominalCoefficients W) 1) p =
      iteratedFDeriv ℝ m
        (fun q => (SlowFirstOrderEdge.stressX (terminalAmplitude W) F.data (terminalShift W) q, 0))
          p := by
  have hs := nominalCoefficients_smooth W
  exact first_pair_jets_of_interior_equality W ((hs.stressTheta 1).prodMk (hs.stressAxial 1))
    (nominal_first_pair_eq W) m hp heta

/-- The actual constructed modulation witness supplies the additional
angular anchor, using the same profile and the same finite modification. -/
theorem modulated_first_edgeJets {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)
    {c left : ℝ} (hc : 0 < c) (hl : left < terminalShift W + 2) :
    BaseResidual.PolynomialEdgeJets
      (BaseResidual.outerWindow (Real.exp (terminalShift W + 3 - 1)) (terminalShift W + 3))
      (BaseResidual.activeZeta c left (terminalShift W + 3))
      (BaseResidual.activeDelta left (terminalShift W + 3))
      (BaseResidual.stressPair (modifiedCoefficients W v.profiles v.finiteModification) 1) :=
  modified_first_edgeJets W v.profiles v.finiteModification
    (fun _ heta => v.slow_outer_angular heta) hc hl

end NavierStokes.FirstOrderBaseEdge
