/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryDynamics

@[expose] public section

/-!
# Exact dynamics of the selected signed unit

The unit is the actual normalized primary pulse in the selected copy chart.
Its scalar signed amplitude is deliberately absent here.  The time equation,
base action, and tangency germ therefore apply to either signed column before
the separate scalar multiplication and compact cutoff.
-/

noncomputable section

namespace NavierStokes.ActualSignedDynamics

open Set Function Filter HarmonicCalculus
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPrimaryDynamics
open scoped ContDiff Topology InnerProductSpace BigOperators


abbrev Native := ActualSignedGeometry.Native
abbrev Space := ProblemStatement.Space

variable {B N0 : ℕ}

/-- The actual unweighted unit, before choosing a periodic copy. -/
noncomputable def nativeUnit (j : Fin 2) (L : Label B N0) (x : Native) : Space :=
  PrimaryPulseBounds.normalizedPulse ((phases B N0 j).frame L)
    ((phases B N0 j).lam L) ((phases B N0 j).u L) ((phases B N0 j).L L)
    (pulseCoordinates L x)

/-- The selected native unit transported to the full free lift. -/
noncomputable def unitPulse (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space :=
  nativeUnit j L (copyPoint j L n k x)

noncomputable def unitMotion (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space :=
  (normalScale L n * clockScale L n) •
    (phases B N0 j).phase.velocity L (phasePoint L (copyPoint j L n k x))

noncomputable def unitAction (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : Space →L[ℝ] Space :=
  clockScale L n • PrimaryCopyBridge.baseOperator
    ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
    ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))

theorem pulseCoordinates_contDiff (L : Label B N0) :
    ContDiff ℝ ∞ (pulseCoordinates L) :=
  contDiff_fst.prodMk (contDiff_snd.snd.div_const _)

theorem nativeUnit_contDiffAt (j : Fin 2) (L : Label B N0) {x : Native}
    (hp : x.1 ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : x.2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (nativeUnit j L) x := by
  have hz : pulseCoordinates L x ∈
      (PrimaryPulseBounds.productDomain
        (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N)
        (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo)).carrier L := by
    exact ⟨hp, by simpa only [pulseCoordinates, length_sign] using ht⟩
  exact (((phases B N0 j).pulse_jets.smooth L).contDiffAt
    ((PrimaryPulseBounds.productDomain _ _ _).isOpen L |>.mem_nhds hz)).comp x
      (pulseCoordinates_contDiff L).contDiffAt

theorem unitPulse_contDiffAt (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hp : (copyPoint j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : (copyPoint j L n k x).2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (unitPulse j L n k) x :=
  (nativeUnit_contDiffAt j L hp ht).comp x (copyPoint_smooth j L n k).contDiffAt

/-- Unnormalizing the slot time gives the actual homogeneous projected ODE. -/
theorem nativeUnit_hasDerivAt (j : Fin 2) (L : Label B N0) {x : Native}
    (hp : x.1 ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : x.2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => nativeUnit j L (x.1, (x.2.1,t)))
      (TangentProjection.projectedRhs
        ((phases B N0 j).phase.normal L (phasePoint L x))
        ((phases B N0 j).phase.velocity L (phasePoint L x))
        (nativeUnit j L x)
        (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L x.1)
          ((phases B N0 j).phase.shear L (phasePoint L x)) (nativeUnit j L x))
        0 (((phases B N0 j).frame L).viscosity (phasePoint L x))) x.2.2 := by
  let P := phases B N0 j
  let ell := P.L L
  have hL : 0 < ell := P.L_pos L
  have hθ : x.2.2 / ell ∈ Ioo (0 : ℝ) 1 := ht
  have hd := PrimaryPulseBounds.normalizedPulse_hasDerivAt (P.frame L) (P.lam L) (P.u L) hL
    ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    ((sourcePair L x.1 hp).coefficient_continuous j) hp ((sourcePair L x.1 hp).kinematics j) hθ
  have hv : ell * (x.2.2 / ell) = x.2.2 := mul_div_cancel₀ _ hL.ne'
  have htime : x.2.2 ∈ Icc (0 : ℝ) ell := by
    have hz := mul_nonneg hL.le hθ.1.le
    rw [hv] at hz
    exact ⟨hz, (div_le_one hL).mp hθ.2.le⟩
  have hz : phasePoint L x ∈
      ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).slot P.V P.openV).carrier
        L :=
    ⟨hp, P.interval L htime⟩
  have hd' := hd.scomp x.2.2 ((hasDerivAt_id x.2.2).div_const ell)
  simp only [hv, one_div, smul_smul, inv_mul_cancel₀ hL.ne', one_smul] at hd'
  have he (t : ℝ) : nativeUnit j L (x.1,(x.2.1,t)) =
      PrimaryPulseBounds.normalizedPulse (P.frame L) (P.lam L) (P.u L) ell (x.1,t/ell) := by
    simp only [nativeUnit, pulseCoordinates, ell, P, length_sign]
  simp only [he]
  convert! hd' using 1
  rw [show (P.frame L).normal (x.1,x.2.2) = P.phase.normal L (phasePoint L x) from
    frame_normal P L hz,
    show (P.frame L).normalMotion (x.1,x.2.2) = P.phase.velocity L (phasePoint L x) from
    frame_motion P L hz]
  rfl

/-- The copied unit satisfies the exact equation used by the signed principal. -/
theorem unitPulse_ode (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hp : (copyPoint j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : (copyPoint j L n k x).2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    along ((PrimaryResidualClass.directions (commonContext B)).fastField n)
      (unitPulse j L n k) x =
      TangentProjection.projectedRhs
        ((chartCoefficients j L).normal
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
          (PrimaryResidualClass.directions (commonContext B)) n x)
        (unitMotion j L n k x) (unitPulse j L n k x)
        (unitAction j L n k x (unitPulse j L n k x)) 0
        (ChartScales.epsilon h n * (ChartScales.carrier h n : ℝ)^2 *
          ‖(chartCoefficients j L).normal
            (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
            (PrimaryResidualClass.directions (commonContext B)) n x‖^2) := by
  have hd := nativeUnit_hasDerivAt j L hp ht
  have ha := along_copy j L n k (nativeUnit j L) hd
    ((unitPulse_contDiffAt j L n k hp ht).differentiableAt (by simp))
  change along _ (unitPulse j L n k) x = _ at ha
  rw [ha, normal_eq_copy j L n U k hR hT hc, damping_scale, frame_viscosity]
  have hs := NormalScaling.projectedRhs_rescale
    ((phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k x)))
    ((phases B N0 j).phase.velocity L (phasePoint L (copyPoint j L n k x)))
    (nativeUnit j L (copyPoint j L n k x))
    (PrimaryCopyBridge.baseOperator ((phases B N0 j).phase.F L (copyPoint j L n k x).1)
      ((phases B N0 j).phase.shear L (phasePoint L (copyPoint j L n k x)))
      (nativeUnit j L (copyPoint j L n k x)))
    (0 : Space) (clockScale L n) 1
    (ChartScales.epsilon h (BaseChartJets.cellBand L) *
      (ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ)^2 *
      ‖(phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k x))‖^2)
    (normalScale_pos L n).ne'
  simpa only [unitMotion, unitPulse, unitAction, _root_.smul_apply,
    mul_one, one_smul, smul_zero] using hs.symm

/-- The action in the unit ODE is exactly the chart's real base shear. -/
theorem unitPulse_action (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1) :
    CurlClassBounds.complexify (unitAction j L n k x (unitPulse j L n k x)) =
      LinearWaveResidual.shear ((chartCoefficients j L).radius n)
        ((chartCoefficients j L).frequencyBase n) ((chartCoefficients j L).axialBase n)
        ((PrimaryResidualClass.directions (commonContext B)).radialField n)
        (fun y => CurlClassBounds.complexify (unitPulse j L n k y)) x := by
  have hh := copy_shear_function j L n k (nativeUnit j L) hR hT
  rw [SignedWaveUpdate.shear_smul] at hh
  apply (smul_right_injective _ (velocityScale_pos L n).ne')
  simpa only [unitAction, unitPulse, _root_.smul_apply,
    map_smul, smul_smul, mul_comm] using hh.symm

/-- The native unit is tangent even at the endpoints of its closed time interval. -/
theorem nativeUnit_tangent (j : Fin 2) (L : Label B N0) {x : Native}
    (hp : x.1 ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : x.2.2 / (phases B N0 j).L L ∈ Icc (0 : ℝ) 1) :
    ⟪(phases B N0 j).phase.normal L (phasePoint L x), nativeUnit j L x⟫_ℝ = 0 := by
  let P := phases B N0 j
  let ell := P.L L
  have hL : 0 < ell := P.L_pos L
  have hθ : x.2.2 / ell ∈ Icc (0 : ℝ) 1 := ht
  have hv : ell * (x.2.2 / ell) = x.2.2 := mul_div_cancel₀ _ hL.ne'
  have htime : x.2.2 ∈ Icc (0 : ℝ) ell := by
    have hz := mul_nonneg hL.le hθ.1
    rw [hv] at hz
    exact ⟨hz, (div_le_one hL).mp hθ.2⟩
  have hz : phasePoint L x ∈
      ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).slot P.V P.openV).carrier
        L :=
    ⟨hp, P.interval L htime⟩
  change ⟪P.phase.normal L (phasePoint L x),
    PrimaryPulseBounds.normalizedPulse (P.frame L) (P.lam L) (P.u L) ell
      (x.1, x.2.2 / ell)⟫_ℝ = 0
  rw [← frame_normal P L hz]
  unfold PrimaryPulseBounds.normalizedPulse
  simp only [hv]
  exact (P.frame L).ambient_tangent _ _

/-- The actual chart normal agrees with its copied native expression on a
neighborhood of every point in the closed clock core.  The proof differentiates
the padded plateau's phase germ, so the core itself need not be open. -/
theorem normal_eq_copy_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (chartCoefficients j L).normal
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n =ᶠ[𝓝 x]
      fun y => normalScale L n •
        (phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k y)) := by
  filter_upwards [(phase_germ j L n k hc).eventuallyEq_nhds,
    (isOpen_lt continuous_const continuous_fst.fst).mem_nhds hR,
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT] with y hy hyR hyT
  obtain ⟨hF,hG⟩ := native_base_differentiable j L n k hyR hyT
  have hp := PrimaryMaterialDefect.differentiableAt_phase
    ((phases B N0 j).phase.epsilon L) ((phases B N0 j).phase.p L)
    ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) (slotPoint j L n k y) hF hG
  have hd := (((hp.hasFDerivAt.comp y (slotPoint_hasFDerivAt j L n k y)).const_mul
    ((ChartScales.carrier h (BaseChartJets.cellBand L) : ℝ) / (ChartScales.carrier h n :
      ℝ)))).congr_of_eventuallyEq hy
  have htheta : PhaseCalculus.phaseNormal ((phases B N0 j).phase.epsilon L)
      ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
      ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) (slotPoint j L n k y) =
        (phases B N0 j).phase.normal L (phasePoint L (copyPoint j L n k y)) := by
    rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _ (slotPoint j L n k y)
      ((phases B N0 j).epsilon_ne L) hF hG]
    unfold PhaseJetBounds.PhaseFamily.normal
    simp only [phasePoint]
    rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _
      ((copyPoint j L n k y).1, ((phases B N0 j).phase.theta L, (copyPoint j L n k y).2.2))
      ((phases B N0 j).epsilon_ne L) hF hG]
    rfl
  rw [← htheta]
  have hrad : (chartCoefficients j L).radius n y = y.1.1 := rfl
  have heps : (phases B N0 j).phase.epsilon L = ChartScales.epsilon h (BaseChartJets.cellBand L) :=
    rfl
  ext i
  fin_cases i <;>
    simp [LinearWaveBounds.WaveCoefficients.normal, HarmonicCalculus.phaseNormal,
      HarmonicCalculus.along, hd.fderiv,
      ContinuousLinearMap.comp_apply, slotLinear_radial, slotLinear_angular j L n y,
      slotLinear_axial, map_smul, smul_eq_mul, PiLp.smul_apply,
      PhaseCalculus.phaseNormal, normalScale, hrad, heps]
  · ring
  · rw [slotPoint_radius]
    field_simp [(radialScale_pos L n).ne', hyR.ne']
  · ring

/-- True ambient tangency near every admissible closed-core point. -/
theorem unitPulse_tangent_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hp : (copyPoint j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : (copyPoint j L n k x).2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    (fun y => ⟪(chartCoefficients j L).normal
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n y, unitPulse j L n k y⟫_ℝ)
      =ᶠ[𝓝 x] fun _ => 0 := by
  have hp' := (copyPoint_smooth j L n k).continuous.fst.continuousAt.eventually
    ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L |>.mem_nhds hp)
  have ht' := ((copyPoint_smooth j L n k).continuous.snd.snd.div_const
    ((phases B N0 j).L L)).continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [normal_eq_copy_germ j L n U k hR hT hc, hp', ht'] with y hy hyp hyt
  rw [hy, inner_smul_left, unitPulse, nativeUnit_tangent j L hyp ⟨hyt.1.le, hyt.2.le⟩, mul_zero]

theorem unitPulse_tangent (j : Fin 2) (L : Label B N0) (n : ℕ)
    (U : LocalSignedRequest.SlowRegion (2*h)) (k : TorusInverse.Frequency) {x : FullPoint}
    (hR : 0 < x.1.1) (hT : 0 < x.1.2.1.1)
    (hp : (copyPoint j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (ht : (copyPoint j L n k x).2.2 / (phases B N0 j).L L ∈ Ioo (0 : ℝ) 1)
    (hc : (copyPoint j L n k x).2 ∈ (clockWindow L).core) :
    ⟪(chartCoefficients j L).normal
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal U))
      (PrimaryResidualClass.directions (commonContext B)) n x, unitPulse j L n k x⟫_ℝ = 0 :=
  (unitPulse_tangent_germ j L n U k hR hT hp ht hc).eq_of_nhds

end NavierStokes.ActualSignedDynamics
