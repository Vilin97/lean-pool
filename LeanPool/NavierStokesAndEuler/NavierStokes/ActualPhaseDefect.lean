/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization

@[expose] public section

/-!
# The material defect of the actual primary chart phase

The same selected phase is pulled through the actual physical band change.
The base coefficients are identified through their common physical field
before the native material cancellation is used.
-/

noncomputable section

namespace NavierStokes.ActualPhaseDefect

open Set Function Filter HarmonicCalculus
open scoped ContDiff Topology BigOperators

abbrev Slow := PhaseCalculus.Slow
abbrev Plane := TorusInverse.Plane
abbrev Cylinder := PhysicalResidualBridge.Cylinder


theorem ratioPower_mul_power {Q Qr : ℝ} (_hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    PhysicalParticularWave.ratioPower Q Qr a * Qr^a = Q^a := by
  unfold PhysicalParticularWave.ratioPower
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hQr a).ne']

theorem bandPoint_change {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) (p : Slow) :
    BaseChartJets.bandPoint h Qr (ActualSignedGeometry.slowChange h Q Qr p) =
      BaseChartJets.bandPoint h Q p := by
  have hscale (a x : ℝ) : Qr^a*(PhysicalParticularWave.ratioPower Q Qr a*x) = Q^a*x := by
    rw [← mul_assoc, mul_comm (Qr^a), ratioPower_mul_power hQ hQr]
  apply Prod.ext
  · change 1-Qr*(PhysicalParticularWave.ratioPower Q Qr 1*p.2.2) = 1-Q*p.2.2
    simpa only [Real.rpow_one] using congrArg (fun z => 1-z) (hscale 1 p.2.2)
  · ext i
    fin_cases i
    · change Real.sqrt Qr*(PhysicalParticularWave.ratioPower Q Qr (1/2)*p.1) = Real.sqrt Q*p.1
      simpa only [Real.sqrt_eq_rpow] using hscale (1/2) p.1
    · rfl
    · exact hscale (CoordinateAlgebra.D h) p.2.1

theorem clock_eq_velocity_radial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    PhysicalParticularWave.clockWeight h Q Qr = PhysicalParticularWave.velocityWeight h Q Qr *
      PhysicalParticularWave.ratioPower Q Qr (1/2) := by
  exact (PhysicalParticularWave.ratioPower_mul hQ hQr (CoordinateAlgebra.A h) (1/2)).symm

/-- Only primitive base values and the actual chart differential enter this
identity.  It does not assume a phase-defect identity. -/
theorem material_chartChange {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (scale : ℝ)
    (b F G br Fr Gr : Cylinder → ℝ) (Phi : Cylinder → ℝ) {x : Cylinder}
    (hx : 0 < x.1.1)
    (hPhi : DifferentiableAt ℝ Phi (PhysicalParticularWave.cylinderChange h Q Qr gap x))
    (hb : b x = PhysicalParticularWave.velocityWeight h Q Qr *
      br (PhysicalParticularWave.cylinderChange h Q Qr gap x))
    (hF : F x = PhysicalParticularWave.clockWeight h Q Qr *
      Fr (PhysicalParticularWave.cylinderChange h Q Qr gap x))
    (hG : G x = PhysicalParticularWave.velocityWeight h Q Qr *
      Gr (PhysicalParticularWave.cylinderChange h Q Qr gap x)) :
    LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius b F G
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial (PhysicalResidualBridge.commonGraph Q h
        i).temporal
      (fun y => scale*Phi (PhysicalParticularWave.cylinderChange h Q Qr gap y)) x =
    scale*PhysicalParticularWave.clockWeight h Q Qr *
      LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius br Fr Gr
        (PhysicalResidualBridge.commonGraph Qr h (i+gap)).radial
          PhysicalResidualBridge.ScaledGraph.angular
        (PhysicalResidualBridge.commonGraph Qr h (i+gap)).axial
        (PhysicalResidualBridge.commonGraph Qr h (i+gap)).temporal Phi
        (PhysicalParticularWave.cylinderChange h Q Qr gap x) := by
  have hd := ((hPhi.hasFDerivAt.comp x
    (PhysicalParticularWave.cylinderChange h Q Qr gap).hasFDerivAt).const_mul scale).fderiv
  simp only [Function.comp_def] at hd
  unfold LinearWaveResidual.materialPhaseDefect along
  rw [hd]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    PhysicalParticularWave.cylinderChange_radial hQ hQr h i gap hx,
    PhysicalParticularWave.cylinderChange_angular,
    PhysicalParticularWave.cylinderChange_axial hQ hQr h i gap,
    PhysicalParticularWave.cylinderChange_temporal hQ hQr h i gap,
    map_smul, smul_eq_mul, hb, hF, hG, clock_eq_velocity_radial hQ hQr h]
  ring

section Slot

variable {dimension h : ℝ}
  (sys : PartitionedCovariance.SlotSystem dimension h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)

theorem slot_coordinate_temporal (l : SlotColoring.Label) :
    (ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0).coordinateLinear
      ActualSignedGeometry.temporalVector = (0,(ChartScales.timeCoefficient h l.1)⁻¹) := by
  let g := ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0
  have hb : g.basis (0,(ChartScales.timeCoefficient h l.1)⁻¹) = ActualSignedGeometry.temporalVector
    := by
    rw [ActualSignedGeometry.slotGeometry_basis]
    simp [ (ChartScales.timeCoefficient_pos h l.1).ne']
  have he := (g.basis.symm_apply_eq).mpr hb.symm
  change g.basis.symm (CommonCoverSolve.coverPower 0 ActualSignedGeometry.temporalVector) = _
  simp only [CommonCoverSolve.coverPower_apply, pow_zero]
  exact he

theorem slot_coordinates_temporal (l : SlotColoring.Label) (x : Cylinder) :
    ActualSignedGeometry.slotLinear
      (ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0)
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).temporal x) =
      PhaseCalculus.eV-ChartScales.epsilon h l.1 • PhaseCalculus.eT := by
  change ((0,(0,-ChartScales.epsilon h l.1)),(0,
    ((ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0).coordinateLinear
      (ChartScales.timeCoefficient h l.1 • ActualSignedGeometry.temporalVector)).2)) = _
  rw [map_smul, slot_coordinate_temporal]
  simp [PhaseCalculus.eV, PhaseCalculus.eT, (ChartScales.timeCoefficient_pos h l.1).ne']

theorem slot_material (l : SlotColoring.Label) (p pz x0 : ℝ) (b F G : Slow → ℝ)
    (k : TorusInverse.Frequency) {x : Cylinder} (hx : 0 < x.1.1)
    (hF : DifferentiableAt ℝ F (x.1.1,x.1.2.1))
    (hG : DifferentiableAt ℝ G (x.1.1,x.1.2.1)) :
    LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius
      (fun y => b (y.1.1,y.1.2.1)) (fun y => F (y.1.1,y.1.2.1)) (fun y => G (y.1.1,y.1.2.1))
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).axial
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).temporal
      (PhaseCalculus.phase (ChartScales.epsilon h l.1) p pz x0 F G ∘
        ActualSignedGeometry.slotCoordinates
          (ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0) k) x =
    PrimaryMaterialDefect.expression (ChartScales.epsilon h l.1) p pz x0
      (((ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0).coordinates k
        x.1.2.2).2)
      (b (x.1.1,x.1.2.1)) (G (x.1.1,x.1.2.1))
      (PhaseCalculus.slowR F (x.1.1,x.1.2.1)) (PhaseCalculus.slowR G (x.1.1,x.1.2.1))
      (PhaseCalculus.slowT F (x.1.1,x.1.2.1)) (PhaseCalculus.slowT G (x.1.1,x.1.2.1))
      (PhaseCalculus.slowZ F (x.1.1,x.1.2.1)) (PhaseCalculus.slowZ G (x.1.1,x.1.2.1)) := by
  let g := ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0
  let chi := ActualSignedGeometry.slotCoordinates g k
  have hchi := ActualSignedGeometry.slotCoordinates_hasFDerivAt g k x
  have hPhi := PrimaryMaterialDefect.differentiableAt_phase (ChartScales.epsilon h l.1)
    p pz x0 F G (chi x) hF hG
  have hd := fderiv_comp x hPhi hchi.differentiableAt
  rw [hchi.fderiv] at hd
  have he : LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius
      (fun y => b (y.1.1,y.1.2.1)) (fun y => F (y.1.1,y.1.2.1)) (fun y => G (y.1.1,y.1.2.1))
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).axial
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).temporal
      (PhaseCalculus.phase (ChartScales.epsilon h l.1) p pz x0 F G ∘ chi) x =
      LinearWaveResidual.materialPhaseDefect (fun y : PhaseCalculus.Slot => y.1.1)
        (fun y => b y.1) (fun y => F y.1) (fun y => G y.1)
        (fun _ => PhaseCalculus.eR) (fun _ => PhaseCalculus.eTheta)
        (fun _ => ChartScales.epsilon h l.1 • PhaseCalculus.eZ)
        (LinearWaveResidual.timeDirection (ChartScales.epsilon h l.1)
          (fun _ => PhaseCalculus.eV) (fun _ => PhaseCalculus.eT))
        (PhaseCalculus.phase (ChartScales.epsilon h l.1) p pz x0 F G) (chi x) := by
    simp only [LinearWaveResidual.materialPhaseDefect, along, hd, ContinuousLinearMap.comp_apply]
    rw [ActualSignedGeometry.slot_coordinates_radial, ActualSignedGeometry.slot_coordinates_angular,
      ActualSignedGeometry.slot_coordinates_axial, slot_coordinates_temporal]
    rfl
  rw [he, LinearWaveResidual.materialPhaseDefect_slot_formula _ _ _ _ _ _ _ _
    (ChartScales.epsilon_pos h l.1).ne' hx hF hG]
  rfl

end Slot

section Base

variable {out : OutgoingProfile.Profile} {W : NominalProfile.Witness out}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

theorem radialSlow_change (n m : ℕ) (p : Slow) :
    BaseContextAssembly.radialSlow H v upper B n p =
      PhysicalParticularWave.velocityWeight out.data.h (ChartScales.Q n) (ChartScales.Q m) *
        BaseContextAssembly.radialSlow H v upper B m
          (ActualSignedGeometry.slowChange out.data.h (ChartScales.Q n) (ChartScales.Q m) p) := by
  change ChartScales.Q n ^ CoordinateAlgebra.A out.data.h *
      SlowBorelBase.baseVelocity _ _ _ _ (BaseChartJets.bandPoint _ _ _) 0 =
    PhysicalParticularWave.velocityWeight _ _ _ * (ChartScales.Q m ^ CoordinateAlgebra.A out.data.h
      *
      SlowBorelBase.baseVelocity _ _ _ _ (BaseChartJets.bandPoint _ _ _) 0)
  rw [bandPoint_change (ChartScales.Q_pos n) (ChartScales.Q_pos m),
    PhysicalParticularWave.velocityWeight, ← mul_assoc,
    ratioPower_mul_power (ChartScales.Q_pos n) (ChartScales.Q_pos m)]

theorem axialSlow_change (n m : ℕ) {p : Slow} (hT : 0 < p.2.2) :
    BaseContextAssembly.axialSlow H v upper B n p =
      PhysicalParticularWave.velocityWeight out.data.h (ChartScales.Q n) (ChartScales.Q m) *
        BaseContextAssembly.axialSlow H v upper B m
          (ActualSignedGeometry.slowChange out.data.h (ChartScales.Q n) (ChartScales.Q m) p) := by
  have hTr := ActualSignedGeometry.slowChange_time (h := out.data.h)
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) hT
  unfold BaseContextAssembly.axialSlow
  rw [BaseChartJets.axial_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
      out.data.h_pos out.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H
        v) hT
      (C := W.axis.normalization),
    BaseChartJets.axial_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
      out.data.h_pos out.data.h_lt_half (ChartScales.Q_pos m) (FinalSlowBase.coefficients_smooth H
        v) hTr
      (C := W.axis.normalization),
    bandPoint_change (ChartScales.Q_pos n) (ChartScales.Q_pos m),
    PhysicalParticularWave.velocityWeight, ← mul_assoc,
    ratioPower_mul_power (ChartScales.Q_pos n) (ChartScales.Q_pos m)]

theorem frequencySlow_change (n m : ℕ) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseContextAssembly.frequencySlow H v upper B n p =
      PhysicalParticularWave.clockWeight out.data.h (ChartScales.Q n) (ChartScales.Q m) *
        BaseContextAssembly.frequencySlow H v upper B m
          (ActualSignedGeometry.slowChange out.data.h (ChartScales.Q n) (ChartScales.Q m) p) := by
  have hTr := ActualSignedGeometry.slowChange_time (h := out.data.h)
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) hT
  have hRr := ActualSignedGeometry.slowChange_radius (h := out.data.h)
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) hR
  unfold BaseContextAssembly.frequencySlow
  rw [BaseChartJets.frequency_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
      out.data.h_pos out.data.h_lt_half (ChartScales.Q_pos n) (FinalSlowBase.coefficients_smooth H
        v) hT hR,
    BaseChartJets.frequency_eq_normalized_velocity (FinalSlowBase.scales_strictMono H v upper B)
      out.data.h_pos out.data.h_lt_half (ChartScales.Q_pos m) (FinalSlowBase.coefficients_smooth H
        v) hTr hRr,
    bandPoint_change (ChartScales.Q_pos n) (ChartScales.Q_pos m),
    ActualSignedGeometry.slowChange_apply,
    clock_eq_velocity_radial (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  symm
  calc
    _ = (PhysicalParticularWave.velocityWeight out.data.h (ChartScales.Q n) (ChartScales.Q m) *
        ChartScales.Q m ^ CoordinateAlgebra.A out.data.h) *
        (SlowBorelBase.baseVelocity (FinalSlowBase.scales H v upper B) out.data.h
          W.axis.normalization
          (FinalSlowBase.coefficients H v) (BaseChartJets.bandPoint out.data.h (ChartScales.Q n) p)
            1 / p.1) := by
      have hs := (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)
        (1/2)).ne'
      field_simp [hs, hR.ne']
    _ = _ := by
      rw [PhysicalParticularWave.velocityWeight,
        ratioPower_mul_power (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
      ring

end Base

theorem material_congr_germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R b F G : E → ℝ) (Vr Vtheta Vz Vt : E → E) {Phi Psi : E → ℝ} {x : E}
    (he : Phi =ᶠ[𝓝 x] Psi) :
    LinearWaveResidual.materialPhaseDefect R b F G Vr Vtheta Vz Vt Phi =ᶠ[𝓝 x]
      LinearWaveResidual.materialPhaseDefect R b F G Vr Vtheta Vz Vt Psi := by
  filter_upwards [ParticularWaveAssembly.along_germ he Vr, ParticularWaveAssembly.along_germ he
    Vtheta,
    ParticularWaveAssembly.along_germ he Vz, ParticularWaveAssembly.along_germ he Vt] with y hr
      htheta hz ht
  simp only [LinearWaveResidual.materialPhaseDefect, hr, htheta, hz, ht]

theorem periodic_material_germ {dimension h : ℝ}
    (sys : PartitionedCovariance.SlotSystem dimension h
      ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector)
    (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    (p pz x0 : ℝ) (b F G : Slow → ℝ)
    {S : Set Slow} (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S)
    (k : TorusInverse.Frequency) {x : Cylinder} (hR : 0 < x.1.1)
    (hx : (x.1.1,x.1.2.1) ∈ S)
    (hc : (ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0).coordinates
      k x.1.2.2 ∈
      (ActualSignedGeometry.clockWindow sys l.1).core) :
    (fun y => LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius
      (fun z => b (z.1.1,z.1.2.1)) (fun z => F (z.1.1,z.1.2.1)) (fun z => G (z.1.1,z.1.2.1))
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).axial
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
        l.1)).temporal
      (ActualSignedGeometry.periodicPhase sys l 0 (ChartScales.epsilon h l.1) p pz x0 F G) y) =ᶠ[𝓝
        x]
    fun y => PrimaryMaterialDefect.expression (ChartScales.epsilon h l.1) p pz x0
      ((ActualSignedGeometry.slotGeometry sys ActualSignedGeometry.vectors_det l 0).coordinates k
        y.1.2.2).2
      (b (y.1.1,y.1.2.1)) (G (y.1.1,y.1.2.1))
      (PhaseCalculus.slowR F (y.1.1,y.1.2.1)) (PhaseCalculus.slowR G (y.1.1,y.1.2.1))
      (PhaseCalculus.slowT F (y.1.1,y.1.2.1)) (PhaseCalculus.slowT G (y.1.1,y.1.2.1))
      (PhaseCalculus.slowZ F (y.1.1,y.1.2.1)) (PhaseCalculus.slowZ G (y.1.1,y.1.2.1)) := by
  have hp := ActualSignedGeometry.periodicPhase_germ sys hh hl 0 (ChartScales.epsilon h l.1)
    p pz x0 F G k hc
  have he := material_congr_germ PhysicalResidualBridge.ScaledGraph.radius
    (fun z => b (z.1.1,z.1.2.1)) (fun z => F (z.1.1,z.1.2.1)) (fun z => G (z.1.1,z.1.2.1))
    (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
      l.1)).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h l.1)).axial
    (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
      l.1)).temporal hp
  have hmem : ∀ᶠ y : Cylinder in 𝓝 x, (y.1.1,y.1.2.1) ∈ S :=
    (hS.preimage (continuous_fst.fst.prodMk continuous_fst.snd.fst)).mem_nhds hx
  have hpos : ∀ᶠ y : Cylinder in 𝓝 x, 0 < y.1.1 :=
    (isOpen_lt continuous_const continuous_fst.fst).mem_nhds hR
  filter_upwards [he,hmem,hpos] with y hy hys hyr
  exact hy.trans (slot_material sys l p pz x0 b F G k hyr
    ((hF.contDiffAt (hS.mem_nhds hys)).differentiableAt (by simp))
    ((hG.contDiffAt (hS.mem_nhds hys)).differentiableAt (by simp)))

theorem context_material_swap
    (c : CorrectionState.Context LocalSignedRequest.Point)
    (s : WeightedClasses.StripData LocalSignedRequest.Point)
    (a : LinearWaveBounds.WaveCoefficients (LocalSignedRequest.Point × ℝ))
    (n : ℕ) (G : PhysicalResidualBridge.ScaledGraph)
    (hG : PhysicalResidualTZ.MatchesAtTZ c.operators G n)
    (hepsilon : s.epsilon n = c.operators.epsilon n)
    (Phi : Cylinder → ℝ) (hphase : a.phase n = fun y => Phi (PhysicalResidualTZ.swapCylinder y))
    (x : LocalSignedRequest.Point × ℝ) :
    a.defect (HarmonicWaveInteraction.productStrip s) (PrimaryResidualClass.directions c) n x =
      LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius
        (fun y => a.radialBase n (PhysicalResidualTZ.swapCylinder y))
        (fun y => a.frequencyBase n (PhysicalResidualTZ.swapCylinder y))
        (fun y => a.axialBase n (PhysicalResidualTZ.swapCylinder y))
        G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial G.temporal Phi
        (PhysicalResidualTZ.swapCylinder x) := by
  have hr : PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions c).radialField n x) =
      G.radial (PhysicalResidualTZ.swapCylinder x) := by
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.radialField,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
      hG.eR, hG.vR, hG.frequency, hG.profile, PhysicalResidualBridge.ScaledGraph.radial, smul_smul]
  have hz : PhysicalResidualTZ.swapCylinder ((PrimaryResidualClass.directions c).axialField
      (HarmonicWaveInteraction.productStrip s) n x) = G.axial (PhysicalResidualTZ.swapCylinder x)
        := by
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.axialField,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
      hG.eZ, hepsilon, hG.epsilon, PhysicalResidualBridge.ScaledGraph.axial,
      HarmonicWaveInteraction.productStrip, HarmonicWaveInteraction.pullbackStrip]
  have ht : PhysicalResidualTZ.swapCylinder (LinearWaveResidual.timeDirection
      ((HarmonicWaveInteraction.productStrip s).epsilon n)
      ((PrimaryResidualClass.directions c).fastField n)
      (fun _ => (PrimaryResidualClass.directions c).slow) x) =
      G.temporal (PhysicalResidualTZ.swapCylinder x) := by
    simp [PrimaryResidualClass.directions, LinearWaveBounds.GraphDirections.fastField,
      LinearWaveResidual.timeDirection, PhysicalResidualTZ.swapCylinder_apply,
      PhysicalResidualTZ.swapSlow_apply, hG.eT, hG.vT, hG.fast, hepsilon, hG.epsilon,
      PhysicalResidualBridge.ScaledGraph.temporal, HarmonicWaveInteraction.productStrip,
      HarmonicWaveInteraction.pullbackStrip]
  have ha : PhysicalResidualTZ.swapCylinder (PrimaryResidualClass.directions c).angular =
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualTZ.swapCylinder x) := rfl
  have hd (z : LocalSignedRequest.Point × ℝ) :
      fderiv ℝ (fun y => Phi (PhysicalResidualTZ.swapCylinder y)) x z =
        fderiv ℝ Phi (PhysicalResidualTZ.swapCylinder x) (PhysicalResidualTZ.swapCylinder z) :=
    PhysicalResidualTZ.fderiv_reindex PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv Phi x
      z
  unfold LinearWaveBounds.WaveCoefficients.defect LinearWaveResidual.materialPhaseDefect along
  rw [hphase]
  simp only [hd, hr, hz, ht, ha, PhysicalResidualTZ.swapCylinder_swapCylinder]

section Actual

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

noncomputable def nativeCopy (j : Fin 2) (L : Label B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : FullPoint) : Slow × Plane :=
  ActualSignedGeometry.copyPoint slots vectors_det
    (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j)
    n (CommonWindow.index h n) k (ActualSignedGeometry.meanEquiv.symm x.1)

noncomputable def viewMap (L : Label B N0) (n : ℕ) : FullPoint →L[ℝ] Cylinder :=
  (PhysicalParticularWave.cylinderChange h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
    L))
    (ChartScales.nativeIndex h (BaseChartJets.cellBand L)-CommonWindow.index h n)).comp
      PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv.toContinuousLinearMap

theorem nativeCopy_view (j : Fin 2) (L : Label B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : FullPoint) :
    nativeCopy j L n k x = ParticularWaveBounds.nativePoint
      (ActualSignedGeometry.slotGeometry slots vectors_det
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0) k
      (ActualSignedGeometry.cylinderNative (viewMap L n x)) :=
  ActualSignedGeometry.copyPoint_eq_reference_view slots vectors_det _ n (CommonWindow.index h n) k
    (PhysicalResidualTZ.swapCylinder x)

theorem view_slot (j : Fin 2) (L : Label B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : FullPoint) :
    ActualSignedGeometry.slotCoordinates
      (ActualSignedGeometry.slotGeometry slots vectors_det
        (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0) k
      (viewMap L n x) = ((nativeCopy j L n k x).1,(x.2,(nativeCopy j L n k x).2.2)) := by
  exact (congrArg (fun z : Slow × Plane => (z.1,(x.2,z.2.2))) (nativeCopy_view j L n k x)).symm

/-- The phase germ itself is valid on the closed native core, with the
angle and both fast coordinates free.  No open-q restriction is needed. -/
theorem chart_phase_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hc : (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots
      (BaseChartJets.cellBand L)).core) :
    (chartCoefficients j L).phase n =ᶠ[𝓝 x]
    fun y => ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
      PhaseCalculus.phase (ChartScales.epsilon h (BaseChartJets.cellBand L))
        ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
        ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L)
        ((nativeCopy j L n k y).1,(y.2,(nativeCopy j L n k y).2.2)) := by
  let l := PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j
  have hl : 4 ≤ l.1 := ((choice B N0).prepared.large _ L.property).four_le
  have hcore : (ActualSignedGeometry.slotGeometry slots vectors_det l 0).coordinates k
      (viewMap L n x).1.2.2 ∈ (ActualSignedGeometry.clockWindow slots l.1).core := by
    rw [nativeCopy_view j L n k x] at hc
    exact hc
  have hp := ActualSignedGeometry.periodicPhase_germ slots outgoing.data.h_pos.le hl 0
    (ChartScales.epsilon h (BaseChartJets.cellBand L))
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) k hcore
  have hm : Tendsto (viewMap L n) (𝓝 x) (𝓝 (viewMap L n x)) := (viewMap L n).continuous.continuousAt
  filter_upwards [hm.eventually hp] with y hy
  rw [chartCoefficients_phase_view j L n hi y]
  change ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
    ActualSignedGeometry.periodicPhase slots l 0 (ChartScales.epsilon h (BaseChartJets.cellBand L))
      ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
      ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L) (viewMap L n y) = _
  rw [hy]
  change _ * PhaseCalculus.phase _ _ _ _ _ _
    (ActualSignedGeometry.slotCoordinates (ActualSignedGeometry.slotGeometry slots vectors_det l 0)
      k
      (viewMap L n y)) = _
  rw [view_slot]

noncomputable def defect (j : Fin 2) (L : Label B N0) (n : ℕ) : FullPoint → ℝ :=
  (chartCoefficients j L).defect
    (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal standardRegion))
    (PrimaryResidualClass.directions (commonContext B)) n

noncomputable def referenceMaterial (j : Fin 2) (L : Label B N0) : Cylinder → ℝ :=
  LinearWaveResidual.materialPhaseDefect PhysicalResidualBridge.ScaledGraph.radius
    (fun y => BaseContextAssembly.radialSlow certificate modulation upper B (BaseChartJets.cellBand
      L)
      (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.F L (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.G L (y.1.1,y.1.2.1))
    (PhysicalResidualBridge.commonGraph (ChartScales.Q (BaseChartJets.cellBand L)) h
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L))).radial
    PhysicalResidualBridge.ScaledGraph.angular
    (PhysicalResidualBridge.commonGraph (ChartScales.Q (BaseChartJets.cellBand L)) h
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L))).axial
    (PhysicalResidualBridge.commonGraph (ChartScales.Q (BaseChartJets.cellBand L)) h
      (ChartScales.nativeIndex h (BaseChartJets.cellBand L))).temporal
    (ActualSignedGeometry.periodicPhase slots
      (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0
      (ChartScales.epsilon h (BaseChartJets.cellBand L))
      ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
      ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L))

noncomputable def nativeExpression (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : ℝ :=
  let z := nativeCopy j L n k x
  PrimaryMaterialDefect.expression (ChartScales.epsilon h (BaseChartJets.cellBand L))
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L) z.2.2
    (BaseContextAssembly.radialSlow certificate modulation upper B (BaseChartJets.cellBand L) z.1)
    ((phases B N0 j).phase.G L z.1)
    (PhaseCalculus.slowR ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowR ((phases B N0 j).phase.G L) z.1)
    (PhaseCalculus.slowT ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowT ((phases B N0 j).phase.G L) z.1)
    (PhaseCalculus.slowZ ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowZ ((phases B N0 j).phase.G L) z.1)

theorem chart_material_view (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    {x : FullPoint} (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1)
    (hp : ((viewMap L n x).1.1,(viewMap L n x).1.2.1) ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L) :
    defect j L n x =
      (((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
        PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
          (BaseChartJets.cellBand L))) *
      referenceMaterial j L (viewMap L n x) := by
  have hphys := CommonBaseContext.context_matches_physical certificate modulation upper B
    (CommonWindow.index h) n
  have hswap := context_material_swap (commonContext B)
    (BaseContextAssembly.nativeStrip nominal standardRegion) (chartCoefficients j L) n
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n))
    hphys rfl
    (ActualSignedGeometry.preparedViewPhase certificate modulation slots (choice B N0).prepared
      j L n (CommonWindow.index h n))
    (funext (chartCoefficients_phase_view j L n hi)) x
  apply hswap.trans
  have hF := ((phases B N0 j).baseF.smooth L).contDiffAt
    (((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L).mem_nhds hp)
  have hG := ((phases B N0 j).baseG.smooth L).contDiffAt
    (((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L).mem_nhds hp)
  have hPhi := ActualSignedGeometry.periodicPhase_differentiableAt slots
    (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j) 0
    (ChartScales.epsilon h (BaseChartJets.cellBand L))
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L)
    (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))
  have he := material_chartChange (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand
    L))
    h (CommonWindow.index h n) (ChartScales.nativeIndex h (BaseChartJets.cellBand
      L)-CommonWindow.index h n)
    ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ))
    (fun y => (chartCoefficients j L).radialBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => (chartCoefficients j L).frequencyBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => (chartCoefficients j L).axialBase n (PhysicalResidualTZ.swapCylinder y))
    (fun y => BaseContextAssembly.radialSlow certificate modulation upper B (BaseChartJets.cellBand
      L)
      (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.F L (y.1.1,y.1.2.1))
    (fun y => (phases B N0 j).phase.G L (y.1.1,y.1.2.1)) _
    (x := PhysicalResidualTZ.swapCylinder x) hR hPhi
    (radialSlow_change certificate modulation upper B n (BaseChartJets.cellBand L)
      (BaseContextAssembly.slowCoordinates x.1))
    (frequencySlow_change certificate modulation upper B n (BaseChartJets.cellBand L) hT hR)
    (axialSlow_change certificate modulation upper B n (BaseChartJets.cellBand L) hT)
  simp only [Nat.add_sub_of_le hi] at he
  exact he

/-- The literal initializer defect agrees as an ambient germ with the
native material expression.  The closed core condition includes both
endpoints of the native slow partition and leaves all fast variables free. -/
theorem chart_defect_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1)
    (hp : (nativeCopy j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hc : (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots
      (BaseChartJets.cellBand L)).core) :
    defect j L n =ᶠ[𝓝 x] fun y =>
      (((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
        PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
          (BaseChartJets.cellBand L))) *
      nativeExpression j L n k y := by
  let S := (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L
  let l := PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j
  have hS : IsOpen S := (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen L
  have hpv : ((viewMap L n x).1.1,(viewMap L n x).1.2.1) ∈ S := by
    rw [nativeCopy_view] at hp
    exact hp
  have hcv : (ActualSignedGeometry.slotGeometry slots vectors_det l 0).coordinates k
      (viewMap L n x).1.2.2 ∈ (ActualSignedGeometry.clockWindow slots l.1).core := by
    rw [nativeCopy_view] at hc
    exact hc
  have hRv : 0 < (viewMap L n x).1.1 :=
    ActualSignedGeometry.slowChange_radius (h := h) (ChartScales.Q_pos n)
      (ChartScales.Q_pos (BaseChartJets.cellBand L)) (p := BaseContextAssembly.slowCoordinates x.1)
        hR
  have href := periodic_material_germ slots outgoing.data.h_pos.le
    ((choice B N0).prepared.large _ L.property).four_le
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L)
    (BaseContextAssembly.radialSlow certificate modulation upper B (BaseChartJets.cellBand L))
    ((phases B N0 j).phase.F L) ((phases B N0 j).phase.G L)
    hS ((phases B N0 j).baseF.smooth L) ((phases B N0 j).baseG.smooth L) k hRv hpv hcv
  have hpull := (viewMap L n).continuous.continuousAt.eventually href
  have hnear : ∀ᶠ y : FullPoint in 𝓝 x,
      ((viewMap L n y).1.1,(viewMap L n y).1.2.1) ∈ S :=
    (hS.preimage (((viewMap L n).continuous.fst.fst).prodMk
      (viewMap L n).continuous.fst.snd.fst)).mem_nhds hpv
  have hTnear : ∀ᶠ y : FullPoint in 𝓝 x, 0 < y.1.2.1.1 :=
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT
  have hRnear : ∀ᶠ y : FullPoint in 𝓝 x, 0 < y.1.1 :=
    (isOpen_lt continuous_const continuous_fst.fst).mem_nhds hR
  filter_upwards [hpull,hnear,hTnear,hRnear] with y hy hpy hTy hRy
  rw [chart_material_view j L n hi hTy hRy hpy]
  unfold nativeExpression
  rw [nativeCopy_view]
  exact congrArg (fun z : ℝ => _ * z) hy

noncomputable def reducedExpression (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) : ℝ :=
  let z := nativeCopy j L n k x
  PrimaryMaterialDefect.expression 1
    ((phases B N0 j).phase.p L) ((phases B N0 j).phase.pz L) ((phases B N0 j).phase.x0 L) z.2.2
    (BaseRadialJets.reducedRadial (FinalSlowBase.scales certificate modulation upper B) h
      (FinalSlowBase.coefficients certificate modulation) (ChartScales.Q (BaseChartJets.cellBand
        L)) z.1)
    ((phases B N0 j).phase.G L z.1)
    (PhaseCalculus.slowR ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowR ((phases B N0 j).phase.G L) z.1)
    (PhaseCalculus.slowT ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowT ((phases B N0 j).phase.G L) z.1)
    (PhaseCalculus.slowZ ((phases B N0 j).phase.F L) z.1)
    (PhaseCalculus.slowZ ((phases B N0 j).phase.G L) z.1)

theorem nativeExpression_reduced (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) :
    nativeExpression j L n k x = ChartScales.epsilon h (BaseChartJets.cellBand L) *
      reducedExpression j L n k x := by
  have hTr : 0 < (nativeCopy j L n k x).1.2.2 :=
    ActualSignedGeometry.slowChange_time (h := h) (ChartScales.Q_pos n)
      (ChartScales.Q_pos (BaseChartJets.cellBand L)) (p := BaseContextAssembly.slowCoordinates x.1)
        hT
  have hb := BaseRadialJets.radial_eq (FinalSlowBase.scales_strictMono certificate modulation upper
    B)
    outgoing.data.h_pos outgoing.data.h_lt_half (ChartScales.Q_pos (BaseChartJets.cellBand L))
    (FinalSlowBase.coefficients_smooth certificate modulation) (C := nominal.axis.normalization) hTr
  dsimp only [nativeExpression, reducedExpression, BaseContextAssembly.radialSlow]
  rw [hb]
  unfold PrimaryMaterialDefect.expression
  dsimp only [ChartScales.epsilon, h]
  ring

noncomputable def materialWeight (L : Label B N0) (n : ℕ) : ℝ :=
  ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
      L)) *
    (ChartScales.epsilon h (BaseChartJets.cellBand L)/ChartScales.epsilon h n)

/-- The exact small factor is the target-band viscosity. -/
theorem chart_defect_reduced_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hi : CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand L))
    (k : TorusInverse.Frequency) {x : FullPoint} (hT : 0 < x.1.2.1.1) (hR : 0 < x.1.1)
    (hp : (nativeCopy j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hc : (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots
      (BaseChartJets.cellBand L)).core) :
    defect j L n =ᶠ[𝓝 x]
      fun y => ChartScales.epsilon h n * materialWeight L n * reducedExpression j L n k y := by
  have he := chart_defect_germ j L n hi k hT hR hp hc
  have hTnear : ∀ᶠ y : FullPoint in 𝓝 x, 0 < y.1.2.1.1 :=
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst).mem_nhds hT
  filter_upwards [he,hTnear] with y hy hTy
  rw [hy, nativeExpression_reduced j L n k hTy]
  unfold materialWeight
  let a := ((ChartScales.carrier h (BaseChartJets.cellBand L):ℝ)/(ChartScales.carrier h n:ℝ)) *
    PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
      L))
  let e := ChartScales.epsilon h n
  let er := ChartScales.epsilon h (BaseChartJets.cellBand L)
  let r := reducedExpression j L n k y
  change a*(er*r) = e*(a*(er/e))*r
  have hc : e*(er/e) = er := mul_div_cancel₀ er (ChartScales.epsilon_pos h n).ne'
  calc
    a*(er*r) = a*((e*(er/e))*r) := by rw [hc]
    _ = e*(a*(er/e))*r := by ring

theorem materialWeight_normal (L : Label B N0) (n : ℕ) :
    materialWeight L n =
      PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
        L))
        (ChartScales.carrier h n) (ChartScales.carrier h (BaseChartJets.cellBand L)) *
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand L))
        (CoordinateAlgebra.A h-h) := by
  have he : ChartScales.epsilon h (BaseChartJets.cellBand L)/ChartScales.epsilon h n =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
        L)) (-h) := by
    simpa only [neg_neg, ChartScales.epsilon] using PhysicalParticularWave.ratioPower_neg_div
      (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand L)) (-h)
  unfold materialWeight PhysicalParticularWave.normalWeight PhysicalParticularWave.clockWeight
  rw [he]
  simp only [mul_assoc, PhysicalParticularWave.ratioPower_mul
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand L))]
  congr 2
  ring

noncomputable def materialWeightBound : ℝ :=
  2*ActualSignedGeometry.powerBound (h/2+1/2) *
    ActualSignedGeometry.powerBound (CoordinateAlgebra.A h-h)

theorem materialWeight_pos (L : Label B N0) (n : ℕ) : 0 < materialWeight L n := by
  unfold materialWeight
  exact mul_pos
    (mul_pos (div_pos (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _))
      (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)))
      (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _))
    (div_pos (ChartScales.epsilon_pos h _) (ChartScales.epsilon_pos h _))

theorem materialWeight_bound (L : Label B N0) (n : ℕ)
    (hnm : n ≤ BaseChartJets.cellBand L+4) (hmn : BaseChartJets.cellBand L ≤ n+4) :
    materialWeight L n ≤ materialWeightBound := by
  let near : ∀ (_ : Unit) (_ : ℕ), n ≤ BaseChartJets.cellBand L+4 ∧
      BaseChartJets.cellBand L ≤ n+4 := fun _ _ => ⟨hnm,hmn⟩
  have hnormal : PhysicalParticularWave.normalWeight (ChartScales.Q n) (ChartScales.Q
    (BaseChartJets.cellBand L))
      (ChartScales.carrier h n) (ChartScales.carrier h (BaseChartJets.cellBand L)) ≤
      2*ActualSignedGeometry.powerBound (h/2+1/2) := by
    rw [← ActualSignedGeometry.normalScale_value (fun _ => n) (fun (_ : Unit) _ =>
      BaseChartJets.cellBand L)
      near outgoing.data.h_pos.le () 0]
    exact ((ActualSignedGeometry.normalScale (fun _ => n) (fun (_ : Unit) _ =>
      BaseChartJets.cellBand L)
      near outgoing.data.h_pos.le).bounds () 0).2
  rw [materialWeight_normal]
  exact mul_le_mul hnormal (ActualSignedGeometry.dyadic_ratioPower_le hnm hmn _)
    (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _).le
    (by have := ActualSignedGeometry.powerBound_one (h/2+1/2); linarith)

theorem native_core_of_interval (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hu : |(nativeCopy j L n k x).2.1| ≤ slots.radius)
    (hv : (nativeCopy j L n k x).2.2 ∈ Ioo 0 ((phases B N0 j).L L)) :
    (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots (BaseChartJets.cellBand
      L)).core :=
  ⟨abs_le.mp hu, hv.1.le, hv.2.le⟩

theorem active_copy_defect_germ (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hactive : BaseChartJets.cellBand L ∈ CommonWindow.levels n)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hx : x ∈ (HarmonicWaveInteraction.productStrip
      (BaseContextAssembly.nativeStrip nominal standardRegion)).domain)
    (hp : (nativeCopy j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hc : (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots
      (BaseChartJets.cellBand L)).core) :
    defect j L n =ᶠ[𝓝 x]
      fun y => ChartScales.epsilon h n * materialWeight L n * reducedExpression j L n k y :=
  chart_defect_reduced_germ j L n (CommonWindow.index_le hactive) k
    (BaseContextAssembly.nativeStrip_time nominal standardRegion hx)
    (BaseContextAssembly.nativeStrip_radius nominal standardRegion hx) hp hc

theorem active_copy_defect_jets (j : Fin 2) (L : Label B N0) (n : ℕ)
    (hactive : BaseChartJets.cellBand L ∈ CommonWindow.levels n)
    (k : TorusInverse.Frequency) {x : FullPoint}
    (hx : x ∈ (HarmonicWaveInteraction.productStrip
      (BaseContextAssembly.nativeStrip nominal standardRegion)).domain)
    (hp : (nativeCopy j L n k x).1 ∈
      (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hc : (nativeCopy j L n k x).2 ∈ (ActualSignedGeometry.clockWindow slots
      (BaseChartJets.cellBand L)).core)
    (m : ℕ) :
    iteratedFDeriv ℝ m (defect j L n) x = iteratedFDeriv ℝ m
      (fun y => ChartScales.epsilon h n * materialWeight L n * reducedExpression j L n k y) x :=
  PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (active_copy_defect_germ j L n hactive k hx hp
    hc) m

theorem active_materialWeight_bound (L : Label B N0) (n : ℕ)
    (hactive : BaseChartJets.cellBand L ∈ CommonWindow.levels n) :
    0 < materialWeight L n ∧ materialWeight L n ≤ materialWeightBound :=
  ⟨materialWeight_pos L n, materialWeight_bound L n
    (CommonWindow.distance hactive).1 (CommonWindow.distance hactive).2⟩

/-! ## Actual native jets before the copy-coordinate pullback -/

noncomputable def paddedRegion : LocalSignedRequest.SlowRegion (2*h) where
  carrier := {z | 0 < z.1 ∧ SimilarityCoordinates.coordinateQ (2*h) z ∈ Ioo (1/4 : ℝ) 4}
  isOpen := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hq := (SimilarityCoordinates.coordinateQ_smooth
      (by linarith [outgoing.data.h_pos] : 0 < 2*h)
      (by linarith [outgoing.data.h_lt_half] : 2*h < 1) hz.1).continuousAt
    exact inter_mem (isOpen_lt continuous_const continuous_fst |>.mem_nhds hz.1)
      (hq.preimage_mem_nhds (isOpen_Ioo.mem_nhds hz.2))
  coord_pos := by linarith [outgoing.data.h_pos]
  coord_lt_one := by linarith [outgoing.data.h_lt_half]
  qlo := 1/4
  qhi := 4
  qlo_pos := by norm_num
  time_pos := fun _ hz => hz.1
  q_mem := fun _ hz => ⟨hz.2.1.le,hz.2.2.le⟩

theorem padded_slow_mem {p : Slow} (hT : 0 < p.2.2)
    (hq : SimilarityHomogeneity.chartQ h p ∈ Icc (1/2 : ℝ) 2)
    (hr : PrimaryTargetBounds.profileRadius h p ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)) :
    p ∈ BaseContextAssembly.slowCarrier nominal paddedRegion := by
  apply (BaseContextAssembly.nativeStrip_mem nominal paddedRegion (BaseContextAssembly.insertSlow
    p)).mpr
  refine ⟨⟨hT,?_,?_⟩,hr⟩
  · exact (by norm_num : (1/4 : ℝ) < 1/2).trans_le hq.1
  · exact hq.2.trans_lt (by norm_num)

noncomputable def reducedSlowDomain (U : LocalSignedRequest.SlowRegion (2*h)) :
    PhaseJetBounds.Domain (Fin 2 × Label B N0) Slow where
  scale i := ChartScales.S (BaseChartJets.cellBand i.2)
  carrier i := (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier i.2 ∩
    BaseContextAssembly.slowCarrier nominal U
  isOpen i := ((PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).isOpen i.2).inter
    (BaseContextAssembly.slowCarrier_open nominal U)
  one_le_scale i := (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).one_le_scale
    i.2

noncomputable def reducedJetDomain (U : LocalSignedRequest.SlowRegion (2*h)) :
    PhaseJetBounds.Domain (Fin 2 × Label B N0) (Slow × ℝ) :=
  (reducedSlowDomain U).slot (fun i => (phases B N0 i.1).V i.2)
    (fun i => (phases B N0 i.1).openV i.2)

noncomputable def nativeReduced (i : Fin 2 × Label B N0) (z : Slow × ℝ) : ℝ :=
  PrimaryMaterialDefect.expression 1
    ((phases B N0 i.1).phase.p i.2) ((phases B N0 i.1).phase.pz i.2)
    ((phases B N0 i.1).phase.x0 i.2) z.2
    (BaseRadialJets.reducedRadial (FinalSlowBase.scales certificate modulation upper B) h
      (FinalSlowBase.coefficients certificate modulation) (ChartScales.Q (BaseChartJets.cellBand
        i.2)) z.1)
    ((phases B N0 i.1).phase.G i.2 z.1)
    (PhaseCalculus.slowR ((phases B N0 i.1).phase.F i.2) z.1)
    (PhaseCalculus.slowR ((phases B N0 i.1).phase.G i.2) z.1)
    (PhaseCalculus.slowT ((phases B N0 i.1).phase.F i.2) z.1)
    (PhaseCalculus.slowT ((phases B N0 i.1).phase.G i.2) z.1)
    (PhaseCalculus.slowZ ((phases B N0 i.1).phase.F i.2) z.1)
    (PhaseCalculus.slowZ ((phases B N0 i.1).phase.G i.2) z.1)

theorem reducedExpression_eq_native (j : Fin 2) (L : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) (x : FullPoint) :
    reducedExpression j L n k x =
      nativeReduced (j,L) ((nativeCopy j L n k x).1,(nativeCopy j L n k x).2.2) := rfl

theorem native_reduced_polynomial (U : LocalSignedRequest.SlowRegion (2*h)) :
    PhaseJetBounds.PolynomialJets (reducedJetDomain (B := B) (N0 := N0) U) nativeReduced := by
  let D := reducedSlowDomain (B := B) (N0 := N0) U
  let V : (Fin 2 × Label B N0) → Set ℝ := fun i => (phases B N0 i.1).V i.2
  have hV : ∀ i, IsOpen (V i) := fun i => (phases B N0 i.1).openV i.2
  have hF : PhaseJetBounds.PolynomialJets D (fun i => (phases B N0 i.1).phase.F i.2) := by
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (phases B N0 0).baseF Prod.snd
      (fun _ => rfl) (fun _ _ hp => hp.1)
  have hG : PhaseJetBounds.PolynomialJets D (fun i => (phases B N0 i.1).phase.G i.2) := by
    exact PrimaryGeometryAssembly.polynomial_restrict_reindex (phases B N0 0).baseG Prod.snd
      (fun _ => rfl) (fun _ _ hp => hp.1)
  have hgeom0 := BaseContextAssembly.native_geometry nominal U (Fin 2 × Label B N0)
  have hgeom : BaseChartJets.GeometryBounds D h
      (BaseContextAssembly.geometryRadius nominal U) (BaseContextAssembly.geometryBound nominal U)
      (U.qlo/2) (BaseContextAssembly.geometryUpper U)
      (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal) :=
    ⟨fun i p hp => hgeom0.time i p hp.2,
     fun i p hp => hgeom0.radius i p hp.2,
     fun i p hp => hgeom0.bounded i p hp.2,
     fun i p hp => hgeom0.q_range i p hp.2,
     fun i p hp => hgeom0.x_range i p hp.2⟩
  have hb : PhaseJetBounds.PolynomialJets D (fun i =>
      BaseRadialJets.reducedRadial (FinalSlowBase.scales certificate modulation upper B) h
        (FinalSlowBase.coefficients certificate modulation) (ChartScales.Q (BaseChartJets.cellBand
          i.2))) :=
    BaseChartJets.polynomial_of_unit (AllBandBaseJets.reducedRadial_polynomial
      outgoing.data.h_pos outgoing.data.h_lt_half (BaseContextAssembly.geometryRadius_pos nominal U)
      (BaseContextAssembly.one_le_geometryBound nominal U) (div_pos U.qlo_pos (by norm_num))
      (BaseContextAssembly.geometryUpper_pos U) (NominalConeAssembly.activeLeft_pos nominal) hgeom
      (FinalSlowBase.coefficients_smooth certificate modulation)
      (FinalSlowBase.scales_admissible_on certificate modulation upper B
        (NominalConeAssembly.activeLeft_pos nominal).le (le_max_right _ _))
      (fun i => ChartScales.Q (BaseChartJets.cellBand i.2))
      (fun _ => ChartScales.Q_pos _) (fun _ => ChartScales.Q_le_one _))
  let M := (phases B N0 0).M+(phases B N0 1).M
  have hM0 := (phases B N0 0).one_le_M
  have hM1 := (phases B N0 1).one_le_M
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMj (j : Fin 2) : (phases B N0 j).M ≤ M := by
    fin_cases j <;> dsimp [M] <;> linarith
  have hp : PhaseJetBounds.PolynomialJets (D.slot V hV) (fun i _ => (phases B N0 i.1).phase.p i.2)
    :=
    PhaseJetBounds.PolynomialJets.const_uniform _ hM (fun i => by
      rw [Real.norm_eq_abs]
      exact ((phases B N0 i.1).constants i.2).2.1.trans (hMj i.1))
  have hpz : PhaseJetBounds.PolynomialJets (D.slot V hV) (fun i _ => (phases B N0 i.1).phase.pz
    i.2) :=
    PhaseJetBounds.PolynomialJets.const_uniform _ hM (fun i => by
      rw [Real.norm_eq_abs]
      exact ((phases B N0 i.1).constants i.2).2.2.1.trans (hMj i.1))
  have hx0 : PhaseJetBounds.PolynomialJets (D.slot V hV) (fun i _ => (phases B N0 i.1).phase.x0
    i.2) :=
    PhaseJetBounds.PolynomialJets.const_uniform _ hM (fun i => by
      rw [Real.norm_eq_abs]
      exact ((phases B N0 i.1).constants i.2).2.2.2.trans (hMj i.1))
  have ht : PhaseJetBounds.PolynomialJets (D.slot V hV) (fun _ (z : Slow × ℝ) => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PhaseJetBounds.PolynomialJets.affine (D := D.slot V hV)
        (ContinuousLinearMap.snd ℝ Slow ℝ) (fun _ => 0) (m := 1) hM (fun i z hz => by
          simp only [ContinuousLinearMap.coe_snd', add_zero, Real.norm_eq_abs, pow_one]
          exact ((phases B N0 i.1).slot i.2 z.2 hz.2).trans
            (mul_le_mul_of_nonneg_right (hMj i.1) (zero_le_one.trans (D.one_le_scale i)))))
  have hFR := (hF.directional (1,(0,0))).lift_slot V hV
  have hGR := (hG.directional (1,(0,0))).lift_slot V hV
  have hFT := (hF.directional (0,(0,1))).lift_slot V hV
  have hGT := (hG.directional (0,(0,1))).lift_slot V hV
  have hFZ := (hF.directional (0,(1,0))).lift_slot V hV
  have hGZ := (hG.directional (0,(1,0))).lift_slot V hV
  have hbb := hb.lift_slot V hV
  have hGG := hG.lift_slot V hV
  change PhaseJetBounds.PolynomialJets (D.slot V hV) (fun i z => nativeReduced i z)
  simpa only [nativeReduced, PrimaryMaterialDefect.expression, one_mul,
    PhaseCalculus.slowR, PhaseCalculus.slowT, PhaseCalculus.slowZ] using
    (hbb.mul hx0).sub (ht.mul (((hbb.mul ((hp.mul hFR).add (hpz.mul hGR))).sub
      ((hp.mul hFT).add (hpz.mul hGT))).add (hGG.mul ((hp.mul hFZ).add (hpz.mul hGZ)))))

theorem native_reduced_finite_jets (U : LocalSignedRequest.SlowRegion (2*h)) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ (j : Fin 2) (L : Label B N0),
      JetBounds.FiniteJetBound N (nativeReduced (j,L))
        ((reducedJetDomain U).carrier (j,L)) (C*ChartScales.S (BaseChartJets.cellBand L)^m) := by
  obtain ⟨C,hC,m,hm⟩ := (native_reduced_polynomial (B := B) (N0 := N0) U).bound N
  exact ⟨C,hC,m,fun j L => hm (j,L)⟩

theorem native_reduced_domain_mem (U : LocalSignedRequest.SlowRegion (2*h))
    (j : Fin 2) (L : Label B N0) {p : Slow} {t : ℝ}
    (hp : p ∈ (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N).carrier L)
    (hs : p ∈ BaseContextAssembly.slowCarrier nominal U)
    (ht : t ∈ Icc 0 ((phases B N0 j).L L)) :
    (p,t) ∈ (reducedJetDomain U).carrier (j,L) :=
  ⟨⟨hp,hs⟩,(phases B N0 j).interval L ht⟩

end Actual

end NavierStokes.ActualPhaseDefect
