/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalSignedWave
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity

@[expose] public section

/-!
# A common-torus signed request with native wave geometry

The torus-averaged signed request is independent of the free fast coordinate
and angle at which it is evaluated. The common state can therefore be kept on
its original torus while the primary wave uses native fast coordinates.
Freezing the band index preserves every actual derivative and average.
-/

noncomputable section

namespace NavierStokes.TorusMeanRequestRebase

open Set Function WeightedClasses CorrectionState
open scoped Topology ContDiff


abbrev Point := LocalSignedRequest.Point
abbrev Cylinder := PhysicalSignedWave.Cylinder
abbrev Plane := TorusInverse.Plane

section Freeze

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable def freezeStrip (s : StripData D) (m : ℕ) : StripData D :=
  { s with
    epsilon := fun _ => s.epsilon m
    epsilon_pos := fun _ => s.epsilon_pos m
    epsilon_le_one := fun _ => s.epsilon_le_one m
    slow := fun _ => s.slow m
    one_le_slow := fun _ => s.one_le_slow m }

noncomputable def freezeTriple (v : MeanIncrementBounds.Triple D) (m : ℕ) :
    MeanIncrementBounds.Triple D :=
  ⟨fun _ => v.radial m, fun _ => v.angular m, fun _ => v.axial m⟩

noncomputable def freezeContext (c : Context D) (m : ℕ) : Context D where
  operators := { c.operators with
    epsilon := fun _ => c.operators.epsilon m
    radialFrequency := fun _ => c.operators.radialFrequency m
    fastCoefficient := fun _ => c.operators.fastCoefficient m }
  base := freezeTriple c.base m
  virtualTheta := fun _ => c.virtualTheta m
  virtualAxial := fun _ => c.virtualAxial m

noncomputable def freezeState (u : State D) (m : ℕ) : State D where
  mean := freezeTriple u.mean m
  pressure := fun _ => u.pressure m
  oscillation := fun _ => u.oscillation m
  oscillatoryPressure := fun _ => u.oscillatoryPressure m
  errors := ⟨fun _ => u.errors.base m, fun _ => u.errors.gaussian m,
    fun _ => u.errors.aliasError m⟩

noncomputable def freezeWave (a : LinearWaveBounds.WaveCoefficients D) (m : ℕ) :
    LinearWaveBounds.WaveCoefficients D where
  radius := fun _ => a.radius m
  radialBase := fun _ => a.radialBase m
  frequencyBase := fun _ => a.frequencyBase m
  axialBase := fun _ => a.axialBase m
  phase := fun _ => a.phase m
  amplitude := fun _ => a.amplitude m
  pressure := fun _ => a.pressure m
  frequency := fun _ => a.frequency m

noncomputable def freezeDirections (d : LinearWaveBounds.GraphDirections D) (m : ℕ) :
    LinearWaveBounds.GraphDirections D :=
  { d with radialScale := fun _ => d.radialScale m, fastScale := fun _ => d.fastScale m }

@[simp] theorem freezeStrip_domain (s : StripData D) (m : ℕ) :
    (freezeStrip s m).domain = s.domain := rfl

@[simp] theorem freezeStrip_epsilon (s : StripData D) (m n : ℕ) :
    (freezeStrip s m).epsilon n = s.epsilon m := rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem freezeState_covariance (u : State D) (m n : ℕ) (i j : Fin 3) :
    (freezeState u m).covariance i j n = u.covariance i j m := rfl

@[simp] theorem freezeState_theta (c : Context D) (u : State D) (m n : ℕ) :
    (freezeState u m).thetaResidual (freezeContext c m) n = u.thetaResidual c m := rfl

@[simp] theorem freezeState_axial (c : Context D) (u : State D) (m n : ℕ) :
    (freezeState u m).axialResidual (freezeContext c m) n = u.axialResidual c m := rfl

@[simp] theorem freezeContext_frame (c : Context D) (m n : ℕ) :
    HarmonicResidual.contextFrame (freezeContext c m) n = HarmonicResidual.contextFrame c m := rfl

theorem freezeState_coherent (u : State D) (m n nr : ℕ) (U : Set D) :
    PhysicalResidualNaturality.StateOn U (ContinuousLinearEquiv.refl ℝ D) 1 1
      (freezeState u m) (freezeState u m) n nr := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PhysicalResidualNaturality.ScalarOn, freezeState, freezeTriple]

theorem freezeContext_coherent (c : Context D) (m n nr : ℕ) (U : Set D) :
    PhysicalResidualNaturality.ContextOn U (ContinuousLinearEquiv.refl ℝ D) 1 1
      (freezeContext c m) (freezeContext c m) n nr := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [freezeContext_frame]
  all_goals simp [PhysicalResidualNaturality.ScalarOn, freezeContext, freezeTriple]

end Freeze

/-! ## The evaluation point carries no torus or angle dependence -/

theorem fullRequest_free_variables (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (r : ℝ) (z Y Y' : Plane) (theta theta' : ℝ) :
    LocalSignedRequest.fullRequest s P coord c u n ((r, (z, Y)), theta) =
      LocalSignedRequest.fullRequest s P coord c u n ((r, (z, Y')), theta') := rfl

theorem stateRequest_free_variables (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (r : ℝ) (z Y Y' : Plane) (theta theta' : ℝ) :
    PhysicalSignedWave.stateRequest s P h c u n ((r, (z, Y)), theta) =
      PhysicalSignedWave.stateRequest s P h c u n ((r, (z, Y')), theta') := rfl

/-- This changes only the evaluation point, not the state or the measure
used for its torus average. The fast-coordinate map can be arbitrary. -/
theorem stateRequest_fast_map (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (mapFast : Plane → Plane) (x : Cylinder) :
    PhysicalSignedWave.stateRequest s P h c u n
      ((x.1.1, (x.1.2.1, mapFast x.1.2.2)), x.2) =
      PhysicalSignedWave.stateRequest s P h c u n x := rfl

theorem stateRequest_inverseCover (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n gap : ℕ) (x : Cylinder) :
    PhysicalSignedWave.stateRequest s P h c u n
      ((x.1.1, (x.1.2.1, (CommonCoverSolve.coverPower gap).symm x.1.2.2)), x.2) =
      PhysicalSignedWave.stateRequest s P h c u n x := rfl

/-- Equality uses exactly the source and target epsilons. No equality of
their unrelated domains, phase frames, or native backgrounds is needed. -/
theorem stateRequest_freeze (s sr : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ)
    (hepsilon : sr.epsilon n = s.epsilon m) (x : Cylinder) :
    PhysicalSignedWave.stateRequest sr P h (freezeContext c m) (freezeState u m) n x =
      PhysicalSignedWave.stateRequest s P h c u m x := by
  change (sr.epsilon n)⁻¹ • _ = (s.epsilon m)⁻¹ • _
  rw [hepsilon]
  rfl

theorem stateRequest_freeze_full (s : StripData Point) (sr : StripData Cylinder)
    (P : SignedStressPrimitive.Patch) (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ)
    (hepsilon : sr.epsilon n = s.epsilon m) (x : Cylinder) :
    PhysicalSignedWave.stateRequest sr P h (freezeContext c m) (freezeState u m) n x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m (PhysicalResidualTZ.swapCylinder x) := by
  change (sr.epsilon n)⁻¹ • _ = (s.epsilon m)⁻¹ • _
  rw [hepsilon]
  rfl

@[simp] theorem stateRequest_freezeStrip (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ) (x : Cylinder) :
    PhysicalSignedWave.stateRequest (freezeStrip s m) P h (freezeContext c m) (freezeState u m) n x
      =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s (freezeStrip s m) P h c u m n rfl x

/-! ## Identity band views of the native primary -/

theorem ratioPower_self {Q : ℝ} (hQ : 0 < Q) (a : ℝ) :
    PhysicalParticularWave.ratioPower Q Q a = 1 :=
  div_self (Real.rpow_pos_of_pos hQ a).ne'

theorem slowChange_self (h : ℝ) {Q : ℝ} (hQ : 0 < Q) (z : Plane) :
    PhysicalSignedWave.slowChange h Q Q z = z := by
  simp [PhysicalSignedWave.slowChange, ratioPower_self hQ]

theorem requestChart_self (h : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    PhysicalSignedWave.requestChart h hQ hQ 0 = ContinuousLinearEquiv.refl ℝ Point := by
  ext x <;>
  simp [PhysicalSignedWave.requestChart_apply, ratioPower_self hQ, slowChange_self h hQ,
    TemporalMeanUpdate.coverMap]

variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}

/-- The dummy band index repeats one physical scale and one native cover.
Every coordinate change is the identity; the supplied primary is retained. -/
noncomputable def identityViews (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0) : B.Views m where
  exponent := h
  referenceScale := Q
  referenceScale_pos := hQ
  referenceCover := cover
  scale _ := Q
  scale_pos _ := hQ
  cover _ := cover
  cover_le _ := le_rfl
  frequency _ := B.base.frequency m
  frequency_ne _ := hfrequency
  strip := B.strip
  directions := B.directions
  background := B.base

@[simp] theorem identityViews_map (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0)
    (n : ℕ) (x : Cylinder) :
    (identityViews B m h Q cover hQ hfrequency).map n x = x := by
  simp [PhysicalSignedWave.PrimaryData.Views.map, identityViews,
    PhysicalParticularWave.cylinderChange, ratioPower_self hQ, CommonCoverSolve.coverPower]

@[simp] theorem identityViews_velocity (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0) (n : ℕ) :
    (identityViews B m h Q cover hQ hfrequency).velocity n = 1 :=
  ratioPower_self hQ _

/-! ## The actual common state supplies the request of these native views -/

section IdentityStateData

variable (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
  (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0)
  (hh : 0 < h) (hh1 : h < 1 / 2)
  (R : LocalSignedRequest.SlowRegion (2 * h)) (P : SignedStressPrimitive.Patch)
  (c : Context Point) (u : State Point)
  (H : MeanStateRegularity.PrimitiveData R P.a P.b c u)
  (hp : GaugeMomentBalances.MovingField R P.a P.b u.pressure)
  (hslow : ∀ x ∈ B.strip.domain, (x.1.2.1.2, x.1.2.1.1) ∈ R.carrier)

/-- Both stored states and both contexts are the same frozen common objects.
Only their dummy band index is changed. The native primary is left intact.
Residual regularity and periodicity are derived from the primitive data. -/
noncomputable def stateData : (identityViews B m h Q cover hQ hfrequency).StateData where
  patch := P
  context := freezeContext c m
  referenceContext := freezeContext c m
  current := freezeState u m
  referenceState := freezeState u m
  exponent_pos := hh
  exponent_lt_half := hh1
  domain _ := PhysicalMeanDomain.slowDomain R.carrier
  domain_open _ := PhysicalMeanDomain.slowDomain_open R.isOpen
  state_coherent n := by
    change PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain R.carrier)
      (PhysicalSignedWave.requestChart h hQ hQ (cover - cover))
      (PhysicalParticularWave.velocityWeight h Q Q) (PhysicalParticularWave.ratioPower Q Q (1 / 2))
      (freezeState u m) (freezeState u m) n m
    simp only [Nat.sub_self, requestChart_self, PhysicalParticularWave.velocityWeight,
      ratioPower_self hQ]
    exact freezeState_coherent u m n m _
  context_coherent n := by
    change PhysicalResidualNaturality.ContextOn (PhysicalMeanDomain.slowDomain R.carrier)
      (PhysicalSignedWave.requestChart h hQ hQ (cover - cover))
      (PhysicalParticularWave.velocityWeight h Q Q) (PhysicalParticularWave.ratioPower Q Q (1 / 2))
      (freezeContext c m) (freezeContext c m) n m
    simp only [Nat.sub_self, requestChart_self, PhysicalParticularWave.velocityWeight,
      ratioPower_self hQ]
    exact freezeContext_coherent c m n m _
  time_pos x hx := R.time_pos _ (hslow x hx)
  fibers _ x hx _ _ := hslow x hx
  referenceSlow _ := R.carrier
  referenceSlow_open _ := R.isOpen
  referenceSlow_mem _ x hx := by
    change PhysicalSignedWave.slowChange h Q Q (x.1.2.1.2, x.1.2.1.1) ∈ R.carrier
    rw [slowChange_self h hQ]
    exact hslow x hx
  reference_theta_smooth _ := by
    simpa only [freezeState_theta] using (H.theta P.a_pos P.a_lt_b).smooth m
  reference_axial_smooth _ := by
    simpa only [freezeState_axial] using (H.axial P.a_pos P.a_lt_b hp).smooth m
  reference_theta_periodic _ := by
    simpa only [freezeState_theta] using (H.theta P.a_pos P.a_lt_b).periodic m
  reference_axial_periodic _ := by
    simpa only [freezeState_axial] using (H.axial P.a_pos P.a_lt_b hp).periodic m

theorem stateData_request (s : StripData Cylinder) (n : ℕ)
    (hepsilon : B.strip.epsilon n = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).request n x =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s B.strip P h c u m n hepsilon x

theorem stateData_referenceRequest (s : StripData Cylinder)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s B.strip P h c u m m hepsilon x

/-- Exact binding to the original common-coordinate full signed request.
The swap only puts the slow coordinates into their original `(time,axial)` order. -/
theorem stateData_referenceRequest_full (s : StripData Point)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m (PhysicalResidualTZ.swapCylinder x) :=
  stateRequest_freeze_full s B.strip P h c u m m hepsilon x

theorem stateData_referenceRequest_fast (s : StripData Point)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (mapFast : Plane → Plane) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m
        (PhysicalResidualTZ.swapCylinder ((x.1.1, (x.1.2.1, mapFast x.1.2.2)), x.2)) := by
  rw [stateData_referenceRequest_full B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow s
    hepsilon x]
  rfl

end IdentityStateData

end NavierStokes.TorusMeanRequestRebase
