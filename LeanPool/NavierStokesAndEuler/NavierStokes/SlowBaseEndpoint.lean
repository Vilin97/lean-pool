/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.EndpointCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointResidualLimits

/-!
# Endpoint extensions of the actual summed slow base

At nonzero axial coordinate the stable coordinate extension has positive q.
The original cutoff schedule therefore gives a locally finite series on an
open neighborhood crossing t = 1. No new summation or cutoff choice is made.

For velocity and pressure, the nonzero-axial extension combines with the
proved heat exterior on the central plane.  The forward-integral potential
is only extended at nonzero axial coordinate here; a central-plane gauge
correction is a separate construction.
-/

@[expose] public section


namespace NavierStokes.SlowBaseEndpoint

noncomputable section

open Set Filter Metric
open ProblemStatement SimilarityProfile SlowBorelBase
open scoped Topology ContDiff BigOperators

section LocallyFiniteProfiles

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The same coefficient series evaluated at the actual stable coordinate
extension, including the original leading power. -/
noncomputable def profileExtension (a : ℕ → ℕ) (h b : ℝ) (f : ℕ → Inner → V)
    (p : PhysicalPoint) : V :=
  (EndpointCoordinates.chartExtension h p).1 ^ b •
    slowSum a h f (EndpointCoordinates.chartExtension h p)

/-- Cartesian profile extension, given by `profileExtension a h b f
(AxisymmetricFields.profilePoint z.1 z.2)`. -/
noncomputable def cartesianProfileExtension (a : ℕ → ℕ) (h b : ℝ)
    (f : ℕ → Inner → V) (z : SpaceTime) : V :=
  profileExtension a h b f (AxisymmetricFields.profilePoint z.1 z.2)

theorem profileExtension_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {p : PhysicalPoint}
    (hp : p ∈ EndpointCoordinates.domain h) :
    ContDiffAt ℝ ∞ (profileExtension a h b f) p := by
  have hc := EndpointCoordinates.chartExtension_smoothAt hh hh1 hp
  have hq : 0 < (EndpointCoordinates.chartExtension h p).1 :=
    EndpointCoordinates.qExtension_pos hp
  exact (hc.fst.rpow_const_of_ne hq.ne').smul
    ((slowSum_smoothAt ha hf h hq).comp p hc)

theorem profileExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) :
    ContDiffOn ℝ ∞ (profileExtension a h b f) (EndpointCoordinates.domain h) :=
  fun _ hp => (profileExtension_smoothAt ha hh hh1 hf b hp).contDiffWithinAt

theorem profileExtension_eq_physical (a : ℕ → ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (b : ℝ) (f : ℕ → Inner → V)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    profileExtension a h b f p = physicalProfile a h b f p := by
  simp only [profileExtension, EndpointCoordinates.chartExtension_eq_physical hh hh1 hp,
    physicalProfile]

theorem profileExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (b : ℝ) (f : ℕ → Inner → V)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    profileExtension a h b f =ᶠ[𝓝 p] physicalProfile a h b f := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with y hy
  exact profileExtension_eq_physical a hh hh1 b f hy

theorem cartesianProfileExtension_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) {z : SpaceTime}
    (hz : z ∈ EndpointCoordinates.cartesianDomain h) :
    ContDiffAt ℝ ∞ (cartesianProfileExtension a h b f) z :=
  (profileExtension_smoothAt ha hh hh1 hf b hz).comp z
    AxisymmetricFields.contDiff_profilePoint.contDiffAt

theorem cartesianProfileExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {f : ℕ → Inner → V}
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (b : ℝ) :
    ContDiffOn ℝ ∞ (cartesianProfileExtension a h b f) (EndpointCoordinates.cartesianDomain h) :=
  fun _ hz => (cartesianProfileExtension_smoothAt ha hh hh1 hf b hz).contDiffWithinAt

/-- One neighborhood and one finite index work for every coefficient
family.  In particular the seven bundled fields keep the same schedule. -/
theorem endpoint_common_finite_index {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {x : Space} (hx : x 2 ≠ 0) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      U ⊆ EndpointCoordinates.cartesianDomain h ∧ ∃ N : ℕ,
      ∀ z ∈ U, ∀ f : ℕ → Inner → V,
        (∀ j : ℕ, N ≤ j → slowStage a h f j (EndpointCoordinates.cartesianExtension h z) = 0) ∧
        slowSum a h f (EndpointCoordinates.cartesianExtension h z) =
          f 0 (EndpointCoordinates.cartesianExtension h z).2 +
            ∑ j ∈ Finset.range N, slowStage a h f j (EndpointCoordinates.cartesianExtension h z) :=
                by
  obtain ⟨U, hU, hxU, hsub, _, hroot, hq⟩ :=
    EndpointCoordinates.cartesian_endpoint_neighborhood hh hh1 hx
  obtain ⟨N, hN⟩ := SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood
    (fun j => (a j : ℝ)) (SolenoidalDiagonal.realScales_tendsto ha)
    (EndpointCoordinates.endpointRoot_pos (2 * h) hx)
  refine ⟨U, hU, hxU, hsub, N, ?_⟩
  intro z hz f
  have hzero : ∀ j : ℕ, N ≤ j →
      slowStage a h f j (EndpointCoordinates.cartesianExtension h z) = 0 := by
    intro j hj
    simp only [slowStage, SolenoidalDiagonal.cutStage,
      hN j hj _ (hq z hz).1, zero_smul]
  refine ⟨hzero, ?_⟩
  change f 0 _ + (∑' j, slowStage a h f j _) = _
  rw [tsum_eq_sum (s := Finset.range N) (fun j hj =>
    hzero j (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)))]

end LocallyFiniteProfiles

section ActualFields

/-- Stream extension, given by `profileExtension a h (-CoordinateAlgebra.A h) (bundleComponent C
d 0)`. -/
noncomputable def streamExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  profileExtension a h (-CoordinateAlgebra.A h) (bundleComponent C d 0)

/-- Swirl extension, given by `profileExtension a h (1 / 2 - CoordinateAlgebra.A h)
(bundleComponent C d 1)`. -/
noncomputable def swirlExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  profileExtension a h (1 / 2 - CoordinateAlgebra.A h) (bundleComponent C d 1)

/-- Potential extension, given by `AxisymmetricFields.potential (streamExtension a h C d)
(swirlExtension a h C d)`. -/
noncomputable def potentialExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamExtension a h C d) (swirlExtension a h C d)

/-- Velocity extension, given by `SpatialCurl.spatialCurl (potentialExtension a h C d)`. -/
noncomputable def velocityExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  SpatialCurl.spatialCurl (potentialExtension a h C d)

/-- Pressure extension, given by `cartesianProfileExtension a h (-2 * CoordinateAlgebra.A h)
(bundleComponent C d 2)`. -/
noncomputable def pressureExtension (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : PressureField :=
  cartesianProfileExtension a h (-2 * CoordinateAlgebra.A h) (bundleComponent C d 2)

theorem potentialExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (potentialExtension a h C d) (EndpointCoordinates.cartesianDomain h) := by
  rw [potentialExtension, BaseResidual.potential_eq_scalars]
  exact BaseResidual.potentialFromScalars_smooth
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _)

theorem velocityExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (velocityExtension a h C d) (EndpointCoordinates.cartesianDomain h) := by
  intro z hz
  exact (SpatialCurl.contDiffAt_spatialCurl
    ((potentialExtension_smoothOn ha hh hh1 hd C).contDiffAt
      ((EndpointCoordinates.cartesianDomain_open h).mem_nhds hz)) (by simp)).contDiffWithinAt

theorem pressureExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (pressureExtension a h C d) (EndpointCoordinates.cartesianDomain h) :=
  cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 2) _

theorem potentialExtension_eq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    potentialExtension a h C d z = BaseResidual.summedPotential a h C d z := by
  have h0 := profileExtension_eq_physical a hh hh1 (-CoordinateAlgebra.A h)
    (bundleComponent C d 0) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have h1 := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  simp only [potentialExtension, BaseResidual.summedPotential, AxisymmetricFields.potential,
    streamExtension, swirlExtension, h0, h1, streamFactor, swirlPotential]

theorem potentialExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    potentialExtension a h C d =ᶠ[𝓝 z] BaseResidual.summedPotential a h C d := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
  exact potentialExtension_eq a hh hh1 C d hy

theorem velocityExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    velocityExtension a h C d =ᶠ[𝓝 z] baseVelocity a h C d :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (potentialExtension_eventuallyEq a hh hh1 C d hz)

theorem pressureExtension_eventuallyEq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    pressureExtension a h C d =ᶠ[𝓝 z] basePressure a h C d := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
  exact profileExtension_eq_physical a hh hh1 (-2 * CoordinateAlgebra.A h)
    (bundleComponent C d 2) hy

/-- The original forward-integral potential extends at every nonzero
axial endpoint, with exactly the original cutoff schedule. -/
noncomputable def potentialNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (BaseResidual.summedPotential a h C d) x where
  value := potentialExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := potentialExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => potentialExtension_eq a hh hh1 C d hz.2.1

/-- Velocity nonzero axial, bundling `value`, `domain`, `isOpen`, `mem` and the required
compatibility proofs. -/
noncomputable def velocityNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (baseVelocity a h C d) x where
  value := velocityExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := velocityExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => (velocityExtension_eventuallyEq a hh hh1 C d hz.2.1).self_of_nhds

/-- Pressure nonzero axial, bundling `value`, `domain`, `isOpen`, `mem` and the required
compatibility proofs. -/
noncomputable def pressureNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (basePressure a h C d) x where
  value := pressureExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := pressureExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => (pressureExtension_eventuallyEq a hh hh1 C d hz.2.1).self_of_nhds

/-- The fixed physical radial anchor used for the exact gauge correction. -/
noncomputable def radialAnchor (p : PhysicalPoint) : PhysicalPoint := (p.1, (1, p.2.2))

theorem radialAnchor_smooth : ContDiff ℝ ∞ radialAnchor :=
  contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd)

/-- This is the literal anchored-potential formula.  Equality of its curl
with the original velocity is proved in the separate gauge module. -/
noncomputable def anchoredPotential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d)
    (fun p => swirlPotential a h C d p - swirlPotential a h C d (radialAnchor p))

/-- Anchored potential extension, constructed using `AxisymmetricFields.potential`. -/
noncomputable def anchoredPotentialExtension (a : ℕ → ℕ) (h C : ℝ)
    (d : Coefficients) : VelocityField :=
  AxisymmetricFields.potential (streamExtension a h C d)
    (fun p => swirlExtension a h C d p - swirlExtension a h C d (radialAnchor p))

theorem anchoredPotentialExtension_smoothOn {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
    (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (anchoredPotentialExtension a h C d) (EndpointCoordinates.cartesianDomain h) :=
        by
  have hanchor : ContDiffOn ℝ ∞
      (fun z : SpaceTime => swirlExtension a h C d (radialAnchor (AxisymmetricFields.profilePoint
          z.1 z.2)))
      (EndpointCoordinates.cartesianDomain h) := by
    intro z hz
    have hz' : radialAnchor (AxisymmetricFields.profilePoint z.1 z.2) ∈
        EndpointCoordinates.domain h := hz
    exact ((profileExtension_smoothAt ha hh hh1 (bundleComponent_smooth hd C 1)
      (1 / 2 - CoordinateAlgebra.A h) hz').comp z
        (radialAnchor_smooth.comp
            AxisymmetricFields.contDiff_profilePoint).contDiffAt).contDiffWithinAt
  rw [anchoredPotentialExtension, BaseResidual.potential_eq_scalars]
  exact BaseResidual.potentialFromScalars_smooth
    (cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    ((cartesianProfileExtension_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _).sub hanchor)

theorem anchoredPotentialExtension_eq (a : ℕ → ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (C : ℝ) (d : Coefficients) {z : SpaceTime} (hz : z.1 < 1) :
    anchoredPotentialExtension a h C d z = anchoredPotential a h C d z := by
  have h0 := profileExtension_eq_physical a hh hh1 (-CoordinateAlgebra.A h)
    (bundleComponent C d 0) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have h1 := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have hr := profileExtension_eq_physical a hh hh1 (1 / 2 - CoordinateAlgebra.A h)
    (bundleComponent C d 1) (p := radialAnchor (AxisymmetricFields.profilePoint z.1 z.2)) hz
  simp only [anchoredPotentialExtension, anchoredPotential, AxisymmetricFields.potential,
    streamExtension, swirlExtension, h0, h1, hr, streamFactor, swirlPotential]

/-- The exact anchored potential also extends at every nonzero axial
endpoint.  In particular the subtracted gauge uses the same sum and schedule. -/
noncomputable def anchoredPotentialNonzeroAxial {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d)
    (C : ℝ) {x : Space} (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (anchoredPotential a h C d) x where
  value := anchoredPotentialExtension a h C d
  domain := EndpointCoordinates.cartesianDomain h
  isOpen := EndpointCoordinates.cartesianDomain_open h
  mem := EndpointCoordinates.cartesian_endpoint_mem hh hh1 hx
  smooth := anchoredPotentialExtension_smoothOn ha hh hh1 hd C
  agrees := fun _ hz => anchoredPotentialExtension_eq a hh hh1 C d hz.2.1

end ActualFields

section LocalClosedExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Convert a genuine locally smooth closed-side continuation into an
ambient smooth extension.  A local bump and the already proved joint
Taylor--Borel extension are the actual construction. -/
theorem oneSidedExtension_of_closed_local {f g : SpaceTime → V} {x : Space}
    {U : Set SpaceTime} (hU : IsOpen U) (hxU : (1, x) ∈ U)
    (hg : ContDiffOn ℝ ∞ g (U ∩ SpacetimeEndpoint.closedPast 1))
    (he : EqOn g f (U ∩ SpacetimeEndpoint.openPast 1)) :
    Nonempty (JointResidualLimits.OneSidedExtension f x) := by
  obtain ⟨r, hr, hrU⟩ : ∃ r, 0 < r ∧ closedBall (1, x) r ⊆ U :=
    nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let χ : ContDiffBump ((1 : ℝ), x) :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  let cut : SpaceTime → V := fun z => χ z • g z
  have hlocal : ContDiffOn ℝ ∞ cut (SpacetimeEndpoint.closedPast 1) := by
    intro z hz
    by_cases hzU : z ∈ U
    · have hgs : ContDiffWithinAt ℝ ∞ g (SpacetimeEndpoint.closedPast 1) z :=
        (hg z ⟨hzU, hz⟩).mono_of_mem_nhdsWithin
          (inter_mem (nhdsWithin_le_nhds (hU.mem_nhds hzU)) self_mem_nhdsWithin)
      exact χ.contDiff.contDiffWithinAt.smul hgs
    · have hzχ : z ∉ tsupport (χ : SpaceTime → ℝ) := by
        rw [χ.tsupport_eq]
        exact fun hzχ => hzU (hrU hzχ)
      have hz0 : (χ : SpaceTime → ℝ) =ᶠ[𝓝 z] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hzχ
      have hl0 : cut =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hz0] with y hy
        change χ y = 0 at hy
        simp only [cut, hy, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hl0).contDiffWithinAt
  let G := SpacetimeGluing.smoothExtension 1 cut hlocal
  refine ⟨⟨G, ball (1, x) (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    (SpacetimeGluing.smoothExtension_contDiff hlocal).contDiffOn, ?_⟩⟩
  intro z hz
  have hzU : z ∈ U := hrU ((ball_subset_closedBall.trans
    (closedBall_subset_closedBall (half_le_self hr.le))) hz.1)
  have hzP : z ∈ SpacetimeEndpoint.closedPast 1 :=
    ⟨(show z.1 < 1 from hz.2.1).le, hz.2.2⟩
  change SpacetimeGluing.smoothExtension 1 cut hlocal z = f z
  rw [SpacetimeGluing.smoothExtension_eqOn_past hlocal hzP]
  change χ z • g z = f z
  rw [χ.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hz.1).le), one_smul]
  exact he ⟨hzU, hz.2⟩

end LocalClosedExtension

theorem radialEnergy_pos_of_nonzero_of_axial_zero {x : Space} (hx : x ≠ 0) (hz : x 2 = 0) :
    0 < AxisymmetricFields.radialEnergy x := by
  by_contra h
  have hr := AxisymmetricFields.radialEnergy_nonneg x
  have he : AxisymmetricFields.radialEnergy x = 0 := le_antisymm (le_of_not_gt h) hr
  have h0 : x 0 = 0 := by
    dsimp only [AxisymmetricFields.radialEnergy] at he
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  have h1 : x 1 = 0 := by
    dsimp only [AxisymmetricFields.radialEnergy] at he
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  apply hx
  ext i
  fin_cases i <;> simpa only [PiLp.zero_apply] using (show x _ = 0 from by assumption)

section CompleteAwayExtensions

open GlobalSlowProfiles AssembledSlowBase ModulatedExterior

/-- For the actual repaired scheme, velocity and pressure have ambient
smooth continuations at every nonzero point of the terminal slice. -/
theorem realized_fields_awayExtensions {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
    {s : Scheme S F.data.h W.axis.normalization} {d : Coefficients}
    (hd : RealizesScheme s M.contains d)
    (hbase : s.base = (modifiedScheme W Q M).base) (houter : s.B = nominalOuterRadius W)
    (hds : SmoothCoefficients d) (henergy : RestoredSquaredSwirl W Q (S := S))
    {a : ℕ → ℕ} (ha : StrictMono a) :
    JointResidualLimits.AwayExtensions (baseVelocity a F.data.h W.axis.normalization d) ∧
      JointResidualLimits.AwayExtensions (basePressure a F.data.h W.axis.normalization d) := by
  have hall (x : Space) (hx : x ≠ 0) :
      Nonempty (JointResidualLimits.OneSidedExtension
        (baseVelocity a F.data.h W.axis.normalization d) x) ∧
      Nonempty (JointResidualLimits.OneSidedExtension
        (basePressure a F.data.h W.axis.normalization d) x) := by
    by_cases hz : x 2 = 0
    · obtain ⟨U, hU, hxU, _, _, hu, hp⟩ := realized_terminal_extension W Q M hd hbase houter
        hds henergy ha hz (radialEnergy_pos_of_nonzero_of_axial_zero hx hz)
      constructor
      · apply oneSidedExtension_of_closed_local hU hxU hu
        exact fun _ hy => completedVelocity_before _ _ _ hy.2.1
      · apply oneSidedExtension_of_closed_local hU hxU hp
        exact fun _ hy => completedPressure_before _ _ _ hy.2.1
    · exact ⟨⟨velocityNonzeroAxial ha F.data.h_pos F.data.h_lt_half hds W.axis.normalization hz⟩,
        ⟨pressureNonzeroAxial ha F.data.h_pos F.data.h_lt_half hds W.axis.normalization hz⟩⟩
  exact ⟨fun x hx => (hall x hx).1, fun x hx => (hall x hx).2⟩

end CompleteAwayExtensions

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The original potential of the actual entrance-aligned base extends at
nonzero axial coordinate, with its selected scale sequence unchanged. -/
noncomputable def finalPotentialNonzeroAxial (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (FinalSlowBase.vectorPotential H v upper B) x :=
  potentialNonzeroAxial (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) W.axis.normalization hx

/-- Final velocity nonzero axial, constructed using `velocityNonzeroAxial`. -/
noncomputable def finalVelocityNonzeroAxial (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (FinalSlowBase.velocity H v upper B) x :=
  velocityNonzeroAxial (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) W.axis.normalization hx

/-- Final pressure nonzero axial, constructed using `pressureNonzeroAxial`. -/
noncomputable def finalPressureNonzeroAxial (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension (FinalSlowBase.pressure H v upper B) x :=
  pressureNonzeroAxial (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) W.axis.normalization hx

/-- Final anchored potential nonzero axial, constructed using `anchoredPotentialNonzeroAxial`. -/
noncomputable def finalAnchoredPotentialNonzeroAxial (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) :
    JointResidualLimits.OneSidedExtension
      (anchoredPotential (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
        (FinalSlowBase.coefficients H v)) x :=
  anchoredPotentialNonzeroAxial (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) W.axis.normalization hx

/-- This includes the central plane and the spatial axis away from zero.
The inputs are the actual finite profile witnesses, not endpoint assumptions. -/
theorem final_fields_awayExtensions (upper : ℝ) (B : ℕ) :
    JointResidualLimits.AwayExtensions (FinalSlowBase.velocity H v upper B) ∧
      JointResidualLimits.AwayExtensions (FinalSlowBase.pressure H v upper B) :=
  realized_fields_awayExtensions W v.profiles v.finiteModification
    (FinalSlowBase.realizesScheme H v) (EntranceAlignedBase.modulated_base_eq H v)
    (EntranceAlignedBase.modulated_outer H v) (FinalSlowBase.coefficients_smooth H v)
    (ModulatedExterior.actual_squared_swirl_restored v) (FinalSlowBase.scales_strictMono H v upper
        B)

theorem final_potential_jets_tendsto (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 ≠ 0) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n (FinalSlowBase.vectorPotential H v upper B))
      (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (iteratedFDeriv ℝ n (finalPotentialNonzeroAxial H v upper B hx).value (1, x))) :=
  (finalPotentialNonzeroAxial H v upper B hx).jet_tendsto n

/-- The already constructed finite profile gives actual endpoint
extensions for the selected slow base without another profile input. -/
theorem constructed_fields_awayExtensions (upper : ℝ) (B : ℕ) :
    JointResidualLimits.AwayExtensions
        (FinalSlowBase.velocity FinalSlowBase.actualProfile.certificate
          FinalSlowBase.actualProfile.modulation upper B) ∧
      JointResidualLimits.AwayExtensions
        (FinalSlowBase.pressure FinalSlowBase.actualProfile.certificate
          FinalSlowBase.actualProfile.modulation upper B) :=
  final_fields_awayExtensions FinalSlowBase.actualProfile.certificate
    FinalSlowBase.actualProfile.modulation upper B

end FinalBase

end

end NavierStokes.SlowBaseEndpoint
