/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalGraphBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LiftedMeanResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanChartCompatibility

/-!
# The physical residual of a scaled graph pullback

This file keeps the cylindrical angle separate from the lifted slow and fast
variables.  Every differential operator is an actual Frechet derivative.
-/

@[expose] public section


namespace NavierStokes.PhysicalResidualBridge

open Set Filter Function
open scoped Topology ContDiff
open ProblemStatement HarmonicCalculus


noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The complete real graph-coordinate residual, including the quadratic
transport term and the cylindrical connection terms. -/
noncomputable def graphResidual (ε : ℝ) (R : E → ℝ) (Vr Vθ Vz Vt : E → E)
    (a : E → Fin 3 → ℝ) (p : E → ℝ) (x : E) : Fin 3 → ℝ := fun i =>
  along Vt (fun y => a y i) x +
    LinearWaveResidual.realTransport R Vr Vθ Vz a a x i -
    ε * LinearWaveResidual.realFrameLaplacian R Vr Vθ Vz a x i +
    ![along Vr p x, (R x)⁻¹ * along Vθ p x, along Vz p x] i

theorem along_scaled_pull {Γ : E → F} {V : E → E} {W : F → F}
    {f : F → ℝ} {x : E} (c k : ℝ)
    (hΓ : DifferentiableAt ℝ Γ x) (hf : DifferentiableAt ℝ f (Γ x))
    (hV : fderiv ℝ Γ x (V x) = k • W (Γ x)) :
    along V (fun y => c * f (Γ y)) x = c * k * along W f (Γ x) := by
  have hd := (hf.hasFDerivAt.comp x hΓ.hasFDerivAt).const_mul c
  dsimp only [Function.comp_def] at hd
  unfold along
  rw [hd.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    hV, map_smul, smul_eq_mul]
  ring

/-- Repeating the genuine derivative differentiates the target direction
field as well.  In particular this includes the radial-profile derivative. -/
theorem along_twice_scaled_pull {Ω : Set E} {U : Set F} {Γ : E → F}
    {V : E → E} {W : F → F} {f : F → ℝ} {x : E} (c k : ℝ)
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hΓ : ContDiffOn ℝ ∞ Γ Ω)
    (hmap : MapsTo Γ Ω U) (hW : ContDiffOn ℝ ∞ W U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hV : ∀ y ∈ Ω, fderiv ℝ Γ y (V y) = k • W (Γ y)) (hx : x ∈ Ω) :
    along V (along V (fun y => c * f (Γ y))) x =
      c * k ^ 2 * along W (along W f) (Γ x) := by
  have he : EqOn (along V (fun y => c * f (Γ y)))
      (fun y => (c * k) * along W f (Γ y)) Ω := by
    intro y hy
    exact along_scaled_pull c k
      ((hΓ.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hf.contDiffAt (hU.mem_nhds (hmap hy))).differentiableAt (by simp)) (hV y hy)
  rw [along_congr hΩ he hx]
  rw [along_scaled_pull (c * k) k
    ((hΓ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (((contDiffOn_along hU hW hf).contDiffAt (hU.mem_nhds (hmap hx))).differentiableAt
      (by simp)) (hV x hx)]
  ring

/-- Differential data used by the generic pullback calculation below.  The
explicit physical graph later supplies every field of this structure. -/
structure PullbackData (Ω : Set E) (U : Set F) (Γ : E → F)
    (l v : ℝ) (R : F → ℝ) (Vr Vθ Vz Vt : F → F)
    (Sr Sθ Sz St : E → E) (r : E → ℝ) : Prop where
  source_open : IsOpen Ω
  target_open : IsOpen U
  smooth : ContDiffOn ℝ ∞ Γ Ω
  mapsTo : MapsTo Γ Ω U
  radial_smooth : ContDiffOn ℝ ∞ Vr U
  angular_smooth : ContDiffOn ℝ ∞ Vθ U
  axial_smooth : ContDiffOn ℝ ∞ Vz U
  radial : ∀ x ∈ Ω, fderiv ℝ Γ x (Sr x) = l • Vr (Γ x)
  angular : ∀ x ∈ Ω, fderiv ℝ Γ x (Sθ x) = Vθ (Γ x)
  axial : ∀ x ∈ Ω, fderiv ℝ Γ x (Sz x) = l • Vz (Γ x)
  temporal : ∀ x ∈ Ω, fderiv ℝ Γ x (St x) = (v * l) • Vt (Γ x)
  radius : ∀ x ∈ Ω, R (Γ x) = l * r x

theorem graphResidual_scaled_pull {Ω : Set E} {U : Set F} {Γ : E → F}
    {l v ε : ℝ} {R : F → ℝ} {Vr Vθ Vz Vt : F → F}
    {Sr Sθ Sz St : E → E} {r : E → ℝ}
    (G : PullbackData Ω U Γ l v R Vr Vθ Vz Vt Sr Sθ Sz St r)
    (hl : l ≠ 0) (hε : l = v * ε)
    {a : F → Fin 3 → ℝ} {p : F → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {x : E} (hx : x ∈ Ω) (hr : r x ≠ 0) (i : Fin 3) :
    graphResidual 1 r Sr Sθ Sz St (fun y j => v * a (Γ y) j)
      (fun y => v ^ 2 * p (Γ y)) x i =
      v ^ 2 * l * graphResidual ε R Vr Vθ Vz Vt a p (Γ x) i := by
  have hdΓ := (G.smooth.contDiffAt (G.source_open.mem_nhds hx)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hda j := ((ha j).contDiffAt (G.target_open.mem_nhds (G.mapsTo hx))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hdp := (hp.contDiffAt (G.target_open.mem_nhds (G.mapsTo hx))).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hθ (y : E) (hy : y ∈ Ω) : fderiv ℝ Γ y (Sθ y) = (1 : ℝ) • Vθ (Γ y) := by
    simpa only [one_smul] using G.angular y hy
  have hAr j c := along_scaled_pull c l hdΓ (hda j) (G.radial x hx)
  have hAθ j c := along_scaled_pull c 1 hdΓ (hda j) (hθ x hx)
  have hAz j c := along_scaled_pull c l hdΓ (hda j) (G.axial x hx)
  have hAt j c := along_scaled_pull c (v * l) hdΓ (hda j) (G.temporal x hx)
  have hArr j c := along_twice_scaled_pull c l G.source_open G.target_open G.smooth
    G.mapsTo G.radial_smooth (ha j) G.radial hx
  have hAθθ j c := along_twice_scaled_pull c 1 G.source_open G.target_open G.smooth
    G.mapsTo G.angular_smooth (ha j) hθ hx
  have hAzz j c := along_twice_scaled_pull c l G.source_open G.target_open G.smooth
    G.mapsTo G.axial_smooth (ha j) G.axial hx
  have hPr := along_scaled_pull (v ^ 2) l hdΓ hdp (G.radial x hx)
  have hPθ := along_scaled_pull (v ^ 2) 1 hdΓ hdp (hθ x hx)
  have hPz := along_scaled_pull (v ^ 2) l hdΓ hdp (G.axial x hx)
  fin_cases i <;>
    simp [graphResidual, LinearWaveResidual.realTransport,
      LinearWaveResidual.realFrameLaplacian, LinearWaveResidual.realAngularGenerator,
      cylindricalLaplacian, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, hAr, hAθ, hAz, hAt, hArr, hAθθ, hAzz, hPr, hPθ, hPz,
      smul_eq_mul, G.radius x hx] <;>
    field_simp [hl, hr] <;> rw [hε] <;> ring

theorem graphResidual_eq_cylindrical {U : Set SpaceTime}
    {a : VelocityField} {p : PressureField} {t : ℝ} {q : Space}
    (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ a U)
    (hp : ContDiffOn ℝ ∞ p U) (hx : (t, q) ∈ U) :
    graphResidual 1 LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) LinearWaveResidual.physicalTimeDirection
      (fun z i => a z i) p (t, q) =
      fun i => CylindricalResidual.cylindricalResidual a p t q i := by
  have hAc (i : Fin 3) : ContDiffOn ℝ ∞ (fun z => a z i) U :=
    (AxisymmetricFields.projection i).contDiff.comp_contDiffOn ha
  have had := (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hpd := (hp.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have has : ContDiffAt ℝ 2 (fun y : Space => a (t, y)) q :=
    ((ha.contDiffAt (hU.mem_nhds hx)).comp q (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hasd := has.differentiableAt (by norm_num)
  have hfirst (i j : Fin 3) :
      along (LinearWaveResidual.spaceDirection i) (fun z => a z j) (t, q) =
      CylindricalResidual.dCoord i (fun y => a (t, y)) q j := by
    rw [LinearWaveResidual.along_space_slice
      (((hAc j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    exact CylindricalResidual.dCoord_map (AxisymmetricFields.projection j) hasd i
  have hLap (j : Fin 3) : cylindricalLaplacian LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) (fun z => a z j) (t, q) =
      CylindricalResidual.scalarLaplacian (fun y => a (t, y)) q j := by
    rw [LinearWaveResidual.laplacian_space_slice hU (hAc j) hx]
    exact CylindricalResidual.scalarLaplacian_component has j
  have htime (j : Fin 3) :
      along LinearWaveResidual.physicalTimeDirection (fun z => a z j) (t, q) =
      temporalDerivative a t q j := by
    calc
      _ = (along LinearWaveResidual.physicalTimeDirection a (t, q)) j :=
        LinearWaveResidual.along_map (AxisymmetricFields.projection j) _ had
      _ = _ := congrArg (fun v : Space => v j) (LinearWaveResidual.along_time_slice had)
  ext i
  fin_cases i <;>
    simp [graphResidual, LinearWaveResidual.realTransport,
      LinearWaveResidual.realFrameLaplacian, LinearWaveResidual.realAngularGenerator,
      hfirst, hLap, htime, LinearWaveResidual.along_space_slice hpd,
      LinearWaveResidual.coordinateRadius, CylindricalResidual.cylindricalResidual,
      CylindricalResidual.vectorAdvection, CylindricalResidual.vectorLaplacian,
      CylindricalResidual.scalarGradient, CylindricalResidual.connection_apply] <;> ring

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ
/-- Lift: an abbreviation for `ℝ × (Plane × Plane)`. -/
abbrev Lift := ℝ × (Plane × Plane)
/-- Cylinder: an abbreviation for `Lift × ℝ`. -/
abbrev Cylinder := Lift × ℝ

/-- Numerical and directional data of one fixed chart. -/
structure ScaledGraph where
  /-- Radial scale of `ScaledGraph`, of type `ℝ`. -/
  radialScale : ℝ
  /-- Velocity scale of `ScaledGraph`, of type `ℝ`. -/
  velocityScale : ℝ
  /-- Epsilon of `ScaledGraph`, of type `ℝ`. -/
  epsilon : ℝ
  /-- Exponent of `ScaledGraph`, of type `ℝ`. -/
  exponent : ℝ
  /-- Frequency of `ScaledGraph`, of type `ℝ`. -/
  frequency : ℝ
  /-- Fast coefficient of `ScaledGraph`, of type `ℝ`. -/
  fastCoefficient : ℝ
  /-- Radial vector of `ScaledGraph`, of type `Plane`. -/
  radialVector : Plane
  /-- Temporal vector of `ScaledGraph`, of type `Plane`. -/
  temporalVector : Plane

namespace ScaledGraph

/-- Map as an element of `Cylinder`. -/
noncomputable def map (G : ScaledGraph) (p : SpaceTime) : Cylinder :=
  ((G.radialScale * p.2 0,
    ((G.radialScale * G.epsilon * p.2 2,
       G.velocityScale * G.radialScale * G.epsilon * (1 - p.1)),
     (G.frequency * (G.radialScale * p.2 0) ^ G.exponent) • G.radialVector +
       (G.velocityScale * G.radialScale * G.fastCoefficient * p.1) • G.temporalVector)),
    p.2 1)

/-- Radius, given by `x.1.1`. -/
noncomputable def radius (x : Cylinder) : ℝ := x.1.1

/-- Radial, given by `((1, ((0, 0), (G.frequency * GraphCalculus.radialSpeed G.exponent x.1.1) •
G.radialVector)), 0)`. -/
noncomputable def radial (G : ScaledGraph) (x : Cylinder) : Cylinder :=
  ((1, ((0, 0), (G.frequency * GraphCalculus.radialSpeed G.exponent x.1.1) •
    G.radialVector)), 0)

/-- Angular, given by `(0, 1)`. -/
noncomputable def angular (_x : Cylinder) : Cylinder := (0, 1)

/-- Axial, given by `((0, ((G.epsilon, 0), 0)), 0)`. -/
noncomputable def axial (G : ScaledGraph) (_x : Cylinder) : Cylinder :=
  ((0, ((G.epsilon, 0), 0)), 0)

/-- Temporal, given by `((0, ((0, -G.epsilon), G.fastCoefficient • G.temporalVector)), 0)`. -/
noncomputable def temporal (G : ScaledGraph) (_x : Cylinder) : Cylinder :=
  ((0, ((0, -G.epsilon), G.fastCoefficient • G.temporalVector)), 0)

theorem map_smoothAt (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) : ContDiffAt ℝ ∞ G.map p := by
  have hP (j : Fin 3) : ContDiffAt ℝ ∞ (fun z : SpaceTime => z.2 j) p :=
    (PhysicalGraphBounds.coordinateProjection j).contDiff.contDiffAt
  have hR : ContDiffAt ℝ ∞ (fun z : SpaceTime => G.radialScale * z.2 0) p :=
    contDiffAt_const.mul (hP 0)
  have hY : ContDiffAt ℝ ∞ (fun z : SpaceTime =>
      (G.frequency * (G.radialScale * z.2 0) ^ G.exponent) • G.radialVector) p :=
    (contDiffAt_const.mul (hR.rpow_const_of_ne hr)).smul contDiffAt_const
  have hT : ContDiffAt ℝ ∞ (fun z : SpaceTime =>
      (G.velocityScale * G.radialScale * G.fastCoefficient * z.1) • G.temporalVector) p :=
    (contDiffAt_const.mul contDiffAt_fst).smul contDiffAt_const
  exact (hR.prodMk (((contDiffAt_const.mul (hP 2)).prodMk
    (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_fst))).prodMk
      (hY.add hT))).prodMk (hP 1)

theorem fderiv_map_apply (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) (w : SpaceTime) :
    fderiv ℝ G.map p w =
    ((G.radialScale * w.2 0,
      ((G.radialScale * G.epsilon * w.2 2,
        -(G.velocityScale * G.radialScale * G.epsilon) * w.1),
       (G.frequency * GraphCalculus.radialSpeed G.exponent
          (G.radialScale * p.2 0) * G.radialScale * w.2 0) • G.radialVector +
         (G.velocityScale * G.radialScale * G.fastCoefficient * w.1) • G.temporalVector)),
      w.2 1) := by
  have hP (j : Fin 3) : HasFDerivAt (fun z : SpaceTime => z.2 j)
      (PhysicalGraphBounds.coordinateProjection j) p :=
    (PhysicalGraphBounds.coordinateProjection j).hasFDerivAt
  have htime : HasFDerivAt (fun z : SpaceTime => z.1)
      (ContinuousLinearMap.fst ℝ ℝ Space) p :=
    (ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt
  have hR := (hP 0).const_mul G.radialScale
  have hY := ((hR.rpow_const (p := G.exponent) (Or.inl hr)).const_mul G.frequency).smul_const
    G.radialVector
  have hT := (htime.const_mul (G.velocityScale * G.radialScale * G.fastCoefficient)).smul_const
    G.temporalVector
  have hτ : HasFDerivAt (fun z : SpaceTime =>
      (G.velocityScale * G.radialScale * G.epsilon) * (1 - z.1))
      ((G.velocityScale * G.radialScale * G.epsilon) •
        (0 - ContinuousLinearMap.fst ℝ ℝ Space)) p :=
    ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).sub htime).const_mul _
  have hd := (hR.prodMk (((hP 2).const_mul (G.radialScale * G.epsilon)).prodMk hτ |>.prodMk
    (hY.add hT))).prodMk (hP 1)
  change HasFDerivAt G.map _ p at hd
  rw [hd.fderiv]
  ext <;> simp [ContinuousLinearMap.fst, GraphCalculus.radialSpeed,
    smul_eq_mul] <;> ring_nf <;> simp

theorem map_radial (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) :
    fderiv ℝ G.map p (LinearWaveResidual.spaceDirection 0 p) =
      G.radialScale • G.radial (G.map p) := by
  rw [G.fderiv_map_apply hr]
  ext <;> simp [radial, map, LinearWaveResidual.spaceDirection,
    coordinateVector, smul_eq_mul] <;> ring

theorem map_angular (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) :
    fderiv ℝ G.map p (LinearWaveResidual.spaceDirection 1 p) = angular (G.map p) := by
  rw [G.fderiv_map_apply hr]
  ext <;> simp [angular, LinearWaveResidual.spaceDirection,
    coordinateVector]

theorem map_axial (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) :
    fderiv ℝ G.map p (LinearWaveResidual.spaceDirection 2 p) =
      G.radialScale • G.axial (G.map p) := by
  rw [G.fderiv_map_apply hr]
  ext <;> simp [axial, LinearWaveResidual.spaceDirection,
    coordinateVector, smul_eq_mul]

/-- Forward physical time produces minus the slow-time direction. -/
theorem map_temporal (G : ScaledGraph) {p : SpaceTime}
    (hr : G.radialScale * p.2 0 ≠ 0) :
    fderiv ℝ G.map p (LinearWaveResidual.physicalTimeDirection p) =
      (G.velocityScale * G.radialScale) • G.temporal (G.map p) := by
  rw [G.fderiv_map_apply hr]
  ext <;> simp [temporal, LinearWaveResidual.physicalTimeDirection, smul_eq_mul] <;> ring

theorem radial_smooth (G : ScaledGraph) {U : Set Cylinder}
    (hR : ∀ x ∈ U, x.1.1 ≠ 0) : ContDiffOn ℝ ∞ G.radial U := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  have hr : ContDiffAt ℝ ∞ (fun y : Cylinder => y.1.1) x := contDiffAt_fst.fst
  have hc : ContDiffAt ℝ ∞ (fun y : Cylinder =>
      (G.frequency * GraphCalculus.radialSpeed G.exponent y.1.1) • G.radialVector) x :=
    (contDiffAt_const.mul (contDiffAt_const.mul (hr.rpow_const_of_ne (hR x hx)))).smul
      contDiffAt_const
  exact (contDiffAt_const.prodMk (contDiffAt_const.prodMk hc)).prodMk contDiffAt_const

/-- Source, given by `{p | 0 < p.2 0} ∩ G.map ⁻¹' U`. -/
noncomputable def source (G : ScaledGraph) (U : Set Cylinder) : Set SpaceTime :=
  {p | 0 < p.2 0} ∩ G.map ⁻¹' U

theorem source_open (G : ScaledGraph) (hl : 0 < G.radialScale)
    {U : Set Cylinder} (hU : IsOpen U) : IsOpen (G.source U) := by
  have hc : ContinuousOn G.map {p : SpaceTime | 0 < p.2 0} := by
    intro p hp
    exact (G.map_smoothAt (mul_pos hl hp).ne').continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous) hU

theorem pullbackData (G : ScaledGraph) (hl : 0 < G.radialScale)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0) :
    PullbackData (G.source U) U G.map G.radialScale G.velocityScale radius
      G.radial angular G.axial G.temporal
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) LinearWaveResidual.physicalTimeDirection
      LinearWaveResidual.coordinateRadius where
  source_open := G.source_open hl hU
  target_open := hU
  smooth := fun _ hp => (G.map_smoothAt (mul_pos hl hp.1).ne').contDiffWithinAt
  mapsTo := fun _ hp => hp.2
  radial_smooth := G.radial_smooth hR
  angular_smooth := contDiffOn_const
  axial_smooth := contDiffOn_const
  radial := fun _ hp => G.map_radial (mul_pos hl hp.1).ne'
  angular := fun _ hp => G.map_angular (mul_pos hl hp.1).ne'
  axial := fun _ hp => G.map_axial (mul_pos hl hp.1).ne'
  temporal := fun _ hp => G.map_temporal (mul_pos hl hp.1).ne'
  radius := fun _ _ => rfl

/-- Physical cylindrical velocity obtained from the actual graph. -/
noncomputable def velocity (G : ScaledGraph) (a : Cylinder → Fin 3 → ℝ) : VelocityField :=
  fun p => AxisymmetricResidual.pack (G.velocityScale * a (G.map p) 0)
    (G.velocityScale * a (G.map p) 1) (G.velocityScale * a (G.map p) 2)

@[simp] theorem velocity_apply (G : ScaledGraph) (a : Cylinder → Fin 3 → ℝ)
    (p : SpaceTime) (i : Fin 3) : G.velocity a p i = G.velocityScale * a (G.map p) i := by
  fin_cases i <;> simp [velocity]

/-- Pressure, defined pointwise by `G.velocityScale ^ 2 * p (G.map z)`. -/
noncomputable def pressure (G : ScaledGraph) (p : Cylinder → ℝ) : PressureField :=
  fun z => G.velocityScale ^ 2 * p (G.map z)

theorem velocity_smooth (G : ScaledGraph) (hl : 0 < G.radialScale)
    {U : Set Cylinder} {a : Cylinder → Fin 3 → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun z => a z i) U) :
    ContDiffOn ℝ ∞ (G.velocity a) (G.source U) := by
  have hg : ContDiffOn ℝ ∞ G.map (G.source U) :=
    fun p hp => (G.map_smoothAt (mul_pos hl hp.1).ne').contDiffWithinAt
  have hc (i : Fin 3) : ContDiffOn ℝ ∞
      (fun p => G.velocityScale * a (G.map p) i) (G.source U) :=
    contDiffOn_const.mul ((ha i).comp hg (fun _ hp => hp.2))
  exact (((hc 0).smul contDiffOn_const).add ((hc 1).smul contDiffOn_const)).add
    ((hc 2).smul contDiffOn_const)

theorem pressure_smooth (G : ScaledGraph) (hl : 0 < G.radialScale)
    {U : Set Cylinder} {p : Cylinder → ℝ} (hp : ContDiffOn ℝ ∞ p U) :
    ContDiffOn ℝ ∞ (G.pressure p) (G.source U) :=
  contDiffOn_const.mul (hp.comp
    (fun _ hz => (G.map_smoothAt (mul_pos hl hz.1).ne').contDiffWithinAt)
    (fun _ hz => hz.2))

theorem cylindricalResidual_eq (G : ScaledGraph) (hl : 0 < G.radialScale)
    (hε : G.radialScale = G.velocityScale * G.epsilon)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {a : Cylinder → Fin 3 → ℝ} {p : Cylinder → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {z : SpaceTime} (hz : z ∈ G.source U) (i : Fin 3) :
    CylindricalResidual.cylindricalResidual (G.velocity a) (G.pressure p) z.1 z.2 i =
      G.velocityScale ^ 2 * G.radialScale *
        graphResidual G.epsilon radius G.radial angular G.axial G.temporal a p (G.map z) i := by
  rw [← congrFun (graphResidual_eq_cylindrical (G.source_open hl hU)
    (G.velocity_smooth hl ha) (G.pressure_smooth hl hp) hz) i]
  simp only [velocity_apply]
  exact graphResidual_scaled_pull (G.pullbackData hl hU hR) hl.ne' hε ha hp hz hz.1.ne' i

/-- Identification with the viscosity-one Cartesian PDE.  The representation
premises concern only field values on a neighborhood. -/
theorem physical_residual (G : ScaledGraph) (hl : 0 < G.radialScale)
    (hε : G.radialScale = G.velocityScale * G.epsilon)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {a : Cylinder → Fin 3 → ℝ} {p : Cylinder → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {t : ℝ} {q : Space} (hz : (t, q) ∈ G.source U)
    {u : VelocityField} {P : PressureField}
    (hu : ContDiffAt ℝ 2 u (t, CylindricalResidual.chart q))
    (hP : DifferentiableAt ℝ P (t, CylindricalResidual.chart q))
    (hrep : (fun z : SpaceTime => u (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) (G.velocity a z)))
    (hpRep : CylindricalResidual.pressurePullback P =ᶠ[𝓝 (t, q)] G.pressure p)
    (i : Fin 3) :
    CylindricalResidual.frame (-(q 1))
      (navierStokesResidual u P t (CylindricalResidual.chart q)) i =
      G.velocityScale ^ 2 * G.radialScale *
        graphResidual G.epsilon radius G.radial angular G.axial G.temporal a p (G.map (t, q)) i :=
            by
  rw [CylindricalResidual.navierStokesResidual_of_representation hu hP hz.1 hrep hpRep,
    CylindricalResidual.frame_inverse]
  exact G.cylindricalResidual_eq hl hε hU hR ha hp hz i

end ScaledGraph

/-- One arbitrary integer-cover chart; the index is not constrained to the
native band index. -/
noncomputable def commonGraph (Q h : ℝ) (i : ℕ) : ScaledGraph where
  radialScale := Q ^ (-(1 / 2 : ℝ))
  velocityScale := Q ^ (-CoordinateAlgebra.A h)
  epsilon := Q ^ h
  exponent := ChartScales.radialExponent h
  frequency := ChartScales.Lambda ^ i * Q ^ (ChartScales.radialExponent h / 2)
  fastCoefficient := ChartScales.Tg ^ i * Q ^ (1 + h)
  radialVector := PhysicalGraphBounds.radialDirection
  temporalVector := PhysicalGraphBounds.timeDirection

theorem commonGraph_scale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ) :
    (commonGraph Q h i).radialScale =
      (commonGraph Q h i).velocityScale * (commonGraph Q h i).epsilon := by
  change Q ^ (-(1 / 2 : ℝ)) = Q ^ (-CoordinateAlgebra.A h) * Q ^ h
  rw [← Real.rpow_add hQ]
  congr 1
  unfold CoordinateAlgebra.A
  ring

theorem commonGraph_axialScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ) :
    (commonGraph Q h i).radialScale * (commonGraph Q h i).epsilon =
      Q ^ (-CoordinateAlgebra.D h) := by
  change Q ^ (-(1 / 2 : ℝ)) * Q ^ h = Q ^ (-CoordinateAlgebra.D h)
  rw [← Real.rpow_add hQ]
  congr 1
  unfold CoordinateAlgebra.D
  ring

theorem commonGraph_slowTimeScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ) :
    (commonGraph Q h i).velocityScale * (commonGraph Q h i).radialScale *
      (commonGraph Q h i).epsilon = Q ^ (-1 : ℝ) := by
  change Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) * Q ^ h = Q ^ (-1 : ℝ)
  rw [← Real.rpow_add hQ, ← Real.rpow_add hQ]
  congr 1
  unfold CoordinateAlgebra.A
  ring

theorem commonGraph_fastTimeScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ) :
    (commonGraph Q h i).velocityScale * (commonGraph Q h i).radialScale *
      (commonGraph Q h i).fastCoefficient = ChartScales.Tg ^ i := by
  change Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) *
    (ChartScales.Tg ^ i * Q ^ (1 + h)) = _
  rw [show Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) *
      (ChartScales.Tg ^ i * Q ^ (1 + h)) =
      ChartScales.Tg ^ i * (Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) *
        Q ^ (1 + h)) by ring]
  rw [← Real.rpow_add hQ, ← Real.rpow_add hQ]
  have he : -CoordinateAlgebra.A h + -(1 / 2 : ℝ) + (1 + h) = 0 := by
    unfold CoordinateAlgebra.A
    ring
  rw [he, Real.rpow_zero, mul_one]

theorem commonGraph_radialScale {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r)
    (h : ℝ) (i : ℕ) :
    (commonGraph Q h i).frequency * ((commonGraph Q h i).radialScale * r) ^
      (commonGraph Q h i).exponent = ChartScales.Lambda ^ i * r ^ ChartScales.radialExponent h := by
  change (ChartScales.Lambda ^ i * Q ^ (ChartScales.radialExponent h / 2)) *
    (Q ^ (-(1 / 2 : ℝ)) * r) ^ ChartScales.radialExponent h = _
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hQ _).le hr.le,
    ← Real.rpow_mul hQ.le]
  rw [show (ChartScales.Lambda ^ i * Q ^ (ChartScales.radialExponent h / 2)) *
      (Q ^ (-(1 / 2 : ℝ) * ChartScales.radialExponent h) * r ^ ChartScales.radialExponent h) =
      ChartScales.Lambda ^ i *
        (Q ^ (ChartScales.radialExponent h / 2) *
          Q ^ (-(1 / 2 : ℝ) * ChartScales.radialExponent h)) *
        r ^ ChartScales.radialExponent h by ring]
  rw [← Real.rpow_add hQ,
    show ChartScales.radialExponent h / 2 + -(1 / 2 : ℝ) * ChartScales.radialExponent h = 0 by ring,
    Real.rpow_zero, mul_one]

theorem commonGraph_map {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ)
    {p : SpaceTime} (hr : 0 < p.2 0) :
    (commonGraph Q h i).map p =
      ((Q ^ (-(1 / 2 : ℝ)) * p.2 0,
        ((Q ^ (-CoordinateAlgebra.D h) * p.2 2, (1 - p.1) / Q),
          (SlotGeometry.cover ^ i)
            ((p.2 0) ^ ChartScales.radialExponent h • PhysicalGraphBounds.radialDirection +
              p.1 • PhysicalGraphBounds.timeDirection))), p.2 1) := by
  unfold ScaledGraph.map
  rw [commonGraph_axialScale hQ, commonGraph_slowTimeScale hQ,
    commonGraph_fastTimeScale hQ, commonGraph_radialScale hQ hr]
  simp only [map_add, map_smul, PhysicalGraphBounds.cover_pow_radialDirection,
    PhysicalGraphBounds.cover_pow_timeDirection, smul_smul, Real.rpow_neg_one]
  simp [commonGraph, div_eq_mul_inv, mul_comm]

theorem commonGraph_residualScale {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (i : ℕ) :
    Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
      ((commonGraph Q h i).velocityScale ^ 2 * (commonGraph Q h i).radialScale) = 1 := by
  change Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
    ((Q ^ (-CoordinateAlgebra.A h)) ^ 2 * Q ^ (-(1 / 2 : ℝ))) = 1
  rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ, ← Real.rpow_add hQ]
  convert! Real.rpow_zero Q using 1
  congr 1
  norm_num
  ring

/-- The exact power multiplying the physical viscosity-one residual. -/
theorem commonGraph_physical_residual {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {a : Cylinder → Fin 3 → ℝ} {p : Cylinder → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {t : ℝ} {q : Space}
    (hz : (t, q) ∈ (commonGraph Q h k).source U)
    {u : VelocityField} {P : PressureField}
    (hu : ContDiffAt ℝ 2 u (t, CylindricalResidual.chart q))
    (hP : DifferentiableAt ℝ P (t, CylindricalResidual.chart q))
    (hrep : (fun z : SpaceTime => u (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) ((commonGraph Q h k).velocity a z)))
    (hpRep : CylindricalResidual.pressurePullback P =ᶠ[𝓝 (t, q)]
      (commonGraph Q h k).pressure p) (i : Fin 3) :
    graphResidual (Q ^ h) ScaledGraph.radius (commonGraph Q h k).radial
      ScaledGraph.angular (commonGraph Q h k).axial (commonGraph Q h k).temporal
      a p ((commonGraph Q h k).map (t, q)) i =
      Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
        CylindricalResidual.frame (-(q 1))
          (navierStokesResidual u P t (CylindricalResidual.chart q)) i := by
  have he := (commonGraph Q h k).physical_residual (Real.rpow_pos_of_pos hQ _)
    (commonGraph_scale hQ h k) hU hR ha hp hz hu hP hrep hpRep i
  rw [he, ← mul_assoc, commonGraph_residualScale hQ, one_mul]
  rfl

/-! ## The actual linear-plus-quadratic correction expression -/

theorem twice_along_add {U : Set E} (hU : IsOpen U) {V : E → E}
    (hV : ContDiffOn ℝ ∞ V U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U) :
    along V (along V (fun y => f y + g y)) x =
      along V (along V f) x + along V (along V g) x := by
  have he : EqOn (along V (fun y => f y + g y))
      (fun y => along V f y + along V g y) U := by
    intro y hy
    exact along_add V ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [along_congr hU he hx]
  exact along_add V
    (((contDiffOn_along hU hV hf).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((contDiffOn_along hU hV hg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))

theorem laplacian_add {U : Set E} (hU : IsOpen U) (R : E → ℝ) {Vr Vθ Vz : E → E}
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (fun y => f y + g y) x =
      cylindricalLaplacian R Vr Vθ Vz f x + cylindricalLaplacian R Vr Vθ Vz g x := by
  simp only [cylindricalLaplacian, twice_along_add hU hr hf hg hx,
    twice_along_add hU hθ hf hg hx, twice_along_add hU hz hf hg hx,
    along_add Vr ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)), smul_eq_mul]
  ring

theorem graphResidual_add {U : Set E} (hU : IsOpen U) (ε : ℝ) (R : E → ℝ)
    {Vr Vθ Vz : E → E} (Vt : E → E)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {B a : E → Fin 3 → ℝ} {p₀ p : E → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp₀ : ContDiffOn ℝ ∞ p₀ U) (hp : ContDiffOn ℝ ∞ p U) {x : E} (hx : x ∈ U)
    (i : Fin 3) :
    graphResidual ε R Vr Vθ Vz Vt (fun y j => B y j + a y j) (fun y => p₀ y + p y) x i =
      graphResidual ε R Vr Vθ Vz Vt B p₀ x i +
      LinearWaveResidual.realComponentLinearResidual ε R Vr Vθ Vz Vt B a p x i +
      LinearWaveResidual.realTransport R Vr Vθ Vz a a x i := by
  have hfirst (V : E → E) (j : Fin 3) := along_add V
    (((hB j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((ha j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  have hLap (j : Fin 3) := laplacian_add hU R hr hθ hz (hB j) (ha j) hx
  have hP (V : E → E) := along_add V
    ((hp₀.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hp.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  fin_cases i <;>
    simp [graphResidual, LinearWaveResidual.realComponentLinearResidual,
      LinearWaveResidual.realTransport, LinearWaveResidual.realFrameLaplacian,
      LinearWaveResidual.realAngularGenerator, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, hfirst, hLap, hP] <;> ring

theorem transport_realLift (R : E → ℝ) (Vr Vθ Vz : E → E)
    {a : E → Fin 3 → ℝ} {x : E}
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a y j) x) (i : Fin 3) :
    (LinearWaveResidual.transport R Vr Vθ Vz (LinearWaveResidual.realLift a)
      (LinearWaveResidual.realLift a) x i).re =
      LinearWaveResidual.realTransport R Vr Vθ Vz a a x i := by
  have hD (V : E → E) (j : Fin 3) := along_ofReal V (ha j)
  fin_cases i <;>
    simp [LinearWaveResidual.transport, LinearWaveResidual.realTransport,
      LinearWaveResidual.realLift, angularGenerator, LinearWaveResidual.realAngularGenerator,
      hD, ← Complex.ofReal_div]

/-- Complex increment as an element of `ℝ`. -/
noncomputable def complexIncrement (ε : ℝ) (R : E → ℝ) (Vr Vθ Vz Vt : E → E)
    (B a : E → Fin 3 → ℝ) (p : E → ℝ) (x : E) (i : Fin 3) : ℝ :=
  (LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt (LinearWaveResidual.realLift B)
    (LinearWaveResidual.realLift a) (fun y => (p y : ℂ)) x i +
    LinearWaveResidual.transport R Vr Vθ Vz (LinearWaveResidual.realLift a)
      (LinearWaveResidual.realLift a) x i).re

theorem complexIncrement_eq {U : Set E} (hU : IsOpen U) (ε : ℝ) (R : E → ℝ)
    {Vr Vθ Vz : E → E} (Vt : E → E)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {B a : E → Fin 3 → ℝ} {p : E → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {x : E} (hx : x ∈ U) (i : Fin 3) :
    complexIncrement ε R Vr Vθ Vz Vt B a p x i =
      LinearWaveResidual.realComponentLinearResidual ε R Vr Vθ Vz Vt B a p x i +
        LinearWaveResidual.realTransport R Vr Vθ Vz a a x i := by
  have haC j : ContDiffOn ℝ ∞ (fun y => (a y j : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (ha j)
  have hpC : DifferentiableAt ℝ (fun y => (p y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((hp.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  have hl := congrFun (LinearWaveResidual.realMap_linearResidual Complex.reCLM ε R Vt
    hU hr hθ hz haC
    (fun j => ((hB j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hpC hx) i
  have ht := transport_realLift R Vr Vθ Vz
    (fun j => ((ha j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) i
  simp only [complexIncrement, Complex.add_re, ht]
  have h := congrArg
    (fun z : ℝ => z + LinearWaveResidual.realTransport R Vr Vθ Vz a a x i) hl
  simp only [add_left_inj] at h
  exact congrArg (fun z : ℝ => z + LinearWaveResidual.realTransport R Vr Vθ Vz a a x i) h

/-- The base equation supplies only the fixed base residual.  All linear,
quadratic, pressure, and viscous increment terms are derived above. -/
theorem fullResidual_eq_graph {U : Set E} (hU : IsOpen U) (ε : ℝ) (R : E → ℝ)
    {Vr Vθ Vz : E → E} (Vt : E → E)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {B a : E → Fin 3 → ℝ} {p₀ p : E → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp₀ : ContDiffOn ℝ ∞ p₀ U) (hp : ContDiffOn ℝ ∞ p U) {x : E} (hx : x ∈ U)
    (virtual error : Fin 3 → ℝ)
    (hbase : ∀ i, graphResidual ε R Vr Vθ Vz Vt B p₀ x i = virtual i + error i)
    (i : Fin 3) :
    complexIncrement ε R Vr Vθ Vz Vt B a p x i + virtual i + error i =
      graphResidual ε R Vr Vθ Vz Vt (fun y j => B y j + a y j)
        (fun y => p₀ y + p y) x i := by
  rw [complexIncrement_eq hU ε R Vt hr hθ hz hB ha hp hx,
    graphResidual_add hU ε R Vt hr hθ hz hB ha hp₀ hp hx, hbase]
  ring

/-- The absolute graph before choosing a band or an integer covering. -/
noncomputable def absoluteLift (h : ℝ) (p : SpaceTime) : Lift :=
  (p.2 0, ((p.2 2, 1 - p.1),
    (p.2 0) ^ ChartScales.radialExponent h • PhysicalGraphBounds.radialDirection +
      p.1 • PhysicalGraphBounds.timeDirection))

theorem commonGraph_eq_physicalToChart (h : ℝ) (n k : ℕ) {p : SpaceTime}
    (hr : 0 < p.2 0) :
    (commonGraph (ChartScales.Q n) h k).map p =
      (MeanChartCompatibility.physicalToChart h n k (absoluteLift h p), p.2 1) := by
  rw [commonGraph_map (ChartScales.Q_pos n) h k hr,
    MeanChartCompatibility.physicalToChart_apply,
    MeanChartCompatibility.coverMap_eq_coverPower, CommonCoverSolve.coverPower_apply]
  simp [absoluteLift, MeanChartCompatibility.chartScale, Real.rpow_neg_one,
    div_eq_mul_inv, mul_comm]

/-- Matching consists of the literal coefficient and direction data at one
band, with no assumption about a residual or a differential operator. -/
structure MatchesAt (o : MeanIncrementBounds.Operators Lift) (G : ScaledGraph) (n : ℕ) : Prop where
  epsilon : o.epsilon n = G.epsilon
  frequency : o.radialFrequency n = G.frequency
  fast : o.fastCoefficient n = G.fastCoefficient
  radius : o.radius = Prod.fst
  profile : o.radialProfile = fun x => GraphCalculus.radialSpeed G.exponent x.1
  eR : o.eR = (1, (0, 0))
  eZ : o.eZ = (0, ((1, 0), 0))
  eT : o.eT = (0, ((0, 1), 0))
  vR : o.vR = (0, (0, G.radialVector))
  vT : o.vT = (0, (0, G.temporalVector))

theorem matchesAt_graphOperators (r : CorrectionState.ReconstructionData)
    (epsilon fast : ℕ → ℝ) (G : ScaledGraph) (n : ℕ)
    (hε : epsilon n = G.epsilon) (hM : r.frequency n = G.frequency)
    (hc : fast n = G.fastCoefficient) (hd : r.exponent = G.exponent)
    (hv : r.radialDirection = G.radialVector) :
    MatchesAt (CorrectionState.graphOperators r epsilon fast
      (((1, 0) : Plane), (0 : Plane)) (((0, 1) : Plane), (0 : Plane)) G.temporalVector) G n := by
  constructor
  · exact hε
  · exact hM
  · exact hc
  · rfl
  · simp only [CorrectionState.graphOperators, hd, RadialPullback.radialJacobian,
      GraphCalculus.radialSpeed]
  · rfl
  · rfl
  · rfl
  · simp only [CorrectionState.graphOperators, hv]
  · rfl

theorem MatchesAt.radialDirection {c : CorrectionState.Context Lift} {G : ScaledGraph} {n : ℕ}
    (H : MatchesAt c.operators G n) : LiftedMeanResidual.radialDirection c n = G.radial := by
  funext x
  simp [LiftedMeanResidual.radialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.radialVector, H.eR, H.frequency, H.profile, H.vR,
    ScaledGraph.radial]
  rfl

theorem MatchesAt.axialDirection {c : CorrectionState.Context Lift} {G : ScaledGraph} {n : ℕ}
    (H : MatchesAt c.operators G n) : LiftedMeanResidual.axialDirection c n = G.axial := by
  funext x
  simp [LiftedMeanResidual.axialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.axialVector, H.epsilon, H.eZ, ScaledGraph.axial]

theorem MatchesAt.timeDirection {c : CorrectionState.Context Lift} {G : ScaledGraph} {n : ℕ}
    (H : MatchesAt c.operators G n) : LiftedMeanResidual.timeDirection c n = G.temporal := by
  funext x
  simp [LiftedMeanResidual.timeDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.temporalVector, H.epsilon, H.fast, H.vT, H.eT, ScaledGraph.temporal]

/-- Base components, given by `![c.base.radial n x.1, c.base.angular n x.1, c.base.axial n
x.1]`. -/
noncomputable def baseComponents (c : CorrectionState.Context Lift) (n : ℕ)
    (x : Cylinder) : Fin 3 → ℝ :=
  ![c.base.radial n x.1, c.base.angular n x.1, c.base.axial n x.1]

/-- Increment components, given by `![s.mean.radial n x.1 + s.oscillation n x 0, s.mean.angular
n x.1 + s.oscillation n x 1, s.mean.axial n x.1 + s.oscillation n x 2]`. -/
noncomputable def incrementComponents (s : CorrectionState.State Lift) (n : ℕ)
    (x : Cylinder) : Fin 3 → ℝ :=
  ![s.mean.radial n x.1 + s.oscillation n x 0,
    s.mean.angular n x.1 + s.oscillation n x 1,
    s.mean.axial n x.1 + s.oscillation n x 2]

theorem context_fullResidual_formula {c : CorrectionState.Context Lift}
    {G : ScaledGraph} {n : ℕ} (H : MatchesAt c.operators G n)
    (s : CorrectionState.State Lift) (x : Cylinder) (i : Fin 3) :
    LiftedMeanResidual.fullResidual c s n x i =
      complexIncrement G.epsilon ScaledGraph.radius G.radial ScaledGraph.angular G.axial G.temporal
        (baseComponents c n) (incrementComponents s n) (s.totalPressureIncrement n) x i +
        LiftedMeanResidual.virtualDivergence c n x i + s.errors.base n x i := by
  have hB : LiftedMeanResidual.complexBase c n =
      LinearWaveResidual.realLift (baseComponents c n) := by
    funext y j
    fin_cases j <;> rfl
  have ha : LiftedMeanResidual.complexPerturbation s n =
      LinearWaveResidual.realLift (incrementComponents s n) := by
    funext y j
    fin_cases j <;> rfl
  unfold LiftedMeanResidual.fullResidual LiftedMeanResidual.nonlinearResidual
  rw [H.epsilon, H.radialDirection, H.axialDirection, H.timeDirection, H.radius, hB, ha]
  rfl

/-- Exact total-field residual for the actual correction state.  The only
base premise is its independently verified fixed pressure/virtual-stress
equation, and the base error is included once. -/
theorem context_fullResidual_eq_graph {c : CorrectionState.Context Lift}
    {G : ScaledGraph} {n : ℕ} (H : MatchesAt c.operators G n)
    (s : CorrectionState.State Lift) {U : Set Cylinder}
    (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0) {p₀ : Cylinder → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun x => baseComponents c n x i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => incrementComponents s n x i) U)
    (hp₀ : ContDiffOn ℝ ∞ p₀ U) (hp : ContDiffOn ℝ ∞ (s.totalPressureIncrement n) U)
    {x : Cylinder} (hx : x ∈ U)
    (hbase : ∀ i, graphResidual G.epsilon ScaledGraph.radius G.radial ScaledGraph.angular
      G.axial G.temporal (baseComponents c n) p₀ x i =
        LiftedMeanResidual.virtualDivergence c n x i + s.errors.base n x i) (i : Fin 3) :
    LiftedMeanResidual.fullResidual c s n x i =
      graphResidual G.epsilon ScaledGraph.radius G.radial ScaledGraph.angular G.axial G.temporal
        (fun y j => baseComponents c n y j + incrementComponents s n y j)
        (fun y => p₀ y + s.totalPressureIncrement n y) x i := by
  rw [context_fullResidual_formula H]
  exact fullResidual_eq_graph hU G.epsilon ScaledGraph.radius G.temporal
    (G.radial_smooth hR) contDiffOn_const contDiffOn_const hB ha hp₀ hp hx _ _ hbase i

/-- The actual correction-state residual is the scaled Cartesian
Navier--Stokes residual on the physical graph.  The cover index `k` is free.
The base pressure is fixed separately because a correction state stores only
pressure increments. -/
theorem context_fullResidual_physical {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k n : ℕ)
    (c : CorrectionState.Context Lift) (s : CorrectionState.State Lift)
    (H : MatchesAt c.operators (commonGraph Q h k) n)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {p₀ : Cylinder → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun x => baseComponents c n x i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => incrementComponents s n x i) U)
    (hp₀ : ContDiffOn ℝ ∞ p₀ U) (hp : ContDiffOn ℝ ∞ (s.totalPressureIncrement n) U)
    {t : ℝ} {q : Space} (hz : (t, q) ∈ (commonGraph Q h k).source U)
    (hbase : ∀ i, graphResidual (Q ^ h) ScaledGraph.radius (commonGraph Q h k).radial
      ScaledGraph.angular (commonGraph Q h k).axial (commonGraph Q h k).temporal
      (baseComponents c n) p₀ ((commonGraph Q h k).map (t, q)) i =
        LiftedMeanResidual.virtualDivergence c n ((commonGraph Q h k).map (t, q)) i +
          s.errors.base n ((commonGraph Q h k).map (t, q)) i)
    {u : VelocityField} {P : PressureField}
    (hu : ContDiffAt ℝ 2 u (t, CylindricalResidual.chart q))
    (hP : DifferentiableAt ℝ P (t, CylindricalResidual.chart q))
    (hrep : (fun z : SpaceTime => u (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t, q)]
      (fun z => CylindricalResidual.frame (z.2 1) ((commonGraph Q h k).velocity
        (fun y j => baseComponents c n y j + incrementComponents s n y j) z)))
    (hpRep : CylindricalResidual.pressurePullback P =ᶠ[𝓝 (t, q)] (commonGraph Q h k).pressure
      (fun y => p₀ y + s.totalPressureIncrement n y)) (i : Fin 3) :
    LiftedMeanResidual.fullResidual c s n ((commonGraph Q h k).map (t, q)) i =
      Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
        CylindricalResidual.frame (-(q 1))
          (navierStokesResidual u P t (CylindricalResidual.chart q)) i := by
  rw [context_fullResidual_eq_graph H s hU hR hB ha hp₀ hp hz.2 hbase]
  exact commonGraph_physical_residual hQ h k hU hR (fun j => (hB j).add (ha j))
    (hp₀.add hp) hz hu hP hrep hpRep i

end

end NavierStokes.PhysicalResidualBridge
