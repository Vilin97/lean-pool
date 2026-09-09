/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonBaseContext
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopyAngularInvariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeStateCoherence

@[expose] public section

/-!
# The actual fixed-base residual in every common chart

Pressure and error are normalized values of the same final Cartesian base.
The equation is derived from its proved residual identity on the entire
free auxiliary lift, rather than only on a physical graph.
-/

noncomputable section

namespace NavierStokes.ActualBaseResidual

open Set Filter Function HarmonicCalculus PhysicalResidualBridge
open scoped ContDiff Topology BigOperators


section Pullback

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative calculation permits a non-unit source viscosity and a
non-injective coordinate map. This is used to keep every auxiliary value free. -/
theorem graphResidual_scaled_viscosity {Ω : Set E} {U : Set F} {Γ : E → F}
    {l v ε μ : ℝ} {R : F → ℝ} {Vr Vθ Vz Vt : F → F}
    {Sr Sθ Sz St : E → E} {r : E → ℝ}
    (G : PullbackData Ω U Γ l v R Vr Vθ Vz Vt Sr Sθ Sz St r)
    (hl : l ≠ 0) (hμ : μ = v * ε / l)
    {a : F → Fin 3 → ℝ} {p : F → ℝ}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) {x : E} (hx : x ∈ Ω) (hr : r x ≠ 0) (i : Fin 3) :
    graphResidual μ r Sr Sθ Sz St (fun y j => v * a (Γ y) j)
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
  rw [hμ]
  fin_cases i <;>
    simp only [graphResidual, LinearWaveResidual.realTransport,
      LinearWaveResidual.realFrameLaplacian, LinearWaveResidual.realAngularGenerator,
      cylindricalLaplacian, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
        Matrix.cons_val_one, hAr, hAθ, hAz, hAt, hArr, hAθθ, hAzz, hPr, hPθ, hPz,
      smul_eq_mul, G.radius x hx] <;>
    field_simp [hl, hr] ; ring


/-- The full residual depends only on germs, including its second derivatives. -/
theorem graphResidual_congr {U : Set E} (hU : IsOpen U) (ε : ℝ)
    (R : E → ℝ) (Vr Vθ Vz Vt : E → E) {a b : E → Fin 3 → ℝ} {p q : E → ℝ}
    (ha : ∀ j, EqOn (fun x => a x j) (fun x => b x j) U) (hp : EqOn p q U)
    {x : E} (hx : x ∈ U) (i : Fin 3) :
    graphResidual ε R Vr Vθ Vz Vt a p x i = graphResidual ε R Vr Vθ Vz Vt b q x i := by
  have hval : a x = b x := funext fun j => ha j hx
  have hfirst (V : E → E) (j : Fin 3) := along_congr (V := V) hU (ha j) hx
  have hsecond (V : E → E) (j : Fin 3) :=
    along_congr (V := V) hU (fun y hy => along_congr (V := V) hU (ha j) hy) hx
  have hpressure (V : E → E) := along_congr (V := V) hU hp hx
  fin_cases i <;> simp only [graphResidual, LinearWaveResidual.realTransport,
    LinearWaveResidual.realFrameLaplacian, LinearWaveResidual.realAngularGenerator,
    cylindricalLaplacian, Matrix.cons_val_zero, Matrix.cons_val_one,
    hval, hfirst, hsecond, hpressure]


end Pullback

abbrev Point := CommonBaseContext.Point
abbrev Full := Point × ℝ
abbrev Space := ProblemStatement.Space
abbrev SpaceTime := ProblemStatement.SpaceTime

/-- Translation invariance propagates through every derivative in the residual. -/
theorem graphResidual_invariant (θ : Full) (ε : ℝ) (R : Full → ℝ)
    (Vr Vθ Vz Vt : Full → Full) (a : Full → Fin 3 → ℝ) (p : Full → ℝ)
    (hR : CopyAngularInvariance.Invariant θ R)
    (hr : CopyAngularInvariance.Invariant θ Vr) (htheta : CopyAngularInvariance.Invariant θ Vθ)
    (hz : CopyAngularInvariance.Invariant θ Vz) (ht : CopyAngularInvariance.Invariant θ Vt)
    (ha : CopyAngularInvariance.Invariant θ a) (hp : CopyAngularInvariance.Invariant θ p)
    (i : Fin 3) :
    CopyAngularInvariance.Invariant θ (fun x => graphResidual ε R Vr Vθ Vz Vt a p x i) := by
  intro x t
  have hfirst (V : Full → Full) (hV : CopyAngularInvariance.Invariant θ V) (j : Fin 3) :=
    ((ha.component j).along hV) x t
  have hsecond (V : Full → Full) (hV : CopyAngularInvariance.Invariant θ V) (j : Fin 3) :=
    (((ha.component j).along hV).along hV) x t
  have hpressure (V : Full → Full) (hV : CopyAngularInvariance.Invariant θ V) := (hp.along hV) x t
  fin_cases i <;> simp only [graphResidual, LinearWaveResidual.realTransport,
    LinearWaveResidual.realFrameLaplacian, LinearWaveResidual.realAngularGenerator,
    cylindricalLaplacian, Matrix.cons_val_zero, Matrix.cons_val_one,
    hR x t, ha x t, hfirst Vr hr, hfirst Vθ htheta, hfirst Vz hz, hfirst Vt ht,
    hsecond Vr hr, hsecond Vθ htheta, hsecond Vz hz,
    hpressure Vr hr, hpressure Vθ htheta, hpressure Vz hz]


noncomputable def domain : Set Full := {x | 0 < x.1.1 ∧ 0 < x.1.2.1.1}

noncomputable def timeDomain : Set Full := {x | 0 < x.1.2.1.1}

theorem domain_open : IsOpen domain :=
  (isOpen_lt continuous_const continuous_fst.fst).inter
    (isOpen_lt continuous_const continuous_fst.snd.fst.fst)

theorem timeDomain_open : IsOpen timeDomain :=
  isOpen_lt continuous_const continuous_fst.snd.fst.fst

noncomputable def cylinderLinear (h Q : ℝ) : Full →L[ℝ] SpaceTime where
  toFun x := (-Q * x.1.2.1.1,
    AxisymmetricResidual.pack (Real.sqrt Q * x.1.1) x.2
      (Q ^ CoordinateAlgebra.D h * x.1.2.1.2))
  map_add' x y := by
    apply Prod.ext
    · change -Q * (x.1.2.1.1 + y.1.2.1.1) = -Q * x.1.2.1.1 + -Q * y.1.2.1.1
      ring
    · ext i
      fin_cases i <;> simp [AxisymmetricResidual.pack] <;> ring
  map_smul' c x := by
    apply Prod.ext
    · change -Q * (c * x.1.2.1.1) = c * (-Q * x.1.2.1.1)
      ring
    · ext i
      fin_cases i <;> simp [AxisymmetricResidual.pack] <;> ring
  cont := by
    apply Continuous.prodMk
    · exact continuous_const.mul continuous_fst.snd.fst.fst
    · exact (((continuous_const.mul continuous_fst.fst).smul continuous_const).add
        (continuous_snd.smul continuous_const)).add
          ((continuous_const.mul continuous_fst.snd.fst.snd).smul continuous_const)

noncomputable def cylinderPoint (h Q : ℝ) (x : Full) : SpaceTime :=
  (1 - Q * x.1.2.1.1, AxisymmetricResidual.pack (Real.sqrt Q * x.1.1) x.2
    (Q ^ CoordinateAlgebra.D h * x.1.2.1.2))

theorem cylinderPoint_eq (h Q : ℝ) (x : Full) :
    cylinderPoint h Q x = (1, 0) + cylinderLinear h Q x := by
  apply Prod.ext
  · change 1 - Q * x.1.2.1.1 = 1 + -Q * x.1.2.1.1
    ring
  · simp only [cylinderPoint, cylinderLinear, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add, zero_add]

theorem cylinderPoint_smooth (h Q : ℝ) : ContDiff ℝ ∞ (cylinderPoint h Q) := by
  have he : cylinderPoint h Q = fun x => (1, 0) + cylinderLinear h Q x :=
    funext (cylinderPoint_eq h Q)
  rw [he]
  exact contDiff_const.add (cylinderLinear h Q).contDiff

theorem cylinderPoint_hasFDerivAt (h Q : ℝ) (x : Full) :
    HasFDerivAt (cylinderPoint h Q) (cylinderLinear h Q) x := by
  have he : cylinderPoint h Q = fun x => (1, 0) + cylinderLinear h Q x :=
    funext (cylinderPoint_eq h Q)
  rw [he]
  exact (cylinderLinear h Q).hasFDerivAt.const_add (1, 0)

noncomputable def physicalPoint (h Q : ℝ) (x : Full) : SpaceTime :=
  ((cylinderPoint h Q x).1, CylindricalResidual.chart (cylinderPoint h Q x).2)

theorem physicalPoint_smooth (h Q : ℝ) : ContDiff ℝ ∞ (physicalPoint h Q) :=
  (cylinderPoint_smooth h Q).fst.prodMk
    (CylindricalResidual.contDiff_chart.comp (cylinderPoint_smooth h Q).snd)

theorem physicalPoint_time {h Q : ℝ} (hQ : 0 < Q) {x : Full}
    (hx : 0 < x.1.2.1.1) : (physicalPoint h Q x).1 < 1 := by
  change 1 - Q * x.1.2.1.1 < 1
  linarith [mul_pos hQ hx]

theorem profilePoint_chart (t : ℝ) (q : Space) :
    AxisymmetricFields.profilePoint t (CylindricalResidual.chart q) =
      (t, ((q 0) ^ 2 / 2, q 2)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [AxisymmetricFields.profilePoint, AxisymmetricFields.radialEnergy,
      CylindricalResidual.chart, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
    nlinarith [Real.cos_sq_add_sin_sq (q 1)]
  · simp only [AxisymmetricFields.profilePoint, CylindricalResidual.chart,
      AxisymmetricResidual.pack_two]

theorem physicalPoint_profile {h Q : ℝ} (hQ : 0 ≤ Q) (x : Full) :
    AxisymmetricFields.profilePoint (physicalPoint h Q x).1 (physicalPoint h Q x).2 =
      (1 - Q * x.1.2.1.1, (Q * x.1.1 ^ 2 / 2, Q ^ CoordinateAlgebra.D h * x.1.2.1.2)) := by
  rw [physicalPoint, profilePoint_chart]
  simp only [cylinderPoint, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_two,
    mul_pow, Real.sq_sqrt hQ]

theorem physicalPoint_zero_angle (h : ℝ) (n : ℕ) (x : Point) :
    physicalPoint h (ChartScales.Q n) (x, 0) = BaseContextAssembly.physicalPoint h n x := by
  apply Prod.ext
  · rfl
  ext i
  fin_cases i <;>
    simp [physicalPoint, cylinderPoint, CylindricalResidual.chart,
      BaseContextAssembly.physicalPoint, BaseChartJets.bandPoint,
      BaseContextAssembly.slowCoordinates]


/-- The elementary power identities used by the actual chart differential. -/
theorem scale_identities {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Q ^ CoordinateAlgebra.D h * Q ^ h = Real.sqrt Q ∧
    Q * Q ^ h = Q ^ CoordinateAlgebra.A h * Real.sqrt Q ∧
    Q ^ h = Q ^ CoordinateAlgebra.A h * 1 / Real.sqrt Q ∧
    (Q ^ CoordinateAlgebra.A h) ^ 2 * Real.sqrt Q =
      Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) := by
  rw [Real.sqrt_eq_rpow]
  have hadd (a b : ℝ) := (Real.rpow_add hQ a b).symm
  constructor
  · rw [hadd]
    congr 1
    simp [CoordinateAlgebra.D]
  constructor
  · nth_rw 1 [← Real.rpow_one Q]
    rw [hadd, hadd]
    congr 1
    simp [CoordinateAlgebra.A]
    ring
  constructor
  · rw [mul_one, ← Real.rpow_sub hQ]
    congr 1
    simp [CoordinateAlgebra.A]
  · rw [← Real.rpow_mul_natCast hQ.le, hadd]
    congr 1
    norm_num
    ring

/-- The cylinder pullback forgets the auxiliary coordinate. Its derivative
still matches all common-chart directions, whatever the common cover index. -/
theorem cylinderPullback {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k : ℕ) :
    PullbackData domain BaseResidual.past (cylinderPoint h Q)
      (Real.sqrt Q) (Q ^ CoordinateAlgebra.A h)
      LinearWaveResidual.coordinateRadius
      (LinearWaveResidual.spaceDirection 0) (LinearWaveResidual.spaceDirection 1)
      (LinearWaveResidual.spaceDirection 2) LinearWaveResidual.physicalTimeDirection
      (PhysicalResidualTZ.graphRadialTZ (commonGraph Q h k)) PhysicalResidualTZ.graphAngularTZ
      (PhysicalResidualTZ.graphAxialTZ (commonGraph Q h k))
      (PhysicalResidualTZ.graphTemporalTZ (commonGraph Q h k)) ScaledGraph.radius where
  source_open := domain_open
  target_open := BaseResidual.past_isOpen
  smooth := (cylinderPoint_smooth h Q).contDiffOn
  mapsTo := fun x hx => ⟨physicalPoint_time (h := h) hQ hx.2, Set.mem_univ _⟩
  radial_smooth := contDiff_const.contDiffOn
  angular_smooth := contDiff_const.contDiffOn
  axial_smooth := contDiff_const.contDiffOn
  radial := by
    intro x hx
    rw [(cylinderPoint_hasFDerivAt h Q x).fderiv]
    apply Prod.ext
    · simp [cylinderLinear, PhysicalResidualTZ.graphRadialTZ_eq, ScaledGraph.radial,
        LinearWaveResidual.spaceDirection]
    · ext i
      fin_cases i <;>
        simp [cylinderLinear, PhysicalResidualTZ.graphRadialTZ_eq, ScaledGraph.radial,
          LinearWaveResidual.spaceDirection, ProblemStatement.coordinateVector]
  angular := by
    intro x hx
    rw [(cylinderPoint_hasFDerivAt h Q x).fderiv]
    apply Prod.ext
    · simp [cylinderLinear, PhysicalResidualTZ.graphAngularTZ_eq, ScaledGraph.angular,
        LinearWaveResidual.spaceDirection]
    · ext i
      fin_cases i <;>
        simp [cylinderLinear, PhysicalResidualTZ.graphAngularTZ_eq, ScaledGraph.angular,
          LinearWaveResidual.spaceDirection, ProblemStatement.coordinateVector]
  axial := by
    intro x hx
    rw [(cylinderPoint_hasFDerivAt h Q x).fderiv]
    apply Prod.ext
    · simp [cylinderLinear, PhysicalResidualTZ.graphAxialTZ_apply,
        LinearWaveResidual.spaceDirection]
    · ext i
      fin_cases i <;>
        simp [cylinderLinear, PhysicalResidualTZ.graphAxialTZ_apply, commonGraph,
          LinearWaveResidual.spaceDirection, ProblemStatement.coordinateVector,
          (scale_identities hQ h).1]
  temporal := by
    intro x hx
    rw [(cylinderPoint_hasFDerivAt h Q x).fderiv]
    apply Prod.ext
    · simpa [cylinderLinear, PhysicalResidualTZ.graphTemporalTZ_apply, commonGraph,
        LinearWaveResidual.physicalTimeDirection] using (scale_identities hQ h).2.1
    · ext i
      fin_cases i <;>
        simp [cylinderLinear, PhysicalResidualTZ.graphTemporalTZ_apply,
          LinearWaveResidual.physicalTimeDirection]
  radius := by
    intro x hx
    simp [LinearWaveResidual.coordinateRadius, cylinderPoint, ScaledGraph.radius]


section CylindricalRegularity

noncomputable def cartesianCylinder (x : SpaceTime) : SpaceTime :=
  (x.1, CylindricalResidual.chart x.2)

theorem cartesianCylinder_smooth : ContDiff ℝ ∞ cartesianCylinder :=
  contDiff_fst.prodMk (CylindricalResidual.contDiff_chart.comp contDiff_snd)

theorem velocityComponents_smooth {u : ProblemStatement.VelocityField}
    (hu : ContDiffOn ℝ ∞ u BaseResidual.past) :
    ContDiffOn ℝ ∞ (CylindricalResidual.velocityComponents u) BaseResidual.past := by
  have hc := hu.comp cartesianCylinder_smooth.contDiffOn (fun _ hx => hx)
  have hangle : ContDiff ℝ ∞ (fun x : SpaceTime => -(x.2 1)) :=
    ((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).neg
  exact (CylindricalResidual.contDiff_frame.comp hangle).contDiffOn.clm_apply hc

theorem pressurePullback_smooth {p : ProblemStatement.PressureField}
    (hp : ContDiffOn ℝ ∞ p BaseResidual.past) :
    ContDiffOn ℝ ∞ (CylindricalResidual.pressurePullback p) BaseResidual.past :=
  hp.comp cartesianCylinder_smooth.contDiffOn (fun _ hx => hx)

end CylindricalRegularity

/-- Axisymmetry of the complete curl field, in cylindrical components. -/
theorem axisymmetric_components (b f u : AxisymmetricFields.Profile) (t : ℝ) (q : Space) :
    CylindricalResidual.frame (-(q 1))
      (AxisymmetricResidual.velocity b f u (t, CylindricalResidual.chart q)) =
    AxisymmetricResidual.velocity b f u (t, AxisymmetricResidual.pack (q 0) 0 (q 2)) := by
  have hp0 : AxisymmetricFields.profilePoint t (AxisymmetricResidual.pack (q 0) 0 (q 2)) =
      (t, ((q 0)^2 / 2, q 2)) := by
    simp [AxisymmetricFields.profilePoint, AxisymmetricFields.radialEnergy]
  simp only [AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
    AxisymmetricResidual.componentY, AxisymmetricResidual.lift, profilePoint_chart, hp0]
  rw [CylindricalResidual.frame_apply]
  ext i
  fin_cases i <;> simp [CylindricalResidual.chart, AxisymmetricResidual.pack,
    ProblemStatement.coordinateVector,
    Real.cos_neg, Real.sin_neg]
  · linear_combination -(q 0 * b (t, ((q 0)^2 / 2, q 2))) * Real.cos_sq_add_sin_sq (q 1)
  · linear_combination (q 0 * f (t, ((q 0)^2 / 2, q 2))) * Real.cos_sq_add_sin_sq (q 1)


noncomputable def profileAtScale (h Q : ℝ) (x : Point) : AxisymmetricFields.ProfilePoint :=
  (1 - Q * x.2.1.1, (Q * x.1 ^ 2 / 2, Q ^ CoordinateAlgebra.D h * x.2.1.2))

noncomputable def profileJacobian (h Q : ℝ) (x : Point) : Point →L[ℝ]
  AxisymmetricFields.ProfilePoint :=
  ((-Q) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _))).prod
  (((Q * x.1) • ContinuousLinearMap.fst ℝ ℝ _).prod
    ((Q ^ CoordinateAlgebra.D h) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ _))))

theorem profileJacobian_apply (h Q : ℝ) (x d : Point) :
    profileJacobian h Q x d =
      (-Q * d.2.1.1, (Q * x.1 * d.1, Q ^ CoordinateAlgebra.D h * d.2.1.2)) := rfl

theorem profileAtScale_hasFDerivAt (h Q : ℝ) (x : Point) :
    HasFDerivAt (profileAtScale h Q) (profileJacobian h Q x) x := by
  have hr := (hasFDerivAt_id (𝕜 := ℝ) x).fst
  have ht := (hasFDerivAt_id (𝕜 := ℝ) x).snd.fst.fst
  have hz := (hasFDerivAt_id (𝕜 := ℝ) x).snd.fst.snd
  have hd := ((ht.const_mul Q).const_sub 1).prodMk
    ((((hr.mul hr).const_mul Q).const_mul (1 / 2 : ℝ)).prodMk
      (hz.const_mul (Q ^ CoordinateAlgebra.D h)))
  convert! hd using 1
  · funext y
    apply Prod.ext
    · simp [profileAtScale]
    · simp [profileAtScale, pow_two]
      ring
  · ext
    all_goals simp [profileJacobian, smul_eq_mul]
    all_goals ring

/-- A direct derivative calculation for the normalized stress profile. -/
theorem normalized_profile_radialDiv
    (o : MeanIncrementBounds.Operators Point) (n : ℕ)
    (hR : o.radius = fun x => x.1) (heR : o.eR = (1, (0, 0)))
    {w : ℝ × ℝ} (hvR : o.vR = (0, (0, w)))
    {Q : ℝ} (hQ : 0 < Q) (h k : ℝ) (S : AxisymmetricFields.Profile)
    {x : Point} (hx : 0 < x.1)
    (hS : DifferentiableAt ℝ S (profileAtScale h Q x)) :
    o.radialDiv k (fun _ y => Q ^ (2 * CoordinateAlgebra.A h) * S (profileAtScale h Q y)) n x =
      Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
        LeadingStress.radialDivergence k S (profileAtScale h Q x) := by
  have hd := (hS.hasFDerivAt.comp x (profileAtScale_hasFDerivAt h Q x)).const_mul
    (Q ^ (2 * CoordinateAlgebra.A h))
  dsimp only [Function.comp_def] at hd
  have hzero : profileJacobian h Q x o.vR = 0 := by rw [hvR, profileJacobian_apply]; simp
  have hrad : profileJacobian h Q x o.eR = (Q * x.1) • (0, (1, 0)) := by
    rw [heR, profileJacobian_apply]
    simp
  have hsqrt : Real.sqrt (2 * (profileAtScale h Q x).2.1) = Real.sqrt Q * x.1 := by
    change Real.sqrt (2 * (Q * x.1 ^ 2 / 2)) = _
    rw [show 2 * (Q * x.1 ^ 2 / 2) = Q * x.1 ^ 2 by ring,
      Real.sqrt_mul hQ.le, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, hd.fderiv, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, hrad, hzero, map_zero, map_smul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, MeanIncrementBounds.Operators.invRadius,
    hR, smul_eq_mul, mul_zero, add_zero]
  have hpower : Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) =
      Q ^ (2 * CoordinateAlgebra.A h) * Real.sqrt Q := by
    rw [Real.rpow_add hQ, Real.sqrt_eq_rpow]
  rw [LeadingStress.radialDivergence, hsqrt, hpower]
  unfold SimilarityProfile.partialS
  field_simp [hx.ne', (Real.sqrt_pos.2 hQ).ne']
  ring_nf
  rw [Real.sq_sqrt hQ.le]
  ring

/-- Rotation of the actual Cartesian tangential stress force. -/
theorem tangentialStressForce_components (theta axial : AxisymmetricFields.Profile)
    (t : ℝ) (q : Space) (hr : 0 < q 0) :
    CylindricalResidual.frame (-(q 1))
      (SlowResidualMatching.tangentialStressForce theta axial t (CylindricalResidual.chart q)) =
      AxisymmetricResidual.pack 0
        (-LeadingStress.radialDivergence 2 theta (t, ((q 0)^2 / 2, q 2)))
        (-LeadingStress.radialDivergence 1 axial (t, ((q 0)^2 / 2, q 2))) := by
  have he : AxisymmetricFields.radialEnergy (CylindricalResidual.chart q) = (q 0)^2/2 :=
    congrArg (fun p : AxisymmetricFields.ProfilePoint => p.2.1) (profilePoint_chart t q)
  have hsqrt : Real.sqrt (2 * AxisymmetricFields.radialEnergy (CylindricalResidual.chart q)) = q 0
    := by
    rw [he, show 2 * ((q 0)^2 / 2) = (q 0)^2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hr]
  simp only [SlowResidualMatching.tangentialStressForce, hsqrt, profilePoint_chart]
  rw [CylindricalResidual.frame_apply]
  ext i
  fin_cases i <;> simp [CylindricalResidual.chart, AxisymmetricResidual.pack,
    ProblemStatement.coordinateVector,
    Real.cos_neg, Real.sin_neg]
  · field_simp [hr.ne']
    ring
  · field_simp [hr.ne']
    linear_combination -(LeadingStress.radialDivergence 2 theta (t, ((q 0)^2/2, q 2))) *
      Real.cos_sq_add_sin_sq (q 1)


/-- Exact cancellation of a positive band ratio, at every real exponent. -/
theorem band_power_product (n m : ℕ) (a : ℝ) :
    ChartScales.Q m ^ a * (ChartScales.Q n / ChartScales.Q m) ^ a = ChartScales.Q n ^ a := by
  rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos m) a).ne']

theorem cylinderPoint_bandChart (h : ℝ) (n m k : ℕ) (x : Point) (theta : ℝ) :
    cylinderPoint h (ChartScales.Q m) (GaugeStateCoherence.bandChartEquiv h n m k x, theta) =
      cylinderPoint h (ChartScales.Q n) (x, theta) := by
  simp only [cylinderPoint, GaugeStateCoherence.bandChartEquiv_apply,
    GaugeStateCoherence.bandSlowEquiv_apply, GaugeStateCoherence.bandScale]
  apply Prod.ext
  · field_simp [(ChartScales.Q_pos m).ne']
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [AxisymmetricResidual.pack, ProblemStatement.coordinateVector]
    · rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← mul_assoc]
      norm_num only [one_div] at ⊢
      rw [band_power_product]
    · rw [← mul_assoc, band_power_product]

theorem physicalPoint_bandChart (h : ℝ) (n m k : ℕ) (x : Point) (theta : ℝ) :
    physicalPoint h (ChartScales.Q m) (GaugeStateCoherence.bandChartEquiv h n m k x, theta) =
      physicalPoint h (ChartScales.Q n) (x, theta) := by
  simp only [physicalPoint, cylinderPoint_bandChart]

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W)
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
  (upper : ℝ) (B : ℕ)

/-- The normalized pressure of the actual summed base, at arbitrary positive scale. -/
noncomputable def pressureAtScale (Q : ℝ) (x : Full) : ℝ :=
  Q ^ (2 * CoordinateAlgebra.A F.data.h) *
    FinalSlowBase.pressure H v upper B (physicalPoint F.data.h Q x)

/-- The normalized Cartesian error, expressed in the cylindrical frame. -/
noncomputable def errorAtScale (Q : ℝ) (x : Full) : Fin 3 → ℝ := fun i =>
  Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
    CylindricalResidual.frame (-x.2)
      (FinalSlowBase.error H v upper B (physicalPoint F.data.h Q x)) i

noncomputable def velocityAtScale (Q : ℝ) (x : Full) : Fin 3 → ℝ := fun i =>
  Q ^ CoordinateAlgebra.A F.data.h *
    CylindricalResidual.frame (-x.2)
      (FinalSlowBase.velocity H v upper B (physicalPoint F.data.h Q x)) i

noncomputable def stressAtScale (Q : ℝ) (x : Full) : Fin 3 → ℝ := fun i =>
  Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
    CylindricalResidual.frame (-x.2)
      (FinalSlowBase.stressForce H v upper B (physicalPoint F.data.h Q x)) i

noncomputable def basePressure (n : ℕ) : Full → ℝ :=
  pressureAtScale H v upper B (ChartScales.Q n)

noncomputable def baseError (n : ℕ) : Full → Fin 3 → ℝ :=
  errorAtScale H v upper B (ChartScales.Q n)

theorem pressureAtScale_smooth {Q : ℝ} (hQ : 0 < Q) :
    ContDiffOn ℝ ∞ (pressureAtScale H v upper B Q) timeDomain :=
  contDiffOn_const.mul ((FinalSlowBase.pressure_smooth H v upper B).comp
    (physicalPoint_smooth F.data.h Q).contDiffOn (fun _ hx => ⟨physicalPoint_time (h := F.data.h)
      hQ hx, Set.mem_univ _⟩))

theorem errorAtScale_smooth {Q : ℝ} (hQ : 0 < Q) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => errorAtScale H v upper B Q x i) timeDomain := by
  have he := (FinalSlowBase.error_smooth H v upper B).comp
    (physicalPoint_smooth F.data.h Q).contDiffOn (fun _ hx => ⟨physicalPoint_time (h := F.data.h)
      hQ hx, Set.mem_univ _⟩)
  have hr := (CylindricalResidual.contDiff_frame.comp contDiff_snd.neg).contDiffOn.clm_apply he
  exact contDiffOn_const.mul ((AxisymmetricFields.projection i).contDiff.comp_contDiffOn hr)

theorem basePressure_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (basePressure H v upper B n) timeDomain :=
  pressureAtScale_smooth H v upper B (ChartScales.Q_pos n)

theorem baseError_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => baseError H v upper B n x i) timeDomain :=
  errorAtScale_smooth H v upper B (ChartScales.Q_pos n) i

/-- The actual base PDE after anisotropic scaling. No auxiliary point is
restricted to the image of a physical graph. -/
theorem scaled_residual {Q : ℝ} (hQ : 0 < Q) (k : ℕ) {x : Full} (hx : x ∈ domain)
    (i : Fin 3) :
    graphResidual (Q ^ F.data.h) ScaledGraph.radius
      (PhysicalResidualTZ.graphRadialTZ (commonGraph Q F.data.h k))
      PhysicalResidualTZ.graphAngularTZ
      (PhysicalResidualTZ.graphAxialTZ (commonGraph Q F.data.h k))
      (PhysicalResidualTZ.graphTemporalTZ (commonGraph Q F.data.h k))
      (velocityAtScale H v upper B Q) (pressureAtScale H v upper B Q) x i =
      stressAtScale H v upper B Q x i + errorAtScale H v upper B Q x i := by
  have hu := velocityComponents_smooth (FinalSlowBase.velocity_smooth H v upper B)
  have hp := pressurePullback_smooth (FinalSlowBase.pressure_smooth H v upper B)
  have huc (j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => CylindricalResidual.velocityComponents (FinalSlowBase.velocity H v upper B) y j)
      BaseResidual.past := (AxisymmetricFields.projection j).contDiff.comp_contDiffOn hu
  have hscale := graphResidual_scaled_viscosity (cylinderPullback hQ F.data.h k)
    (Real.sqrt_pos.2 hQ).ne' (scale_identities hQ F.data.h).2.2.1 huc hp hx hx.1.ne' i
  have hpow : (Q ^ CoordinateAlgebra.A F.data.h) ^ 2 =
      Q ^ (2 * CoordinateAlgebra.A F.data.h) := by
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 1
    norm_num
    ring
  have hfun : (fun y j => Q ^ CoordinateAlgebra.A F.data.h *
      CylindricalResidual.velocityComponents (FinalSlowBase.velocity H v upper B)
        (cylinderPoint F.data.h Q y) j) = velocityAtScale H v upper B Q := by
    funext y j
    simp only [velocityAtScale, CylindricalResidual.velocityComponents,
      CylindricalResidual.components, cylinderPoint, AxisymmetricResidual.pack_one, physicalPoint]
  have hpfun : (fun y => (Q ^ CoordinateAlgebra.A F.data.h) ^ 2 *
      CylindricalResidual.pressurePullback (FinalSlowBase.pressure H v upper B)
        (cylinderPoint F.data.h Q y)) = pressureAtScale H v upper B Q := by
    funext y
    rw [hpow]
    rfl
  rw [hfun, hpfun, (scale_identities hQ F.data.h).2.2.2] at hscale
  rw [hscale]
  have htarget : cylinderPoint F.data.h Q x ∈ BaseResidual.past := ⟨physicalPoint_time (h :=
    F.data.h) hQ hx.2, Set.mem_univ _⟩
  erw [congrFun (graphResidual_eq_cylindrical BaseResidual.past_isOpen hu hp htarget) i]
  have huv := (FinalSlowBase.velocity_smooth H v upper B).contDiffAt
    (BaseResidual.past_isOpen.mem_nhds
      ⟨physicalPoint_time (h := F.data.h) hQ hx.2, Set.mem_univ _⟩)
  have hpv := (FinalSlowBase.pressure_smooth H v upper B).contDiffAt
    (BaseResidual.past_isOpen.mem_nhds
      ⟨physicalPoint_time (h := F.data.h) hQ hx.2, Set.mem_univ _⟩)
  have hr : 0 < (cylinderPoint F.data.h Q x).2 0 := by
    simpa only [cylinderPoint, AxisymmetricResidual.pack_zero] using
      mul_pos (Real.sqrt_pos.2 hQ) hx.1
  have hns := CylindricalResidual.navierStokesResidual_cylindrical
    (huv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hpv.differentiableAt (by simp)) hr
  have hf := congrArg (CylindricalResidual.frame (-x.2)) hns
  simp only [cylinderPoint, AxisymmetricResidual.pack_one,
    CylindricalResidual.frame_inverse] at hf
  rw [← congrArg (fun z : Space => z i) hf]
  erw [FinalSlowBase.residual_identity H v upper B (physicalPoint F.data.h Q x)]
  simp only [stressAtScale, errorAtScale, map_add, PiLp.add_apply]
  ring

/-- Cylindrical components of the actual summed velocity equal its values on
the zero-angle ray. This uses its defining curl, including every slow order. -/
theorem actual_velocity_components {t : ℝ} (ht : t < 1) (q : Space) :
    CylindricalResidual.frame (-(q 1))
      (FinalSlowBase.velocity H v upper B (t, CylindricalResidual.chart q)) =
    FinalSlowBase.velocity H v upper B (t, AxisymmetricResidual.pack (q 0) 0 (q 2)) := by
  let a := FinalSlowBase.scales H v upper B
  let d := FinalSlowBase.coefficients H v
  have hh := F.data.h_pos
  have hh1 := F.data.h_lt_half
  have ha := FinalSlowBase.scales_strictMono H v upper B
  have hd := FinalSlowBase.coefficients_smooth H v
  have hH (z : Space) : DifferentiableAt ℝ
      (SlowBorelBase.streamFactor a F.data.h W.axis.normalization d)
      (AxisymmetricFields.profilePoint t z) :=
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
      (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 0)
      (-CoordinateAlgebra.A F.data.h) ht).differentiableAt (by simp)
  have hK (z : Space) : DifferentiableAt ℝ
      (SlowBorelBase.swirlPotential a F.data.h W.axis.normalization d)
      (AxisymmetricFields.profilePoint t z) :=
    (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
      (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 1)
      (1 / 2 - CoordinateAlgebra.A F.data.h) ht).differentiableAt (by simp)
  change CylindricalResidual.frame (-(q 1))
      (AxisymmetricFields.velocity _ _ (t, CylindricalResidual.chart q)) =
    AxisymmetricFields.velocity _ _ (t, AxisymmetricResidual.pack (q 0) 0 (q 2))
  rw [AxisymmetricResidual.velocity_from_potential_at _ _ _ _ (hH _) (hK _),
    AxisymmetricResidual.velocity_from_potential_at _ _ _ _ (hH _) (hK _)]
  exact axisymmetric_components _ _ _ _ _

/-- The directly normalized velocity is exactly the fixed base stored by
`CommonBaseContext`; the common cover index affects only derivative directions. -/
theorem velocityAtScale_eq_baseComponents (index : ℕ → ℕ) (n : ℕ) {x : Full}
    (hx : x ∈ domain) :
    velocityAtScale H v upper B (ChartScales.Q n) x =
      baseComponents (CommonBaseContext.context H v upper B index) n x := by
  have ht := physicalPoint_time (h := F.data.h) (ChartScales.Q_pos n) hx.2
  have hc := actual_velocity_components H v upper B ht
    (cylinderPoint F.data.h (ChartScales.Q n) x).2
  have hp : ((cylinderPoint F.data.h (ChartScales.Q n) x).1,
      AxisymmetricResidual.pack ((cylinderPoint F.data.h (ChartScales.Q n) x).2 0) 0
        ((cylinderPoint F.data.h (ChartScales.Q n) x).2 2)) =
      BaseContextAssembly.physicalPoint F.data.h n x.1 := by
    simpa [physicalPoint, cylinderPoint, CylindricalResidual.chart] using
      physicalPoint_zero_angle F.data.h n x.1
  erw [hp] at hc
  simp only [cylinderPoint, AxisymmetricResidual.pack_one] at hc
  change CylindricalResidual.frame (-x.2)
      (FinalSlowBase.velocity H v upper B (physicalPoint F.data.h (ChartScales.Q n) x)) = _ at hc
  ext i
  fin_cases i <;>
    simp only [velocityAtScale, hc, baseComponents]
  · exact (CommonBaseContext.context_radial_physical H v upper B index n x.1).symm
  · exact (CommonBaseContext.context_angular_physical H v upper B index n hx.2 hx.1).symm
  · exact (CommonBaseContext.context_axial_physical H v upper B index n hx.2).symm


theorem profileAtScale_eq_physicalProfile (n : ℕ) (x : Point) :
    AxisymmetricFields.profilePoint (BaseContextAssembly.physicalPoint F.data.h n x).1
      (BaseContextAssembly.physicalPoint F.data.h n x).2 =
      profileAtScale F.data.h (ChartScales.Q n) x := by
  rw [← physicalPoint_zero_angle F.data.h n x]
  exact physicalPoint_profile (ChartScales.Q_pos n).le (x, 0)

theorem virtualTheta_eq (index : ℕ → ℕ) (n : ℕ) {x : Point} (hx : 0 < x.1) :
    (CommonBaseContext.context H v upper B index).virtualTheta n x =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) *
        SlowBorelBase.baseStressTheta (FinalSlowBase.scales H v upper B)
          F.data.h W.axis.normalization (FinalSlowBase.coefficients H v)
            (profileAtScale F.data.h (ChartScales.Q n) x) := by
  change (BaseContextAssembly.virtualStress H v upper B n x).1 = _
  rw [BaseContextAssembly.virtualStress_eq_raw H v upper B n hx]
  change ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) * _ = _
  rw [profileAtScale_eq_physicalProfile (F := F) n x]

theorem virtualAxial_eq (index : ℕ → ℕ) (n : ℕ) {x : Point} (hx : 0 < x.1) :
    (CommonBaseContext.context H v upper B index).virtualAxial n x =
      ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) *
        SlowBorelBase.baseStressAxial (FinalSlowBase.scales H v upper B)
          F.data.h W.axis.normalization (FinalSlowBase.coefficients H v)
            (profileAtScale F.data.h (ChartScales.Q n) x) := by
  change (BaseContextAssembly.virtualStress H v upper B n x).2 = _
  rw [BaseContextAssembly.virtualStress_eq_raw H v upper B n hx]
  change ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h) * _ = _
  rw [profileAtScale_eq_physicalProfile (F := F) n x]

/-- Equality of genuine germs transports both pieces of the radial operator. -/
theorem radialDiv_germ_eq (o : MeanIncrementBounds.Operators Point) (k : ℝ)
    {f g : MeanIncrementBounds.Field Point} {n : ℕ} {x : Point}
    (he : f n =ᶠ[𝓝 x] g n) : o.radialDiv k f n x = o.radialDiv k g n x := by
  simp only [MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.dr,
    WeightedClasses.graphDerivative, Pi.add_apply, Pi.smul_apply, Pi.mul_apply]
  rw [he.fderiv_eq, he.self_of_nhds]

/-- The scaled physical stress force is exactly the fixed context's virtual
radial divergence, including its connection terms. -/
theorem stressAtScale_eq_virtualDivergence (index : ℕ → ℕ) (n : ℕ) {x : Full}
    (hx : x ∈ domain) :
    stressAtScale H v upper B (ChartScales.Q n) x =
      LiftedMeanResidual.virtualDivergence (CommonBaseContext.context H v upper B index) n x := by
  let c := CommonBaseContext.context H v upper B index
  let Q := ChartScales.Q n
  let Sθ := SlowBorelBase.baseStressTheta (FinalSlowBase.scales H v upper B)
    F.data.h W.axis.normalization (FinalSlowBase.coefficients H v)
  let Sz := SlowBorelBase.baseStressAxial (FinalSlowBase.scales H v upper B)
    F.data.h W.axis.normalization (FinalSlowBase.coefficients H v)
  have ht : (profileAtScale F.data.h Q x.1).1 < 1 :=
    physicalPoint_time (h := F.data.h) (ChartScales.Q_pos n) hx.2
  have hθ : DifferentiableAt ℝ Sθ (profileAtScale F.data.h Q x.1) :=
    (SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper B)
      F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
        (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 3)
      (-CoordinateAlgebra.A F.data.h - 1 / 2) ht).differentiableAt (by simp)
  have hz : DifferentiableAt ℝ Sz (profileAtScale F.data.h Q x.1) :=
    (SlowBorelBase.physicalProfile_smoothAt (FinalSlowBase.scales_strictMono H v upper B)
      F.data.h_pos F.data.h_lt_half (SlowBorelBase.bundleComponent_smooth
        (FinalSlowBase.coefficients_smooth H v) W.axis.normalization 4)
      (-CoordinateAlgebra.A F.data.h - 1 / 2) ht).differentiableAt (by simp)
  have hθeq : c.virtualTheta n =ᶠ[𝓝 x.1]
      (fun y => Q ^ (2 * CoordinateAlgebra.A F.data.h) * Sθ (profileAtScale F.data.h Q y)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst : Continuous (fun y : Point =>
      y.1))).mem_nhds hx.1] with y hy
    exact virtualTheta_eq H v upper B index n hy
  have hzeq : c.virtualAxial n =ᶠ[𝓝 x.1]
      (fun y => Q ^ (2 * CoordinateAlgebra.A F.data.h) * Sz (profileAtScale F.data.h Q y)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst : Continuous (fun y : Point =>
      y.1))).mem_nhds hx.1] with y hy
    exact virtualAxial_eq H v upper B index n hy
  have hθdiv := normalized_profile_radialDiv c.operators n rfl rfl
    (w := TorusInverse.vector .radial) rfl (ChartScales.Q_pos n) F.data.h 2 Sθ hx.1 hθ
  have hzdiv := normalized_profile_radialDiv c.operators n rfl rfl
    (w := TorusInverse.vector .radial) rfl (ChartScales.Q_pos n) F.data.h 1 Sz hx.1 hz
  have hdcθ : c.operators.radialDiv 2 c.virtualTheta n x.1 =
      Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
        LeadingStress.radialDivergence 2 Sθ (profileAtScale F.data.h Q x.1) :=
    (radialDiv_germ_eq c.operators 2 hθeq).trans hθdiv
  have hdcz : c.operators.radialDiv 1 c.virtualAxial n x.1 =
      Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
        LeadingStress.radialDivergence 1 Sz (profileAtScale F.data.h Q x.1) :=
    (radialDiv_germ_eq c.operators 1 hzeq).trans hzdiv
  have hr : 0 < (cylinderPoint F.data.h Q x).2 0 := by
    simpa only [cylinderPoint, AxisymmetricResidual.pack_zero] using
      mul_pos (Real.sqrt_pos.2 (ChartScales.Q_pos n)) hx.1
  have hs := tangentialStressForce_components Sθ Sz (cylinderPoint F.data.h Q x).1
    (cylinderPoint F.data.h Q x).2 hr
  have hp : ((cylinderPoint F.data.h Q x).1,
      (((cylinderPoint F.data.h Q x).2 0)^2/2, (cylinderPoint F.data.h Q x).2 2)) =
      profileAtScale F.data.h Q x.1 := by
    simp only [cylinderPoint, profileAtScale, AxisymmetricResidual.pack_zero,
      AxisymmetricResidual.pack_two, mul_pow, Real.sq_sqrt (show 0 ≤ Q from (ChartScales.Q_pos
        n).le)]
  rw [hp] at hs
  simp only [cylinderPoint, AxisymmetricResidual.pack_one] at hs
  ext i
  change Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
    (CylindricalResidual.frame (-x.2)
      (SlowResidualMatching.tangentialStressForce Sθ Sz (cylinderPoint F.data.h Q x).1
        (CylindricalResidual.chart (cylinderPoint F.data.h Q x).2))) i = _
  erw [hs]
  change Q ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) * _ =
    LiftedMeanResidual.virtualDivergence c n x i
  fin_cases i <;>
    simp only [LiftedMeanResidual.virtualDivergence, hdcθ, hdcz] <;>
    simp [AxisymmetricResidual.pack, ProblemStatement.coordinateVector]


theorem velocityAtScale_smooth {Q : ℝ} (hQ : 0 < Q) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => velocityAtScale H v upper B Q x i) timeDomain := by
  have hu := (FinalSlowBase.velocity_smooth H v upper B).comp
    (physicalPoint_smooth F.data.h Q).contDiffOn
      (fun _ hx => ⟨physicalPoint_time (h := F.data.h) hQ hx, Set.mem_univ _⟩)
  have hr := (CylindricalResidual.contDiff_frame.comp contDiff_snd.neg).contDiffOn.clm_apply hu
  exact contDiffOn_const.mul ((AxisymmetricFields.projection i).contDiff.comp_contDiffOn hr)

theorem baseComponents_smooth (index : ℕ → ℕ) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => baseComponents (CommonBaseContext.context H v upper B index) n x i)
      domain := by
  have hu := (velocityAtScale_smooth H v upper B (ChartScales.Q_pos n) i).mono
    (show domain ⊆ timeDomain from fun _ hx => hx.2)
  apply hu.congr
  intro x hx
  exact (congrFun (velocityAtScale_eq_baseComponents H v upper B index n hx) i).symm

/-- The fixed-base equation required by initialization, on the entire free
lift. It is derived from `FinalSlowBase.residual_identity`. -/
theorem fixed_base_residual (index : ℕ → ℕ) (n : ℕ) {x : Full} (hx : x ∈ domain) (i : Fin 3) :
    graphResidual (ChartScales.Q n ^ F.data.h) ScaledGraph.radius
      (PhysicalResidualTZ.graphRadialTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
      PhysicalResidualTZ.graphAngularTZ
      (PhysicalResidualTZ.graphAxialTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
      (PhysicalResidualTZ.graphTemporalTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
      (baseComponents (CommonBaseContext.context H v upper B index) n)
      (basePressure H v upper B n) x i =
      LiftedMeanResidual.virtualDivergence (CommonBaseContext.context H v upper B index) n x i +
        baseError H v upper B n x i := by
  have he := graphResidual_congr domain_open (ChartScales.Q n ^ F.data.h) ScaledGraph.radius
    (PhysicalResidualTZ.graphRadialTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
    PhysicalResidualTZ.graphAngularTZ
    (PhysicalResidualTZ.graphAxialTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
    (PhysicalResidualTZ.graphTemporalTZ (commonGraph (ChartScales.Q n) F.data.h (index n)))
    (fun j y hy => congrFun (velocityAtScale_eq_baseComponents H v upper B index n hy) j)
    (show EqOn (pressureAtScale H v upper B (ChartScales.Q n)) (basePressure H v upper B n) domain
      from fun _ _ => rfl) hx i
  rw [← he, scaled_residual H v upper B (ChartScales.Q_pos n) (index n) hx,
    stressAtScale_eq_virtualDivergence H v upper B index n hx]
  rfl

theorem pressureAtScale_angle_eq (Q : ℝ) (x : Point) (theta : ℝ) :
    pressureAtScale H v upper B Q (x, theta) = pressureAtScale H v upper B Q (x, 0) := by
  unfold pressureAtScale FinalSlowBase.pressure SlowBorelBase.basePressure
  simp only [physicalPoint, profilePoint_chart, cylinderPoint, AxisymmetricResidual.pack_zero,
    AxisymmetricResidual.pack_two]

theorem basePressure_angle_eq (n : ℕ) (x : Point) (theta : ℝ) :
    basePressure H v upper B n (x, theta) = basePressure H v upper B n (x, 0) :=
  pressureAtScale_angle_eq H v upper B _ x theta

theorem baseError_angular_continuous (n : ℕ) {x : Point} (hx : 0 < x.2.1.1) (i : Fin 3) :
    Continuous (fun theta => baseError H v upper B n (x, theta) i) := by
  apply continuous_iff_continuousAt.mpr
  intro theta
  exact ((baseError_smooth H v upper B n i).contDiffAt
    (timeDomain_open.mem_nhds hx)).continuousAt.comp (continuous_const.prodMk
      continuous_id).continuousAt


/-- The pressure stored separately from the correction's pressure increment. -/
noncomputable def fixedPressure (n : ℕ) (x : Point) : ℝ := basePressure H v upper B n (x, 0)

theorem basePressure_eq_fixedPressure (n : ℕ) (x : Full) :
    basePressure H v upper B n x = fixedPressure H v upper B n x.1 :=
  basePressure_angle_eq H v upper B n x.1 x.2

/-- Full band transition. The auxiliary cover is arbitrary because this is
the same physical base field on every free lift. -/
theorem basePressure_band (n m k : ℕ) (x : Point) (theta : ℝ) :
    basePressure H v upper B n (x, theta) =
      (ChartScales.Q n / ChartScales.Q m) ^ (2 * CoordinateAlgebra.A F.data.h) *
        basePressure H v upper B m (GaugeStateCoherence.bandChartEquiv F.data.h n m k x, theta) :=
          by
  simp only [basePressure, pressureAtScale, physicalPoint_bandChart]
  rw [← mul_assoc, mul_comm ((ChartScales.Q n / ChartScales.Q m) ^ _) (ChartScales.Q m ^ _),
    band_power_product]

theorem baseError_band (n m k : ℕ) (x : Point) (theta : ℝ) (i : Fin 3) :
    baseError H v upper B n (x, theta) i =
      (ChartScales.Q n / ChartScales.Q m) ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) *
        baseError H v upper B m (GaugeStateCoherence.bandChartEquiv F.data.h n m k x, theta) i := by
  simp only [baseError, errorAtScale, physicalPoint_bandChart]
  rw [← mul_assoc, mul_comm ((ChartScales.Q n / ChartScales.Q m) ^ _) (ChartScales.Q m ^ _),
    band_power_product]

noncomputable def errorState : CorrectionState.State Point where
  mean := ⟨0, 0, 0⟩
  pressure := 0
  oscillation := 0
  oscillatoryPressure := 0
  errors := ⟨baseError H v upper B, 0, 0⟩

/-- The genuine excluded base error satisfies the full free-lift state law,
with constants dictated by the physical scaling. -/
theorem errorState_band (U : Set Point) (n m k : ℕ) :
    PhysicalResidualNaturality.StateOn U (GaugeStateCoherence.bandChartEquiv F.data.h n m k)
      (GaugeStateCoherence.bandVelocityScale F.data.h n m) (GaugeStateCoherence.bandScale n m)
      (errorState H v upper B) (errorState H v upper B) n m := by
  have hp : GaugeStateCoherence.bandVelocityScale F.data.h n m *
      GaugeStateCoherence.bandVelocityScale F.data.h n m * GaugeStateCoherence.bandScale n m =
      (ChartScales.Q n / ChartScales.Q m) ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) := by
    unfold GaugeStateCoherence.bandVelocityScale GaugeStateCoherence.bandScale
    rw [← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)),
      ← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
    congr 1
    ring
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx theta i; simp [errorState]
  · intro x hx theta; simp [errorState]
  · intro x hx theta i
    simpa only [errorState, hp] using baseError_band H v upper B n m k x theta i
  · intro x hx theta i; simp [errorState]
  · intro x hx theta i; simp [errorState]

theorem fixedPressure_band (U : Set Point) (n m k : ℕ) :
    PhysicalResidualNaturality.ScalarOn U (GaugeStateCoherence.bandChartEquiv F.data.h n m k)
      (GaugeStateCoherence.bandVelocityScale F.data.h n m *
        GaugeStateCoherence.bandVelocityScale F.data.h n m)
      (fixedPressure H v upper B n) (fixedPressure H v upper B m) := by
  intro x hx
  have hp : GaugeStateCoherence.bandVelocityScale F.data.h n m *
      GaugeStateCoherence.bandVelocityScale F.data.h n m =
      (ChartScales.Q n / ChartScales.Q m) ^ (2 * CoordinateAlgebra.A F.data.h) := by
    unfold GaugeStateCoherence.bandVelocityScale
    rw [← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
    congr 1
    ring
  simpa only [fixedPressure, hp] using basePressure_band H v upper B n m k x 0


/-- The actual excluded error has no angular dependence on positive time
and radius; this follows from the proved base equation. -/
theorem baseError_angle_eq (n : ℕ) {x : Point} (hR : 0 < x.1) (hT : 0 < x.2.1.1)
    (theta : ℝ) (i : Fin 3) :
    baseError H v upper B n (x, theta) i = baseError H v upper B n (x, 0) i := by
  let c := CommonBaseContext.context H v upper B (fun _ => 0)
  let G := commonGraph (ChartScales.Q n) F.data.h 0
  have hr : CopyAngularInvariance.Invariant (0, (1 : ℝ)) ScaledGraph.radius := by
    intro y t
    simp [ScaledGraph.radius]
  have hvr : CopyAngularInvariance.Invariant (0, (1 : ℝ)) (PhysicalResidualTZ.graphRadialTZ G) := by
    intro y t
    simp [PhysicalResidualTZ.graphRadialTZ_eq, ScaledGraph.radial]
  have hvtheta : CopyAngularInvariance.Invariant (0, (1 : ℝ)) PhysicalResidualTZ.graphAngularTZ :=
    fun _ _ => rfl
  have hvz : CopyAngularInvariance.Invariant (0, (1 : ℝ)) (PhysicalResidualTZ.graphAxialTZ G) :=
    fun _ _ => rfl
  have hvt : CopyAngularInvariance.Invariant (0, (1 : ℝ)) (PhysicalResidualTZ.graphTemporalTZ G) :=
    fun _ _ => rfl
  have ha : CopyAngularInvariance.Invariant (0, (1 : ℝ)) (baseComponents c n) := by
    intro y t
    simp [baseComponents]
  have hp : CopyAngularInvariance.Invariant (0, (1 : ℝ)) (basePressure H v upper B n) := by
    intro y t
    rw [basePressure_eq_fixedPressure, basePressure_eq_fixedPressure]
    simp
  have hinv := graphResidual_invariant (0, (1 : ℝ)) (ChartScales.Q n ^ F.data.h)
    ScaledGraph.radius (PhysicalResidualTZ.graphRadialTZ G) PhysicalResidualTZ.graphAngularTZ
    (PhysicalResidualTZ.graphAxialTZ G) (PhysicalResidualTZ.graphTemporalTZ G)
    (baseComponents c n) (basePressure H v upper B n) hr hvr hvtheta hvz hvt ha hp i
  have he := hinv (x, 0) theta
  simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero, zero_add] at
    he
  have ht := fixed_base_residual H v upper B (fun _ => 0) n (x := (x, theta)) ⟨hR, hT⟩ i
  have h0 := fixed_base_residual H v upper B (fun _ => 0) n (x := (x, 0)) ⟨hR, hT⟩ i
  change _ = _ at he
  rw [ht, h0] at he
  exact add_left_cancel he


theorem baseError_auxiliary_eq (n : ℕ) (R : ℝ) (s Y Y' : ℝ × ℝ) (theta : ℝ) :
    baseError H v upper B n ((R, (s, Y)), theta) =
      baseError H v upper B n ((R, (s, Y')), theta) := rfl

theorem basePressure_auxiliary_eq (n : ℕ) (R : ℝ) (s Y Y' : ℝ × ℝ) (theta : ℝ) :
    basePressure H v upper B n ((R, (s, Y)), theta) =
      basePressure H v upper B n ((R, (s, Y')), theta) := rfl

/-- Fixed-band common-cover specialization of the same physical error field. -/
theorem errorState_common (U : Set Point) (n k : ℕ) :
    PhysicalResidualNaturality.StateOn U (CommonBaseContext.coverLift k) 1 1
      (errorState H v upper B) (errorState H v upper B) n n := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx; simp [errorState]
  · intro x hx theta i; simp [errorState]
  · intro x hx theta; simp [errorState]
  · intro x hx theta i
    simp [errorState, baseError, errorAtScale, physicalPoint, cylinderPoint]
  · intro x hx theta i; simp [errorState]
  · intro x hx theta i; simp [errorState]

theorem fixedPressure_common (U : Set Point) (n k : ℕ) :
    PhysicalResidualNaturality.ScalarOn U (CommonBaseContext.coverLift k) 1
      (fixedPressure H v upper B n) (fixedPressure H v upper B n) := by
  intro x hx
  simp [fixedPressure, basePressure, pressureAtScale, physicalPoint, cylinderPoint]

end Actual

end NavierStokes.ActualBaseResidual
