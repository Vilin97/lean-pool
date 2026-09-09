/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialLocalization
public import LeanPool.NavierStokesAndEuler.NavierStokes.OffplaneCorrectionExtensions
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualCalculus

/-!
# Direct angular means in the physical diagonal

The angular velocity is retained as a direct field. It is not replaced by
an axial primitive. Axisymmetry proves its divergence equation, and an
annular zero germ removes the coordinate singularity on the axis.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.DirectAngularDiagonal

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators

/-- Slow: an abbreviation for `ℝ × ℝ`. -/
abbrev Slow := ℝ × ℝ
/-- Cyl point: an abbreviation for `ℝ × (ℝ × ℝ)`. -/
abbrev CylPoint := ℝ × (ℝ × ℝ)
/-- Coefficient: an abbreviation for `CylPoint → ℝ`. -/
abbrev Coefficient := CylPoint → ℝ

/-- Radius, given by `PolarCharts.radius (PhysicalGraphBounds.radialProjection w)`. -/
noncomputable def radius (w : SpaceTime) : ℝ :=
  PolarCharts.radius (PhysicalGraphBounds.radialProjection w)

/-- Slow point, given by `(w.1, w.2 2)`. -/
noncomputable def slowPoint (w : SpaceTime) : Slow := (w.1, w.2 2)

/-- Cyl point, given by `(w.1, (radius w, w.2 2))`. -/
noncomputable def cylPoint (w : SpaceTime) : CylPoint := (w.1, (radius w, w.2 2))

/-- Slow of cyl, given by `(p.1, p.2.2)`. -/
noncomputable def slowOfCyl (p : CylPoint) : Slow := (p.1, p.2.2)

/-- Physical domain, given by `slowPoint ⁻¹' U`. -/
noncomputable def physicalDomain (U : Set Slow) : Set SpaceTime := slowPoint ⁻¹' U

/-- Positive domain, given by `{p | slowOfCyl p ∈ U ∧ 0 < p.2.1}`. -/
noncomputable def positiveDomain (U : Set Slow) : Set CylPoint :=
  {p | slowOfCyl p ∈ U ∧ 0 < p.2.1}

theorem slowPoint_smooth : ContDiff ℝ ∞ slowPoint :=
  contDiff_fst.prodMk ((AxisymmetricFields.projection 2).contDiff.comp contDiff_snd)

theorem physicalDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (physicalDomain U) :=
  hU.preimage slowPoint_smooth.continuous

theorem positiveDomain_open {U : Set Slow} (hU : IsOpen U) : IsOpen (positiveDomain U) :=
  (hU.preimage (continuous_fst.prodMk continuous_snd.snd)).inter
    (isOpen_lt continuous_const continuous_snd.fst)

theorem radius_nonneg (w : SpaceTime) : 0 ≤ radius w := PolarCharts.radius_nonneg _

theorem radius_continuous : Continuous radius :=
  PolarCharts.radius_continuous.comp PhysicalGraphBounds.radialProjection.continuous

/-- Profile to cyl, given by `(p.1, (Real.sqrt (2 * p.2.1), p.2.2))`. -/
noncomputable def profileToCyl (p : AxisymmetricFields.ProfilePoint) : CylPoint :=
  (p.1, (Real.sqrt (2 * p.2.1), p.2.2))

/-- Rate, given by `b (profileToCyl p) / Real.sqrt (2 * p.2.1)`. -/
noncomputable def rate (b : Coefficient) (p : AxisymmetricFields.ProfilePoint) : ℝ :=
  b (profileToCyl p) / Real.sqrt (2 * p.2.1)

/-- Literal angular velocity with physical tangential magnitude `b`. -/
noncomputable def angularField (b : Coefficient) (w : SpaceTime) : Space :=
  (-w.2 1 / radius w * b (cylPoint w)) • coordinateVector 0 +
    (w.2 0 / radius w * b (cylPoint w)) • coordinateVector 1

/-- Rotation field, constructed using `AxisymmetricResidual.pack`. -/
noncomputable def rotationField (F : AxisymmetricFields.Profile) (w : SpaceTime) : Space :=
  AxisymmetricResidual.pack (-w.2 1 * F (AxisymmetricFields.profilePoint w.1 w.2))
    (w.2 0 * F (AxisymmetricFields.profilePoint w.1 w.2)) 0

theorem profileToCyl_profilePoint (w : SpaceTime) :
    profileToCyl (AxisymmetricFields.profilePoint w.1 w.2) = cylPoint w := by
  have he : 2 * AxisymmetricFields.radialEnergy w.2 = w.2 0 ^ 2 + w.2 1 ^ 2 := by
    unfold AxisymmetricFields.radialEnergy
    ring
  simp only [profileToCyl, AxisymmetricFields.profilePoint, he, cylPoint, radius,
    PolarCharts.radius, PhysicalGraphBounds.radialProjection_apply]

theorem angularField_eq_rotationField (b : Coefficient) : angularField b = rotationField (rate b)
    := by
  funext w
  have hr : Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) = radius w :=
    congrArg (fun p : CylPoint => p.2.1) (profileToCyl_profilePoint w)
  simp only [angularField, rotationField, rate]
  rw [profileToCyl_profilePoint]
  simp only [AxisymmetricFields.profilePoint, hr, AxisymmetricResidual.pack, zero_smul, add_zero]
  congr 1 <;> congr 1 <;> ring

/-- The cancellation is computed from actual Cartesian derivatives. -/
theorem divergence_rotationField {F : AxisymmetricFields.Profile} {w : SpaceTime}
    (hF : DifferentiableAt ℝ F (AxisymmetricFields.profilePoint w.1 w.2)) :
    spatialDivergence (rotationField F) w.1 w.2 = 0 := by
  have hf := AxisymmetricFields.hasFDerivAt_profile_composition F w.1 w.2 hF
  have hd := AxisymmetricResidual.hasFDerivAt_pack
    ((AxisymmetricFields.projection 1).hasFDerivAt.neg.mul hf)
    ((AxisymmetricFields.projection 0).hasFDerivAt.mul hf)
    (hasFDerivAt_const (0 : ℝ) w.2)
  unfold spatialDivergence spatialDerivative
  change (∑ i : Fin 3, fderiv ℝ (fun x => rotationField F (w.1, x)) w.2
    (coordinateVector i) i) = 0
  rw [show fderiv ℝ (fun x => rotationField F (w.1, x)) w.2 = _ from hd.fderiv,
    Fin.sum_univ_three]
  simp [AxisymmetricResidual.packDerivative_apply, AxisymmetricFields.profileDerivative_apply,
    AxisymmetricFields.projection, coordinateVector]
  ring

theorem rotationField_smoothAt {F : AxisymmetricFields.Profile} {w : SpaceTime}
    (hF : ContDiffAt ℝ ∞ F (AxisymmetricFields.profilePoint w.1 w.2)) :
    ContDiffAt ℝ ∞ (rotationField F) w := by
  have hf := hF.comp w AxisymmetricFields.contDiff_profilePoint.contDiffAt
  exact (((((AxisymmetricFields.projection 1).contDiff.comp contDiff_snd).contDiffAt.neg.mul
      hf).smul
    contDiffAt_const).add
    ((((AxisymmetricFields.projection 0).contDiff.comp contDiff_snd).contDiffAt.mul hf).smul
      contDiffAt_const)).add (show ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : ℝ) • coordinateVector
          2) w from contDiffAt_const)

theorem rate_smoothAt {U : Set Slow} (hU : IsOpen U) {b : Coefficient}
    (hb : ContDiffOn ℝ ∞ b (positiveDomain U)) {w : SpaceTime}
    (hw : w ∈ physicalDomain U) (hr : 0 < radius w) :
    ContDiffAt ℝ ∞ (rate b) (AxisymmetricFields.profilePoint w.1 w.2) := by
  have he : 2 * AxisymmetricFields.radialEnergy w.2 = w.2 0 ^ 2 + w.2 1 ^ 2 := by
    unfold AxisymmetricFields.radialEnergy
    ring
  have hpos : 0 < 2 * AxisymmetricFields.radialEnergy w.2 := by
    rw [he]
    exact Real.sqrt_pos.mp hr
  have hs : ContDiffAt ℝ ∞ (fun p : AxisymmetricFields.ProfilePoint => Real.sqrt (2 * p.2.1))
      (AxisymmetricFields.profilePoint w.1 w.2) :=
    (contDiffAt_const.mul contDiffAt_snd.fst).sqrt hpos.ne'
  have hp : profileToCyl (AxisymmetricFields.profilePoint w.1 w.2) ∈ positiveDomain U := by
    rw [profileToCyl_profilePoint]
    exact ⟨hw, hr⟩
  have hb' := hb.contDiffAt ((positiveDomain_open hU).mem_nhds hp)
  exact (hb'.comp _ (contDiffAt_fst.prodMk (hs.prodMk contDiffAt_snd.snd))).div hs
    (Real.sqrt_pos.mpr hpos).ne'

/-- A moving positive inner support radius is a primitive support datum.
It may shrink as the physical terminal point is approached. -/
structure AngularData (U : Set Slow) where
  /-- Scalar of `AngularData`, of type `Coefficient`. -/
  scalar : Coefficient
  smooth : ContDiffOn ℝ ∞ scalar (positiveDomain U)
  /-- Inner of `AngularData`, of type `Slow → ℝ`. -/
  inner : Slow → ℝ
  inner_continuous : ContinuousOn inner U
  inner_pos : ∀ s ∈ U, 0 < inner s
  vanishes : ∀ p, slowOfCyl p ∈ U → 0 ≤ p.2.1 → p.2.1 < inner (slowOfCyl p) → scalar p = 0

namespace AngularData

variable {U : Set Slow} (D : AngularData U)

theorem field_zero_germ (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U)
    (hr : radius w < D.inner (slowPoint w)) :
    angularField D.scalar =ᶠ[𝓝 w] fun _ => 0 := by
  have hi : ContinuousAt (fun y => D.inner (slowPoint y)) w :=
    (D.inner_continuous.continuousAt (hU.mem_nhds hw)).comp slowPoint_smooth.continuous.continuousAt
  have hp := (hi.sub radius_continuous.continuousAt)
    (lt_mem_nhds (sub_pos.mpr hr))
  filter_upwards [(physicalDomain_open hU).mem_nhds hw, hp] with y hy hpy
  have hz := D.vanishes (cylPoint y) hy (radius_nonneg y) (sub_pos.mp hpy)
  simp only [angularField, hz, mul_zero, zero_smul, add_zero]

theorem field_smoothAt (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    ContDiffAt ℝ ∞ (angularField D.scalar) w := by
  by_cases hr : 0 < radius w
  · rw [angularField_eq_rotationField]
    exact rotationField_smoothAt (rate_smoothAt hU D.smooth hw hr)
  · have hz : radius w = 0 := le_antisymm (le_of_not_gt hr) (radius_nonneg w)
    exact contDiffAt_const.congr_of_eventuallyEq
      (D.field_zero_germ hU hw (hz ▸ D.inner_pos _ hw))

theorem field_smooth (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (angularField D.scalar) (physicalDomain U) :=
  fun _ hw => (D.field_smoothAt hU hw).contDiffWithinAt

theorem field_divergence (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (angularField D.scalar) w.1 w.2 = 0 := by
  by_cases hr : 0 < radius w
  · rw [angularField_eq_rotationField]
    exact divergence_rotationField ((rate_smoothAt hU D.smooth hw hr).differentiableAt (by simp))
  · have hz : radius w = 0 := le_antisymm (le_of_not_gt hr) (radius_nonneg w)
    have he := (D.field_zero_germ hU hw (hz ▸ D.inner_pos _ hw)).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
    have he' : (fun y : Space => angularField D.scalar (w.1, y)) =ᶠ[𝓝 w.2] fun _ => 0 := he
    unfold spatialDivergence spatialDerivative
    rw [he'.fderiv_eq]
    simp

/-- Multiply, bundling `scalar`, `smooth`, `inner`, `inner_continuous` and the required
compatibility proofs. -/
noncomputable def multiply (f : Coefficient) (hf : ContDiffOn ℝ ∞ f (positiveDomain U)) :
    AngularData U where
  scalar p := f p * D.scalar p
  smooth := hf.mul D.smooth
  inner := D.inner
  inner_continuous := D.inner_continuous
  inner_pos := D.inner_pos
  vanishes p hp hr hi := by rw [D.vanishes p hp hr hi, mul_zero]

end AngularData

theorem angularField_axis (b : Coefficient) (t : ℝ) (x : Space) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    angularField b (t, x) = 0 := by
  simp [angularField, h0, h1]

theorem angularField_mul (f b : Coefficient) :
    angularField (fun p => f p * b p) = fun w => f (cylPoint w) • angularField b w := by
  funext w
  simp only [angularField, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- Cut coefficient, defined pointwise by `SmoothCutoffs.scaledCutoff a (q p) * b p`. -/
noncomputable def cutCoefficient (a : ℝ) (q b : Coefficient) : Coefficient :=
  fun p => SmoothCutoffs.scaledCutoff a (q p) * b p

theorem cut_angularField (a : ℝ) (q b : Coefficient) :
    angularField (cutCoefficient a q b) =
      fun w => SmoothCutoffs.scaledCutoff a (q (cylPoint w)) • angularField b w :=
  angularField_mul _ _

/-- Cut, given by `D.multiply (fun p => SmoothCutoffs.scaledCutoff a (q p))
((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq)`. -/
noncomputable def AngularData.cut {U : Set Slow} (D : AngularData U) (a : ℝ)
    (q : Coefficient) (hq : ContDiffOn ℝ ∞ q (positiveDomain U)) : AngularData U :=
  D.multiply (fun p => SmoothCutoffs.scaledCutoff a (q p))
    ((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq)

theorem divergence_cut_angular {U : Set Slow} (hU : IsOpen U) (D : AngularData U)
    (a : ℝ) (q : Coefficient) (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (fun y => SmoothCutoffs.scaledCutoff a (q (cylPoint y)) • angularField
        D.scalar y)
      w.1 w.2 = 0 := by
  rw [← cut_angularField]
  exact (D.cut a q hq).field_divergence hU hw

/-! ## Locally finite direct angular sums -/

/-- Angular sum, given by `SolenoidalDiagonal.potentialSum a q (fun j => angularField (b j))`. -/
noncomputable def angularSum (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (b : ℕ → Coefficient) : VelocityField :=
  SolenoidalDiagonal.potentialSum a q (fun j => angularField (b j))

/-- Angular partial, given by `SolenoidalDiagonal.partialPotential a q (fun j => angularField (b
j)) N`. -/
noncomputable def angularPartial (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (b : ℕ → Coefficient) (N : ℕ) : VelocityField :=
  SolenoidalDiagonal.partialPotential a q (fun j => angularField (b j)) N

theorem divergence_congr {v w : VelocityField} {x : SpaceTime} (h : v =ᶠ[𝓝 x] w) :
    spatialDivergence v x.1 x.2 = spatialDivergence w x.1 x.2 := by
  have he : (fun y : Space => v (x.1, y)) =ᶠ[𝓝 x.2] fun y => w (x.1, y) :=
    h.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  unfold spatialDivergence spatialDerivative
  rw [he.fderiv_eq]

theorem divergence_finset_sum {I : Type} (J : Finset I) (v : I → VelocityField)
    (x : SpaceTime) (hv : ∀ j ∈ J, DifferentiableAt ℝ (fun y : Space => v j (x.1, y)) x.2) :
    spatialDivergence (fun y => ∑ j ∈ J, v j y) x.1 x.2 =
      ∑ j ∈ J, spatialDivergence (v j) x.1 x.2 := by
  unfold spatialDivergence spatialDerivative
  rw [fderiv_fun_sum hv]
  simp only [_root_.sum_apply]
  calc
    _ = ∑ i : Fin 3, ∑ j ∈ J, (fderiv ℝ (fun y => v j (x.1, y)) x.2 (coordinateVector i)) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact map_sum (EuclideanSpace.proj i) _ _
    _ = _ := Finset.sum_comm

theorem angularSum_eventuallyEq_partial {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {x : SpaceTime} (hq : ContinuousAt q x) (hx : 0 < q x)
    (b : ℕ → Coefficient) :
    ∃ N : ℕ, angularSum a q b =ᶠ[𝓝 x] angularPartial a q b N :=
  SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hx _

theorem angularSum_smooth {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x) :
    ContDiffOn ℝ ∞ (angularSum a q (fun j => (D j).scalar)) (physicalDomain U) :=
  SolenoidalDiagonal.potentialSum_contDiffOn ha (physicalDomain_open hU) hpos hq
    (fun j => (D j).field_smooth hU)

theorem angularSum_allJets {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x)
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ᶠ y in 𝓝 x,
      iteratedFDeriv ℝ k (angularSum a q (fun j => (D j).scalar)) y =
        ∑ j ∈ Finset.range N, iteratedFDeriv ℝ k
          (SolenoidalDiagonal.cutStage a q (fun j => angularField (D j).scalar) j) y :=
  SolenoidalDiagonal.potentialSum_allJets_eventuallyEq_sum ha (physicalDomain_open hU)
    hpos hq (fun j => (D j).field_smooth hU) hx

theorem angularSum_locallyFinite {U : Set Slow} (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContinuousOn q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x) :
    LocallyFinite (fun j => support (fun x : physicalDomain U =>
      SolenoidalDiagonal.cutStage a q (fun j => angularField (D j).scalar) j x)) :=
  SolenoidalDiagonal.locallyFinite_cutStage_support_on ha hq hpos _

theorem angularSum_divergence {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (q : Coefficient)
    (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    (hqp : ContDiffOn ℝ ∞ (fun x => q (cylPoint x)) (physicalDomain U))
    (hpos : ∀ x ∈ physicalDomain U, 0 < q (cylPoint x))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    spatialDivergence (angularSum a (fun x => q (cylPoint x)) (fun j => (D j).scalar)) x.1 x.2 = 0
        := by
  have hqAt := hqp.contDiffAt ((physicalDomain_open hU).mem_nhds hx)
  obtain ⟨N, hN⟩ := angularSum_eventuallyEq_partial ha hqAt.continuousAt (hpos x hx)
    (fun j => (D j).scalar)
  rw [divergence_congr hN]
  have hs (j : ℕ) : DifferentiableAt ℝ
      (fun y : Space => SolenoidalDiagonal.cutStage a (fun x => q (cylPoint x))
        (fun j => angularField (D j).scalar) j (x.1, y)) x.2 :=
    ((SolenoidalDiagonal.cutStage_contDiffAt hqAt
      (fun j => (D j).field_smoothAt hU hx) j).comp x.2
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change spatialDivergence (fun y => ∑ j ∈ Finset.range N,
    SolenoidalDiagonal.cutStage a (fun x => q (cylPoint x)) (fun j => angularField (D j).scalar) j
        y) x.1 x.2 = 0
  rw [divergence_finset_sum _ _ x (fun j _ => hs j)]
  apply Finset.sum_eq_zero
  intro j _
  exact divergence_cut_angular hU (D j) (a j) q hq hx

theorem angularSum_axis (a : ℕ → ℝ) (q : SpaceTime → ℝ) (b : ℕ → Coefficient)
    (t : ℝ) (x : Space) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    angularSum a q b (t, x) = 0 := by
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage,
    angularField_axis _ _ _ h0 h1, smul_zero, tsum_zero]

theorem angularSum_axis_zero_germ {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x) (hx : x ∈ physicalDomain U)
    (haxis : radius x = 0) :
    angularSum a q (fun j => (D j).scalar) =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨N, hN⟩ := angularSum_eventuallyEq_partial ha hq hpos (fun j => (D j).scalar)
  have hz (j : ℕ) : (fun y => SolenoidalDiagonal.cutStage a q
      (fun j => angularField (D j).scalar) j y) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(D j).field_zero_germ hU hx (haxis ▸ (D j).inner_pos _ hx)] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  have hsum : angularPartial a q (fun j => (D j).scalar) N =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(Filter.eventually_all_finset (Finset.range N)).2 (fun j _ => hz j)] with y hy
    exact Finset.sum_eq_zero hy
  exact hN.trans hsum

/-! ## Curl potentials plus direct angular velocity -/

/-- Mixed velocity, defined pointwise by `SolenoidalDiagonal.velocitySum a q A x + angularSum a
q b x`. -/
noncomputable def mixedVelocity (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A : ℕ → VelocityField) (b : ℕ → Coefficient) : VelocityField :=
  fun x => SolenoidalDiagonal.velocitySum a q A x + angularSum a q b x

theorem mixedVelocity_smooth {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x)
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (physicalDomain U)) :
    ContDiffOn ℝ ∞ (mixedVelocity a q A (fun j => (D j).scalar)) (physicalDomain U) :=
  (SolenoidalDiagonal.velocitySum_contDiffOn ha (physicalDomain_open hU) hpos hq hA).add
    (angularSum_smooth hU D ha hq hpos)

theorem mixedVelocity_divergence {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (q : Coefficient)
    (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    (hqp : ContDiffOn ℝ ∞ (fun x => q (cylPoint x)) (physicalDomain U))
    (hpos : ∀ x ∈ physicalDomain U, 0 < q (cylPoint x))
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (physicalDomain U))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    spatialDivergence (mixedVelocity a (fun x => q (cylPoint x)) A (fun j => (D j).scalar)) x.1 x.2
        = 0 := by
  have hmem := (physicalDomain_open hU).mem_nhds hx
  have hc := (SolenoidalDiagonal.velocitySum_contDiffOn ha (physicalDomain_open hU) hpos hqp
      hA).contDiffAt hmem
  have hd := (angularSum_smooth hU D ha hqp hpos).contDiffAt hmem
  unfold mixedVelocity
  rw [ResidualCalculus.spatialDivergence_add _ _ _ _
    ((hc.comp x.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hd.comp x.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)),
    SolenoidalDiagonal.divergence_velocitySum_on ha (physicalDomain_open hU) hpos hqp hA x hx,
    angularSum_divergence hU D ha q hq hqp hpos hx, add_zero]

theorem mixedVelocity_axis (a : ℕ → ℝ) (q : SpaceTime → ℝ) (A : ℕ → VelocityField)
    (b : ℕ → Coefficient) (t : ℝ) (x : Space) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    mixedVelocity a q A b (t, x) = SolenoidalDiagonal.velocitySum a q A (t, x) := by
  rw [mixedVelocity, angularSum_axis a q b t x h0 h1, add_zero]

/-! ## The actual similarity cutoff -/

/-- Preterminal slow, given by `{s | s.1 < 1}`. -/
noncomputable def preterminalSlow : Set Slow := {s | s.1 < 1}

theorem preterminalSlow_open : IsOpen preterminalSlow := isOpen_lt continuous_fst continuous_const

/-- Q coefficient, given by `SimilarityProfile.q h`. -/
noncomputable def qCoefficient (h : ℝ) : Coefficient := SimilarityProfile.q h

theorem qCoefficient_physical (h : ℝ) (w : SpaceTime) :
    qCoefficient h (cylPoint w) = PhysicalWaveSum.physicalQ h w := rfl

theorem physicalDomain_preterminal : physicalDomain preterminalSlow = PhysicalWaveSum.preterminal
    := rfl

theorem qCoefficient_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (qCoefficient h) (positiveDomain preterminalSlow) :=
  fun _ hp => (SimilarityProfile.q_smoothAt hh hh1 hp.1).contDiffWithinAt

theorem physicalQ_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) (physicalDomain preterminalSlow) :=
  fun _ hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt

theorem actual_diagonal_divergence {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → AngularData preterminalSlow) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {w : SpaceTime} (hw : w.1 < 1) :
    spatialDivergence (angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)) w.1 w.2
        = 0 :=
  angularSum_divergence preterminalSlow_open D ha (qCoefficient h) (qCoefficient_smooth hh hh1)
    (physicalQ_smooth hh hh1) (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx) hw

theorem actual_diagonal_smooth {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → AngularData preterminalSlow) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ContDiffOn ℝ ∞ (angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar))
      PhysicalWaveSum.preterminal :=
  angularSum_smooth preterminalSlow_open D ha (physicalQ_smooth hh hh1)
    (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx)

theorem actual_mixed_divergence {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → AngularData preterminalSlow) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) PhysicalWaveSum.preterminal)
    {w : SpaceTime} (hw : w.1 < 1) :
    spatialDivergence (mixedVelocity a (PhysicalWaveSum.physicalQ h) A (fun j => (D j).scalar)) w.1
        w.2 = 0 :=
  mixedVelocity_divergence preterminalSlow_open D ha (qCoefficient h) (qCoefficient_smooth hh hh1)
    (physicalQ_smooth hh hh1) (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx) hA hw

/-! ## The existing Cartesian spatial cutoff is axisymmetric -/

/-- Spatial profile, given by `SpatialLocalization.cutoffProfile (p.2.1 ^ 2, p.2.2)`. -/
noncomputable def spatialProfile (p : CylPoint) : ℝ :=
  SpatialLocalization.cutoffProfile (p.2.1 ^ 2, p.2.2)

theorem spatialProfile_smooth : ContDiff ℝ ∞ spatialProfile :=
  SpatialLocalization.cutoffProfile_contDiff.comp ((contDiff_snd.fst.pow 2).prodMk contDiff_snd.snd)

theorem spatialProfile_physical (w : SpaceTime) :
    spatialProfile (cylPoint w) = SpatialLocalization.spatialCutoff w.2 := by
  have hr : radius w ^ 2 = w.2 0 ^ 2 + w.2 1 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simp only [spatialProfile, cylPoint, hr, SpatialLocalization.spatialCutoff,
    SpatialLocalization.radialSquare]

theorem spatialCut_angular {U : Set Slow} (hU : IsOpen U) (D : AngularData U)
    {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (SpatialLocalization.cutPotential (angularField D.scalar)) w.1 w.2 = 0 := by
  have he : angularField (fun p => spatialProfile p * D.scalar p) =
      SpatialLocalization.cutPotential (angularField D.scalar) := by
    rw [angularField_mul]
    funext x
    rw [spatialProfile_physical]
    rfl
  rw [← he]
  exact (D.multiply spatialProfile spatialProfile_smooth.contDiffOn).field_divergence hU hw

theorem angularSum_multiply (a : ℕ → ℝ) (q : SpaceTime → ℝ) (f : Coefficient)
    (b : ℕ → Coefficient) :
    angularSum a q (fun j p => f p * b j p) = fun w => f (cylPoint w) • angularSum a q b w := by
  funext w
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage,
      angularField_mul]
  simp_rw [smul_comm (SmoothCutoffs.scaledCutoff _ _) (f (cylPoint w))]
  exact tsum_const_smul'' _

theorem spatialCut_angularSum (a : ℕ → ℝ) (q : SpaceTime → ℝ) (b : ℕ → Coefficient) :
    SpatialLocalization.cutPotential (angularSum a q b) =
      angularSum a q (fun j p => spatialProfile p * b j p) := by
  rw [angularSum_multiply]
  funext w
  rw [spatialProfile_physical]
  rfl

theorem spatialCut_angularSum_divergence {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (q : Coefficient)
    (hq : ContDiffOn ℝ ∞ q (positiveDomain U))
    (hqp : ContDiffOn ℝ ∞ (fun x => q (cylPoint x)) (physicalDomain U))
    (hpos : ∀ x ∈ physicalDomain U, 0 < q (cylPoint x))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    spatialDivergence (SpatialLocalization.cutPotential
      (angularSum a (fun x => q (cylPoint x)) (fun j => (D j).scalar))) x.1 x.2 = 0 := by
  rw [spatialCut_angularSum]
  exact angularSum_divergence hU
    (fun j => (D j).multiply spatialProfile spatialProfile_smooth.contDiffOn) ha q hq hqp hpos hx

theorem actual_spatialCut_diagonal_divergence {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → AngularData preterminalSlow) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (t : ℝ) (ht : t < 1) (x : Space) :
    spatialDivergence (SpatialLocalization.cutPotential
      (angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar))) t x = 0 := by
  have hqp : ContDiffOn ℝ ∞ (fun w => qCoefficient h (cylPoint w)) (physicalDomain preterminalSlow)
      := by
    simpa only [qCoefficient_physical] using physicalQ_smooth hh hh1
  have hpos : ∀ w ∈ physicalDomain preterminalSlow, 0 < qCoefficient h (cylPoint w) :=
    fun _ hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw
  have he := spatialCut_angularSum_divergence preterminalSlow_open D ha (qCoefficient h)
    (qCoefficient_smooth hh hh1) hqp hpos (x := (t, x)) ht
  simpa only [qCoefficient_physical] using he

/-! ## Actual full-fiber means restricted to a physical graph -/

/-- Lift: an abbreviation for `PressureStream.Lift Slow`. -/
abbrev Lift := PressureStream.Lift Slow

/-- The time/axial variables in the actual mean-field convention `(T,Z)`. -/
noncomputable def graphSlow (G : PhysicalResidualBridge.ScaledGraph) (s : Slow) : Slow :=
  (G.velocityScale * G.radialScale * G.epsilon * (1 - s.1),
    G.radialScale * G.epsilon * s.2)

/-- Graph point as an element of `Lift`. -/
noncomputable def graphPoint (G : PhysicalResidualBridge.ScaledGraph) (p : CylPoint) : Lift :=
  (G.radialScale * p.2.1, (graphSlow G (slowOfCyl p),
    (G.frequency * (G.radialScale * p.2.1) ^ G.exponent) • G.radialVector +
      (G.velocityScale * G.radialScale * G.fastCoefficient * p.1) • G.temporalVector))

/-- The physical velocity normalization is included here. -/
noncomputable def graphCoefficient (G : PhysicalResidualBridge.ScaledGraph) (f : Lift → ℝ) :
    Coefficient :=
  fun p => G.velocityScale * f (graphPoint G p)

theorem graphPoint_actual (G : PhysicalResidualBridge.ScaledGraph) (p : CylPoint) (theta : ℝ) :
    graphPoint G p = PhysicalResidualTZ.swapSlow
      (G.map (p.1, AxisymmetricResidual.pack p.2.1 theta p.2.2)).1 := by
  simp only [graphPoint, graphSlow, slowOfCyl, PhysicalResidualTZ.swapSlow_apply,
    PhysicalResidualBridge.ScaledGraph.map, AxisymmetricResidual.pack_zero,
    AxisymmetricResidual.pack_one, AxisymmetricResidual.pack_two]

theorem graphCoefficient_actual (G : PhysicalResidualBridge.ScaledGraph) (f : Lift → ℝ)
    (p : CylPoint) (theta : ℝ) :
    graphCoefficient G f p = G.velocityScale *
      f (PhysicalResidualTZ.swapSlow (G.map (p.1, AxisymmetricResidual.pack p.2.1 theta p.2.2)).1)
          := by
  rw [graphCoefficient, graphPoint_actual G p theta]

theorem graphSlow_smooth (G : PhysicalResidualBridge.ScaledGraph) : ContDiff ℝ ∞ (graphSlow G) :=
  (contDiff_const.mul (contDiff_const.sub contDiff_fst)).prodMk (contDiff_const.mul contDiff_snd)

theorem graphPoint_smoothAt (G : PhysicalResidualBridge.ScaledGraph) (hG : 0 < G.radialScale)
    {p : CylPoint} (hp : 0 < p.2.1) : ContDiffAt ℝ ∞ (graphPoint G) p := by
  have hr : ContDiffAt ℝ ∞ (fun p : CylPoint => (G.radialScale * p.2.1) ^ G.exponent) p :=
    (contDiffAt_const.mul contDiffAt_snd.fst).rpow_const_of_ne (mul_pos hG hp).ne'
  exact (contDiffAt_const.mul contDiffAt_snd.fst).prodMk
    (((graphSlow_smooth G).contDiffAt.comp p (contDiffAt_fst.prodMk contDiffAt_snd.snd)).prodMk
      (((contDiffAt_const.mul hr).smul contDiffAt_const).add
        ((contDiffAt_const.mul contDiffAt_fst).smul contDiffAt_const)))

/-- Smoothness and the positive moving support of the actual mean field
produce the angular data. No divergence or physical output is assumed. -/
noncomputable def graphAngularData (G : PhysicalResidualBridge.ScaledGraph) (hG : 0 < G.radialScale)
    {U : Set Slow} (hU : IsOpen U) {a b : ℝ} (ha : 0 < a) (ell : Slow → ℝ)
    (hell : ContinuousOn ell U) (hpos : ∀ s ∈ U, 0 < ell s)
    (f : Lift → ℝ) (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell U f) : AngularData (graphSlow G ⁻¹' U) where
  scalar := graphCoefficient G f
  smooth := by
    intro p hp
    have hfAt : ContDiffAt ℝ ∞ f (graphPoint G p) :=
      hf.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hp.1)
    exact (contDiffAt_const.mul (hfAt.comp p (graphPoint_smoothAt G hG hp.2))).contDiffWithinAt
  inner s := ell (graphSlow G s) * a / G.radialScale
  inner_continuous := ((hell.comp (graphSlow_smooth G).continuous.continuousOn (fun _ hx => hx)).mul
    continuousOn_const).div_const _
  inner_pos s hs := div_pos (mul_pos (hpos _ hs) ha) hG
  vanishes := by
    classical
    intro p hp _ hi
    have hz : f (graphPoint G p) = 0 := by
      by_contra hn
      have hbound := (hs (graphPoint G p) hp hn).1
      have hlt := (lt_div_iff₀ hG).mp hi
      apply (not_lt_of_ge hbound)
      simpa only [graphPoint, mul_comm G.radialScale p.2.1] using hlt
    simp only [graphCoefficient, hz, mul_zero]

/-- Common angular data, given by `graphAngularData _ (Real.rpow_pos_of_pos hQ _) hU ha ell hell
hpos f hf hs`. -/
noncomputable def commonAngularData {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (cover : ℕ)
    {U : Set Slow} (hU : IsOpen U) {a b : ℝ} (ha : 0 < a) (ell : Slow → ℝ)
    (hell : ContinuousOn ell U) (hpos : ∀ s ∈ U, 0 < ell s)
    (f : Lift → ℝ) (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell U f) :
    AngularData (graphSlow (PhysicalResidualBridge.commonGraph Q h cover) ⁻¹' U) :=
  graphAngularData _ (Real.rpow_pos_of_pos hQ _) hU ha ell hell hpos f hf hs

/-- The common-graph coefficient carries exactly the manuscript's
`Q^(-A)` velocity factor, with no independent angular choice. -/
theorem commonCoefficient_actual (Q h : ℝ) (cover : ℕ) (f : Lift → ℝ) (p : CylPoint) (theta : ℝ) :
    graphCoefficient (PhysicalResidualBridge.commonGraph Q h cover) f p =
      Q ^ (-CoordinateAlgebra.A h) *
        f (PhysicalResidualTZ.swapSlow
          ((PhysicalResidualBridge.commonGraph Q h cover).map
            (p.1, AxisymmetricResidual.pack p.2.1 theta p.2.2)).1) :=
  graphCoefficient_actual _ f p theta

/-- The direct angular part of the literal temporal update, with its
regularity and support inherited from the actual input residual. -/
noncomputable def temporalAngularData (G : PhysicalResidualBridge.ScaledGraph) (hG : 0 <
    G.radialScale)
    (g : VariableGaugeMean.GaugeData Slow) (h : ℝ) (index : ℕ → ℕ)
    (axial : Slow × PressureStream.Plane) (c : CorrectionState.Context Lift)
    (u : CorrectionState.State Lift) (n : ℕ) {U : Set Slow} (hU : IsOpen U)
    {a b : ℝ} (ha : 0 < a) (ell : Slow → ℝ) (hell : ContinuousOn ell U)
    (hpos : ∀ s ∈ U, 0 < ell s)
    (hf : ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U (u.thetaResidual c n))
    (hs : VariableGaugeMean.SupportedGauge a b ell U (u.thetaResidual c n)) :
    AngularData (graphSlow G ⁻¹' U) :=
  graphAngularData G hG hU ha ell hell hpos
    ((VariableGaugeMean.temporalIncrementState g h index axial c u).angular n)
    (VariableGaugeMean.temporalAtIndex_contDiffOn h n (index n) hU hf hp)
    (VariableGaugeMean.temporalAtIndex_supportedGauge h n (index n) hs)

/-- The direct angular part of the literal rank update. Its smoothness
comes from the actual five-row rank family and current debt. -/
noncomputable def rankAngularData (G : PhysicalResidualBridge.ScaledGraph) (hG : 0 < G.radialScale)
    (g : VariableGaugeMean.GaugeData Slow) (r : CorrectionState.RankData Slow)
    (axial : Slow × PressureStream.Plane) (c : CorrectionState.Context Lift)
    (u : CorrectionState.State Lift) (n : ℕ) {U : Set Slow} (hU : IsOpen U)
    (H : LocalRankDefect.RankGeometry g r U c u) : AngularData (graphSlow G ⁻¹' U) :=
  graphAngularData G hG hU H.inner_pos (r.length n) (H.length_smooth n).continuousOn
    (H.length_pos n) ((VariableGaugeMean.rankIncrementState g r axial c u).angular n)
    (H.angular_lift_smooth n) (H.angular_supportedGauge axial n)

/-! ## Agreement with the actual offplane continuation fields -/

/-- Native graph data, bundling `radialScale`, `velocityScale`, `epsilon`, `exponent` and the
required compatibility proofs. -/
noncomputable def nativeGraphData (h : ℝ) (n : ℕ) : PhysicalResidualBridge.ScaledGraph where
  radialScale := 1
  velocityScale := 1
  epsilon := 1
  exponent := ChartScales.radialExponent h
  frequency := ChartScales.Lambda ^ ChartScales.nativeIndex h n
  fastCoefficient := ChartScales.Tg ^ ChartScales.nativeIndex h n
  radialVector := PhysicalGraphBounds.radialDirection
  temporalVector := PhysicalGraphBounds.timeDirection

theorem native_graphPoint (h : ℝ) (n : ℕ) (w : SpaceTime) :
    graphPoint (nativeGraphData h n) (cylPoint w) = OffplaneCorrectionExtensions.physicalLift h n w
        := by
  simp only [graphPoint, nativeGraphData, cylPoint, graphSlow, slowOfCyl, one_mul,
    OffplaneCorrectionExtensions.physicalLift, OffplaneCorrectionExtensions.physicalSlow,
    PhysicalGraphBounds.nativeGraph_eq, PhysicalGraphBounds.radialProfile,
    PhysicalGraphBounds.radiusPower_eq, smul_smul]
  rfl

/-- This is the direct continuation field, with no curl applied. -/
theorem native_angularField (h : ℝ) (n : ℕ) (f : Lift → ℝ) :
    angularField (graphCoefficient (nativeGraphData h n) f) =
      OffplaneCorrectionExtensions.angularField h n f := by
  funext w
  simp only [angularField, graphCoefficient]
  rw [native_graphPoint]
  simp only [nativeGraphData, one_mul,
    OffplaneCorrectionExtensions.angularField, OffplaneCorrectionExtensions.azimuthalPotential,
    OffplaneCorrectionExtensions.physicalScalar, Function.comp_apply]
  rfl

/-- Continuation angular data, constructed using `graphAngularData`. -/
noncomputable def continuationAngularData {coord a b : ℝ}
    {W : OffplaneCorrectionExtensions.Window coord a b} {f : Lift → ℝ}
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (h : ℝ) (n : ℕ) :
    AngularData (graphSlow (nativeGraphData h n) ⁻¹' W.carrier) :=
  graphAngularData (b := W.upper) (nativeGraphData h n)
    (by norm_num [nativeGraphData]) W.isOpen W.lower_pos
    (fun _ => 1) continuousOn_const (fun _ _ => by norm_num) e.value e.smooth (by
      intro p hp hn
      simpa only [one_mul] using W.fixed_support e.supported p hp hn)

theorem continuation_angular_divergence {coord a b : ℝ}
    {W : OffplaneCorrectionExtensions.Window coord a b} {f : Lift → ℝ}
    (e : OffplaneCorrectionExtensions.SupportedContinuation W f) (h : ℝ) (n : ℕ)
    {w : SpaceTime} (hw : w ∈ OffplaneCorrectionExtensions.physicalDomain W.carrier) :
    spatialDivergence (OffplaneCorrectionExtensions.angularField h n e.value) w.1 w.2 = 0 := by
  rw [← native_angularField]
  apply (continuationAngularData e h n).field_divergence
    (W.isOpen.preimage (graphSlow_smooth _).continuous)
  simpa only [physicalDomain, Set.mem_preimage, slowPoint, graphSlow, nativeGraphData,
    one_mul, OffplaneCorrectionExtensions.physicalDomain,
        OffplaneCorrectionExtensions.physicalSlow] using hw

/-! ## Mixed finite prefixes and preservation of every axis jet -/

theorem mixedVelocity_allJets {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    (hq : ContDiffOn ℝ ∞ q (physicalDomain U)) (hpos : ∀ x ∈ physicalDomain U, 0 < q x)
    {A : ℕ → VelocityField} (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (physicalDomain U))
    {x : SpaceTime} (hx : x ∈ physicalDomain U) :
    ∃ N M : ℕ, ∀ k : ℕ,
      iteratedFDeriv ℝ k (mixedVelocity a q A (fun j => (D j).scalar)) =ᶠ[𝓝 x]
      iteratedFDeriv ℝ k (fun y =>
        (∑ j ∈ Finset.range N, SpatialCurl.spatialCurl (SolenoidalDiagonal.cutStage a q A j) y) +
          angularPartial a q (fun j => (D j).scalar) M y) := by
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.velocitySum_eventuallyEq_sum ha
    (physicalDomain_open hU) hpos hq hA hx
  obtain ⟨M, hM⟩ := angularSum_eventuallyEq_partial ha
    (hq.contDiffAt ((physicalDomain_open hU).mem_nhds hx)).continuousAt (hpos x hx)
    (fun j => (D j).scalar)
  exact ⟨N, M, fun k => SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (hN.add hM) k⟩

theorem angularSum_axis_jets {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x) (hx : x ∈ physicalDomain U)
    (haxis : radius x = 0) (k : ℕ) :
    iteratedFDeriv ℝ k (angularSum a q (fun j => (D j).scalar)) x = 0 := by
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (angularSum_axis_zero_germ hU D ha hq hpos hx haxis) k).self_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he

theorem potentialSum_zero_germ {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x)
    (A : ℕ → VelocityField) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) :
    SolenoidalDiagonal.potentialSum a q A =ᶠ[𝓝 x] fun _ => 0 := by
  obtain ⟨N, hN⟩ := SolenoidalDiagonal.potentialSum_eventuallyEq_partial ha hq hpos A
  have hz (j : ℕ) : SolenoidalDiagonal.cutStage a q A j =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hA j] with y hy
    simp only [SolenoidalDiagonal.cutStage, hy, smul_zero]
  apply hN.trans
  filter_upwards [(Filter.eventually_all_finset (Finset.range N)).2 (fun j _ => hz j)] with y hy
  exact Finset.sum_eq_zero hy

/-- If the actual potentials vanish near the axis, adding the direct
angular diagonal preserves the entire axis germ, hence every axis jet. -/
theorem mixedVelocity_axis_zero_germ {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x) (hx : x ∈ physicalDomain U)
    (haxis : radius x = 0) (A : ℕ → VelocityField) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) :
    mixedVelocity a q A (fun j => (D j).scalar) =ᶠ[𝓝 x] fun _ => 0 := by
  have hc := SolenoidalDiagonal.spatialCurl_eventuallyEq (potentialSum_zero_germ ha hq hpos A hA)
  have hd := angularSum_axis_zero_germ hU D ha hq hpos hx haxis
  filter_upwards [hc, hd] with y hy hdy
  change SpatialCurl.spatialCurl (SolenoidalDiagonal.potentialSum a q A) y +
    angularSum a q (fun j => (D j).scalar) y = 0
  rw [hy, hdy]
  simp [SpatialCurl.spatialCurl, SpatialCurl.curl]

theorem mixedVelocity_axis_jets {U : Set Slow} (hU : IsOpen U) (D : ℕ → AngularData U)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {q : SpaceTime → ℝ}
    {x : SpaceTime} (hq : ContinuousAt q x) (hpos : 0 < q x) (hx : x ∈ physicalDomain U)
    (haxis : radius x = 0) (A : ℕ → VelocityField) (hA : ∀ j, A j =ᶠ[𝓝 x] fun _ => 0) (k : ℕ) :
    iteratedFDeriv ℝ k (mixedVelocity a q A (fun j => (D j).scalar)) x = 0 := by
  have he := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (mixedVelocity_axis_zero_germ hU D ha hq hpos hx haxis A hA) k).self_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using he

end NavierStokes.DirectAngularDiagonal
