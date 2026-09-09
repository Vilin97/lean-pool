/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Smooth axisymmetric fields in Cartesian coordinates

Profiles use coordinates `(t,s,z)`, where `s=(x₀²+x₁²)/2`. The velocity is an
actual Euclidean curl. No division by the radius is used, including at the axis.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisymmetricFields

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

/-- Profile point: an abbreviation for `ℝ × (ℝ × ℝ)`. -/
abbrev ProfilePoint := ℝ × (ℝ × ℝ)
/-- Profile: an abbreviation for `ProfilePoint → ℝ`. -/
abbrev Profile := ProfilePoint → ℝ

/-- Projection, given by `EuclideanSpace.proj i`. -/
def projection (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

@[simp] theorem projection_apply (i : Fin 3) (x : Space) : projection i x = x i := rfl

/-- Radial energy, given by `(x 0 ^ 2 + x 1 ^ 2) / 2`. -/
def radialEnergy (x : Space) : ℝ := (x 0 ^ 2 + x 1 ^ 2) / 2

/-- Profile point, given by `(t, (radialEnergy x, x 2))`. -/
def profilePoint (t : ℝ) (x : Space) : ProfilePoint := (t, (radialEnergy x, x 2))

/-- Partial S, given by `fderiv ℝ F p (0, (1, 0))`. -/
def partialS (F : Profile) (p : ProfilePoint) : ℝ := fderiv ℝ F p (0, (1, 0))
/-- Partial Z, given by `fderiv ℝ F p (0, (0, 1))`. -/
def partialZ (F : Profile) (p : ProfilePoint) : ℝ := fderiv ℝ F p (0, (0, 1))

/-- Potential as an element of `VelocityField`. -/
def potential (H K : Profile) : VelocityField := fun w =>
  ((-(1 / 2) : ℝ) * (w.2 1 * H (profilePoint w.1 w.2))) • coordinateVector 0 +
  ((1 / 2 : ℝ) * (w.2 0 * H (profilePoint w.1 w.2))) • coordinateVector 1 +
  K (profilePoint w.1 w.2) • coordinateVector 2

/-- Velocity, given by `SpatialCurl.spatialCurl (potential H K)`. -/
def velocity (H K : Profile) : VelocityField := SpatialCurl.spatialCurl (potential H K)

theorem radialEnergy_nonneg (x : Space) : 0 ≤ radialEnergy x := by
  exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)

theorem contDiff_radialEnergy {n : WithTop ℕ∞} : ContDiff ℝ n radialEnergy := by
  exact (((projection 0).contDiff.pow 2).add
    ((projection 1).contDiff.pow 2)).div_const 2

theorem contDiff_profilePoint {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun w : SpaceTime => profilePoint w.1 w.2) :=
  contDiff_fst.prodMk ((contDiff_radialEnergy.comp contDiff_snd).prodMk
    ((projection 2).contDiff.comp contDiff_snd))

theorem contDiff_profilePoint_slice (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (profilePoint t) :=
  contDiff_const.prodMk (contDiff_radialEnergy.prodMk (projection 2).contDiff)

/-- Radial linear, given by `x 0 • projection 0 + x 1 • projection 1`. -/
def radialLinear (x : Space) : Space →L[ℝ] ℝ :=
  x 0 • projection 0 + x 1 • projection 1

theorem hasFDerivAt_radialEnergy (x : Space) : HasFDerivAt radialEnergy (radialLinear x) x := by
  have h0 := (projection 0).hasFDerivAt (x := x)
  have h1 := (projection 1).hasFDerivAt (x := x)
  convert! ((h0.fun_mul h0).fun_add (h1.fun_mul h1)).mul_const (1 / 2 : ℝ) using 1
  · funext y
    simp only [radialEnergy, projection_apply]
    ring
  · ext v
    simp [radialLinear]
    ring

/-- Profile jacobian, given by `(0 : Space →L[ℝ] ℝ).prod ((radialLinear x).prod (projection
2))`. -/
def profileJacobian (x : Space) : Space →L[ℝ] ProfilePoint :=
  (0 : Space →L[ℝ] ℝ).prod ((radialLinear x).prod (projection 2))

theorem hasFDerivAt_profilePoint (t : ℝ) (x : Space) :
    HasFDerivAt (profilePoint t) (profileJacobian x) x :=
  (hasFDerivAt_const t x).prodMk
    ((hasFDerivAt_radialEnergy x).prodMk (projection 2).hasFDerivAt)

@[simp] theorem profileJacobian_apply (x v : Space) :
    profileJacobian x v = (0, (x 0 * v 0 + x 1 * v 1, v 2)) := by
  simp [profileJacobian, radialLinear]

/-- Profile derivative, given by `(fderiv ℝ F (profilePoint t x)).comp (profileJacobian x)`. -/
def profileDerivative (F : Profile) (t : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (fderiv ℝ F (profilePoint t x)).comp (profileJacobian x)

theorem hasFDerivAt_profile_composition (F : Profile) (t : ℝ) (x : Space)
    (hF : DifferentiableAt ℝ F (profilePoint t x)) :
    HasFDerivAt (fun y => F (profilePoint t y)) (profileDerivative F t x) x :=
  hF.hasFDerivAt.comp x (hasFDerivAt_profilePoint t x)

theorem profileDerivative_apply (F : Profile) (t : ℝ) (x v : Space) :
    profileDerivative F t x v =
      (x 0 * v 0 + x 1 * v 1) * partialS F (profilePoint t x) +
        v 2 * partialZ F (profilePoint t x) := by
  unfold profileDerivative
  rw [ContinuousLinearMap.comp_apply, profileJacobian_apply]
  have hsplit : (0, (x 0 * v 0 + x 1 * v 1, v 2)) =
      (x 0 * v 0 + x 1 * v 1) • ((0, (1, 0)) : ProfilePoint) +
        v 2 • ((0, (0, 1)) : ProfilePoint) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul]
  rfl

/-- Potential jacobian as an element of `Space →L[ℝ] Space`. -/
def potentialJacobian (H K : Profile) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  ((-(1 / 2) : ℝ) •
    (x 1 • profileDerivative H t x + H (profilePoint t x) • projection 1)).smulRight
      (coordinateVector 0) +
  ((1 / 2 : ℝ) •
    (x 0 • profileDerivative H t x + H (profilePoint t x) • projection 0)).smulRight
      (coordinateVector 1) +
  (profileDerivative K t x).smulRight (coordinateVector 2)

theorem hasFDerivAt_potential (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) :
    HasFDerivAt (fun y => potential H K (t, y)) (potentialJacobian H K t x) x := by
  have hHv := hasFDerivAt_profile_composition H t x hH
  have hKv := hasFDerivAt_profile_composition K t x hK
  exact ((((projection 1).hasFDerivAt.mul hHv).const_mul (-(1 / 2))).smul_const
      (coordinateVector 0)).add
    (((((projection 0).hasFDerivAt.mul hHv).const_mul (1 / 2)).smul_const
      (coordinateVector 1))) |>.add (hKv.smul_const (coordinateVector 2))

theorem velocity_zero (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) :
    velocity H K (t, x) 0 =
      -x 0 * partialZ H (profilePoint t x) / 2 + x 1 * partialS K (profilePoint t x) := by
  change (SpatialCurl.curlLinear (fderiv ℝ (fun y => potential H K (t, y)) x)) 0 = _
  rw [(hasFDerivAt_potential H K t x hH hK).fderiv, SpatialCurl.curlLinear_apply_zero]
  simp only [Fin.isValue, potentialJacobian, one_div, smul_add, neg_smul, coordinateVector,
      add_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, smul_apply, profileDerivative_apply, ne_eq,
        zero_ne_one,
    not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, PiLp.single_eq_same, mul_one, zero_add,
        Fin.reduceEq, zero_mul,
    add_zero, smul_eq_mul, projection_apply, PiLp.add_apply, PiLp.smul_apply, one_mul, neg_zero,
        PiLp.neg_apply,
    one_ne_zero, neg_mul]
  ring

theorem velocity_one (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) :
    velocity H K (t, x) 1 =
      -x 1 * partialZ H (profilePoint t x) / 2 - x 0 * partialS K (profilePoint t x) := by
  change (SpatialCurl.curlLinear (fderiv ℝ (fun y => potential H K (t, y)) x)) 1 = _
  rw [(hasFDerivAt_potential H K t x hH hK).fderiv, SpatialCurl.curlLinear_apply_one]
  simp only [Fin.isValue, potentialJacobian, one_div, smul_add, neg_smul, coordinateVector,
      add_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, smul_apply, profileDerivative_apply, ne_eq,
        Fin.reduceEq,
    not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, add_zero, zero_mul, PiLp.single_eq_same,
        one_mul, zero_add,
    smul_eq_mul, projection_apply, neg_zero, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
        mul_one, zero_ne_one,
    one_ne_zero, neg_mul, sub_left_inj]
  ring

theorem velocity_two (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) :
    velocity H K (t, x) 2 =
      H (profilePoint t x) + radialEnergy x * partialS H (profilePoint t x) := by
  change (SpatialCurl.curlLinear (fderiv ℝ (fun y => potential H K (t, y)) x)) 2 = _
  rw [(hasFDerivAt_potential H K t x hH hK).fderiv, SpatialCurl.curlLinear_apply_two]
  simp only [Fin.isValue, potentialJacobian, one_div, smul_add, neg_smul, coordinateVector,
      add_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, smul_apply, profileDerivative_apply,
        PiLp.single_eq_same, mul_one,
    ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq,
        zero_mul,
    smul_eq_mul, projection_apply, neg_zero, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
        zero_add, zero_ne_one]
  unfold radialEnergy
  ring

/-- The Cartesian potential is smooth on all of space, including the axis. -/
theorem contDiff_potential {H K : Profile} {n : WithTop ℕ∞}
    (hH : ContDiff ℝ n H) (hK : ContDiff ℝ n K) : ContDiff ℝ n (potential H K) := by
  have h0 : ContDiff ℝ n (fun w : SpaceTime => w.2 0) :=
    (projection 0).contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ n (fun w : SpaceTime => w.2 1) :=
    (projection 1).contDiff.comp contDiff_snd
  have hHv := hH.comp contDiff_profilePoint
  have hKv := hK.comp contDiff_profilePoint
  exact (((contDiff_const.mul (h1.mul hHv)).smul contDiff_const).add
    ((contDiff_const.mul (h0.mul hHv)).smul contDiff_const)).add
    (hKv.smul contDiff_const)

/-- Smoothness may be required only on a prescribed set of times. -/
theorem contDiffOn_potential {H K : Profile} {times : Set ℝ} {n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H (times ×ˢ (univ : Set (ℝ × ℝ))))
    (hK : ContDiffOn ℝ n K (times ×ˢ (univ : Set (ℝ × ℝ)))) :
    ContDiffOn ℝ n (potential H K) (times ×ˢ (univ : Set Space)) := by
  have hm : MapsTo (fun w : SpaceTime => profilePoint w.1 w.2)
      (times ×ˢ (univ : Set Space)) (times ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro w hw
    exact ⟨hw.1, mem_univ _⟩
  have h0 : ContDiffOn ℝ n (fun w : SpaceTime => w.2 0) (times ×ˢ univ) :=
    ((projection 0).contDiff.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ n (fun w : SpaceTime => w.2 1) (times ×ˢ univ) :=
    ((projection 1).contDiff.comp contDiff_snd).contDiffOn
  have hHv := hH.comp contDiff_profilePoint.contDiffOn hm
  have hKv := hK.comp contDiff_profilePoint.contDiffOn hm
  exact (((contDiffOn_const.mul (h1.mul hHv)).smul contDiffOn_const).add
    ((contDiffOn_const.mul (h0.mul hHv)).smul contDiffOn_const)).add
    (hKv.smul contDiffOn_const)

theorem contDiff_velocity {H K : Profile} {m n : WithTop ℕ∞}
    (hH : ContDiff ℝ n H) (hK : ContDiff ℝ n K) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (velocity H K) :=
  SpatialCurl.contDiff_spatialCurl (contDiff_potential hH hK) hmn

theorem smooth_velocity {H K : Profile}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (velocity H K) :=
  contDiff_velocity hH hK (by simp)

theorem contDiffOn_velocity {H K : Profile} {times : Set ℝ} {m n : WithTop ℕ∞}
    (hH : ContDiffOn ℝ n H (times ×ˢ (univ : Set (ℝ × ℝ))))
    (hK : ContDiffOn ℝ n K (times ×ˢ (univ : Set (ℝ × ℝ)))) (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (velocity H K) (times ×ˢ (univ : Set Space)) :=
  SpatialCurl.contDiffOn_spatialCurl (contDiffOn_potential hH hK) hmn

theorem divergence_velocity {H K : Profile}
    (hH : ContDiff ℝ 2 H) (hK : ContDiff ℝ 2 K) (t : ℝ) (x : Space) :
    spatialDivergence (velocity H K) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl (potential H K) t x
    (((contDiff_potential hH hK).comp (contDiff_const.prodMk contDiff_id)).contDiffAt)

theorem divergence_velocity_on {H K : Profile} {times : Set ℝ}
    (hH : ContDiffOn ℝ 2 H (times ×ˢ (univ : Set (ℝ × ℝ))))
    (hK : ContDiffOn ℝ 2 K (times ×ˢ (univ : Set (ℝ × ℝ))))
    {t : ℝ} (ht : t ∈ times) (x : Space) : spatialDivergence (velocity H K) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl_on (contDiffOn_potential hH hK) ht x

/-- On the axis the field is purely axial with value `H(t,0,z)`, with no
limit or removable-singularity argument required. -/
theorem velocity_on_axis (H K : Profile) (t : ℝ) (x : Space)
    (hH : DifferentiableAt ℝ H (profilePoint t x))
    (hK : DifferentiableAt ℝ K (profilePoint t x)) (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    velocity H K (t, x) = H (t, (0, x 2)) • coordinateVector 2 := by
  ext i
  fin_cases i
  · change velocity H K (t, x) 0 = (H (t, (0, x 2)) • coordinateVector 2) 0
    rw [velocity_zero H K t x hH hK]
    simp [hx0, hx1, coordinateVector]
  · change velocity H K (t, x) 1 = (H (t, (0, x 2)) • coordinateVector 2) 1
    rw [velocity_one H K t x hH hK]
    simp [hx0, hx1, coordinateVector]
  · change velocity H K (t, x) 2 = (H (t, (0, x 2)) • coordinateVector 2) 2
    rw [velocity_two H K t x hH hK]
    simp [profilePoint, radialEnergy, hx0, hx1, coordinateVector]

/-- The potential's closed spatial support is controlled by the two profile
supports, pulled back under the smooth `(t,s,z)` coordinate map. -/
theorem tsupport_potential_slice_subset (H K : Profile) (t : ℝ) :
    tsupport (fun x : Space => potential H K (t, x)) ⊆
      profilePoint t ⁻¹' (tsupport H ∪ tsupport K) := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    have hnH : profilePoint t x ∉ tsupport H := fun h => hn (Or.inl h)
    have hnK : profilePoint t x ∉ tsupport K := fun h => hn (Or.inr h)
    have hHzero := image_eq_zero_of_notMem_tsupport hnH
    have hKzero := image_eq_zero_of_notMem_tsupport hnK
    exact hx (by simp [potential, hHzero, hKzero])
  · exact ((isClosed_tsupport H).union (isClosed_tsupport K)).preimage
      (contDiff_profilePoint_slice t (n := 0)).continuous

/-- Taking the actual curl does not enlarge this closed spatial support. -/
theorem tsupport_velocity_slice_subset (H K : Profile) (t : ℝ) :
    tsupport (fun x : Space => velocity H K (t, x)) ⊆
      profilePoint t ⁻¹' (tsupport H ∪ tsupport K) :=
  (SpatialCurl.tsupport_curl_subset (fun x : Space => potential H K (t, x))).trans
    (tsupport_potential_slice_subset H K t)

theorem velocity_eq_zero_outside_profile_support (H K : Profile) (t : ℝ) (x : Space)
    (hH : profilePoint t x ∉ tsupport H) (hK : profilePoint t x ∉ tsupport K) :
    velocity H K (t, x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport (f := fun y : Space => velocity H K (t, y))
  intro hx
  rcases tsupport_velocity_slice_subset H K t hx with h | h
  · exact hH h
  · exact hK h

/-- The Cartesian cylinder cut out by bounds on `s` and `z` is compact. -/
theorem isCompact_cylinder (R Z : ℝ) :
    IsCompact {x : Space | radialEnergy x ≤ R ∧ |x 2| ≤ Z} := by
  have hc : IsClosed {x : Space | radialEnergy x ≤ R ∧ |x 2| ≤ Z} :=
    (isClosed_le (contDiff_radialEnergy (n := 0)).continuous continuous_const).inter
      (isClosed_le (projection 2).continuous.abs continuous_const)
  apply (isCompact_closedBall (0 : Space) (Real.sqrt (2 * R + Z ^ 2))).of_isClosed_subset hc
  intro x hx
  have hz : (x 2) ^ 2 ≤ Z ^ 2 := by
    have hZ : 0 ≤ Z := (abs_nonneg (x 2)).trans hx.2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 2)) hZ).2 hx.2
  have hs : (∑ i : Fin 3, (x i) ^ 2) ≤ 2 * R + Z ^ 2 := by
    rw [Fin.sum_univ_three]
    have hr := hx.1
    dsimp [radialEnergy] at hr
    linarith
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simpa only [Real.norm_eq_abs, sq_abs] using hs

/-- Bounds on profile support give a literal closed cylinder in Cartesian
space: `s ≤ R` and `|z| ≤ Z`. -/
theorem tsupport_velocity_cylinder_subset (H K : Profile) (t R Z : ℝ)
    (hH : tsupport H ⊆ {p : ProfilePoint | p.2.1 ≤ R ∧ |p.2.2| ≤ Z})
    (hK : tsupport K ⊆ {p : ProfilePoint | p.2.1 ≤ R ∧ |p.2.2| ≤ Z}) :
    tsupport (fun x : Space => velocity H K (t, x)) ⊆
      {x : Space | radialEnergy x ≤ R ∧ |x 2| ≤ Z} := by
  intro x hx
  rcases tsupport_velocity_slice_subset H K t hx with h | h
  · exact hH h
  · exact hK h

theorem hasCompactSupport_velocity_of_profile_bounds (H K : Profile) (t R Z : ℝ)
    (hH : tsupport H ⊆ {p : ProfilePoint | p.2.1 ≤ R ∧ |p.2.2| ≤ Z})
    (hK : tsupport K ⊆ {p : ProfilePoint | p.2.1 ≤ R ∧ |p.2.2| ≤ Z}) :
    HasCompactSupport (fun x : Space => velocity H K (t, x)) :=
  (isCompact_cylinder R Z).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_velocity_cylinder_subset H K t R Z hH hK)

end NavierStokes.AxisymmetricFields
