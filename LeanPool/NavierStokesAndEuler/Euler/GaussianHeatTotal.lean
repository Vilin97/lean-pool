/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatSmoothing

@[expose] public section

/-! The genuine four-coordinate cylinder heat semigroup and simultaneous derivative gain. -/

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse
  EulerCylinderSobolev
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A finite product of commuting directional Gaussian averages. -/
def heatList (directions : List LiftTangent) (v : ℝ≥0) (f : LiftL2 period) : LiftL2 period :=
  match directions with
  | [] => f
  | a :: tail => lineHeat period a v (heatList tail v f)

theorem heatList_norm_le (directions : List LiftTangent) (v : ℝ≥0) (f : LiftL2 period) :
    ‖heatList period directions v f‖ ≤ ‖f‖ := by
  induction directions with
  | nil => rfl
  | cons a tail ih => exact (lineHeat_norm_le period a v _).trans ih

theorem heatList_add (directions : List LiftTangent) (v : ℝ≥0) (f g : LiftL2 period) :
    heatList period directions v (f+g) = heatList period directions v f + heatList period
      directions v g := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [heatList, ih, lineHeat_add]

theorem heatList_smul (directions : List LiftTangent) (v : ℝ≥0) (c : ℝ) (f : LiftL2 period) :
    heatList period directions v (c • f) = c • heatList period directions v f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [heatList, ih, lineHeat_smul]

def heatListOperator (directions : List LiftTangent) (v : ℝ≥0) : LiftL2 period →L[ℝ] LiftL2 period
  :=
  LinearMap.mkContinuous
    { toFun := heatList period directions v
      map_add' := heatList_add period directions v
      map_smul' := heatList_smul period directions v }
    1 (fun f => by simpa using heatList_norm_le period directions v f)

@[simp] theorem heatListOperator_apply (directions : List LiftTangent) (v : ℝ≥0) (f : LiftL2
  period) :
    heatListOperator period directions v f = heatList period directions v f := rfl

theorem heatList_translation (directions : List LiftTangent) (v : ℝ≥0) (b : LiftDomain period) (f :
  LiftL2 period) :
    translation period b (heatList period directions v f) = heatList period directions v
      (translation period b f) := by
  induction directions with
  | nil => rfl
  | cons a tail ih => rw [heatList, heatList, lineHeat_translation, ih]

/-- Every finite heat product commutes with every directional average. -/
theorem heatList_lineHeat_commute (directions : List LiftTangent) (a : LiftTangent)
    (v w : ℝ≥0) (f : LiftL2 period) :
    heatList period directions v (lineHeat period a w f) = lineHeat period a w (heatList period
      directions v f) := by
  induction directions with
  | nil => rfl
  | cons b tail ih => rw [heatList, heatList, ih, lineHeat_commute]

@[simp] theorem heatList_zero (directions : List LiftTangent) (f : LiftL2 period) :
    heatList period directions 0 f = f := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [heatList, lineHeat_zero, ih]

/-- The finite product is itself a semigroup with additive variance. -/
theorem heatList_semigroup (directions : List LiftTangent) (v w : ℝ≥0) (f : LiftL2 period) :
    heatList period directions v (heatList period directions w f) = heatList period directions
      (v+w) f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    rw [heatList, heatList, heatList, heatList_lineHeat_commute, lineHeat_semigroup, ih]

/-- A Lipschitz estimate for the Gaussian operator in its input field. -/
theorem lineHeat_dist_le (a : LiftTangent) (v : ℝ≥0) (f g : LiftL2 period) :
    dist (lineHeat period a v f) (lineHeat period a v g) ≤ dist f g := by
  change dist (lineHeatOperator period a v f) (lineHeatOperator period a v g) ≤ dist f g
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact lineHeat_norm_le period a v (f-g)

/-- Joint continuity follows from contraction in the field and strong continuity in variance. -/
theorem lineHeat_joint_continuous (a : LiftTangent) :
    Continuous (fun p : ℝ≥0 × LiftL2 period => lineHeat period a p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime : ContinuousAt (fun v : ℝ≥0 => lineHeat period a v p.2) p.1 :=
    (lineHeat_continuous period a p.2).continuousAt
  have ht := (Metric.continuousAt_iff.mp htime) (ε/2) (by linarith)
  obtain ⟨δ, hδ, hδbound⟩ := ht
  refine ⟨min δ (ε/2), lt_min hδ (by linarith), ?_⟩
  intro q hq
  have htimeclose : dist q.1 p.1 < δ := (show dist q.1 p.1 ≤ dist q p by exact le_max_left _
    _).trans_lt ((lt_min_iff.mp hq).1)
  have hfieldclose : dist q.2 p.2 < ε/2 := (show dist q.2 p.2 ≤ dist q p by exact le_max_right _
    _).trans_lt ((lt_min_iff.mp hq).2)
  have h := dist_triangle (lineHeat period a q.1 q.2) (lineHeat period a q.1 p.2) (lineHeat period
    a p.1 p.2)
  have ha := lineHeat_dist_le period a q.1 q.2 p.2
  have hb := hδbound htimeclose
  linarith

theorem heatList_continuous (directions : List LiftTangent) (f : LiftL2 period) :
    Continuous (fun v : ℝ≥0 => heatList period directions v f) := by
  induction directions with
  | nil => exact continuous_const
  | cons a tail ih => exact (lineHeat_joint_continuous period a).comp (continuous_id.prodMk ih)

/-- A finite heat product gains a derivative in each direction included in the product. -/
theorem heatList_one_derivative (directions : List LiftTangent) (a : LiftTangent)
    (ha : a ∈ directions) {v : ℝ≥0} (hv : 0 < v) (f : LiftL2 period) :
    ∃ g : LiftL2 period,
      HasDerivAt (lineOrbit period a (heatList period directions v f)) g 0 ∧
      ‖g‖ ≤ (gaussianAbsMoment 1 / Real.sqrt (v : ℝ)) * ‖f‖ := by
  induction directions with
  | nil => simp at ha
  | cons b tail ih =>
    rcases List.mem_cons.mp ha with hab | hat
    · subst b
      obtain ⟨g, hg, hgb⟩ := lineHeat_one_derivative period a hv (heatList period tail v f)
      refine ⟨g, hg, hgb.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (heatList_norm_le period tail v f)
        (div_nonneg (gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _))
    · obtain ⟨g, hg, hgb⟩ := ih hat
      refine ⟨lineHeat period b v g, lineHeat_strongDerivative period b a v _ g hg, ?_⟩
      exact (lineHeat_norm_le period b v g).trans hgb

/-- The four actual commuting standard coordinate directions on R³×T. -/
def cylinderDirections : List LiftTangent := List.ofFn standardDirection

/-- The actual cylinder heat semigroup, parameterized by Gaussian variance. -/
def cylinderHeat (v : ℝ≥0) : LiftL2 period →L[ℝ] LiftL2 period :=
  heatListOperator period cylinderDirections v

theorem cylinderHeat_norm_le (v : ℝ≥0) (f : LiftL2 period) : ‖cylinderHeat period v f‖ ≤ ‖f‖ :=
  heatList_norm_le period cylinderDirections v f

@[simp] theorem cylinderHeat_zero (f : LiftL2 period) : cylinderHeat period 0 f = f :=
  heatList_zero period cylinderDirections f

theorem cylinderHeat_semigroup (v w : ℝ≥0) (f : LiftL2 period) :
    cylinderHeat period v (cylinderHeat period w f) = cylinderHeat period (v+w) f :=
  heatList_semigroup period cylinderDirections v w f

theorem cylinderHeat_continuous (f : LiftL2 period) : Continuous (fun v : ℝ≥0 => cylinderHeat
  period v f) :=
  heatList_continuous period cylinderDirections f

theorem cylinderHeat_translation (v : ℝ≥0) (a : LiftDomain period) (f : LiftL2 period) :
    cylinderHeat period v (translation period a f) = translation period a (cylinderHeat period v f)
      :=
  (heatList_translation period cylinderDirections v a f).symm

/-- The actual heat average gains all four first derivatives with a uniform parabolic bound. -/
theorem cylinderHeat_one_derivative {v : ℝ≥0} (hv : 0 < v) (f : LiftL2 period) (i : Fin 4) :
    ∃ g : LiftL2 period,
      HasDerivAt (lineOrbit period (standardDirection i) (cylinderHeat period v f)) g 0 ∧
      ‖g‖ ≤ (gaussianAbsMoment 1 / Real.sqrt (v : ℝ)) * ‖f‖ := by
  exact heatList_one_derivative period cylinderDirections (standardDirection i)
    (List.mem_ofFn.mpr ⟨i, rfl⟩) hv f

end EulerGaussianCylinderHeat
