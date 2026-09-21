/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.CoordinateSecondVariation

/-!
# Broken endpoint-fixed variations

This module constructs the local coordinate ingredients for a finite broken
variation.  At each partition node we use a genuine short geodesic in the
variation parameter.  Its intrinsic second acceleration is zero, so every
piecewise second-variation endpoint term vanishes without requiring a hidden
smoothness assumption at the joins.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

namespace LocalSecondOrderSolution

variable {F : E → E → E} {z u : E}
/-- A `C¹` second-order system has a `C²` position curve at its initial
time. -/
theorem contDiffAt_curve_two_of_contDiffAt
    (sol : LocalSecondOrderSolution F z u)
    (hF : ContDiffAt ℝ 1
      (fun q : E × E ↦ secondOrderSystem F q) (z, u)) :
    ContDiffAt ℝ 2 sol.curve 0 := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ) + 1 by norm_num,
    contDiffAt_succ_iff_hasFDerivAt]
  let D : ℝ → ℝ →L[ℝ] E := fun t ↦
    ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity t)
  refine ⟨D, ?_, ?_⟩
  · have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [sol.radius_pos]
    exact ⟨Ioo (-sol.radius) sol.radius,
      isOpen_Ioo.mem_nhds hzero, fun t ht ↦
        (sol.curve_hasDeriv t ht).hasFDerivAt⟩
  · have hvel : ContDiffAt ℝ 1 sol.velocity 0 :=
      sol.contDiffAt_velocity_of_contDiffAt hF
    change ContDiffAt ℝ 1
      ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)) ∘
        sol.velocity) 0
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := E)).contDiff.contDiffAt.comp 0 hvel

end LocalSecondOrderSolution

variable {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]

/-- In any fixed chart, every tangent coordinate state has a local coordinate
geodesic node path.  Its second coordinate derivative has zero intrinsic
covariant acceleration, exactly the endpoint condition needed by the broken
second-variation argument. -/
theorem exists_coordinateGeodesicNodePath
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {z : E} (hz : z ∈ (extChartAt I x₀).target) (j : E) :
    ∃ sol : LocalSecondOrderSolution
        (coordinateAcceleration (I := I) (M := M) cov x₀ b) z j,
      (∀ᶠ e in nhds (0 : ℝ), sol.curve e ∈ (extChartAt I x₀).target) ∧
      ContDiffAt ℝ 2 sol.curve 0 ∧
      HasDerivAt sol.curve j 0 ∧
      HasDerivAt sol.velocity
        (-coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b z j j) 0 ∧
      coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ b z j j
          (-coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b z j j) = 0 := by
  have hsystem := coordinateAcceleration_system_contDiffAt_of_mem_target
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) hz j
  obtain ⟨sol⟩ := exists_localSecondOrderSolution_of_contDiffAt hsystem
  refine ⟨sol, ?_, sol.contDiffAt_curve_two_of_contDiffAt hsystem, ?_, ?_, ?_⟩
  · have hcont : ContinuousAt sol.curve 0 := by
      have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
        constructor <;> linarith [sol.radius_pos]
      exact (sol.curve_hasDeriv 0 hzero).continuousAt
    have htarget : (extChartAt I x₀).target ∈ nhds (sol.curve 0) := by
      rw [sol.initial_curve]
      exact (isOpen_extChartAt_target (I := I) x₀).mem_nhds hz
    exact hcont.eventually htarget
  · have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [sol.radius_pos]
    simpa [sol.initial_velocity] using sol.curve_hasDeriv 0 hzero
  · have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [sol.radius_pos]
    have h := sol.velocity_hasDeriv 0 hzero
    rw [sol.initial_curve, sol.initial_velocity,
      coordinateAcceleration_eq_neg_connectionTerm,
      ← coordinateParallelOperator_self_eq_coordinateConnectionTerm] at h
    exact h
  · simp [coordinateCovariantFieldDerivative]

/-! ### Affine endpoint interpolation in one chart -/

/-- A globally smooth coordinate node path with prescribed position, first
variation, and second variation at zero. -/
def coordinateSecondOrderNodePath (z j c : E) (e : ℝ) : E :=
  z + e • j + (e ^ 2 / 2) • c

/-- Velocity of `coordinateSecondOrderNodePath`. -/
def coordinateSecondOrderNodeVelocity (j c : E) (e : ℝ) : E :=
  j + e • c

@[simp] theorem coordinateSecondOrderNodePath_zero (z j c : E) :
    coordinateSecondOrderNodePath z j c 0 = z := by
  simp [coordinateSecondOrderNodePath]

@[simp] theorem coordinateSecondOrderNodeVelocity_zero (j c : E) :
    coordinateSecondOrderNodeVelocity j c 0 = j := by
  simp [coordinateSecondOrderNodeVelocity]

theorem coordinateSecondOrderNodePath_hasDerivAt (z j c : E) (e : ℝ) :
    HasDerivAt (coordinateSecondOrderNodePath z j c)
      (coordinateSecondOrderNodeVelocity j c e) e := by
  have hsquare : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) e e := by
    have hpow : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * e) e := by
      simpa using (hasDerivAt_pow (𝕜 := ℝ) 2 e)
    have hdiv : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) ((2 * e) / 2) e :=
      hpow.div_const 2
    convert hdiv using 1 <;> ring
  have hmain := (hasDerivAt_const e z).add
      ((hasDerivAt_id e).smul_const j) |>.add (hsquare.smul_const c)
  convert hmain using 1
  · funext s
    rfl
  · simp [coordinateSecondOrderNodeVelocity]

theorem coordinateSecondOrderNodeVelocity_hasDerivAt (j c : E) (e : ℝ) :
    HasDerivAt (coordinateSecondOrderNodeVelocity j c) c e := by
  have hmain := (hasDerivAt_const e j).add ((hasDerivAt_id e).smul_const c)
  convert hmain using 1
  · funext s
    rfl
  · simp

theorem coordinateSecondOrderNodePath_contDiff :
    ContDiff ℝ ∞ (coordinateSecondOrderNodePath (E := E) z u c) := by
  unfold coordinateSecondOrderNodePath
  fun_prop

theorem coordinateSecondOrderNodeVelocity_contDiff :
    ContDiff ℝ ∞ (coordinateSecondOrderNodeVelocity (E := E) u c) := by
  unfold coordinateSecondOrderNodeVelocity
  fun_prop

/-- Affine weight of the left endpoint of `[a,b]`. -/
def brokenVariationLeftWeight (a b t : ℝ) : ℝ := (b - t) / (b - a)

/-- Affine weight of the right endpoint of `[a,b]`. -/
def brokenVariationRightWeight (a b t : ℝ) : ℝ := (t - a) / (b - a)

@[simp] theorem brokenVariationLeftWeight_left {a b : ℝ} (hab : a < b) :
    brokenVariationLeftWeight a b a = 1 := by
  simp [brokenVariationLeftWeight, ne_of_gt (sub_pos.mpr hab)]

@[simp] theorem brokenVariationLeftWeight_right {a b : ℝ} (_hab : a < b) :
    brokenVariationLeftWeight a b b = 0 := by
  simp [brokenVariationLeftWeight]

@[simp] theorem brokenVariationRightWeight_left {a b : ℝ} (_hab : a < b) :
    brokenVariationRightWeight a b a = 0 := by
  simp [brokenVariationRightWeight]

@[simp] theorem brokenVariationRightWeight_right {a b : ℝ} (hab : a < b) :
    brokenVariationRightWeight a b b = 1 := by
  simp [brokenVariationRightWeight, ne_of_gt (sub_pos.mpr hab)]

theorem hasDerivAt_brokenVariationLeftWeight (a b t : ℝ) :
    HasDerivAt (brokenVariationLeftWeight a b) (-(b - a)⁻¹) t := by
  unfold brokenVariationLeftWeight
  simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div, one_div] using
    ((hasDerivAt_const t b).sub (hasDerivAt_id t)).div_const (b - a)

theorem hasDerivAt_brokenVariationRightWeight (a b t : ℝ) :
    HasDerivAt (brokenVariationRightWeight a b) ((b - a)⁻¹) t := by
  unfold brokenVariationRightWeight
  simpa only [Pi.sub_apply, id_eq, sub_zero, one_div] using
    ((hasDerivAt_id t).sub (hasDerivAt_const t a)).div_const (b - a)

/-- Coordinate residual between a moving node and the first-order motion
prescribed by the variational field at that node. -/
def brokenVariationNodeResidual
    (node : ℝ → E) (z j : E) (e : ℝ) : E :=
  node e - z - e • j

/-- One chart piece of the endpoint-spliced broken variation. -/
def coordinateBrokenVariationPiece
    (a b : ℝ) (z j : ℝ → E)
    (leftNode rightNode : ℝ → E) (e t : ℝ) : E :=
  z t + e • j t +
    brokenVariationLeftWeight a b t •
      brokenVariationNodeResidual leftNode (z a) (j a) e +
    brokenVariationRightWeight a b t •
      brokenVariationNodeResidual rightNode (z b) (j b) e

/-- Coordinate time derivative displayed for a broken variation piece. -/
def coordinateBrokenVariationVelocity
    (a b : ℝ) (z' j' : ℝ → E)
    (z j : ℝ → E) (leftNode rightNode : ℝ → E)
    (e t : ℝ) : E :=
  z' t + e • j' t - (b - a)⁻¹ •
      brokenVariationNodeResidual leftNode (z a) (j a) e +
    (b - a)⁻¹ •
      brokenVariationNodeResidual rightNode (z b) (j b) e

/-- Coordinate variation field displayed for a broken variation piece. -/
def coordinateBrokenVariationField
    (a b : ℝ) (j : ℝ → E)
    (leftVelocity rightVelocity : ℝ → E) (e t : ℝ) : E :=
  j t + brokenVariationLeftWeight a b t • (leftVelocity e - j a) +
    brokenVariationRightWeight a b t • (rightVelocity e - j b)

/-- Mixed coordinate derivative displayed for a broken variation piece. -/
def coordinateBrokenVariationMixed
    (a b : ℝ) (j' : ℝ → E) (j : ℝ → E)
    (leftVelocity rightVelocity : ℝ → E) (e t : ℝ) : E :=
  j' t - (b - a)⁻¹ • (leftVelocity e - j a) +
    (b - a)⁻¹ • (rightVelocity e - j b)

/-- Second variation-coordinate derivative of a broken piece. -/
def coordinateBrokenVariationSecondField
    (a b : ℝ) (leftAcceleration rightAcceleration : ℝ → E)
    (e t : ℝ) : E :=
  brokenVariationLeftWeight a b t • leftAcceleration e +
    brokenVariationRightWeight a b t • rightAcceleration e

/-- Time derivative displayed for the second variation-coordinate field. -/
def coordinateBrokenVariationSecondMixed
    (a b : ℝ) (leftAcceleration rightAcceleration : ℝ → E)
    (e : ℝ) : E :=
  -(b - a)⁻¹ • leftAcceleration e +
    (b - a)⁻¹ • rightAcceleration e

@[simp] theorem coordinateBrokenVariationSecondField_left
    {a b : ℝ} (hab : a < b)
    (leftAcceleration rightAcceleration : ℝ → E) (e : ℝ) :
    coordinateBrokenVariationSecondField a b
        leftAcceleration rightAcceleration e a = leftAcceleration e := by
  simp [coordinateBrokenVariationSecondField, hab]

@[simp] theorem coordinateBrokenVariationSecondField_right
    {a b : ℝ} (hab : a < b)
    (leftAcceleration rightAcceleration : ℝ → E) (e : ℝ) :
    coordinateBrokenVariationSecondField a b
        leftAcceleration rightAcceleration e b = rightAcceleration e := by
  simp [coordinateBrokenVariationSecondField, hab]

/-- A geodesic left node makes the intrinsic endpoint acceleration of the
broken variation piece vanish. -/
theorem coordinateBrokenVariation_secondCovariantField_left_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b₀ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {a b : ℝ} (hab : a < b) (z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E)
    (hleft : leftAcceleration 0 =
      -coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b₀ (z a) (j a) (j a)) :
    coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ b₀ (z a) (j a) (j a)
        (coordinateBrokenVariationSecondField a b
          leftAcceleration rightAcceleration 0 a) = 0 := by
  rw [coordinateBrokenVariationSecondField_left hab, hleft]
  simp [coordinateCovariantFieldDerivative]

/-- A geodesic right node makes the intrinsic endpoint acceleration of the
broken variation piece vanish. -/
theorem coordinateBrokenVariation_secondCovariantField_right_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b₀ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {a b : ℝ} (hab : a < b) (z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E)
    (hright : rightAcceleration 0 =
      -coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b₀ (z b) (j b) (j b)) :
    coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ b₀ (z b) (j b) (j b)
        (coordinateBrokenVariationSecondField a b
          leftAcceleration rightAcceleration 0 b) = 0 := by
  rw [coordinateBrokenVariationSecondField_right hab, hright]
  simp [coordinateCovariantFieldDerivative]

@[simp] theorem coordinateBrokenVariationPiece_left
    {a b : ℝ} (hab : a < b) (z j : ℝ → E)
    (leftNode rightNode : ℝ → E) (e : ℝ) :
    coordinateBrokenVariationPiece a b z j leftNode rightNode e a =
      leftNode e := by
  simp [coordinateBrokenVariationPiece, brokenVariationNodeResidual, hab]

@[simp] theorem coordinateBrokenVariationPiece_right
    {a b : ℝ} (hab : a < b) (z j : ℝ → E)
    (leftNode rightNode : ℝ → E) (e : ℝ) :
    coordinateBrokenVariationPiece a b z j leftNode rightNode e b =
      rightNode e := by
  simp [coordinateBrokenVariationPiece, brokenVariationNodeResidual, hab]

@[simp] theorem coordinateBrokenVariationPiece_zero
    (a b : ℝ) (z j : ℝ → E) (leftNode rightNode : ℝ → E)
    (hleft : leftNode 0 = z a) (hright : rightNode 0 = z b) (t : ℝ) :
    coordinateBrokenVariationPiece a b z j leftNode rightNode 0 t = z t := by
  simp [coordinateBrokenVariationPiece, brokenVariationNodeResidual,
    hleft, hright]

@[simp] theorem coordinateBrokenVariationVelocity_zero
    (a b : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode : ℝ → E)
    (hleft : leftNode 0 = z a) (hright : rightNode 0 = z b) (t : ℝ) :
    coordinateBrokenVariationVelocity a b z' j' z j
      leftNode rightNode 0 t = z' t := by
  simp [coordinateBrokenVariationVelocity, brokenVariationNodeResidual,
    hleft, hright]

@[simp] theorem coordinateBrokenVariationField_zero
    (a b : ℝ) (j : ℝ → E) (leftVelocity rightVelocity : ℝ → E)
    (hleft : leftVelocity 0 = j a) (hright : rightVelocity 0 = j b) (t : ℝ) :
    coordinateBrokenVariationField a b j leftVelocity rightVelocity 0 t = j t := by
  simp [coordinateBrokenVariationField, hleft, hright]

@[simp] theorem coordinateBrokenVariationMixed_zero
    (a b : ℝ) (j' j : ℝ → E) (leftVelocity rightVelocity : ℝ → E)
    (hleft : leftVelocity 0 = j a) (hright : rightVelocity 0 = j b) (t : ℝ) :
    coordinateBrokenVariationMixed a b j' j leftVelocity rightVelocity 0 t = j' t := by
  simp [coordinateBrokenVariationMixed, hleft, hright]

theorem coordinateBrokenVariationPiece_hasDerivAt_time
    (a b e t : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode : ℝ → E)
    (hz : HasDerivAt z (z' t) t) (hj : HasDerivAt j (j' t) t) :
    HasDerivAt
      (coordinateBrokenVariationPiece a b z j leftNode rightNode e)
      (coordinateBrokenVariationVelocity a b z' j' z j
        leftNode rightNode e t) t := by
  have hleft := (hasDerivAt_brokenVariationLeftWeight a b t).smul_const
    (brokenVariationNodeResidual leftNode (z a) (j a) e)
  have hright := (hasDerivAt_brokenVariationRightWeight a b t).smul_const
    (brokenVariationNodeResidual rightNode (z b) (j b) e)
  have hmain := hz.add (hj.const_smul e) |>.add hleft |>.add hright
  convert hmain using 1
  · funext s
    rfl
  · simp only [coordinateBrokenVariationVelocity, sub_eq_add_neg, neg_smul]

theorem coordinateBrokenVariationSecondField_hasDerivAt_time
    (a b e t : ℝ) (leftAcceleration rightAcceleration : ℝ → E) :
    HasDerivAt
      (coordinateBrokenVariationSecondField a b
        leftAcceleration rightAcceleration e)
      (coordinateBrokenVariationSecondMixed a b
        leftAcceleration rightAcceleration e) t := by
  have hleft := (hasDerivAt_brokenVariationLeftWeight a b t).smul_const
    (leftAcceleration e)
  have hright := (hasDerivAt_brokenVariationRightWeight a b t).smul_const
    (rightAcceleration e)
  convert hleft.add hright using 1
  · funext s
    rfl
  · simp only [coordinateBrokenVariationSecondMixed, sub_eq_add_neg, neg_smul]

theorem brokenVariationNodeResidual_hasDerivAt
    {node velocity : ℝ → E} {z j : E} {e : ℝ}
    (hnode : HasDerivAt node (velocity e) e) :
    HasDerivAt (brokenVariationNodeResidual node z j)
      (velocity e - j) e := by
  have hlinear := (hasDerivAt_id e).smul_const j
  change HasDerivAt (fun s ↦ node s - z - s • j) (velocity e - j) e
  convert (hnode.sub_const z).sub hlinear using 1
  · funext s
    rfl
  · rw [one_smul]

theorem coordinateBrokenVariationPiece_hasDerivAt_parameter
    (a b t : ℝ) (z j : ℝ → E)
    (leftNode rightNode leftVelocity rightVelocity : ℝ → E)
    {e : ℝ}
    (hleft : HasDerivAt leftNode (leftVelocity e) e)
    (hright : HasDerivAt rightNode (rightVelocity e) e) :
    HasDerivAt
      (fun s ↦ coordinateBrokenVariationPiece a b z j
        leftNode rightNode s t)
      (coordinateBrokenVariationField a b j leftVelocity rightVelocity e t) e := by
  have hleftResidual := brokenVariationNodeResidual_hasDerivAt
    (z := z a) (j := j a) hleft
  have hrightResidual := brokenVariationNodeResidual_hasDerivAt
    (z := z b) (j := j b) hright
  have hmain := (hasDerivAt_const e (z t)).add
      ((hasDerivAt_id e).smul_const (j t)) |>.add
      (hleftResidual.const_smul (brokenVariationLeftWeight a b t)) |>.add
      (hrightResidual.const_smul (brokenVariationRightWeight a b t))
  convert hmain using 1
  · funext s
    rfl
  · simp only [coordinateBrokenVariationField, zero_add, one_smul]

theorem coordinateBrokenVariationVelocity_hasDerivAt_parameter
    (a b t : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode leftVelocity rightVelocity : ℝ → E)
    {e : ℝ}
    (hleft : HasDerivAt leftNode (leftVelocity e) e)
    (hright : HasDerivAt rightNode (rightVelocity e) e) :
    HasDerivAt
      (fun s ↦ coordinateBrokenVariationVelocity a b z' j' z j
        leftNode rightNode s t)
      (coordinateBrokenVariationMixed a b j' j
        leftVelocity rightVelocity e t) e := by
  have hleftResidual := brokenVariationNodeResidual_hasDerivAt
    (z := z a) (j := j a) hleft
  have hrightResidual := brokenVariationNodeResidual_hasDerivAt
    (z := z b) (j := j b) hright
  have hmain := (hasDerivAt_const e (z' t)).add
      ((hasDerivAt_id e).smul_const (j' t)) |>.add
      (hleftResidual.const_smul (-(b - a)⁻¹)) |>.add
      (hrightResidual.const_smul ((b - a)⁻¹))
  convert hmain using 1
  · funext s
    simp only [coordinateBrokenVariationVelocity, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      id_eq, sub_eq_add_neg, neg_smul]
  · simp only [coordinateBrokenVariationMixed, zero_add, one_smul,
      sub_eq_add_neg, neg_smul]

theorem coordinateBrokenVariationField_hasDerivAt_parameter
    (a b t : ℝ) (j : ℝ → E)
    (leftVelocity rightVelocity leftAcceleration rightAcceleration : ℝ → E)
    {e : ℝ}
    (hleft : HasDerivAt leftVelocity (leftAcceleration e) e)
    (hright : HasDerivAt rightVelocity (rightAcceleration e) e) :
    HasDerivAt
      (fun s ↦ coordinateBrokenVariationField a b j
        leftVelocity rightVelocity s t)
      (coordinateBrokenVariationSecondField a b
        leftAcceleration rightAcceleration e t) e := by
  have hleft' := hleft.sub_const (j a) |>.const_smul
    (brokenVariationLeftWeight a b t)
  have hright' := hright.sub_const (j b) |>.const_smul
    (brokenVariationRightWeight a b t)
  have hmain := (hasDerivAt_const e (j t)).add hleft' |>.add hright'
  convert hmain using 1
  · funext s
    rfl
  · simp only [coordinateBrokenVariationSecondField, zero_add]

theorem coordinateBrokenVariationMixed_hasDerivAt_parameter
    (a b t : ℝ) (j' j : ℝ → E)
    (leftVelocity rightVelocity leftAcceleration rightAcceleration : ℝ → E)
    {e : ℝ}
    (hleft : HasDerivAt leftVelocity (leftAcceleration e) e)
    (hright : HasDerivAt rightVelocity (rightAcceleration e) e) :
    HasDerivAt
      (fun s ↦ coordinateBrokenVariationMixed a b j' j
        leftVelocity rightVelocity s t)
      (coordinateBrokenVariationSecondMixed a b
        leftAcceleration rightAcceleration e) e := by
  have hleft' := hleft.sub_const (j a) |>.const_smul (-(b - a)⁻¹)
  have hright' := hright.sub_const (j b) |>.const_smul ((b - a)⁻¹)
  have hmain := (hasDerivAt_const e (j' t)).add hleft' |>.add hright'
  convert hmain using 1
  · funext s
    simp only [coordinateBrokenVariationMixed, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      sub_eq_add_neg, neg_smul]
  · simp only [coordinateBrokenVariationSecondMixed, zero_add,
      sub_eq_add_neg, neg_smul]

/-! ### The second-variation boundary field -/

/-- Coordinate representative of the intrinsic second variation
`Dₑ(∂ₑF)` along the base curve. -/
def coordinateBrokenVariationSecondCovariantField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (a b : ℝ) (z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E) (t : ℝ) : E :=
  coordinateBrokenVariationSecondField a b
      leftAcceleration rightAcceleration 0 t +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ basis (z t) (j t) (j t)

/-- Displayed ordinary time derivative of the second-variation boundary
field. -/
def coordinateBrokenVariationSecondCovariantFieldTimeDerivative
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (a b : ℝ) (z' j' z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E) (t : ℝ) : E :=
  coordinateBrokenVariationSecondMixed a b
      leftAcceleration rightAcceleration 0 +
    fderiv ℝ (fun q ↦ coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ basis q (j t) (j t))
      (z t) (z' t) +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ basis (z t) (j' t) (j t) +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ basis (z t) (j t) (j' t)

theorem coordinateBrokenVariationSecondCovariantField_hasDerivAt_time
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (a b t : ℝ) (z' j' z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E)
    (hz : HasDerivAt z (z' t) t) (hj : HasDerivAt j (j' t) t)
    (htarget : z t ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (coordinateBrokenVariationSecondCovariantField
        (I := I) (M := M) cov x₀ basis a b z j
          leftAcceleration rightAcceleration)
      (coordinateBrokenVariationSecondCovariantFieldTimeDerivative
        (I := I) (M := M) cov x₀ basis a b z' j' z j
          leftAcceleration rightAcceleration t) t := by
  have hsecond := coordinateBrokenVariationSecondField_hasDerivAt_time
    a b 0 t leftAcceleration rightAcceleration
  have hP := coordinateParallelOperator_apply_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hz hj hj htarget
  unfold coordinateBrokenVariationSecondCovariantField
    coordinateBrokenVariationSecondCovariantFieldTimeDerivative
  convert hsecond.add hP using 1
  · funext s
    rfl
  · abel

/-- The final term in the pointwise second-variation identity is the ordinary
time derivative of the boundary pairing `<Dₑ∂ₑF, ∂ₜF>`. -/
theorem coordinateBrokenVariationBoundaryPairing_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (a b t : ℝ) (z'' z' j' z j : ℝ → E)
    (leftAcceleration rightAcceleration : ℝ → E)
    (hz : HasDerivAt z (z' t) t) (hz' : HasDerivAt z' (z'' t) t)
    (hj : HasDerivAt j (j' t) t)
    (hgeodesic : coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ basis
        (z t) (z' t) (z' t) (z'' t) = 0)
    (htarget : z t ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k =ᶠ[
        nhds ((extChartAt I x₀).symm (z t))]
        (trivializationAt E TM x₀).localFrame basis k) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
          (coordinateBrokenVariationSecondCovariantField
            (I := I) (M := M) cov x₀ basis a b z j
              leftAcceleration rightAcceleration s)
          ((extChartAt I x₀).symm (z s)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
          (z' s) ((extChartAt I x₀).symm (z s))))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
          (coordinateCovariantFieldDerivative
            (I := I) (M := M) cov x₀ basis (z t) (z' t)
              (coordinateBrokenVariationSecondCovariantField
                (I := I) (M := M) cov x₀ basis a b z j
                  leftAcceleration rightAcceleration t)
              (coordinateBrokenVariationSecondCovariantFieldTimeDerivative
                (I := I) (M := M) cov x₀ basis a b z' j' z j
                  leftAcceleration rightAcceleration t))
          ((extChartAt I x₀).symm (z t)))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
          (z' t) ((extChartAt I x₀).symm (z t)))) t := by
  have hC := coordinateBrokenVariationSecondCovariantField_hasDerivAt_time
    (I := I) (M := M) (E := E) cov x₀ basis a b t z' j' z j
      leftAcceleration rightAcceleration hz hj htarget
  exact coordinate_boundaryPairing_hasDerivAt_of_geodesic
    (I := I) (M := M) (E := E) cov x₀ basis hmetric
      hz hz' hC hgeodesic htarget hframe

/-! ### Covariant first variation of a broken piece -/

/-- The coordinate representative of `Dₑ(∂ₜF)` for one endpoint-spliced
broken variation piece. -/
def coordinateBrokenVariationFirstCovariantField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (a b : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode leftVelocity rightVelocity : ℝ → E)
    (e t : ℝ) : E :=
  coordinateFirstVariationCovariantField
    (I := I) (M := M) cov x₀ basis
    (fun s ↦ coordinateBrokenVariationPiece a b z j
      leftNode rightNode s t)
    (fun s ↦ coordinateBrokenVariationField a b j
      leftVelocity rightVelocity s t)
    (fun s ↦ coordinateBrokenVariationVelocity a b z' j' z j
      leftNode rightNode s t)
    (fun s ↦ coordinateBrokenVariationMixed a b j' j
      leftVelocity rightVelocity s t) e

@[simp] theorem coordinateBrokenVariationFirstCovariantField_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (a b t : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode leftVelocity rightVelocity : ℝ → E)
    (hleftNode : leftNode 0 = z a) (hrightNode : rightNode 0 = z b)
    (hleftVelocity : leftVelocity 0 = j a)
    (hrightVelocity : rightVelocity 0 = j b) :
    coordinateBrokenVariationFirstCovariantField
        (I := I) (M := M) cov x₀ basis a b z' j' z j
        leftNode rightNode leftVelocity rightVelocity 0 t =
      coordinateCovariantFieldDerivative
        (I := I) (M := M) cov x₀ basis
          (z t) (j t) (z' t) (j' t) := by
  simp [coordinateBrokenVariationFirstCovariantField,
    coordinateFirstVariationCovariantField, hleftNode, hrightNode,
    hleftVelocity, hrightVelocity]

/-- Exact variation-parameter derivative of `Dₑ(∂ₜF)` at the base curve.
The displayed value is the `dB` consumed by
`coordinate_secondVariation_inner_identity`. -/
theorem coordinateBrokenVariationFirstCovariantField_hasDerivAt_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (a b t : ℝ) (z' j' z j : ℝ → E)
    (leftNode rightNode leftVelocity rightVelocity
      leftAcceleration rightAcceleration : ℝ → E)
    (hleftNode : HasDerivAt leftNode (leftVelocity 0) 0)
    (hrightNode : HasDerivAt rightNode (rightVelocity 0) 0)
    (hleftVelocity : HasDerivAt leftVelocity (leftAcceleration 0) 0)
    (hrightVelocity : HasDerivAt rightVelocity (rightAcceleration 0) 0)
    (hleftNode0 : leftNode 0 = z a) (hrightNode0 : rightNode 0 = z b)
    (hleftVelocity0 : leftVelocity 0 = j a)
    (hrightVelocity0 : rightVelocity 0 = j b)
    (htarget : z t ∈ (extChartAt I x₀).target) :
    HasDerivAt
      (fun e ↦ coordinateBrokenVariationFirstCovariantField
        (I := I) (M := M) cov x₀ basis a b z' j' z j
        leftNode rightNode leftVelocity rightVelocity e t)
      (coordinateBrokenVariationSecondMixed a b
          leftAcceleration rightAcceleration 0 +
        fderiv ℝ (fun q ↦ coordinateParallelOperator
          (I := I) (M := M) (E := E) cov x₀ basis q (j t) (z' t))
          (z t) (j t) +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ basis (z t)
            (coordinateBrokenVariationSecondField a b
              leftAcceleration rightAcceleration 0 t) (z' t) +
        coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ basis (z t) (j t) (j' t)) 0 := by
  have hQ := coordinateBrokenVariationPiece_hasDerivAt_parameter
    a b t z j leftNode rightNode leftVelocity rightVelocity
      hleftNode hrightNode
  have hW := coordinateBrokenVariationField_hasDerivAt_parameter
    a b t j leftVelocity rightVelocity leftAcceleration rightAcceleration
      hleftVelocity hrightVelocity
  have hV := coordinateBrokenVariationVelocity_hasDerivAt_parameter
    a b t z' j' z j leftNode rightNode leftVelocity rightVelocity
      hleftNode hrightNode
  have hdV := coordinateBrokenVariationMixed_hasDerivAt_parameter
    a b t j' j leftVelocity rightVelocity leftAcceleration rightAcceleration
      hleftVelocity hrightVelocity
  have h := coordinateFirstVariationCovariantField_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hQ hW hV hdV
      (by simpa [hleftNode0, hrightNode0] using htarget)
  simpa [coordinateBrokenVariationFirstCovariantField,
    hleftNode0, hrightNode0, hleftVelocity0, hrightVelocity0] using h

/-! ### Packaged data for one broken piece -/

/-- The coordinate data of one endpoint-spliced variation piece.  Position,
velocity, and acceleration of the two moving endpoint nodes are stored
separately so that the same package can be read in overlapping charts. -/
structure CoordinateBrokenVariationData (E : Type*) where
  a : ℝ
  b : ℝ
  z : ℝ → E
  dz : ℝ → E
  ddz : ℝ → E
  J : ℝ → E
  dJ : ℝ → E
  leftNode : ℝ → E
  rightNode : ℝ → E
  leftVelocity : ℝ → E
  rightVelocity : ℝ → E
  leftAcceleration : ℝ → E
  rightAcceleration : ℝ → E

namespace CoordinateBrokenVariationData

variable (d : CoordinateBrokenVariationData E)

/-- Coordinate position of the packaged variation. -/
def position (e t : ℝ) : E :=
  coordinateBrokenVariationPiece d.a d.b d.z d.J
    d.leftNode d.rightNode e t

/-- Coordinate time velocity of the packaged variation. -/
def velocity (e t : ℝ) : E :=
  coordinateBrokenVariationVelocity d.a d.b d.dz d.dJ d.z d.J
    d.leftNode d.rightNode e t

/-- Coordinate variation field of the packaged variation. -/
def field (e t : ℝ) : E :=
  coordinateBrokenVariationField d.a d.b d.J
    d.leftVelocity d.rightVelocity e t

/-- Coordinate mixed derivative of the packaged variation. -/
def mixed (e t : ℝ) : E :=
  coordinateBrokenVariationMixed d.a d.b d.dJ d.J
    d.leftVelocity d.rightVelocity e t

/-- Coordinate second variation field of the packaged variation. -/
def secondField (e t : ℝ) : E :=
  coordinateBrokenVariationSecondField d.a d.b
    d.leftAcceleration d.rightAcceleration e t

/-- Time derivative of the coordinate second variation field. -/
def secondMixed (e : ℝ) : E :=
  coordinateBrokenVariationSecondMixed d.a d.b
    d.leftAcceleration d.rightAcceleration e

/-- The intrinsic second-variation field along the base curve, in the
coordinates of this piece. -/
def secondCovariantField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (t : ℝ) : E :=
  coordinateBrokenVariationSecondCovariantField
    (I := I) (M := M) cov x₀ basis d.a d.b d.z d.J
      d.leftAcceleration d.rightAcceleration t

/-- The displayed ordinary derivative of `secondCovariantField`. -/
def secondCovariantFieldTimeDerivative
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (t : ℝ) : E :=
  coordinateBrokenVariationSecondCovariantFieldTimeDerivative
    (I := I) (M := M) cov x₀ basis d.a d.b d.dz d.dJ d.z d.J
      d.leftAcceleration d.rightAcceleration t

/-- The covariant first variation of time velocity. -/
def firstCovariantField
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e t : ℝ) : E :=
  coordinateBrokenVariationFirstCovariantField
    (I := I) (M := M) cov x₀ basis d.a d.b d.dz d.dJ d.z d.J
      d.leftNode d.rightNode d.leftVelocity d.rightVelocity e t

end CoordinateBrokenVariationData

end LocalGeodesicData
end BonnetMyersEntry
