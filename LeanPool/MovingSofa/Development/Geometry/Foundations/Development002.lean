/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.Isoperimetric.BrunnMinkowski
public import LeanPool.MovingSofa.Development.Geometry.Foundations.Development001


public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Moving sofa: related mathematical developments

* `Infrastructure.Analysis.Foundations.Development002`.
* `Infrastructure.Curves.Foundations.Development001`.
* `Infrastructure.Analysis.Foundations.Development004`.
* `Infrastructure.Geometry.Foundations.Development003`.
* `Infrastructure.Analysis.Foundations.Development003`.
* `Infrastructure.Geometry.Foundations.Development004`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Analysis.BoundedVariation`.
* `Analysis.MeasureProducts`.
* `Analysis.Stieltjes.Integral`.
* `Analysis.Stieltjes.AbsoluteContinuity`.
* `Analysis.Stieltjes.Calculus`.
* `Analysis.Stieltjes.DensityIntegration`.
* `Analysis.Stieltjes.Linearity`.
* `Analysis.Stieltjes.InnerProduct`.
* `Analysis.Stieltjes.Smooth`.
* `Analysis.Stieltjes.Frame`.
* `Analysis.Stieltjes.Transport`.
* `Analysis.Stieltjes.Continuous`.
* `Analysis.Stieltjes.Affine`.
* `Analysis.Stieltjes.RiemannSums`.
* `Analysis.Stieltjes.Shift`.
* `Analysis.SurfaceMeasure.Basic`.
* `Analysis.SurfaceMeasure.ExteriorNormal`.
* `Analysis.SurfaceMeasure.GraphDefinitions`.
* `Analysis.SurfaceMeasure.Regularity`.
* `Analysis.SurfaceMeasure.Segment`.
* `Analysis.SurfaceMeasure.SegmentFaces`.
* `Analysis.SurfaceMeasure.SegmentGraph`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Bounded Variation
-/

public section

noncomputable section

namespace MovingSofa

/-- Bounded variation for a real function on its actual closed-interval domain. -/
@[expose]
def IsIntervalBoundedVariation (a b : ℝ) (f : Set.Icc a b → ℝ) : Prop :=
  BoundedVariationOn f Set.univ

private theorem intervalBV_add {a b : ℝ} {f g : Set.Icc a b → ℝ}
    (hf : IsIntervalBoundedVariation a b f) (hg : IsIntervalBoundedVariation a b g) :
    IsIntervalBoundedVariation a b (f + g) := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
      Finset.sum_le_sum fun _ _ ↦ edist_add_add_le _ _ _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- The submodule of continuous planar interval functions with coordinatewise finite variation. -/
@[expose]
def continuousBVSubmodule (a b : ℝ) : Submodule ℝ (Set.Icc a b → Point) where
  carrier := {f | Continuous f ∧
    ∀ i : Fin 2, IsIntervalBoundedVariation a b (fun t ↦ f t i)}
  zero_mem' := by
    refine ⟨continuous_const, fun i ↦ ?_⟩
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, fun i ↦ intervalBV_add (hf.2 i) (hg.2 i)⟩
  smul_mem' := by
    intro c f hf
    refine ⟨continuous_const.smul hf.1, fun i ↦ ?_⟩
    exact (ContinuousLinearMap.lsmul ℝ ℝ c).lipschitzWith.comp_boundedVariationOn (hf.2 i)

/-- The real vector space of continuous planar BV paths on a closed interval. -/
abbrev ContinuousBVPaths (a b : ℝ) : Type := continuousBVSubmodule a b

/-- A continuous planar BV path has finite vector variation on its whole domain. -/
theorem ContinuousBVPaths.boundedVariationOn {a b : ℝ} (x : ContinuousBVPaths a b) :
    BoundedVariationOn x.val Set.univ := by
  have hdist (p q : Point) : edist p q ≤ edist (p 0) (q 0) + edist (p 1) (q 1) := by
    have hnorm (z : Point) : ‖z‖ ≤ |z 0| + |z 1| := by
      nlinarith [Point.norm_sq_eq z, sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0),
        abs_nonneg (z 1), norm_nonneg z, mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]
    simp only [edist_dist, dist_eq_norm, Real.norm_eq_abs]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using hnorm (p - q))
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨x.property.2 0, x.property.2 1⟩) ?_
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (x.val (u (i + 1)) 0) (x.val (u i) 0) +
          edist (x.val (u (i + 1)) 1) (x.val (u i) 1)) :=
      Finset.sum_le_sum fun _ _ ↦ hdist _ _
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le (f := fun t ↦ x.val t 0) (n := n) hu hus)
      (eVariationOn.sum_le (f := fun t ↦ x.val t 1) (n := n) hu hus)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Measure Products
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Multiply a signed measure by a real density using the continuous multiplication map. -/
def functionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X) : SignedMeasure X :=
  μ.withDensity f (ContinuousLinearMap.mul ℝ ℝ)

/-- Multiply one signed measure by each of two scalar densities. -/
def pairFunctionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f.1 μ, functionMeasureMul f.2 μ)

/-- Multiply both components of a signed-measure pair by one scalar density. -/
def functionPairMeasureMul {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f μ.1, functionMeasureMul f μ.2)

/-- The sum of the coordinatewise density products of a function pair and measure pair. -/
def functionMeasureDot {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.1 + functionMeasureMul f.2 μ.2

/-- The oriented planar determinant `p₀ q₁ - p₁ q₀`. -/
@[expose]
def planeCrossProduct (p q : Point) : ℝ :=
  p 0 * q 1 - p 1 * q 0

/-- The signed-measure determinant of a function pair and a measure pair. -/
def functionMeasureCross {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X × SignedMeasure X) :
    SignedMeasure X :=
  functionMeasureMul f.1 μ.2 - functionMeasureMul f.2 μ.1

/-- Bundle the scalar, vector and dot-product operations on signed measures. -/
def functionMeasureProducts (X : Type*) [MeasurableSpace X] :
    ((X → ℝ) → SignedMeasure X → SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → SignedMeasure X → SignedMeasure X × SignedMeasure X) ×
    ((X → ℝ) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X × SignedMeasure X) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (functionMeasureMul, pairFunctionMeasureMul, functionPairMeasureMul, functionMeasureDot)

/-- Bundle the planar determinant and its signed-measure counterpart. -/
def planeCrossProducts (X : Type*) [MeasurableSpace X] :
    (Point → Point → ℝ) ×
    (((X → ℝ) × (X → ℝ)) → (SignedMeasure X × SignedMeasure X) → SignedMeasure X) :=
  (planeCrossProduct, functionMeasureCross)

/-! ### The oriented planar determinant

Basic algebra of `planeCrossProduct`, the transitivity of the order it induces on the closed
first quadrant, and the two shapes of level set used when a planar region is fanned into
triangles over a base point.
-/

@[simp] theorem planeCrossProduct_self (p : Point) : planeCrossProduct p p = 0 := by
  simp only [planeCrossProduct]
  ring

@[simp] theorem planeCrossProduct_zero_left (p : Point) : planeCrossProduct 0 p = 0 := by
  simp [planeCrossProduct]

@[simp] theorem planeCrossProduct_zero_right (p : Point) : planeCrossProduct p 0 = 0 := by
  simp [planeCrossProduct]

/-- The oriented determinant is antisymmetric. -/
theorem planeCrossProduct_swap (p q : Point) :
    planeCrossProduct p q = -planeCrossProduct q p := by
  simp only [planeCrossProduct]
  ring

/-- The oriented determinant is the inner product against the quarter turn of its first
argument. -/
theorem planeCrossProduct_eq_inner (p q : Point) :
    planeCrossProduct p q = inner ℝ q !₂[-p 1, p 0] := by
  simp [planeCrossProduct, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- In the closed first quadrant the oriented determinant order is transitive: if `v` is
nonzero and both `u × v` and `v × w` are nonnegative, then so is `u × w`. -/
theorem planeCrossProduct_nonneg_trans {u v w : Point} (hv : v ≠ 0)
    (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1) (hv0 : 0 ≤ v 0) (hv1 : 0 ≤ v 1)
    (hw0 : 0 ≤ w 0) (hw1 : 0 ≤ w 1)
    (huv : 0 ≤ planeCrossProduct u v) (hvw : 0 ≤ planeCrossProduct v w) :
    0 ≤ planeCrossProduct u w := by
  have hvpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2) with h | h
    · refine absurd ?_ hv
      have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · exact h
  have hid : planeCrossProduct u w * (v 0 ^ 2 + v 1 ^ 2)
      = (w 0 * v 0 + w 1 * v 1) * planeCrossProduct u v
        + planeCrossProduct v w * (u 0 * v 0 + u 1 * v 1) := by
    simp only [planeCrossProduct]
    ring
  nlinarith [mul_nonneg (add_nonneg (mul_nonneg hw0 hv0) (mul_nonneg hw1 hv1)) huv,
    mul_nonneg hvw (add_nonneg (mul_nonneg hu0 hv0) (mul_nonneg hu1 hv1))]

/-- The closed angular sector between two rays through a base point is convex. -/
theorem convex_setOf_planeCrossProduct_fan (u v L : Point) :
    Convex ℝ {x : Point | 0 ≤ planeCrossProduct u (x - L) ∧
      0 ≤ planeCrossProduct (x - L) v} := by
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  simp only [Set.mem_ofPred_eq, planeCrossProduct, PiLp.sub_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  constructor
  · nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
  · nlinarith [mul_nonneg ha hx.2, mul_nonneg hb hy.2]

/-- The line through a base point in a nonzero direction carries no planar area. -/
theorem volume_setOf_planeCrossProduct_sub_eq_zero {w : Point} (hw : w ≠ 0) (L : Point) :
    volume {x : Point | planeCrossProduct w (x - L) = 0} = 0 := by
  have hrot : (!₂[-w 1, w 0] : Point) ≠ 0 := by
    intro h
    refine hw ?_
    have h0 : w 0 = 0 := by simpa using congrArg (fun v : Point ↦ v 1) h
    have h1 : w 1 = 0 := by simpa using congrArg (fun v : Point ↦ v 0) h
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have hset : {x : Point | planeCrossProduct w (x - L) = 0}
      = {x : Point | inner ℝ x (!₂[-w 1, w 0] : Point) =
          inner ℝ L (!₂[-w 1, w 0] : Point)} := by
    ext x
    simp only [Set.mem_ofPred_eq, planeCrossProduct_eq_inner, inner_sub_left, sub_eq_zero]
  rw [hset]
  exact volume.addHaar_setOf_real_inner_eq hrot _

/-- The planar cross product is the frame determinant at every angle. -/
theorem planeCrossProduct_eq_inner_frame (a b : Point) (t : ℝ) :
    planeCrossProduct a b =
      inner ℝ a (normalVector (t : Real.Angle)) * inner ℝ b (tangentVector (t : Real.Angle)) -
        inner ℝ a (tangentVector (t : Real.Angle)) *
          inner ℝ b (normalVector (t : Real.Angle)) := by
  simp only [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two, Real.Angle.cos_coe, Real.Angle.sin_coe, RCLike.inner_apply,
    conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (a.ofLp 1 * b.ofLp 0 - a.ofLp 0 * b.ofLp 1) * (Real.sin_sq_add_cos_sq t)

/-- The oriented determinant of a point against the frame tangent is its normal coordinate. -/
theorem planeCrossProduct_tangentVector (p : Point) (t : Real.Angle) :
    planeCrossProduct p (tangentVector t) = inner ℝ p (normalVector t) := by
  simp [planeCrossProduct, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Integral
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A right-continuous real BV function on its actual closed-interval domain. -/
structure RightContinuousIntervalBV (a b : ℝ) where
  /-- The real-valued function on the closed parameter interval. -/
  toFun : Set.Icc a b → ℝ
  boundedVariation : IsIntervalBoundedVariation a b toFun
  right_continuous : ∀ t, ContinuousWithinAt toFun (Set.Ici t) t

/-- A right-continuous interval-BV function is determined by its underlying function. -/
theorem RightContinuousIntervalBV.toFun_injective {a b : ℝ} :
    Function.Injective (@RightContinuousIntervalBV.toFun a b) := by
  rintro ⟨f, hf, hfr⟩ ⟨g, hg, hgr⟩ hfg
  cases hfg
  rfl

/-- A right-continuous interval-BV function on a nonempty interval is bounded, by its value at
the left endpoint plus the total variation. -/
theorem RightContinuousIntervalBV.exists_norm_bound {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) : ∃ C : ℝ, ∀ t, ‖f.toFun t‖ ≤ C := by
  refine ⟨‖f.toFun ⟨a, le_rfl, hab⟩‖ + (eVariationOn f.toFun Set.univ).toReal, fun t ↦ ?_⟩
  calc ‖f.toFun t‖
      ≤ ‖f.toFun ⟨a, le_rfl, hab⟩‖ + ‖f.toFun t - f.toFun ⟨a, le_rfl, hab⟩‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := by
        gcongr
        simpa [dist_eq_norm_sub] using
          f.boundedVariation.dist_le (Set.mem_univ t) (Set.mem_univ ⟨a, le_rfl, hab⟩)

/-- The finite signed Stieltjes measure on the interval, with zero initial atom. -/
@[expose]
def intervalStieltjesMeasure {a b : ℝ} (f : RightContinuousIntervalBV a b) :
    SignedMeasure (Set.Icc a b) :=
  f.boundedVariation.vectorMeasure

/-- The Stieltjes integral, used for bounded measurable integrands and Borel subsets. -/
@[expose]
def intervalStieltjesIntegral {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) (X : Set (Set.Icc a b)) : ℝ :=
  ∫ᵛ t in X, g t ∂[ContinuousLinearMap.mul ℝ ℝ; intervalStieltjesMeasure f]

/-- Over the whole parameter interval, the interval Stieltjes integral is the unrestricted
vector-measure integral. -/
theorem intervalStieltjesIntegral_univ {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (g : Set.Icc a b → ℝ) :
    intervalStieltjesIntegral f g Set.univ =
      VectorMeasure.integral (intervalStieltjesMeasure f) g (ContinuousLinearMap.mul ℝ ℝ) := by
  simp only [intervalStieltjesIntegral, VectorMeasure.restrict_univ]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Absolute Continuity
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Extend an interval function to the real line by zero outside its domain. -/
def stieltjesScalarExtension {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (t : ℝ) : ℝ := by
  classical
  exact if h : t ∈ Set.Icc a b then f.toFun ⟨t, h⟩ else 0

/-- An integrable density represents the interval Stieltjes measure on measurable sets. -/
def HasIntervalStieltjesDensity {a b : ℝ} (f : RightContinuousIntervalBV a b)
    (r : ℝ → ℝ) : Prop :=
  Integrable r (volume.restrict (Set.Icc a b)) ∧
    ∀ E : Set ℝ, MeasurableSet E →
      intervalStieltjesMeasure f {t | (t : ℝ) ∈ E} =
        ∫ t in E, r t ∂volume.restrict (Set.Icc a b)

theorem intervalStieltjesMeasure_Ioc {a b : ℝ}
    (f : RightContinuousIntervalBV a b) (c d : Set.Icc a b) (hcd : c ≤ d) :
    intervalStieltjesMeasure f (Set.Ioc c d) = f.toFun d - f.toFun c := by
  rw [intervalStieltjesMeasure, f.boundedVariation.vectorMeasure_Ioc hcd]
  rw [f.right_continuous d |>.rightLim_eq, f.right_continuous c |>.rightLim_eq]

private theorem stieltjesScalarExtension_eq_add_integral {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) (t : Set.Icc a b) :
    stieltjesScalarExtension f (t : ℝ) =
      f.toFun ⟨a, le_rfl, hab⟩ + ∫ x in a..(t : ℝ), r x := by
  have hinc := hr.2 (Ioc a (t : ℝ)) measurableSet_Ioc
  have hset : {x : Icc a b | (x : ℝ) ∈ Ioc a (t : ℝ)} =
      Ioc (⟨a, le_rfl, hab⟩ : Icc a b) t := rfl
  rw [hset, intervalStieltjesMeasure_Ioc f _ _ t.property.1] at hinc
  have hmeasure :
      (volume.restrict (Set.Icc a b)).restrict (Set.Ioc a (t : ℝ)) =
        volume.restrict (Set.Ioc a (t : ℝ)) := by
    exact Measure.restrict_restrict_of_subset
      (fun x hx ↦ ⟨hx.1.le, hx.2.trans t.property.2⟩)
  have hrestrict :
      (∫ x in Set.Ioc a (t : ℝ), r x ∂volume.restrict (Set.Icc a b)) =
        ∫ x in Set.Ioc a (t : ℝ), r x := by
    rw [hmeasure]
  rw [stieltjesScalarExtension]
  simp only [dite_eq_left t.2]
  change f.toFun t = _
  rw [intervalIntegral.integral_of_le t.2.1]
  have hinc' := hinc.trans hrestrict
  linarith

private theorem absolutelyContinuousOnInterval_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hp := hri.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (by simp [hab])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f.toFun ⟨a, le_rfl, hab⟩) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hs := hc.add hp
  apply hs.congr
  intro x hx
  have hx' : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨x, hx'⟩
  simpa [stieltjesScalarExtension, hx'] using hprim.symm

private theorem ae_hasDerivAt_of_stieltjesDensity {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) (r : ℝ → ℝ)
    (hr : HasIntervalStieltjesDensity f r) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasDerivAt (stieltjesScalarExtension f) (r t) t := by
  have hri : IntervalIntegrable r volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hr.1
  have hder := IntervalIntegrable.ae_hasDerivAt_integral hri
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hder] with x hx hxo
  have hxu : x ∈ Set.uIcc a b := by
    simpa [Set.uIcc_of_le hab] using ⟨hxo.1.le, hxo.2.le⟩
  have hd := hx hxu a (by simp [hab])
  have hd' := hd.const_add (f.toFun ⟨a, le_rfl, hab⟩)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hyo
  have hycc : y ∈ Set.Icc a b := ⟨hyo.1.le, hyo.2.le⟩
  have hprim := stieltjesScalarExtension_eq_add_integral hab f r hr ⟨y, hycc⟩
  simpa [stieltjesScalarExtension, hycc] using hprim

private theorem intervalStieltjes_hasDensity_deriv {a b : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b)
    (hf : AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b) :
    HasIntervalStieltjesDensity f (deriv (stieltjesScalarExtension f)) := by
  let g := stieltjesScalarExtension f
  have hr : IntegrableOn (deriv g) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  have hsub : Continuous f.toFun := by
    have h := (continuousOn_iff_continuous_domRestrict).mp
      (show ContinuousOn g (Icc a b) by simpa only [uIcc_of_le hab] using hf.continuousOn)
    convert h using 1
    funext x
    simp [g, stieltjesScalarExtension, x.property]
  have hri : Integrable (fun x : Icc a b ↦ deriv g x)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr
  have hmeasure : intervalStieltjesMeasure f =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun x : Icc a b ↦ deriv g x) := by
    apply f.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc hsub hri
    intro c d hcd
    have hinc := (hf.mono (show uIcc (c : ℝ) (d : ℝ) ⊆ uIcc a b by
      rw [uIcc_of_le (show (c : ℝ) ≤ d from hcd), uIcc_of_le hab]
      exact Icc_subset_Icc c.property.1 d.property.2)).integral_deriv_eq_sub
    have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
    rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc]
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc c.property.1 d.property.2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hinc]
    simp [stieltjesScalarExtension, c.property, d.property]
  refine ⟨hr, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hri hpre,
    integral_subtype_preimage measurableSet_Icc hE]

theorem intervalStieltjes_absoluteContinuity (a b : ℝ) (hab : a ≤ b)
    (f : RightContinuousIntervalBV a b) :
    (AbsolutelyContinuousOnInterval (stieltjesScalarExtension f) a b ↔
      ∃ r : ℝ → ℝ, HasIntervalStieltjesDensity f r) ∧
    (∀ r : ℝ → ℝ, HasIntervalStieltjesDensity f r →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasDerivAt (stieltjesScalarExtension f) (r t) t) := by
  refine ⟨⟨?_, ?_⟩, fun r hr ↦ ae_hasDerivAt_of_stieltjesDensity hab f r hr⟩
  · intro hf
    exact ⟨deriv (stieltjesScalarExtension f), intervalStieltjes_hasDensity_deriv hab f hf⟩
  · rintro ⟨r, hr⟩
    exact absolutelyContinuousOnInterval_of_stieltjesDensity hab f r hr

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Calculus
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_integration_by_parts (a b : ℝ) (hab : a ≤ b)
    (f g : RightContinuousIntervalBV a b) :
    ∃ left : Set.Icc a b → ℝ,
      (∀ t : Set.Icc a b, a < (t : ℝ) →
        Tendsto f.toFun (nhdsWithin t (Set.Iio t)) (𝓝 (left t))) ∧
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ)} +
        intervalStieltjesIntegral g left {t | a < (t : ℝ)} =
      f.toFun ⟨b, hab, le_rfl⟩ * g.toFun ⟨b, hab, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab⟩ * g.toFun ⟨a, le_rfl, hab⟩ := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  refine ⟨Function.leftLim f.toFun, fun t _ ↦ f.boundedVariation.tendsto_leftLim t, ?_⟩
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioc_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation (show a' ≤ b' by
      exact hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ)} = Set.Ioc a' b' := by
    ext t
    constructor
    · intro ht
      exact ⟨ht, t.property.2⟩
    · exact fun ht ↦ ht.1
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  change (∫ᵛ t in Set.Ioc a' b', g.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; f.boundedVariation.vectorMeasure]) +
    (∫ᵛ t in Set.Ioc a' b', Function.leftLim f.toFun t
      ∂[ContinuousLinearMap.mul ℝ ℝ; g.boundedVariation.vectorMeasure]) = _
  rw [hparts]
  simp only [hfa, hga]
  change _ + (f.toFun b' * g.toFun b' - f.toFun a' * g.toFun a' - _) = _
  dsimp [a', b']
  ring

/-- Stieltjes integration by parts on the open interval `(a, b)`: no endpoint atom is included
at `b`, and none is introduced at `a`. The left limit in the first integrand accounts for
simultaneous jumps. -/
theorem intervalStieltjes_integration_by_parts_Ioo (a b : ℝ) (hab : a < b)
    (f g : RightContinuousIntervalBV a b) :
    intervalStieltjesIntegral g (Function.leftLim f.toFun)
        {t | a < (t : ℝ) ∧ (t : ℝ) < b} +
      intervalStieltjesIntegral f g.toFun {t | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Function.leftLim f.toFun ⟨b, hab.le, le_rfl⟩ *
          Function.leftLim g.toFun ⟨b, hab.le, le_rfl⟩ -
        f.toFun ⟨a, le_rfl, hab.le⟩ * g.toFun ⟨a, le_rfl, hab.le⟩ := by
  have hfa (t : Set.Icc a b) : Function.rightLim f.toFun t = f.toFun t :=
    (f.right_continuous t).rightLim_eq
  have hga (t : Set.Icc a b) : Function.rightLim g.toFun t = g.toFun t :=
    (g.right_continuous t).rightLim_eq
  have hparts := BoundedVariationOn.setIntegral_Ioo_leftLim_vectorMeasure_eq_sub
    (B := ContinuousLinearMap.mul ℝ ℝ) f.boundedVariation g.boundedVariation
    (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) < ⟨b, hab.le, le_rfl⟩ from hab)
  have hset : {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      Set.Ioo (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ⟨b, hab.le, le_rfl⟩ := by
    ext t
    exact ⟨fun ht ↦ ⟨ht.1, ht.2⟩, fun ht ↦ ⟨ht.1, ht.2⟩⟩
  have hmulflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [hmulflip] at hparts
  rw [hset]
  unfold intervalStieltjesIntegral intervalStieltjesMeasure
  rw [hparts]
  simp only [hfa, hga, ContinuousLinearMap.mul_apply']
  ring

theorem intervalStieltjes_product (a b : ℝ)
    (f g : RightContinuousIntervalBV a b)
    (hcont : Continuous f.toFun ∨ Continuous g.toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = f.toFun t * g.toFun t) ∧
      ∀ E : Set (Set.Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          intervalStieltjesIntegral f g.toFun E + intervalStieltjesIntegral g f.toFun E := by
  let h : RightContinuousIntervalBV a b :=
    ⟨fun t ↦ f.toFun t * g.toFun t,
      f.boundedVariation.bilinear_comp g.boundedVariation (ContinuousLinearMap.mul ℝ ℝ),
      fun t ↦ (f.right_continuous t).mul (g.right_continuous t)⟩
  refine ⟨h, fun _ ↦ rfl, fun E _ ↦ ?_⟩
  have hflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  have hfr : Function.rightLim f.toFun = f.toFun :=
    funext fun t ↦ (f.right_continuous t).rightLim_eq
  have hgr : Function.rightLim g.toFun = g.toFun :=
    funext fun t ↦ (g.right_continuous t).rightLim_eq
  rcases hcont with hf | hg
  · have hfl : Function.leftLim f.toFun = f.toFun :=
      funext fun t ↦ hf.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_leftLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfl, hgr] at hp
    change _ = _ + _
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith
  · have hgl : Function.leftLim g.toFun = g.toFun :=
      funext fun t ↦ hg.continuousAt.continuousWithinAt.leftLim_eq
    have hp := f.boundedVariation.setIntegral_rightLim_vectorMeasure_eq_sub
      (B := ContinuousLinearMap.mul ℝ ℝ) g.boundedVariation (s := E)
    rw [hflip, hfr, hgl] at hp
    unfold intervalStieltjesIntegral intervalStieltjesMeasure
    change (f.boundedVariation.bilinear_comp g.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).vectorMeasure E = _
    linarith

/-- The integrated Stieltjes product rule: a bounded measurable weight distributes over the
Lebesgue–Stieltjes measure of a product one factor of which is continuous. -/
theorem intervalStieltjesIntegral_product_of_bounded {a b : ℝ} (hab : a ≤ b)
    (f g h : RightContinuousIntervalBV a b) (hgc : Continuous g.toFun)
    (hh : ∀ t, h.toFun t = f.toFun t * g.toFun t)
    (φ : Set.Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) (hφb : ∀ t, ‖φ t‖ ≤ C)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral h φ E =
      intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E +
        intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E := by
  obtain ⟨h', hh', hh'm⟩ := intervalStieltjes_product a b f g (Or.inr hgc)
  have hheq : h = h' :=
    RightContinuousIntervalBV.toFun_injective (funext fun t ↦ (hh t).trans (hh' t).symm)
  obtain ⟨Cf, hCf⟩ := f.exists_norm_bound hab
  obtain ⟨Cg, hCg⟩ := g.exists_norm_bound hab
  have hfm : Measurable f.toFun := f.boundedVariation.measurable
  have hgm : Measurable g.toFun := g.boundedVariation.measurable
  -- both Stieltjes measures are absolutely continuous over the sum of their total variations
  set ρ : Measure (Set.Icc a b) := (intervalStieltjesMeasure f).totalVariation +
    (intervalStieltjesMeasure g).totalVariation with hρ
  have _ : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  have hac : ∀ μ : SignedMeasure (Set.Icc a b), μ.totalVariation ≤ ρ →
      μ ≪ᵥ ρ.toENNRealVectorMeasure := fun μ hle ↦ by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
    exact Measure.absolutelyContinuous_of_le hle
  have hacf := hac (intervalStieltjesMeasure f) (by rw [hρ]; exact Measure.le_add_right le_rfl)
  have hacg := hac (intervalStieltjesMeasure g) (by rw [hρ]; exact Measure.le_add_left le_rfl)
  set rf : Set.Icc a b → ℝ := (intervalStieltjesMeasure f).rnDeriv ρ with hrf
  set rg : Set.Icc a b → ℝ := (intervalStieltjesMeasure g).rnDeriv ρ with hrg
  have hrfi : Integrable rf ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hrgi : Integrable rg ρ := SignedMeasure.integrable_rnDeriv _ ρ
  have hμf : ρ.withDensityᵥ rf = intervalStieltjesMeasure f :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacf
  have hμg : ρ.withDensityᵥ rg = intervalStieltjesMeasure g :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq _ ρ hacg
  have hgrf : Integrable (fun x ↦ g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hgm.aestronglyMeasurable (Filter.Eventually.of_forall hCg)
  have hfrg : Integrable (fun x ↦ f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall hCf)
  have hsumi : Integrable (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) ρ := hgrf.add hfrg
  have hφg : Measurable fun t ↦ φ t * g.toFun t := hφ.mul hgm
  have hφf : Measurable fun t ↦ φ t * f.toFun t := hφ.mul hfm
  -- the product measure is the density of the two-term Radon–Nikodym sum
  have hsum : intervalStieltjesMeasure h =
      ρ.withDensityᵥ (fun x ↦ g.toFun x * rf x + f.toFun x * rg x) := by
    rw [hheq]
    ext S hS
    rw [withDensityᵥ_apply hsumi hS, hh'm S hS]
    have h1 : intervalStieltjesIntegral f g.toFun S = ∫ x in S, g.toFun x * rf x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμf,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
          hgm.aestronglyMeasurable Cg hCg S hS]
    have h2 : intervalStieltjesIntegral g f.toFun S = ∫ x in S, f.toFun x * rg x ∂ρ := by
      rw [intervalStieltjesIntegral, ← hμg,
        VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
          hfm.aestronglyMeasurable Cf hCf S hS]
    rw [h1, h2, integral_add hgrf.integrableOn hfrg.integrableOn]
  have hb1 : ∀ x, ‖φ x * g.toFun x‖ ≤ C * Cg := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCg x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hb2 : ∀ x, ‖φ x * f.toFun x‖ ≤ C * Cf := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hφb x) (hCf x) (norm_nonneg _) ((norm_nonneg _).trans (hφb x))
  have hi1 : Integrable (fun x ↦ φ x * g.toFun x * rf x) ρ :=
    hrfi.bdd_mul hφg.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have hi2 : Integrable (fun x ↦ φ x * f.toFun x * rg x) ρ :=
    hrgi.bdd_mul hφf.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  rw [show intervalStieltjesIntegral h φ E =
      ∫ x in E, φ x * (g.toFun x * rf x + f.toFun x * rg x) ∂ρ by
    rw [intervalStieltjesIntegral, hsum,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hsumi
        hφ.aestronglyMeasurable C hφb E hE],
    show intervalStieltjesIntegral f (fun t ↦ φ t * g.toFun t) E =
      ∫ x in E, φ x * g.toFun x * rf x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμf,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrfi
        hφg.aestronglyMeasurable (C * Cg) hb1 E hE],
    show intervalStieltjesIntegral g (fun t ↦ φ t * f.toFun t) E =
      ∫ x in E, φ x * f.toFun x * rg x ∂ρ by
    rw [intervalStieltjesIntegral, ← hμg,
      VectorMeasure.setIntegral_withDensity_mul_of_bounded hrgi
        hφf.aestronglyMeasurable (C * Cf) hb2 E hE],
    ← integral_add hi1.integrableOn hi2.integrableOn]
  exact setIntegral_congr_fun hE fun x _ ↦ by ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Density Integration
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuous integrand against an interval Stieltjes measure with an ordinary density is
the corresponding weighted Lebesgue integral on the interval subtype. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ} (hq : Continuous q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul hri hq E hE

/-- The density formula also applies to a bounded-variation integrand on a nonempty compact
interval. -/
theorem intervalStieltjesIntegral_eq_integral_mul_of_density_bv
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b) {r : ℝ → ℝ}
    (hr : HasIntervalStieltjesDensity F r) {q : Icc a b → ℝ}
    (hq : BoundedVariationOn q univ) (E : Set (Icc a b)) (hE : MeasurableSet E) :
    intervalStieltjesIntegral F q E =
      ∫ t in E, q t * r t ∂volume.comap (Subtype.val : Icc a b → ℝ) := by
  have hri : Integrable (fun t : Icc a b ↦ r t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hr.1
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ r t) := by
    ext S hS
    have himage : MeasurableSet ((Subtype.val : Icc a b → ℝ) '' S) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hS
    have hpre : {t : Icc a b | (t : ℝ) ∈ (Subtype.val : Icc a b → ℝ) '' S} = S :=
      Set.preimage_image_eq S Subtype.val_injective
    rw [withDensityᵥ_apply hri hS, ← hpre,
      integral_subtype_preimage measurableSet_Icc himage]
    exact hr.2 _ himage
  let _ : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  let C := ‖q t₀‖ + (eVariationOn q univ).toReal
  have hq_bound : ∀ t, ‖q t‖ ≤ C := by
    intro t
    calc
      ‖q t‖ ≤ ‖q t₀‖ + ‖q t - q t₀‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖q t₀‖ + (eVariationOn q univ).toReal := by
        gcongr
        simpa [dist_eq_norm_sub] using hq.dist_le (mem_univ t) (mem_univ t₀)
      _ = C := rfl
  unfold intervalStieltjesIntegral
  rw [hmeasure]
  exact VectorMeasure.setIntegral_withDensity_mul_of_bounded hri
    hq.stronglyMeasurable.aestronglyMeasurable C hq_bound E hE

/-- A real function agreeing with a BV representative is integrable on its interval. -/
theorem RightContinuousIntervalBV.integrableOn_Icc_of_eq
    {a b : ℝ} (f : RightContinuousIntervalBV a b) (q : ℝ → ℝ)
    (hq : ∀ t : Icc a b, q t = f.toFun t) : IntegrableOn q (Icc a b) := by
  have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    ⟨by
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp only [image_univ, Subtype.range_val]
      exact measure_Icc_lt_top⟩
  let _ := hfinite
  rw [IntegrableOn, ← map_comap_subtype_coe measurableSet_Icc,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff
      (μ := volume.comap (Subtype.val : Icc a b → ℝ))]
  convert f.boundedVariation.integrable
      (μ := volume.comap (Subtype.val : Icc a b → ℝ)) using 1
  funext t
  exact hq t

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Linearity
-/

public section

noncomputable section

open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_linear_combination (a b : ℝ)
    (f g : RightContinuousIntervalBV a b) (r s : ℝ) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = r * f.toFun t + s * g.toFun t) ∧
      intervalStieltjesMeasure h =
        r • intervalStieltjesMeasure f + s • intervalStieltjesMeasure g := by
  let hfun : Set.Icc a b → ℝ := fun t ↦ r * f.toFun t + s * g.toFun t
  have hBV : IsIntervalBoundedVariation a b hfun := by
    have hfr := (ContinuousLinearMap.lsmul ℝ ℝ r).lipschitzWith.comp_boundedVariationOn
      f.boundedVariation
    have hgr := (ContinuousLinearMap.lsmul ℝ ℝ s).lipschitzWith.comp_boundedVariationOn
      g.boundedVariation
    exact BoundedVariationOn.add hfr hgr
  change BoundedVariationOn hfun Set.univ at hBV
  let h : RightContinuousIntervalBV a b :=
    { toFun := hfun
      boundedVariation := hBV
      right_continuous := fun t ↦ by
        exact (f.right_continuous t).const_mul r |>.add ((g.right_continuous t).const_mul s) }
  refine ⟨h, ?_, ?_⟩
  · intro t
    rfl
  · apply MeasureTheory.VectorMeasure.ext_of_Icc
    intro x y hxy
    have hbv : BoundedVariationOn h.toFun Set.univ := h.boundedVariation
    have hleft (z : Set.Icc a b) :
        Function.leftLim h.toFun z =
          r * Function.leftLim f.toFun z + s * Function.leftLim g.toFun z := by
      rcases Filter.eq_or_neBot (𝓝[<] z) with hz | hz
      · simp [leftLim_eq_of_eq_bot _ hz, h, hfun]
      · exact tendsto_nhds_unique (hbv.tendsto_leftLim z)
          ((f.boundedVariation.tendsto_leftLim z).const_smul r |>.add
            ((g.boundedVariation.tendsto_leftLim z).const_smul s))
    have hfxy : Function.rightLim f.toFun y = f.toFun y :=
      (f.right_continuous y).rightLim_eq
    have gfxy : Function.rightLim g.toFun y = g.toFun y :=
      (g.right_continuous y).rightLim_eq
    have hxy' : Function.rightLim h.toFun y = h.toFun y :=
      (h.right_continuous y).rightLim_eq
    simp only [smul_apply, add_apply]
    rw [show intervalStieltjesMeasure h (Set.Icc x y) =
        Function.rightLim h.toFun y - Function.leftLim h.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc hbv hxy]
    rw [show intervalStieltjesMeasure f (Set.Icc x y) =
        Function.rightLim f.toFun y - Function.leftLim f.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc f.boundedVariation hxy]
    rw [show intervalStieltjesMeasure g (Set.Icc x y) =
        Function.rightLim g.toFun y - Function.leftLim g.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc g.boundedVariation hxy]
    rw [hleft x]
    rw [hxy', hfxy, gfxy]
    simp [h, hfun, sub_eq_add_neg]
    ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Inner Product
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Componentwise product rule for the Euclidean pairing of two planar interval-BV functions,
when the second function is continuous. -/
theorem intervalStieltjes_inner_fin_two {a b : ℝ}
    (f g : Fin 2 → RightContinuousIntervalBV a b)
    (hg : ∀ i, Continuous (g i).toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = ∑ i, (f i).toFun t * (g i).toFun t) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          ∑ i, (intervalStieltjesIntegral (f i) (g i).toFun E +
            intervalStieltjesIntegral (g i) (f i).toFun E) := by
  obtain ⟨p0, hp0, hp0m⟩ := intervalStieltjes_product a b (f 0) (g 0) (Or.inr (hg 0))
  obtain ⟨p1, hp1, hp1m⟩ := intervalStieltjes_product a b (f 1) (g 1) (Or.inr (hg 1))
  obtain ⟨h, hh, hhm⟩ := intervalStieltjes_linear_combination a b p0 p1 1 1
  refine ⟨h, ?_, ?_⟩
  · intro t
    rw [hh, hp0, hp1, Fin.sum_univ_two]
    ring
  · intro E hE
    rw [show intervalStieltjesMeasure h E =
        intervalStieltjesMeasure p0 E + intervalStieltjesMeasure p1 E by
      rw [hhm]
      simp]
    rw [hp0m E hE, hp1m E hE, Fin.sum_univ_two]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Smooth
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A continuously differentiable real function restricted to a compact interval, together with
its Stieltjes density. -/
theorem exists_intervalBV_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (φ φ' : ℝ → ℝ) (hderiv : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : Continuous φ') :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = φ t) ∧ HasIntervalStieltjesDensity F φ' := by
  have hdiff : Differentiable ℝ φ := fun t ↦ (hderiv t).differentiableAt
  have hcontDiff : ContDiff ℝ 1 φ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hdiff, ?_⟩
    convert hφ' using 1
    funext t
    exact (hderiv t).deriv
  have hBVreal : BoundedVariationOn φ (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (hcontDiff.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)).boundedVariationOn
  let ι : Icc a b → ℝ := (↑)
  have hBV : BoundedVariationOn (φ ∘ ι) Set.univ :=
    ne_top_of_le_ne_top hBVreal
      (eVariationOn.comp_le_of_monotoneOn φ ι
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  let F : RightContinuousIntervalBV a b :=
    { toFun := φ ∘ ι
      boundedVariation := hBV
      right_continuous := fun t ↦
        (hderiv (t : ℝ)).continuousAt.comp_continuousWithinAt
          continuous_subtype_val.continuousWithinAt }
  have hφ'int : Integrable φ' (volume.restrict (Icc a b)) :=
    hφ'.continuousOn.integrableOn_compact isCompact_Icc
  have hsubtype : Integrable (fun t : Icc a b ↦ φ' t)
      (volume.comap (Subtype.val : Icc a b → ℝ)) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hφ'int
  have hmeasure : intervalStieltjesMeasure F =
      (volume.comap (Subtype.val : Icc a b → ℝ)).withDensityᵥ
        (fun t : Icc a b ↦ φ' t) := by
    apply F.boundedVariation.vectorMeasure_eq_withDensity_of_integral_Icc
    · exact (continuous_iff_continuousAt.2 fun t ↦ (hderiv t).continuousAt).comp
        continuous_subtype_val
    · exact hsubtype
    · intro c d hcd
      have hftc : ∫ x in (c : ℝ)..(d : ℝ), φ' x = φ d - φ c :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ ↦ hderiv x) (hφ'.intervalIntegrable (c : ℝ) (d : ℝ))
      have hset : Icc c d = {x : Icc a b | (x : ℝ) ∈ Icc (c : ℝ) (d : ℝ)} := rfl
      rw [hset, integral_subtype_preimage measurableSet_Icc measurableSet_Icc,
        Measure.restrict_restrict_of_subset
          (Icc_subset_Icc c.property.1 d.property.2)]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd, hftc]
      simp [F, ι]
  refine ⟨F, fun _ ↦ rfl, hφ'int, ?_⟩
  intro E hE
  have hpre : MeasurableSet {t : Icc a b | (t : ℝ) ∈ E} :=
    hE.preimage measurable_subtype_coe
  rw [hmeasure, withDensityᵥ_apply hsubtype hpre,
    integral_subtype_preimage measurableSet_Icc hE]

/-- A right-continuous interval bounded-variation function that agrees on its interval with an
absolutely continuous function differentiable on the open interval has that derivative as its
Stieltjes density. Unlike `exists_intervalBV_of_hasDerivAt` this identifies the density of a
*given* bounded-variation function, and asks for differentiability only in the interior. -/
theorem hasIntervalStieltjesDensity_of_hasDerivAt {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (φ φ' : ℝ → ℝ)
    (hF : ∀ t : Icc a b, F.toFun t = φ t)
    (hac : AbsolutelyContinuousOnInterval φ a b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt φ (φ' t) t)
    (hint : IntegrableOn φ' (Icc a b)) :
    HasIntervalStieltjesDensity F φ' := by
  have hext : ∀ t ∈ Icc a b, stieltjesScalarExtension F t = φ t := by
    intro t ht
    rw [stieltjesScalarExtension, dite_eq_left ht]
    exact hF ⟨t, ht⟩
  have hac' : AbsolutelyContinuousOnInterval (stieltjesScalarExtension F) a b :=
    hac.congr fun t ht ↦ (hext t (by simpa only [uIcc_of_le hab] using ht)).symm
  obtain ⟨ρ, hρ⟩ := (intervalStieltjes_absoluteContinuity a b hab F).1.1 hac'
  have hIoo : ρ =ᵐ[volume.restrict (Ioo a b)] φ' := by
    filter_upwards [(intervalStieltjes_absoluteContinuity a b hab F).2 ρ hρ,
      ae_restrict_mem measurableSet_Ioo] with t ht htmem
    refine ht.unique ((hderiv t htmem).congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds htmem] with u hu
    exact hext u (Ioo_subset_Icc_self hu)
  have hIcc : ρ =ᵐ[volume.restrict (Icc a b)] φ' := by
    rwa [Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))] at hIoo
  refine ⟨hint, fun E hE ↦ ?_⟩
  rw [hρ.2 E hE]
  exact integral_congr_ae (hIcc.filter_mono (ae_mono Measure.restrict_le_self))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Frame
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A coordinate of the rotating normal frame is a continuous interval-BV function whose
Stieltjes density is the corresponding tangent coordinate. -/
theorem exists_normalVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = normalVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ normalVector (t : Real.Angle) i)
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
    · change HasDerivAt Real.sin (Real.cos t) t
      exact Real.hasDerivAt_sin t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop
    · change Continuous Real.cos
      fun_prop

/-- A coordinate of the rotating tangent frame is a continuous interval-BV function whose
Stieltjes density is the negative normal coordinate. -/
theorem exists_tangentVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = tangentVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ -normalVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i)
    (fun t : ℝ ↦ -normalVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt (fun t : ℝ ↦ -Real.sin t) (-Real.cos t) t
      convert (Real.hasDerivAt_sin t).neg using 1
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.cos t)
      fun_prop
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Transport
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

/-- Continuous monotone surjective reparametrization preserves the Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφ : Monotone φ)
    (hφs : Function.Surjective φ) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ φ
          boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
            hab F.boundedVariation hφ hφs
          right_continuous := fun _ ↦
            (hFc.comp hφc).continuousAt.continuousWithinAt }
        (g ∘ φ) Set.univ := by
  let Fφ : RightContinuousIntervalBV c d :=
    { toFun := F.toFun ∘ φ
      boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
        hab F.boundedVariation hφ hφs
      right_continuous := fun _ ↦
        (hFc.comp hφc).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fφ).map φ = intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
      hab hcd F.boundedVariation hFc hφc hφ hφs
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fφ).variation := by
    change IsFiniteMeasure Fφ.boundedVariation.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Fφ.boundedVariation
  have hgint : (intervalStieltjesMeasure Fφ).Integrable (g ∘ φ) :=
    (hgc.comp hφc).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fφ).variation.map φ) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map hφc.measurable hgm hgint]
  rfl

/-- Restricting a continuous Stieltjes integral agrees with integration on the subinterval. -/
theorem intervalStieltjesIntegral_Ioc_eq_inclusion
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) (l u : Set.Icc a b) (hlu : l ≤ u) :
    let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    intervalStieltjesIntegral F g (Ioc l u) =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ ι
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
        (g ∘ ι) Set.univ := by
  dsimp only
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
    ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
  let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
    ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
      (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
  let Fr : RightContinuousIntervalBV (l : ℝ) u :=
    { toFun := F.toFun ∘ ι
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map ι =
      (intervalStieltjesMeasure F).restrict (Ioc l u) :=
    BoundedVariationOn.vectorMeasure_map_Icc_inclusion F.boundedVariation hFc l u hlu
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ ι) :=
    (hgc.comp (continuous_subtype_val.subtype_mk _)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map ι) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map
    (continuous_subtype_val.subtype_mk _).measurable hgm hgint]
  rfl

/-- A continuous Stieltjes integral splits over a finite monotone partition. -/
theorem intervalStieltjesIntegral_eq_sum_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    intervalStieltjesIntegral F g Set.univ =
      ∑ i : Fin n, intervalStieltjesIntegral F g (Ioc (cuts i.castSucc) (cuts i.succ)) := by
  have hab : a ≤ b := by
    calc
      a = cuts 0 := hzero.symm
      _ ≤ cuts (Fin.last n) := hcuts (Fin.zero_le _)
      _ = b := hlast
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation := by
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  have hmeas (i : Fin n) : MeasurableSet (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    measurableSet_Ioc
  have hall : (intervalStieltjesMeasure F).Integrable g :=
    hgc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hint (i : Fin n) :
      (intervalStieltjesMeasure F).IntegrableOn g (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    hall.integrableOn
  have hpair : Set.Pairwise ((Finset.univ : Finset (Fin n)) : Set (Fin n))
      (Disjoint on fun i ↦ Ioc (cuts i.castSucc) (cuts i.succ)) := by
    intro i _ j _ hij
    change Disjoint (Ioc (cuts i.castSucc) (cuts i.succ))
      (Ioc (cuts j.castSucc) (cuts j.succ))
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hij_fin : i.succ ≤ j.castSucc := by
        simpa using Nat.succ_le_of_lt hij'
      exact (not_lt_of_ge (le_trans hxi.2 (hcuts hij_fin))) hxj.1
    · have hji_fin : j.succ ≤ i.castSucc := by
        simpa using Nat.succ_le_of_lt hji'
      exact (not_lt_of_ge (le_trans hxj.2 (hcuts hji_fin))) hxi.1
  rw [← MeasureTheory.VectorMeasure.setIntegral_biUnion_finset Finset.univ
    (fun i _ ↦ hmeas i) hpair (fun i _ ↦ hint i)]
  have hunion :
      (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Set.univ \ {cuts 0} := by
    rw [hcuts.iUnion_Ioc_fin]
    ext x
    simp only [mem_Ioc, mem_sdiff, mem_univ, true_and, mem_singleton_iff]
    constructor
    · rintro ⟨hx0, _⟩ hxe
      exact hx0.ne' hxe
    · intro hxe
      exact ⟨lt_of_le_of_ne (by
        change (cuts 0 : ℝ) ≤ (x : ℝ)
        simpa [hzero] using x.property.1) (fun hx ↦ hxe hx.symm),
        by
          change (x : ℝ) ≤ (cuts (Fin.last n) : ℝ)
          simpa [hlast] using x.property.2⟩
  simp only [Finset.mem_univ, iUnion_true]
  rw [hunion]
  rw [MeasureTheory.VectorMeasure.setIntegral_sdiff (s := Set.univ) (t := {cuts 0})
    MeasurableSet.univ (measurableSet_singleton _) hall.integrableOn (subset_univ _)]
  rw [MeasureTheory.VectorMeasure.integral_singleton]
  have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
    BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous F.boundedVariation hFc _
  rw [hz]
  simp

/-- Reversing both continuous integrand and BV integrator negates their Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g) :
    let r := Set.Icc.reverse hab
    let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
      (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
    intervalStieltjesIntegral
        { toFun := F.toFun ∘ r
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
        (g ∘ r) Set.univ =
      -intervalStieltjesIntegral F g Set.univ := by
  dsimp only
  let r := Set.Icc.reverse hab
  let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
    (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
  let Fr : RightContinuousIntervalBV a b :=
    { toFun := F.toFun ∘ r
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map r = -intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_reverse_Icc hab F.boundedVariation hFc
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ r) :=
    (hgc.comp (Set.Icc.continuous_reverse hab)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map r) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [MeasureTheory.VectorMeasure.restrict_univ]
  rw [← MeasureTheory.VectorMeasure.integral_neg_vectorMeasure, ← hmap,
    MeasureTheory.VectorMeasure.integral_map
      (Set.Icc.continuous_reverse hab).measurable hgm hgint]
  rfl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Continuous
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- A continuous function is integrable against a BV Stieltjes measure on a compact interval. -/
theorem RightContinuousIntervalBV.integrable_of_continuous {a b : ℝ} (F :
  RightContinuousIntervalBV a b)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) : (intervalStieltjesMeasure F).Integrable g := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  exact hg.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

private theorem intervalStieltjesIntegral_univ_eq_Ioc_of_continuous
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g {t | a < (t : ℝ)} := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  let cuts : Fin 2 → Set.Icc a b := Fin.cases a' (fun _ ↦ b')
  have hcuts : Monotone cuts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Std.le_refl,
      Nat.reduceAdd, Fin.cases_zero, cuts, a', b',
      Fin.mk_one, zero_le, nonpos_iff_eq_zero, one_ne_zero] at hij ⊢
    exact hab
  have hparts := intervalStieltjesIntegral_eq_sum_Ioc F hF g hg cuts hcuts rfl rfl
  have hset : Set.Ioc a' b' = {t : Set.Icc a b | a < (t : ℝ)} := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_ofPred_eq]
    constructor
    · exact fun ht ↦ ht.1
    · exact fun ht ↦ ⟨ht, t.property.2⟩
  dsimp [cuts] at hparts
  simpa [Fin.sum_univ_succ, hset] using hparts

/-- For a continuous driver and a continuous integrand, the closed-interval Stieltjes integral
agrees with the open-interval one: neither endpoint carries an atom. -/
theorem intervalStieltjesIntegral_univ_eq_Ioo_of_continuous {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g (Set.Ioo ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩) := by
  set a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  set b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hdiff : (Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b' ⊆ {a'} ∪ {b'} := by
    intro t ht
    rcases lt_or_ge a' t with hlt | hle
    · exact Or.inr (le_antisymm t.property.2 (not_lt.mp fun h ↦ ht.2 ⟨hlt, h⟩))
    · exact Or.inl (le_antisymm hle t.property.1)
  have hzero : intervalStieltjesIntegral F g
      ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') = 0 := by
    refine VectorMeasure.setIntegral_of_variation_apply_eq_zero _ (measure_mono_null hdiff ?_)
    refine measure_union_null ?_ ?_ <;>
      · rw [intervalStieltjesMeasure, F.boundedVariation.variation_vectorMeasure_singleton,
          hF.continuousAt.continuousWithinAt.rightLim_eq,
          hF.continuousAt.continuousWithinAt.leftLim_eq]
        simp
  have hsplit := VectorMeasure.setIntegral_inter_add_sdiff
    (μ := intervalStieltjesMeasure F) (B := ContinuousLinearMap.mul ℝ ℝ) (f := g)
    (s := (Set.univ : Set (Set.Icc a b))) (t := Set.Ioo a' b')
    MeasurableSet.univ measurableSet_Ioo (F.integrable_of_continuous hg).integrableOn
  rw [Set.univ_inter] at hsplit
  change intervalStieltjesIntegral F g (Set.Ioo a' b') +
    intervalStieltjesIntegral F g ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') =
    intervalStieltjesIntegral F g Set.univ at hsplit
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- Integration by parts for continuous BV functions on the full compact interval. -/
theorem intervalStieltjes_integration_by_parts_of_continuous
    (a b : ℝ) (hab : a ≤ b) (F G : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (hG : Continuous G.toFun) :
    intervalStieltjesIntegral F G.toFun Set.univ +
        intervalStieltjesIntegral G F.toFun Set.univ =
      F.toFun ⟨b, hab, le_rfl⟩ * G.toFun ⟨b, hab, le_rfl⟩ -
        F.toFun ⟨a, le_rfl, hab⟩ * G.toFun ⟨a, le_rfl, hab⟩ := by
  obtain ⟨left, hleft, hparts⟩ := intervalStieltjes_integration_by_parts a b hab F G
  have hleft_eq : Set.EqOn left F.toFun {t | a < (t : ℝ)} := by
    intro t ht
    change a < (t : ℝ) at ht
    have hnonempty : (Set.Iio t).Nonempty := by
      let s : Set.Icc a b := ⟨(a + (t : ℝ)) / 2, by constructor <;> linarith [t.property.2]⟩
      exact ⟨s, by change (a + (t : ℝ)) / 2 < (t : ℝ); linarith⟩
    have hne : (nhdsWithin t (Set.Iio t)).NeBot :=
      nhdsWithin_Iio_neBot' hnonempty le_rfl
    let _ : (nhdsWithin t (Set.Iio t)).NeBot := hne
    have hcont : Filter.Tendsto F.toFun (nhdsWithin t (Set.Iio t))
        (nhds (F.toFun t)) := hF.continuousAt.continuousWithinAt
    exact tendsto_nhds_unique (hleft t ht) hcont
  have hintegrand : intervalStieltjesIntegral G left {t | a < (t : ℝ)} =
      intervalStieltjesIntegral G F.toFun {t | a < (t : ℝ)} := by
    unfold intervalStieltjesIntegral
    exact MeasureTheory.VectorMeasure.setIntegral_congr_fun hleft_eq
  rw [intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab F hF G.toFun hG,
    intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab G hG F.toFun hF,
    ← hintegrand]
  exact hparts

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Affine
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

private def unitIntervalIdentity : RightContinuousIntervalBV 0 1 where
  toFun t := t
  boundedVariation := by
    apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
      Set.univ).boundedVariationOn (C := 1)
    intro t _
    rw [abs_of_nonneg t.property.1]
    exact t.property.2
  right_continuous t := continuous_subtype_val.continuousAt.continuousWithinAt

private theorem continuous_unitIntervalIdentity :
    Continuous unitIntervalIdentity.toFun :=
  continuous_subtype_val

/-- A continuous BV driver carries total Stieltjes mass equal to its increment. -/
theorem intervalStieltjesMeasure_univ_of_continuous {a b : ℝ} (hab : a ≤ b)
    (Q : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) :
    intervalStieltjesMeasure Q univ =
      Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩ := by
  have hu : (univ : Set (Icc a b)) = Icc ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ := by
    ext x
    simp only [mem_univ, mem_Icc, true_iff]
    exact x.property
  unfold intervalStieltjesMeasure
  rw [hu, Q.boundedVariation.vectorMeasure_Icc (show
      (⟨a, le_rfl, hab⟩ : Icc a b) ≤ ⟨b, hab, le_rfl⟩ from hab),
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq]

/-- An affine function of a continuous BV driver has that driver's Stieltjes measure, scaled by
the affine map's slope. -/
theorem intervalStieltjesMeasure_affine {a b : ℝ}
    (Q F : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) (u v : ℝ)
    (hF : ∀ t, F.toFun t = u + v * Q.toFun t) :
    intervalStieltjesMeasure F = v • intervalStieltjesMeasure Q := by
  have hFc : Continuous F.toFun := by
    rw [show F.toFun = fun t ↦ u + v * Q.toFun t from funext hF]
    exact continuous_const.add (continuous_const.mul hQ)
  apply VectorMeasure.ext_of_Icc
  intro x y hxy
  simp only [smul_apply]
  unfold intervalStieltjesMeasure
  rw [F.boundedVariation.vectorMeasure_Icc hxy, Q.boundedVariation.vectorMeasure_Icc hxy,
    hFc.continuousAt.continuousWithinAt.rightLim_eq,
    hFc.continuousAt.continuousWithinAt.leftLim_eq,
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq, hF x, hF y]
  ring

/-- Shifting a continuous BV driver and its integrand by constants shifts the interval Stieltjes
integral over the whole parameter interval by the integrand's shift times the driver's increment;
the driver's own shift has no effect. -/
theorem intervalStieltjesIntegral_add_const {a b : ℝ} (hab : a ≤ b)
    (F G : RightContinuousIntervalBV a b) (hF : Continuous F.toFun) (c : ℝ)
    (hFG : ∀ t, G.toFun t = F.toFun t + c) (g : Icc a b → ℝ) (hg : Continuous g) (d : ℝ) :
    intervalStieltjesIntegral G (fun t ↦ g t + d) univ =
      intervalStieltjesIntegral F g univ +
        d * (F.toFun ⟨b, hab, le_rfl⟩ - F.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  have hmeas : intervalStieltjesMeasure G = intervalStieltjesMeasure F := by
    rw [intervalStieltjesMeasure_affine F G hF c 1 fun t ↦ by rw [hFG t]; ring, one_smul]
  have hsum : (fun t ↦ g t + d) = g + fun _ ↦ d := rfl
  rw [intervalStieltjesIntegral_univ, intervalStieltjesIntegral_univ, hmeas, hsum,
    VectorMeasure.integral_add (F.integrable_of_continuous hg)
      (F.integrable_of_continuous continuous_const),
    VectorMeasure.integral_const, ← intervalStieltjesMeasure_univ_of_continuous hab F hF]
  simp

/-- The signed cross integral of two affine functions of one continuous BV driver. -/
theorem intervalStieltjesIntegral_affine_driver_cross {a b : ℝ} (hab : a ≤ b)
    (Q F G : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun)
    (u v w z : ℝ) (hF : ∀ t, F.toFun t = u + v * Q.toFun t)
    (hG : ∀ t, G.toFun t = w + z * Q.toFun t) :
    intervalStieltjesIntegral G F.toFun univ - intervalStieltjesIntegral F G.toFun univ =
      (u * z - w * v) * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Q).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Q.boundedVariation
  have hFm := intervalStieltjesMeasure_affine Q F hQ u v hF
  have hGm := intervalStieltjesMeasure_affine Q G hQ w z hG
  have hi (H : RightContinuousIntervalBV a b) (c d : ℝ)
      (hH : ∀ t, H.toFun t = c + d * Q.toFun t) :
      intervalStieltjesIntegral Q H.toFun univ =
        c * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) +
          d * intervalStieltjesIntegral Q Q.toFun univ := by
    have heq : H.toFun = (fun _ ↦ c) + d • Q.toFun := by
      funext t
      exact hH t
    have hc := Q.integrable_of_continuous (g := fun _ ↦ c) continuous_const
    have hd := Q.integrable_of_continuous (g := d • Q.toFun) (continuous_const.smul hQ)
    unfold intervalStieltjesIntegral
    simp only [VectorMeasure.restrict_univ, heq]
    rw [VectorMeasure.integral_add hc hd, VectorMeasure.integral_smul,
      VectorMeasure.integral_const, intervalStieltjesMeasure_univ_of_continuous hab Q hQ]
    simp
  have hFI := hi F u v hF
  have hGI := hi G w z hG
  unfold intervalStieltjesIntegral at hFI hGI ⊢
  simp only [VectorMeasure.restrict_univ] at hFI hGI ⊢
  rw [hFm, hGm, VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_smul_vectorMeasure, hFI, hGI]
  ring

theorem intervalStieltjesIntegral_affine_cross
    (F G : RightContinuousIntervalBV 0 1) (a b c d : ℝ)
    (hF : ∀ t, F.toFun t = a + b * (t : ℝ))
    (hG : ∀ t, G.toFun t = c + d * (t : ℝ)) :
    intervalStieltjesIntegral G F.toFun Set.univ -
        intervalStieltjesIntegral F G.toFun Set.univ = a * d - c * b := by
  simpa only [unitIntervalIdentity, sub_zero, mul_one] using
    intervalStieltjesIntegral_affine_driver_cross (by norm_num : (0 : ℝ) ≤ 1)
      unitIntervalIdentity F G continuous_unitIntervalIdentity a b c d hF hG

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Riemann-Stieltjes sums for continuous integrands

Left-endpoint sums over finite monotone partitions converge to the interval Stieltjes
integral of a continuous integrand against a continuous BV integrator, uniformly in the
mesh of the partition.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Two Stieltjes integrals differ by at most the uniform distance of their integrands
times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_le_of_abs_sub_le
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {g h : Set.Icc a b → ℝ}
    (hg : (intervalStieltjesMeasure F).Integrable g)
    (hh : (intervalStieltjesMeasure F).Integrable h)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, |g t - h t| ≤ ε) :
    |intervalStieltjesIntegral F g univ - intervalStieltjesIntegral F h univ| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← VectorMeasure.integral_sub hg hh, ← Real.norm_eq_abs]
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.mul ℝ ℝ) (by simpa only [Real.norm_eq_abs] using hbound)
  refine h.trans ?_
  calc
    ε * ‖ContinuousLinearMap.mul ℝ ℝ‖ * (intervalStieltjesMeasure F).variation.real univ ≤
        ε * 1 * (intervalStieltjesMeasure F).variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = _ := by ring

private theorem intervalStieltjesIntegral_sum_indicator_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {ι : Type*}
    (s : Finset ι) (l u : ι → Set.Icc a b) (c : ι → ℝ)
    (hlu : ∀ i ∈ s, l i ≤ u i) :
    intervalStieltjesIntegral F
        (fun t ↦ ∑ i ∈ s, (Ioc (l i) (u i)).indicator (fun _ ↦ c i) t) univ =
      ∑ i ∈ s, c i * (F.toFun (u i) - F.toFun (l i)) := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  rw [VectorMeasure.restrict_univ, VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [VectorMeasure.integral_indicator_const _ measurableSet_Ioc]
    change c i * F.boundedVariation.vectorMeasure (Ioc (l i) (u i)) = _
    rw [F.boundedVariation.vectorMeasure_Ioc (hlu i hi),
      (F.right_continuous (u i)).rightLim_eq, (F.right_continuous (l i)).rightLim_eq]
  · intro i _
    exact (MeasureTheory.integrable_const (c i)).indicator measurableSet_Ioc

/-- The error in a left-endpoint Stieltjes sum is controlled by the cell oscillation of the
integrand times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_sum_le_of_oscillation
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (i : Fin n) t, t ∈ Ioc (cuts i.castSucc) (cuts i.succ) →
      |g t - g (cuts i.castSucc)| ≤ ε) :
    |intervalStieltjesIntegral F g univ -
        ∑ i : Fin n, g (cuts i.castSucc) *
          (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  let step : Set.Icc a b → ℝ := fun t ↦ ∑ i : Fin n,
    (Ioc (cuts i.castSucc) (cuts i.succ)).indicator (fun _ ↦ g (cuts i.castSucc)) t
  have hstep : (intervalStieltjesMeasure F).Integrable step := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (MeasureTheory.integrable_const _).indicator measurableSet_Ioc
  have heval : intervalStieltjesIntegral F step univ =
      ∑ i : Fin n, g (cuts i.castSucc) *
        (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc)) :=
    intervalStieltjesIntegral_sum_indicator_Ioc (ι := Fin n) F Finset.univ
      (fun i ↦ cuts i.castSucc) (fun i ↦ cuts i.succ)
      (fun i ↦ g (cuts i.castSucc)) (fun i _ ↦ hcuts (Fin.castSucc_le_succ i))
  rw [← heval]
  apply intervalStieltjesIntegral_sub_le_of_abs_sub_le F
    (F.integrable_of_continuous hg) hstep hε
  have hatom : (intervalStieltjesMeasure F).variation {cuts 0} = 0 := by
    rw [VectorMeasure.variation_apply_singleton]
    have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
      BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous
        F.boundedVariation hF _
    simp [hz]
  have hae : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, t ≠ cuts 0 := by
    rw [ae_iff]
    have hset : {x : Set.Icc a b | ¬x ≠ cuts 0} = {cuts 0} := by
      ext x
      simp
    rw [hset]
    exact hatom
  filter_upwards [hae] with t ht
  have htcell : t ∈ ⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ) := by
    rw [hcuts.iUnion_Ioc_fin]
    refine ⟨lt_of_le_of_ne ?_ (Ne.symm ht), ?_⟩
    · change (cuts 0 : ℝ) ≤ (t : ℝ)
      simpa [hzero] using t.property.1
    · change (t : ℝ) ≤ (cuts (Fin.last n) : ℝ)
      simpa [hlast] using t.property.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htcell
  have hvalue : step t = g (cuts i.castSucc) := by
    dsimp [step]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      apply Set.indicator_of_notMem
      intro hj
      rcases lt_or_gt_of_ne hji with hji | hij
      · have hji' : j.succ ≤ i.castSucc := by simpa using Nat.succ_le_of_lt hji
        exact (not_lt_of_ge (hj.2.trans (hcuts hji'))) hi.1
      · have hij' : i.succ ≤ j.castSucc := by simpa using Nat.succ_le_of_lt hij
        exact (not_lt_of_ge (hi.2.trans (hcuts hij'))) hj.1
    · simp
  rw [hvalue]
  exact hosc i t hi

/-- Sufficiently fine partitions approximate a continuous Stieltjes integrand uniformly. -/
theorem exists_mesh_bound_intervalStieltjesIntegral_sub_sum
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b),
      Monotone cuts → (cuts 0 : ℝ) = a → (cuts (Fin.last n) : ℝ) = b →
      (∀ i : Fin n, (cuts i.succ : ℝ) - (cuts i.castSucc : ℝ) < δ) →
      |intervalStieltjesIntegral F g univ -
          ∑ i : Fin n, g (cuts i.castSucc) *
            (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
        ε * (intervalStieltjesMeasure F).variation.real univ := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun cuts hcuts hzero hlast hmesh ↦ ?_⟩
  apply intervalStieltjesIntegral_sub_sum_le_of_oscillation F hF hg cuts hcuts hzero hlast
    hε.le
  intro i t ht
  have hdist : dist t (cuts i.castSucc) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (show (cuts i.castSucc : ℝ) ≤ (t : ℝ) from ht.1.le))]
    exact (sub_le_sub_right (show (t : ℝ) ≤ (cuts i.succ : ℝ) from ht.2) _).trans_lt
      (hmesh i)
  simpa only [Real.dist_eq] using (hmod hdist).le

/-- Left-endpoint Stieltjes sums converge along any family of partitions whose mesh
tends to zero. -/
theorem tendsto_stieltjesSum_of_mesh_tendsto_zero
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) (N : ℕ → ℕ)
    (cuts : ∀ k, Fin (N k + 1) → Set.Icc a b)
    (hcuts : ∀ k, Monotone (cuts k))
    (hzero : ∀ k, (cuts k 0 : ℝ) = a)
    (hlast : ∀ k, (cuts k (Fin.last (N k)) : ℝ) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (N k),
      (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ) :
    Filter.Tendsto (fun k ↦ ∑ i : Fin (N k), g (cuts k i.castSucc) *
      (F.toFun (cuts k i.succ) - F.toFun (cuts k i.castSucc)))
      Filter.atTop (nhds (intervalStieltjesIntegral F g univ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (intervalStieltjesMeasure F).variation.real univ with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  have hpos : 0 < ε / (V + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, happrox⟩ :=
    exists_mesh_bound_intervalStieltjesIntegral_sub_sum F hF hg hpos
  filter_upwards [hmesh δ hδ] with k hk
  have hbound := happrox (cuts k) (hcuts k) (hzero k) (hlast k) hk
  rw [Real.dist_eq, abs_sub_comm]
  apply hbound.trans_lt
  have hcancel : ε / (V + 1) * (V + 1) = ε :=
    div_mul_cancel₀ ε (by positivity)
  change ε / (V + 1) * V < ε
  nlinarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Stieltjes / Shift
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Translate a continuous interval-BV representative and its Stieltjes measure. -/
theorem exists_intervalBV_shift_add {a b c : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV (a + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV a b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc a b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  let φ : Icc a b → Icc (a + c) (b + c) := fun t ↦
    ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  let ψ : Icc (a + c) (b + c) → Icc a b := fun t ↦
    ⟨(t : ℝ) - c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hφc : Continuous φ := (continuous_subtype_val.add_const c).subtype_mk _
  have hψc : Continuous ψ := (continuous_subtype_val.sub continuous_const).subtype_mk _
  have hφm : Monotone φ := fun x y hxy ↦ by
    change (x : ℝ) + c ≤ (y : ℝ) + c
    linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]
  have hφs : Function.Surjective φ := by
    intro y
    refine ⟨ψ y, ?_⟩
    apply Subtype.ext
    simp [φ, ψ]
  have hφi : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    simpa [φ] using congrArg Subtype.val hxy
  let e : Icc a b ≃ₜ Icc (a + c) (b + c) :=
    { toFun := φ
      invFun := ψ
      left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      continuous_toFun := hφc
      continuous_invFun := hψc }
  let hgbv := BoundedVariationOn.comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c)
    f.boundedVariation hφm hφs
  let g : RightContinuousIntervalBV a b :=
    { toFun := f.toFun ∘ φ
      boundedVariation := hgbv
      right_continuous := fun t ↦
        (hfc.comp hφc).continuousAt.continuousWithinAt }
  refine ⟨g, fun _ ↦ rfl, ?_⟩
  intro E hE
  have hmap := BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c) hab f.boundedVariation hfc hφc hφm hφs
  have hφE : MeasurableSet (φ '' E) := e.measurableEmbedding.measurableSet_image' hE
  change hgbv.vectorMeasure E = f.boundedVariation.vectorMeasure (φ '' E)
  rw [← hmap, VectorMeasure.map_apply _ hφc.measurable hφE,
    hφi.preimage_image]

/-- Specialize interval translation to an interval starting at zero. -/
theorem exists_intervalBV_shift_from_zero {b c : ℝ} (hb : 0 ≤ b)
    (f : RightContinuousIntervalBV (0 + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV 0 b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc 0 b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc 0 b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  exact exists_intervalBV_shift_add (a := 0) (b := b) (c := c) hb f hfc

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Basic
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

instance angleMeasurableSpace : MeasurableSpace Real.Angle := borel Real.Angle

instance angleBorelSpace : BorelSpace Real.Angle := ⟨rfl⟩

/-- An exterior normal direction at a point of a convex body. -/
@[expose]
def IsExteriorNormal (K : ConvexBody Point) (p : Point) (a : Real.Angle) : Prop :=
  ∀ q ∈ (K : Set Point), inner ℝ (q - p) (normalVector a) ≤ 0

/-- Boundary points with exactly one exterior unit normal. -/
@[expose]
def regularBoundary (K : ConvexBody Point) : Set Point :=
  {p | p ∈ frontier (K : Set Point) ∧ ∃! a, IsExteriorNormal K p a}

/-- The unique exterior normal at regular points, extended by zero elsewhere. -/
@[expose]
def exteriorNormalAngle (K : ConvexBody Point) (p : Point) : Real.Angle := by
  classical
  exact if h : ∃! a, IsExteriorNormal K p a then h.exists.choose else 0

/-- A nontrivial segment presentation and a perpendicular angular direction. -/
@[expose]
def IsSegmentPresentation (K : ConvexBody Point) (d : Point × Point × Real.Angle) : Prop :=
  d.1 ≠ d.2.1 ∧ (K : Set Point) = segment ℝ d.1 d.2.1 ∧
    inner ℝ (d.2.1 - d.1) (normalVector d.2.2) = 0

/-- Surface measure in angular coordinates, including point and segment bodies. -/
@[expose]
def surfaceAreaMeasure (K : ConvexBody Point) : Measure Real.Angle := by
  classical
  exact if (K : Set Point).Subsingleton then 0
  else if h : ∃ d, IsSegmentPresentation K d then
    let d := h.choose
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))
  else
    Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Exterior Normal
-/

public section

noncomputable section

namespace MovingSofa

open Set

/-- Every frontier point of a convex body with nonempty interior admits an exterior unit normal. -/
theorem exists_isExteriorNormal_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a, IsExteriorNormal K p a := by
  have hpnot : p ∉ interior (K : Set Point) := by
    have hpK : p ∈ K := by
      change p ∈ (K : Set Point)
      rw [← K.isClosed.closure_eq]
      exact frontier_subset_closure hp
    exact (mem_frontier_iff_notMem_interior hpK).mp hp
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open K.convex.interior isOpen_interior hpnot
  let fc : Point →L[ℝ] ℝ := f.toContinuousLinearMap
  have hfne : fc ≠ 0 := by
    obtain ⟨q, hq⟩ := hK
    intro hzero
    have h := hf q hq
    have hfp : fc p = 0 := by rw [hzero]; rfl
    have hfq : fc q = 0 := by rw [hzero]; rfl
    change fc p < fc q at h
    linarith
  let w : Point := -(InnerProductSpace.toDual ℝ Point).symm fc
  have hw : w ≠ 0 := by
    intro hzero
    apply hfne
    apply (InnerProductSpace.toDual ℝ Point).symm.injective
    simpa using neg_eq_zero.mp hzero
  obtain ⟨a, ha⟩ := exists_angle_normalVector_eq (u := ‖w‖⁻¹ • w) (by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)])
  refine ⟨a, ?_⟩
  rw [IsExteriorNormal, ha]
  intro q hq
  have hclosed : IsClosed {q : Point | fc p ≤ fc q} :=
    isClosed_le continuous_const fc.continuous
  have hinterior : interior (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} :=
    fun q hq ↦ (hf q hq).le
  have hsubset : (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} := by
    rw [← K.isClosed.closure_eq,
      ← K.convex.closure_interior_eq_closure_of_nonempty_interior hK]
    exact closure_minimal hinterior hclosed
  have hfpq := hsubset hq
  rw [inner_smul_right, inner_neg_right, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  dsimp only [fc] at hfpq ⊢
  rw [map_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg w))
    (neg_nonpos.mpr (sub_nonneg.mpr hfpq))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Graph Definitions
-/

public section

noncomputable section

namespace MovingSofa

/-- Project the convex body horizontally after translating and changing orthonormal frame. -/
@[expose]
def horizontalProjection (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set ℝ :=
  (fun p : Point ↦ e (p - o) 0) '' (K : Set Point)

/-- The infimum and supremum of the body’s horizontal projection in the chosen frame. -/
@[expose]
def horizontalBounds (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : ℝ × ℝ :=
  (sInf (horizontalProjection K o e), sSup (horizontalProjection K o e))

/-- The supremum of the body’s vertical section at a given horizontal coordinate. -/
@[expose]
def upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (x : ℝ) : ℝ :=
  sSup {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}

/-- The argument of a planar vector, viewed as an angle modulo a full turn. -/
@[expose]
def vectorNormalAngle (p : Point) : Real.Angle :=
  (Complex.arg ⟨p 0, p 1⟩ : ℝ)

/-- The normal vector associated to a nonzero planar vector is its normalization. -/
theorem normalVector_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    normalVector (vectorNormalAngle p) = ‖p‖⁻¹ • p := by
  let z : ℂ := ⟨p 0, p 1⟩
  have hz : z ≠ 0 := by
    intro hz
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re hz
    · exact congrArg Complex.im hz
  have hnorm : ‖z‖ = ‖p‖ := by
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    congr 1
    simp only [z, Complex.normSq_apply, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, pow_two]
  ext i
  fin_cases i
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.cos_arg hz
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.sin_arg z

/-- Weight the upper graph by its normal direction and arc-length Jacobian. -/
@[expose]
def upperGraphSurfaceIntegrand (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (x : ℝ) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) *
    Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Regularity
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

instance angleCompactSpace : CompactSpace Real.Angle :=
  AddCircle.homeomorphCircle'.symm.compactSpace

/-- The unit normal depends continuously on its angle. -/
theorem continuous_normalVector_angle :
    Continuous normalVector := by
  let c : Real.Angle → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases t.cos (fun _ ↦ t.sin) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_cos
    · exact Real.Angle.continuous_sin
  have heq : normalVector = (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

private theorem isClosed_isExteriorNormal (K : ConvexBody Point) :
    IsClosed {z : Point × Real.Angle | IsExteriorNormal K z.1 z.2} := by
  change IsClosed {z : Point × Real.Angle |
    ∀ q ∈ (K : Set Point), inner ℝ (q - z.1) (normalVector z.2) ≤ 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro _
  apply isClosed_le
  · exact (continuous_const.sub continuous_fst).inner
      (continuous_normalVector_angle.comp continuous_snd)
  · exact continuous_const

private def normalGraph (K : ConvexBody Point) : Set (Point × Real.Angle) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧ IsExteriorNormal K z.1 z.2}

private theorem isCompact_normalGraph (K : ConvexBody Point) :
    IsCompact (normalGraph K) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hclosed : IsClosed (normalGraph K) := by
    exact (isClosed_frontier.preimage continuous_fst).inter (isClosed_isExteriorNormal K)
  apply (hfront.prod isCompact_univ).of_isClosed_subset
  · exact hclosed
  · rintro ⟨p, a⟩ ⟨hp, _⟩
    exact ⟨hp, Set.mem_univ a⟩

private def normalDomain (K : ConvexBody Point) : Set Point :=
  Prod.fst '' normalGraph K

private theorem isCompact_normalDomain (K : ConvexBody Point) :
    IsCompact (normalDomain K) :=
  (isCompact_normalGraph K).image continuous_fst

private def separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    Set (Point × (Real.Angle × Real.Angle)) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧
    IsExteriorNormal K z.1 z.2.1 ∧ IsExteriorNormal K z.1 z.2.2 ∧
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2}

private theorem isCompact_separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPairs K n) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hrel₁ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.1} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hrel₂ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.2} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hsep : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2} := by
    exact isClosed_le continuous_const
      ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))
  have hfclosed : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      z.1 ∈ frontier (K : Set Point)} :=
    isClosed_frontier.preimage continuous_fst
  have hclosed : IsClosed (separatedNormalPairs K n) := by
    have h := ((hfclosed.inter hrel₁).inter hrel₂).inter hsep
    simpa only [separatedNormalPairs, Set.inter_def, Set.mem_ofPred_eq, and_assoc] using h
  apply (hfront.prod (isCompact_univ.prod isCompact_univ)).of_isClosed_subset hclosed
  rintro ⟨p, a, b⟩ ⟨hp, _⟩
  exact ⟨hp, Set.mem_univ _, Set.mem_univ _⟩

private def separatedNormalPoints (K : ConvexBody Point) (n : ℕ) : Set Point :=
  Prod.fst '' separatedNormalPairs K n

private theorem isCompact_separatedNormalPoints (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPoints K n) :=
  (isCompact_separatedNormalPairs K n).image continuous_fst

private theorem regularBoundary_eq_normalDomain_sdiff_iUnion (K : ConvexBody Point) :
    regularBoundary K = normalDomain K \ ⋃ n, separatedNormalPoints K n := by
  ext p
  constructor
  · rintro ⟨hp, a, ha, hua⟩
    refine ⟨⟨(p, a), ⟨hp, ha⟩, rfl⟩, ?_⟩
    intro hnonunique
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hnonunique
    obtain ⟨⟨q, b, c⟩, ⟨_, hb, hc, hdist⟩, rfl⟩ := hn
    rw [hua b hb, hua c hc, dist_self] at hdist
    have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  · rintro ⟨hdom, hnot⟩
    obtain ⟨⟨q, a⟩, ⟨hp, ha⟩, hqp⟩ := hdom
    change q = p at hqp
    subst q
    refine ⟨hp, a, ha, ?_⟩
    intro b hb
    by_contra hba
    have hdpos : 0 < dist a b := dist_pos.mpr (Ne.symm hba)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdpos
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(p, (a, b)), ?_, rfl⟩⟩
    exact ⟨hp, ha, hb, hn.le⟩

/-- Points with a unique exterior normal form a Borel set. -/
theorem measurableSet_regularBoundary (K : ConvexBody Point) :
    MeasurableSet (regularBoundary K) := by
  rw [regularBoundary_eq_normalDomain_sdiff_iUnion]
  exact (isCompact_normalDomain K).measurableSet.diff
    (MeasurableSet.iUnion fun n ↦ (isCompact_separatedNormalPoints K n).measurableSet)

/-- The exterior normal varies continuously on the regular boundary. -/
theorem continuousOn_exteriorNormalAngle_regularBoundary (K : ConvexBody Point) :
    ContinuousOn (exteriorNormalAngle K) (regularBoundary K) := by
  have hnormal (p : Point) (hp : p ∈ regularBoundary K) :
      IsExteriorNormal K p (exteriorNormalAngle K p) := by
    rcases hp.2 with ⟨a, ha, hua⟩
    dsimp only [exteriorNormalAngle]
    split
    · rename_i h
      exact h.exists.choose_spec
    · rename_i h
      exact (h ⟨a, ha, hua⟩).elim
  have hunique (p : Point) (hp : p ∈ regularBoundary K) (a : Real.Angle)
      (ha : IsExteriorNormal K p a) : a = exteriorNormalAngle K p := by
    rcases hp.2 with ⟨b, hb, hub⟩
    exact (hub a ha).trans (hub _ (hnormal p hp)).symm
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_of_isClosed_graph
  have hgraph : Function.graph ((regularBoundary K).domRestrict (exteriorNormalAngle K)) =
      {z : (regularBoundary K) × Real.Angle | IsExteriorNormal K z.1 z.2} := by
    ext z
    constructor
    · intro hz
      change exteriorNormalAngle K z.1 = z.2 at hz
      change IsExteriorNormal K z.1 z.2
      rw [← hz]
      exact hnormal z.1 z.1.2
    · intro hz
      change exteriorNormalAngle K z.1 = z.2
      exact (hunique z.1 z.1.2 z.2 hz).symm
  rw [hgraph]
  exact (isClosed_isExteriorNormal K).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- The exterior normal is measurable for any measure restricted to the regular boundary. -/
theorem aemeasurable_exteriorNormalAngle_restrict_regularBoundary
    (K : ConvexBody Point) (μ : Measure Point) :
    AEMeasurable (exteriorNormalAngle K) (μ.restrict (regularBoundary K)) :=
  aemeasurable_restrict_of_measurable_subtype (measurableSet_regularBoundary K)
    (continuousOn_exteriorNormalAngle_regularBoundary K).domRestrict.measurable

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two angular unit normals perpendicular to a nonzero planar vector are equal or antipodal. -/
theorem normalVector_eq_or_eq_add_pi_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) : s = t ∨ s = t + (Real.pi : Real.Angle) := by
  let o : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hnorm (a : Real.Angle) : ‖normalVector a‖ = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a =>
      rw [EuclideanSpace.norm_eq]
      simp [normalVector, frame, Fin.sum_univ_two]
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal o hv (hnorm s) (hnorm t) hvs hvt with
    h | h
  · left
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · exact congrFun (congrArg WithLp.ofLp h) 0
        · exact congrFun (congrArg WithLp.ofLp h) 1
  · right
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · have h0 := congrFun (congrArg WithLp.ofLp h) 0
          simpa [normalVector, frame, Real.cos_add_pi] using h0
        · have h1 := congrFun (congrArg WithLp.ofLp h) 1
          simpa [normalVector, frame, Real.sin_add_pi] using h1

private theorem dirac_add_antipode_eq_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) :
    Measure.dirac s + Measure.dirac (s + (Real.pi : Real.Angle)) =
      Measure.dirac t + Measure.dirac (t + (Real.pi : Real.Angle)) := by
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal hv hvs hvt with h | h
  · rw [h]
  · rw [h]
    have hpi : (t + (Real.pi : Real.Angle)) + (Real.pi : Real.Angle) = t := by
      rw [add_assoc, Real.Angle.coe_pi_add_coe_pi, add_zero]
    rw [hpi, add_comm]

/-- The atomic segment measure is independent of its segment presentation. -/
theorem segmentPresentation_measure_eq (K : ConvexBody Point)
    {d c : Point × Point × Real.Angle}
    (hd : IsSegmentPresentation K d) (hc : IsSegmentPresentation K c) :
    ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) =
      ENNReal.ofReal (dist c.1 c.2.1) •
        (Measure.dirac c.2.2 + Measure.dirac (c.2.2 + (Real.pi : Real.Angle))) := by
  have hseg : segment ℝ d.1 d.2.1 = segment ℝ c.1 c.2.1 := hd.2.1.symm.trans hc.2.1
  have hlen : dist d.1 d.2.1 = dist c.1 c.2.1 := EuclideanGeometry.dist_eq_of_segment_eq hseg
  have hcn : inner ℝ (d.2.1 - d.1) (normalVector c.2.2) = 0 :=
    EuclideanGeometry.inner_direction_eq_zero_of_segment_eq hseg hc.2.2
  rw [hlen, dirac_add_antipode_eq_of_orthogonal (sub_ne_zero.mpr hd.1.symm) hd.2.2 hcn]

/-- A singleton convex body has zero surface measure. -/
theorem surfaceAreaMeasure_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure K = 0 := by
  simp [surfaceAreaMeasure, hK]

private theorem surfaceAreaMeasure_eq_chosenSegment (K : ConvexBody Point)
    (hK : ¬(K : Set Point).Subsingleton) (hseg : ∃ d, IsSegmentPresentation K d) :
    surfaceAreaMeasure K =
      ENNReal.ofReal (dist hseg.choose.1 hseg.choose.2.1) •
        (Measure.dirac hseg.choose.2.2 +
          Measure.dirac (hseg.choose.2.2 + ((Real.pi : ℝ) : Real.Angle))) := by
  simp [surfaceAreaMeasure, hK, hseg]

/-- A nondegenerate segment presentation makes the represented convex body nonsingleton. -/
theorem not_subsingleton_of_isSegmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    ¬(K : Set Point).Subsingleton := by
  intro hK
  apply hd.1
  apply hK
  · rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  · rw [hd.2.1]
    exact right_mem_segment ℝ _ _

/-- The surface measure of a segment is its length times the two normal atoms. -/
theorem surfaceAreaMeasure_eq_segmentPresentation (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure K = ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) := by
  let hseg : ∃ c, IsSegmentPresentation K c := ⟨d, hd⟩
  rw [surfaceAreaMeasure_eq_chosenSegment K
    (not_subsingleton_of_isSegmentPresentation K hd) hseg]
  exact segmentPresentation_measure_eq K hseg.choose_spec hd

/-- The surface area measure of a singleton convex body is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  infer_instance

/-- The surface area measure of a convex body with a segment presentation is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  exact (Measure.dirac d.2.2 +
    Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle))).smul_finite
      ENNReal.ofReal_ne_top

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment Faces
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem not_both_mem_short_angleArc {E : Set Real.Angle} {a b : ℝ}
    (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hE : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b)
    (t : Real.Angle) : ¬(t ∈ E ∧ t + (Real.pi : Real.Angle) ∈ E) := by
  rintro ⟨ht, htpi⟩
  obtain ⟨s, hs, hst⟩ := hE ht
  obtain ⟨u, hu, hut⟩ := hE htpi
  have hang : (u : Real.Angle) = ((s + Real.pi : ℝ) : Real.Angle) := by
    calc
      (u : Real.Angle) = t + (Real.pi : Real.Angle) := hut
      _ = (s : Real.Angle) + (Real.pi : Real.Angle) := by rw [← hst]
      _ = ((s + Real.pi : ℝ) : Real.Angle) := Real.Angle.coe_add _ _ |>.symm
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hlow : -(2 * Real.pi) < u - (s + Real.pi) := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  have hupp : u - (s + Real.pi) < 0 := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  rw [hk] at hlow hupp
  have hkneg : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hkgt : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
  rw [← Int.cast_zero] at hkneg
  have hcast_neg_one : (((-1 : ℤ) : ℝ)) = -1 := by norm_num
  rw [← hcast_neg_one] at hkgt
  have hkneg' : k < 0 := Int.cast_lt.mp hkneg
  have hkgt' : (-1 : ℤ) < k := Int.cast_lt.mp hkgt
  omega

/-- A normal perpendicular to a segment exposes the whole segment. -/
theorem exposedEdge_eq_segment_of_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) = 0) :
    exposedEdge K t = (K : Set Point) := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hconst : ∀ p ∈ (K : Set Point),
      inner ℝ p (normalVector t) = inner ℝ d.1 (normalVector t) := by
    intro p hp
    rw [hd.2.1, segment_eq_image'] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    rw [inner_add_left, inner_smul_left, ht, mul_zero, add_zero]
  have hsupport : supportValue K t = inner ℝ d.1 (normalVector t) := by
    apply le_antisymm
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact (hconst p hp).le
    · exact inner_le_supportValue K hfst t
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    change inner ℝ p (normalVector t) = supportValue K t
    rw [hconst p hp, hsupport]

private theorem exposedEdge_subset_endpoints_of_not_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0) :
    exposedEdge K t ⊆ {d.1, d.2.1} := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hsnd : d.2.1 ∈ K := by
    change d.2.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact right_mem_segment ℝ _ _
  intro p hp
  have hpK : p ∈ segment ℝ d.1 d.2.1 := by
    rw [← hd.2.1]
    exact hp.1
  rw [segment_eq_image'] at hpK
  obtain ⟨u, hu, rfl⟩ := hpK
  have hx := inner_le_supportValue K hfst t
  have hy := inner_le_supportValue K hsnd t
  rw [← hp.2] at hx hy
  simp only [inner_add_left, inner_smul_left] at hx hy
  let c := inner ℝ (d.2.1 - d.1) (normalVector t)
  change inner ℝ d.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hx
  change inner ℝ d.2.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hy
  have hdiff : inner ℝ d.2.1 (normalVector t) =
      inner ℝ d.1 (normalVector t) + c := by
    dsimp only [c]
    rw [inner_sub_left]
    ring
  rw [hdiff] at hy
  have hc : c ≠ 0 := ht
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hu0 : u = 0 := by
      apply le_antisymm _ hu.1
      by_contra hnot
      have hupos : 0 < u := lt_of_not_ge hnot
      nlinarith
    simp [hu0]
  · have hu1 : u = 1 := by
      apply le_antisymm hu.2
      by_contra hnot
      have hult : u < 1 := lt_of_not_ge hnot
      nlinarith
    simp [hu1]

/-- The face-union formula for a segment on an angular arc shorter than a half-turn. -/
theorem surfaceAreaMeasure_face_union_of_segmentPresentation
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) (E : Set Real.Angle) (hE : MeasurableSet E)
    {a b : ℝ} (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hsubset : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) :
    surfaceAreaMeasure K E =
      Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  have hnotboth := not_both_mem_short_angleArc hab hshort hsubset d.2.2
  have hnormalPi :
      normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
    induction d.2.2 using Real.Angle.induction_on with
    | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
  have hpiorth :
      inner ℝ (d.2.1 - d.1)
        (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [hnormalPi, inner_neg_right, hd.2.2, neg_zero]
  by_cases hn : d.2.2 ∈ E
  · have hnpi : d.2.2 + (Real.pi : Real.Angle) ∉ E := fun hnpi ↦ hnotboth ⟨hn, hnpi⟩
    have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
      apply Set.Subset.antisymm
      · intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        exact hpt.1
      · intro p hp
        exact Set.mem_iUnion₂.mpr ⟨d.2.2, hn, by
          rw [exposedEdge_eq_segment_of_orthogonal K d hd d.2.2 hd.2.2]
          exact hp⟩
    rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
    simp [hE, hn, hnpi, edist_dist]
  · by_cases hnpi : d.2.2 + (Real.pi : Real.Angle) ∈ E
    · have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
        apply Set.Subset.antisymm
        · intro p hp
          obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
          exact hpt.1
        · intro p hp
          exact Set.mem_iUnion₂.mpr ⟨d.2.2 + (Real.pi : Real.Angle), hnpi, by
            rw [exposedEdge_eq_segment_of_orthogonal K d hd _ hpiorth]
            exact hp⟩
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
      simp [hE, hn, hnpi, edist_dist]
    · have hunion : (⋃ t ∈ E, exposedEdge K t) ⊆ {d.1, d.2.1} := by
        intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        have htorth : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0 := by
          intro hortho
          rcases normalVector_eq_or_eq_add_pi_of_orthogonal
              (sub_ne_zero.mpr hd.1.symm) hortho hd.2.2 with h | h
          · exact hn (h ▸ ht)
          · exact hnpi (h ▸ ht)
        exact exposedEdge_subset_endpoints_of_not_orthogonal K d hd t htorth hpt
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
      have hzero : Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) = 0 := by
        let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
        exact measure_mono_null hunion
          ((Set.finite_singleton d.2.1).insert d.1 |>.measure_zero _)
      rw [hzero]
      simp [hE, hn, hnpi]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Analysis / Surface Measure / Segment Graph
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A singleton convex body has equal horizontal projection bounds. -/
theorem horizontalBounds_eq_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 = (horizontalBounds K o e).2 := by
  obtain ⟨p, hp⟩ := K.nonempty
  have hset : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hK hx hp⟩
  simp [horizontalBounds, horizontalProjection, hset]

/-- Every surface-area integral of a singleton convex body vanishes. -/
theorem surfaceAreaMeasure_integral_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (ψ : Real.Angle → ℝ) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  simp

private theorem horizontalProjection_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalProjection K o e = Set.uIcc (e (a - o) 0) (e (b - o) 0) := by
  rw [horizontalProjection, hK, segment_eq_image']
  calc
    (fun p : Point ↦ e (p - o) 0) ''
        ((fun t : ℝ ↦ a + t • (b - a)) '' Set.Icc 0 1) =
        (fun t : ℝ ↦ e (a - o) 0 + t * (e (b - o) 0 - e (a - o) 0)) ''
          Set.Icc 0 1 := by
      rw [Set.image_image]
      congr 1
      funext t
      simp only [map_sub, map_add, map_smul, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    _ = segment ℝ (e (a - o) 0) (e (b - o) 0) :=
      (segment_eq_image' ℝ (e (a - o) 0) (e (b - o) 0)).symm
    _ = Set.uIcc (e (a - o) 0) (e (b - o) 0) := segment_eq_uIcc _ _

private theorem horizontalBounds_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalBounds K o e =
      (min (e (a - o) 0) (e (b - o) 0), max (e (a - o) 0) (e (b - o) 0)) := by
  rw [horizontalBounds, horizontalProjection_segment K o e hK]
  simp [Set.uIcc, csInf_Icc, csSup_Icc]

private theorem coordinate_normal_second_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    e (normalVector d.2.2) 1 = 0 := by
  have hb := horizontalBounds_segment K o e hd.2.1
  rw [hb] at hbounds
  dsimp only at hbounds
  have hx : e (d.1 - o) 0 = e (d.2.1 - o) 0 := by
    have hle₁ := min_le_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hle₂ := min_le_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₁ := le_max_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₂ := le_max_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    linarith
  have hdir0 : e (d.2.1 - d.1) 0 = 0 := by
    simp only [map_sub, PiLp.sub_apply] at hx ⊢
    linarith
  have hdir_ne : e (d.2.1 - d.1) 1 ≠ 0 := by
    intro h
    have hz : d.2.1 - d.1 = 0 := e.injective (by
      simp only [map_zero]
      ext i
      fin_cases i
      · exact hdir0
      · exact h)
    exact hd.1.symm (sub_eq_zero.mp hz)
  have hinner : inner ℝ (e (d.2.1 - d.1)) (e (normalVector d.2.2)) = 0 := by
    rw [e.inner_map_map]
    exact hd.2.2
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    hdir0, mul_zero, zero_add] at hinner
  exact (mul_eq_zero.mp hinner).resolve_right hdir_ne

/-- A segment with zero horizontal width contributes zero against weights supported on
normals with positive vertical coordinate. -/
theorem segment_integral_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  have hn := coordinate_normal_second_eq_zero_of_horizontalBounds_eq K o e d hd hbounds
  have hψn : ψ d.2.2 = 0 := hsupport d.2.2 (by linarith)
  have hnpi : e (normalVector (d.2.2 + (Real.pi : Real.Angle))) 1 = 0 := by
    have hv : normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply, hn, neg_zero]
  have hψnpi : ψ (d.2.2 + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by rw [hnpi]; exact hε)
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
    (MeasureTheory.integrable_dirac (by finiteness))]
  simp [hψn, hψnpi]

private theorem upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Icc (e (a - o) 0) (e (b - o) 0)) :
    upperGraphHeight K o e x = e (a - o) 1 +
      ((x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
        (e (b - o) 1 - e (a - o) 1) := by
  let t := (x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)
  let y := e (a - o) 1 + t * (e (b - o) 1 - e (a - o) 1)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have hfiber : {z : ℝ | o + e.symm !₂[x, z] ∈ (K : Set Point)} = {y} := by
    ext z
    rw [Set.mem_ofPred_eq, hK, segment_eq_image', Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, hr, heq⟩
      have heq' := congrArg (fun p : Point ↦ e (p - o)) heq
      have heq0 := congrFun (congrArg WithLp.ofLp heq') 0
      have heq1 := congrFun (congrArg WithLp.ofLp heq') 1
      have hrt : r = t := by
        dsimp [t]
        simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero,
          smul_eq_mul] at heq0
        simp at heq0
        apply (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr
        simp only [map_sub, PiLp.sub_apply]
        linarith
      dsimp [y]
      rw [← hrt]
      simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_one,
          smul_eq_mul] at heq1
      simp at heq1
      simp only [map_sub, PiLp.sub_apply]
      linarith
    · intro hzy
      subst z
      refine ⟨t, ht, ?_⟩
      apply e.injective
      ext i
      fin_cases i
      · have hdx : e b 0 - e a 0 ≠ 0 := by
          simp only [map_sub, PiLp.sub_apply] at hab
          linarith
        simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [t]
        simp only [map_sub, PiLp.sub_apply]
        field_simp [hdx]
        ring
      · simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [y]
        simp only [map_sub, PiLp.sub_apply]
        ring
  rw [upperGraphHeight, hfiber, csSup_singleton]

private theorem deriv_upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (e (a - o) 0) (e (b - o) 0)) :
    deriv (upperGraphHeight K o e) x =
      (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0) := by
  let g : ℝ → ℝ := fun y ↦ e (a - o) 1 +
    ((y - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
      (e (b - o) 1 - e (a - o) 1)
  have hg : HasDerivAt g
      ((e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)) x := by
    dsimp [g]
    have hsub : HasDerivAt (fun y : ℝ ↦ y - e (a - o) 0) 1 x :=
      (hasDerivAt_id x).sub_const _
    have hdiv := HasDerivAt.div_const hsub (e (b - o) 0 - e (a - o) 0)
    have hmul := HasDerivAt.mul_const hdiv (e (b - o) 1 - e (a - o) 1)
    convert hmul.const_add (e (a - o) 1) using 1
    all_goals ring
  have heq : upperGraphHeight K o e =ᶠ[nhds x] g := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact upperGraphHeight_segment_of_lt K o e hK hab ⟨hy.1.le, hy.2.le⟩
  exact (hg.congr_of_eventuallyEq heq).deriv

private theorem segment_graph_normal (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    q ≠ 0 ∧ inner ℝ (b - a) q = 0 ∧
      e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ ∧
      dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  have hdx : 0 < e (b - o) 0 - e (a - o) 0 := sub_pos.mpr hab
  have hden : e b 0 - e a 0 ≠ 0 := by
    simp only [map_sub, PiLp.sub_apply] at hab
    linarith
  have horth : inner ℝ (b - a) q = 0 := by
    rw [← e.inner_map_map]
    simp only [q, m, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, map_sub, PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hden]
    ring
  have hup : e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ := by
    rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
    simp [q]
  have hlen : dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
    rw [dist_eq_norm, ← e.norm_map]
    have hv : e (b - a) = (e (b - o) 0 - e (a - o) 0) • !₂[1, m] := by
      ext i
      fin_cases i
      · simp [m]
      · simp [m]
        field_simp [hden]
    rw [show a - b = -(b - a) by module, map_neg, norm_neg, hv, norm_smul,
      Real.norm_eq_abs, abs_of_pos hdx]
    congr 1
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [m, Real.norm_eq_abs, pow_two]
    ring
  exact ⟨hq, horth, hup, hlen⟩

private theorem segment_graph_integrand_ae (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    upperGraphSurfaceIntegrand K o e ψ =ᵐ[
        volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))]
      fun _ ↦ ψ (vectorNormalAngle q) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hnormq : Real.sqrt (1 + m ^ 2) = ‖q‖ := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [← restrict_Ioo_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ ?_
  rw [upperGraphSurfaceIntegrand,
    deriv_upperGraphHeight_segment_of_lt K o e hK hab hx]
  change ψ (vectorNormalAngle q) * Real.sqrt (1 + m ^ 2) = _
  rw [hnormq]

private theorem integrable_segment_graph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := by
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  have hc : Integrable (fun _ : ℝ ↦ ψ (vectorNormalAngle
      (e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1])) *
      ‖e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1]‖)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := integrable_const _
  exact hc.congr hae.symm

private theorem segment_graph_integral (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (e (a - o) 0) (e (b - o) 0),
        upperGraphSurfaceIntegrand K o e ψ x := by
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  let t := vectorNormalAngle q
  obtain ⟨hq, horth, hup, hlen⟩ := segment_graph_normal o e hab
  have hd : IsSegmentPresentation K (a, b, t) := by
    refine ⟨?_, hK, ?_⟩
    · intro heq
      have := hab
      simp only at heq
      rw [heq] at this
      exact this.false
    · dsimp [t]
      rw [normalVector_vectorNormalAngle hq, inner_smul_right, horth, mul_zero]
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hdowncoord : e (normalVector (t + (Real.pi : Real.Angle))) 1 = -‖q‖⁻¹ := by
    have hv : normalVector (t + (Real.pi : Real.Angle)) = -normalVector t := by
      induction t using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply]
    exact congrArg Neg.neg hup
  have hdown : ψ (t + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by
      rw [hdowncoord]
      have hinv : 0 < ‖q‖⁻¹ := inv_pos.mpr hqnorm
      linarith)
  have hlhs : (∫ u, ψ u ∂surfaceAreaMeasure K) = dist a b * ψ t := by
    rw [surfaceAreaMeasure_eq_segmentPresentation K (a, b, t) hd]
    rw [MeasureTheory.integral_smul_measure]
    rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
      (MeasureTheory.integrable_dirac (by finiteness))]
    simp [hdown, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist a b)]
  rw [hlhs, hlen]
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  rw [integral_congr_ae hae]
  have hdx : 0 ≤ e (b - o) 0 - e (a - o) 0 := sub_nonneg.mpr hab.le
  have hdx' : 0 ≤ e b 0 - e a 0 := by
    simp only [map_sub, PiLp.sub_apply] at hdx
    linarith
  simp only [Fin.isValue, map_sub, PiLp.sub_apply, sub_sub_sub_cancel_right, norm_map,
    integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    Real.volume_real_Icc, smul_eq_mul, t, q, m]
  rw [max_eq_left hdx']
  ring

/-- The surface-area integral of a nonvertical segment agrees with its upper
graph integral. -/
theorem segment_graph_formula (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
        (volume.restrict (Set.Icc (horizontalBounds K o e).1
          (horizontalBounds K o e).2)) ∧
      (∫ t, ψ t ∂surfaceAreaMeasure K) =
        ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
          upperGraphSurfaceIntegrand K o e ψ x := by
  rw [horizontalBounds_segment K o e hd.2.1] at hbounds ⊢
  dsimp only at hbounds ⊢
  have hne : e (d.1 - o) 0 ≠ e (d.2.1 - o) 0 := by
    intro heq
    simp only [map_sub, PiLp.sub_apply] at heq hbounds
    rw [heq, min_self, max_self] at hbounds
    exact hbounds.false
  rcases lt_or_gt_of_ne hne with hab | hba
  · rw [min_eq_left hab.le, max_eq_right hab.le] at hbounds ⊢
    exact ⟨integrable_segment_graph K o e ψ hd.2.1 hbounds,
      segment_graph_integral K o e ψ hd.2.1 hbounds hε hsupport⟩
  · rw [min_eq_right hba.le, max_eq_left hba.le] at hbounds ⊢
    have hK' : (K : Set Point) = segment ℝ d.2.1 d.1 := by
      rw [segment_symm]
      exact hd.2.1
    exact ⟨integrable_segment_graph K o e ψ hK' hbounds,
      segment_graph_integral K o e ψ hK' hbounds hε hsupport⟩

/-- A nonsingleton planar convex body with empty interior has a segment presentation. -/
theorem exists_segmentPresentation_of_interior_empty (K : ConvexBody Point)
    (hsub : ¬(K : Set Point).Subsingleton) (hint : interior (K : Set Point) = ∅) :
    ∃ d, IsSegmentPresentation K d := by
  obtain ⟨a, b, hab, hK⟩ := K.exists_eq_segment_of_interior_empty hsub hint
  let orient : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let _ : Fact (Module.finrank ℝ Point = 2) := ⟨by simp [Point]⟩
  let n := ‖b - a‖⁻¹ • orient.rotation (Real.pi / 2 : ℝ) (b - a)
  have hvnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hn : ‖n‖ = 1 := by
    rw [norm_smul, (orient.rotation (Real.pi / 2 : ℝ)).norm_map]
    simp [hvnorm.ne']
  obtain ⟨t, ht⟩ := exists_angle_normalVector_eq hn
  refine ⟨(a, b, t), hab, hK, ?_⟩
  rw [ht]
  exact orient.inner_smul_rotation_pi_div_two_right (b - a) ‖b - a‖⁻¹

end MovingSofa

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Curve.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Curve.Area`.
* `Curve.AreaTransport`.
* `Curve.Concatenation`.
* `Curve.AreaAdditivity`.
* `Curve.CyclicRotation`.
* `Curve.Jordan.Basic`.
* `Curve.Jordan.Orientation`.
* `Curve.Jordan.Area`.
* `Curve.Jordan.ArcArea`.
* `Curve.Jordan.Parametrization`.
* `Curve.Jordan.UnitSphere`.
* `Curve.Jordan.Winding`.
* `Curve.Jordan.RadialWinding`.
* `Curve.Jordan.WindingConcatenation`.
* `Curve.Jordan.CyclicRotation`.
* `Curve.Jordan.WindingKernel`.
* `Curve.Jordan.WindingLocalConstancy`.
* `Curve.Jordan.WindingLifts`.
* `Curve.NullRange`.
* `Curve.SegmentArea`.
* `Curve.SegmentArea.Parametrization`.
* `Curve.SmoothIntervalPaths`.
* `Curve.Jordan.RadialLoop`.
* `Curve.StieltjesChainRule`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Area
-/

public section

noncomputable section

namespace MovingSofa

/-- The constant planar path, as a continuous path of bounded variation. -/
@[expose]
def constBVPath (a b : ℝ) (p : Point) : ContinuousBVPaths a b :=
  ⟨fun _ ↦ p, continuous_const, fun i ↦ by
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]⟩

/-- View one coordinate of a continuous BV path as a right-continuous BV function. -/
@[expose]
def continuousBVCoordinate {a b : ℝ} (x : ContinuousBVPaths a b) (i : Fin 2) :
    RightContinuousIntervalBV a b where
  toFun t := x.val t i
  boundedVariation := x.property.2 i
  right_continuous _ :=
    ((PiLp.continuous_apply 2 _ i).comp x.property.1).continuousAt.continuousWithinAt

/-- Half the difference of the two coordinate Stieltjes integrals, giving signed area. -/
@[expose]
def curveAreaFunctional {a b : ℝ} (x : ContinuousBVPaths a b) : ℝ :=
  (intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ x.val t 0) Set.univ -
    intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ x.val t 1) Set.univ) / 2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Area Transport
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- A continuous monotone surjection preserves continuous bounded variation. -/
theorem continuousBVPaths_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  exact ⟨y, rfl⟩

/-- A continuous monotone surjection preserves signed path area. -/
theorem curveArea_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  refine ⟨y, rfl, ?_⟩
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      φ hφc hφm hφs,
    intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      φ hφc hφm hφs]
  rfl

/-- A continuous monotone surjective reparametrisation identifies the signed areas of two given
paths whenever one is the composite of the other with it. -/
theorem curveAreaFunctional_eq_of_comp_monotone_surjective {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφm : Monotone φ)
    (hφs : Function.Surjective φ) (hy : y.val = x.val ∘ φ) :
    curveAreaFunctional y = curveAreaFunctional x := by
  obtain ⟨z, hz, hza⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hφm hφs
  rw [show y = z from Subtype.ext (hy.trans hz.symm)]
  exact hza

/-- Translating a continuous BV path shifts its signed area by the cross product of the
translation vector with the path's total displacement, halved. -/
theorem curveAreaFunctional_add_constBVPath {a b : ℝ} (hab : a ≤ b)
    (x : ContinuousBVPaths a b) (v : Point) :
    curveAreaFunctional (x + constBVPath a b v) =
      curveAreaFunctional x +
        (v 0 * (x.val ⟨b, hab, le_rfl⟩ 1 - x.val ⟨a, le_rfl, hab⟩ 1) -
          v 1 * (x.val ⟨b, hab, le_rfl⟩ 0 - x.val ⟨a, le_rfl, hab⟩ 0)) / 2 := by
  have hcont : ∀ i : Fin 2, Continuous (continuousBVCoordinate x i).toFun :=
    fun i ↦ (PiLp.continuous_apply 2 _ i).comp x.property.1
  have hval : ∀ (i : Fin 2) (t : Set.Icc a b),
      (continuousBVCoordinate (x + constBVPath a b v) i).toFun t =
        (continuousBVCoordinate x i).toFun t + v i := by
    intro i t
    change (x.val t + v) i = x.val t i + v i
    simp
  have hint : ∀ i j : Fin 2,
      intervalStieltjesIntegral (continuousBVCoordinate (x + constBVPath a b v) i)
          (fun t ↦ (x + constBVPath a b v).val t j) univ =
        intervalStieltjesIntegral (continuousBVCoordinate x i) (fun t ↦ x.val t j) univ +
          v j * (x.val ⟨b, hab, le_rfl⟩ i - x.val ⟨a, le_rfl, hab⟩ i) := by
    intro i j
    rw [show (fun t ↦ (x + constBVPath a b v).val t j) =
      fun t ↦ (continuousBVCoordinate x j).toFun t + v j from funext (hval j)]
    exact intervalStieltjesIntegral_add_const hab (continuousBVCoordinate x i) _ (hcont i)
      (v i) (hval i) _ (hcont j) (v j)
  unfold curveAreaFunctional
  rw [hint 1 0, hint 0 1]
  ring

/-- Reversing a continuous BV path negates its signed area. -/
theorem curveArea_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) :
    let r := Set.Icc.reverse hab
    let y : ContinuousBVPaths a b :=
      ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
          (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
    curveAreaFunctional y = -curveAreaFunctional x := by
  dsimp only
  let r := Set.Icc.reverse hab
  let y : ContinuousBVPaths a b :=
    ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
        (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
  have hcoord (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate y p)
          (fun t ↦ y.val t q) Set.univ =
        -intervalStieltjesIntegral (continuousBVCoordinate x p)
          (fun t ↦ x.val t q) Set.univ := by
    have hrev := intervalStieltjesIntegral_comp_reverse hab
      (continuousBVCoordinate x p)
      ((PiLp.continuous_apply 2 _ p).comp x.property.1)
      (fun t ↦ x.val t q) ((PiLp.continuous_apply 2 _ q).comp x.property.1)
    change intervalStieltjesIntegral _ _ Set.univ = -intervalStieltjesIntegral _ _ Set.univ
    exact hrev
  unfold curveAreaFunctional
  rw [hcoord 1 0, hcoord 0 1]
  ring

/-- A continuous antitone surjection negates signed path area. -/
theorem curveArea_comp_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφa : Antitone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = -curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i) hφa hφs⟩
  let r := Set.Icc.reverse hcd
  let ψ : Set.Icc c d → Set.Icc a b := φ ∘ r
  have hψc : Continuous ψ := hφc.comp (Set.Icc.continuous_reverse hcd)
  have hψm : Monotone ψ := fun _ _ hst ↦
    hφa ((Set.Icc.antitone_reverse hcd) hst)
  have hψs : Function.Surjective ψ :=
    hφs.comp (Set.Icc.surjective_reverse hcd)
  obtain ⟨z, hz, hzarea⟩ :=
    curveArea_comp_monotone_surjective hab hcd x ψ hψc hψm hψs
  have hyrev : curveAreaFunctional z = -curveAreaFunctional y := by
    have hz' : z.val = y.val ∘ r := by
      rw [hz]
      rfl
    let yr : ContinuousBVPaths c d :=
      ⟨y.val ∘ r, y.property.1.comp (Set.Icc.continuous_reverse hcd), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hcd (y.property.2 i)
          (Set.Icc.antitone_reverse hcd) (Set.Icc.surjective_reverse hcd)⟩
    have hyr := curveArea_comp_reverse hcd y
    change curveAreaFunctional yr = -curveAreaFunctional y at hyr
    have hzy : z = yr := by
      apply Subtype.ext
      exact hz'
    simpa [hzy] using hyr
  refine ⟨y, rfl, ?_⟩
  linarith

/-- A constant path has zero signed area, including on an empty parameter interval. -/
theorem curveAreaFunctional_eq_zero_of_constant
    {a b : ℝ} (x : ContinuousBVPaths a b) (p : Point)
    (hx : ∀ t, x.val t = p) : curveAreaFunctional x = 0 := by
  have hfun : x.val = fun _ ↦ p := funext hx
  have hcoord (i : Fin 2) : (fun t ↦ x.val t i) = fun _ ↦ p i := by
    funext t
    rw [hx t]
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 0)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 0)
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 1)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 1)
  unfold curveAreaFunctional
  unfold intervalStieltjesIntegral
  rw [MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 0) (g := fun _ ↦ p 0)
      (fun _ _ ↦ congrFun (hcoord 0) _),
    MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 1) (g := fun _ ↦ p 1)
      (fun _ _ ↦ congrFun (hcoord 1) _)]
  rw [MeasureTheory.VectorMeasure.setIntegral_const,
    MeasureTheory.VectorMeasure.setIntegral_const]
  by_cases hab : a ≤ b
  · let _ : Fact (a ≤ b) := ⟨hab⟩
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder,
      Filter.map_const]
  · let _ : IsEmpty (Set.Icc a b) :=
      ⟨fun t ↦ hab (le_trans t.property.1 t.property.2)⟩
    have hfilters : (Filter.atTop : Filter (Set.Icc a b)) = Filter.atBot :=
      Subsingleton.elim _ _
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder, hfilters]

/-- A continuous monotone or antitone surjection transports BV paths and signed area. -/
theorem curveArea_comp_monotone_or_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
      (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
      (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x) := by
  rcases hφ with hm | ha
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    refine ⟨y, hy, fun _ ↦ harea, ?_⟩
    intro ha
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    refine ⟨y, hy, ?_, fun _ ↦ harea⟩
    intro hm
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Concatenation
-/

public section

noncomputable section

namespace MovingSofa

/-- A continuous path of bounded variation with an ordered real parameter interval. -/
structure RectifiablePathData where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b

/-- An ordered interval partition identifies the path with a nonempty list of parametrized
pieces. -/
@[expose]
def IsPathConcatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) : Prop :=
  0 < n ∧ ∃ cuts : Fin (n + 1) → Set.Icc Γ.a Γ.b,
    Monotone cuts ∧ (cuts 0 : ℝ) = Γ.a ∧ (cuts (Fin.last n) : ℝ) = Γ.b ∧
    ∀ i : Fin n,
      ∃ (φ : Set.Icc (0 : ℝ) 1 →
          Set.Icc (cuts i.castSucc : ℝ) (cuts i.succ : ℝ))
        (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (pieces i).a (pieces i).b),
        Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
        Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
        ∀ s, Γ.path.val ⟨(φ s : ℝ),
          le_trans (cuts i.castSucc).property.1 (φ s).property.1,
          le_trans (φ s).property.2 (cuts i.succ).property.2⟩ = (pieces i).path.val (ψ s)

/-- A concatenated path stays inside the union of the ranges of its pieces. -/
theorem IsPathConcatenation.range_subset_iUnion {Γ : RectifiablePathData} {n : ℕ}
    {pieces : Fin n → RectifiablePathData} (h : IsPathConcatenation Γ pieces) :
    Set.range Γ.path.val ⊆ ⋃ i, Set.range (pieces i).path.val := by
  classical
  obtain ⟨hn, cuts, hmono, hfirst, hlast, hconc⟩ := h
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : Fin n,
      (cuts i.castSucc : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (cuts i.succ : ℝ) := by
    set T := Finset.univ.filter fun i : Fin (n + 1) ↦ (t : ℝ) ≤ (cuts i : ℝ) with hT
    have hmemT : ∀ i, i ∈ T ↔ (t : ℝ) ≤ (cuts i : ℝ) := fun i ↦ by simp [hT]
    have hTne : T.Nonempty :=
      ⟨Fin.last n, (hmemT _).mpr (by rw [hlast]; exact t.property.2)⟩
    have hmin : (t : ℝ) ≤ (cuts (T.min' hTne) : ℝ) := (hmemT _).mp (T.min'_mem hTne)
    rcases Fin.eq_zero_or_eq_succ (T.min' hTne) with hzero | ⟨j, hj⟩
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · rw [show ((⟨0, hn⟩ : Fin n).castSucc) = 0 from rfl, hfirst]
        exact t.property.1
      · exact (hzero ▸ hmin).trans
          (Subtype.coe_le_coe.mpr (hmono (Fin.zero_le ((⟨0, hn⟩ : Fin n).succ))))
    · refine ⟨j, ?_, by rw [← hj]; exact hmin⟩
      by_contra hlt
      have hle := T.min'_le _ ((hmemT j.castSucc).mpr (not_le.mp hlt).le)
      rw [hj] at hle
      exact absurd (lt_of_lt_of_le (Fin.castSucc_lt_succ (i := j)) hle) (lt_irrefl _)
  obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hconc i
  obtain ⟨s, hs⟩ := hφs ⟨(t : ℝ), hi₁, hi₂⟩
  have hval : ((φ s : ℝ)) = (t : ℝ) := congrArg Subtype.val hs
  refine Set.mem_iUnion.mpr ⟨i, ψ s, ?_⟩
  rw [← heq s]
  exact congrArg _ (Subtype.ext hval)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Area Additivity
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

theorem curveArea_concatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) (h : IsPathConcatenation Γ pieces) :
    curveAreaFunctional Γ.path = ∑ i, curveAreaFunctional (pieces i).path := by
  rcases h with ⟨_, cuts, hcuts, hcuts_zero, hcuts_last, hpieces⟩
  have hcoord (i : Fin n) (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate Γ.path p)
          (fun t ↦ Γ.path.val t q) (Ioc (cuts i.castSucc) (cuts i.succ)) =
        intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
          (fun t ↦ (pieces i).path.val t q) Set.univ := by
    obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hpieces i
    let l := cuts i.castSucc
    let u := cuts i.succ
    let ι : Set.Icc (l : ℝ) u → Set.Icc Γ.a Γ.b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hp : BoundedVariationOn ((continuousBVCoordinate Γ.path p).toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top (continuousBVCoordinate Γ.path p).boundedVariation
        (eVariationOn.comp_le_of_monotoneOn _ ι
          (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    let Fp : RightContinuousIntervalBV (l : ℝ) u :=
      { toFun := (continuousBVCoordinate Γ.path p).toFun ∘ ι
        boundedVariation := hp
        right_continuous := fun _ ↦
          (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
            (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
    rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate Γ.path p)
      ((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t q)
      ((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1) l u
      (hcuts (Fin.castSucc_le_succ i))]
    change intervalStieltjesIntegral Fp
        ((fun t ↦ Γ.path.val t q) ∘ ι) Set.univ =
      intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
        (fun t ↦ (pieces i).path.val t q) Set.univ
    rw [intervalStieltjesIntegral_comp_monotone_surjective
      (show (l : ℝ) ≤ u from hcuts (Fin.castSucc_le_succ i)) (by norm_num) Fp
      (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      ((fun t ↦ Γ.path.val t q) ∘ ι)
      (((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      φ hφc hφm hφs,
      intervalStieltjesIntegral_comp_monotone_surjective
        (pieces i).ordered (by norm_num) (continuousBVCoordinate (pieces i).path p)
        ((PiLp.continuous_apply 2 _ p).comp (pieces i).path.property.1)
        (fun t ↦ (pieces i).path.val t q)
        ((PiLp.continuous_apply 2 _ q).comp (pieces i).path.property.1)
        ψ hψc hψm hψs]
    congr 1
    · congr 1
      funext s
      simpa [Fp, continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z p) (heq s)
    · funext s
      simpa [continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z q) (heq s)
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 1)
      ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 0) ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 0)
      ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 1) ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last]
  simp_rw [hcoord]
  rw [← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Cyclic Rotation
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Restrict a continuous BV path to a closed subinterval. -/
@[expose]
def ContinuousBVPaths.restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (_hlu : l ≤ u) : ContinuousBVPaths (l : ℝ) u :=
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun t ↦
    ⟨t, le_trans l.property.1 t.property.1, le_trans t.property.2 u.property.2⟩
  ⟨x.val ∘ ι, x.property.1.comp (continuous_subtype_val.subtype_mk _), fun i ↦
    ne_top_of_le_ne_top (x.property.2 i)
      (eVariationOn.comp_le_of_monotoneOn (fun t ↦ x.val t i) ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))⟩

private theorem curveArea_restrict_Ioc
    {a b : ℝ} (x : ContinuousBVPaths a b) (l u : Set.Icc a b) (hlu : l ≤ u) :
    (intervalStieltjesIntegral (continuousBVCoordinate x 1)
        (fun t ↦ x.val t 0) (Ioc l u) -
      intervalStieltjesIntegral (continuousBVCoordinate x 0)
        (fun t ↦ x.val t 1) (Ioc l u)) / 2 =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      l u hlu,
    intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      l u hlu]
  rfl

/-- Signed path area is additive along any monotone chain of cuts of the parameter interval. -/
theorem curveArea_eq_sum_restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    curveAreaFunctional x =
      ∑ i : Fin n, curveAreaFunctional (ContinuousBVPaths.restrict x (cuts i.castSucc)
        (cuts i.succ) (hcuts (Fin.castSucc_le_succ i))) := by
  simp_rw [← curveArea_restrict_Ioc x]
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      cuts hcuts hzero hlast,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      cuts hcuts hzero hlast, ← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

/-- Split the signed area of a continuous BV path at any parameter value. -/
theorem curveArea_eq_restriction_add_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hs1 : a ≤ (s : ℝ) := s.property.1
  have hs2 : (s : ℝ) ≤ b := s.property.2
  change curveAreaFunctional x =
    curveAreaFunctional (ContinuousBVPaths.restrict x a' s hs1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' hs2)
  have hcuts : Monotone (![a', s, b'] : Fin 3 → Set.Icc a b) := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i
    · exact hs1
    · exact hs2
  have hsum := curveArea_eq_sum_restrict x ![a', s, b'] hcuts rfl rfl
  rw [Fin.sum_univ_two] at hsum
  exact hsum

/-- The tail and head restrictions have signed areas summing to the original area. -/
theorem curveArea_cyclic_cut_sum
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) +
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) := by
  rw [curveArea_eq_restriction_add_restriction hab x s, add_comm]

/-- Package a restricted continuous BV path with its interval endpoints. -/
def ContinuousBVPaths.restrictionData {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hlu : l ≤ u) : RectifiablePathData where
  a := l
  b := u
  ordered := hlu
  path := ContinuousBVPaths.restrict x l u hlu

/-- A tail-then-head concatenation preserves the signed area. -/
theorem curveArea_cyclic_rotation
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (rotated : ContinuousBVPaths c d) (hcd : c ≤ d)
    (hrot : IsPathConcatenation
      { a := c, b := d, ordered := hcd, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1]) :
    curveAreaFunctional rotated = curveAreaFunctional x := by
  rw [curveArea_concatenation _ _ hrot]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousBVPaths.restrictionData]
  exact (curveArea_cyclic_cut_sum hab x s).symm

/-- Concatenating continuous paths with matching endpoints preserves coordinatewise variation. -/
theorem boundedVariation_concatUnitIntervals_coordinate
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) (i : Fin 2) :
    BoundedVariationOn (fun t ↦ Function.concatUnitIntervals p.val q.val t i) Set.univ := by
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let o : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩
  let w : Set.Icc (0 : ℝ) 2 := ⟨2, by norm_num⟩
  let f := fun t ↦ Function.concatUnitIntervals p.val q.val t i
  have hzo : z ≤ o := by change (0 : ℝ) ≤ 1; norm_num
  have how : o ≤ w := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit := eVariationOn.Icc_add_Icc f hzo how (Set.mem_univ o)
  simp only [Set.univ_inter] at hsplit
  have hwhole : Set.Icc z w = Set.univ := by
    ext t
    change ((0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2) ↔ True
    exact iff_true_intro t.property
  rw [hwhole] at hsplit
  change eVariationOn f Set.univ ≠ ⊤
  rw [← hsplit]
  apply ENNReal.add_ne_top.mpr
  constructor
  · refine ne_top_of_le_ne_top (p.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc z o) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) i)
            (Set.Icc z o) := by
              apply eVariationOn.congr
              intro t ht
              have ht' : (t : ℝ) ≤ 1 := by exact ht.2
              simp [f, Function.concatUnitIntervals, ht']
      _ ≤ eVariationOn (fun t ↦ p.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ p.val t i)
              (t := Set.Icc z o)
              (fun t : Set.Icc (0 : ℝ) 2 ↦ Set.projIcc 0 1 (by norm_num) (t : ℝ))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num) hxy)
              (mapsTo_univ _ _))
  · refine ne_top_of_le_ne_top (q.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc o w) =
          eVariationOn
            (fun t : Set.Icc (0 : ℝ) 2 ↦
              q.val (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1)) i)
            (Set.Icc o w) := by
              apply eVariationOn.congr
              intro t ht
              have hleft : (1 : ℝ) ≤ t := by exact ht.1
              have ht' : ¬(t : ℝ) ≤ 1 ∨ (t : ℝ) = 1 := by
                rcases lt_or_eq_of_le hleft with h | h
                · exact Or.inl (not_le_of_gt h)
                · exact Or.inr h.symm
              rcases ht' with ht' | htEq
              · simp [f, Function.concatUnitIntervals, ht']
              · simpa [f, Function.concatUnitIntervals, htEq] using congrArg (fun z ↦ z i) hjoin
      _ ≤ eVariationOn (fun t ↦ q.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ q.val t i)
              (t := Set.Icc o w)
              (fun t : Set.Icc (0 : ℝ) 2 ↦
                Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num)
                (sub_le_sub_right (show (_ : ℝ) ≤ _ from hxy) 1))
              (mapsTo_univ _ _))

private def concatUnitPaths (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate p q hjoin⟩

private theorem isPathConcatenation_concatUnitPaths
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := concatUnitPaths p q hjoin }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p },
        { a := 0, b := 1, ordered := by norm_num, path := q }] := by
  let cuts : Fin 3 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cuts, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hij ⊢
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨t, by simp [cuts]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk continuous_subtype_val _
    · intro x y hxy
      exact hxy
    · intro y
      exact ⟨⟨y, by simpa [cuts] using y.property⟩, Subtype.ext rfl⟩
    · intro t
      have ht : (t : ℝ) ≤ 1 := t.property.2
      simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, ht]
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(t : ℝ) + 1, by
          change (1 : ℝ) ≤ (t : ℝ) + 1 ∧ (t : ℝ) + 1 ≤ 2
          constructor <;> linarith [t.property.1, t.property.2]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
    · intro x y hxy
      change (x : ℝ) + 1 ≤ (y : ℝ) + 1
      linarith [show (x : ℝ) ≤ y from hxy]
    · intro y
      refine ⟨⟨(y : ℝ) - 1, ?_⟩, Subtype.ext ?_⟩
      · have hy1 : (1 : ℝ) ≤ y := by exact y.property.1
        have hy2 : (y : ℝ) ≤ 2 := by exact y.property.2
        constructor <;> linarith [y.property.1, y.property.2]
      · simp [φ]
    · intro t
      by_cases ht : (t : ℝ) = 0
      · have htSub : t = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext ht
        rw [htSub]
        simpa [φ, ψ, concatUnitPaths, Function.concatUnitIntervals] using hjoin
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, htpos]

private def unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private theorem continuous_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitIntervalParam a b hab) := Set.Icc.continuous_convexComb _ _

private theorem monotone_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitIntervalParam a b hab) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + (s : ℝ) * b ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith

private theorem surjective_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitIntervalParam a b hab) := by
  intro x
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨⟨0, by norm_num⟩, Subtype.ext ?_⟩
    change (1 - (0 : ℝ)) * a + 0 * a = (x : ℝ)
    have hx : (x : ℝ) = a := le_antisymm x.property.2 x.property.1
    simp [hx]
  · refine ⟨⟨((x : ℝ) - a) / (b - a), ?_⟩, Subtype.ext ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right x.property.2 a)
    · change (1 - ((x : ℝ) - a) / (b - a)) * a + ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

private theorem unitIntervalParam_zero (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩ := by
  exact Set.Icc.convexComb_zero _ _

private theorem unitIntervalParam_one (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩ := by
  exact Set.Icc.convexComb_one _ _

/-- Rotate a closed continuous BV path by concatenating its tail and head. -/
theorem exists_cyclic_rotation_path {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
  let tail := ContinuousBVPaths.restrict x s ⟨b, hab, le_rfl⟩ s.property.2
  let head := ContinuousBVPaths.restrict x ⟨a, le_rfl, hab⟩ s s.property.1
  obtain ⟨p, hp⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.2 tail
    (unitIntervalParam s b s.property.2) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.1 head
    (unitIntervalParam a s s.property.1) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  have hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩ := by
    rw [hp, hq]
    simp only [Function.comp_apply, unitIntervalParam_one, unitIntervalParam_zero]
    exact hx
  let rotated := concatUnitPaths p q hjoin
  have hrot : IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
    obtain ⟨hn, cuts, hm, hz, ho, hc⟩ := isPathConcatenation_concatUnitPaths p q hjoin
    refine ⟨hn, cuts, hm, hz, ho, ?_⟩
    intro i
    fin_cases i
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 0
      refine ⟨φ, unitIntervalParam s b s.property.2 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = p.val (ψ t) at h
      rw [hp] at h
      exact h
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 1
      refine ⟨φ, unitIntervalParam a s s.property.1 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = q.val (ψ t) at h
      rw [hq] at h
      exact h
  refine ⟨rotated, ?_, hrot⟩
  change Function.concatUnitIntervals p.val q.val = _
  rw [hp, hq]
  rfl

/-- Construct an area-preserving cyclic rotation of a closed continuous BV path. -/
theorem exists_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] ∧
      curveAreaFunctional rotated = curveAreaFunctional x := by
  obtain ⟨rotated, hr, hrot⟩ := exists_cyclic_rotation_path hab x s hx
  exact ⟨rotated, hr, hrot,
    curveArea_cyclic_rotation hab x s rotated (by norm_num) hrot⟩

private theorem mem_range_convexComb {a b : ℝ} (l u z : Set.Icc a b)
    (hlz : l ≤ z) (hzu : z ≤ u) : z ∈ Set.range (Set.Icc.convexComb l u) := by
  obtain ⟨t, ht⟩ := surjective_unitIntervalParam (l : ℝ) u (hlz.trans hzu)
    ⟨z, hlz, hzu⟩
  refine ⟨t, Subtype.ext ?_⟩
  have h := congrArg (fun y : Set.Icc (l : ℝ) u ↦ (y : ℝ)) ht
  exact h

/-- Cutting and rejoining a closed path does not change its carrier. -/
theorem range_cyclic_concat {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s : Set.Icc a b)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩) :
    Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)) = Set.range x := by
  have hjoin : (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩) ⟨1, by norm_num⟩ =
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ⟨0, by norm_num⟩ := by
    simpa using hx.symm
  rw [Function.range_concatUnitIntervals _ _ hjoin]
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.range_comp_subset_range _ _) (Set.range_comp_subset_range _ _)
  · rintro _ ⟨t, rfl⟩
    by_cases hst : s ≤ t
    · obtain ⟨r, hr⟩ := mem_range_convexComb s ⟨b, hab, le_rfl⟩ t hst t.property.2
      exact Or.inl ⟨r, congrArg x hr⟩
    · obtain ⟨r, hr⟩ := mem_range_convexComb ⟨a, le_rfl, hab⟩ s t t.property.1
        (le_of_not_ge hst)
      exact Or.inr ⟨r, congrArg x hr⟩

/-- Every point of a nondegenerate closed path occurs before its terminal parameter. -/
theorem exists_param_lt_top_of_mem_range {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b → Point)
    (hx : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    {p : Point} (hp : p ∈ Set.range x) :
    ∃ s : Set.Icc a b, (s : ℝ) < b ∧ x s = p := by
  obtain ⟨s, hs⟩ := hp
  by_cases hsb : (s : ℝ) < b
  · exact ⟨s, hsb, hs⟩
  · have hst : s = ⟨b, hab.le, le_rfl⟩ :=
      Subtype.ext (le_antisymm s.property.2 (le_of_not_gt hsb))
    exact ⟨⟨a, le_rfl, hab.le⟩, hab, hx.trans (hst ▸ hs)⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Basic
-/

public section

namespace MovingSofa

/-- The set is the range of an injective continuous map from a closed real interval. -/
@[expose]
def IsJordanArc (Γ : Set Point) : Prop :=
  ∃ (a b : ℝ) (_ : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

/-- The set is the range of an injective continuous map from the circle. -/
@[expose]
def IsJordanCurve (Γ : Set Point) : Prop :=
  ∃ x : Circle → Point, Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

/-- Bundle the predicates for Jordan arcs and Jordan curves. -/
def jordanSets : (Set Point → Prop) × (Set Point → Prop) :=
  (IsJordanArc, IsJordanCurve)

/-- A Jordan arc admits a parametrization with the specified starting and ending points. -/
@[expose]
def IsOrientedJordanArc (Γ : Set Point) (p q : Point) : Prop :=
  ∃ (a b : ℝ) (hab : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = p ∧ x ⟨b, hab, le_rfl⟩ = q

/-- A Jordan arc equipped with ordered endpoints. -/
structure OrientedJordanArc where
  /-- The point set traced by the arc. -/
  carrier : Set Point
  /-- The initial endpoint of the oriented arc. -/
  startPoint : Point
  /-- The terminal endpoint of the oriented arc. -/
  endPoint : Point
  parametrizable : IsOrientedJordanArc carrier startPoint endPoint

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Orientation
-/

public section

noncomputable section

namespace MovingSofa

/-- Points outside the curve whose connected component in its complement is bounded. -/
@[expose]
def jordanInterior (Γ : Set Point) : Set Point :=
  {p | p ∉ Γ ∧ Bornology.IsBounded (connectedComponentIn Γᶜ p)}

/-- A continuous real angle lifts the normalized displacement from the specified point. -/
@[expose]
def IsCurveAngleLift {a b : ℝ} (x : Set.Icc a b → Point) (p : Point)
    (θ : Set.Icc a b → ℝ) : Prop :=
  Continuous θ ∧ ∀ t,
    Real.cos (θ t) = (x t - p) 0 / ‖x t - p‖ ∧
    Real.sin (θ t) = (x t - p) 1 / ‖x t - p‖

/-- The angle-lift increment divided by `2π`, with value zero if no lift exists. -/
@[expose]
def curveWinding {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point) (p : Point) : ℝ := by
  classical
  exact if h : ∃ θ, IsCurveAngleLift x p θ then
    (h.choose ⟨b, hab, le_rfl⟩ - h.choose ⟨a, le_rfl, hab⟩) / (2 * Real.pi)
  else 0

/-- A simple closed parametrization with the specified winding sign on the interior. -/
@[expose]
def IsOrientedJordanParametrization {a b : ℝ} (hab : a ≤ b)
    (Γ : Set Point) (counterclockwise : Bool) (x : Set.Icc a b → Point) : Prop :=
  a < b ∧ IsJordanCurve Γ ∧ Continuous x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩ ∧
    Set.InjOn x {t | (t : ℝ) < b} ∧
    ∀ p ∈ jordanInterior Γ, curveWinding hab x p = if counterclockwise then 1 else -1

/-- A Jordan curve together with a choice of clockwise or counterclockwise orientation. -/
structure OrientedJordanCurve where
  /-- The point set traced by the Jordan curve. -/
  carrier : Set Point
  isJordan : IsJordanCurve carrier
  /-- Select positive winding orientation when true and negative orientation when false. -/
  counterclockwise : Bool

/-- Bundle the winding functional and the oriented-parametrization predicate. -/
def jordanCurveOrientation :
    (∀ (a b : ℝ), a ≤ b → (Set.Icc a b → Point) → Point → ℝ) ×
    (∀ (a b : ℝ), a ≤ b → Set Point → Bool → (Set.Icc a b → Point) → Prop) :=
  (fun _ _ hab ↦ curveWinding hab, fun _ _ hab ↦ IsOrientedJordanParametrization hab)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Area
-/

public section

noncomputable section

namespace MovingSofa

/-- An injective continuous BV parametrization respecting an oriented arc’s endpoints. -/
structure ArcBVParametrization (Γ : OrientedJordanArc) where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b
  injective : Function.Injective path.val
  range_eq : Set.range path.val = Γ.carrier
  start_eq : path.val ⟨a, le_rfl, ordered⟩ = Γ.startPoint
  end_eq : path.val ⟨b, ordered, le_rfl⟩ = Γ.endPoint

/-- A continuous BV parametrization respecting a Jordan curve’s orientation. -/
structure ClosedBVParametrization (Γ : OrientedJordanCurve) where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b
  oriented : IsOrientedJordanParametrization ordered Γ.carrier Γ.counterclockwise path.val

/-- Oriented Jordan arcs admitting a continuous BV parametrization. -/
abbrev RectifiableOrientedArc :=
  {Γ : OrientedJordanArc // Nonempty (ArcBVParametrization Γ)}

/-- Oriented Jordan curves admitting a continuous BV parametrization. -/
abbrev RectifiableOrientedCurve :=
  {Γ : OrientedJordanCurve // Nonempty (ClosedBVParametrization Γ)}

/-- The signed Stieltjes area of a chosen BV parametrization of the oriented arc. -/
@[expose]
def jordanArcArea (Γ : RectifiableOrientedArc) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

/-- The signed Stieltjes area of a chosen BV parametrization of the oriented curve. -/
def jordanClosedCurveArea (Γ : RectifiableOrientedCurve) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

/-- Bundle the signed area functionals for oriented arcs and closed curves. -/
def jordanArea : (RectifiableOrientedArc → ℝ) × (RectifiableOrientedCurve → ℝ) :=
  (jordanArcArea, jordanClosedCurveArea)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Arc Area
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Same-carrier Jordan arcs have equal or opposite signed areas according to their endpoints. -/
theorem curveArea_arc_same_carrier
    (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
    (y : ArcBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  let _ : Fact (x.a ≤ x.b) := ⟨x.ordered⟩
  let _ : Fact (y.a ≤ y.b) := ⟨y.ordered⟩
  have hxemb : Topology.IsEmbedding x.path.val :=
    (x.path.property.1.isClosedEmbedding x.injective).isEmbedding
  let φ : Set.Icc y.a y.b → Set.Icc x.a x.b := fun t ↦
    hxemb.toHomeomorph.symm ⟨y.path.val t, by
      rw [x.range_eq, hcarrier, ← y.range_eq]
      exact Set.mem_range_self t⟩
  have hφc : Continuous φ :=
    hxemb.toHomeomorph.symm.continuous.comp <|
      y.path.property.1.subtype_mk _
  have hxy (t : Set.Icc y.a y.b) : x.path.val (φ t) = y.path.val t := by
    exact congrArg Subtype.val (hxemb.toHomeomorph.apply_symm_apply
      ⟨y.path.val t, by
        rw [x.range_eq, hcarrier, ← y.range_eq]
        exact Set.mem_range_self t⟩)
  have hφi : Function.Injective φ := fun s t hst ↦
    y.injective <| by rw [← hxy s, ← hxy t, hst]
  have hφs : Function.Surjective φ := by
    intro s
    have hmem : x.path.val s ∈ Set.range y.path.val := by
      rw [y.range_eq, ← hcarrier, ← x.range_eq]
      exact Set.mem_range_self s
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, ?_⟩
    apply x.injective
    rw [hxy t, ht]
  have hxbot : x.path.val (⊥ : Set.Icc x.a x.b) = Γ.startPoint := by
    convert x.start_eq using 1
  have hxtop : x.path.val (⊤ : Set.Icc x.a x.b) = Γ.endPoint := by
    convert x.end_eq using 1
  have hybot : y.path.val (⊥ : Set.Icc y.a y.b) = Δ.startPoint := by
    convert y.start_eq using 1
  have hytop : y.path.val (⊤ : Set.Icc y.a y.b) = Δ.endPoint := by
    convert y.end_eq using 1
  have hmono (hstart : Γ.startPoint = Δ.startPoint)
      (hend : Γ.endPoint = Δ.endPoint) : Monotone φ := by
    apply (hφc.strictMono_of_inj_boundedOrder ?_ hφi).monotone
    have hbot : φ ⊥ = ⊥ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hstart, hxbot]
    have htop : φ ⊤ = ⊤ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hend, hxtop]
    rw [hbot, htop]
    exact bot_le
  have hanti (hstart : Γ.startPoint = Δ.endPoint)
      (hend : Γ.endPoint = Δ.startPoint) : Antitone φ := by
    apply (hφc.strictAnti_of_inj_boundedOrder ?_ hφi).antitone
    have htop : φ ⊤ = ⊥ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hstart, hxbot]
    have hbot : φ ⊥ = ⊤ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hend, hxtop]
    rw [htop, hbot]
    exact bot_le
  constructor
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective
      x.ordered y.ordered x.path φ hφc (hmono hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    simpa [hzy] using hzarea.symm
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective
      x.ordered y.ordered x.path φ hφc (hanti hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    rw [hzy] at hzarea
    linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Parametrization
-/

public section

noncomputable section

open Set Function

namespace MovingSofa

/-- Identify an open interval with the corresponding subset of the closed interval. -/
def openIntervalToIntervalInterior {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} where
  toFun t := ⟨⟨t, t.property.1.le, t.property.2.le⟩, t.property⟩
  invFun t := ⟨t, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk fun t ↦ ⟨t.property.1.le, t.property.2.le⟩).subtype_mk _
  continuous_invFun := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

/-- Regard a parametrized point as an element of the path’s range. -/
def intervalToRange {a b : ℝ} (x : Set.Icc a b → Point) :
    Set.Icc a b → Set.range x := fun t ↦ ⟨x t, ⟨t, rfl⟩⟩

theorem intervalToRange_continuous {a b : ℝ} (x : Set.Icc a b → Point)
    (hx : Continuous x) : Continuous (intervalToRange x) :=
  hx.subtype_mk fun t ↦ ⟨t, rfl⟩

theorem intervalToRange_surjective {a b : ℝ} (x : Set.Icc a b → Point) :
    Function.Surjective (intervalToRange x) := by
  rintro ⟨p, t, rfl⟩
  exact ⟨t, rfl⟩

/-- The carrier of a closed parametrized loop with its basepoint removed. -/
@[expose]
def puncturedLoopRangeSet {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : Set (Set.range x) :=
  {p | (p : Point) ≠ x ⟨a, le_rfl, hab⟩}

theorem puncturedLoopRangeSet_isOpen {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : IsOpen (puncturedLoopRangeSet hab x) := by
  let p : Set.range x := ⟨x ⟨a, le_rfl, hab⟩, ⟨⟨a, le_rfl, hab⟩, rfl⟩⟩
  rw [show puncturedLoopRangeSet hab x = ({p}ᶜ : Set (Set.range x)) by
    ext q
    change ((q : Point) ≠ (p : Point)) ↔ q ≠ p
    exact not_congr Subtype.ext_iff.symm]
  exact isOpen_compl_singleton

theorem intervalToRange_preimage_punctured {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    intervalToRange x ⁻¹' puncturedLoopRangeSet hab x =
      {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} := by
  ext t
  simp only [Set.mem_preimage, puncturedLoopRangeSet, Set.mem_ofPred_eq, intervalToRange]
  constructor
  · intro ht
    constructor
    · exact lt_of_le_of_ne t.property.1 fun hta ↦ by
        apply ht
        exact congrArg x (Subtype.ext hta.symm)
    · exact lt_of_le_of_ne t.property.2 fun htb ↦ by
        apply ht
        have ht_top : t = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
        rw [ht_top]
        exact hclosed.symm
  · rintro ⟨hat, htb⟩ htx
    have : t = ⟨a, le_rfl, hab⟩ := hinj htb hab' htx
    exact hat.ne (congrArg Subtype.val this).symm

theorem intervalToPuncturedRange_injective {a b : ℝ} (hab : a ≤ b)
    (_hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Function.Injective
      ((puncturedLoopRangeSet hab x).restrictPreimage (intervalToRange x)) := by
  intro s t hst
  apply Subtype.ext
  apply hinj (x₁ := s.val) (x₂ := t.val)
  · have hsne : x s.val ≠ x ⟨a, le_rfl, hab⟩ := s.property
    exact lt_of_le_of_ne s.val.property.2 fun hsb ↦ by
      apply hsne
      have hs_top : s.val = ⟨b, hab, le_rfl⟩ := Subtype.ext hsb
      rw [hs_top]
      exact hclosed.symm
  · have htne : x t.val ≠ x ⟨a, le_rfl, hab⟩ := t.property
    exact lt_of_le_of_ne t.val.property.2 fun htb ↦ by
      apply htne
      have ht_top : t.val = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
      rw [ht_top]
      exact hclosed.symm
  · exact congrArg (fun p : puncturedLoopRangeSet hab x ↦ (p : Point)) hst

/-- Removing the basepoint turns a closed once-traversal into a homeomorphism from the
open parameter interval onto the punctured carrier. -/
noncomputable def openIntervalHomeomorphPuncturedRange {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.Ioo a b ≃ₜ puncturedLoopRangeSet hab x := by
  let f := intervalToRange x
  let s := puncturedLoopRangeSet hab x
  have hfq : Topology.IsQuotientMap f :=
    (intervalToRange_continuous x hx).isClosedMap.isQuotientMap
      (intervalToRange_continuous x hx) (intervalToRange_surjective x)
  have hgq : Topology.IsQuotientMap (s.restrictPreimage f) :=
    hfq.restrictPreimage_isOpen (puncturedLoopRangeSet_isOpen hab x)
  have hgh : IsHomeomorph (s.restrictPreimage f) :=
    isHomeomorph_iff_isQuotientMap_injective.2
      ⟨hgq, intervalToPuncturedRange_injective hab hab' x hclosed hinj⟩
  exact (openIntervalToIntervalInterior hab').trans <|
    (Homeomorph.setCongr
      (intervalToRange_preimage_punctured hab hab' x hclosed hinj).symm).trans
      (hgh.homeomorph _)

/-- The punctured-loop homeomorphism agrees pointwise with the original path. -/
theorem openIntervalHomeomorphPuncturedRange_coe {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) (t : Set.Ioo a b) :
    ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj t :
        puncturedLoopRangeSet hab x) : Point) =
      x ⟨t, t.property.1.le, t.property.2.le⟩ := by
  rfl

private def puncturedLoopRangeHomeomorphOfEq
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    puncturedLoopRangeSet hcd y ≃ₜ puncturedLoopRangeSet hab x where
  toFun q :=
    ⟨⟨q, by rw [hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart)⟩
  invFun q :=
    ⟨⟨q, by rw [← hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _

/-- The transition between two endpoint-matched once-traversals, restricted to their open
parameter intervals. -/
private noncomputable def openIntervalClosedCurveTransition
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    Set.Ioo c d ≃ₜ Set.Ioo a b :=
  (openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj).trans
    ((puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart).trans
      (openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj).symm)

private theorem openIntervalClosedCurveTransition_point
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩)
    (t : Set.Ioo c d) :
    x ⟨openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.1.le,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.2.le⟩ =
      y ⟨t, t.property.1.le, t.property.2.le⟩ := by
  let ex := openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj
  let ey := openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj
  let ec := puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart
  change x ⟨ex.symm (ec (ey t)), (ex.symm (ec (ey t))).property.1.le,
      (ex.symm (ec (ey t))).property.2.le⟩ =
    y ⟨t, t.property.1.le, t.property.2.le⟩
  rw [← openIntervalHomeomorphPuncturedRange_coe hab hab' x hxc hxclosed hxinj
      (ex.symm (ec (ey t))),
    ← openIntervalHomeomorphPuncturedRange_coe hcd hcd' y hyc hyclosed hyinj t]
  exact congrArg (fun q : puncturedLoopRangeSet hab x ↦ (q : Point))
    (ex.apply_symm_apply (ec (ey t)))

private theorem homeomorph_Ioo_strictMono_or_strictAnti
    {a b c d : ℝ} (hcd : c < d) (e : Set.Ioo c d ≃ₜ Set.Ioo a b) :
    StrictMono e ∨ StrictAnti e := by
  let f : ℝ → ℝ := Function.extend ((↑) : Set.Ioo c d → ℝ)
    (fun t ↦ (e t : ℝ)) 0
  have hf_apply (t : Set.Ioo c d) : f t = (e t : ℝ) :=
    Subtype.val_injective.extend_apply _ _ t
  have hfc : ContinuousOn f (Set.Ioo c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    funext t
    exact hf_apply t
  have hfi : Set.InjOn f (Set.Ioo c d) := by
    intro s hs t ht hst
    have heq : e ⟨s, hs⟩ = e ⟨t, ht⟩ := by
      apply Subtype.ext
      calc
        (e ⟨s, hs⟩ : ℝ) = f s := (hf_apply ⟨s, hs⟩).symm
        _ = f t := hst
        _ = (e ⟨t, ht⟩ : ℝ) := hf_apply ⟨t, ht⟩
    exact congrArg Subtype.val (e.injective heq)
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo hcd hfc hfi with hm | ha
  · left
    intro s t hst
    have := hm s.property t.property hst
    change (e s : ℝ) < (e t : ℝ)
    simpa only [hf_apply] using this
  · right
    intro s t hst
    have := ha s.property t.property hst
    change (e t : ℝ) < (e s : ℝ)
    simpa only [hf_apply] using this

private def closedIntervalReverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b ≃ₜ Set.Icc a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem closedIntervalReverse_antitone {a b : ℝ} (_hab : a ≤ b) :
    Antitone (closedIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  change a + b - (t : ℝ) ≤ a + b - (s : ℝ)
  linarith

private theorem closedIntervalReverse_left {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨a, le_rfl, hab⟩ = ⟨b, hab, le_rfl⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private theorem closedIntervalReverse_right {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨b, hab, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private def openIntervalReverse {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ Set.Ioo a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem openIntervalReverse_strictAnti {a b : ℝ} (_hab : a < b) :
    StrictAnti (openIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) < (t : ℝ) := hst
  change a + b - (t : ℝ) < a + b - (s : ℝ)
  linarith

private theorem openIntervalClosedCurveTransition_strictMono_or_strictAnti
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    StrictMono (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) ∨
    StrictAnti (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) :=
  homeomorph_Ioo_strictMono_or_strictAnti hcd'
    (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
      hyclosed hxinj hyinj hrange hstart)

/-- An endpoint-matched pair of continuous once-traversals of the same carrier differ by a
continuous surjective monotone or antitone reparametrization of the closed intervals. -/
private theorem exists_reparametrization_with_endpoints
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧
      ((Monotone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) ∨
        (Antitone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)) ∧
      ∀ t, x (φ t) = y t := by
  let e := openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
    hxclosed hyclosed hxinj hyinj hrange hstart
  rcases openIntervalClosedCurveTransition_strictMono_or_strictAnti hab hab' hcd hcd'
      x y hxc hyc hxclosed hyclosed hxinj hyinj hrange hstart with hm | ha
  · let eo : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse e hm e.symm e.apply_symm_apply
    let φ := OrderIso.extendIoo hab' eo
    refine ⟨φ, OrderIso.continuous_extendIoo hcd' hab' eo,
      OrderIso.surjective_extendIoo hcd' hab' eo, Or.inl ⟨?_, ?_, ?_⟩, ?_⟩
    · exact OrderIso.monotone_extendIoo hcd' hab' eo
    · exact OrderIso.extendIoo_left hcd' hab' eo
    · exact OrderIso.extendIoo_right hcd' hab' eo
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht, show φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' eo]
        exact hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht, show φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' eo]
        exact hxclosed.symm.trans (hstart.trans hyclosed)
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have ht : t = ⟨ti, ti.property.1.le, ti.property.2.le⟩ := Subtype.ext rfl
          rw [ht]
          exact OrderIso.extendIoo_interior hab' eo ti
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti
  · let r := openIntervalReverse hab'
    let g : Set.Ioo c d ≃ₜ Set.Ioo a b := e.trans r
    have hgm : StrictMono g := by
      intro s t hst
      exact openIntervalReverse_strictAnti hab' (ha hst)
    let go : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse g hgm g.symm g.apply_symm_apply
    let ψ := OrderIso.extendIoo hab' go
    let φ : Set.Icc c d → Set.Icc a b := fun t ↦ closedIntervalReverse hab (ψ t)
    refine ⟨φ, (closedIntervalReverse hab).continuous.comp
        (OrderIso.continuous_extendIoo hcd' hab' go),
      (closedIntervalReverse hab).surjective.comp
        (OrderIso.surjective_extendIoo hcd' hab' go), Or.inr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (closedIntervalReverse_antitone hab).comp_monotone
        (OrderIso.monotone_extendIoo hcd' hab' go)
    · rw [show φ ⟨c, le_rfl, hcd⟩ =
          closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩) from rfl,
        show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · rw [show φ ⟨d, hcd, le_rfl⟩ =
          closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩) from rfl,
        show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩)) = _
        rw [show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
        rw [closedIntervalReverse_left hab]
        exact hxclosed.symm.trans hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩)) = _
        rw [show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
        rw [closedIntervalReverse_right hab]
        exact hstart.trans hyclosed
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have hψ := OrderIso.extendIoo_interior hab' go ti
          dsimp [go, g, r] at hψ
          change a + b - (ψ t : ℝ) = (e ti : ℝ)
          rw [hψ]
          change a + b - (a + b - (e ti : ℝ)) = (e ti : ℝ)
          ring
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti

/-- Equal-start simple closed paths with the same range admit a monotone or antitone transition. -/
theorem exists_reparametrization_of_range_eq_of_start_eq
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y = x ∘ φ := by
  rcases exists_reparametrization_with_endpoints hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart with ⟨φ, hφc, hφs, hφo, hφxy⟩
  refine ⟨φ, hφc, hφs, hφo.imp (fun h ↦ h.1) (fun h ↦ h.1), ?_⟩
  funext t
  exact (hφxy t).symm

/-- Equal-start closed Jordan parametrizations admit a monotone or antitone transition. -/
theorem ClosedBVParametrization.exists_reparametrization_of_start_eq
    {Γ Δ : OrientedJordanCurve} (x : ClosedBVParametrization Γ)
    (y : ClosedBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier)
    (hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
    ∃ φ : Set.Icc y.a y.b → Set.Icc x.a x.b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y.path.val = x.path.val ∘ φ := by
  have hrange : Set.range x.path.val = Set.range y.path.val := by
    rw [x.oriented.2.2.2.1, y.oriented.2.2.2.1]
    exact hcarrier
  exact exists_reparametrization_of_range_eq_of_start_eq x.ordered x.oriented.1 y.ordered
    y.oriented.1
    x.path.val y.path.val x.path.property.1 y.path.property.1
    x.oriented.2.2.2.2.1 y.oriented.2.2.2.2.1
    x.oriented.2.2.2.2.2.1 y.oriented.2.2.2.2.2.1 hrange hstart

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Unit Sphere
-/

public section

noncomputable section
namespace MovingSofa

private def circlePoint (z : Circle) : Point := WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im]

private lemma norm_circlePoint (z : Circle) : ‖circlePoint z‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [circlePoint, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, Real.norm_eq_abs, sq_abs]
  have h := Complex.sq_norm (z : ℂ)
  simp only [Complex.normSq_apply, Circle.norm_coe] at h
  nlinarith

private lemma continuous_circlePoint : Continuous circlePoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val

/-- A planar set homeomorphic to the unit sphere is a Jordan curve. -/
lemma isJordanCurve_of_unitSphere_homeomorph {Γ : Set Point}
    (e : {u : Point | ‖u‖ = 1} ≃ₜ ↥Γ) : IsJordanCurve Γ := by
  let f : Circle → {u : Point | ‖u‖ = 1} := fun z ↦ ⟨circlePoint z, norm_circlePoint z⟩
  refine ⟨fun z ↦ (e (f z) : Point), continuous_subtype_val.comp
    (e.continuous.comp (continuous_circlePoint.subtype_mk _)), ?_, ?_⟩
  · intro z w h
    have he := e.injective (Subtype.ext h)
    have hpoint := congrArg Subtype.val he
    apply Subtype.ext
    apply Complex.ext
    · exact congrFun (congrArg WithLp.ofLp hpoint) 0
    · exact congrFun (congrArg WithLp.ofLp hpoint) 1
  · apply Set.Subset.antisymm
    · rintro p ⟨z, rfl⟩
      exact (e (f z)).property
    · intro p hp
      let u := e.symm ⟨p, hp⟩
      let z : ℂ := ⟨u.val 0, u.val 1⟩
      have hz : ‖z‖ = 1 := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
        rw [Complex.sq_norm]
        have hu : ‖u.val‖ = 1 := u.property
        have hsq := congrArg (fun r : ℝ ↦ r ^ 2) hu
        rw [EuclideanSpace.norm_sq_eq] at hsq
        simpa [z, Fin.sum_univ_two, sq] using hsq
      let ζ : Circle := ⟨z, by
        change z ∈ Metric.sphere 0 1
        simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
      refine ⟨ζ, ?_⟩
      have hf : f ζ = u := by
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl
      change (e (f ζ) : Point) = p
      rw [hf]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Winding
-/

public section

noncomputable section

namespace MovingSofa

/-- Two continuous angle lifts have the same endpoint increment. -/
theorem IsCurveAngleLift.endpoint_increment_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ ψ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift x p ψ) :
    θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩ =
      ψ ⟨b, hab, le_rfl⟩ - ψ ⟨a, le_rfl, hab⟩ := by
  let _ : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have h := Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin hθ.1 hψ.1
    (fun t ↦ (hθ.2 t).1.trans (hψ.2 t).1.symm)
    (fun t ↦ (hθ.2 t).2.trans (hψ.2 t).2.symm)
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩
  linarith

/-- Compute the winding value from any continuous angle lift. -/
theorem IsCurveAngleLift.curveWinding_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) :
    curveWinding hab x p = (θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩) / (2 * Real.pi) := by
  unfold curveWinding
  rw [dite_eq_left ⟨θ, hθ⟩]
  congr 1
  exact IsCurveAngleLift.endpoint_increment_eq hab (Exists.choose_spec ⟨θ, hθ⟩) hθ

/-- A nonzero winding value provides a continuous angle lift. -/
theorem exists_curveAngleLift_of_curveWinding_ne_zero {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} (h : curveWinding hab x p ≠ 0) :
    ∃ θ, IsCurveAngleLift x p θ := by
  by_contra hn
  apply h
  simp only [curveWinding, dite_eq_right hn]

/-- Pull back an angle lift along a continuous parameter map. -/
theorem IsCurveAngleLift.comp {a b c d : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    IsCurveAngleLift (x ∘ φ) p (θ ∘ φ) :=
  ⟨hθ.1.comp hφ, fun t ↦ hθ.2 (φ t)⟩

/-- Compute winding after continuous reparametrization from lifted endpoint values. -/
theorem IsCurveAngleLift.curveWinding_comp {a b c d : ℝ} (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    curveWinding hcd (x ∘ φ) p =
      (θ (φ ⟨d, hcd, le_rfl⟩) - θ (φ ⟨c, le_rfl, hcd⟩)) / (2 * Real.pi) :=
  (hθ.comp hφ).curveWinding_eq hcd

/-- A continuous reparametrization preserving endpoints preserves winding. -/
theorem curveWinding_comp_of_endpoints {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) :
    curveWinding hcd (x ∘ φ) p = curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]

/-- A continuous reparametrization exchanging endpoints negates winding. -/
theorem curveWinding_comp_of_reversed_endpoints {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩) :
    curveWinding hcd (x ∘ φ) p = -curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Radial Winding
-/

public section

noncomputable section
namespace MovingSofa

/-- The parameter angle lifts a positive radial loop about its center. -/
lemma isCurveAngleLift_radial {a b : ℝ} (o : Point) (r : Set.Icc a b → ℝ)
    (hr : ∀ t, 0 < r t) :
    IsCurveAngleLift (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o
      (fun t ↦ (t : ℝ)) := by
  refine ⟨continuous_subtype_val, fun t ↦ ?_⟩
  have hn : ‖r t • normalVector ((t : ℝ) : Real.Angle)‖ = r t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr t), norm_normalVector_real, mul_one]
  simp only [add_sub_cancel_left, hn]
  constructor
  · change Real.cos (t : ℝ) = r t * Real.cos (t : ℝ) / r t
    field_simp [(hr t).ne']
  · change Real.sin (t : ℝ) = r t * Real.sin (t : ℝ) / r t
    field_simp [(hr t).ne']

/-- A positive radial loop winds once around its center. -/
lemma curveWinding_radial_center (o : Point) (r : Set.Icc (0 : ℝ) (2 * Real.pi) → ℝ)
    (hr : ∀ t, 0 < r t) :
    curveWinding (by positivity)
      (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o = 1 := by
  rw [(isCurveAngleLift_radial o r hr).curveWinding_eq]
  simp

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Winding Concatenation
-/

public section

noncomputable section

namespace MovingSofa

private theorem cos_sin_add_sub {α β : ℝ}
    (hc : Real.cos α = Real.cos β) (hs : Real.sin α = Real.sin β) (t : ℝ) :
    Real.cos (t + (α - β)) = Real.cos t ∧
      Real.sin (t + (α - β)) = Real.sin t := by
  have hcd : Real.cos (α - β) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.cos_sq_add_sin_sq β]
  have hsd : Real.sin (α - β) = 0 := by
    rw [Real.sin_sub, hc, hs]
    ring
  simp [Real.cos_add, Real.sin_add, hcd, hsd]

/-- Winding is additive for two paths joined at a common endpoint. -/
theorem curveWinding_concatUnitIntervals
    {x y : Set.Icc (0 : ℝ) 1 → Point} {p : Point}
    {θ ψ : Set.Icc (0 : ℝ) 1 → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift y p ψ)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    curveWinding (by norm_num) (Function.concatUnitIntervals x y) p =
      curveWinding (by norm_num) x p + curveWinding (by norm_num) y p := by
  let δ := θ ⟨1, by norm_num⟩ - ψ ⟨0, by norm_num⟩
  have htrig (t : Set.Icc (0 : ℝ) 1) :
      Real.cos (ψ t + δ) = Real.cos (ψ t) ∧
      Real.sin (ψ t + δ) = Real.sin (ψ t) := by
    apply cos_sin_add_sub
    · rw [(hθ.2 _).1, (hψ.2 _).1, hjoin]
    · rw [(hθ.2 _).2, (hψ.2 _).2, hjoin]
  let η := Function.concatUnitIntervals θ (fun t ↦ ψ t + δ)
  have hη : IsCurveAngleLift (Function.concatUnitIntervals x y) p η := by
    refine ⟨Function.continuous_concatUnitIntervals hθ.1
      (hψ.1.add continuous_const) (by dsimp [δ]; ring), ?_⟩
    intro t
    dsimp [η, Function.concatUnitIntervals]
    split_ifs with ht
    · exact hθ.2 _
    · exact ⟨(htrig _).1.trans (hψ.2 _).1, (htrig _).2.trans (hψ.2 _).2⟩
  rw [hη.curveWinding_eq, hθ.curveWinding_eq, hψ.curveWinding_eq]
  simp only [η, Function.concatUnitIntervals]
  norm_num
  dsimp [δ]
  change (ψ ⟨1, _⟩ + (θ ⟨1, _⟩ - ψ ⟨0, _⟩) - θ ⟨0, _⟩) / (2 * Real.pi) =
    (θ ⟨1, _⟩ - θ ⟨0, _⟩) / (2 * Real.pi) +
      (ψ ⟨1, _⟩ - ψ ⟨0, _⟩) / (2 * Real.pi)
  ring

/-- Moving a closed path's cut point preserves winding. -/
theorem curveWinding_concat_of_cyclic_endpoints {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hφ₁ : φ ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φ) (x ∘ ψ)) p =
      curveWinding hab x p := by
  have hjoin : (x ∘ φ) ⟨1, by norm_num⟩ = (x ∘ ψ) ⟨0, by norm_num⟩ := by
    simp only [Function.comp_apply, hφ₁, hψ₀]
    exact hx.symm
  rw [curveWinding_concatUnitIntervals (hθ.comp hφ) (hθ.comp hψ) hjoin,
    hθ.curveWinding_comp (by norm_num) hφ, hθ.curveWinding_comp (by norm_num) hψ,
    hφ₀, hφ₁, hψ₀, hψ₁, hθ.curveWinding_eq hab]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Cyclic Rotation
-/

public section

noncomputable section
namespace MovingSofa

private theorem strictMono_convexComb {a b : ℝ} (l u : Set.Icc a b) (hlu : l < u) :
    StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- Moving an oriented Jordan path's start to an interior parameter preserves area and
orientation. -/
theorem exists_oriented_cyclic_rotation {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val ⟨0, by norm_num⟩ = x.val s ∧
      curveAreaFunctional r = curveAreaFunctional x := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _, harea⟩ := exists_cyclic_rotation_eq_concat hab x s hclosed.symm
  refine ⟨r, ?_, ?_, harea⟩
  · refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
    · rw [hr, range_cyclic_concat hab x.val s hclosed]
      exact hx.2.2.2.1
    · rw [hr]
      simp
    · rw [hr]
      exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
        hx.2.2.2.2.2.1 hclosed s has hsb
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (strictMono_convexComb _ _ hsb) (strictMono_convexComb _ _ has)
        (by simp) (by simp) (by simp)
    · intro p hp
      have hxw := hx.2.2.2.2.2.2 p hp
      have hn : curveWinding hab x.val p ≠ 0 := by
        rw [hxw]
        cases ccw <;> norm_num
      obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
      rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
        (by simp) (by simp) (by simp) (by simp)]
      exact hxw
  · rw [hr]
    simp

/-- A cyclic rotation together with its literal tail-then-head formula. -/
theorem exists_oriented_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _⟩ :=
    exists_cyclic_rotation_path hab x s hclosed.symm
  refine ⟨r, ?_, hr⟩
  refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
  · rw [hr, range_cyclic_concat hab x.val s hclosed]
    exact hx.2.2.2.1
  · rw [hr]
    simp
  · rw [hr]
    exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
      hx.2.2.2.2.2.1 hclosed s has hsb
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (strictMono_convexComb _ _ hsb)
      (strictMono_convexComb _ _ has)
      (by simp) (by simp) (by simp)
  · intro p hp
    have hxw := hx.2.2.2.2.2.2 p hp
    have hn : curveWinding hab x.val p ≠ 0 := by
      rw [hxw]
      cases ccw <;> norm_num
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
    rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
      (by simp) (by simp) (by simp) (by simp)]
    exact hxw

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Winding Kernel
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The inverse-distance vector kernel based at `z`. -/
@[expose]
def windingKernel (z p : Point) : Point :=
  (‖z - p‖ ^ 2)⁻¹ • (z - p)

private def pointComplex : Point ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem pointComplex_windingKernel (z p : Point) :
    pointComplex (windingKernel z p) =
      (starRingEnd ℂ (pointComplex z - pointComplex p))⁻¹ := by
  have hsub : pointComplex (z - p) = pointComplex z - pointComplex p :=
    map_sub pointComplex z p
  rw [windingKernel, map_smul, hsub]
  let v : ℂ := pointComplex z - pointComplex p
  change (‖z - p‖ ^ 2)⁻¹ • v = (starRingEnd ℂ v)⁻¹
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, star_star, Complex.normSq_eq_norm_sq, norm_star]
  have hn : ‖v‖ = ‖z - p‖ := by
    rw [show v = pointComplex (z - p) by simp [v, hsub]]
    exact LinearIsometryEquiv.norm_map pointComplex (z - p)
  rw [hn, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

private theorem norm_windingKernel (z p : Point) :
    ‖windingKernel z p‖ = if p = z then 0 else ‖z - p‖⁻¹ := by
  by_cases hp : p = z
  · subst p
    simp [windingKernel]
  · have hnorm : ‖z - p‖ ≠ 0 := by
      simpa [norm_eq_zero, sub_eq_zero] using Ne.symm hp
    rw [windingKernel, norm_smul, Real.norm_eq_abs]
    simp only [abs_inv, abs_pow, abs_norm]
    simp only [hp, ↓reduceIte]
    field_simp

private theorem ball_zero_subset_ball_two_mul (R : ℝ) (z : Point)
    (hz : ‖z‖ < R) : Metric.ball 0 R ⊆ Metric.ball z (2 * R) := by
  intro p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp ⊢
  have hp' : ‖p‖ < R := by simpa using hp
  calc
    ‖p - z‖ ≤ ‖p‖ + ‖z‖ := norm_sub_le p z
    _ < R + R := add_lt_add hp' hz
    _ = 2 * R := by ring

private theorem measurable_windingKernel (z : Point) : Measurable (windingKernel z) := by
  unfold windingKernel
  exact (((measurable_const.sub measurable_id).norm.pow_const 2).inv.smul
    (measurable_const.sub measurable_id))

private theorem indicator_inv_norm_pointComplex (S : ℝ) (p : Point) :
    (Metric.ball (0 : Point) S).indicator (fun p ↦ ‖p‖⁻¹) p =
      (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) := by
  have hm : pointComplex p ∈ Metric.ball (0 : ℂ) S ↔
      p ∈ Metric.ball (0 : Point) S := by
    simp [Metric.mem_ball, dist_eq_norm]
  by_cases hp : p ∈ Metric.ball (0 : Point) S
  · simp [hp, hm.mpr hp]
  · simp [hp, mt hm.mp hp]

private theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : Point ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  have hf : Integrable ((Metric.ball (0 : ℂ) S).indicator fun q ↦ ‖q‖⁻¹) :=
    (integrable_indicator_iff measurableSet_ball).mpr (Complex.integrableOn_inv_norm_ball S)
  refine (((LinearIsometryEquiv.measurePreserving pointComplex).integrable_comp_emb
    pointComplex.toHomeomorph.measurableEmbedding).mpr hf).congr ?_
  filter_upwards with p
  exact (indicator_inv_norm_pointComplex S p).symm

private theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : Point in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : Point ↦ ‖p‖⁻¹) measurableSet_ball]
  calc
    (∫ p : Point, (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
        ∫ p : Point, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) :=
      integral_congr_ae (Filter.Eventually.of_forall (indicator_inv_norm_pointComplex S))
    _ = ∫ q : ℂ, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) q :=
      (LinearIsometryEquiv.measurePreserving pointComplex).integral_comp
        pointComplex.toHomeomorph.measurableEmbedding _
    _ = 2 * Real.pi * S := by
      rw [integral_indicator measurableSet_ball]
      exact Complex.setIntegral_inv_norm_ball S hS

private theorem indicator_centered_inv_norm_eq (z : Point) (S : ℝ) :
    (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) =
      fun p ↦ (Metric.ball 0 S).indicator (fun q ↦ ‖q‖⁻¹) (z - p) := by
  funext p
  have hm : p ∈ Metric.ball z S ↔ z - p ∈ Metric.ball 0 S := by
    simp only [Metric.mem_ball, dist_eq_norm]
    simp [sub_zero, norm_sub_rev]
  by_cases hp : p ∈ Metric.ball z S
  · simp [hp, hm.mp hp]
  · simp [hp, mt hm.mpr hp]

private theorem indicator_centered_inv_norm_nonneg (z : Point) (S : ℝ) (p : Point) :
    0 ≤ (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
  Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem integrable_indicator_centered_inv_norm (z : Point) (S : ℝ) :
    Integrable ((Metric.ball z S).indicator fun p ↦ ‖z - p‖⁻¹) := by
  rw [indicator_centered_inv_norm_eq, MeasureTheory.integrable_comp_sub_left]
  exact (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_norm_ball S)

private theorem integral_indicator_centered_inv_norm (z : Point) (S : ℝ) (hS : 0 < S) :
    (∫ p : Point, (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p) = 2 * Real.pi * S := by
  rw [indicator_centered_inv_norm_eq,
    MeasureTheory.integral_sub_left_eq_self _ volume z, integral_indicator measurableSet_ball]
  exact setIntegral_inv_norm_ball S hS

private theorem norm_windingKernel_le_indicator (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (fun p ↦ ‖windingKernel z p‖) ≤ᵐ[volume.restrict (Metric.ball 0 R)]
      (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  have hpz : p ∈ Metric.ball z (2 * R) := ball_zero_subset_ball_two_mul R z hz hp
  rw [norm_windingKernel]
  by_cases heq : p = z
  · simp only [heq, ↓reduceIte]
    exact indicator_centered_inv_norm_nonneg z (2 * R) z
  · simp [heq, hpz]

/-- The winding kernel is integrable on a disk containing its base point. -/
theorem integrableOn_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    IntegrableOn (windingKernel z) (Metric.ball 0 R) :=
  Integrable.mono' (integrable_indicator_centered_inv_norm z (2 * R)).integrableOn
    (measurable_windingKernel z).aestronglyMeasurable
    (norm_windingKernel_le_indicator R z hz)

/-- The norm of the winding kernel has an integrable uniform majorant on an interior disk. -/
theorem setIntegral_norm_windingKernel_ball_le
    (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R := by
  have hg : Integrable ((Metric.ball z (2 * R)).indicator fun p ↦ ‖z - p‖⁻¹) :=
    integrable_indicator_centered_inv_norm z (2 * R)
  calc
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤
        ∫ p in Metric.ball 0 R, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_mono_ae_restrict (integrableOn_windingKernel_ball R z hz).norm
        hg.integrableOn (norm_windingKernel_le_indicator R z hz)
    _ ≤ ∫ p, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_le_integral hg
        (Filter.Eventually.of_forall (indicator_centered_inv_norm_nonneg z (2 * R)))
    _ = 2 * Real.pi * (2 * R) :=
      integral_indicator_centered_inv_norm z (2 * R) (by linarith)
    _ = 4 * Real.pi * R := by ring

/-- The integral of the winding kernel over a disk is `π` times its base point. -/
theorem setIntegral_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  let T : Point ≃ₗᵢ[ℝ] ℂ := pointComplex.trans Complex.conjLIE
  let a : ℂ := T z
  have ha : ‖a‖ < R := by simpa [a, T] using hz
  have hc := Complex.setIntegral_inv_sub_ball R a ha
  let G : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hpres := (LinearIsometryEquiv.measurePreserving T).integral_comp
    T.toHomeomorph.measurableEmbedding G
  have hfun : ∀ p : Point,
      G (T p) = (Metric.ball 0 R).indicator
        (fun p ↦ pointComplex (windingKernel z p)) p := by
    intro p
    have hm : T p ∈ Metric.ball (0 : ℂ) R ↔ p ∈ Metric.ball (0 : Point) R := by
      simp [Metric.mem_ball, dist_eq_norm, T]
    by_cases hp : p ∈ Metric.ball (0 : Point) R
    · rw [show G (T p) = (a - T p)⁻¹ by simp [G, hm.mpr hp]]
      rw [show (Metric.ball (0 : Point) R).indicator
          (fun p ↦ pointComplex (windingKernel z p)) p =
          pointComplex (windingKernel z p) by simp [hp]]
      rw [pointComplex_windingKernel]
      simp only [a, T, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply,
        map_sub]
    · rw [show G (T p) = 0 by simp [G, mt hm.mp hp]]
      simp [hp]
  have htransport :
      (∫ q in Metric.ball 0 R, (a - q)⁻¹) =
        pointComplex (∫ p in Metric.ball 0 R, windingKernel z p) := by
    rw [← integral_indicator measurableSet_ball]
    change (∫ q, G q) = _
    rw [← hpres]
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    rw [integral_indicator measurableSet_ball]
    simpa using
      (pointComplex.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hInt)
  apply pointComplex.injective
  rw [← htransport, hc]
  simp [a, T, Complex.real_smul]

/-- Off the range of a continuous interval path, each coordinate of the winding kernel is
a bounded continuous function of the parameter. -/
theorem windingKernel_coord_continuous_bounded
    {a b : ℝ} {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) (i : Fin 2) :
    Continuous (fun t ↦ windingKernel (x t) p i) ∧
      ∃ C : ℝ, ∀ t, |windingKernel (x t) p i| ≤ C := by
  have hsub : Continuous (fun t ↦ x t - p) := hx.sub continuous_const
  have hne : ∀ t, ‖x t - p‖ ^ 2 ≠ 0 := by
    intro t
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    intro h
    exact hp ⟨t, sub_eq_zero.mp h⟩
  have hkernel : Continuous (fun t ↦ windingKernel (x t) p) := by
    unfold windingKernel
    exact ((hsub.norm.pow 2).inv₀ hne).smul hsub
  have hcoord : Continuous (fun t ↦ windingKernel (x t) p i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i).comp hkernel
  refine ⟨hcoord, ?_⟩
  have hbdd : BddAbove ((fun t ↦ |windingKernel (x t) p i|) '' Set.univ) :=
    isCompact_univ.bddAbove_image hcoord.abs.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun t ↦ hC ⟨t, Set.mem_univ t, rfl⟩⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Winding Local Constancy
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_m85d0e79 (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_m85d0e79 (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_m85d0e79 (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

/-- The principal relative argument varies continuously while the relative dot product is
positive. This is the branch needed for a small displacement of the basepoint. -/
lemma continuous_arg_conj_mul_of_re_pos {α : Type*} [TopologicalSpace α]
    {z w : α → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (z t) * w t).re) :
    Continuous (fun t ↦ Complex.arg (starRingEnd ℂ (z t) * w t)) := by
  have hf : Continuous (fun u ↦ starRingEnd ℂ (z u) * w u) :=
    (continuous_star.comp hz).mul hw
  change Continuous (Complex.arg ∘ fun u ↦ starRingEnd ℂ (z u) * w u)
  exact Complex.continuousOn_arg.comp_continuous hf (fun t ↦ Or.inl (hpos t))

/-- The principal relative argument rotates the normalized coordinates of `z` to those of `w`. -/
lemma normalized_complex_rotation_by_arg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) :
    Real.cos (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hz, Complex.sin_arg,
    Complex.cos_arg hzw, Complex.sin_arg]
  simp only [Complex.norm_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  rw [Complex.norm_conj]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- Coordinate form of the preceding rotation identity for any chosen real lift of `z`. -/
lemma normalized_complex_rotation_by_relative_arg {z w : ℂ} {θ : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hc : Real.cos θ = z.re / ‖z‖) (hs : Real.sin θ = z.im / ‖z‖) :
    Real.cos (θ + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (θ + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, hc, hs, Complex.cos_arg hzw, Complex.sin_arg,
    Complex.norm_mul, Complex.norm_conj]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- A positive relative dot product supplies the continuous principal correction between two
basepoints. -/
lemma IsCurveAngleLift.add_principal_basepoint_correction {a b : ℝ}
    {x : Set.Icc a b → Point} {p q : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    IsCurveAngleLift x q (fun u ↦ θ u +
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q))) := by
  let z := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - q)
  have hz : Continuous z := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hw : Continuous w := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hδ : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ (z u) * w u)) :=
    continuous_arg_conj_mul_of_re_pos hz hw hpos
  refine ⟨hθ.1.add hδ, fun u ↦ ?_⟩
  have hprod : starRingEnd ℂ (z u) * w u ≠ 0 := by
    intro hzero
    have := hpos u
    rw [hzero] at this
    simp at this
  have hzne : z u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hwne : w u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hc : Real.cos (θ u) = (z u).re / ‖z u‖ := by
    simpa only [z, pointComplex_re_m85d0e79, Complex.orthonormalBasisOneI.repr.symm.norm_map]
      using (hθ.2
        u).1
  have hs : Real.sin (θ u) = (z u).im / ‖z u‖ := by
    simpa only [z, pointComplex_im_m85d0e79, Complex.orthonormalBasisOneI.repr.symm.norm_map]
      using (hθ.2
        u).2
  simpa only [z, w, pointComplex_re_m85d0e79, pointComplex_im_m85d0e79,
      Complex.orthonormalBasisOneI.repr.symm.norm_map] using
    normalized_complex_rotation_by_relative_arg hzne hwne hc hs

/-- Moving the basepoint through the positive-relative-dot neighborhood preserves winding. -/
theorem curveWinding_eq_of_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p q : Point} {θ : Set.Icc a b → ℝ} (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    curveWinding hab x q = curveWinding hab x p := by
  let δ := fun u ↦ Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
    Complex.orthonormalBasisOneI.repr.symm (x u - q))
  have hθδ : IsCurveAngleLift x q (fun u ↦ θ u + δ u) :=
    hθ.add_principal_basepoint_correction hx hpos
  have hδ : δ ⟨a, le_rfl, hab⟩ = δ ⟨b, hab, le_rfl⟩ := by
    simp only [δ, hclosed]
  rw [hθδ.curveWinding_eq hab, hθ.curveWinding_eq hab]
  rw [hδ]
  ring

/-- Off a compact continuous loop, every sufficiently nearby basepoint has positive relative dot
product with the original radial vectors. -/
theorem exists_ball_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) :
    ∃ r > 0, ∀ q, dist q p < r → ∀ u,
      0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q)).re := by
  let _ : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  let f : Set.Icc a b → ℝ := fun u ↦ ‖x u - p‖
  have hf : Continuous f := (hx.sub continuous_const).norm
  obtain ⟨u₀, -, hu₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  have hne (u : Set.Icc a b) : x u - p ≠ 0 := by
    intro hzero
    apply hp
    refine ⟨u, ?_⟩
    exact sub_eq_zero.mp hzero
  have hfu₀ : 0 < f u₀ := norm_pos_iff.mpr (hne u₀)
  refine ⟨f u₀ / 2, half_pos hfu₀, fun q hq u ↦ ?_⟩
  have hmin : f u₀ ≤ f u := hu₀ (Set.mem_univ u)
  have hd : ‖p - q‖ < f u₀ / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hq
  have hd' : ‖p - q‖ < ‖x u - p‖ := lt_of_lt_of_le hd (by linarith)
  rw [conj_pointComplex_mul_re_m85d0e79]
  have hw : x u - q = (x u - p) + (p - q) := by abel
  rw [hw, inner_add_right, real_inner_self_eq_norm_sq]
  have hcs := abs_real_inner_le_norm (x u - p) (p - q)
  have hlower : -(‖x u - p‖ * ‖p - q‖) ≤ inner ℝ (x u - p) (p - q) :=
    (neg_le_of_abs_le hcs)
  nlinarith [norm_pos_iff.mpr (hne u)]

/-- Winding of a continuous closed loop is locally constant away from its range. -/
theorem curveWinding_locally_constant_off_range {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos hab hx hp
  refine ⟨Metric.ball p r, Metric.isOpen_ball, Metric.mem_ball_self hr, fun q hq ↦ ?_⟩
  have hqp : dist q p < r := by simpa [dist_comm] using hq
  have hpos := hdot q hqp
  by_cases hpLift : ∃ θ, IsCurveAngleLift x p θ
  · obtain ⟨θ, hθ⟩ := hpLift
    exact curveWinding_eq_of_relative_dot_pos hab hx hclosed hθ hpos
  · have hqLift : ¬∃ ψ, IsCurveAngleLift x q ψ := by
      rintro ⟨ψ, hψ⟩
      have hrev : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - q)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - p)).re := by
        intro u
        rw [conj_pointComplex_mul_re_m85d0e79, real_inner_comm, ← conj_pointComplex_mul_re_m85d0e79]
        exact hpos u
      exact hpLift ⟨_, hψ.add_principal_basepoint_correction hx hrev⟩
    unfold curveWinding
    rw [dite_eq_right hqLift, dite_eq_right hpLift]

/-- While the relative dot product with the initial radius vector stays positive, the
increment of a continuous angle lift is the principal relative argument, computed as the
arctangent of the ratio of the relative cross product to the relative dot product. -/
theorem IsCurveAngleLift.sub_eq_arctan_of_dot_pos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ) {t u : Set.Icc a b}
    (htu : (t : ℝ) ≤ (u : ℝ))
    (hpos : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
      0 < (x t - p) 0 * (x s - p) 0 + (x t - p) 1 * (x s - p) 1) :
    θ u - θ t = Real.arctan
      (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
        ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
  have hsub : ∀ s : Set.Icc (t : ℝ) (u : ℝ), (s : ℝ) ∈ Set.Icc a b := fun s ↦
    ⟨le_trans t.property.1 s.property.1, le_trans s.property.2 u.property.2⟩
  let ι : Set.Icc (t : ℝ) (u : ℝ) → Set.Icc a b := fun s ↦ ⟨s.val, hsub s⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  set y : Set.Icc (t : ℝ) (u : ℝ) → Point := x ∘ ι with hy
  have hycont : Continuous y := hx.comp hι
  have hιu : ι ⟨(u : ℝ), htu, le_rfl⟩ = u := Subtype.ext rfl
  have hιt : ι ⟨(t : ℝ), le_rfl, htu⟩ = t := Subtype.ext rfl
  set z : ℂ := Complex.orthonormalBasisOneI.repr.symm (x t - p) with hz
  set w : Set.Icc (t : ℝ) (u : ℝ) → ℂ :=
    fun s ↦ Complex.orthonormalBasisOneI.repr.symm (y s - p) with hw
  have hwcont : Continuous w :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hycont.sub continuous_const)
  have hre (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).re =
        (x t - p) 0 * (x (ι s) - p) 0 + (x t - p) 1 * (x (ι s) - p) 1 := by
    simp only [hz, hw, hy, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      pointComplex_re_m85d0e79, pointComplex_im_m85d0e79, Function.comp_apply]
    ring
  have him (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).im =
        (x t - p) 0 * (x (ι s) - p) 1 - (x t - p) 1 * (x (ι s) - p) 0 := by
    simp only [hz, hw, hy, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      pointComplex_re_m85d0e79, pointComplex_im_m85d0e79, Function.comp_apply]
    ring
  have hposC : ∀ s : Set.Icc (t : ℝ) (u : ℝ), 0 < (starRingEnd ℂ z * w s).re := by
    intro s
    rw [hre s]
    exact hpos (ι s) s.property.1 s.property.2
  have hzne : z ≠ 0 := by
    intro h0
    have := hposC ⟨(t : ℝ), le_rfl, htu⟩
    rw [h0] at this
    simp at this
  have hwne : ∀ s, w s ≠ 0 := by
    intro s h0
    have := hposC s
    rw [h0] at this
    simp at this
  have hznorm : ‖z‖ = ‖x t - p‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map _
  have hc : Real.cos (θ t) = z.re / ‖z‖ := by
    rw [hznorm, hz, pointComplex_re_m85d0e79]; exact (hθ.2 t).1
  have hsn : Real.sin (θ t) = z.im / ‖z‖ := by
    rw [hznorm, hz, pointComplex_im_m85d0e79]; exact (hθ.2 t).2
  have hlift1 : IsCurveAngleLift y p (θ ∘ ι) := hθ.comp hι
  have hlift2 : IsCurveAngleLift y p
      (fun s ↦ θ t + Complex.arg (starRingEnd ℂ z * w s)) := by
    refine ⟨continuous_const.add
      (continuous_arg_conj_mul_of_re_pos continuous_const hwcont hposC), fun s ↦ ?_⟩
    have hrot := normalized_complex_rotation_by_relative_arg hzne (hwne s) hc hsn
    have hwnorm : ‖w s‖ = ‖y s - p‖ :=
      Complex.orthonormalBasisOneI.repr.symm.norm_map _
    rw [hwnorm] at hrot
    simpa only [hw, pointComplex_re_m85d0e79, pointComplex_im_m85d0e79] using hrot
  have hincr := IsCurveAngleLift.endpoint_increment_eq htu hlift1 hlift2
  simp only [Function.comp_apply, hιu, hιt] at hincr
  have hwt : w ⟨(t : ℝ), le_rfl, htu⟩ = z := by
    simp only [hw, hy, Function.comp_apply, hιt, hz]
  have hargt : Complex.arg (starRingEnd ℂ z * w ⟨(t : ℝ), le_rfl, htu⟩) = 0 := by
    rw [hwt, mul_comm, Complex.mul_conj]
    exact Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg z)
  rw [hargt] at hincr
  have hre' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).re =
      (x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1 := by
    rw [hre ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have him' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).im =
      (x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0 := by
    rw [him ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have hargu : Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩) =
      Real.arctan
        (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
          ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
    rw [← hre', ← him']
    have hlt : |Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hposC _))
    refine (Real.arctan_eq_of_tan_eq (Complex.tan_arg _) ?_).symm
    exact ⟨neg_lt_of_abs_lt hlt, lt_of_abs_lt hlt⟩
  rw [hargu] at hincr
  linarith [hincr]

/-- Winding is constant on an open neighbourhood of any point off the range of a closed
continuous loop, and that neighbourhood avoids the range. -/
theorem curveWinding_locally_constant_on_compl_range
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      q ∉ Set.range x ∧ curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨U, hU, hpU, heq⟩ := curveWinding_locally_constant_off_range hab hx hclosed hp
  have hclosedRange : IsClosed (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isClosed
  exact ⟨U ∩ (Set.range x)ᶜ, hU.inter hclosedRange.isOpen_compl, ⟨hpU, hp⟩,
    fun q hq ↦ ⟨hq.2, heq q hq.1⟩⟩

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Winding Lifts
-/

public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_m8588f5d (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_m8588f5d (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_m8588f5d (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

/-- Every continuous interval path avoiding a point admits a continuous angle lift. -/
theorem exists_curveAngleLift_of_avoids {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) : ∃ α, IsCurveAngleLift x p α := by
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let φ : I → Set.Icc a b := Set.Icc.convexComb A B
  let z : I → ℂ := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x (φ u) - p)
  have hz : Continuous z :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp ((hx.comp (Set.Icc.continuous_convexComb
        A B)).sub
      continuous_const)
  have hzne (u : I) : z u ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨φ u, heq⟩
  let ϑ : I → Real.Angle := fun u ↦ (Complex.arg (z u) : Real.Angle)
  have hϑ : Continuous ϑ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuousAt_arg_coe_angle (hzne u)).comp hz.continuousAt
  let ϑ₀ := ϑ 0
  obtain ⟨β, hβ, hβ0, hβϑ⟩ := Real.Angle.exists_continuous_lift_zero
    (fun u ↦ ϑ u - ϑ₀) (hϑ.sub continuous_const) (by simp [ϑ₀])
  let ψ : Set.Icc a b → I := fun u ↦
    ⟨((u : ℝ) - a) / (b - a), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr u.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (by linarith [u.property.2])⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hφψ (u : Set.Icc a b) : φ (ψ u) = u := by
    apply Subtype.ext
    simp [φ, ψ, A, B]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  let c := Complex.arg (z 0)
  refine ⟨fun u ↦ β (ψ u) + c, hβ.comp hψ |>.add continuous_const, fun u ↦ ?_⟩
  have hangle : ((β (ψ u) + c : ℝ) : Real.Angle) = Complex.arg
      (Complex.orthonormalBasisOneI.repr.symm (x u - p)) := by
    rw [Real.Angle.coe_add, hβϑ]
    simp only [ϑ₀, c, ϑ]
    change (Complex.arg (Complex.orthonormalBasisOneI.repr.symm (x (φ (ψ u)) - p)) : Real.Angle) -
        (Complex.arg (z 0) : Real.Angle) + (Complex.arg (z 0) : Real.Angle) = _
    rw [hφψ]
    simp
  have hne : Complex.orthonormalBasisOneI.repr.symm (x u - p) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨u, heq⟩
  constructor
  · have := congrArg Real.Angle.cos hangle
    rw [Real.Angle.cos_coe, Real.Angle.cos_coe, Complex.cos_arg hne] at this
    simpa only [pointComplex_re_m8588f5d, Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      this
  · have := congrArg Real.Angle.sin hangle
    rw [Real.Angle.sin_coe, Real.Angle.sin_coe, Complex.sin_arg] at this
    simpa only [pointComplex_im_m8588f5d, Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      this

/-- A closed path contained in a strict half-plane about a point has winding zero there. -/
theorem curveWinding_eq_zero_of_inner_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (p v : Point) (hv : v ≠ 0) (hpos : ∀ u, 0 < inner ℝ v (x u - p)) :
    curveWinding hab x p = 0 := by
  let z := Complex.orthonormalBasisOneI.repr.symm v
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  have hz : z ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff]
    exact hv
  have hpositive (u : Set.Icc a b) : 0 < (starRingEnd ℂ z * w u).re := by
    rw [conj_pointComplex_mul_re_m8588f5d]
    exact hpos u
  have harg : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ z * w u)) :=
    continuous_arg_conj_mul_of_re_pos continuous_const
      (Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub continuous_const)) hpositive
  let α := fun u ↦ Complex.arg z + Complex.arg (starRingEnd ℂ z * w u)
  have hα : IsCurveAngleLift x p α := by
    refine ⟨continuous_const.add harg, fun u ↦ ?_⟩
    have hw : w u ≠ 0 := by
      intro heq
      simpa [heq] using hpositive u
    simpa only [α, w, pointComplex_re_m8588f5d, pointComplex_im_m8588f5d,
        Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      normalized_complex_rotation_by_arg hz hw
  rw [hα.curveWinding_eq hab]
  have hend : α ⟨b, hab, le_rfl⟩ = α ⟨a, le_rfl, hab⟩ := by
    simp only [α, w, hclosed]
  rw [hend, sub_self, zero_div]

/-- A closed continuous loop has winding zero at every point of an unbounded connected
component of the complement of its range. -/
theorem curveWinding_eq_zero_of_unbounded_component
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x)
    (hunbounded : ¬Bornology.IsBounded (connectedComponentIn (Set.range x)ᶜ p)) :
    curveWinding hab x p = 0 := by
  let V := connectedComponentIn (Set.range x)ᶜ p
  let _ : PreconnectedSpace V :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hlc : IsLocallyConstant (fun z : V ↦ curveWinding hab x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := connectedComponentIn_subset _ _ z.property
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  have hrangeBounded : Bornology.IsBounded (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hrangeBounded
  have hRnonneg : 0 ≤ R := by
    have h := hR (Set.mem_range_self ⟨a, le_rfl, hab⟩)
    have hnorm : ‖x ⟨a, le_rfl, hab⟩‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    exact (norm_nonneg _).trans hnorm
  have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
    by_contra hn
    push Not at hn
    apply hunbounded
    refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
    intro v hv
    simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
  obtain ⟨v, hvV, hvnorm⟩ := hvfar
  have hvzero : curveWinding hab x v = 0 := by
    apply curveWinding_eq_zero_of_inner_pos hab hx hclosed v (-v)
    · exact neg_ne_zero.mpr (by
        intro hv0
        rw [hv0, norm_zero] at hvnorm
        linarith)
    · intro u
      rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [← real_inner_comm v (x u)]
      have hxu := hR (Set.mem_range_self u)
      have hxnorm : ‖x u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hxu
      have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
      have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
      have hinner := abs_real_inner_le_norm (x u) v
      have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
      have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
          (mul_lt_mul_of_pos_right hvlarge hvpos)
      rw [pow_two]
      linarith
  exact (hlc.apply_eq_of_preconnectedSpace ⟨p, mem_connectedComponentIn hp⟩ ⟨v, hvV⟩).trans
    hvzero

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The range of an almost injective continuous BV path is null

A continuous planar BV path that is injective on `[a, b)` sweeps a Lebesgue null set: each
compact initial subarc has finite Hausdorff length, hence vanishing Hausdorff `2`-measure,
and a rational exhaustion together with the terminal point covers the whole range.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- The range of a continuous planar BV path injective on `[a, b)` is Lebesgue null. -/
theorem ContinuousBVPaths.volume_range_eq_zero_of_injOn
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) : volume (Set.range x.val) = 0 := by
  let γ : ℝ → Point := x.val ∘ Set.projIcc a b hab
  have hγcont : Continuous γ := x.property.1.comp continuous_projIcc
  have hγBV (q : ℝ) : BoundedVariationOn γ (Icc a q) := by
    apply ne_top_of_le_ne_top x.boundedVariationOn
    exact eVariationOn.comp_le_of_monotoneOn x.val (Set.projIcc a b hab)
      ((Set.monotone_projIcc hab).monotoneOn _) (fun _ _ ↦ mem_univ _)
  have hnull (q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}) :
      volume (γ '' Icc a (q : ℝ)) = 0 := by
    apply volume_image_Icc_eq_zero_of_boundedVariationOn γ q.property.1 hγcont.continuousOn
      _ (hγBV _)
    intro u hu v hv huv
    have huab : u ∈ Icc a b := ⟨hu.1, hu.2.trans q.property.2.le⟩
    have hvab : v ∈ Icc a b := ⟨hv.1, hv.2.trans q.property.2.le⟩
    have heq := hinj (show (Set.projIcc a b hab u : ℝ) < b by
        rw [Set.projIcc_of_mem hab huab]; exact hu.2.trans_lt q.property.2)
      (show (Set.projIcc a b hab v : ℝ) < b by
        rw [Set.projIcc_of_mem hab hvab]; exact hv.2.trans_lt q.property.2) huv
    have hval := congrArg Subtype.val heq
    simpa only [Set.projIcc_of_mem hab huab, Set.projIcc_of_mem hab hvab] using hval
  apply measure_mono_null (t := {x.val ⟨b, hab, le_rfl⟩} ∪
    ⋃ q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}, γ '' Icc a (q : ℝ))
  · rintro y ⟨t, rfl⟩
    by_cases ht : (t : ℝ) = b
    · exact Or.inl (congrArg x.val (show t = ⟨b, hab, le_rfl⟩ from Subtype.ext ht))
    · have htb : (t : ℝ) < b := lt_of_le_of_ne t.property.2 ht
      obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
      apply Or.inr
      apply mem_iUnion.2
      refine ⟨⟨q, t.property.1.trans htq.le, hqb⟩, (t : ℝ), ⟨t.property.1, htq.le⟩, ?_⟩
      dsimp [γ]
      rw [Set.projIcc_of_mem hab t.property]
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null hnull)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Segment Area
-/

public section

noncomputable section

namespace MovingSofa

/-- Half the oriented determinant of the two endpoints. -/
@[expose]
def segmentArea (p q : Point) : ℝ := planeCrossProduct p q / 2

/-- The signed segment area is antisymmetric in its two endpoints. -/
theorem segmentArea_swap (p q : Point) : segmentArea p q = -segmentArea q p := by
  rw [segmentArea, segmentArea, planeCrossProduct_swap p q]
  ring

/-- Translating both endpoints of a segment shifts its signed area by a boundary term. -/
theorem segmentArea_add_right (p q v : Point) :
    segmentArea (p + v) (q + v) =
      segmentArea p q + (v 0 * (q 1 - p 1) - v 1 * (q 0 - p 0)) / 2 := by
  have hadd : ∀ (x y : Point) (i : Fin 2), (x + y) i = x i + y i := fun _ _ _ ↦ by simp
  simp only [segmentArea, planeCrossProduct, hadd]
  ring

/-- The signed area of the segment joining two convex combinations of endpoints is the same
combination of the two signed areas, provided the two endpoints of each pair have a common height:
the mixed terms then cancel. -/
theorem segmentArea_combination_of_apply_one_eq (c : ℝ) {p₁ p₂ q₁ q₂ : Point}
    (hp : p₁ 1 = p₂ 1) (hq : q₁ 1 = q₂ 1) :
    segmentArea ((1 - c) • p₁ + c • p₂) ((1 - c) • q₁ + c • q₂) =
      (1 - c) * segmentArea p₁ q₁ + c * segmentArea p₂ q₂ := by
  simp only [segmentArea, planeCrossProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp, hq]
  ring

/-- Two points on a normal line through the origin span no signed area. -/
theorem segmentArea_eq_zero_of_inner_normalVector_eq_zero {p q : Point} {t : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = 0)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = 0) : segmentArea p q = 0 := by
  rw [segmentArea, planeCrossProduct_eq_inner_frame p q t, hp, hq]
  ring

/-- Collinear additivity of the signed segment area on a common normal line. -/
theorem segmentArea_sub_segmentArea_of_inner_normalVector_eq {p q s : Point} {t c : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = c)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = c)
    (hs : inner ℝ s (normalVector (t : Real.Angle)) = c) :
    segmentArea p s - segmentArea q s = segmentArea p q := by
  rw [segmentArea, segmentArea, segmentArea, planeCrossProduct_eq_inner_frame p s t,
    planeCrossProduct_eq_inner_frame q s t, planeCrossProduct_eq_inner_frame p q t,
    hp, hq, hs]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Segment Area / Parametrization
-/

public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- The affine segment from `p` to `q`, bundled as a continuous BV path. -/
@[expose]
def lineSegmentBVPath (p q : Point) : ContinuousBVPaths 0 1 where
  val := Path.segment p q
  property := by
    constructor
    · exact (Path.segment p q).continuous
    · intro i
      let C : NNReal := ⟨|q i - p i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦ p i + r * (q i - p i)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        change |(p i + x * (q i - p i)) - (p i + y * (q i - p i))| ≤
          |q i - p i| * |x - y|
        rw [show (p i + x * (q i - p i)) - (p i + y * (q i - p i)) =
          (x - y) * (q i - p i) by ring, abs_mul, mul_comm]
      have hid : BoundedVariationOn ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) Set.univ := by
        apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
          Set.univ).boundedVariationOn (C := 1)
        intro t _
        rw [abs_of_nonneg t.property.1]
        exact t.property.2
      have hbv := hLip.comp_boundedVariationOn hid
      rw [show (fun t ↦ (Path.segment p q t) i) =
          (fun r : ℝ ↦ p i + r * (q i - p i)) ∘ ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) by
        funext t
        simp only [Path.segment_apply, AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul, Function.comp_apply]
        change (t : ℝ) * (q i - p i) + p i =
          p i + (t : ℝ) * (q i - p i)
        ring]
      exact hbv

/-- The affine parametrization of an oriented segment, evaluated. -/
theorem lineSegmentBVPath_apply (p q : Point) (s : Set.Icc (0 : ℝ) 1) :
    (lineSegmentBVPath p q).val s = (1 - (s : ℝ)) • p + (s : ℝ) • q := by
  change Path.segment p q s = _
  simp [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

theorem curveAreaFunctional_lineSegmentBVPath (p q : Point) :
    curveAreaFunctional (lineSegmentBVPath p q) = segmentArea p q := by
  have hcoord (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) :
      (continuousBVCoordinate (lineSegmentBVPath p q) i).toFun t =
        p i + (q i - p i) * (t : ℝ) := by
    change (Path.segment p q t) i = _
    simp [Path.segment_apply, AffineMap.lineMap_apply_module']
    ring
  unfold curveAreaFunctional segmentArea
  change
    (intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 1)
        (continuousBVCoordinate (lineSegmentBVPath p q) 0).toFun Set.univ -
      intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 0)
        (continuousBVCoordinate (lineSegmentBVPath p q) 1).toFun Set.univ) / 2 =
      planeCrossProduct p q / 2
  rw [intervalStieltjesIntegral_affine_cross
    (continuousBVCoordinate (lineSegmentBVPath p q) 0)
    (continuousBVCoordinate (lineSegmentBVPath p q) 1)
    (p 0) (q 0 - p 0) (p 1) (q 1 - p 1) (hcoord 0) (hcoord 1)]
  simp only [planeCrossProduct]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Smooth Interval Paths
-/

public section

noncomputable section

namespace MovingSofa

/-- A continuously differentiable planar path on a compact interval has continuous
bounded-variation coordinates. -/
@[expose]
def continuousBVOfContDiffOn {a b : ℝ} (f : ℝ → Point)
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) : ContinuousBVPaths a b := by
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf.continuousOn, ?_⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath := hC.comp_boundedVariationOn (fun t _ ↦ t.property) hid
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A Lipschitz planar path on a compact interval has continuous bounded-variation coordinates. -/
@[expose]
def continuousBVOfLipschitz {a b : ℝ} (f : Set.Icc a b → Point)
    {C : NNReal} (hf : LipschitzWith C f) : ContinuousBVPaths a b := by
  refine ⟨f, hf.continuous, ?_⟩
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath : BoundedVariationOn f Set.univ := by
    exact hf.comp_boundedVariationOn
      (show BoundedVariationOn (id : Set.Icc a b → Set.Icc a b) Set.univ from hid)
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A coordinate of an interval path has bounded variation on a closed subinterval on which the
path agrees with a continuously differentiable function. -/
theorem boundedVariationOn_coord_Icc_of_contDiffOn {a b : ℝ} (g : Set.Icc a b → Point)
    {l r : ℝ} (hl : a ≤ l) (hlr : l ≤ r) (hr : r ≤ b) {F : ℝ → Point}
    (hF : ContDiffOn ℝ 1 F (Set.Icc l r))
    (hgF : ∀ t : Set.Icc l r, g ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩ = F t.val)
    (i : Fin 2) :
    BoundedVariationOn (fun t : Set.Icc a b ↦ g t i)
      (Set.Icc ⟨l, hl, hlr.trans hr⟩ ⟨r, hl.trans hlr, hr⟩) := by
  set ι : Set.Icc l r → Set.Icc a b := fun t ↦ ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩
  have hmono : MonotoneOn ι Set.univ := fun _ _ _ _ h ↦ h
  have himg : ι '' Set.univ =
      Set.Icc (⟨l, hl, hlr.trans hr⟩ : Set.Icc a b) ⟨r, hl.trans hlr, hr⟩ := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨t.2.1, t.2.2⟩
    · intro hx
      exact ⟨⟨x.val, hx.1, hx.2⟩, Set.mem_univ _, Subtype.ext rfl⟩
  change eVariationOn _ _ ≠ ⊤
  rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ ι hmono]
  have hfun : ((fun t : Set.Icc a b ↦ g t i) ∘ ι) = fun t : Set.Icc l r ↦ F t.val i := by
    funext t
    exact congrArg (fun p : Point ↦ p i) (hgF t)
  rw [hfun]
  exact (continuousBVOfContDiffOn F hF).property.2 i

/-- Gluing two continuously differentiable pieces along a shared endpoint gives a continuous
path of bounded variation. -/
@[expose]
def continuousBVOfContDiffOnIccUnionIcc {a b c : ℝ} (f : ℝ → Point) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : ContDiffOn ℝ 1 f (Set.Icc a b)) (h₂ : ContDiffOn ℝ 1 f (Set.Icc b c)) :
    ContinuousBVPaths a c := by
  have hf : ContinuousOn f (Set.Icc a c) := by
    rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
    exact h₁.continuousOn.union_of_isClosed h₂.continuousOn isClosed_Icc isClosed_Icc
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf, fun i ↦ ?_⟩
  refine BoundedVariationOn.univ_of_Icc_endpoints (hab.trans hbc)
    (BoundedVariationOn.Icc_union_Icc
      (show (⟨a, le_rfl, hab.trans hbc⟩ : Set.Icc a c) ≤ ⟨b, hab, hbc⟩ from hab)
      (show (⟨b, hab, hbc⟩ : Set.Icc a c) ≤ ⟨c, hab.trans hbc, le_rfl⟩ from hbc)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ le_rfl hab hbc h₁ (fun _ ↦ rfl) i)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ hab hbc le_rfl h₂ (fun _ ↦ rfl) i))

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Radial Loop
-/

public section

noncomputable section
namespace MovingSofa

/-- A Lipschitz map on the unit circle induces a continuous BV loop in increasing angular order. -/
@[expose]
def radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : ContinuousBVPaths 0 (2 * Real.pi) := by
  let n : Set.Icc (0 : ℝ) (2 * Real.pi) → {u : Point | ‖u‖ = 1} :=
    fun t ↦ ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩
  have hn : LipschitzWith 1 n := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    exact lipschitzWith_normalVector_real.dist_le_mul t.val u.val
  exact continuousBVOfLipschitz (f ∘ n) (hf.comp hn)

/-- The radial BV loop evaluates by applying the circle map to the angular normal. -/
lemma radialBVLoop_apply (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (t : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (radialBVLoop f hf).val t =
      f ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩ := rfl

/-- The radial BV loop has equal endpoints. -/
lemma radialBVLoop_closed (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) :
    (radialBVLoop f hf).val ⟨0, le_rfl, by positivity⟩ =
      (radialBVLoop f hf).val ⟨2 * Real.pi, by positivity, le_rfl⟩ := by
  rw [radialBVLoop_apply, radialBVLoop_apply]
  apply congrArg f
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [normalVector, frame]

/-- An injective circle map gives a radial loop injective before its final endpoint. -/
lemma radialBVLoop_injOn (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (hinj : Function.Injective f) :
    Set.InjOn (radialBVLoop f hf).val {t | (t : ℝ) < 2 * Real.pi} := by
  intro t ht u hu h
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [radialBVLoop_apply, radialBVLoop_apply] at h
  have hn := congrArg Subtype.val (hinj h)
  have ha : (t.val : Real.Angle) = (u.val : Real.Angle) := by
    apply Real.Angle.cos_sin_inj
    · exact congrFun (congrArg WithLp.ofLp hn) 0
    · exact congrFun (congrArg WithLp.ofLp hn) 1
  apply Subtype.ext
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show t.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨t.property.1, by simpa using ht⟩)
    (show u.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨u.property.1, by simpa using hu⟩)).mp ha

/-- The radial BV loop has the same range as the underlying unit-circle map. -/
lemma range_radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : Set.range (radialBVLoop f hf).val = Set.range f := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact ⟨_, (radialBVLoop_apply f hf t).symm⟩
  · rintro p ⟨u, rfl⟩
    obtain ⟨θ, hθ⟩ := exists_angle_normalVector_eq u.property
    let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let t := AddCircle.equivIco (2 * Real.pi) 0 θ
    have ht : (t.val : Real.Angle) = θ := AddCircle.coe_equivIco
    refine ⟨⟨t.val, t.property.1, ?_⟩, ?_⟩
    · simpa using t.property.2.le
    · rw [radialBVLoop_apply]
      apply congrArg f
      apply Subtype.ext
      exact (congrArg normalVector ht).trans hθ

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# A Stieltjes chain rule with a local quadratic remainder

The hypothesis of `ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder`
quantifies the remainder only over parameter pairs closer than a fixed positive threshold.
This is what a locally defined argument branch supplies: no single plane function has to be
named, and no constant is needed across a branch cut.
-/

public section

noncomputable section

open Set

namespace MovingSofa

/-- If a real parameter function `A` has increments matching the signed pair
`D₁ dγ₁ - D₀ dγ₀` up to a quadratic remainder on all parameter pairs closer than a fixed
positive threshold, then its endpoint increment is the corresponding difference of
coordinate Stieltjes integrals. -/
theorem ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hBV : BoundedVariationOn x.val univ) (A : Set.Icc a b → ℝ) (D : Point → Fin 2 → ℝ)
    (hD : ∀ i, Continuous (fun t ↦ D (x.val t) i)) {C : ℝ} (hC : 0 ≤ C)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (herror : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
      |A u - A t -
        (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤ C * ‖x.val u - x.val t‖ ^ 2) :
    A ⟨b, hab, le_rfl⟩ - A ⟨a, le_rfl, hab⟩ =
      intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ D (x.val t) 1) univ -
      intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ D (x.val t) 0) univ := by
  obtain ⟨cuts, hcuts, hzero, hlast, hmesh⟩ :=
    Set.Icc.exists_partitions_mesh_tendsto_zero hab
  let N : ℕ → ℕ := fun k ↦ k + 1
  have htaylor := hBV.tendsto_sum_of_local_quadratic_remainder hab x.property.1 A
    (fun t v ↦ D (x.val t) 1 * v 1 - D (x.val t) 0 * v 0) hC hδ₀ herror
    N cuts hcuts hzero hlast hmesh
  have hcoord (i : Fin 2) := tendsto_stieltjesSum_of_mesh_tendsto_zero
    (continuousBVCoordinate x i) ((PiLp.continuous_apply 2 _ i).comp x.property.1)
    (hD i) N cuts hcuts hzero hlast hmesh
  have hsum := (hcoord 1).sub (hcoord 0)
  simp only [← Finset.sum_sub_distrib, continuousBVCoordinate] at hsum
  exact tendsto_nhds_unique htaylor hsum

end MovingSofa

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.MonotoneRoof`.
* `Area.ThreePieceRoof`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Monotone Roof
-/

public section

noncomputable section

namespace MovingSofa

/-- Recover the vertical coordinate using a chosen inverse of the path’s horizontal
coordinate. -/
def monotoneRoofHeight {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : ℝ) : ℝ := by
  classical
  letI : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  exact γ.val (Function.invFun (fun t ↦ γ.val t 0) s) 1

/-- The closed region between the horizontal axis and the path’s roof graph. -/
def monotoneRoofRegion {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b) : Set Point :=
  {p | γ.val ⟨a, le_rfl, hab.le⟩ 0 ≤ p 0 ∧
    p 0 ≤ γ.val ⟨b, hab.le, le_rfl⟩ 0 ∧ 0 ≤ p 1 ∧
    p 1 ≤ monotoneRoofHeight hab γ (p 0)}

/-- Traverse the roof path backwards and return along its horizontal base. -/
def monotoneRoofLoop {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : Set.Icc (0 : ℝ) 2) : Point :=
  if hs : s.val ≤ 1 then
    γ.val ⟨b - (b - a) * s.val, by
      constructor
      · nlinarith [s.property.1]
      · nlinarith [s.property.1]⟩
  else
    (2 - s.val) • γ.val ⟨a, le_rfl, hab.le⟩ +
      (s.val - 1) • γ.val ⟨b, hab.le, le_rfl⟩

private theorem monotoneRoofLoop_concatenation {a b : ℝ} (hab : a < b)
    (γ γrev : ContinuousBVPaths a b)
    (hγrev : γrev.val = γ.val ∘ Set.Icc.reverse hab.le)
    (Γ : ContinuousBVPaths 0 2) (hΓval : Γ.val = monotoneRoofLoop hab γ) :
    IsPathConcatenation (⟨0, 2, by norm_num, Γ⟩ : RectifiablePathData)
      ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
        ⟨0, 1, zero_le_one, lineSegmentBVPath
          (γ.val ⟨a, le_rfl, hab.le⟩) (γ.val ⟨b, hab.le, le_rfl⟩)⟩] := by
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  refine ⟨by norm_num,
    ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩], ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exact absurd hij (by decide))
        | (refine Subtype.mk_le_mk.mpr ?_; norm_num)
  · rfl
  · rfl
  · intro i
    fin_cases i
    · change ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
          (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b),
          Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
            Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
            ∀ u, Γ.val ⟨(ϕ u : ℝ), (ϕ u).property.1,
              le_trans (ϕ u).property.2 (by norm_num)⟩ = γrev.val (ψ u)
      refine ⟨fun u ↦ ⟨(u : ℝ), u.property.1, u.property.2⟩,
        fun u ↦ ⟨a + (b - a) * (u : ℝ),
          by linarith only [mul_nonneg hba.le u.property.1],
          by linarith only [mul_le_mul_of_nonneg_left u.property.2 hba.le]⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact continuous_subtype_val.subtype_mk _
      · exact fun x y hxy ↦ hxy
      · exact fun z ↦ ⟨⟨(z : ℝ), z.property.1, z.property.2⟩, Subtype.ext rfl⟩
      · exact (continuous_const.add
          (continuous_const.mul continuous_subtype_val)).subtype_mk _
      · intro x y hxy
        have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
        change a + (b - a) * (x : ℝ) ≤ a + (b - a) * (y : ℝ)
        linarith only [mul_le_mul_of_nonneg_left hxy' hba.le]
      · intro t
        refine ⟨⟨((t : ℝ) - a) / (b - a), ?_, ?_⟩, ?_⟩
        · exact div_nonneg (by linarith only [t.property.1]) hba.le
        · rw [div_le_one hba]
          linarith only [t.property.2]
        · apply Subtype.ext
          change a + (b - a) * (((t : ℝ) - a) / (b - a)) = (t : ℝ)
          field_simp
          ring
      · intro u
        have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
        have h1 : (u : ℝ) ≤ 1 := u.property.2
        rw [hΓval, hγrev]
        change monotoneRoofLoop hab γ ⟨(u : ℝ), h0, by linarith⟩ =
          γ.val (Set.Icc.reverse hab.le ⟨a + (b - a) * (u : ℝ),
            by linarith only [mul_nonneg hba.le h0],
            by linarith only [mul_le_mul_of_nonneg_left h1 hba.le]⟩)
        unfold monotoneRoofLoop
        rw [dite_eq_left (show ((⟨(u : ℝ), h0, by linarith⟩ : Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1
          from h1)]
        exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
          change b - (b - a) * (u : ℝ) = a + b - (a + (b - a) * (u : ℝ))
          ring))
    · change ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (1 : ℝ) 2)
          (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
          Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
            Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
            ∀ u, Γ.val ⟨(ϕ u : ℝ), le_trans (by norm_num) (ϕ u).property.1,
              (ϕ u).property.2⟩ =
              (lineSegmentBVPath (γ.val A) (γ.val B)).val (ψ u)
      refine ⟨fun u ↦ ⟨1 + (u : ℝ), by linarith [u.property.1], by
          linarith [u.property.2]⟩,
        fun u ↦ u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (continuous_const.add continuous_subtype_val).subtype_mk _
      · intro x y hxy
        have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
        change (1 : ℝ) + (x : ℝ) ≤ 1 + (y : ℝ)
        linarith
      · intro z
        refine ⟨⟨(z : ℝ) - 1, by linarith [z.property.1], by
          linarith [z.property.2]⟩, ?_⟩
        apply Subtype.ext
        change (1 : ℝ) + ((z : ℝ) - 1) = (z : ℝ)
        ring
      · exact continuous_id
      · exact fun x y hxy ↦ hxy
      · exact fun z ↦ ⟨z, rfl⟩
      · intro u
        have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
        have h1 : (u : ℝ) ≤ 1 := u.property.2
        rw [hΓval]
        change monotoneRoofLoop hab γ ⟨1 + (u : ℝ), by linarith, by linarith⟩ =
          Path.segment (γ.val A) (γ.val B) u
        unfold monotoneRoofLoop
        rcases eq_or_lt_of_le h0 with hu0 | hu0
        · rw [dite_eq_left (show ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
            Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by simp [← hu0])]
          have huval : (u : ℝ) = 0 := hu0.symm
          have hseg : Path.segment (γ.val A) (γ.val B) u = γ.val A := by
            rw [Path.segment_apply]
            rw [show (u : ℝ) = 0 from huval]
            simp
          rw [hseg]
          exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
            change b - (b - a) * (1 + (u : ℝ)) = a
            rw [huval]
            ring))
        · rw [dite_eq_right (show ¬ ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
            Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by
              change ¬ (1 + (u : ℝ) ≤ 1)
              linarith)]
          change (2 - (1 + (u : ℝ))) • γ.val A + ((1 + (u : ℝ)) - 1) • γ.val B =
            Path.segment (γ.val A) (γ.val B) u
          rw [Path.segment_apply, AffineMap.lineMap_apply_module']
          module

private theorem monotoneRoof_area {a b : ℝ} (hab : a < b)
    (γ : ContinuousBVPaths a b) (hk : StrictMono (fun t ↦ γ.val t 0))
    (hh : ∀ t, 0 ≤ γ.val t 1)
    (ha : γ.val ⟨a, le_rfl, hab.le⟩ 1 = 0)
    (hb : γ.val ⟨b, hab.le, le_rfl⟩ 1 = 0) :
    ClassicalResults.area (monotoneRoofRegion hab γ) = -curveAreaFunctional γ ∧
      ClassicalResults.area (monotoneRoofRegion hab γ) =
        ∫ s in γ.val ⟨a, le_rfl, hab.le⟩ 0..γ.val ⟨b, hab.le, le_rfl⟩ 0,
          monotoneRoofHeight hab γ s := by
  classical
  set A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩ with hAdef
  set B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩ with hBdef
  set c : ℝ := γ.val A 0 with hcdef
  set d : ℝ := γ.val B 0 with hddef
  have hAB : A < B := hab
  have hcd : c < d := hk hAB
  -- the horizontal coordinate as a map onto `[c, d]`
  have hγ0 : Continuous fun t : Set.Icc a b ↦ γ.val t 0 :=
    (PiLp.continuous_apply 2 _ 0).comp γ.property.1
  have hγ1 : Continuous fun t : Set.Icc a b ↦ γ.val t 1 :=
    (PiLp.continuous_apply 2 _ 1).comp γ.property.1
  have hmem : ∀ t : Set.Icc a b, γ.val t 0 ∈ Set.Icc c d := fun t ↦
    ⟨hk.monotone (show A ≤ t from t.property.1),
      hk.monotone (show t ≤ B from t.property.2)⟩
  set kmap : Set.Icc a b → Set.Icc c d := fun t ↦ ⟨γ.val t 0, hmem t⟩ with hkmapdef
  have hkc : Continuous kmap := hγ0.subtype_mk _
  have hkinj : Function.Injective kmap := fun x y h ↦ hk.injective (congrArg Subtype.val h)
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hksurj : Function.Surjective kmap := by
    intro s
    obtain ⟨t, ht⟩ := intermediate_value_univ A B hγ0 s.property
    exact ⟨t, Subtype.ext ht⟩
  -- the continuous monotone inverse `φ = k⁻¹`
  set khom : Set.Icc a b ≃ₜ Set.Icc c d :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective kmap ⟨hkinj, hksurj⟩) hkc
    with hkhomdef
  set φ : Set.Icc c d → Set.Icc a b := ⇑khom.symm with hφdef
  have hkhom_apply : ∀ t, khom t = kmap t := fun _ ↦ rfl
  have hφk : ∀ s : Set.Icc c d, γ.val (φ s) 0 = (s : ℝ) := by
    intro s
    have := khom.apply_symm_apply s
    rw [hkhom_apply] at this
    exact congrArg Subtype.val this
  have hφc : Continuous φ := khom.symm.continuous
  have hφs : Function.Surjective φ := khom.symm.surjective
  have hφm : Monotone φ := by
    intro s t hst
    by_contra hcon
    have hlt : φ t < φ s := lt_of_not_ge hcon
    have hlt2 := hk hlt
    simp only [hφk] at hlt2
    exact absurd hst (not_le.mpr hlt2)
  -- the roof height, as a globally continuous function on the line
  set g : ℝ → ℝ := fun s ↦ γ.val (φ (Set.projIcc c d hcd.le s)) 1 with hgdef
  have hgc : Continuous g := hγ1.comp (hφc.comp continuous_projIcc)
  have hgnonneg : ∀ s, 0 ≤ g s := fun s ↦ hh _
  have hheight : ∀ s ∈ Set.Icc c d, monotoneRoofHeight hab γ s = g s := by
    intro s hs
    have hex : ∃ t : Set.Icc a b, γ.val t 0 = s := ⟨φ ⟨s, hs⟩, hφk ⟨s, hs⟩⟩
    have hinv := @Function.invFun_eq _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s hex
    have hpt : @Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s = φ ⟨s, hs⟩ :=
      hk.injective (by simpa using hinv.trans (hφk ⟨s, hs⟩).symm)
    change γ.val (@Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s) 1 = g s
    rw [hpt]
    simp [hgdef, Set.projIcc_of_mem _ hs]
  -- the roof region is the closed subgraph of `g` over `[c, d]`
  have hregion : monotoneRoofRegion hab γ =
      {p : Point | p 0 ∈ Set.Icc c d ∧
        p 1 ∈ Set.Icc ((fun _ : ℝ ↦ (0 : ℝ)) (p 0)) (g (p 0))} := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, by rwa [hheight (p 0) ⟨h1, h2⟩] at h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, by rwa [hheight (p 0) ⟨h1, h2⟩]⟩
  -- the planar volume of a closed vertical subgraph
  have hvolVertical : ∀ (f₀ g₀ : ℝ → ℝ) (S : Set ℝ), Measurable f₀ → Measurable g₀ →
      MeasurableSet S → MeasureTheory.IntegrableOn f₀ S → MeasureTheory.IntegrableOn g₀ S →
      (∀ x ∈ S, f₀ x ≤ g₀ x) →
      MeasureTheory.volume {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        ENNReal.ofReal (∫ x in S, (g₀ - f₀) x) := by
    intro f₀ g₀ S hf hg hS hfi hgi hfg
    have hT : MeasurableSet {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} :=
      measurableSet_region_between_cc hf hg hS
    have hpre : {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        (fun p : Point ↦ (p 0, p 1)) ⁻¹'
          {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} := rfl
    rw [hpre, EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
      hT.nullMeasurableSet]
    rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hS]
    change (MeasureTheory.volume.prod MeasureTheory.volume) (regionBetween f₀ g₀ S) = _
    rw [volume_regionBetween_eq_integral hfi hgi hS hfg]
  have hgint : MeasureTheory.IntegrableOn g (Set.Icc c d) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hIcc : (∫ x in Set.Icc c d, g x) = ∫ s in c..d, g s := by
    rw [intervalIntegral.integral_of_le hcd.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have harea : ClassicalResults.area (monotoneRoofRegion hab γ) = ∫ s in c..d, g s := by
    rw [ClassicalResults.area, hregion,
      hvolVertical (fun _ ↦ 0) g (Set.Icc c d) measurable_const hgc.measurable
        measurableSet_Icc (MeasureTheory.integrableOn_zero) hgint
        (fun x _ ↦ hgnonneg x)]
    rw [ENNReal.toReal_ofReal]
    · simp only [Pi.sub_apply, sub_zero]
      exact hIcc
    · exact MeasureTheory.integral_nonneg (fun x ↦ by simp [hgnonneg x])
  -- the two coordinate Stieltjes drivers
  have hBVext : ∀ {u v : ℝ} (F G : RightContinuousIntervalBV u v),
      F.toFun = G.toFun → F = G := by
    intro u v F G hFG
    cases F
    cases G
    simp only at hFG
    subst hFG
    rfl
  set K := continuousBVCoordinate γ 0 with hKdef
  set H := continuousBVCoordinate γ 1 with hHdef
  have hKcont : Continuous K.toFun := hγ0
  have hHcont : Continuous H.toFun := hγ1
  -- the identity driver on `[c, d]`, with Lebesgue density one
  obtain ⟨Q, hQfun, hQdens⟩ := exists_intervalBV_of_hasDerivAt hcd.le (fun x ↦ x)
    (fun _ ↦ (1 : ℝ)) (fun t ↦ hasDerivAt_id t) continuous_const
  have hstieltjes : intervalStieltjesIntegral K H.toFun Set.univ =
      intervalStieltjesIntegral Q (H.toFun ∘ φ) Set.univ := by
    rw [intervalStieltjesIntegral_comp_monotone_surjective hab.le hcd.le K hKcont
      H.toFun hHcont φ hφc hφm hφs]
    congr 1
    apply hBVext
    funext s
    change γ.val (φ s) 0 = Q.toFun s
    rw [hQfun s, hφk s]
  have hroofint : intervalStieltjesIntegral K H.toFun Set.univ = ∫ s in c..d, g s := by
    rw [hstieltjes, intervalStieltjesIntegral_eq_integral_mul_of_density Q hQdens
      (hHcont.comp hφc) Set.univ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
    have hfun : (fun t : Set.Icc c d ↦ (H.toFun ∘ φ) t * (1 : ℝ)) =
        fun t : Set.Icc c d ↦ g (t : ℝ) := by
      funext t
      simp only [Function.comp_apply, mul_one, hgdef, Set.projIcc_val]
      rfl
    rw [hfun, MeasureTheory.integral_subtype_comap measurableSet_Icc g, hIcc]
  -- integration by parts identifies the curve area with the roof integral
  have hparts := intervalStieltjes_integration_by_parts_of_continuous a b hab.le K H
    hKcont hHcont
  have hends : K.toFun B * H.toFun B - K.toFun A * H.toFun A = 0 := by
    change γ.val B 0 * γ.val B 1 - γ.val A 0 * γ.val A 1 = 0
    rw [ha, hb]
    ring
  have hJγ : curveAreaFunctional γ = -intervalStieltjesIntegral K H.toFun Set.univ := by
    have hform : curveAreaFunctional γ =
        (intervalStieltjesIntegral H K.toFun Set.univ -
          intervalStieltjesIntegral K H.toFun Set.univ) / 2 := rfl
    rw [hform]
    rw [hends] at hparts
    linarith
  have hheightint : (∫ s in c..d, monotoneRoofHeight hab γ s) = ∫ s in c..d, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hheight s (by rwa [Set.uIcc_of_le hcd.le] at hs)
  constructor
  · rw [hJγ, neg_neg, hroofint, harea]
  · exact harea.trans hheightint.symm

theorem monotone_roof_signed_area {a b : ℝ} (hab : a < b)
    (γ : ContinuousBVPaths a b) (hk : StrictMono (fun t ↦ γ.val t 0))
    (hh : ∀ t, 0 ≤ γ.val t 1)
    (ha : γ.val ⟨a, le_rfl, hab.le⟩ 1 = 0)
    (hb : γ.val ⟨b, hab.le, le_rfl⟩ 1 = 0) :
    ∃ Γ : ContinuousBVPaths 0 2, Γ.val = monotoneRoofLoop hab γ ∧
      curveAreaFunctional Γ = ClassicalResults.area (monotoneRoofRegion hab γ) ∧
      ClassicalResults.area (monotoneRoofRegion hab γ) =
        ∫ s in γ.val ⟨a, le_rfl, hab.le⟩ 0..γ.val ⟨b, hab.le, le_rfl⟩ 0,
          monotoneRoofHeight hab γ s := by
  classical
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨harea, hheight⟩ := monotoneRoof_area hab γ hk hh ha hb
  -- the reversed roof, as a path on `[a, b]`
  have hJrev := curveArea_comp_reverse hab.le γ
  set γrev : ContinuousBVPaths a b :=
    ⟨γ.val ∘ Set.Icc.reverse hab.le,
      γ.property.1.comp (Set.Icc.continuous_reverse hab.le), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i)
          (Set.Icc.antitone_reverse hab.le) (Set.Icc.surjective_reverse hab.le)⟩ with hγrevdef
  change curveAreaFunctional γrev = -curveAreaFunctional γ at hJrev
  -- the antitone reparametrization of `[0, 2]` onto `[a, b]`, pausing on `[1, 2]`
  set revmap : Set.Icc (0 : ℝ) 2 → Set.Icc a b :=
    fun s ↦ Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) with hrevmapdef
  have hrevc : Continuous revmap :=
    continuous_projIcc.comp (by fun_prop)
  have hrevanti : Antitone revmap := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hmul := mul_le_mul_of_nonneg_left hst' (sub_nonneg.mpr hab.le)
    change Set.projIcc a b hab.le (b - (b - a) * (t : ℝ)) ≤
      Set.projIcc a b hab.le (b - (b - a) * (s : ℝ))
    exact Set.monotone_projIcc hab.le (by linarith)
  have hrevsurj : Function.Surjective revmap := by
    intro t
    have hba : (0 : ℝ) < b - a := by linarith
    refine ⟨⟨(b - (t : ℝ)) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [t.property.2]) hba.le
    · rw [div_le_iff₀ hba]
      nlinarith [t.property.1]
    · have hval : b - (b - a) * ((b - (t : ℝ)) / (b - a)) = (t : ℝ) := by
        field_simp
        ring
      change Set.projIcc a b hab.le (b - (b - a) * ((b - (t : ℝ)) / (b - a))) = t
      rw [hval, Set.projIcc_val]
  -- the base segment piece, paused on `[0, 1]`
  set w : Point := γ.val B - γ.val A with hwdef
  set ρ : Set.Icc (0 : ℝ) 2 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) with hρdef
  have hρc : Continuous ρ := continuous_projIcc.comp (by fun_prop)
  have hρm : Monotone ρ := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) ≤
      Set.projIcc 0 1 zero_le_one ((t : ℝ) - 1)
    exact Set.monotone_projIcc zero_le_one (by linarith)
  have hρs : Function.Surjective ρ := by
    intro u
    refine ⟨⟨(u : ℝ) + 1, ?_, ?_⟩, ?_⟩
    · linarith [u.property.1]
    · linarith [u.property.2]
    · change Set.projIcc 0 1 zero_le_one ((u : ℝ) + 1 - 1) = u
      rw [show ((u : ℝ) + 1 - 1) = (u : ℝ) from by ring, Set.projIcc_val]
  obtain ⟨Bpath, hBpathval⟩ := continuousBVPaths_comp_monotone_surjective
    (by norm_num : (0 : ℝ) ≤ 1) (lineSegmentBVPath 0 w) ρ hρc hρm hρs
  set Apath : ContinuousBVPaths 0 2 :=
    ⟨γ.val ∘ revmap, γ.property.1.comp hrevc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i) hrevanti
        hrevsurj⟩ with hApathdef
  set Γ : ContinuousBVPaths 0 2 := Apath + Bpath with hΓdef
  have hΓval : Γ.val = monotoneRoofLoop hab γ := by
    funext s
    have h0 : (0 : ℝ) ≤ (s : ℝ) := s.property.1
    have h2 : (s : ℝ) ≤ 2 := s.property.2
    have hval : Γ.val s = γ.val (revmap s) + Path.segment (0 : Point) w (ρ s) := by
      change Apath.val s + Bpath.val s = _
      rw [hBpathval]
      rfl
    rw [hval]
    unfold monotoneRoofLoop
    split_ifs with hs
    · have hrevs : revmap s = ⟨b - (b - a) * (s : ℝ),
          by constructor <;> nlinarith⟩ := by
        change Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        exact Set.projIcc_of_mem hab.le _
      have hρ0 : ρ s = ⟨0, by norm_num⟩ := by
        change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_le_left zero_le_one (by linarith)
      rw [hrevs, hρ0]
      simp
    · rw [not_le] at hs
      have hrevs : revmap s = A := by
        change Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        rw [Set.projIcc_of_le_left hab.le (by nlinarith)]
      have hρ1 : ρ s = ⟨(s : ℝ) - 1, by constructor <;> linarith⟩ := by
        change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_mem zero_le_one _
      rw [hrevs, hρ1]
      change γ.val A + AffineMap.lineMap (0 : Point) w ((s : ℝ) - 1) =
        (2 - (s : ℝ)) • γ.val A + ((s : ℝ) - 1) • γ.val B
      rw [AffineMap.lineMap_apply_module', hwdef]
      module
  -- additivity of the curve area along the cut at `s = 1`
  have hΓ2 : (0 : ℝ) ≤ 2 := by norm_num
  have hba : (0 : ℝ) < b - a := by linarith
  have hconcat : IsPathConcatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
      ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
        ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] :=
    monotoneRoofLoop_concatenation hab γ γrev rfl Γ hΓval
  -- the two pieces and the final assembly
  have hsum := curveArea_concatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
    ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
      ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] hconcat
  have hbase : curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) = 0 := by
    rw [curveAreaFunctional_lineSegmentBVPath, segmentArea, planeCrossProduct, ha, hb]
    ring
  have hJΓ : curveAreaFunctional Γ = -curveAreaFunctional γ := by
    have hΓsum : curveAreaFunctional Γ =
        curveAreaFunctional γrev +
          curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) := by
      rw [show curveAreaFunctional Γ =
        curveAreaFunctional (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData).path from rfl, hsum,
        Fin.sum_univ_two]
      rfl
    rw [hΓsum, hbase, hJrev, add_zero]
  exact ⟨Γ, hΓval, hJΓ.trans harea.symm, hheight⟩

/-- Above a parameter's abscissa, a strictly monotone roof has that parameter's ordinate. -/
theorem monotoneRoofHeight_apply {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) (s : Set.Icc a b) :
    monotoneRoofHeight hab γ (γ.val s 0) = γ.val s 1 := by
  classical
  have hne : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  have hinv : @Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0) = s :=
    hk.injective (@Function.invFun_eq _ _ hne (fun t ↦ γ.val t 0) _ ⟨s, rfl⟩)
  change γ.val (@Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0)) 1 = γ.val s 1
  rw [hinv]

/-- Every abscissa between a roof's endpoints is the abscissa of a roof parameter. -/
theorem exists_eq_monotoneRoof_fst {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    {c : ℝ} (hc : c ∈ Set.Icc (γ.val ⟨a, le_rfl, hab.le⟩ 0) (γ.val ⟨b, hab.le, le_rfl⟩ 0)) :
    ∃ s : Set.Icc a b, γ.val s 0 = c := by
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  exact intermediate_value_univ _ _ ((PiLp.continuous_apply 2 _ 0).comp γ.property.1) hc

/-- The closed region under a strictly monotone roof, described parametrically: it consists of the
points on or below the roof on the vertical line through some roof parameter. -/
theorem monotoneRoofRegion_eq_param {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) :
    monotoneRoofRegion hab γ =
      {p : Point | ∃ s : Set.Icc a b, p 0 = γ.val s 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ γ.val s 1} := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs⟩ := exists_eq_monotoneRoof_fst hab γ ⟨h1, h2⟩
    refine ⟨s, hs.symm, h3, ?_⟩
    rwa [← hs, monotoneRoofHeight_apply hab γ hk s] at h4
  · rintro ⟨s, hs0, hs1, hs2⟩
    refine ⟨?_, ?_, hs1, ?_⟩
    · rw [hs0]
      exact hk.monotone (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ≤ s from s.property.1)
    · rw [hs0]
      exact hk.monotone (show s ≤ (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) from s.property.2)
    · rw [hs0, monotoneRoofHeight_apply hab γ hk s]
      exact hs2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-! # Three-piece monotone roofs

A *three-piece roof* over `[r, l]` is the continuous BV path on `[0, 3]` that runs up a straight
segment from a base point `P` to `f l`, traverses an arc `f` backwards from `l` to `r`, and runs
down a straight segment from `f r` to a base point `Q`.  When the arc's first coordinate is
strictly decreasing and `P`, `Q` lie strictly to the left of `f l` resp. to the right of `f r`, the
resulting path has strictly increasing first coordinate, so it is a monotone roof in the sense of
`MovingSofa.monotoneRoofRegion`.

`area_region_under_strictMono_roof` computes the area of the closed region under such a roof, above
the base line `y = -h` carrying `P` and `Q`, as the signed area of the four-piece closed loop that
bounds it, and `area_region_under_roof_le` compares that area with the areas of a base set and of a
set containing the rest of the open region.
-/

public section

noncomputable section

namespace MovingSofa

/-- A segment path, read as its base point plus a multiple of its displacement. -/
private theorem segment_eq_add_smul (p q : Point) (u : Set.Icc (0 : ℝ) 1) :
    Path.segment p q u = p + (u : ℝ) • (q - p) := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

/-- Clamping to a nondegenerate interval is strictly monotone away from both clamps. -/
private theorem projIcc_lt_projIcc {a b : ℝ} (hab : a < b) {s t : ℝ} (hst : s < t)
    (hs : s < b) (ht : a < t) :
    Set.projIcc a b hab.le s < Set.projIcc a b hab.le t := by
  change max a (min b s) < max a (min b t)
  rw [min_eq_right hs.le, max_eq_right (le_min hab.le ht.le)]
  exact max_lt (lt_min hab ht) (lt_min hs hst)

/-- A convex combination of two numbers bounded by `c` is bounded by `c`. -/
private theorem affine_le_of_le {A B c s : ℝ} (hA : A ≤ c) (hB : B ≤ c)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : A + s * (B - A) ≤ c := by nlinarith

/-- The middle arc's parameter times run over the arc's own interval. -/
theorem mem_Icc_roofArcTime {r l : ℝ} (hrl : r < l) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    l + (s - 1) * (r - l) ∈ Set.Icc r l := by
  refine ⟨?_, ?_⟩
  · have h : (0 : ℝ) ≤ (1 - (s - 1)) * (l - r) :=
      mul_nonneg (by linarith only [hs2]) (by linarith only [hrl])
    linarith only [h]
  · have h : (s - 1) * (r - l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [hs1]) (by linarith only [hrl])
    linarith only [h]

/-- Three pieces — a rising segment into the left end of a strictly decreasing arc, that arc
traversed backwards, and a rising segment out of its right end — assemble into a continuous BV
path on `[0, 3]` whose first coordinate is strictly increasing. -/
theorem exists_strictMono_roof_of_strictAntiOn {r l : ℝ} (hrl : r < l)
    (c : ContinuousBVPaths r l) (f : ℝ → Point) (P Q : Point)
    (hf : ∀ (t : ℝ) (ht : t ∈ Set.Icc r l), c.val ⟨t, ht⟩ = f t)
    (hanti : StrictAntiOn (fun t ↦ f t 0) (Set.Icc r l))
    (hP : P 0 < f l 0) (hQ : f r 0 < Q 0) :
    ∃ γ : ContinuousBVPaths 0 3,
      (∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P)) ∧
        (∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
          γ.val s = f (l + ((s : ℝ) - 1) * (r - l))) ∧
        (∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) →
          γ.val s = f r + ((s : ℝ) - 2) • (Q - f r)) ∧
        StrictMono fun s ↦ γ.val s 0 := by
  have hlr : r - l < 0 := by linarith
  have hcf : ∀ u : Set.Icc r l, c.val u = f (u : ℝ) := fun u ↦ hf u u.property
  have hcanti : ∀ u v : Set.Icc r l, u ≤ v → f (v : ℝ) 0 ≤ f (u : ℝ) 0 := by
    intro u v huv
    rcases eq_or_lt_of_le huv with h | h
    · rw [h]
    · exact (hanti u.property v.property h).le
  -- the antitone reparametrisation of `[0, 3]` onto the arc's domain
  set μ : Set.Icc (0 : ℝ) 3 → Set.Icc r l :=
    fun s ↦ Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) with hμdef
  have hμc : Continuous μ := continuous_projIcc.comp (by fun_prop)
  have hμa : Antitone μ := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := hst
    exact Set.monotone_projIcc hrl.le (by nlinarith)
  have hμs : Function.Surjective μ := by
    intro u
    have hu1 : r ≤ (u : ℝ) := u.property.1
    have hu2 : (u : ℝ) ≤ l := u.property.2
    have hne : l - r ≠ 0 := by linarith
    have hq : 0 ≤ (l - (u : ℝ)) / (l - r) := div_nonneg (by linarith) (by linarith)
    have hq1 : (l - (u : ℝ)) / (l - r) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    refine ⟨⟨1 + (l - (u : ℝ)) / (l - r), by linarith, by linarith⟩, ?_⟩
    change Set.projIcc r l hrl.le (l + (1 + (l - (u : ℝ)) / (l - r) - 1) * (r - l)) = u
    rw [show l + (1 + (l - (u : ℝ)) / (l - r) - 1) * (r - l) = (u : ℝ) by
      field_simp; ring]
    exact Set.projIcc_of_mem hrl.le u.property
  have hμleft : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → μ s = ⟨l, hrl.le, le_rfl⟩ := by
    intro s hs
    change Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) = _
    exact Set.projIcc_of_right_le hrl.le
      (le_add_of_nonneg_right (show (0 : ℝ) ≤ ((s : ℝ) - 1) * (r - l) by nlinarith))
  have hμmid : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      (μ s : ℝ) = l + ((s : ℝ) - 1) * (r - l) := by
    intro s hs1 hs2
    change (Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) : ℝ) = _
    rw [Set.projIcc_of_mem hrl.le ⟨by nlinarith, by nlinarith⟩]
  have hμright : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → μ s = ⟨r, le_rfl, hrl.le⟩ := by
    intro s hs
    change Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) = _
    exact Set.projIcc_of_le_left hrl.le (by nlinarith)
  have hμstrict : ∀ s t : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) < (t : ℝ) →
      (t : ℝ) ≤ 2 → μ t < μ s := by
    intro s t hs hst ht
    exact projIcc_lt_projIcc hrl (by nlinarith) (by nlinarith) (by nlinarith)
  -- the two clamped affine reparametrisations of the side segments
  set ρ₀ : Set.Icc (0 : ℝ) 3 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one (s : ℝ) with hρ₀def
  set ρ₂ : Set.Icc (0 : ℝ) 3 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) with hρ₂def
  have hρ₀c : Continuous ρ₀ := continuous_projIcc.comp (by fun_prop)
  have hρ₂c : Continuous ρ₂ := continuous_projIcc.comp (by fun_prop)
  have hρ₀m : Monotone ρ₀ := fun s t hst ↦ Set.monotone_projIcc zero_le_one hst
  have hρ₂m : Monotone ρ₂ := fun s t hst ↦
    Set.monotone_projIcc zero_le_one (by linarith [show (s : ℝ) ≤ t from hst])
  have hρ₀s : Function.Surjective ρ₀ := fun u ↦
    ⟨⟨(u : ℝ), u.property.1, le_trans u.property.2 (by norm_num)⟩,
      Set.projIcc_of_mem zero_le_one u.property⟩
  have hρ₂s : Function.Surjective ρ₂ := by
    intro u
    refine ⟨⟨(u : ℝ) + 2, by linarith [u.property.1], by linarith [u.property.2]⟩, ?_⟩
    change Set.projIcc 0 1 zero_le_one ((u : ℝ) + 2 - 2) = u
    rw [show (u : ℝ) + 2 - 2 = (u : ℝ) by ring]
    exact Set.projIcc_of_mem zero_le_one u.property
  have hρ₀left : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → (ρ₀ s : ℝ) = (s : ℝ) := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one (s : ℝ) : ℝ) = _
    rw [Set.projIcc_of_mem zero_le_one ⟨s.property.1, hs⟩]
  have hρ₀right : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (ρ₀ s : ℝ) = 1 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one (s : ℝ) : ℝ) = _
    rw [Set.projIcc_of_right_le zero_le_one hs]
  have hρ₂left : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 2 → (ρ₂ s : ℝ) = 0 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) : ℝ) = _
    rw [Set.projIcc_of_le_left zero_le_one (by linarith)]
  have hρ₂right : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → (ρ₂ s : ℝ) = (s : ℝ) - 2 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) : ℝ) = _
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith, by linarith [s.property.2]⟩]
  -- the three summands of the roof
  obtain ⟨A₀, hA₀⟩ := continuousBVPaths_comp_monotone_surjective zero_le_one
    (lineSegmentBVPath P (f l)) ρ₀ hρ₀c hρ₀m hρ₀s
  obtain ⟨A₂, hA₂⟩ := continuousBVPaths_comp_monotone_surjective zero_le_one
    (lineSegmentBVPath 0 (Q - f r)) ρ₂ hρ₂c hρ₂m hρ₂s
  set A₁ : ContinuousBVPaths 0 3 :=
    ⟨c.val ∘ μ, c.property.1.comp hμc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hrl.le (c.property.2 i) hμa hμs⟩
    with hA₁def
  have hval : ∀ s : Set.Icc (0 : ℝ) 3,
      (A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂).val s =
        (P + (ρ₀ s : ℝ) • (f l - P)) + (f (μ s : ℝ) - f l) +
          (ρ₂ s : ℝ) • (Q - f r) := by
    intro s
    change A₀.val s + (A₁.val s - f l) + A₂.val s = _
    rw [hA₀, hA₂]
    change Path.segment P (f l) (ρ₀ s) + (c.val (μ s) - f l) +
      Path.segment (0 : Point) (Q - f r) (ρ₂ s) = _
    rw [segment_eq_add_smul, segment_eq_add_smul, hcf (μ s)]
    simp
  have hcoord : ∀ s : Set.Icc (0 : ℝ) 3,
      (A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂).val s 0 =
        P 0 + (ρ₀ s : ℝ) * (f l 0 - P 0) + (f (μ s : ℝ) 0 - f l 0) +
          (ρ₂ s : ℝ) * (Q 0 - f r 0) := by
    intro s
    rw [hval s]
    simp
  refine ⟨A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hval s, hρ₀left s hs, hμleft s hs]
    simp [hρ₂left s (by linarith)]
  · intro s hs1 hs2
    rw [hval s, hρ₀right s hs1, hμmid s hs1 hs2, hρ₂left s hs2]
    simp
  · intro s hs
    rw [hval s, hρ₀right s (by linarith), hμright s hs, hρ₂right s hs]
    simp
  · intro s t hst
    have hst' : (s : ℝ) < (t : ℝ) := hst
    have hd0 : (0 : ℝ) < f l 0 - P 0 := by linarith
    have hd2 : (0 : ℝ) < Q 0 - f r 0 := by linarith
    have m0 : (ρ₀ s : ℝ) * (f l 0 - P 0) ≤ (ρ₀ t : ℝ) * (f l 0 - P 0) :=
      mul_le_mul_of_nonneg_right (hρ₀m hst.le) hd0.le
    have m2 : (ρ₂ s : ℝ) * (Q 0 - f r 0) ≤ (ρ₂ t : ℝ) * (Q 0 - f r 0) :=
      mul_le_mul_of_nonneg_right (hρ₂m hst.le) hd2.le
    have m1 : f (μ s : ℝ) 0 ≤ f (μ t : ℝ) 0 := hcanti (μ t) (μ s) (hμa hst.le)
    simp only [hcoord]
    rcases lt_or_ge (s : ℝ) 1 with hc | hc
    · have hs0 : (ρ₀ s : ℝ) < (ρ₀ t : ℝ) :=
        projIcc_lt_projIcc zero_lt_one hst' hc (by linarith [s.property.1])
      have := mul_lt_mul_of_pos_right hs0 hd0
      linarith only [this, m1, m2]
    · rcases le_or_gt (t : ℝ) 2 with hc2 | hc2
      · have hmid : f (μ s : ℝ) 0 < f (μ t : ℝ) 0 :=
          hanti (μ t).property (μ s).property (hμstrict s t hc hst' hc2)
        linarith only [hmid, m0, m2]
      · have hs2 : (ρ₂ s : ℝ) < (ρ₂ t : ℝ) :=
          projIcc_lt_projIcc zero_lt_one (by linarith)
            (by linarith [t.property.2]) (by linarith)
        have := mul_lt_mul_of_pos_right hs2 hd2
        linarith only [this, m0, m1]

/-- A linear functional bounded at the two base corners of a three-piece roof and along its
middle arc is bounded along the whole roof. -/
theorem le_of_threePieceRoof {r l α β cc : ℝ} (hrl : r < l) (f : ℝ → Point) (P Q : Point)
    (γ : ContinuousBVPaths 0 3)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = f (l + ((s : ℝ) - 1) * (r - l)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → γ.val s = f r + ((s : ℝ) - 2) • (Q - f r))
    (hP : α * P 0 + β * P 1 ≤ cc) (hQ : α * Q 0 + β * Q 1 ≤ cc)
    (harc : ∀ t ∈ Set.Icc r l, α * f t 0 + β * f t 1 ≤ cc) (s : Set.Icc (0 : ℝ) 3) :
    α * γ.val s 0 + β * γ.val s 1 ≤ cc := by
  have hcoord : ∀ (p q : Point) (u : ℝ) (i : Fin 2),
      (p + u • (q - p)) i = p i + u * (q i - p i) := fun _ _ _ _ ↦ by simp
  rcases le_or_gt (s : ℝ) 1 with hs | hs
  · rw [hγ0 s hs, hcoord, hcoord]
    have hmid := affine_le_of_le (A := α * P 0 + β * P 1) (B := α * f l 0 + β * f l 1)
      (c := cc) (s := (s : ℝ)) hP (harc l ⟨hrl.le, le_rfl⟩) s.property.1 hs
    calc α * (P 0 + (s : ℝ) * (f l 0 - P 0)) + β * (P 1 + (s : ℝ) * (f l 1 - P 1))
        = (α * P 0 + β * P 1) +
          (s : ℝ) * ((α * f l 0 + β * f l 1) - (α * P 0 + β * P 1)) := by ring
      _ ≤ cc := hmid
  · rcases le_or_gt (s : ℝ) 2 with hs2 | hs2
    · rw [hγ1 s hs.le hs2]
      exact harc _ (mem_Icc_roofArcTime hrl hs.le hs2)
    · rw [hγ2 s hs2.le, hcoord, hcoord]
      have hmid := affine_le_of_le (A := α * f r 0 + β * f r 1) (B := α * Q 0 + β * Q 1)
        (c := cc) (s := (s : ℝ) - 2) (harc r ⟨le_rfl, hrl.le⟩) hQ
        (by linarith only [hs2]) (by linarith only [s.property.2])
      calc α * (f r 0 + ((s : ℝ) - 2) * (Q 0 - f r 0)) +
            β * (f r 1 + ((s : ℝ) - 2) * (Q 1 - f r 1))
          = (α * f r 0 + β * f r 1) +
            ((s : ℝ) - 2) * ((α * Q 0 + β * Q 1) - (α * f r 0 + β * f r 1)) := by ring
        _ ≤ cc := hmid

/-- The closed region under a strictly monotone three-piece roof whose two side segments begin
and end on the line `y = -h` has area equal to the signed area of the four-piece loop that
bounds it: the base segment, the two side segments and the arc. -/
theorem area_region_under_strictMono_roof {r l h : ℝ} (hrl : r < l)
    (c : ContinuousBVPaths r l) (f : ℝ → Point) (P Q : Point) (γ : ContinuousBVPaths 0 3)
    (hf : ∀ (t : ℝ) (ht : t ∈ Set.Icc r l), c.val ⟨t, ht⟩ = f t)
    (hP : P 1 = -h) (hQ : Q 1 = -h)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = f (l + ((s : ℝ) - 1) * (r - l)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → γ.val s = f r + ((s : ℝ) - 2) • (Q - f r))
    (hγmono : StrictMono fun s ↦ γ.val s 0)
    (hγlow : ∀ s : Set.Icc (0 : ℝ) 3, -h ≤ γ.val s 1) :
    ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      segmentArea Q (f r) + curveAreaFunctional c + segmentArea (f l) P + segmentArea P Q := by
  have h03 : (0 : ℝ) < 3 := by norm_num
  have h02 : (0 : ℝ) ≤ 2 := by norm_num
  have hadd : ∀ (x y : Point) (i : Fin 2), (x + y) i = x i + y i := fun _ _ _ ↦ by simp
  have hcf : ∀ u : Set.Icc r l, c.val u = f (u : ℝ) := fun u ↦ hf u u.property
  -- the upward shift taking the base line to the horizontal axis
  set v : Point := !₂[0, h] with hvdef
  have hv0 : v 0 = 0 := rfl
  have hv1 : v 1 = h := rfl
  set γ' : ContinuousBVPaths 0 3 := γ + constBVPath 0 3 v with hγ'def
  have hγ'val : ∀ s, γ'.val s = γ.val s + v := fun _ ↦ rfl
  have hγ'coord : ∀ (s : Set.Icc (0 : ℝ) 3) (i : Fin 2), γ'.val s i = γ.val s i + v i := by
    intro s i
    rw [hγ'val s, hadd]
  have hγ'mono : StrictMono fun s ↦ γ'.val s 0 := by
    intro s t hst
    have hm : γ.val s 0 < γ.val t 0 := hγmono hst
    change γ'.val s 0 < γ'.val t 0
    rw [hγ'coord s 0, hγ'coord t 0]
    linarith only [hm]
  have hγstart : γ.val ⟨0, le_rfl, h03.le⟩ = P := by
    rw [hγ0 _ (by norm_num)]
    simp
  have hγend : γ.val ⟨3, h03.le, le_rfl⟩ = Q := by
    rw [hγ2 _ (by norm_num)]
    norm_num
  have hγ'zero : γ'.val ⟨0, le_rfl, h03.le⟩ 1 = 0 := by
    rw [hγ'coord, hγstart, hP, hv1]
    ring
  have hγ'three : γ'.val ⟨3, h03.le, le_rfl⟩ 1 = 0 := by
    rw [hγ'coord, hγend, hQ, hv1]
    ring
  have hγ'nonneg : ∀ s, 0 ≤ γ'.val s 1 := by
    intro s
    rw [hγ'coord, hv1]
    linarith only [hγlow s]
  -- the region is the roof region of the shifted path, translated back down
  have hregion : {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      (fun q : Point ↦ q + v) ⁻¹' monotoneRoofRegion h03 γ' := by
    rw [monotoneRoofRegion_eq_param h03 γ' hγ'mono]
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hadd, hγ'coord, hv0, hv1, add_zero]
    constructor
    · rintro ⟨s, e1, e2, e3⟩
      exact ⟨s, e1, by linarith only [e2], by linarith only [e3]⟩
    · rintro ⟨s, e1, e2, e3⟩
      exact ⟨s, e1, by linarith only [e2], by linarith only [e3]⟩
  have harea : ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      ClassicalResults.area (monotoneRoofRegion h03 γ') := by
    rw [ClassicalResults.area, ClassicalResults.area, hregion,
      MeasureTheory.measure_preimage_add_right]
  obtain ⟨Γ, hΓval, hΓarea, -⟩ :=
    monotone_roof_signed_area h03 γ' hγ'mono hγ'nonneg hγ'zero hγ'three
  -- reading the closed loop on its two branches
  have hloopLow : ∀ (t : Set.Icc (0 : ℝ) 2) (u : Set.Icc (0 : ℝ) 3), (t : ℝ) ≤ 1 →
      (u : ℝ) = 3 - 3 * (t : ℝ) → Γ.val t = γ.val u + v := by
    intro t u ht hu
    rw [hΓval]
    unfold monotoneRoofLoop
    split_ifs with hs
    · rw [hγ'val]
      exact congrArg (fun z : Point ↦ z + v) (congrArg (fun z ↦ γ.val z)
        (Subtype.ext (by rw [hu]; ring)))
    · exact absurd ht hs
  have hloopHigh : ∀ t : Set.Icc (0 : ℝ) 2, 1 ≤ (t : ℝ) →
      Γ.val t = (2 - (t : ℝ)) • (P + v) + ((t : ℝ) - 1) • (Q + v) := by
    intro t ht
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [hloopLow t ⟨0, le_rfl, h03.le⟩ (le_of_eq heq.symm) (by rw [← heq]; norm_num),
        hγstart, ← heq]
      module
    · rw [hΓval]
      unfold monotoneRoofLoop
      split_ifs with hs
      · exact absurd hs (not_le.mpr hlt)
      · simp only [hγ'val, hγstart, hγend]
  -- the four cuts of the loop's parameter interval
  set e0 : Set.Icc (0 : ℝ) 2 := ⟨0, le_rfl, h02⟩ with he0
  set e1 : Set.Icc (0 : ℝ) 2 := ⟨1 / 3, by norm_num⟩ with he1
  set e2 : Set.Icc (0 : ℝ) 2 := ⟨2 / 3, by norm_num⟩ with he2
  set e3 : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩ with he3
  set e4 : Set.Icc (0 : ℝ) 2 := ⟨2, h02, le_rfl⟩ with he4
  have hle01 : e0 ≤ e1 := by change (0 : ℝ) ≤ 1 / 3; norm_num
  have hle12 : e1 ≤ e2 := by change (1 : ℝ) / 3 ≤ 2 / 3; norm_num
  have hle23 : e2 ≤ e3 := by change (2 : ℝ) / 3 ≤ 1; norm_num
  have hle34 : e3 ≤ e4 := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit : curveAreaFunctional Γ =
      curveAreaFunctional (ContinuousBVPaths.restrict Γ e0 e1 hle01) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e1 e2 hle12) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e2 e3 hle23) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e3 e4 hle34) := by
    have hcm : Monotone (![e0, e1, e2, e3, e4] : Fin 5 → Set.Icc (0 : ℝ) 2) := by
      refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
      fin_cases i
      · exact hle01
      · exact hle12
      · exact hle23
      · exact hle34
    have hsum := curveArea_eq_sum_restrict Γ ![e0, e1, e2, e3, e4] hcm rfl rfl
    rw [Fin.sum_univ_four] at hsum
    exact hsum
  -- each restriction, read off through an affine reparametrisation
  have hres : ∀ (u1 u2 : Set.Icc (0 : ℝ) 2) (hu : u1 ≤ u2)
      (t : Set.Icc ((u1 : ℝ)) ((u2 : ℝ))) (wp : Set.Icc (0 : ℝ) 2), (wp : ℝ) = (t : ℝ) →
      (ContinuousBVPaths.restrict Γ u1 u2 hu).val t = Γ.val wp :=
    fun _ _ _ _ _ hw ↦ congrArg (fun z ↦ Γ.val z) (Subtype.ext hw.symm)
  have hseg : ∀ (u1 u2 : Set.Icc (0 : ℝ) 2) (hu : u1 ≤ u2) (p q : Point)
      (φ : Set.Icc ((u1 : ℝ)) ((u2 : ℝ)) → Set.Icc (0 : ℝ) 1), Continuous φ → Monotone φ →
      Function.Surjective φ →
      (ContinuousBVPaths.restrict Γ u1 u2 hu).val = (lineSegmentBVPath p q).val ∘ φ →
      curveAreaFunctional (ContinuousBVPaths.restrict Γ u1 u2 hu) = segmentArea p q := by
    intro u1 u2 hu p q φ hφc hφm hφs hcomp
    rw [curveAreaFunctional_eq_of_comp_monotone_surjective zero_le_one hu
        (lineSegmentBVPath p q) _ φ hφc hφm hφs hcomp,
      curveAreaFunctional_lineSegmentBVPath]
  obtain ⟨φ₁, hφ₁c, hφ₁m, hφ₁s, hφ₁v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e0 : ℝ)) < ((e1 : ℝ)) by
      change (0 : ℝ) < 1 / 3; norm_num) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨φ₂, hφ₂c, hφ₂m, hφ₂s, hφ₂v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e1 : ℝ)) < ((e2 : ℝ)) by
      change (1 : ℝ) / 3 < 2 / 3; norm_num) hrl
  obtain ⟨φ₃, hφ₃c, hφ₃m, hφ₃s, hφ₃v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e2 : ℝ)) < ((e3 : ℝ)) by
      change (2 : ℝ) / 3 < 1; norm_num) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨φ₄, hφ₄c, hφ₄m, hφ₄s, hφ₄v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e3 : ℝ)) < ((e4 : ℝ)) by
      change (1 : ℝ) < 2; norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hp1 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e0 e1 hle01) =
      segmentArea (Q + v) (f r + v) := by
    refine hseg e0 e1 hle01 _ _ φ₁ hφ₁c hφ₁m hφ₁s ?_
    funext t
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 / 3 := t.property.2
    rw [hres e0 e1 hle01 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ (by linarith) rfl,
      hγ2 _ (by change (2 : ℝ) ≤ 3 - 3 * (t : ℝ); linarith)]
    change _ = Path.segment (Q + v) (f r + v) (φ₁ t)
    rw [segment_eq_add_smul, hφ₁v t,
      show (0 : ℝ) + ((t : ℝ) - ((e0 : ℝ))) / (((e1 : ℝ)) - ((e0 : ℝ))) * (1 - 0) =
        3 * (t : ℝ) from by change (0 : ℝ) + ((t : ℝ) - 0) / (1 / 3 - 0) * (1 - 0) = _; ring,
      show ((3 : ℝ) - 3 * (t : ℝ)) - 2 = 1 - 3 * (t : ℝ) from by ring]
    module
  have hp2 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e1 e2 hle12) =
      curveAreaFunctional (c + constBVPath r l v) := by
    refine curveAreaFunctional_eq_of_comp_monotone_surjective hrl.le hle12
      (c + constBVPath r l v) _ φ₂ hφ₂c hφ₂m hφ₂s ?_
    funext t
    have ht0 : (1 : ℝ) / 3 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 2 / 3 := t.property.2
    rw [hres e1 e2 hle12 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ (by linarith) rfl,
      hγ1 _ (by change (1 : ℝ) ≤ 3 - 3 * (t : ℝ); linarith)
        (by change (3 : ℝ) - 3 * (t : ℝ) ≤ 2; linarith),
      show l + (((3 : ℝ) - 3 * (t : ℝ)) - 1) * (r - l) = ((φ₂ t : ℝ)) from by
        rw [hφ₂v t]
        change _ = r + ((t : ℝ) - 1 / 3) / (2 / 3 - 1 / 3) * (l - r)
        ring]
    change f ((φ₂ t : ℝ)) + v = c.val (φ₂ t) + v
    rw [hcf (φ₂ t)]
  have hp3 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e2 e3 hle23) =
      segmentArea (f l + v) (P + v) := by
    refine hseg e2 e3 hle23 _ _ φ₃ hφ₃c hφ₃m hφ₃s ?_
    funext t
    have ht0 : (2 : ℝ) / 3 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    rw [hres e2 e3 hle23 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ ht1 rfl,
      hγ0 _ (by change (3 : ℝ) - 3 * (t : ℝ) ≤ 1; linarith)]
    change _ = Path.segment (f l + v) (P + v) (φ₃ t)
    rw [segment_eq_add_smul, hφ₃v t,
      show (0 : ℝ) + ((t : ℝ) - ((e2 : ℝ))) / (((e3 : ℝ)) - ((e2 : ℝ))) * (1 - 0) =
        3 * (t : ℝ) - 2 from by
          change (0 : ℝ) + ((t : ℝ) - 2 / 3) / (1 - 2 / 3) * (1 - 0) = _
          ring]
    module
  have hp4 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e3 e4 hle34) =
      segmentArea (P + v) (Q + v) := by
    refine hseg e3 e4 hle34 _ _ φ₄ hφ₄c hφ₄m hφ₄s ?_
    funext t
    have ht0 : (1 : ℝ) ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 2 := t.property.2
    rw [hres e3 e4 hle34 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopHigh _ ht0]
    change _ = Path.segment (P + v) (Q + v) (φ₄ t)
    rw [segment_eq_add_smul, hφ₄v t,
      show (0 : ℝ) + ((t : ℝ) - ((e3 : ℝ))) / (((e4 : ℝ)) - ((e3 : ℝ))) * (1 - 0) =
        (t : ℝ) - 1 from by change (0 : ℝ) + ((t : ℝ) - 1) / (2 - 1) * (1 - 0) = _; ring]
    module
  -- assembling the four signed areas and undoing the shift
  rw [harea, ← hΓarea, hsplit, hp1, hp2, hp3, hp4,
    curveAreaFunctional_add_constBVPath hrl.le c v, hcf ⟨l, hrl.le, le_rfl⟩,
    hcf ⟨r, le_rfl, hrl.le⟩]
  simp only [segmentArea_add_right, hv0, hv1]
  ring

/-- Comparing the closed region under a strictly monotone roof with a base set that absorbs the
region's bottom edge and a set that absorbs the rest of the open region: the roof itself is a
null set, so the three areas satisfy the expected inequality. -/
theorem area_region_under_roof_le {h : ℝ} (γ : ContinuousBVPaths 0 3)
    (hγmono : StrictMono fun s ↦ γ.val s 0) (R T : Set Point)
    (hRfin : MeasureTheory.volume R ≠ ⊤) (hTfin : MeasureTheory.volume T ≠ ⊤)
    (hbase : ∀ p : Point, (∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0) → p 1 = -h → p ∈ R)
    (hincl : {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1} \ R ⊆ T) :
    ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} ≤
      ClassicalResults.area R + ClassicalResults.area T := by
  have h03 : (0 : ℝ) < 3 := by norm_num
  set Pu : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1}
    with hPudef
  set Pu' : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1}
    with hPu'def
  have hsplit : Pu \ R ⊆ (Pu' \ R) ∪ Set.range γ.val := by
    rintro p ⟨hpP, hpR⟩
    obtain ⟨s, hs0, hs1, hs2⟩ := hpP
    rcases eq_or_lt_of_le hs1 with heq | hlt
    · exact absurd (hbase p ⟨s, hs0⟩ heq.symm) hpR
    · rcases eq_or_lt_of_le hs2 with heq2 | hlt2
      · refine Or.inr ⟨s, ?_⟩
        ext i
        fin_cases i
        · exact hs0.symm
        · exact heq2.symm
      · exact Or.inl ⟨⟨s, hs0, hlt, hlt2⟩, hpR⟩
  have hnull : MeasureTheory.volume (Set.range γ.val) = 0 := by
    refine ContinuousBVPaths.volume_range_eq_zero_of_injOn h03.le γ ?_
    intro a _ b _ hab
    exact hγmono.injective (congrArg (fun p : Point ↦ p 0) hab)
  have hkey : MeasureTheory.volume Pu ≤ MeasureTheory.volume R + MeasureTheory.volume T := by
    refine le_trans (MeasureTheory.measure_le_inter_add_sdiff _ _ R) ?_
    refine add_le_add (MeasureTheory.measure_mono Set.inter_subset_right) ?_
    refine le_trans (MeasureTheory.measure_mono hsplit) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    rw [hnull, add_zero]
    exact MeasureTheory.measure_mono hincl
  have hPufin : MeasureTheory.volume Pu ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hRfin, hTfin⟩) hkey
  simp only [ClassicalResults.area]
  rw [← ENNReal.toReal_add hRfin hTfin]
  exact (ENNReal.toReal_le_toReal hPufin (ENNReal.add_ne_top.mpr ⟨hRfin, hTfin⟩)).mpr hkey

end MovingSofa

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Convex.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Convex.BoundaryVariation`.
* `Convex.BoundaryApproximation`.
* `Convex.Combination`.
* `Convex.AreaSuperlevel`.
* `Convex.CombinationPullback`.
* `Convex.ContactFanArea`.
* `Convex.ExposedFaces`.
* `Convex.Limits`.
* `Convex.SupportEmbedding`.
* `Convex.CombinationProperties`.
* `Convex.EnvelopeFace`.
* `Convex.Space`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Boundary Variation
-/

public section

noncomputable section

namespace MovingSofa

private theorem tangent_cone_decomposition (p : Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    p = (inner ℝ p (normalVector (t : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (s : Real.Angle) +
      (-inner ℝ p (normalVector (s : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;>
    simp only [normalVector, tangentVector, frame, PiLp.inner_apply,
      Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
      Real.Angle.sin_coe, Real.inner_apply] <;>
    norm_num <;> field_simp [h] <;> rw [Real.sin_sub] <;> ring

private theorem exists_nonneg_tangent_coefficients (p q : Point) (s t : ℝ)
    (hst : s < t) (hts : t < s + Real.pi)
    (hs : inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) ≤
      inner ℝ q (normalVector (t : Real.Angle))) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      q - p = α • tangentVector (s : Real.Angle) +
        β • tangentVector (t : Real.Angle) := by
  have hsin : 0 < Real.sin (t - s) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith)
  refine ⟨inner ℝ (q - p) (normalVector (t : Real.Angle)) / Real.sin (t - s),
    -inner ℝ (q - p) (normalVector (s : Real.Angle)) / Real.sin (t - s),
    ?_, ?_, tangent_cone_decomposition (q - p) s t hsin.ne'⟩
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    exact sub_nonneg.mpr ht
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    linarith

private theorem inner_tangent_normal (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) =
      -Real.sin (r - a) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.sin_sub]
  ring

private theorem inner_tangent_tangent (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) =
      Real.cos (r - a) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

private theorem tangent_projection_signs {a r : ℝ}
    (hr : r ∈ Set.Icc a (a + Real.pi / 2)) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) ≤ 0 ∧
    0 ≤ inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) := by
  rw [inner_tangent_normal, inner_tangent_tangent]
  constructor
  · exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1])
      (by linarith [hr.2, Real.pi_pos]))
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1, Real.pi_pos],
      by linarith [hr.2]⟩

private theorem support_selection_projection_order (K : ConvexBody Point)
    {a s t : ℝ} (hs : s ∈ Set.Icc a (a + Real.pi / 2))
    (ht : t ∈ Set.Icc a (a + Real.pi / 2)) (hst : s < t)
    {p q : Point} (hp : p ∈ exposedEdge K (s : Real.Angle))
    (hq : q ∈ exposedEdge K (t : Real.Angle)) :
    inner ℝ q (normalVector (a : Real.Angle)) ≤
        inner ℝ p (normalVector (a : Real.Angle)) ∧
      inner ℝ p (tangentVector (a : Real.Angle)) ≤
        inner ℝ q (tangentVector (a : Real.Angle)) := by
  have hsp := inner_le_supportValue K hq.1 (s : Real.Angle)
  have htp := inner_le_supportValue K hp.1 (t : Real.Angle)
  rw [← hp.2] at hsp
  rw [← hq.2] at htp
  obtain ⟨α, β, hα, hβ, hrepr⟩ := exists_nonneg_tangent_coefficients p q s t hst
    (by linarith [hs.1, ht.2, Real.pi_pos]) hsp htp
  have hsigns := tangent_projection_signs hs
  have hsignt := tangent_projection_signs ht
  constructor
  · have h := congrArg (fun p ↦ inner ℝ p (normalVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonpos_of_nonneg_of_nonpos hα hsigns.1,
      mul_nonpos_of_nonneg_of_nonpos hβ hsignt.1]
  · have h := congrArg (fun p ↦ inner ℝ p (tangentVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonneg hα hsigns.2, mul_nonneg hβ hsignt.2]

private theorem support_selection_boundedVariationOn_quarter (K : ConvexBody Point)
    (f : ℝ → Point) (a : ℝ)
    (hf : ∀ t ∈ Set.Icc a (a + Real.pi / 2), f t ∈ exposedEdge K (t : Real.Angle)) :
    BoundedVariationOn f (Set.Icc a (a + Real.pi / 2)) := by
  let x : ℝ → ℝ := fun t ↦ -inner ℝ (f t) (normalVector (a : Real.Angle))
  let y : ℝ → ℝ := fun t ↦ inner ℝ (f t) (tangentVector (a : Real.Angle))
  have hx : MonotoneOn x (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact neg_le_neg (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).1
  have hy : MonotoneOn y (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).2
  have ha : a ≤ a + Real.pi / 2 := by linarith [Real.pi_pos]
  have hxv : BoundedVariationOn x (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hx.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  have hyv : BoundedVariationOn y (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hy.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  let U := ContinuousLinearMap.toSpanSingleton ℝ (-normalVector (a : Real.Angle))
  let V := ContinuousLinearMap.toSpanSingleton ℝ (tangentVector (a : Real.Angle))
  have hsum := (U.lipschitzWith.comp_boundedVariationOn hxv).add
    (V.lipschitzWith.comp_boundedVariationOn hyv)
  have heq : (U ∘ x) + (V ∘ y) = f := by
    funext t
    simpa [U, V, x, y, Function.comp_def] using
      inner_normalVector_smul_add_inner_tangentVector_smul (f t) (a : Real.Angle)
  rwa [heq] at hsum

private theorem boundedVariationOn_Icc_trans {f : ℝ → Point} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : BoundedVariationOn f (Set.Icc a b))
    (hg : BoundedVariationOn f (Set.Icc b c)) :
    BoundedVariationOn f (Set.Icc a c) := by
  have h := eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at h
  change eVariationOn f (Set.Icc a c) ≠ ⊤
  rw [← h]
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

/-- Every selection of points from the exposed edges has bounded variation on bounded intervals. -/
theorem boundedVariationOn_of_mem_exposedEdge (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by
  have hN : ∀ n : ℕ, BoundedVariationOn f (Set.Icc a (a + n * (Real.pi / 2))) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge (le_refl a))
    | succ n ih =>
      have hn : a ≤ a + n * (Real.pi / 2) :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (by positivity))
      have hn' : a + n * (Real.pi / 2) ≤ a + (n + 1) * (Real.pi / 2) := by
        linarith [Real.pi_pos]
      have hpiece := support_selection_boundedVariationOn_quarter K f
        (a + n * (Real.pi / 2)) (fun t _ ↦ hf t)
      have hstep := boundedVariationOn_Icc_trans hn hn' ih
        (by convert hpiece using 1; congr 1; ring)
      simpa only [Nat.cast_add, Nat.cast_one] using hstep
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (Real.pi / 2))
  have hb : b ≤ a + n * (Real.pi / 2) := by
    have h := (div_lt_iff₀ (by positivity : 0 < Real.pi / 2)).mp hn
    linarith
  exact (hN n).mono (Set.Icc_subset_Icc_right hb)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Boundary Approximation
-/

public section

noncomputable section

namespace MovingSofa

theorem positiveVertex_boundedVariation (K : ConvexBody Point) (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1) (Set.Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)
  · exact boundedVariationOn_of_mem_exposedEdge K _ (fun t ↦ edgeVertices_fst_mem K _) a b

private theorem exists_facePreserving_polygon (K : ConvexBody Point)
    (F : Finset Real.Angle) {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Finset Point) (P : ConvexBody Point),
      V.Nonempty ∧
      (P : Set Point) = convexHull ℝ (V : Set Point) ∧
      (P : Set Point) ⊆ (K : Set Point) ∧
      (∀ t ∈ F, exposedEdge P t = exposedEdge K t) ∧
      Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
  obtain ⟨S, hSK, hSfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded K.isCompact.totallyBounded ε hε
  let N : Finset Point := hSfinite.toFinset
  let E : Finset Point :=
    F.image (fun t ↦ (edgeVertices K t).1) ∪
      F.image (fun t ↦ (edgeVertices K t).2)
  let p₀ : Point := Classical.choose K.nonempty
  let V : Finset Point := insert p₀ (N ∪ E)
  have hp₀ : p₀ ∈ K := Classical.choose_spec K.nonempty
  have hVnonempty : V.Nonempty := by
    exact ⟨p₀, Finset.mem_insert_self p₀ _⟩
  have hVsubset : (V : Set Point) ⊆ (K : Set Point) := by
    intro p hp
    simp only [V, E, Finset.mem_coe, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp
    rcases hp with rfl | hpN | hpE
    · exact hp₀
    · exact hSK (hSfinite.mem_toFinset.mp hpN)
    · rcases hpE with hpE | hpE
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_fst_mem K t).1
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_snd_mem K t).1
  let P : ConvexBody Point :=
    { carrier := convexHull ℝ (V : Set Point)
      convex' := convex_convexHull ℝ _
      isCompact' := V.finite_toSet.isCompact_convexHull ℝ
      nonempty' := ⟨p₀, subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_insert_self p₀ _))⟩ }
  have hPcarrier : (P : Set Point) = convexHull ℝ (V : Set Point) := rfl
  have hPK : (P : Set Point) ⊆ (K : Set Point) := by
    change convexHull ℝ (V : Set Point) ⊆ (K : Set Point)
    exact convexHull_min hVsubset K.convex
  have hfaces : ∀ t ∈ F, exposedEdge P t = exposedEdge K t := by
    intro t ht
    have hfstV : (edgeVertices K t).1 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩))
    have hsndV : (edgeVertices K t).2 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl⟩))
    have hfstP : (edgeVertices K t).1 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hfstV
    have hsndP : (edgeVertices K t).2 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hsndV
    have hsupport : supportValue P t = supportValue K t := by
      apply le_antisymm
      · apply csSup_le (P.nonempty.image _)
        rintro _ ⟨p, hp, rfl⟩
        exact inner_le_supportValue K (hPK hp) t
      · have h := inner_le_supportValue P hfstP t
        rw [(edgeVertices_fst_mem K t).2] at h
        exact h
    ext p
    constructor
    · intro hp
      exact ⟨hPK hp.1, hp.2.trans hsupport⟩
    · intro hp
      have hpseg : p ∈ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
        rw [← exposedEdge_eq_segment_edgeVertices]
        exact hp
      have hpP : p ∈ P := P.convex.segment_subset hsndP hfstP hpseg
      exact ⟨hpP, hp.2.trans hsupport.symm⟩
  have hdist : Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
    apply Metric.hausdorffDist_le_of_mem_dist hε.le
    · intro p hp
      exact ⟨p, hPK hp, dist_self p ▸ hε.le⟩
    · intro p hp
      have hpcover := hcover hp
      simp only [Set.mem_iUnion, Metric.mem_ball] at hpcover
      obtain ⟨q, hqS, hpq⟩ := hpcover
      have hqN : q ∈ N := hSfinite.mem_toFinset.mpr hqS
      have hqV : q ∈ V := by
        simp only [V, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hqN)
      have hqP : q ∈ P := subset_convexHull ℝ (V : Set Point) hqV
      exact ⟨q, hqP, hpq.le⟩
  exact ⟨V, P, hVnonempty, hPcarrier, hPK, hfaces, hdist⟩

theorem exists_facePreserving_polygonApproximation (K : ConvexBody Point)
    (F : Finset Real.Angle) :
    ∃ (V : ℕ → Finset Point) (P : ℕ → ConvexBody Point),
      (∀ n, (V n).Nonempty ∧
        (P n : Set Point) = convexHull ℝ (V n : Set Point) ∧
        (P n : Set Point) ⊆ (K : Set Point) ∧
        ∀ t ∈ F, exposedEdge (P n) t = exposedEdge K t) ∧
      ∀ n : ℕ, 1 ≤ n → Metric.hausdorffDist (P n : Set Point) (K : Set Point) ≤ 1 / (n : ℝ) := by
  let m : ℕ → ℕ := fun n ↦ max n 1
  let V : ℕ → Finset Point := fun n ↦
    Classical.choose (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity))
  let P : ℕ → ConvexBody Point := fun n ↦
    Classical.choose (Classical.choose_spec (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity)))
  have hdata (n : ℕ) := Classical.choose_spec (Classical.choose_spec
    (exists_facePreserving_polygon K F (show 0 < 1 / (m n : ℝ) by positivity)))
  refine ⟨V, P, ?_, ?_⟩
  · intro n
    exact ⟨(hdata n).1, (hdata n).2.1, (hdata n).2.2.1, (hdata n).2.2.2.1⟩
  · intro n hn
    have hmn : m n = n := max_eq_left hn
    simpa only [P, m, hmn] using (hdata n).2.2.2.2

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Combination
-/

public section

noncomputable section

open scoped unitInterval

universe u v w

namespace MovingSofa

/-- A barycentric operation has an injective realization as convex combinations in a real space. -/
@[expose]
def IsConvexDomain {α : Type u} (c : I → α → α → α) : Prop :=
  ∃ (V : ModuleCat.{v} ℝ) (e : α → V), Function.Injective e ∧
    Convex ℝ (Set.range e) ∧
    ∀ (t : I) x y, e (c t x y) = (1 - (t : ℝ)) • e x + (t : ℝ) • e y

/-- Preservation of the specified barycentric operations. -/
@[expose]
def IsConvexLinear {α : Type u} {β : Type v}
    (cα : I → α → α → α) (cβ : I → β → β → β) (f : α → β) : Prop :=
  ∀ t x y, f (cα t x y) = cβ t (f x) (f y)

/-- Separate preservation of barycentric combinations in both variables. -/
@[expose]
def IsConvexBilinear {α : Type u} {β : Type v} {γ : Type w}
    (cα : I → α → α → α) (cβ : I → β → β → β) (cγ : I → γ → γ → γ)
    (g : α → β → γ) : Prop :=
  (∀ x, IsConvexLinear cβ cγ (g x)) ∧
    ∀ y, IsConvexLinear cα cγ (fun x ↦ g x y)

/-- The usual barycentric combination of real numbers. -/
@[expose]
def realCombination (t : I) (x y : ℝ) : ℝ := (1 - (t : ℝ)) * x + (t : ℝ) * y

/-- A quadratic functional is the diagonal of a separately convex-linear real map. -/
@[expose]
def IsQuadraticFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ) : Prop :=
  ∃ g : α → α → ℝ, IsConvexBilinear c c realCombination g ∧ ∀ x, f x = g x x

/-- Concavity or convexity according to the direction of the barycentric inequality. -/
@[expose]
def IsConvexFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (concave : Bool) : Prop :=
  ∀ t x y, if concave then realCombination t (f x) (f y) ≤ f (c t x y)
    else f (c t x y) ≤ realCombination t (f x) (f y)

/-- The segment function, extended by zero outside its parameter interval. -/
@[expose]
def segmentFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (x y : α) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then f (c ⟨t, ht⟩ x y) else 0

/-- The right derivative along the barycentric segment; used for quadratic functionals. -/
@[expose]
def convexDirectionalDerivative {α : Type u} (c : I → α → α → α)
    (f : α → ℝ) (x y : α) : ℝ :=
  derivWithin (segmentFunctional c f x y) (Set.Icc 0 1) 0

/-- Minkowski interpolation of nonempty compact convex bodies, including both endpoints. -/
def convexBodyCombination (t : I) (K L : ConvexBody Point) : ConvexBody Point :=
  (1 - (t : ℝ)) • K + (t : ℝ) • L

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Area Superlevel
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Pointwise unitInterval

namespace MovingSofa

theorem convexBody_area_superlevel (K L : ConvexBody Point)
    (hK : (11 : ℝ) / 5 ≤ ClassicalResults.area (K : Set Point))
    (hL : (11 : ℝ) / 5 ≤ ClassicalResults.area (L : Set Point)) (t : I) :
    (11 : ℝ) / 5 ≤ ClassicalResults.area (convexBodyCombination t K L : Set Point) := by
  let a : ℝ := 1 - (t : ℝ)
  let b : ℝ := t
  let A : Set Point := a • (K : Set Point)
  let B : Set Point := b • (L : Set Point)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr t.2.2
  have hb : 0 ≤ b := t.2.1
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hAcomp : IsCompact A := K.isCompact.smul a
  have hBcomp : IsCompact B := L.isCompact.smul b
  have hABcomp : IsCompact (A + B) := hAcomp.add hBcomp
  have hbm :
      volume A ^ (2 : ℝ)⁻¹ + volume B ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    convert brunn_minkowski_euclideanSpace (d := 1) (A := A) (B := B)
      (K.nonempty.smul_set (a := a)) hAcomp.measurableSet
      (L.nonempty.smul_set (a := b)) hBcomp.measurableSet hABcomp.measurableSet using 1 <;>
      norm_num
  have hKfin : volume (K : Set Point) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hLfin : volume (L : Set Point) ≠ ⊤ := L.isCompact.measure_lt_top.ne
  have hABfin : volume (A + B) ≠ ⊤ := hABcomp.measure_lt_top.ne
  have hKvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (K : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hKfin).2 hK
  have hLvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (L : Set Point) :=
    (ENNReal.ofReal_le_iff_le_toReal hLfin).2 hL
  have hKroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hKvol
  have hLroot := ENNReal.monotone_rpow_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) hLvol
  have hroot :
      ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ ≤
        volume (A + B) ^ (2 : ℝ)⁻¹ := by
    rw [volume_smul_rpow_half (K : Set Point) a ha,
      volume_smul_rpow_half (L : Set Point) b hb] at hbm
    calc
      _ = (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹ := by
        rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a * volume (K : Set Point) ^ (2 : ℝ)⁻¹ +
          ENNReal.ofReal b * volume (L : Set Point) ^ (2 : ℝ)⁻¹ := by
        rw [add_mul]
        exact add_le_add
          (by simpa [mul_comm] using mul_le_mul_left hKroot (ENNReal.ofReal a))
          (by simpa [mul_comm] using mul_le_mul_left hLroot (ENNReal.ofReal b))
      _ ≤ _ := hbm
  have hvol : ENNReal.ofReal ((11 : ℝ) / 5) ≤ volume (A + B) := by
    calc
      _ = (ENNReal.ofReal ((11 : ℝ) / 5) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) :=
        (ENNReal.rpow_inv_natCast_pow (by norm_num) _).symm
      _ ≤ (volume (A + B) ^ (2 : ℝ)⁻¹) ^ (2 : ℕ) := pow_le_pow_left' hroot 2
      _ = _ := ENNReal.rpow_inv_natCast_pow (by norm_num) _
  have hcomb : (convexBodyCombination t K L : Set Point) = A + B := by
    rfl
  rw [hcomb]
  exact (ENNReal.ofReal_le_iff_le_toReal hABfin).1 hvol

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Pulling barycentric functionals back along convex-linear maps

A convex-linear map transports one barycentric operation to another, so every notion defined
from that operation pulls back along it: a quadratic functional stays quadratic, and its
directional derivative along a segment is the directional derivative between the images of the
two endpoints. Neither statement needs any topology or differentiability: the two segment
functions are literally equal.
-/

public section

noncomputable section

open scoped unitInterval

universe u v

namespace MovingSofa

/-- A quadratic functional pulled back along a convex-linear map is quadratic. -/
theorem IsQuadraticFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} (hf : IsQuadraticFunctional cβ f) :
    IsQuadraticFunctional cα fun x ↦ f (F x) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x y ↦ g (F x) (F y), ⟨fun x s y z ↦ ?_, fun y s x z ↦ ?_⟩, fun x ↦ hfg (F x)⟩
  · change g (F x) (F (cα s y z)) = _
    rw [hF]
    exact hg.1 (F x) s (F y) (F z)
  · change g (F (cα s x z)) (F y) = _
    rw [hF]
    exact hg.2 (F y) s (F x) (F z)

/-- The directional derivative of a functional pulled back along a convex-linear map is the
directional derivative of the functional between the images. -/
theorem convexDirectionalDerivative_comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) (f : β → ℝ) (x y : α) :
    convexDirectionalDerivative cα (fun z ↦ f (F z)) x y =
      convexDirectionalDerivative cβ f (F x) (F y) := by
  unfold convexDirectionalDerivative
  congr 1
  funext s
  simp only [segmentFunctional]
  split_ifs with hs
  · exact congrArg f (hF _ x y)
  · rfl

/-- A convex or concave functional pulled back along a convex-linear map keeps its direction of
convexity. -/
theorem IsConvexFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} {concave : Bool}
    (hf : IsConvexFunctional cβ f concave) :
    IsConvexFunctional cα (fun x ↦ f (F x)) concave := by
  intro s x y
  have h := hf s (F x) (F y)
  rw [← hF s x y] at h
  exact h

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area lower bound from ordered support contacts

A compact convex set `K` of the plane that contains a base point `L = (ℓ, 0)` and lies in the
closed quadrant `{(a, b) | ℓ ≤ a, 0 ≤ b}` has area at least the shoelace expression of any
finite fan `L, P₀, …, P_n` of support contacts taken at strictly increasing normal angles in
`[0, π)`.

Two ordered contacts span a nonnegatively oriented determinant over `L`: expanding the
support inequalities in coordinates turns `sin (β - α) · (P - L) × (Q - L)` into a sum of two
products of nonnegative factors. The fan triangles `convexHull ℝ {L, Pᵢ, Pᵢ₊₁}` therefore lie
in `K` with area one half of their determinant, and two of them can meet only along the line
through `L` and the contact they share, which is planar null. Finite additivity of the volume
off that null set and monotonicity give the bound. Repeated contacts, zero contact vectors and
collinear consecutive rays are allowed: a degenerate triangle simply has vanishing area.
-/

public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two ordered support contacts of a set lying in the closed quadrant above a base point
have nonnegative oriented determinant over that base point. -/
theorem planeCrossProduct_sub_nonneg_of_support {K : Set Point} {L P Q : Point}
    (hL : L ∈ K) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < Real.pi)
    (hP : P ∈ K) (hQ : Q ∈ K)
    (hPs : ∀ x ∈ K, inner ℝ x (normalVector (α : Real.Angle)) ≤
      inner ℝ P (normalVector (α : Real.Angle)))
    (hQs : ∀ x ∈ K, inner ℝ x (normalVector (β : Real.Angle)) ≤
      inner ℝ Q (normalVector (β : Real.Angle))) :
    0 ≤ planeCrossProduct (P - L) (Q - L) := by
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (hα.trans_lt hαβ) hβ
  have hsα : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα (by linarith)
  have hsδ : 0 < Real.sin β * Real.cos α - Real.cos β * Real.sin α := by
    have h := Real.sin_pos_of_pos_of_lt_pi (x := β - α) (by linarith) (by linarith)
    rwa [Real.sin_sub] at h
  have hz : 0 ≤ (P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α := by
    have h := hPs Q hQ
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hk : 0 ≤ (Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β := by
    have h := hQs P hP
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hB : 0 ≤ (Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β := by
    have h := hQs L hL
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hq0 : 0 ≤ Q 0 - L 0 := sub_nonneg.mpr (hquadrant Q hQ).1
  have hc : 0 ≤ (Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α := by
    have hid : Real.sin β * ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α)
        = Real.sin α * ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β)
          + (Real.sin β * Real.cos α - Real.cos β * Real.sin α) * (Q 0 - L 0) := by
      ring
    nlinarith [mul_nonneg hsα hB, mul_nonneg hsδ.le hq0]
  have hcross : planeCrossProduct (P - L) (Q - L)
      = (P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0) := by
    simp [planeCrossProduct]
  have hid2 : (Real.sin β * Real.cos α - Real.cos β * Real.sin α) *
      ((P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0))
      = ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α) *
          ((Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β)
        + ((P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α) *
          ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β) := by
    ring
  rw [hcross]
  nlinarith [mul_nonneg hc hk, mul_nonneg hz hB]

theorem supportContact_fan_area (K : Set Point)
    (hcK : IsCompact K) (hvK : Convex ℝ K) (L : Point) (hL : L ∈ K)
    (hLy : L 1 = 0) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    (n : ℕ) (θ : Fin (n + 1) → ℝ)
    (hθ : StrictMono θ) (hθrange : ∀ i, 0 ≤ θ i ∧ θ i < Real.pi)
    (P : Fin (n + 1) → Point) (hP : ∀ i, P i ∈ K)
    (hsupport : ∀ i q, q ∈ K →
      inner ℝ q (normalVector (θ i : Real.Angle)) ≤
        inner ℝ (P i) (normalVector (θ i : Real.Angle))) :
    0 ≤ (1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L) ∧
    (1 / 2 : ℝ) * (∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ ClassicalResults.area K := by
  have hquad : ∀ x ∈ K, 0 ≤ (x - L) 0 ∧ 0 ≤ (x - L) 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hquadrant x hx
    exact ⟨by simpa using sub_nonneg.mpr h1, by simpa [hLy] using h2⟩
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → 0 ≤ planeCrossProduct (P i - L) (P j - L) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · simp
    · exact planeCrossProduct_sub_nonneg_of_support hL hquadrant (hθrange i).1 (hθ hlt)
        (hθrange j).2 (hP i) (hP j) (fun x hx ↦ hsupport i x hx) (fun x hx ↦ hsupport j x hx)
  have hcnn : ∀ i : Fin n, 0 ≤ planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    fun i ↦ hmono _ _ Fin.castSucc_lt_succ.le
  have hsumnn : 0 ≤ ∑ i : Fin n, planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    Finset.sum_nonneg fun i _ ↦ hcnn i
  refine ⟨by linarith, ?_⟩
  set T : Fin n → Set Point := fun i ↦ convexHull ℝ {L, P i.castSucc, P i.succ} with hTdef
  have hTsub : ∀ i, T i ⊆ K := by
    intro i
    refine convexHull_min ?_ hvK
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hL, hP _, hP _]
  have hTvol : ∀ i, volume (T i) = ENNReal.ofReal
      ((1 / 2 : ℝ) * planeCrossProduct (P i.castSucc - L) (P i.succ - L)) := by
    intro i
    have hpos := hcnn i
    simp only [planeCrossProduct] at hpos
    simp only [hTdef, EuclideanSpace.volume_convexHull_triple]
    congr 1
    rw [abs_of_nonneg (by linarith)]
    simp only [planeCrossProduct]
    ring
  have hTmeas : ∀ i, NullMeasurableSet (T i) volume := by
    intro i
    refine (IsCompact.measurableSet ?_).nullMeasurableSet
    exact (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull ℝ
  have hsector : ∀ i : Fin n, T i ⊆ {x : Point |
      0 ≤ planeCrossProduct (P i.castSucc - L) (x - L) ∧
      0 ≤ planeCrossProduct (x - L) (P i.succ - L)} := by
    intro i
    refine convexHull_min ?_ (convex_setOf_planeCrossProduct_fan _ _ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, hcnn i⟩
    · exact ⟨hcnn i, by simp⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) T) := by
    have hkey : ∀ i j : Fin n, i < j → volume (T i ∩ T j) = 0 := by
      intro i j hij
      rcases eq_or_lt_of_le (hcnn i) with h0 | h0
      · exact measure_mono_null Set.inter_subset_left (by rw [hTvol i, ← h0]; simp)
      rcases eq_or_lt_of_le (hcnn j) with h1 | h1
      · exact measure_mono_null Set.inter_subset_right (by rw [hTvol j, ← h1]; simp)
      have hne2 : P j.castSucc - L ≠ 0 := by
        intro h
        rw [h] at h1
        simp [planeCrossProduct] at h1
      have hne1 : P i.succ - L ≠ 0 := by
        intro h
        rw [h] at h0
        simp [planeCrossProduct] at h0
      refine measure_mono_null ?_ (volume_setOf_planeCrossProduct_sub_eq_zero hne1 L)
      rintro x ⟨hxi, hxj⟩
      have hxK : x ∈ K := hTsub i hxi
      have h2 := (hsector i hxi).2
      have h3 := (hsector j hxj).1
      have hle : i.succ ≤ j.castSucc := by
        have hij' : (i : ℕ) < (j : ℕ) := hij
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have h5 : 0 ≤ planeCrossProduct (P i.succ - L) (x - L) :=
        planeCrossProduct_nonneg_trans hne2
          (hquad _ (hP _)).1 (hquad _ (hP _)).2 (hquad _ (hP _)).1 (hquad _ (hP _)).2
          (hquad x hxK).1 (hquad x hxK).2 (hmono _ _ hle) h3
      change planeCrossProduct (P i.succ - L) (x - L) = 0
      rw [planeCrossProduct_swap (x - L)] at h2
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h
    · change volume (T i ∩ T j) = 0
      rw [Set.inter_comm]
      exact hkey j i h
  have hunion : ∑ i : Fin n, volume (T i) ≤ volume K := by
    have h := measure_iUnion₀ (μ := volume) hdisj hTmeas
    rw [tsum_fintype] at h
    rw [← h]
    exact measure_mono (Set.iUnion_subset hTsub)
  have hgoal : ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ volume K := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by linarith [hcnn i])]
    simpa only [hTvol] using hunion
  exact (ENNReal.ofReal_le_iff_le_toReal hcK.measure_lt_top.ne).mp hgoal

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Exposed Faces
-/

public section

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

private theorem support_bound (K : ConvexBody Point) (a : Real.Angle)
    {x : Point} (hx : x ∈ K) : inner ℝ x (normalVector a) ≤ supportValue K a := by
  apply le_csSup
  · exact (K.isCompact.image (continuous_id.inner continuous_const)).bddAbove
  · exact ⟨x, hx, rfl⟩

private theorem edge_nonempty (K : ConvexBody Point) (a : Real.Angle) :
    (exposedEdge K a).Nonempty := by
  obtain ⟨x, hx, he⟩ := (K.isCompact.image (continuous_id.inner continuous_const)).sSup_mem
    (K.nonempty.image (fun x ↦ inner ℝ x (normalVector a)))
  exact ⟨x, hx, he⟩

private theorem mem_edge_iff (K : ConvexBody Point) (a : Real.Angle) (x : Point) :
    x ∈ exposedEdge K a ↔ x ∈ K ∧ ∀ y ∈ K,
      inner ℝ y (normalVector a) ≤ inner ℝ x (normalVector a) := by
  change (x ∈ K ∧ inner ℝ x (normalVector a) = supportValue K a) ↔ _
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, fun y hy ↦ he ▸ support_bound K a hy⟩
  · rintro ⟨hx, hm⟩
    refine ⟨hx, le_antisymm (support_bound K a hx) ?_⟩
    exact csSup_le (K.nonempty.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hm y hy)

private theorem combination_zero (K L : ConvexBody Point) :
    convexBodyCombination 0 K L = K := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set L.nonempty]

private theorem combination_one (K L : ConvexBody Point) :
    convexBodyCombination 1 K L = L := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set K.nonempty]

/-- Exposed faces commute with convex interpolation, including zero and unit weights. -/
theorem exposedEdge_convexBodyCombination (K L : ConvexBody Point) (a : Real.Angle)
    (t : unitInterval) :
    exposedEdge (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) • exposedEdge K a + (t : ℝ) • exposedEdge L a := by
  by_cases h0 : t = 0
  · subst t
    simp [combination_zero, Set.zero_smul_set (edge_nonempty L a)]
  by_cases h1 : t = 1
  · subst t
    simp [combination_one, Set.zero_smul_set (edge_nonempty K a)]
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro h; exact h0 (Subtype.ext h.symm))
  have hu : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 (by
    intro h; exact h1 (Subtype.ext h)))
  have mem_combo (x y : Point) (hx : x ∈ K) (hy : y ∈ L) :
      (1 - (t : ℝ)) • x + (t : ℝ) • y ∈ convexBodyCombination t K L := by
    exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hm⟩ := (mem_edge_iff _ a p).mp hp
    obtain ⟨u, huK, v, hvL, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    have hxedge : x ∈ exposedEdge K a := (mem_edge_iff K a x).mpr ⟨hx, by
      intro z hz
      have h := hm _ (mem_combo z y hz hy)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    have hyedge : y ∈ exposedEdge L a := (mem_edge_iff L a y).mpr ⟨hy, by
      intro z hz
      have h := hm _ (mem_combo x z hx hz)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    exact Set.add_mem_add (Set.smul_mem_smul_set hxedge) (Set.smul_mem_smul_set hyedge)
  · rintro ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    obtain ⟨hx, hmx⟩ := (mem_edge_iff K a x).mp hx
    obtain ⟨hy, hmy⟩ := (mem_edge_iff L a y).mp hy
    apply (mem_edge_iff _ a _).mpr
    refine ⟨mem_combo x y hx hy, ?_⟩
    rintro p ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨z, hz, rfl⟩ := huK
    obtain ⟨w, hw, rfl⟩ := hvL
    have hxz := hmx z hz
    have hyw := hmy w hw
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
    nlinarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Limits
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The supremum of scalar products with a specified direction vector. -/
@[expose]
def vectorSupport (S : Set Point) (u : Point) : ℝ := sSup ((fun x ↦ inner ℝ x u) '' S)

/-- Support values in a unit direction vary by at most the Hausdorff distance. -/
theorem abs_vectorSupport_sub_le_hausdorffDist {S T : Set Point}
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T)
    {u : Point} (hu : ‖u‖ = 1) :
    |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T := by
  simpa only [vectorSupport, hu, mul_one] using
    hcS.abs_csSup_inner_sub_le_hausdorffDist hS hcT hT u

theorem convexBody_selection (A : Set Point) (hA : IsCompact A)
    (K : ℕ → ConvexBody Point) (hK : ∀ n, (K n : Set Point) ⊆ A) :
    ∃ (φ : ℕ → ℕ) (L : ConvexBody Point), StrictMono φ ∧
      Tendsto (fun n ↦ Metric.hausdorffDist (K (φ n) : Set Point) (L : Set Point))
        atTop (𝓝 0) := by
  let C : ℕ → TopologicalSpace.NonemptyCompacts Point := fun n ↦
    ⟨⟨(K n : Set Point), (K n).isCompact⟩, (K n).nonempty⟩
  obtain ⟨L, hLA, φ, hφ, hlim⟩ :=
    (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hA).tendsto_subseq
      (show ∀ n, C n ∈ {L : TopologicalSpace.NonemptyCompacts Point | (L : Set Point) ⊆ A}
        from hK)
  have hconv : Convex ℝ (L : Set Point) :=
    TopologicalSpace.NonemptyCompacts.convex_of_tendsto (fun n ↦ (K (φ n)).convex) hlim
  refine ⟨φ, ⟨(L : Set Point), hconv, L.isCompact, L.nonempty⟩, hφ, ?_⟩
  simpa only [C, Function.comp_apply, TopologicalSpace.NonemptyCompacts.dist_eq,
    TopologicalSpace.NonemptyCompacts.coe_mk, TopologicalSpace.Compacts.coe_mk, ConvexBody.coe_mk]
      using
    (tendsto_iff_dist_tendsto_zero.mp hlim)

theorem compactSet_support_continuity (S T : Set Point)
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T) :
    (∀ u v : Point, ‖u‖ = 1 → ‖v‖ = 1 →
      |vectorSupport S u - vectorSupport S v| ≤ sSup (norm '' S) * ‖u - v‖) ∧
    (∀ u : Point, ‖u‖ = 1 →
      |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T) ∧
    Continuous (fun t : Real.Angle ↦ supportValue S t) ∧
    (∀ (K : ℕ → Set Point), (∀ n, (K n).Nonempty ∧ IsCompact (K n)) →
      Tendsto (fun n ↦ Metric.hausdorffDist (K n) S) atTop (𝓝 0) →
      TendstoUniformlyOn (fun n u ↦ vectorSupport (K n) u) (vectorSupport S)
        atTop {u | ‖u‖ = 1}) := by
  constructor
  · intro u v _ _
    exact hcS.abs_csSup_inner_sub_le hS u v
  constructor
  · intro u hu
    exact abs_vectorSupport_sub_le_hausdorffDist hS hcS hT hcT hu
  constructor
  · unfold supportValue
    apply hcS.continuous_sSup
    change Continuous (fun q : Real.Angle × Point ↦ inner ℝ q.2 (normalVector q.1))
    have hn : Continuous (fun q : Real.Angle × Point ↦ normalVector q.1) := by
      let c : Real.Angle × Point → (i : Fin 2) → ℝ :=
        fun q i ↦ Fin.cases q.1.cos (fun _ ↦ q.1.sin) i
      have hc : Continuous c := by
        apply continuous_pi
        intro i
        fin_cases i
        · exact Real.Angle.continuous_cos.comp continuous_fst
        · exact Real.Angle.continuous_sin.comp continuous_fst
      have heq : (fun q : Real.Angle × Point ↦ normalVector q.1) =
          (fun q ↦ WithLp.toLp 2 (c q)) := by
        funext q
        ext i
        fin_cases i <;> rfl
      rw [heq]
      exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
    simpa [Function.comp_def] using
      (continuous_inner (𝕜 := ℝ) (E := Point)).comp (continuous_snd.prodMk hn)
  · intro K hK hlim
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro u hu
    rw [Real.dist_eq]
    exact (abs_vectorSupport_sub_le_hausdorffDist hS hcS
      (hK n).1 (hK n).2 hu).trans_lt (by simpa [Metric.hausdorffDist_comm] using hn)

private theorem exists_inner_pos_of_eq_iInter
    (U : Set Point) (K : Set Point) (hne : K.Nonempty) (hbounded : Bornology.IsBounded K)
    (hK : K = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u}) :
    ∀ d : Point, d ≠ 0 → ∃ u ∈ U, 0 < inner ℝ d u := by
  intro d hd
  by_contra hno
  push Not at hno
  obtain ⟨z, hz⟩ := hne
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : Point) |>.1 hbounded
  have hzI : z ∈ ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u} := by
    rw [← hK]
    exact hz
  have hmem : ∀ t : ℝ, 0 ≤ t → z + t • d ∈ K := by
    intro t ht
    rw [hK]
    simp only [Set.mem_iInter]
    intro u hu
    have hz' := (Set.mem_iInter.mp (Set.mem_iInter.mp hzI u) hu)
    dsimp at hz' ⊢
    rw [inner_add_left, inner_smul_left]
    change inner ℝ z u + t * inner ℝ d u ≤ vectorSupport K u
    have hdu : inner ℝ d u ≤ 0 := hno u hu
    have htd : t * inner ℝ d u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hdu
    nlinarith [hz', htd]
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖z + t • d‖ ≤ R := by
    intro t ht
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hR (hmem t ht)))
  have hd' : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR0 : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.mp (hR hz))
  let t : ℝ := (R + ‖z‖ + 1) / ‖d‖
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg (by positivity) (le_of_lt hd')
  have hn := hnorm t ht
  have hts : ‖t • d‖ = R + ‖z‖ + 1 := by
    dsimp [t]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact div_mul_cancel₀ _ (ne_of_gt hd')
  have htriangle' : ‖t • d‖ ≤ ‖z + t • d‖ + ‖z‖ := by
    have h := norm_sub_le (z + t • d) z
    simpa [sub_eq_add_neg, add_assoc] using h
  rw [hts] at htriangle'
  nlinarith

private theorem ball_support_margin
    (U : Set Point) (L : Set Point) (q u : Point) (r : ℝ) (hr : 0 ≤ r)
    (hu : u ∈ U) (hunit : ‖u‖ = 1)
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    inner ℝ q u + r ≤ vectorSupport L u := by
  have hp : q + r • u ∈ Metric.closedBall q r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hunit]
    simp
  have hp' := hball hp
  have hpu := (Set.mem_iInter.mp (Set.mem_iInter.mp hp' u) hu)
  dsimp at hpu
  rw [inner_add_left, inner_smul_left] at hpu
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  simp only [huu] at hpu
  simpa using hpu

private theorem eventually_ball_center_mem
    (U : Set Point) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hq : ∀ u ∈ U, inner ℝ q u + r ≤ vectorSupport (L : Set Point) u)
    (hU : ∀ u ∈ U, ‖u‖ = 1) :
    ∀ᶠ n in atTop, q ∈ (K n : Set Point) := by
  filter_upwards [hlim.eventually (gt_mem_nhds hr)] with n hn
  rw [hK n]
  simp only [Set.mem_iInter]
  intro u hu
  have habs := (compactSet_support_continuity (K n : Set Point) (L : Set Point)
    (K n).nonempty (K n).isCompact L.nonempty L.isCompact).2.1 u (hU u hu)
  have hlower : vectorSupport (L : Set Point) u -
      Metric.hausdorffDist (K n : Set Point) (L : Set Point) ≤
      vectorSupport (K n : Set Point) u := by
    linarith [neg_le_of_abs_le habs]
  have hqr := hq u hu
  change inner ℝ q u ≤ vectorSupport (K n : Set Point) u
  calc
    inner ℝ q u ≤ vectorSupport (L : Set Point) u - r := by linarith
    _ ≤ vectorSupport (L : Set Point) u - Metric.hausdorffDist (K n : Set Point) L := by
      exact le_of_lt (by linarith)
    _ ≤ vectorSupport (K n : Set Point) u := hlower

private theorem ball_center_mem_limit
    (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    q ∈ (L : Set Point) := by
  exact ConvexBody.mem_of_tendsto_hausdorffDist q K L
    (eventually_ball_center_mem U q r hr K L hK hlim
      (fun u hu ↦ ball_support_margin U L q u r hr.le hu (hU u hu) hball) hU) hlim

theorem fixedNormalBody_closed (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    (L : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u} := by
  let H : Set Point := ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u}
  have hLH : (L : Set Point) ⊆ H := by
    intro x hx
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq]
    intro u hu
    exact le_csSup (L.isCompact.bddAbove_image
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn)
      ⟨x, hx, rfl⟩
  have hH : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq] at hx hy ⊢
    intro u hu
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      a * inner ℝ x u + b * inner ℝ y u ≤
          a * vectorSupport L u + b * vectorSupport L u :=
        add_le_add (mul_le_mul_of_nonneg_left (hx u hu) ha)
          (mul_le_mul_of_nonneg_left (hy u hu) hb)
      _ = vectorSupport L u := by rw [← add_mul, hab, one_mul]
  have hint : interior H ⊆ (L : Set Point) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (mem_interior_iff_mem_nhds.mp hx)
    exact ball_center_mem_limit U hU x r hr K L hK hlim hball
  apply Set.Subset.antisymm hLH
  rcases (interior H).eq_empty_or_nonempty with hempty | hnonempty
  · have hcol : Collinear ℝ H := hH.collinear_of_interior_eq_empty (by
      simp [Point, finrank_euclideanSpace]) hempty
    intro p hp
    obtain ⟨a, ha⟩ := L.nonempty
    by_cases hpa : p = a
    · simpa only [hpa] using ha
    obtain ⟨u, hu, hpos⟩ := exists_inner_pos_of_eq_iInter U (K 0) (K 0).nonempty
      (K 0).isCompact.isBounded (hK 0)
      (p - a) (sub_ne_zero.mpr hpa)
    have hmax : ∃ x ∈ (L : Set Point), vectorSupport L u = inner ℝ x u ∧
        ∀ y ∈ (L : Set Point), inner ℝ y u ≤ inner ℝ x u := by
      simpa only [vectorSupport, Function.comp_apply, id_eq] using
        L.isCompact.exists_sSup_image_eq_and_ge (α := ℝ) (β := Point)
          (f := fun x : Point ↦ inner ℝ x u) L.nonempty
          (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨x, hx, hxu, _⟩ := hmax
    have hle : inner ℝ p u ≤ inner ℝ x u := by
      rw [← hxu]
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    have hsegment := hcol.mem_segment_of_apply_le (hLH ha) hp (hLH hx)
      (innerSL ℝ u).toLinearMap (by change 0 < inner ℝ u (p - a); rwa [real_inner_comm])
      (by change inner ℝ u p ≤ inner ℝ u x; simpa only [real_inner_comm u] using hle)
    exact L.convex.segment_subset ha hx hsegment
  · have hclosure : closure (interior H) = closure H :=
      hH.closure_interior_eq_closure_of_nonempty_interior hnonempty
    exact subset_closure.trans (hclosure ▸ L.isClosed.closure_subset_iff.mpr hint)

theorem convexArea_hausdorff_continuity (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ClassicalResults.area (K n)) atTop (𝓝 (ClassicalResults.area L)) := by
  let U : Set Point := {u | ‖u‖ = 1}
  have hrepK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u} := by
    intro n
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces (K n)
  have hrepL : (L : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u} := by
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces L
  obtain ⟨R, hR, hcompact⟩ := L.isCompact.exists_isCompact_cthickening
  let C : Set Point := Metric.cthickening R (L : Set Point)
  have hsubset : ∀ᶠ n in atTop, (K n : Set Point) ⊆ C := by
    filter_upwards [hlim.eventually (gt_mem_nhds hR)] with n hn p hp
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact Metric.mem_cthickening_of_dist_le p q R L hq hpq.le
  have hpointwise : ∀ p ∉ frontier (L : Set Point),
      Tendsto (fun n ↦ (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) atTop
        (𝓝 ((L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    intro p hpfrontier
    by_cases hpL : p ∈ (L : Set Point)
    · have hpint : p ∈ interior (L : Set Point) := by
        by_contra hp
        exact hpfrontier ((mem_frontier_iff_notMem_interior hpL).mpr hp)
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (mem_interior_iff_mem_nhds.mp hpint)
      have hmargin : ∀ u ∈ U, inner ℝ p u + r ≤ vectorSupport L u := by
        intro u hu
        rw [hrepL] at hball
        exact ball_support_margin U L p u r hr.le hu hu hball
      have hev := eventually_ball_center_mem U p r hr K L hrepK hlim hmargin
        (fun _ hu ↦ hu)
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
    · have hdist : 0 < Metric.infDist p (L : Set Point) := by
        exact (Metric.infDist_pos_iff_notMem_closure L.nonempty).mp (by
          rwa [L.isClosed.closure_eq])
      have hev : ∀ᶠ n in atTop, p ∉ (K n : Set Point) := by
        filter_upwards [hlim.eventually (gt_mem_nhds hdist)] with n hn hpn
        have hle := Metric.infDist_le_hausdorffDist_of_mem hpn
          (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
            (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
        linarith
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
  have hfrontier : MeasureTheory.volume (frontier (L : Set Point)) = 0 :=
    L.convex.addHaar_frontier MeasureTheory.volume
  have hmeas : ∀ n, MeasurableSet (K n : Set Point) := fun n ↦ (K n).isCompact.measurableSet
  have hCmeas : MeasurableSet C := hcompact.measurableSet
  have hCint : MeasureTheory.Integrable (C.indicator fun _ ↦ (1 : ℝ)) := by
    exact (MeasureTheory.integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hCmeas
  have htendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun n ↦ (K n : Set Point).indicator fun _ ↦ (1 : ℝ))
    (f := (L : Set Point).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun n ↦
      (measurable_const.indicator (hmeas n)).aestronglyMeasurable)
    (by
      filter_upwards [hsubset] with n hn
      filter_upwards [] with p
      by_cases hp : p ∈ (K n : Set Point)
      · have hpC := hn hp
        simp [hp, hpC]
      · by_cases hpC : p ∈ C <;> simp [hp, hpC])
    hCint
    (by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hfrontier] with p hp
      exact hpointwise p hp)
  have heqK : ∀ n, (∫ p, (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (K n : Set Point) := by
    intro n
    change (∫ p, (K n : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume) (hmeas n)
  have heqL : (∫ p, (L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (L : Set Point) := by
    change (∫ p, (L : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume)
      L.isCompact.measurableSet
  simp_rw [heqK] at htendsto
  rw [heqL] at htendsto
  simpa [ClassicalResults.area, MeasureTheory.Measure.real] using htendsto

/-- The support function of a convex body is continuous in the normal direction. -/
theorem continuous_supportValue (K : ConvexBody Point) :
    Continuous fun t : Real.Angle ↦ supportValue (K : Set Point) t :=
  (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1

theorem continuous_supportValue_real (K : ConvexBody Point) :
    Continuous (fun t : ℝ ↦ supportValue K (t : Real.Angle)) :=
  (continuous_supportValue K).comp Real.Angle.continuous_coe

/-- Support values of a nonempty compact set are Lipschitz in the real angle, with the largest
norm of a point of the set as Lipschitz constant. -/
theorem abs_supportValue_sub_le_of_isCompact {s : Set Point} (hne : s.Nonempty)
    (hc : IsCompact s) (x y : ℝ) :
    |supportValue s (x : Real.Angle) - supportValue s (y : Real.Angle)| ≤
      sSup (norm '' s) * |x - y| := by
  have hdir := (compactSet_support_continuity s s hne hc hne hc).1
    (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (norm_normalVector_real y)
  have hframe : ‖normalVector (x : Real.Angle) - normalVector (y : Real.Angle)‖ ≤ |x - y| := by
    simpa [dist_eq_norm, Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul x y
  have h0 : 0 ≤ sSup (norm '' s) :=
    Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  exact hdir.trans (mul_le_mul_of_nonneg_left hframe h0)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Support Embedding
-/

public section

noncomputable section

namespace MovingSofa

theorem supportFunction_minkowski_embedding (K L : ConvexBody Point) :
    (∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ t : Real.Angle,
      supportValue {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = a • x + b • y} t =
        a * supportValue K t + b * supportValue L t) ∧
    ((∀ t : Real.Angle, supportValue K t = supportValue L t) → K = L) ∧
    Continuous (fun t : Real.Angle ↦ supportValue K t) ∧
    (K : Set Point) = ⋂ u ∈ {u : Point | ‖u‖ = 1},
      {p : Point | inner ℝ p u ≤ vectorSupport K u} := by
  refine ⟨?_, ?_, (compactSet_support_continuity K K K.nonempty K.isCompact
    K.nonempty K.isCompact).2.2.1, K.eq_iInter_halfSpaces⟩
  · intro a b ha hb t
    obtain ⟨x, hx, hxmax, hxle⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨y, hy, hymax, hyle⟩ := L.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) L.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' K) = _ at hxmax
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' L) = _ at hymax
    unfold supportValue
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨a • x + b • y, ?_, ?_⟩
      · exact ⟨x, hx, y, hy, rfl⟩
      · change inner ℝ (a • x + b • y) (normalVector t) = _
        rw [inner_add_left, inner_smul_left, inner_smul_left, ← hxmax, ← hymax]
        simp
    · intro r hr
      obtain ⟨z, ⟨x', hx', y', hy', rfl⟩, rfl⟩ := hr
      change inner ℝ (a • x' + b • y') (normalVector t) ≤ _
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      rw [hxmax, hymax]
      exact add_le_add (mul_le_mul_of_nonneg_left (hxle x' hx') ha)
        (mul_le_mul_of_nonneg_left (hyle y' hy') hb)
  · intro hKL
    have hvector (u : Point) (hu : ‖u‖ = 1) : vectorSupport K u = vectorSupport L u := by
      obtain ⟨t, rfl⟩ := exists_angle_normalVector_eq hu
      exact hKL t
    simp only [vectorSupport] at hvector
    apply ConvexBody.ext
    rw [K.eq_iInter_halfSpaces,
      L.eq_iInter_halfSpaces]
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor <;> intro hp u hu
    · simpa [hvector u hu] using hp u hu
    · simpa [hvector u hu] using hp u hu

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Combination Properties
-/

public section

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

/-- Pointwise description of the Minkowski interpolation of two convex bodies. -/
theorem mem_convexBodyCombination_iff (t : I) (K L : ConvexBody Point) (z : Point) :
    z ∈ (convexBodyCombination t K L : Set Point) ↔
      ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
  change z ∈ (1 - (t : ℝ)) • (K : Set Point) + (t : ℝ) • (L : Set Point) ↔ _
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩

/-- The first edge vertex maximizes tangent coordinate on its exposed edge. -/
theorem inner_le_edgeVertices_fst_tangent (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ p (tangentVector a) ≤ inner ℝ (edgeVertices K a).1 (tangentVector a) := by
  rw [inner_edgeVertices_fst_tangent]
  exact le_csSup ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddAbove) ⟨p, hp, rfl⟩

/-- A tangent-coordinate maximizer on an exposed edge is its first vertex. -/
theorem edgeVertices_fst_eq_of_tangent_isGreatest (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmax : ∀ q ∈ exposedEdge K a,
      inner ℝ q (tangentVector a) ≤ inner ℝ p (tangentVector a)) :
    (edgeVertices K a).1 = p := by
  have ht := le_antisymm (hmax _ (edgeVertices_fst_mem K a))
    (inner_le_edgeVertices_fst_tangent K a hp)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).1 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_fst_mem K a).2, hp.2, ht]

/-- A tangent-coordinate minimizer on an exposed edge is its second vertex. -/
theorem edgeVertices_snd_eq_of_tangent_isLeast (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmin : ∀ q ∈ exposedEdge K a,
      inner ℝ p (tangentVector a) ≤ inner ℝ q (tangentVector a)) :
    (edgeVertices K a).2 = p := by
  have hbdd : BddBelow
      ((fun q : Point ↦ inner ℝ q (tangentVector a)) '' exposedEdge K a) :=
    ((isCompact_exposedEdge K a).image
      (continuous_id.inner continuous_const)).bddBelow
  have ht : inner ℝ (edgeVertices K a).2 (tangentVector a) =
      inner ℝ p (tangentVector a) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm (csInf_le hbdd ⟨p, hp, rfl⟩)
    rw [← inner_edgeVertices_snd_tangent]
    exact hmin _ (edgeVertices_snd_mem K a)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).2 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_snd_mem K a).2, hp.2, ht]

private theorem inner_edgeVertices_snd_tangent_le_point (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ (edgeVertices K a).2 (tangentVector a) ≤ inner ℝ p (tangentVector a) := by
  rw [inner_edgeVertices_snd_tangent]
  exact csInf_le ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddBelow) ⟨p, hp, rfl⟩

/-- The extreme points of exposed edges commute with convex combinations. -/
theorem edgeVertices_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2 := by
  let M := convexBodyCombination t K L
  have hedge := exposedEdge_convexBodyCombination K L a t
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have htnonneg : 0 ≤ (t : ℝ) := t.property.1
  constructor
  · apply edgeVertices_fst_eq_of_tangent_isGreatest M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_fst_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_fst_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent L a hy) htnonneg)
  · apply edgeVertices_snd_eq_of_tangent_isLeast M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_snd_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_snd_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point L a hy) htnonneg)

/-- Support values commute with convex combinations. -/
theorem supportValue_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a := by
  rw [show (convexBodyCombination t K L : Set Point) =
      {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y} from
    Set.ext (mem_convexBodyCombination_iff t K L)]
  exact (supportFunction_minkowski_embedding K L).1
    (1 - (t : ℝ)) t (sub_nonneg.mpr t.property.2) t.property.1 a

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Faces of a body cut out by a differentiable family of half-planes

Let `L` be a convex body lying in every half-plane `{q | m s ≤ ⟪q, u_s⟫}` of a family indexed
by a real angle parameter `s`, and let `p ∈ L` attain the bound at `s = t`.  If `m` is
differentiable at `t` with `m' t = ⟪p, v_t⟫` — that is, if `p` is the first-order contact point
of the family — then the reversed face of `L` at `t + π` is pinned down by the sign of the
one-sided derivatives of `s ↦ ⟪z, u_s⟫ - m s` at `t`:
`exposedEdge_add_pi_eq_singleton_of_mem_Ioo` at an interior parameter gives the singleton
`{p}`, while `edgeVertices_add_pi_fst_eq_of_lt` and `edgeVertices_add_pi_snd_eq_of_lt` identify
`p` with one endpoint vertex of the face at the two boundary parameters.
-/

public section

noncomputable section

namespace MovingSofa

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the left of the touching parameter is at most that of the contact point. -/
theorem inner_tangentVector_le_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {a t : ℝ}
    (hat : a < t) (hle : ∀ s ∈ Set.Ioo a t, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ z (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Iic t) t := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hat), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Iic.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨hs, h⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Iic_nonpos hF.hasDerivWithinAt]

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the right of the touching parameter is at least that of the contact point. -/
theorem le_inner_tangentVector_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {t b : ℝ}
    (htb : t < b) (hle : ∀ s ∈ Set.Ioo t b, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ z (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Ici t) t := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Ici.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨h, hs⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Ici_nonneg hF.hasDerivWithinAt]

/-- At an interior touching parameter of a differentiable family of supporting half-planes the
reversed face is the singleton contact point. -/
theorem exposedEdge_add_pi_eq_singleton_of_mem_Ioo {L : ConvexBody Point} {m : ℝ → ℝ}
    {p : Point} {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) = {p} := by
  have hlet : ∀ q ∈ (L : Set Point), m t ≤ inner ℝ q (normalVector (t : Real.Angle)) :=
    fun q hq ↦ hle q hq t ht
  rw [exposedEdge_add_pi_eq_of_forall_le hlet hp hpm]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ ⟨hq ▸ hp, hq ▸ hpm⟩⟩
  have h1 : inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo ht.1
      (fun s hs ↦ hle q hq.1 s ⟨hs.1, hs.2.trans ht.2⟩) hq.2 hd
  have h2 : inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ q (tangentVector (t : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo ht.2
      (fun s hs ↦ hle q hq.1 s ⟨ht.1.trans hs.1, hs.2⟩) hq.2 hd
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul q (t : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
    hq.2, hpm, le_antisymm h1 h2]

/-- At the left endpoint parameter of a differentiable family of supporting half-planes the
contact point is the positive vertex of the reversed face. -/
theorem edgeVertices_add_pi_fst_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hlea : ∀ q ∈ (L : Set Point), m a ≤ inner ℝ q (normalVector (a : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (a : Real.Angle)) = m a)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (a : Real.Angle))) a) :
    (edgeVertices L ((a + Real.pi : ℝ) : Real.Angle)).1 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hlea hp hpm
  refine edgeVertices_fst_eq_of_tangent_isGreatest L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ p (tangentVector (a : Real.Angle)) ≤
      inner ℝ q (tangentVector (a : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

/-- At the right endpoint parameter of a differentiable family of supporting half-planes the
contact point is the negative vertex of the reversed face. -/
theorem edgeVertices_add_pi_snd_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hleb : ∀ q ∈ (L : Set Point), m b ≤ inner ℝ q (normalVector (b : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (b : Real.Angle)) = m b)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (b : Real.Angle))) b) :
    (edgeVertices L ((b + Real.pi : ℝ) : Real.Angle)).2 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hleb hp hpm
  refine edgeVertices_snd_eq_of_tangent_isLeast L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ q (tangentVector (b : Real.Angle)) ≤
      inner ℝ p (tangentVector (b : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Convex / Space
-/

public section

open scoped unitInterval Pointwise

namespace MovingSofa

/-- Convex bodies form a convex domain under Minkowski interpolation. -/
theorem convexBody_isConvexDomain : IsConvexDomain.{0, 0} convexBodyCombination := by
  let e : ConvexBody Point → C(Real.Angle, ℝ) := fun K ↦
    ⟨fun t ↦ supportValue K t, (supportFunction_minkowski_embedding K K).2.2.1⟩
  have he (t : I) (K L : ConvexBody Point) :
      e (convexBodyCombination t K L) = (1 - (t : ℝ)) • e K + (t : ℝ) • e L := by
    ext u
    change supportValue (convexBodyCombination t K L) u = _
    exact supportValue_convexBodyCombination t K L u
  refine ⟨ModuleCat.of ℝ C(Real.Angle, ℝ), e, ?_, ?_, he⟩
  · intro K L h
    apply (supportFunction_minkowski_embedding K L).2.1
    intro t
    exact congrArg (fun f : C(Real.Angle, ℝ) ↦ f t) h
  · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
    refine ⟨convexBodyCombination ⟨b, hb, by linarith⟩ K L, ?_⟩
    have h : 1 - b = a := by linarith
    simpa only [h] using he ⟨b, hb, by linarith⟩ K L

end MovingSofa

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.Foundations.Development001`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.ModuloLinear`.
* `Area.Quadratic`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Modulo Linear
-/

public section

noncomputable section

open scoped unitInterval

universe u

namespace MovingSofa

/-- The difference of two functionals preserves the specified convex combinations. -/
@[expose]
def EquivalentModuloConvexLinear {α : Type u} (c : I → α → α → α)
    (f g : α → ℝ) : Prop :=
  IsConvexLinear c realCombination (fun x ↦ f x - g x)

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Area / Quadratic
-/

public section

noncomputable section

open scoped unitInterval

universe u v

namespace MovingSofa

/-- The directional derivative along a barycentric segment is computed by any derivative of the
segment function at the base point. -/
theorem convexDirectionalDerivative_eq_of_hasDerivWithinAt {α : Type u} (c : I → α → α → α)
    (f : α → ℝ) (x y : α) {d : ℝ}
    (h : HasDerivWithinAt (segmentFunctional c f x y) d (Set.Icc 0 1) 0) :
    convexDirectionalDerivative c f x y = d :=
  h.derivWithin (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num))

/-- A quadratic diagonal has the stated segment derivative, affine in its destination. -/
theorem quadratic_directional_derivative {α : Type u} (c : I → α → α → α) (f : α → ℝ) (h : α → α →
  ℝ)
    (hh : IsConvexBilinear c c realCombination h) (hf : ∀ x, f x = h x x) :
    (∀ x y, HasDerivWithinAt (segmentFunctional c f x y)
      (h x y + h y x - 2 * h x x) (Set.Icc 0 1) 0) ∧
    (∀ x y, convexDirectionalDerivative c f x y = h x y + h y x - 2 * h x x) ∧
    ∀ x, IsConvexLinear c realCombination (fun y ↦ convexDirectionalDerivative c f x y) := by
  have hquad (t : I) (x y : α) :
      f (c t x y) =
        (1 - (t : ℝ)) ^ 2 * h x x +
          (t : ℝ) * (1 - (t : ℝ)) * (h x y + h y x) + (t : ℝ) ^ 2 * h y y := by
    rw [hf]
    have hleft := hh.2 (c t x y) t x y
    change h (c t x y) (c t x y) =
      realCombination t (h x (c t x y)) (h y (c t x y)) at hleft
    rw [hleft, hh.1 x t x y, hh.1 y t x y]
    simp only [realCombination]
    ring
  have hderiv (x y : α) : HasDerivAt
      (fun t : ℝ ↦ (1 - t) ^ 2 * h x x +
        t * (1 - t) * (h x y + h y x) + t ^ 2 * h y y)
      (h x y + h y x - 2 * h x x) 0 := by
    have hid : HasDerivAt (fun t : ℝ ↦ t) 1 0 := hasDerivAt_id 0
    have hsub : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) 0 := hid.const_sub 1
    convert (((hsub.pow 2).mul_const (h x x)).add
      ((hid.mul hsub).mul_const (h x y + h y x))).add
      ((hid.pow 2).mul_const (h y y)) using 1
    all_goals ring
  have hfirst : ∀ x y, HasDerivWithinAt (segmentFunctional c f x y)
      (h x y + h y x - 2 * h x x) (Set.Icc 0 1) 0 := by
    intro x y
    apply (hderiv x y).hasDerivWithinAt.congr
    · intro t ht
      simp only [segmentFunctional, ht, ↓reduceDIte]
      exact hquad ⟨t, ht⟩ x y
    · simp [segmentFunctional, hquad]
  refine ⟨hfirst, ?_, ?_⟩
  · exact fun x y ↦ convexDirectionalDerivative_eq_of_hasDerivWithinAt c f x y (hfirst x y)
  · intro x t y z
    unfold convexDirectionalDerivative
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) 0 :=
      uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num)
    change derivWithin (segmentFunctional c f x (c t y z)) (Set.Icc 0 1) 0 =
      realCombination t
        (derivWithin (segmentFunctional c f x y) (Set.Icc 0 1) 0)
        (derivWithin (segmentFunctional c f x z) (Set.Icc 0 1) 0)
    rw [(hfirst x (c t y z)).derivWithin huniq,
      (hfirst x y).derivWithin huniq, (hfirst x z).derivWithin huniq]
    simp only [realCombination]
    have hright := hh.2 x t y z
    change h (c t y z) x = realCombination t (h y x) (h z x) at hright
    rw [hh.1 x t y z, hright]
    simp only [realCombination]
    ring

/-- The segment function of a quadratic functional is differentiable at the base point, with the
directional derivative as its derivative. -/
theorem IsQuadraticFunctional.hasDerivWithinAt_segmentFunctional {α : Type u}
    {c : I → α → α → α} {f : α → ℝ} (hf : IsQuadraticFunctional c f)
    (x y : α) :
    HasDerivWithinAt (segmentFunctional c f x y)
      (convexDirectionalDerivative c f x y) (Set.Icc 0 1) 0 := by
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨hderiv, hderiv_eq, -⟩ := quadratic_directional_derivative c f g hg hfg
  rw [hderiv_eq x y]
  exact hderiv x y

/-- A concave quadratic functional is maximized exactly where all directional derivatives are
nonpositive. -/
theorem quadratic_maximum_iff {α : Type u} (c : I → α → α → α)
    (hc : IsConvexDomain.{u, v} c) (f : α → ℝ)
    (hq : IsQuadraticFunctional c f) (hconcave : IsConvexFunctional c f true) (x : α) :
    (∀ y, f y ≤ f x) ↔ ∀ y, convexDirectionalDerivative c f x y ≤ 0 := by
  obtain ⟨g, hg, hfg⟩ := hq
  obtain ⟨hderiv, hderiv_eq, -⟩ :=
    quadratic_directional_derivative c f g hg hfg
  obtain ⟨V, e, he, -, hcmap⟩ := hc
  have hc0 (z : α) : c 0 x z = x := by
    apply he
    rw [hcmap]
    simp
  have hquad (t : I) (y : α) :
      f (c t x y) =
        (1 - (t : ℝ)) ^ 2 * g x x +
          (t : ℝ) * (1 - (t : ℝ)) * (g x y + g y x) +
            (t : ℝ) ^ 2 * g y y := by
    rw [hfg]
    have hleft := hg.2 (c t x y) t x y
    change g (c t x y) (c t x y) =
      realCombination t (g x (c t x y)) (g y (c t x y)) at hleft
    rw [hleft, hg.1 x t x y, hg.1 y t x y]
    simp only [realCombination]
    ring
  constructor
  · intro hmax y
    have hlocal : IsLocalMaxOn (segmentFunctional c f x y) (Set.Icc 0 1) 0 :=
      by
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [segmentFunctional, ht, ↓reduceDIte, Set.mem_Icc, Std.le_refl, zero_le_one,
          and_self,
          Set.Icc.mk_zero, hc0]
        exact hmax _
    have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc 0 1) 0 := by
      simpa using sub_mem_posTangentConeAt_of_segment_subset
        (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by rw [segment_eq_Icc (by norm_num)])
    have := hlocal.hasFDerivWithinAt_nonpos (hderiv x y).hasFDerivWithinAt htangent
    simpa [hderiv_eq] using this
  · intro hd y
    have hmid := hconcave (⟨1 / 2, by constructor <;> norm_num⟩ : I) x y
    simp only [↓reduceIte, realCombination] at hmid
    rw [hquad, hfg x, hfg y] at hmid
    have hcoef : g x x - g x y - g y x + g y y ≤ 0 := by
      norm_num at hmid ⊢
      linarith
    have := hd y
    rw [hderiv_eq x y] at this
    rw [hfg y, hfg x]
    linarith

/-- A sum of quadratic functionals is quadratic. -/
theorem IsQuadraticFunctional.add {α : Type u} {c : I → α → α → α} {f g : α → ℝ}
    (hf : IsQuadraticFunctional c f) (hg : IsQuadraticFunctional c g) :
    IsQuadraticFunctional c (fun x ↦ f x + g x) := by
  obtain ⟨F, ⟨hFright, hFleft⟩, hFf⟩ := hf
  obtain ⟨G, ⟨hGright, hGleft⟩, hGg⟩ := hg
  refine ⟨fun x y ↦ F x y + G x y, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change F x (c t y z) + G x (c t y z) = realCombination t (F x y + G x y) (F x z + G x z)
    rw [hFright x t y z, hGright x t y z]
    simp only [realCombination]
    ring
  · have hF : F (c t x y) z = realCombination t (F x z) (F y z) := hFleft z t x y
    have hG : G (c t x y) z = realCombination t (G x z) (G y z) := hGleft z t x y
    change F (c t x y) z + G (c t x y) z = realCombination t (F x z + G x z) (F y z + G y z)
    rw [hF, hG]
    simp only [realCombination]
    ring
  · change f x + g x = F x x + G x x
    rw [hFf x, hGg x]

/-- A sum of convex functionals is convex, and a sum of concave functionals is concave. -/
theorem IsConvexFunctional.add {α : Type u} {c : I → α → α → α} {f g : α → ℝ} {concave : Bool}
    (hf : IsConvexFunctional c f concave) (hg : IsConvexFunctional c g concave) :
    IsConvexFunctional c (fun x ↦ f x + g x) concave := by
  intro t x y
  have hsum : ∀ u v w z : ℝ, realCombination t u v + realCombination t w z =
      realCombination t (u + w) (v + z) := by
    intro u v w z
    simp only [realCombination]
    ring
  cases concave
  · have hfxy : f (c t x y) ≤ realCombination t (f x) (f y) := hf t x y
    have hgxy : g (c t x y) ≤ realCombination t (g x) (g y) := hg t x y
    change f (c t x y) + g (c t x y) ≤ realCombination t (f x + g x) (f y + g y)
    rw [← hsum]
    exact add_le_add hfxy hgxy
  · have hfxy : realCombination t (f x) (f y) ≤ f (c t x y) := hf t x y
    have hgxy : realCombination t (g x) (g y) ≤ g (c t x y) := hg t x y
    change realCombination t (f x + g x) (f y + g y) ≤ f (c t x y) + g (c t x y)
    rw [← hsum]
    exact add_le_add hfxy hgxy

/-- A convex-linear real functional satisfies both barycentric inequalities, with equality. -/
theorem IsConvexLinear.isConvexFunctional {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsConvexLinear c realCombination f) (concave : Bool) :
    IsConvexFunctional c f concave := by
  intro t x y
  cases concave
  · change f (c t x y) ≤ realCombination t (f x) (f y)
    exact (hf t x y).le
  · change realCombination t (f x) (f y) ≤ f (c t x y)
    exact (hf t x y).ge

/-- A convex-linear real functional is quadratic: it is the diagonal of the mean of its values. -/
theorem IsConvexLinear.isQuadraticFunctional {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsConvexLinear c realCombination f) : IsQuadraticFunctional c f := by
  refine ⟨fun x y ↦ (f x + f y) / 2, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change (f x + f (c t y z)) / 2 = realCombination t ((f x + f y) / 2) ((f x + f z) / 2)
    rw [hf t y z]
    simp only [realCombination]
    ring
  · change (f (c t x y) + f z) / 2 = realCombination t ((f x + f z) / 2) ((f y + f z) / 2)
    rw [hf t x y]
    simp only [realCombination]
    ring
  · change f x = (f x + f x) / 2
    ring

/-- Negation exchanges convexity and concavity. -/
theorem IsConvexFunctional.neg {α : Type u} {c : I → α → α → α} {f : α → ℝ} {concave : Bool}
    (hf : IsConvexFunctional c f concave) : IsConvexFunctional c (fun x ↦ -f x) (!concave) := by
  intro t x y
  have hneg : realCombination t (-f x) (-f y) = -realCombination t (f x) (f y) := by
    simp only [realCombination]
    ring
  cases concave
  · have h : f (c t x y) ≤ realCombination t (f x) (f y) := hf t x y
    change realCombination t (-f x) (-f y) ≤ -f (c t x y)
    rw [hneg]
    exact neg_le_neg h
  · have h : realCombination t (f x) (f y) ≤ f (c t x y) := hf t x y
    change -f (c t x y) ≤ realCombination t (-f x) (-f y)
    rw [hneg]
    exact neg_le_neg h

/-- The negative of a quadratic functional is quadratic. -/
theorem IsQuadraticFunctional.neg {α : Type u} {c : I → α → α → α} {f : α → ℝ}
    (hf : IsQuadraticFunctional c f) : IsQuadraticFunctional c (fun x ↦ -f x) := by
  obtain ⟨F, ⟨hFright, hFleft⟩, hFf⟩ := hf
  have hneg : ∀ (t : I) (u v : ℝ), -realCombination t u v = realCombination t (-u) (-v) := by
    intro t u v
    simp only [realCombination]
    ring
  refine ⟨fun x y ↦ -F x y, ⟨fun x t y z ↦ ?_, fun z t x y ↦ ?_⟩, fun x ↦ ?_⟩
  · change -F x (c t y z) = realCombination t (-F x y) (-F x z)
    rw [hFright x t y z, hneg]
  · have hF : F (c t x y) z = realCombination t (F x z) (F y z) := hFleft z t x y
    change -F (c t x y) z = realCombination t (-F x z) (-F y z)
    rw [hF, hneg]
  · change -f x = -F x x
    rw [hFf x]

end MovingSofa

end

end

end

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Foundations.Development002`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Geometry.Convex.FrontierInterior`.
* `Geometry.RadialBoundary`.
-/

public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Convex / Frontier Interior
-/

public section

open Set
open scoped Topology

namespace MovingSofa

/-- A bounded component of the frontier complement that meets the set lies in its interior. -/
lemma connectedComponentIn_compl_frontier_subset_interior {s : Set Point}
    (hs : IsClosed s) {p : Point} (hp : p ∈ interior s) :
    connectedComponentIn (frontier s)ᶜ p ⊆ interior s := by
  have hsub : connectedComponentIn (frontier s)ᶜ p ⊆ interior s ∪ sᶜ := by
    intro q hq
    have hq' := connectedComponentIn_subset (frontier s)ᶜ p hq
    simp only [frontier, hs.closure_eq, mem_compl_iff, mem_sdiff, not_and_or,
      not_not] at hq'
    exact hq'.symm
  rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      hs.isOpen_compl (disjoint_left.mpr (fun _ hx hy ↦ hy (interior_subset hx))) hsub with h | h
  · exact h
  · have hp' : p ∈ (frontier s)ᶜ := by
      simp only [frontier, hs.closure_eq, mem_compl_iff, mem_sdiff, not_and_or,
        not_not]
      exact Or.inr hp
    exact False.elim ((h (mem_connectedComponentIn hp')) (interior_subset hp))

/-- The interior of a bounded closed set lies in the bounded component of its frontier complement.
-/
lemma interior_subset_jordanInterior_frontier {s : Set Point}
    (hs : IsClosed s) (hb : Bornology.IsBounded s) :
    interior s ⊆ jordanInterior (frontier s) := by
  intro p hp
  refine ⟨?_, hb.subset ((connectedComponentIn_compl_frontier_subset_interior hs hp).trans
    interior_subset)⟩
  intro hfront
  exact hfront.2 hp

/-- The outward ray from a point outside a convex set remains outside the set. -/
lemma ray_smul_sub_notMem {s : Set Point} (hs : Convex ℝ s)
    {o p : Point} (ho : o ∈ s) (hp : p ∉ s) {r : ℝ} (hr : 1 ≤ r) :
    o + r • (p - o) ∉ s := by
  intro hq
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h := (hs.starConvex ho).add_smul_sub_mem hq
    (inv_nonneg.mpr hrpos.le) (inv_le_one_of_one_le₀ hr)
  have heq : o + r⁻¹ • (o + r • (p - o) - o) = p := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    abel
  exact hp (heq ▸ h)

/-- Every exterior point of a nonempty bounded closed convex set has an unbounded component outside
its frontier. -/
lemma exterior_component_unbounded {s : Set Point} (hs : Convex ℝ s)
    (hclosed : IsClosed s) {o p : Point} (ho : o ∈ s) (hp : p ∉ s) :
    ¬ Bornology.IsBounded (connectedComponentIn (frontier s)ᶜ p) := by
  let f : ℝ → Point := fun r ↦ o + r • (p - o)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hpre : IsPreconnected (f '' Set.Ici 1) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hsub : f '' Set.Ici 1 ⊆ (frontier s)ᶜ := by
    rintro q ⟨r, hr, rfl⟩ hq
    exact ray_smul_sub_notMem hs ho hp hr (hclosed.closure_eq ▸ hq.1)
  have hpmem : p ∈ f '' Set.Ici 1 := ⟨1, by simp, by simp [f]⟩
  have hcomp := hpre.subset_connectedComponentIn hpmem hsub
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hnorm : 0 < ‖p - o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro h; exact hp (h ▸ ho)))
  let r := max 1 ((C + ‖o‖ + 1) / ‖p - o‖)
  have hr : 1 ≤ r := le_max_left _ _
  have hq := hC (f r) (hcomp ⟨r, hr, rfl⟩)
  have hdiff : ‖r • (p - o)‖ ≤ C + ‖o‖ := by
    calc
      ‖r • (p - o)‖ = ‖f r - o‖ := by simp [f]
      _ ≤ ‖f r‖ + ‖o‖ := norm_sub_le _ _
      _ ≤ C + ‖o‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r)] at hdiff
  have hlower := (div_le_iff₀ hnorm).mp (le_max_right 1 ((C + ‖o‖ + 1) / ‖p - o‖))
  change C + ‖o‖ + 1 ≤ r * ‖p - o‖ at hlower
  linarith

/-- The bounded complementary region of a nonempty compact convex set frontier is its interior. -/
lemma jordanInterior_frontier_eq_interior {s : Set Point} (hs : Convex ℝ s)
    (hclosed : IsClosed s) (hb : Bornology.IsBounded s) (hne : s.Nonempty) :
    jordanInterior (frontier s) = interior s := by
  apply Set.Subset.antisymm
  · intro p hp
    have hps : p ∈ s := by
      by_contra hnot
      obtain ⟨o, ho⟩ := hne
      exact exterior_component_unbounded hs hclosed ho hnot hp.2
    by_contra hnot
    exact hp.1 ⟨subset_closure hps, hnot⟩
  · exact interior_subset_jordanInterior_frontier hclosed hb

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Radial Boundary
-/

public section

noncomputable section

namespace MovingSofa

theorem convexBody_radial_boundary (K : ConvexBody Point) (o : Point)
    (ho : o ∈ interior (K : Set Point)) :
    ∃ (ρ : Point → ℝ)
      (e : {u : Point | ‖u‖ = 1} ≃ₜ ↥(frontier (K : Set Point)))
      (C : NNReal) (γ : ContinuousBVPaths 0 (2 * Real.pi)),
      (∀ u : Point, ‖u‖ = 1 →
        0 < ρ u ∧ o + ρ u • u ∈ frontier (K : Set Point) ∧
        ∀ r : ℝ, 0 < r → o + r • u ∈ frontier (K : Set Point) → r = ρ u) ∧
      (∀ u : {u : Point | ‖u‖ = 1}, (e u : Point) = o + ρ u • (u : Point)) ∧
      LipschitzWith C (fun u ↦ (e u : Point)) ∧
      (∀ t : Set.Icc (0 : ℝ) (2 * Real.pi),
        γ.val t = o + ρ (normalVector ((t : ℝ) : Real.Angle)) •
          normalVector ((t : ℝ) : Real.Angle)) ∧
      IsOrientedJordanParametrization (by positivity)
        (frontier (K : Set Point)) true γ.val ∧
      jordanInterior (frontier (K : Set Point)) = interior (K : Set Point) := by
  obtain ⟨ρ, e, C, hρ, he, hC⟩ := exists_radial_homeomorph K.convex K.isCompact.isBounded o ho
  let f := fun u ↦ (e u : Point)
  let γ := radialBVLoop f hC
  have hrange : Set.range γ.val = frontier (K : Set Point) := by
    rw [range_radialBVLoop]
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact (e u).property
    · intro hp
      obtain ⟨u, hu⟩ := e.surjective ⟨p, hp⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  have hclosed := radialBVLoop_closed f hC
  have hinj := radialBVLoop_injOn f hC (Subtype.val_injective.comp e.injective)
  have hformula (t : Set.Icc (0 : ℝ) (2 * Real.pi)) : γ.val t =
      o + ρ (normalVector ((t : ℝ) : Real.Angle)) • normalVector ((t : ℝ) : Real.Angle) := by
    rw [radialBVLoop_apply]
    exact he _
  have hinter := jordanInterior_frontier_eq_interior K.convex K.isCompact.isClosed
    K.isCompact.isBounded K.nonempty
  have hwcenter : curveWinding (by positivity) γ.val o = 1 := by
    have hx := funext hformula
    rw [hx]
    exact curveWinding_radial_center o _ (fun t ↦ (hρ _ (norm_normalVector_real t)).1)
  let : PreconnectedSpace ↥(interior (K : Set Point)) :=
    Subtype.preconnectedSpace K.convex.interior.isPreconnected
  have hlc : IsLocallyConstant
      (fun p : ↥(interior (K : Set Point)) ↦ curveWinding (by positivity) γ.val p.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro p
    have hp : p.val ∉ Set.range γ.val := by
      rw [hrange]
      exact fun h ↦ h.2 p.property
    obtain ⟨U, hU, hpU, hUeq⟩ :=
      curveWinding_locally_constant_off_range (by positivity) γ.property.1 hclosed hp
    exact ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hpU,
      fun q hq ↦ hUeq q.val hq⟩
  refine ⟨ρ, e, C, γ, hρ, he, hC, hformula, ?_, hinter⟩
  refine ⟨by positivity, isJordanCurve_of_unitSphere_homeomorph e,
    γ.property.1, hrange, hclosed, hinj, ?_⟩
  intro p hp
  rw [hinter] at hp
  exact (hlc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨o, ho⟩).trans hwcenter

end MovingSofa

end

end

end

end

end

end

end

end

end
