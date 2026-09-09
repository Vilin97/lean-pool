/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderReflection
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure

@[expose] public section

/-! Reflection invariance of the concrete lifted-gradient space and pressure solve. -/

noncomputable section

namespace EulerGradientReflection

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerLiftedPressure EulerCylinderReflection EulerSpatialSobolevInverse
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Reflecting a genuine smooth test gradient gives the negative gradient
of the reflected scalar test. -/
theorem reflection_testGradient (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    reflection period (testGradientLp period κ m φ hφ) =
      -testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)
        := by
  apply Lp.ext
  filter_upwards [reflection_ae period (testGradientLp period κ m φ hφ),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (testGradientLp_ae period κ m φ
      hφ),
    Lp.coeFn_neg (testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected
      period φ hφ)),
    testGradientLp_ae period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3]
  change liftedGradient period κ m φ (-x) =
    -(testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)
      x)
  rw [h4, liftedGradient_reflected period κ m φ hφ.2 x, neg_neg]

/-- Reflection preserves the closure of the span of actual test gradients. -/
theorem gradientSpace_reflection_mem (κ : ℝ) (m : Vector3) {g : LiftL2 period}
    (hg : g ∈ gradientSpace period κ m) : reflection period g ∈ gradientSpace period κ m := by
  let R := (reflection period).toContinuousLinearMap
  have hspan : Submodule.span ℝ
      {f : LiftL2 period | ∃ φ : LiftDomain period → ℝ,
        (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) ∧
        f =ᵐ[liftMeasure period] liftedGradient period κ m φ} ≤
      (gradientSpace period κ m).comap R.toLinearMap := by
    apply Submodule.span_le.2
    rintro f ⟨φ, hφ, hf⟩
    have heq : f = testGradientLp period κ m φ hφ := Lp.ext (hf.trans (testGradientLp_ae period κ m
      φ hφ).symm)
    change reflection period f ∈ gradientSpace period κ m
    rw [heq, reflection_testGradient]
    exact (gradientSpace period κ m).neg_mem (testGradient_mem period κ m
      (testGradientLp_mem_generators period κ m (reflectedTest period φ)
        (smoothCompactTest_reflected period φ hφ)))
  have hclosed : IsClosed ((gradientSpace period κ m).comap R.toLinearMap : Set (LiftL2 period)) :=
    (gradientSpace_closed period κ m).preimage R.continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hg

/-- Reflection maps the concrete lifted-gradient subspace onto itself. -/
theorem gradientSpace_map_reflection (κ : ℝ) (m : Vector3) :
    (gradientSpace period κ m).map (reflection period).toLinearMap = gradientSpace period κ m := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact gradientSpace_reflection_mem period κ m hf
  · intro g hg
    exact ⟨reflection period g, gradientSpace_reflection_mem period κ m hg, reflection_involutive
      period g⟩

/-- The genuine orthogonal gradient projection commutes with joint reflection. -/
theorem gradientProjection_reflection (κ : ℝ) (m : Vector3) (f : LiftL2 period) :
    reflection period (gradientProjection period κ m f) = gradientProjection period κ m (reflection
      period f) := by
  have hmap := gradientSpace_map_reflection period κ m
  let : ((gradientSpace period κ m).map (reflection period).toLinearMap).HasOrthogonalProjection :=
    by
    rw [hmap]
    infer_instance
  simpa only [gradientProjection, hmap] using
    (reflection period).map_starProjection (gradientSpace period κ m) f

/-- The actual weak divergence-free constraint is preserved by reflection. -/
theorem divergenceFreeSpace_reflection_mem (κ : ℝ) (m : Vector3) {f : LiftL2 period}
    (hf : f ∈ divergenceFreeSpace period κ m) : reflection period f ∈ divergenceFreeSpace period κ
      m := by
  have hz : gradientProjection period κ m f = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (gradientSpace period κ m)).mpr hf
  apply (Submodule.starProjection_apply_eq_zero_iff (gradientSpace period κ m)).mp
  change gradientProjection period κ m (reflection period f) = 0
  rw [← gradientProjection_reflection, hz, map_zero]

/-- An even coefficient field commutes with the actual reflection isometry. -/
theorem coefficientOperator_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (f : LiftL2 period) :
    reflection period (A.operator f) = A.operator (reflection period f) := by
  apply Lp.ext
  filter_upwards [reflection_ae period (A.operator f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (A.operator_ae f),
    A.operator_ae (reflection period f), reflection_ae period f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, hA]

/-- Uniqueness of the concrete coercive pressure inverse proves its
reflection covariance for the actual even metric. -/
theorem pressure_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v,v⟫_ℝ) (f : LiftL2 period) :
    reflection period (A.pressure κ m c hc hpos f) =
      A.pressure κ m c hc hpos (reflection period f) := by
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
  · exact gradientSpace_reflection_mem period κ m
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f)
  · change gradientProjection period κ m (A.operator (reflection period (A.pressure κ m c hc hpos
    f))) = _
    rw [← coefficientOperator_reflection period A hA, ← gradientProjection_reflection]
    have he := liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c
      hc hpos f
    change gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos f)) =
      gradientProjection period κ m f at he
    rw [he, gradientProjection_reflection]

end EulerGradientReflection
