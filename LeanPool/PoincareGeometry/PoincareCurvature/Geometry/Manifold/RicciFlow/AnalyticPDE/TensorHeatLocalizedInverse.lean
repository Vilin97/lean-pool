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

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoordinatePerturbation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteLocalizedCoefficients

/-!
# Local tensor-heat inversion after cutoff and parabolic rescaling

This file closes the quantitative localization step in the tensor-heat
parametrix.  A normalized cutoff freezes the principal coefficient away from
the chart core, while parabolic rescaling gives weights `|r|`, `|r|`, and
`r²` to the principal oscillation, first-order term, and zeroth-order term.
Consequently the coordinate error tends to zero with the chart radius, so a
genuine local right inverse exists for every sufficiently small nonzero
radius.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

@[reducible] local instance localizedInverseFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localizedInverseFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance localizedInverseSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localizedInverseSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance localizedInversePrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localizedInversePrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance localizedInverseFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localizedInverseFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

/-- Quantitative all-space coefficient data used in a single rescaled chart. -/
structure TensorHeatLocalizedCoefficientData (X W : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] where
  cutoff : X → ℝ
  principal : X → ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
  first : X → ((X →L[ℝ] W) →L[ℝ] W)
  zero : X → (W →L[ℝ] W)
  center : X
  cutoffBound : ℝ
  cutoffLipschitz : ℝ
  supportRadius : ℝ
  principalLipschitz : ℝ
  firstBound : ℝ
  firstLipschitz : ℝ
  zeroBound : ℝ
  zeroLipschitz : ℝ
  cutoffBound_nonneg : 0 ≤ cutoffBound
  cutoffLipschitz_nonneg : 0 ≤ cutoffLipschitz
  supportRadius_nonneg : 0 ≤ supportRadius
  principalLipschitz_nonneg : 0 ≤ principalLipschitz
  firstBound_nonneg : 0 ≤ firstBound
  firstLipschitz_nonneg : 0 ≤ firstLipschitz
  zeroBound_nonneg : 0 ≤ zeroBound
  zeroLipschitz_nonneg : 0 ≤ zeroLipschitz
  norm_cutoff_le : ∀ x, |cutoff x| ≤ cutoffBound
  cutoff_lipschitz : ∀ x y,
    |cutoff x - cutoff y| ≤ cutoffLipschitz * dist x y
  support_radius : ∀ x, cutoff x ≠ 0 → ‖x‖ ≤ supportRadius
  principal_lipschitz : ∀ x y,
    ‖principal x - principal y‖ ≤ principalLipschitz * dist x y
  norm_first_le : ∀ x, ‖first x‖ ≤ firstBound
  first_lipschitz : ∀ x y,
    ‖first x - first y‖ ≤ firstLipschitz * dist x y
  norm_zero_le : ∀ x, ‖zero x‖ ≤ zeroBound
  zero_lipschitz : ∀ x y,
    ‖zero x - zero y‖ ≤ zeroLipschitz * dist x y

namespace TensorHeatLocalizedCoefficientData

variable (D : TensorHeatLocalizedCoefficientData X W)

/-- Cutoff-localized principal coefficient on the normalized cylinder. -/
def principalField {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ) :=
  FiniteParabolicC2AlphaBanach.finiteLocalizedPrincipalCoefficient
    (t₀ := t₀) (T := T)
    D.cutoffBound_nonneg D.cutoffLipschitz_nonneg
    D.principalLipschitz_nonneg D.supportRadius_nonneg
    hα hα1.le D.cutoff D.principal D.center r
    D.norm_cutoff_le D.cutoff_lipschitz D.support_radius D.principal_lipschitz

/-- Cutoff-localized first-order coefficient with its parabolic weight. -/
def firstField {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ) :=
  FiniteParabolicC2AlphaBanach.finiteLocalizedFirstCoefficient
    (t₀ := t₀) (T := T)
    D.cutoffBound_nonneg D.cutoffLipschitz_nonneg
    D.firstBound_nonneg D.firstLipschitz_nonneg
    hα hα1.le D.cutoff D.first D.center r
    D.norm_cutoff_le D.cutoff_lipschitz D.norm_first_le D.first_lipschitz

/-- Cutoff-localized zeroth-order coefficient with its parabolic weight. -/
def zeroField {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ) :=
  FiniteParabolicC2AlphaBanach.finiteLocalizedZeroCoefficient
    (t₀ := t₀) (T := T)
    D.cutoffBound_nonneg D.cutoffLipschitz_nonneg
    D.zeroBound_nonneg D.zeroLipschitz_nonneg
    hα hα1.le D.cutoff D.zero D.center r
    D.norm_cutoff_le D.cutoff_lipschitz D.norm_zero_le D.zero_lipschitz

/-- On the region where the normalized cutoff is one, the localized
principal coefficient is exactly the centered-rescaled coefficient. -/
theorem toFun_principalField_of_cutoff_eq_one
    {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ)
    (z : ℝ × X) (hcut : D.cutoff z.2 = 1) :
    ParabolicC0AlphaSpace.toFun
        (D.principalField (t₀ := t₀) (T := T) hα hα1 r) z =
      D.principal (D.center + r • z.2) := by
  simp [principalField, hcut]

/-- On the cutoff-one region, the localized first-order coefficient is
exactly the parabolically weighted centered-rescaled coefficient. -/
theorem toFun_firstField_of_cutoff_eq_one
    {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ)
    (z : ℝ × X) (hcut : D.cutoff z.2 = 1) :
    ParabolicC0AlphaSpace.toFun
        (D.firstField (t₀ := t₀) (T := T) hα hα1 r) z =
      r • D.first (D.center + r • z.2) := by
  simp [firstField, hcut]

/-- On the cutoff-one region, the localized zeroth-order coefficient is
exactly the parabolically weighted centered-rescaled coefficient. -/
theorem toFun_zeroField_of_cutoff_eq_one
    {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ)
    (z : ℝ × X) (hcut : D.cutoff z.2 = 1) :
    ParabolicC0AlphaSpace.toFun
        (D.zeroField (t₀ := t₀) (T := T) hα hα1 r) z =
      r ^ 2 • D.zero (D.center + r • z.2) := by
  simp [zeroField, hcut]

/-- Explicit scalar majorant for the post-frozen coordinate error. -/
def errorMajorant {t₀ T α : ℝ}
    (Q : ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach X W t₀ T α)
    (r : ℝ) : ℝ :=
  ‖operatorEvaluation (X →L[ℝ] X →L[ℝ] W) W‖ *
      (|r| * (3 * D.cutoffBound * D.principalLipschitz * D.supportRadius +
        D.cutoffBound * D.principalLipschitz +
        D.cutoffLipschitz * D.principalLipschitz * D.supportRadius)) *
      ‖FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL.comp Q‖ +
    ‖operatorEvaluation (X →L[ℝ] W) W‖ *
      (|r| * (3 * D.cutoffBound * D.firstBound +
        D.cutoffBound * D.firstLipschitz * |r| +
        D.cutoffLipschitz * D.firstBound)) *
      ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL.comp Q‖ +
    ‖operatorEvaluation W W‖ *
      (r ^ 2 * (3 * D.cutoffBound * D.zeroBound +
        D.cutoffBound * D.zeroLipschitz * |r| +
        D.cutoffLipschitz * D.zeroBound)) *
      ‖FiniteParabolicC2AlphaBanach.valueComponentL.comp Q‖

@[simp] theorem errorMajorant_zero {t₀ T α : ℝ}
    (Q : ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach X W t₀ T α) :
    D.errorMajorant Q 0 = 0 := by
  simp [errorMajorant]

theorem continuous_errorMajorant {t₀ T α : ℝ}
    (Q : ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach X W t₀ T α) :
    Continuous (D.errorMajorant Q) := by
  unfold errorMajorant
  fun_prop

/-- The explicit localization error is below one throughout some punctured
neighborhood of radius zero. -/
theorem exists_radius_errorMajorant_lt_one {t₀ T α : ℝ}
    (Q : ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach X W t₀ T α) :
    ∃ δ > 0, ∀ r : ℝ, |r| < δ → D.errorMajorant Q r < 1 := by
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ), D.errorMajorant Q r < 1 := by
    have hlim : Tendsto (D.errorMajorant Q) (𝓝 (0 : ℝ))
        (𝓝 (D.errorMajorant Q 0)) :=
      (D.continuous_errorMajorant Q).continuousAt
    have hiio : Iio (1 : ℝ) ∈ 𝓝 (D.errorMajorant Q 0) := by
      rw [D.errorMajorant_zero Q]
      exact Iio_mem_nhds (by norm_num)
    exact hlim hiio
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨δ, hδ, hball⟩ := hevent
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  exact hball (by simpa [Real.dist_eq] using hr)

end TensorHeatLocalizedCoefficientData

/-! ## Genuine frozen tensor heat -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

variable {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)

/-- The actual componentwise coordinate error is bounded by the explicit
radius-dependent majorant. -/
theorem localizedCoordinatePostErrorBound_le_errorMajorant
    {t₀ T α : ℝ} (hα : 0 < α) (hα1 : α < 1) (r : ℝ)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (Q : ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    tensorHeatCoordinatePostErrorBound
        (D.principalField hα hα1 r)
        (ParabolicC0AlphaSpace.constL
          (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
          (D.principal D.center))
        (D.firstField hα hα1 r) (D.zeroField hα hα1 r) Q ≤
      D.errorMajorant Q r := by
  unfold tensorHeatCoordinatePostErrorBound
    TensorHeatLocalizedCoefficientData.errorMajorant
  gcongr
  · exact FiniteParabolicC2AlphaBanach.norm_finiteLocalizedPrincipalCoefficient_sub_frozen_le
      D.cutoffBound_nonneg D.cutoffLipschitz_nonneg
      D.principalLipschitz_nonneg D.supportRadius_nonneg hα hα1.le
      D.cutoff D.principal D.center r D.norm_cutoff_le D.cutoff_lipschitz
      D.support_radius D.principal_lipschitz
  · exact FiniteParabolicC2AlphaBanach.norm_finiteLocalizedFirstCoefficient_le
      D.cutoffBound_nonneg D.cutoffLipschitz_nonneg D.firstBound_nonneg
      D.firstLipschitz_nonneg hα hα1.le D.cutoff D.first D.center r
      D.norm_cutoff_le D.cutoff_lipschitz D.norm_first_le D.first_lipschitz
  · exact FiniteParabolicC2AlphaBanach.norm_finiteLocalizedZeroCoefficient_le
      D.cutoffBound_nonneg D.cutoffLipschitz_nonneg D.zeroBound_nonneg
      D.zeroLipschitz_nonneg hα hα1.le D.cutoff D.zero D.center r
      D.norm_cutoff_le D.cutoff_lipschitz D.norm_zero_le D.zero_lipschitz

/-- A localized coordinate tensor-heat operator has an exact bounded right
inverse whenever its explicit radius-dependent error majorant is below one. -/
theorem exists_localizedTensorHeatSolutionL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x)
    (r : ℝ)
    (hsmall : D.errorMajorant
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) r < 1) :
    ∃ Q : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL
        (D.principalField hα hα1 r) (D.firstField hα hα1 r)
        (D.zeroField hα hα1 r)).comp Q =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T)) := by
  have hfreeze : ParabolicC0AlphaSpace.constL
      (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
      (D.principal D.center) =
      frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α := by
    simp [frozenTensorHeatPrincipalField, hcenter]
  apply exists_localTensorHeatSolutionL_of_coordinate_bound_lt_one
    (I := I) p e b hxFrame hxChart hT hα hα1
  rw [← hfreeze]
  exact lt_of_le_of_lt
    (localizedCoordinatePostErrorBound_le_errorMajorant hα hα1 r D _) hsmall

/-- Localized solvability with the Cauchy condition retained: the selected
right inverse is annihilated by the canonical initial-trace operator. -/
theorem exists_localizedTensorHeatSolutionL_zeroTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x)
    (r : ℝ)
    (hsmall : D.errorMajorant
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) r < 1) :
    ∃ Q : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL
        (D.principalField hα hα1 r) (D.firstField hα hα1 r)
        (D.zeroField hα hα1 r)).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W₂ α
              (parabolicFiniteCylinder E t₀ T)) ∧
      (FiniteParabolicC2AlphaBanach.initialTraceL
        (X := E) (E := W₂) hT hα).comp Q = 0 := by
  have hfreeze : ParabolicC0AlphaSpace.constL
      (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
      (D.principal D.center) =
      frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α := by
    simp [frozenTensorHeatPrincipalField, hcenter]
  apply exists_localTensorHeatSolutionL_of_coordinate_bound_lt_one_zeroTrace
    (I := I) p e b hxFrame hxChart hT hα hα1
  rw [← hfreeze]
  exact lt_of_le_of_lt
    (localizedCoordinatePostErrorBound_le_errorMajorant hα hα1 r D _) hsmall

/-- **Small-radius local tensor-heat solvability.**  Every sufficiently small
positive rescaling radius yields an exact bounded local solution operator. -/
theorem exists_radius_localizedTensorHeatSolutionL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∃ Q : ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T) →L[ℝ]
          FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL
          (D.principalField hα hα1 r) (D.firstField hα hα1 r)
          (D.zeroField hα hα1 r)).comp Q =
        ContinuousLinearMap.id ℝ
          (ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T)) := by
  obtain ⟨δ, hδ, hsmall⟩ := D.exists_radius_errorMajorant_lt_one
    (frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ
  apply exists_localizedTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter r
  exact hsmall r (by simpa [abs_of_pos hr] using hrδ)

/-- Small-radius localized solvability with both the equation and zero
canonical initial trace returned as operator identities. -/
theorem exists_radius_localizedTensorHeatSolutionL_zeroTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∃ Q : ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T) →L[ℝ]
          FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL
          (D.principalField hα hα1 r) (D.firstField hα hα1 r)
          (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
        (FiniteParabolicC2AlphaBanach.initialTraceL
          (X := E) (E := W₂) hT hα).comp Q = 0 := by
  obtain ⟨δ, hδ, hsmall⟩ := D.exists_radius_errorMajorant_lt_one
    (frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ
  apply exists_localizedTensorHeatSolutionL_zeroTrace
    (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter r
  exact hsmall r (by simpa [abs_of_pos hr] using hrδ)

/-- Small-radius localized solvability for arbitrary initial data represented
by a higher-parabolic extension.  The solution has the requested forcing,
retains the extension's canonical trace, and obeys the direct affine
Schauder estimate. -/
theorem exists_radius_localizedTensorHeatSolution_with_initialTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
      ∃ Q : ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T) →L[ℝ]
          FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL
          (D.principalField hα hα1 r) (D.firstField hα hα1 r)
          (D.zeroField hα hα1 r)).comp Q =
            ContinuousLinearMap.id ℝ
              (ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T)) ∧
        (FiniteParabolicC2AlphaBanach.initialTraceL
          (X := E) (E := W₂) hT hα).comp Q = 0 ∧
        ∀ (h : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
          (q : ParabolicC0AlphaBanach E W₂ α
            (parabolicFiniteCylinder E t₀ T)),
          ∃ u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
            FiniteParabolicC2AlphaBanach.coordinateCauchyL
                (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                (D.zeroField hα hα1 r) u = q ∧
            FiniteParabolicC2AlphaBanach.initialTraceL hT hα u =
              FiniteParabolicC2AlphaBanach.initialTraceL hT hα h ∧
            ‖u‖ ≤ ‖h‖ + ‖Q‖ *
              ‖q - FiniteParabolicC2AlphaBanach.coordinateCauchyL
                (D.principalField hα hα1 r) (D.firstField hα hα1 r)
                (D.zeroField hα hα1 r) h‖ := by
  obtain ⟨δ, hδ, hsolve⟩ :=
    exists_radius_localizedTensorHeatSolutionL_zeroTrace
      (I := I) p e b hxFrame hxChart hT hα hα1 D hcenter
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ
  obtain ⟨Q, hPQ, htrace⟩ := hsolve r hr hrδ
  refine ⟨Q, hPQ, htrace, ?_⟩
  intro h q
  exact LinearParabolicParametrix.exists_solution_with_trace_of_rightInverse_zeroTrace
    (FiniteParabolicC2AlphaBanach.initialTraceL hT hα)
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL
      (D.principalField hα hα1 r) (D.firstField hα hα1 r)
      (D.zeroField hα hα1 r)) Q hPQ htrace h q

end AnalyticPDE
end RicciFlow
