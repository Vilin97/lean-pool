/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteAtlas
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteLowerOrder

/-!
# Uniform short-time restriction of the tensor-heat atlas inverse

The local atlas inverse is constructed once on `(t₀,T]`.  This file shows
that it can be reused on every shorter cylinder `(t₀,S]`: extend the short
forcing by the canonical clamped extension, apply the original inverse, and
restrict the resulting genuine second jet back to `S`.

The resulting inverse remains an exact zero-trace right inverse for the
restricted coordinate operator.  Its norm is bounded by three times the
original inverse norm, independently of `S`.  This removes the circularity
that would arise from rebuilding the local inverse after choosing a thin
time horizon.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ S T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)

@[reducible] local instance shortAtlasFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W₂) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortAtlasFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W₂) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance shortAtlasHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortAtlasHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W₂) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance shortAtlasPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortAtlasPrincipalNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance shortAtlasFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance shortAtlasFirstCoeffNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace

/-- The original long-cylinder coordinate Cauchy operator in one chart. -/
def atlasLocalCauchyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) :=
  FiniteParabolicC2AlphaBanach.coordinateCauchyL
    ((A.coefficients p).principalField A.alpha_pos
      A.alpha_lt_one (A.radius p))
    ((A.coefficients p).firstField A.alpha_pos
      A.alpha_lt_one (A.radius p))
    ((A.coefficients p).zeroField A.alpha_pos
      A.alpha_lt_one (A.radius p))

/-- The coordinate Cauchy operator on a shortened cylinder, obtained by
restricting all three localized coefficient fields. -/
def shortLocalCauchyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hST : S ≤ T) :
    FiniteParabolicC2AlphaBanach E W₂ t₀ S α →L[ℝ]
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) :=
  FiniteParabolicC2AlphaBanach.coordinateCauchyL
    (ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
      ((A.coefficients p).principalField A.alpha_pos
        A.alpha_lt_one (A.radius p)))
    (ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
      ((A.coefficients p).firstField A.alpha_pos
        A.alpha_lt_one (A.radius p)))
    (ParabolicC0AlphaSpace.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
      ((A.coefficients p).zeroField A.alpha_pos
        A.alpha_lt_one (A.radius p)))

/-- Reuse the fixed long-cylinder inverse on `(t₀,S]`. -/
def shortLocalInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ S α :=
  (FiniteParabolicC2AlphaBanach.restrictTerminalL hST).comp
    ((A.localInverse p).comp
      (ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos))

/-- The shortened solver remains an exact right inverse of the shortened
coordinate Cauchy operator. -/
theorem shortLocalCauchyL_comp_shortLocalInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    (shortLocalCauchyL cov A p hST).comp
        (shortLocalInverse cov A p hS hST) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) := by
  ext q
  let e := ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q
  have hright := congrArg
    (fun L : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) => L e)
    (A.right_inverse p)
  change shortLocalCauchyL cov A p hST
      (FiniteParabolicC2AlphaBanach.restrictTerminal hST
        (A.localInverse p e)) = q
  rw [show shortLocalCauchyL cov A p hST
      (FiniteParabolicC2AlphaBanach.restrictTerminal hST
        (A.localInverse p e)) =
      ParabolicC0AlphaBanach.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (atlasLocalCauchyL cov A p (A.localInverse p e)) by
        exact FiniteParabolicC2AlphaBanach.coordinateCauchyL_restrictTerminal
          hST _ _ _ _]
  rw [show atlasLocalCauchyL cov A p (A.localInverse p e) = e by
    simpa [atlasLocalCauchyL] using hright]
  exact ParabolicC0AlphaBanach.restrict_extendTerminalL
    hS hST A.alpha_pos q

/-- The shortened inverse retains the canonical zero initial trace. -/
theorem initialTraceL_shortLocalInverse_apply
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S)) :
    FiniteParabolicC2AlphaBanach.initialTraceL hS A.alpha_pos
      (shortLocalInverse cov A p hS hST q) = 0 := by
  let e := ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q
  change FiniteParabolicC2AlphaBanach.initialTraceL hS A.alpha_pos
    (FiniteParabolicC2AlphaBanach.restrictTerminal hST
      (A.localInverse p e)) = 0
  rw [FiniteParabolicC2AlphaBanach.initialTraceL_restrictTerminal]
  have hzero := congrArg
    (fun L : ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        BoundedContinuousFunction E W₂ => L e)
    (A.zero_trace p)
  simpa using hzero

/-- Uniform pointwise operator estimate for the shortened inverse.  The
constant does not deteriorate as `S ↓ t₀`. -/
theorem norm_shortLocalInverse_apply_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S)) :
    ‖shortLocalInverse cov A p hS hST q‖ ≤
      3 * ‖A.localInverse p‖ * ‖q‖ := by
  let e := ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos q
  calc
    ‖shortLocalInverse cov A p hS hST q‖ ≤
        ‖A.localInverse p e‖ :=
      FiniteParabolicC2AlphaBanach.norm_restrictTerminal_le hST _
    _ ≤ ‖A.localInverse p‖ * ‖e‖ :=
      (A.localInverse p).le_opNorm e
    _ ≤ ‖A.localInverse p‖ * (3 * ‖q‖) := by
      have he : ‖e‖ ≤ 3 * ‖q‖ :=
        ((ParabolicC0AlphaBanach.extendTerminalL hS hST A.alpha_pos).le_opNorm q).trans
          (mul_le_mul_of_nonneg_right
            (ParabolicC0AlphaBanach.norm_extendTerminalL_le hS hST A.alpha_pos)
            (norm_nonneg q))
      exact mul_le_mul_of_nonneg_left he
        (norm_nonneg (A.localInverse p))
    _ = 3 * ‖A.localInverse p‖ * ‖q‖ := by ring

/-- The value component of the shortened zero-trace local solution is small
in the full source Hölder norm, with an explicit factor tending to zero with
the cylinder thickness. -/
theorem norm_valueComponentL_shortLocalInverse_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (hthin : S - t₀ ≤ 1)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S)) :
    ‖FiniteParabolicC2AlphaBanach.valueComponentL
        (shortLocalInverse cov A p hS hST q)‖ ≤
      FiniteParabolicC2AlphaBanach.valueShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖) * ‖q‖ := by
  have hmain :=
    FiniteParabolicC2AlphaBanach.norm_valueComponentL_le_valueShortTimeFactor
      hS A.alpha_pos A.alpha_lt_one hthin
      (shortLocalInverse cov A p hS hST q)
      (initialTraceL_shortLocalInverse_apply cov A p hS hST q)
  calc
    ‖FiniteParabolicC2AlphaBanach.valueComponentL
        (shortLocalInverse cov A p hS hST q)‖ ≤
      FiniteParabolicC2AlphaBanach.valueShortTimeFactor (S - t₀) α *
        ‖shortLocalInverse cov A p hS hST q‖ := hmain
    _ ≤ FiniteParabolicC2AlphaBanach.valueShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖ * ‖q‖) :=
      mul_le_mul_of_nonneg_left
        (norm_shortLocalInverse_apply_le cov A p hS hST q)
        (FiniteParabolicC2AlphaBanach.valueShortTimeFactor_nonneg
          (sub_nonneg.mpr hS.le))
    _ = FiniteParabolicC2AlphaBanach.valueShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖) * ‖q‖ := by ring

/-- The first spatial derivative of the shortened zero-trace local solution
is small in the full source Hölder norm. This is the load-bearing
short-time estimate for the first-order cutoff commutator. -/
theorem norm_spaceDerivComponentL_shortLocalInverse_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ S)) :
    ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL
        (shortLocalInverse cov A p hS hST q)‖ ≤
      FiniteParabolicC2AlphaBanach.gradientShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖) * ‖q‖ := by
  have hmain :=
    FiniteParabolicC2AlphaBanach.norm_spaceDerivComponentL_le_gradientShortTimeFactor
      hS A.alpha_pos A.alpha_lt_one
      (shortLocalInverse cov A p hS hST q)
      (initialTraceL_shortLocalInverse_apply cov A p hS hST q)
  calc
    ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL
        (shortLocalInverse cov A p hS hST q)‖ ≤
      FiniteParabolicC2AlphaBanach.gradientShortTimeFactor (S - t₀) α *
        ‖shortLocalInverse cov A p hS hST q‖ := hmain
    _ ≤ FiniteParabolicC2AlphaBanach.gradientShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖ * ‖q‖) :=
      mul_le_mul_of_nonneg_left
        (norm_shortLocalInverse_apply_le cov A p hS hST q)
        (FiniteParabolicC2AlphaBanach.gradientShortTimeFactor_nonneg
          (sub_nonneg.mpr hS.le))
    _ = FiniteParabolicC2AlphaBanach.gradientShortTimeFactor (S - t₀) α *
        (3 * ‖A.localInverse p‖) * ‖q‖ := by ring

/-- Any fixed first-plus-zeroth-order coordinate residual composed with the
shortened local inverse has an explicit operator norm tending to zero with
the cylinder thickness.  This is the analytic estimate used for cutoff and
frame-transition commutators. -/
theorem norm_lowerOrderL_comp_shortLocalInverse_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (hthin : S - t₀ ≤ 1)
    (G : FiniteFirstCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := S) (α := α))
    (D : FiniteZeroCoefficientSpace (X := E) (W := W₂)
      (t₀ := t₀) (T := S) (α := α)) :
    ‖(FiniteParabolicC2AlphaBanach.lowerOrderL G D).comp
        (shortLocalInverse cov A p hS hST)‖ ≤
      FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
          (X := E) (W := W₂) ‖G‖ ‖D‖ (S - t₀) α *
        (3 * ‖A.localInverse p‖) := by
  let F := FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor
    (X := E) (W := W₂) ‖G‖ ‖D‖ (S - t₀) α
  have hF : 0 ≤ F :=
    FiniteParabolicC2AlphaBanach.lowerOrderShortTimeFactor_nonneg
      (norm_nonneg G) (norm_nonneg D) (sub_nonneg.mpr hS.le)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hF (by positivity)) (fun q => ?_)
  calc
    ‖((FiniteParabolicC2AlphaBanach.lowerOrderL G D).comp
        (shortLocalInverse cov A p hS hST)) q‖ ≤
      F * ‖shortLocalInverse cov A p hS hST q‖ :=
        FiniteParabolicC2AlphaBanach.norm_lowerOrderL_apply_le_shortTimeFactor
          hS A.alpha_pos A.alpha_lt_one hthin G D
          (shortLocalInverse cov A p hS hST q)
          (initialTraceL_shortLocalInverse_apply cov A p hS hST q)
    _ ≤ F * (3 * ‖A.localInverse p‖ * ‖q‖) :=
      mul_le_mul_of_nonneg_left
        (norm_shortLocalInverse_apply_le cov A p hS hST q) hF
    _ = F * (3 * ‖A.localInverse p‖) * ‖q‖ := by ring

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
