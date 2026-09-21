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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasShortTime

/-!
# Restricting a tensor-heat parametrix atlas in normalized time

The geometric atlas and all of its spatial coefficient data are independent
of the terminal time.  This file restricts a fixed atlas from `(t₀,T]` to
any shorter normalized cylinder `(t₀,S]`, reusing the original local
inverses by extension and restriction.  The resulting object is again an
honest `FiniteTensorHeatParametrixAtlas`, so the already verified cutoff and
geometric-residual theory applies without new analytic hypotheses.
-/

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

@[reducible] local instance restrictionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance restrictionFirstDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance restrictionHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance restrictionHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance restrictionPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance restrictionPrincipalNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance restrictionFirstNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance restrictionFirstNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace

/-- Restricting a localized principal coefficient in time is the same
coefficient freshly regarded on the shorter cylinder. -/
theorem restrictL_principalField
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hα : 0 < α) (hα1 : α < 1) (r : ℝ) (hST : S ≤ T) :
    ParabolicC0AlphaSpace.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (D.principalField (t₀ := t₀) (T := T) hα hα1 r) =
      D.principalField (t₀ := t₀) (T := S) hα hα1 r := by
  apply Subtype.ext
  rfl

/-- Restricting a localized first-order coefficient in time is the same
coefficient on the shorter cylinder. -/
theorem restrictL_firstField
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hα : 0 < α) (hα1 : α < 1) (r : ℝ) (hST : S ≤ T) :
    ParabolicC0AlphaSpace.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (D.firstField (t₀ := t₀) (T := T) hα hα1 r) =
      D.firstField (t₀ := t₀) (T := S) hα hα1 r := by
  apply Subtype.ext
  rfl

/-- Restricting a localized zeroth-order coefficient in time is the same
coefficient on the shorter cylinder. -/
theorem restrictL_zeroField
    (D : TensorHeatLocalizedCoefficientData E W₂)
    (hα : 0 < α) (hα1 : α < 1) (r : ℝ) (hST : S ≤ T) :
    ParabolicC0AlphaSpace.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (D.zeroField (t₀ := t₀) (T := T) hα hα1 r) =
      D.zeroField (t₀ := t₀) (T := S) hα hα1 r := by
  apply Subtype.ext
  rfl

/-- The original atlas inverse at an arbitrary center, reused on a shorter
normalized cylinder. -/
def restrictedLocalInverseAt
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ S α :=
  shortLocalInverse cov A p hS hST

/-- The restricted inverse is an exact right inverse for the correspondingly
restricted coordinate Cauchy operator. -/
theorem coordinateCauchyL_comp_restrictedLocalInverseAt
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL
      ((A.coefficients p).principalField A.alpha_pos
        A.alpha_lt_one (A.radius p))
      ((A.coefficients p).firstField A.alpha_pos
        A.alpha_lt_one (A.radius p))
      ((A.coefficients p).zeroField A.alpha_pos
        A.alpha_lt_one (A.radius p))).comp
        (restrictedLocalInverseAt cov A p hS hST) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) := by
  have h := shortLocalCauchyL_comp_shortLocalInverse cov A p hS hST
  rw [shortLocalCauchyL,
    restrictL_principalField (S := S) (T := T) (A.coefficients p)
      A.alpha_pos A.alpha_lt_one (A.radius p) hST,
    restrictL_firstField (S := S) (T := T) (A.coefficients p)
      A.alpha_pos A.alpha_lt_one (A.radius p) hST,
    restrictL_zeroField (S := S) (T := T) (A.coefficients p)
      A.alpha_pos A.alpha_lt_one (A.radius p) hST] at h
  simpa only [restrictedLocalInverseAt] using h

/-- Restriction preserves the canonical zero initial trace. -/
theorem initialTraceL_restrictedLocalInverseAt
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := W₂) hS A.alpha_pos).comp
        (restrictedLocalInverseAt cov A p hS hST) = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  simpa only [restrictedLocalInverseAt, ContinuousLinearMap.comp_apply,
    zero_apply] using
    initialTraceL_shortLocalInverse_apply cov A p hS hST q

/-- Restrict a fixed parametrix atlas to a shorter normalized terminal
time.  Its cover, radii, localized spatial coefficients, and partition of
unity are unchanged. -/
def restrictTerminalAtlas
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) :
    FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ S α where
  time_lt := hS
  alpha_pos := A.alpha_pos
  alpha_lt_one := A.alpha_lt_one
  radius := A.radius
  coefficients := A.coefficients
  localInverse := fun p => restrictedLocalInverseAt cov A p hS hST
  radius_pos := A.radius_pos
  center_eq := A.center_eq
  fields_agree := by
    intro p z hz
    simpa [TensorHeatLocalizedCoefficientData.principalField,
      TensorHeatLocalizedCoefficientData.firstField,
      TensorHeatLocalizedCoefficientData.zeroField] using
        A.fields_agree p z hz
  right_inverse := fun p =>
    coordinateCauchyL_comp_restrictedLocalInverseAt cov A p hS hST
  zero_trace := fun p =>
    initialTraceL_restrictedLocalInverseAt cov A p hS hST
  patch_subset_trivialization := A.patch_subset_trivialization
  cover := A.cover

@[simp] theorem restrictTerminalAtlas_radius
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) (p : M) :
    (A.restrictTerminalAtlas cov hS hST).radius p = A.radius p := rfl

/-- Time restriction leaves the finite spatial cover definitionally
unchanged.  Exposing this projection avoids unfolding the proof fields of
the restricted atlas in downstream dependent-index calculations. -/
@[simp] theorem restrictTerminalAtlas_cover
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) :
    (A.restrictTerminalAtlas cov hS hST).cover = A.cover := rfl

@[simp] theorem restrictTerminalAtlas_localInverse
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hS : t₀ < S) (hST : S ≤ T) (p : M) :
    (A.restrictTerminalAtlas cov hS hST).localInverse p =
      restrictedLocalInverseAt cov A p hS hST := rfl

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
