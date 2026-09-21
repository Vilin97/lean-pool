/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyMovingConnectionVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyMetricMixedRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyManifoldLieBracketMixedRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicConnectionVariation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation

/-!
# Deriving the moving connection rule from mixed Koszul data

The curvature commutator applies the time-dependent connection to a section
which itself varies with time.  This file combines the mixed-regularity
derivative of the actual Koszul expression with the fixed-field cyclic
variation formula.  The result derives that moving-section connection
derivative; it does not assume a connection-variation predicate or a
curvature-evolution equation.

The bracket derivatives and mixed scalar regularity are stated explicitly
here.  A later specialization can discharge them from joint spacetime
regularity of the metric and moving section.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [I.Boundaryless]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
/-- The moving-section connection derivative follows from the differentiated
Koszul formula and the cyclic metric-velocity identity.  In contrast with
HasConnectionTimeVariationAt, this rule only concerns a section family for
which the displayed mixed derivative data are supplied. -/
theorem hasDerivAt_along_moving_of_jointKoszulData
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    (hdotSymm : ∀ (y : M) (u v : TM y), hdot y u v = hdot y v u)
    {t : ℝ} {X : Π y : M, TM y} {Y : ℝ → Π y : M, TM y}
    (Ydot : Π y : M, TM y) {x : M}
    (Axy : TM x)
    (hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ∀ τ : ℝ, ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Y τ y)))
    (hYtime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hYjoint : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (Y p.1 p.2)) (t, x))
    (hYdot : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Ydot y)))
    (hAcyclic : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      2 * (g t).inner x Axy (W x) =
        metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t X (Y t) W x +
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t (Y t) X W x -
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t W X (Y t) x)
    (hjointYZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (W p.2)))
    (hdotSpaceYZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => hdot y (Y t y) (W y)) x)
    (hmetricSpaceYdotZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => (g t).inner y (Ydot y) (W y)) x)
    (hjointXZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (W p.2)))
    (hdotSpaceXZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => hdot y (X y) (W y)) x)
    (hjointYX : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (X p.2)))
    (hdotSpaceYX : MDiffAt
      (fun y : M => hdot y (Y t y) (X y)) x)
    (hmetricSpaceYdotX : MDiffAt
      (fun y : M => (g t).inner y (Ydot y) (X y)) x)
    :
    HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
      ((cov t).along X Ydot x + Axy) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  classical
  let A : ∀ y : M, TM y → TM y → TM y := fun y _ _ =>
    if hy : y = x then
      cast (congrArg (fun z : M => TM z) hy.symm) Axy
    else 0
  have hApoint : A x (X x) (Y t x) = Axy := by
    simp [A]
  have hAcyclic' : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      2 * (g t).inner x (A x (X x) (Y t x)) (W x) =
        metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t X (Y t) W x +
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t (Y t) X W x -
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t W X (Y t) x := by
    intro W hW
    rw [hApoint]
    exact hAcyclic W hW
  have hKoszulRhs : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      HasDerivAt
        (fun τ : ℝ => metricKoszulExpression (I := I) (M := M)
          g τ X (Y τ) W x)
        (2 * (hdot x ((cov t).along X (Y t) x) (W x) +
          (g t).inner x
            ((cov t).along X Ydot x + A x (X x) (Y t x)) (W x))) t := by
    intro W hW
    have hW₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% W) :=
      hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hWAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) x := hW₁ x
    have hbracketYZ :=
      PoincareCurvature.hasDerivAt_mlieBracket_left_of_joint_contMDiffAt
        (I := I) (M := M) Y Ydot W hYjoint hYtime hWAt
    have hXAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (X y)) x := hX x
    have hbracketXY :=
      PoincareCurvature.hasDerivAt_mlieBracket_right_of_joint_contMDiffAt
        (I := I) (M := M) Y Ydot X hYjoint hYtime hXAt
    have hKoszulDerivative :=
      hasDerivAt_metricKoszulExpression_movingMiddle_of_jointContMDiff
        (I := I) (M := M) g hdot hdotSymm (t := t) hmetric
        (X := X) (Z := W) (Y := Y) Ydot (x := x) hYtime
        (hjointYZ W hW) (hdotSpaceYZ W hW₁) (hmetricSpaceYdotZ W hW₁)
        (hjointXZ W hW) (hdotSpaceXZ W hW₁) (hjointYX W hW)
        hdotSpaceYX hmetricSpaceYdotX
        hbracketYZ hbracketXY
    have hcyclic :=
      metricVelocityKoszulExpression_eq_cyclicCovariantDerivative
        (I := I) (M := M) (g := g) (cov := cov) hLevi hcov hdot hdotSymm t
        (X := X) (Y := Y t) (Z := W) (x := x) hX (hY t) hW₁
    have hstatic :
        metricKoszulExpression (I := I) (M := M) g t X Ydot W x =
          2 * (g t).inner x ((cov t).along X Ydot x) (W x) := by
      have hk := _root_.CovariantDerivative.koszul_formula
        (I := I) (E := E) (M := M) (cov := cov t) (hLevi t)
        (x := x) hX hYdot hW₁
      have hinner (y : M) (u v : TM y) :
          (g t).inner y u v = Inner.inner ℝ u v := rfl
      simpa [metricKoszulExpression, hinner] using hk.symm
    have hderivativeValue :
        metricVelocityKoszulExpression (I := I) (M := M) hdot X (Y t) W x +
            metricKoszulExpression (I := I) (M := M) g t X Ydot W x =
          2 * (hdot x ((cov t).along X (Y t) x) (W x) +
            (g t).inner x
              ((cov t).along X Ydot x + A x (X x) (Y t x)) (W x)) := by
      have hsplit :
          (g t).inner x
              ((cov t).along X Ydot x + A x (X x) (Y t x)) (W x) =
            (g t).inner x ((cov t).along X Ydot x) (W x) +
              (g t).inner x (A x (X x) (Y t x)) (W x) := by
        change Inner.inner ℝ
            ((cov t).along X Ydot x + A x (X x) (Y t x)) (W x) = _
        exact inner_add_left _ _ _
      have hcycle :
          metricVelocityCovariantDerivativeAlong
                (I := I) (M := M) cov hdot t X (Y t) W x +
              metricVelocityCovariantDerivativeAlong
                (I := I) (M := M) cov hdot t (Y t) X W x -
              metricVelocityCovariantDerivativeAlong
                (I := I) (M := M) cov hdot t W X (Y t) x =
            2 * (g t).inner x (A x (X x) (Y t x)) (W x) :=
            (hAcyclic' W hW).symm
      calc
        _ = 2 * hdot x ((cov t).along X (Y t) x) (W x) +
              (metricVelocityCovariantDerivativeAlong
                  (I := I) (M := M) cov hdot t X (Y t) W x +
                metricVelocityCovariantDerivativeAlong
                  (I := I) (M := M) cov hdot t (Y t) X W x -
                metricVelocityCovariantDerivativeAlong
                  (I := I) (M := M) cov hdot t W X (Y t) x) +
              2 * (g t).inner x ((cov t).along X Ydot x) (W x) := by
          rw [hcyclic, hstatic]
          ring
        _ = 2 * (hdot x ((cov t).along X (Y t) x) (W x) +
              (g t).inner x
                ((cov t).along X Ydot x + A x (X x) (Y t x)) (W x)) := by
          rw [hcycle, hsplit]
          ring
    exact hKoszulDerivative.congr_deriv hderivativeValue
  have hmoving := hasDerivAt_along_moving_of_movingKoszulPairings
    (I := I) (M := M) g cov hcov hLevi A hdot (t := t)
    (σ := Y) Ydot hmetric hX hY hKoszulRhs
  exact hmoving.congr_deriv (by rw [hApoint])
/-- The moving-section connection derivative for an actual Ricci flow.

The cyclic variation vector is obtained from the fixed-field Koszul variation
for the actual intrinsic Ricci tensor.  The two time derivatives of Lie
brackets are proved from joint `C²` regularity of the moving section.  The
remaining hypotheses are scalar regularity of the actual metric pairings and
spatial differentiability of the intrinsic Ricci pairings; no connection-
variation or curvature-evolution predicate is an input. -/
theorem exists_hasDerivAt_along_moving_of_intrinsicRicciFlow_and_jointRegularity
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    [CompactSpace M] [Nonempty M]
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    {X : Π y : M, TM y} {Y : ℝ → Π y : M, TM y}
    (Ydot : Π y : M, TM y) {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hY : ∀ τ : ℝ, ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (Y τ y)))
    (hYtime : ∀ y : M,
      HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hYjoint : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (Y p.1 p.2)) (t, x))
    (hYdot : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Ydot y)))
    (hjointYZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (W p.2)))
    (hmetricSpaceYdotZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => (g t).inner y (Ydot y) (W y)) x)
    (hjointXZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (X p.2) (W p.2)))
    (hjointYX : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.1 p.2) (X p.2)))
    (hmetricSpaceYdotX : MDiffAt
      (fun y : M => (g t).inner y (Ydot y) (X y)) x)
    (hjointFixedPairing : ∀ (U V : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (U y)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (V y)) →
      ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hRicciSpacePairing : ∀ (U V : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (U y)) →
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (V y)) →
      MDiffAt
        (fun y : M => RicciFlow.intrinsicRicciBilinearAt
          (I := I) (M := M) g t y (U y) (V y)) x) :
    ∃ Axy : TM x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
        ((cov t).along X Ydot x + Axy) t ∧
      ∀ (W : Π y : M, TM y),
        ContMDiff I (I.prod 𝓘(ℝ, E)) 2
          (fun y ↦ TotalSpace.mk' E y (W y)) →
        2 * (g t).inner x Axy (W x) =
          -2 * (metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov
              (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
              t X (Y t) W x +
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov
              (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
              t (Y t) X W x -
            metricVelocityCovariantDerivativeAlong
              (I := I) (M := M) cov
              (RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t)
              t W X (Y t) x) := by
  let ricci : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    RicciFlow.intrinsicRicciBilinearAt (I := I) (M := M) g t
  let hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    fun y => (-2 : ℝ) • ricci y
  have hRicciTensor : RicciFlow.intrinsicRicciTensor (I := I) (M := M) g =
      RicciFlow.ricciTensor (I := I) (M := M) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I) (M := M) g hcov hLevi
  have hricciEq (y : M) (u v : TM y) :
      ricci y u v = g.ricciCurvature cov hcov t y u v := by
    have hpoint := congrArg (fun q => q t y u v) hRicciTensor
    simpa [ricci, RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor] using hpoint
  have hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t := by
    intro y u v
    have hmetric₀ := hflow.2.1 ht y u v
    have hmetricEq := hflow.2.2 ht y u v
    change HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (gdot t y u v) t at hmetric₀
    rw [hmetricEq] at hmetric₀
    have hmetricRicci : HasDerivAt (fun τ : ℝ => (g τ).inner y u v)
        ((-2 : ℝ) * g.ricciCurvature cov hcov t y u v) t := by
      simpa [RicciFlow.ricciFlowRHS, RicciFlow.ricciTensor] using hmetric₀
    simpa [hdot, ricci, hricciEq y u v, smul_eq_mul] using hmetricRicci
  have hRicciSymm (y : M) (u v : TM y) : ricci y u v = ricci y v u := by
    have hsymm := RicciFlow.intrinsicRicciTensor_symm
      (I := I) (M := M) g t y u v
    simpa [ricci, RicciFlow.intrinsicRicciBilinearAt_apply] using hsymm
  have hX₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% X) :=
    hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (Y t)) :=
    (hY t).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdotSymm : ∀ (y : M) (u v : TM y), hdot y u v = hdot y v u := by
    intro y u v
    calc
      hdot y u v = (-2 : ℝ) * ricci y u v := by simp [hdot, smul_eq_mul]
      _ = (-2 : ℝ) * ricci y v u := by rw [hRicciSymm]
      _ = hdot y v u := by simp [hdot, smul_eq_mul]
  have hdotSpaceYZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => hdot y (Y t y) (W y)) x := by
    intro W hW
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpacePairing (Y t) W hY₁ hW)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  have hdotSpaceXZ : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 1
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      MDiffAt (fun y : M => hdot y (X y) (W y)) x := by
    intro W hW
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpacePairing X W hX₁ hW)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  have hdotSpaceYX : MDiffAt (fun y : M => hdot y (Y t y) (X y)) x := by
    have h := (mdifferentiableAt_const : MDiffAt (fun _ : M => (-2 : ℝ)) x).smul
      (hRicciSpacePairing (Y t) X hY₁ hX₁)
    convert h using 1 <;> simp [hdot, ricci, smul_eq_mul] <;> funext y <;>
      simp [Pi.mul_apply] <;> ring
  rcases exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_intrinsicRicciFlow
      (I := I) (M := M) g cov hcov hLevi gdot s hflow
      (t := t) ht (X := X) (Y := Y t) (x := x) hX (hY t)
      (fun W hW => hjointFixedPairing (Y t) W (hY t) hW)
      (fun W hW => hRicciSpacePairing (Y t) W hY₁ hW)
      (fun W hW => hjointFixedPairing X W hX hW)
      (fun W hW => hRicciSpacePairing X W hX₁ hW)
      (fun _ _ => hjointFixedPairing X (Y t) hX (hY t))
      (fun _ _ => hRicciSpacePairing X (Y t) hX₁ hY₁) with
    ⟨Axy, _, hAcyclicRaw⟩
  have hAcyclic : ∀ (W : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (W y)) →
      2 * (g t).inner x Axy (W x) =
        metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t X (Y t) W x +
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t (Y t) X W x -
        metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t W X (Y t) x := by
    intro W hW
    have hW₁ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% W) :=
      hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hscaleXYZ := metricVelocityCovariantDerivativeAlong_smul
      (I := I) (M := M) cov ricci (-2 : ℝ) t X (Y t) W x
      (hRicciSpacePairing (Y t) W hY₁ hW₁)
    have hscaleYXZ := metricVelocityCovariantDerivativeAlong_smul
      (I := I) (M := M) cov ricci (-2 : ℝ) t (Y t) X W x
      (hRicciSpacePairing X W hX₁ hW₁)
    have hscaleZXY := metricVelocityCovariantDerivativeAlong_smul
      (I := I) (M := M) cov ricci (-2 : ℝ) t W X (Y t) x
      (hRicciSpacePairing X (Y t) hX₁ hY₁)
    calc
      2 * (g t).inner x Axy (W x) =
          -2 * (metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t X (Y t) W x +
            metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t (Y t) X W x -
            metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov ricci t W X (Y t) x) := hAcyclicRaw W hW
      _ = metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t X (Y t) W x +
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t (Y t) X W x -
          metricVelocityCovariantDerivativeAlong
            (I := I) (M := M) cov hdot t W X (Y t) x := by
        rw [hscaleXYZ, hscaleYXZ, hscaleZXY]
        ring
  refine ⟨Axy, ?_, hAcyclicRaw⟩
  exact hasDerivAt_along_moving_of_jointKoszulData
    (I := I) (M := M) g cov hcov hLevi hdot hdotSymm
    (t := t) (X := X) (Y := Y) Ydot (x := x) Axy
    hmetric hX₁ (fun τ => (hY τ).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    hYtime hYjoint hYdot hAcyclic
    hjointYZ hdotSpaceYZ hmetricSpaceYdotZ
    hjointXZ hdotSpaceXZ hjointYX hdotSpaceYX hmetricSpaceYdotX

section IntrinsicRicciTensorIdentification

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [CompleteSpace E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [T2Space M₁]
  [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
  [IsManifold I₁ (minSmoothness ℝ 3) M₁]
  [IsManifold I₁ ((2 : ℕ∞) + 1) M₁]
  [ContMDiffVectorBundle 2 E₁ (TangentSpace I₁ : M₁ → Type _) I₁]

local notation "TM₁" => (TangentSpace I₁ : M₁ → Type _)
local notation "T₂₁" => (fun x : M₁ => TM₁ x →L[ℝ] TM₁ x →L[ℝ] ℝ)

variable [RiemannianBundle (TangentSpace I₁ : M₁ → Type _)]
  [SigmaCompactSpace M₁]

/-- On the canonical smooth extensions of three fibre vectors, the expanded
metric-velocity derivative of intrinsic Ricci is exactly the induced
covariant-tensor derivative of the genuine Ricci two-tensor.  This is the
identification needed to turn the cyclic Koszul witness into one
geometrically defined connection-variation tensor. -/
theorem metricVelocityCovariantDerivativeAlong_intrinsicRicci_smoothExtend_eq
    (g : TimeDependentRiemannianMetric (I := I₁) (M := M₁))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₁) (M := M₁) (F := E₁) (V := TM₁))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₁) (M := M₁) (F := E₁) (V := TM₁) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} {x : M₁} (u v w : TM₁ x)
    (hRicci : MDiffAt
      (fun y : M₁ => TotalSpace.mk' (E₁ →L[ℝ] (E₁ →L[ℝ] ℝ))
        (E := T₂₁) y (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x) :
    metricVelocityCovariantDerivativeAlong
        (I := I₁) (M := M₁) cov
        (RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t) t
        (smoothExtend (I := I₁) (F := E₁) (V := TM₁) x u)
        (smoothExtend (I := I₁) (F := E₁) (V := TM₁) x v)
        (smoothExtend (I := I₁) (F := E₁) (V := TM₁) x w) x =
      CovariantDerivative.covariantTwoTensorCovariantDerivative
        (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
        x u v w := by
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  let hRicciTensor :
      RicciFlow.intrinsicRicciTensor (I := I₁) (M := M₁) g =
        RicciFlow.ricciTensor (I := I₁) (M := M₁) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I₁) (M := M₁) g hcov hLevi
  have hricciEq (y : M₁) (a b : TM₁ y) :
      RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t y a b =
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y a b := by
    have hpoint := congrArg (fun q => q t y a b) hRicciTensor
    simpa [RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor,
      CovariantDerivative.ricciCovariantTwoTensor_apply] using hpoint
  let X : Π y : M₁, TM₁ y :=
    smoothExtend (I := I₁) (F := E₁) (V := TM₁) x u
  let Y : Π y : M₁, TM₁ y :=
    smoothExtend (I := I₁) (F := E₁) (V := TM₁) x v
  let Z : Π y : M₁, TM₁ y :=
    smoothExtend (I := I₁) (F := E₁) (V := TM₁) x w
  have hfun :
      (fun y : M₁ =>
        RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t y
          (Y y) (Z y)) =
      (fun y : M₁ =>
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y (Y y) (Z y)) := by
    funext y
    exact hricciEq y (Y y) (Z y)
  have hmvf := congrArg
    (fun f : M₁ → ℝ => mvfderiv (I := I₁) f x (X x)) hfun
  have htermY := hricciEq x ((cov t).along X Y x) (Z x)
  have htermZ := hricciEq x (Y x) ((cov t).along X Z x)
  have hvelocity :
      metricVelocityCovariantDerivativeAlong
          (I := I₁) (M := M₁) cov
          (RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t) t
          X Y Z x =
        mvfderiv (I := I₁)
            (fun y : M₁ =>
              CovariantDerivative.ricciCovariantTwoTensor (cov t) y
                (Y y) (Z y)) x (X x) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).along X Y x) (Z x) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            (Y x) ((cov t).along X Z x) := by
    unfold metricVelocityCovariantDerivativeAlong
    rw [hmvf, htermY, htermZ]
  have hD :=
    CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      (cov := cov t) hRicci u v w
  calc
    _ = mvfderiv (I := I₁)
          (fun y : M₁ =>
            CovariantDerivative.ricciCovariantTwoTensor (cov t) y
              (Y y) (Z y)) x (X x) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).along X Y x) (Z x) -
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            (Y x) ((cov t).along X Z x) := hvelocity
    _ = CovariantDerivative.covariantTwoTensorCovariantDerivative
          (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x u v w := by
            simpa [X, Y, Z, CovariantDerivative.along_apply,
              smoothExtend_apply] using hD.symm

/-- For arbitrary spatially differentiable vector fields, the metric-velocity
expression of intrinsic Ricci is the genuine covariant derivative of the
Ricci two-tensor.  This is the tensoriality step needed to identify the
pointwise Koszul connection-variation witness independently of the chosen
test-field extensions. -/
theorem metricVelocityCovariantDerivativeAlong_intrinsicRicci_eq
    (g : TimeDependentRiemannianMetric (I := I₁) (M := M₁))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₁) (M := M₁) (F := E₁) (V := TM₁))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₁) (M := M₁) (F := E₁) (V := TM₁) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} {x : M₁} (X Y Z : Π y : M₁, TM₁ y)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hRicci : MDiffAt
      (fun y : M₁ => TotalSpace.mk' (E₁ →L[ℝ] (E₁ →L[ℝ] ℝ))
        (E := T₂₁) y (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x) :
    metricVelocityCovariantDerivativeAlong
        (I := I₁) (M := M₁) cov
        (RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t) t
        X Y Z x =
      CovariantDerivative.covariantTwoTensorCovariantDerivative
        (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
        x (X x) (Y x) (Z x) := by
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  have hRicciTensor :
      RicciFlow.intrinsicRicciTensor (I := I₁) (M := M₁) g =
        RicciFlow.ricciTensor (I := I₁) (M := M₁) g cov hcov :=
    RicciFlow.intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
      (I := I₁) (M := M₁) g hcov hLevi
  have hricciEq (y : M₁) (a b : TM₁ y) :
      RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t y a b =
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y a b := by
    have hpoint := congrArg (fun q => q t y a b) hRicciTensor
    simpa [RicciFlow.intrinsicRicciBilinearAt_apply,
      RicciFlow.ricciTensor,
      CovariantDerivative.ricciCovariantTwoTensor_apply] using hpoint
  have hfun :
      (fun y : M₁ =>
        RicciFlow.intrinsicRicciBilinearAt (I := I₁) (M := M₁) g t y
          (Y y) (Z y)) =
      (fun y : M₁ =>
        CovariantDerivative.ricciCovariantTwoTensor (cov t) y (Y y) (Z y)) := by
    funext y
    exact hricciEq y (Y y) (Z y)
  have hmvf := congrArg
    (fun f : M₁ → ℝ => mvfderiv (I := I₁) f x (X x)) hfun
  have htermY := hricciEq x ((cov t).along X Y x) (Z x)
  have htermZ := hricciEq x (Y x) ((cov t).along X Z x)
  have hLeib :=
    CovariantDerivative.realLineCovariantDerivative_bilinear
      (cov := cov t)
      (h := CovariantDerivative.ricciCovariantTwoTensor (cov t))
      hRicci hY hZ (X x)
  have hLeib' :
      mvfderiv (I := I₁)
          (fun y : M₁ =>
            CovariantDerivative.ricciCovariantTwoTensor (cov t) y (Y y) (Z y))
          x (X x) =
        CovariantDerivative.covariantTwoTensorCovariantDerivative
            (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
            x (X x) (Y x) (Z x) +
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            ((cov t).along X Y x) (Z x) +
          CovariantDerivative.ricciCovariantTwoTensor (cov t) x
            (Y x) ((cov t).along X Z x) := by
    simpa [CovariantDerivative.realLineCovariantDerivative] using hLeib
  unfold metricVelocityCovariantDerivativeAlong
  rw [hmvf, htermY, htermZ, hLeib']
  ring

end IntrinsicRicciTensorIdentification

section CyclicVariation

variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [FiniteDimensional ℝ E₀] [CompleteSpace E₀]
  {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [T2Space M₀]
  [I₀.Boundaryless] [IsManifold I₀ ∞ M₀]
  [IsManifold I₀ (minSmoothness ℝ 3) M₀] [IsManifold I₀ ((2 : ℕ∞) + 1) M₀]
  [ContMDiffVectorBundle 2 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]

local notation "TM₀" => (TangentSpace I₀ : M₀ → Type _)
local notation "T₂₀" => (fun x : M₀ => TM₀ x →L[ℝ] TM₀ x →L[ℝ] ℝ)
local notation "T₃₀" => (fun x : M₀ => TM₀ x →L[ℝ] T₂₀ x)

variable [RiemannianBundle (TangentSpace I₀ : M₀ → Type _)]
variable [IsContMDiffRiemannianBundle I₀ 1 E₀ (TangentSpace I₀ : M₀ → Type _)]

local instance cyclicVariationT₁ModelNormedAdd :
    NormedAddCommGroup (E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₁ModelNormedSpace :
    NormedSpace ℝ (E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₂ModelNormedAdd :
    NormedAddCommGroup (E₀ →L[ℝ] E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₂ModelNormedSpace :
    NormedSpace ℝ (E₀ →L[ℝ] E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₃ModelNormedAdd :
    NormedAddCommGroup (E₀ →L[ℝ] E₀ →L[ℝ] E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₃ModelNormedSpace :
    NormedSpace ℝ (E₀ →L[ℝ] E₀ →L[ℝ] E₀ →L[ℝ] ℝ) := inferInstance
local instance cyclicVariationT₂NormedAdd (x : M₀) :
    NormedAddCommGroup (T₂₀ x) := inferInstance
local instance cyclicVariationT₂NormedSpace (x : M₀) :
    NormedSpace ℝ (T₂₀ x) := inferInstance
local instance cyclicVariationT₃NormedAdd (x : M₀) :
    NormedAddCommGroup (T₃₀ x) := inferInstance
local instance cyclicVariationT₃NormedSpace (x : M₀) :
    NormedSpace ℝ (T₃₀ x) := inferInstance
local instance cyclicVariationT₃Add (x : M₀) :
    AddCommGroup (T₃₀ x) := ContinuousLinearMap.addCommGroup
local instance cyclicVariationT₃Module (x : M₀) :
    Module ℝ (T₃₀ x) := ContinuousLinearMap.module

/-! The pointwise cyclic formula above already determines a canonical tensor:
take the cyclic covariant derivative of Ricci as a covector and raise its
remaining index with the actual metric.  This packages the pointwise witness
as a single geometrically defined field, rather than choosing an unrelated
vector for each triple of test fields. -/

/-- The metric-raised cyclic covariant derivative of a covariant two-tensor.
For Ricci flow, the connection variation is this tensor with the intrinsic
Ricci tensor as its input (and the displayed minus sign is the `-2 Ric`
velocity after dividing the Koszul formula by two). -/
noncomputable def cyclicCovariantTensorVariationVector
    (cov : CovariantDerivative I₀ E₀ TM₀)
    (h : ∀ x : M₀, T₂₀ x) (x : M₀) (u v : TM₀ x) : TM₀ x := by
  let D : T₃₀ x :=
    CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x
  let Dflip : T₃₀ x :=
    (ContinuousLinearMap.flipₗᵢ ℝ (TM₀ x) (TM₀ x)
      (TM₀ x →L[ℝ] ℝ)) D
  let α : TM₀ x →L[ℝ] ℝ :=
    - D u v - D v u +
      CovariantDerivative.flipLastTwo (I := I₀) x (Dflip u) v
  exact CovariantDerivative.rieszMap (I := I₀) x α

/-- Pairing the cyclic variation vector with an arbitrary tangent vector
recovers the negative Koszul cyclic contraction of the genuine induced
covariant derivative. -/
theorem cyclicCovariantTensorVariationVector_inner
    (cov : CovariantDerivative I₀ E₀ TM₀)
    (h : ∀ x : M₀, T₂₀ x) (x : M₀) (u v w : TM₀ x) :
    Inner.inner ℝ (cyclicCovariantTensorVariationVector
      cov h x u v) w =
      -(CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x u v w +
        CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x v u w -
        CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x w u v) := by
  let D : T₃₀ x :=
    CovariantDerivative.covariantTwoTensorCovariantDerivative cov h x
  let Dflip : T₃₀ x :=
    (ContinuousLinearMap.flipₗᵢ ℝ (TM₀ x) (TM₀ x)
      (TM₀ x →L[ℝ] ℝ)) D
  have hflip (a b c : TM₀ x) : Dflip a b c = D b a c := by
    simp [Dflip]
  change Inner.inner ℝ
    (CovariantDerivative.rieszMap (I := I₀) x
      (-D u v - D v u +
        CovariantDerivative.flipLastTwo (I := I₀) x (Dflip u) v)) w =
    -(D u v w + D v u w - D w u v)
  rw [CovariantDerivative.rieszMap_apply_inner]
  simp only [neg_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, CovariantDerivative.flipLastTwo_apply]
  rw [hflip u w v]
  ring
/-- The actual Ricci-flow derivative of the Levi--Civita connection on canonical
smooth extensions is represented by the metric-raised cyclic covariant
derivative of the genuine Ricci tensor.  The mixed regularity used to obtain
the three time--space commutations remains an explicit hypothesis; no
connection-variation or curvature-evolution predicate is assumed. -/
theorem hasDerivAt_along_smoothExtend_of_intrinsicRicciFlow_and_jointRegularity
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hcovTwo : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 2)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s) {x : M₀} (u v : TM₀ x)
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      (∀ y, MDiffAt (T% U) y) → (∀ y, MDiffAt (T% V) y) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hRicciSpacePairing : ∀ (U V : Π y : M₀, TM₀ y),
      (∀ y, MDiffAt (T% U) y) → (∀ y, MDiffAt (T% V) y) →
      MDiffAt
        (fun y : M₀ => RicciFlow.intrinsicRicciBilinearAt
          (I := I₀) (M := M₀) g t y (U y) (V y)) x) :
    (letI : RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
     letI : IsContMDiffRiemannianBundle I₀ 1 E₀
        (TangentSpace I₀ : M₀ → Type _) :=
       g.slice_isContMDiffRiemannianBundle t
    HasDerivAt
      (fun τ : ℝ =>
        (cov τ).along
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x u)
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x v) x)
      (cyclicCovariantTensorVariationVector (cov t)
        (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x u v) t) := by
  letI : RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀
      (TangentSpace I₀ : M₀ → Type _) := by infer_instance
  let X : Π y : M₀, TM₀ y :=
    smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x u
  let Y : Π y : M₀, TM₀ y :=
    smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x v
  have hX₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% X) := by
    simpa [X] using smoothExtend_contMDiff_two
      (I := I₀) (F := E₀) (V := TangentSpace I₀) x u
  have hY₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% Y) := by
    simpa [Y] using smoothExtend_contMDiff_two
      (I := I₀) (F := E₀) (V := TangentSpace I₀) x v
  have hX₁ := hX₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hX : ∀ y, MDiffAt (T% X) y := fun y =>
    (hX₁ y).mdifferentiableAt one_ne_zero
  have hY : ∀ y, MDiffAt (T% Y) y := fun y =>
    (hY₁ y).mdifferentiableAt one_ne_zero
  have hXbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
      (fun y => TotalSpace.mk' E₀ y (X y)) := by
    simpa [X] using hX₁
  have hYbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
      (fun y => TotalSpace.mk' E₀ y (Y y)) := by
    simpa [Y] using hY₁
  have hXbundle₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (X y)) := by
    simpa [X] using hX₂
  have hYbundle₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (Y y)) := by
    simpa [Y] using hY₂
  have hRicci : MDiffAt
      (fun y : M₀ => TotalSpace.mk'
        (E₀ →L[ℝ] (E₀ →L[ℝ] ℝ))
        (E := T₂₀) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x := by
    letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
    letI : ContMDiffCovariantDerivative (cov t) 2 := hcovTwo t
    exact RicciFlow.ricciCovariantTwoTensor_mdifferentiableAt
      (I := I₀) (M := M₀) (cov t) x
  have spatialMDiffOfContMDiff
      (W : Π y : M₀, TM₀ y)
      (hWbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y => TotalSpace.mk' E₀ y (W y))) :
      ∀ y, MDiffAt (T% W) y := by
    have hWcont : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1 (T% W) := by
      simpa using hWbundle
    intro y
    exact (hWcont y).mdifferentiableAt one_ne_zero
  rcases exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_intrinsicRicciFlow
      (I := I₀) (M := M₀) g cov hcov hLevi gdot s hflow
      (t := t) ht (X := X) (Y := Y) (x := x) hXbundle₂ hYbundle₂
      (fun W hW => hjointFixedPairing Y W hY
        (spatialMDiffOfContMDiff W
          (hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))))
      (fun W hW => hRicciSpacePairing Y W hY
        (spatialMDiffOfContMDiff W hW))
      (fun W hW => hjointFixedPairing X W hX
        (spatialMDiffOfContMDiff W
          (hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))))
      (fun W hW => hRicciSpacePairing X W hX
        (spatialMDiffOfContMDiff W hW))
      (fun _ _ => hjointFixedPairing X Y hX hY)
      (fun _ _ => hRicciSpacePairing X Y hX hY) with
    ⟨Axy, hAxy, hAcyclic⟩
  let Acanonical := cyclicCovariantTensorVariationVector
    (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x u v
  have hPairing (w : TM₀ x) :
      2 * (g t).inner x Axy w = 2 * (g t).inner x Acanonical w := by
    let W : Π y : M₀, TM₀ y :=
      smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x w
    have hW₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% W) := by
      simpa [W] using smoothExtend_contMDiff_two
        (I := I₀) (F := E₀) (V := TangentSpace I₀) x w
    have hW₁ := hW₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hW : ∀ y, MDiffAt (T% W) y := fun y =>
      (hW₁ y).mdifferentiableAt one_ne_zero
    have hWbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y => TotalSpace.mk' E₀ y (W y)) := by
      simpa [W] using hW₁
    have hWbundle₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y => TotalSpace.mk' E₀ y (W y)) := by
      simpa [W] using hW₂
    have hA := hAcyclic W hWbundle₂
    have hD₁ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_smoothExtend_eq
      (I₁ := I₀) (M₁ := M₀) (g := g) (cov := cov)
      (hcov := hcov) (hLevi := hLevi) u v w hRicci
    have hD₂ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_smoothExtend_eq
      (I₁ := I₀) (M₁ := M₀) (g := g) (cov := cov)
      (hcov := hcov) (hLevi := hLevi) v u w hRicci
    have hD₃ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_smoothExtend_eq
      (I₁ := I₀) (M₁ := M₀) (g := g) (cov := cov)
      (hcov := hcov) (hLevi := hLevi) w u v hRicci
    rw [hD₁, hD₂, hD₃] at hA
    have hA' :
        2 * (g t).inner x Axy w =
          -2 * (CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x u v w +
            CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x v u w -
            CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x w u v) := by
      simpa [W, smoothExtend_apply] using hA
    have hCanonical := cyclicCovariantTensorVariationVector_inner
      (cov := cov t) (h := CovariantDerivative.ricciCovariantTwoTensor (cov t))
      x u v w
    calc
      2 * (g t).inner x Axy w = _ := hA'
      _ = 2 * Inner.inner ℝ Acanonical w := by
        rw [hCanonical]
        ring
      _ = 2 * (g t).inner x Acanonical w := by rfl
  have hVector : Axy = Acanonical := by
    apply ext_inner_right ℝ
    intro w
    have h := hPairing w
    have hleft : (g t).inner x Axy w = Inner.inner ℝ Axy w := rfl
    have hright : (g t).inner x Acanonical w = Inner.inner ℝ Acanonical w := rfl
    rw [hleft, hright] at h
    linarith
  have hDerivCanonical :
      HasDerivAt (fun τ : ℝ => (cov τ).along X Y x) Acanonical t := by
    simpa only [hVector] using hAxy
  simpa [X, Y, Acanonical] using hDerivCanonical

/-! The moving-section bridge above first constructs a pointwise vector and
records its pairing against every smooth test field.  The following lemma
identifies that vector intrinsically, so callers can use the actual Ricci
connection-variation tensor without carrying an existential witness. -/
theorem hasDerivAt_along_moving_of_cyclicRicciIdentification
    [SigmaCompactSpace M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    {t : ℝ} {x : M₀}
    {X : Π y : M₀, TM₀ y} {Y : ℝ → Π y : M₀, TM₀ y}
    (Ydot : Π y : M₀, TM₀ y)
    (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% (Y t)) x)
    (hRicci : MDiffAt
      (fun y : M₀ => TotalSpace.mk'
        (E₀ →L[ℝ] (E₀ →L[ℝ] ℝ)) (E := T₂₀) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x)
    (hmoving : ∃ Axy : TM₀ x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
        ((cov t).along X Ydot x + Axy) t ∧
      ∀ (W : Π y : M₀, TM₀ y),
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
          (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
        2 * (g t).inner x Axy (W x) =
          -2 * (metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t X (Y t) W x +
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t (Y t) X W x -
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t W X (Y t) x)) :
    (letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
     HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
       ((cov t).along X Ydot x +
         cyclicCovariantTensorVariationVector (cov t)
           (CovariantDerivative.ricciCovariantTwoTensor (cov t))
           x (X x) (Y t x)) t) := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  rcases hmoving with ⟨Axy, hderiv, hAcyclic⟩
  let C : TM₀ x := cyclicCovariantTensorVariationVector (cov t)
    (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x (X x) (Y t x)
  have hPairing (w : TM₀ x) :
      2 * (g t).inner x Axy w = 2 * (g t).inner x C w := by
    let W : Π y : M₀, TM₀ y :=
      smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x w
    have hW₂ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% W) := by
      simpa [W] using smoothExtend_contMDiff_two
        (I := I₀) (F := E₀) (V := TangentSpace I₀) x w
    have hW₁ := hW₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hWbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y => TotalSpace.mk' E₀ y (W y)) := by
      simpa using hW₁
    have hA := hAcyclic W hW₂
    have hD₁ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_eq
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      X (Y t) W hY ((hW₁ x).mdifferentiableAt one_ne_zero) hRicci
    have hD₂ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_eq
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (Y t) X W hX ((hW₁ x).mdifferentiableAt one_ne_zero) hRicci
    have hD₃ := metricVelocityCovariantDerivativeAlong_intrinsicRicci_eq
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      W X (Y t) hX hY hRicci
    rw [hD₁, hD₂, hD₃] at hA
    have hCyclic := cyclicCovariantTensorVariationVector_inner
      (cov := cov t)
      (h := CovariantDerivative.ricciCovariantTwoTensor (cov t))
      x (X x) (Y t x) w
    have hA' :
        2 * (g t).inner x Axy w =
          -2 * (CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
              x (X x) (Y t x) w +
            CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
              x (Y t x) (X x) w -
            CovariantDerivative.covariantTwoTensorCovariantDerivative
              (cov t) (CovariantDerivative.ricciCovariantTwoTensor (cov t))
              x w (X x) (Y t x)) := by
      simpa [W, smoothExtend_apply] using hA
    calc
      2 * (g t).inner x Axy w = _ := hA'
      _ = 2 * Inner.inner ℝ C w := by
        rw [hCyclic]
        ring
      _ = 2 * (g t).inner x C w := by rfl
  have hVector : Axy = C := by
    apply ext_inner_right ℝ
    intro w
    have h := hPairing w
    have hleft : (g t).inner x Axy w = Inner.inner ℝ Axy w := rfl
    have hright : (g t).inner x C w = Inner.inner ℝ C w := rfl
    rw [hleft, hright] at h
    linarith
  have hvalue :
      (cov t).along X Ydot x + Axy =
        (cov t).along X Ydot x +
          cyclicCovariantTensorVariationVector (cov t)
            (CovariantDerivative.ricciCovariantTwoTensor (cov t))
            x (X x) (Y t x) := by
    calc
      (cov t).along X Ydot x + Axy =
          (cov t).along X Ydot x + C :=
        congrArg (fun z : TM₀ x => (cov t).along X Ydot x + z) hVector
      _ = _ := rfl
  exact hderiv.congr_deriv hvalue
/-- For fixed spatially differentiable fields, the connection derivative under
an intrinsic Ricci flow is the canonical cyclic Ricci-variation tensor.  This
specialization removes the existential vector from the fixed-field Koszul
formula and is the inner-section derivative used by the curvature
commutator. -/
theorem hasDerivAt_along_fixed_of_intrinsicRicciFlow_and_jointRegularity
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (hcovTwo : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 2)
    {x : M₀} {X Y : Π y : M₀, TM₀ y}
    (hX : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (X y)))
    (hY : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (Y y)))
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% U) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% V) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hRicciSpacePairing : ∀ (U V : Π y : M₀, TM₀ y),
      (∀ y, MDiffAt (T% U) y) → (∀ y, MDiffAt (T% V) y) →
      MDiffAt
        (fun y : M₀ => RicciFlow.intrinsicRicciBilinearAt
          (I := I₀) (M := M₀) g t y (U y) (V y)) x) :
    (letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
     letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
       g.slice_isContMDiffRiemannianBundle t
     HasDerivAt (fun τ : ℝ => (cov τ).along X Y x)
       (cyclicCovariantTensorVariationVector (cov t)
         (CovariantDerivative.ricciCovariantTwoTensor (cov t))
         x (X x) (Y x)) t) := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ := by infer_instance
  have spatialMDiffOfContMDiff
      (W : Π y : M₀, TM₀ y)
      (hW : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y => TotalSpace.mk' E₀ y (W y))) :
      ∀ y, MDiffAt (T% W) y := by
    have hWcont : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1 (T% W) := by
      simpa using hW
    intro y
    exact (hWcont y).mdifferentiableAt one_ne_zero
  have hXsp := spatialMDiffOfContMDiff X
    (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  have hYsp := spatialMDiffOfContMDiff Y
    (hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  have hRicci : MDiffAt
      (fun y : M₀ => TotalSpace.mk'
        (E₀ →L[ℝ] (E₀ →L[ℝ] ℝ)) (E := T₂₀) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x := by
    letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
    letI : ContMDiffCovariantDerivative (cov t) 2 := hcovTwo
    exact RicciFlow.ricciCovariantTwoTensor_mdifferentiableAt
      (I := I₀) (M := M₀) (cov t) x
  rcases exists_hasDerivAt_along_const_with_cyclic_metricVariation_of_intrinsicRicciFlow
      (I := I₀) (M := M₀) g cov hcov hLevi gdot s hflow
      (t := t) ht (X := X) (Y := Y) (x := x) hX hY
      (fun W hW => hjointFixedPairing Y W hY hW)
      (fun W hW => hRicciSpacePairing Y W hYsp
        (spatialMDiffOfContMDiff W hW))
      (fun W hW => hjointFixedPairing X W hX hW)
      (fun W hW => hRicciSpacePairing X W hXsp
        (spatialMDiffOfContMDiff W hW))
      (fun _ _ => hjointFixedPairing X Y hX hY)
      (fun _ _ => hRicciSpacePairing X Y hXsp hYsp) with
    ⟨Axy, hAxy, hAcyclic⟩
  have hzeroAlong : (cov t).along X (fun y : M₀ => (0 : TM₀ y)) x = 0 := by
    change ((cov t) (fun y : M₀ => (0 : TM₀ y)) x) (X x) = 0
    have hcovZero : (cov t) (fun y : M₀ => (0 : TM₀ y)) =
        (0 : Π y : M₀, TM₀ y →L[ℝ] TM₀ y) := by
      exact _root_.CovariantDerivative.zero (cov := cov t)
    rw [hcovZero]
    simp
  let Yconst : ℝ → Π y : M₀, TM₀ y := fun _ => Y
  have hAxyMoving : HasDerivAt
      (fun τ : ℝ => (cov τ).along X (Yconst τ) x)
      ((cov t).along X (fun y : M₀ => (0 : TM₀ y)) x + Axy) t := by
    have hAxy' := hAxy.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun _ => rfl))
    exact hAxy'.congr_deriv (by rw [hzeroAlong]; simp)
  have hmoving : ∃ Axy : TM₀ x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X (Yconst τ) x)
        ((cov t).along X (fun y : M₀ => (0 : TM₀ y)) x + Axy) t ∧
      ∀ (W : Π y : M₀, TM₀ y),
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
          (fun y => TotalSpace.mk' E₀ y (W y)) →
        2 * (g t).inner x Axy (W x) =
          -2 * (metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t X Y W x +
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t Y X W x -
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t W X Y x) := by
    exact ⟨Axy, hAxyMoving, hAcyclic⟩
  have hXat : MDiffAt (T% X) x := hXsp x
  have hYat : MDiffAt (T% (Yconst t)) x := by
    simpa [Yconst] using hYsp x
  have hcanonical := hasDerivAt_along_moving_of_cyclicRicciIdentification
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (t := t) (x := x) (X := X) (Y := Yconst)
    (Ydot := fun y : M₀ => (0 : TM₀ y)) hXat hYat hRicci hmoving
  have hcanonical' := hcanonical.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun _ => rfl))
  have hvalue :
      (cov t).along X (fun y : M₀ => (0 : TM₀ y)) x +
          cyclicCovariantTensorVariationVector (cov t)
            (CovariantDerivative.ricciCovariantTwoTensor (cov t))
            x (X x) (Y x) =
        cyclicCovariantTensorVariationVector (cov t)
          (CovariantDerivative.ricciCovariantTwoTensor (cov t))
          x (X x) (Y x) := by
    rw [hzeroAlong]
    simp
  exact hcanonical'.congr_deriv hvalue
/-- The moving-section Koszul bridge for an intrinsic Ricci flow, with its
existential velocity identified as the canonical cyclic Ricci-variation
tensor.  All time--space commutations remain explicit regularity hypotheses;
the theorem derives the connection derivative and does not assume a curvature
evolution equation. -/
theorem hasDerivAt_along_moving_of_intrinsicRicciFlow_and_jointRegularity_canonical
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [IsManifold I₀ ((3 : ℕ∞) + 1) M₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (hcovTwo : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 2)
    {X : Π y : M₀, TM₀ y} {Y : ℝ → Π y : M₀, TM₀ y}
    (Ydot : Π y : M₀, TM₀ y) {x : M₀}
    (hX : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y ↦ TotalSpace.mk' E₀ y (X y)))
    (hY : ∀ τ : ℝ, ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y ↦ TotalSpace.mk' E₀ y (Y τ y)))
    (hYtime : ∀ y : M₀,
      HasDerivAt (fun τ : ℝ => Y τ y) (Ydot y) t)
    (hYjoint : ContMDiffAt (𝓘(ℝ).prod I₀) (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun p : ℝ × M₀ => TotalSpace.mk' E₀ p.2 (Y p.1 p.2)) (t, x))
    (hYdot : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
      (fun y ↦ TotalSpace.mk' E₀ y (Ydot y)))
    (hjointYZ : ∀ (W : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (Y p.1 p.2) (W p.2)))
    (hmetricSpaceYdotZ : ∀ (W : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
      MDiffAt (fun y : M₀ => (g t).inner y (Ydot y) (W y)) x)
    (hjointXZ : ∀ (W : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (X p.2) (W p.2)))
    (hjointYX : ∀ (W : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (Y p.1 p.2) (X p.2)))
    (hmetricSpaceYdotX : MDiffAt
      (fun y : M₀ => (g t).inner y (Ydot y) (X y)) x)
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y ↦ TotalSpace.mk' E₀ y (U y)) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y ↦ TotalSpace.mk' E₀ y (V y)) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hRicciSpacePairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y ↦ TotalSpace.mk' E₀ y (U y)) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y ↦ TotalSpace.mk' E₀ y (V y)) →
      MDiffAt
        (fun y : M₀ => RicciFlow.intrinsicRicciBilinearAt
          (I := I₀) (M := M₀) g t y (U y) (V y)) x) :
    (letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
     letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
       g.slice_isContMDiffRiemannianBundle t
     let core : InnerProductSpace.Core ℝ (TM₀ x) :=
       ((g t).toRiemannianMetric).toCore x
     letI : NormedAddCommGroup (TM₀ x) :=
       core.toNormedAddCommGroupOfTopology
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : InnerProductSpace ℝ (TM₀ x) :=
       InnerProductSpace.ofCoreOfTopology core
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : AddCommGroup (TM₀ x) :=
       (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
     letI : Module ℝ (TM₀ x) :=
       (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
     letI : TopologicalSpace (TM₀ x) :=
       (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
     HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
       ((cov t).along X Ydot x +
         cyclicCovariantTensorVariationVector (cov t)
           (CovariantDerivative.ricciCovariantTwoTensor (cov t))
           x (X x) (Y t x)) t) := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ := by infer_instance
  let core : InnerProductSpace.Core ℝ (TM₀ x) :=
    ((g t).toRiemannianMetric).toCore x
  letI : NormedAddCommGroup (TM₀ x) :=
    core.toNormedAddCommGroupOfTopology
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : InnerProductSpace ℝ (TM₀ x) :=
    InnerProductSpace.ofCoreOfTopology core
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : AddCommGroup (TM₀ x) :=
    (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
  letI : Module ℝ (TM₀ x) :=
    (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
  letI : TopologicalSpace (TM₀ x) :=
    (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
  have hRicci : MDiffAt
      (fun y : M₀ => TotalSpace.mk'
        (E₀ →L[ℝ] (E₀ →L[ℝ] ℝ)) (E := T₂₀) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) x := by
    letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
    letI : ContMDiffCovariantDerivative (cov t) 2 := hcovTwo
    exact RicciFlow.ricciCovariantTwoTensor_mdifferentiableAt
      (I := I₀) (M := M₀) (cov t) x
  rcases exists_hasDerivAt_along_moving_of_intrinsicRicciFlow_and_jointRegularity
      (I := I₀) (M := M₀) g cov hcov hLevi gdot s hflow
      (t := t) ht (X := X) (Y := Y) (Ydot := Ydot) (x := x)
      hX hY hYtime hYjoint hYdot hjointYZ hmetricSpaceYdotZ
      hjointXZ hjointYX hmetricSpaceYdotX hjointFixedPairing
      hRicciSpacePairing with
    ⟨Axy, hderiv, hcyclic⟩
  have hmoving : ∃ Axy : TM₀ x,
      HasDerivAt (fun τ : ℝ => (cov τ).along X (Y τ) x)
        ((cov t).along X Ydot x + Axy) t ∧
      ∀ (W : Π y : M₀, TM₀ y),
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
          (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
        2 * (g t).inner x Axy (W x) =
          -2 * (metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t X (Y t) W x +
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t (Y t) X W x -
            metricVelocityCovariantDerivativeAlong
              (I := I₀) (M := M₀) cov
              (RicciFlow.intrinsicRicciBilinearAt
                (I := I₀) (M := M₀) g t) t W X (Y t) x) := by
    exact ⟨Axy, hderiv, hcyclic⟩
  have hXat : MDiffAt (T% X) x := by
    have hXbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1 (T% X) := by
      simpa using hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact (hXbundle x).mdifferentiableAt one_ne_zero
  have hYat : MDiffAt (T% (Y t)) x := by
    have hYbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1 (T% (Y t)) := by
      simpa using (hY t).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact (hYbundle x).mdifferentiableAt one_ne_zero
  exact hasDerivAt_along_moving_of_cyclicRicciIdentification
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (t := t) (x := x) (X := X) (Y := Y) Ydot hXat hYat hRicci hmoving

/-- The connection-variation tensor selected by the intrinsic Ricci-flow
velocity ġ = -2 Ric. -/
noncomputable def intrinsicRicciConnectionVariation
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (t : ℝ)
    (hcov : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 1) :
    ∀ x : M₀, TM₀ x → TM₀ x → TM₀ x := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
    g.slice_isContMDiffRiemannianBundle t
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 1 := hcov
  exact fun x u v =>
    cyclicCovariantTensorVariationVector (cov t)
      (CovariantDerivative.ricciCovariantTwoTensor (cov t)) x u v

/-- The velocity of the raw curvature commutator obtained by substituting the
intrinsic Ricci-flow connection variation. -/
noncomputable def intrinsicRicciCurvatureAuxVelocity
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (t : ℝ)
    (hcov : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 1)
    (x : M₀) (X Y Z : Π y : M₀, TM₀ y) : TM₀ x := by
  letI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 1 := hcov
  let A := intrinsicRicciConnectionVariation g cov t hcov
  exact ((cov t).along X (fun y => A y (Y y) (Z y)) x +
      A x (X x) ((cov t).along Y Z x)) -
    ((cov t).along Y (fun y => A y (X y) (Z y)) x +
      A x (Y x) ((cov t).along X Z x)) -
    A x (VectorField.mlieBracket I₀ X Y x) (Z x)

/-- The joint regularity needed to apply the Ricci-flow moving-section
connection rule to one nested covariant derivative.  It records genuine
spacetime regularity of that section and of its metric pairings; it contains
no time derivative or curvature-evolution identity. -/
structure IntrinsicRicciMovingSectionRegularity
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (t : ℝ) (x : M₀) (X : Π y : M₀, TM₀ y)
    (Y : ℝ → Π y : M₀, TM₀ y) (Ydot : Π y : M₀, TM₀ y) : Prop where
  jointSection : ContMDiffAt (𝓘(ℝ).prod I₀) (I₀.prod 𝓘(ℝ, E₀)) 2
    (fun p : ℝ × M₀ => TotalSpace.mk' E₀ p.2 (Y p.1 p.2)) (t, x)
  spatialVelocity : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
    (fun y ↦ TotalSpace.mk' E₀ y (Ydot y))
  jointPairingRight : ∀ (W : Π y : M₀, TM₀ y),
    ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
    ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
      (fun p : ℝ × M₀ => (g p.1).inner p.2 (Y p.1 p.2) (W p.2))
  velocityPairingRight : ∀ (W : Π y : M₀, TM₀ y),
    ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
      (fun y ↦ TotalSpace.mk' E₀ y (W y)) →
    MDiffAt (fun y : M₀ => (g t).inner y (Ydot y) (W y)) x
  jointPairingWithX : ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
    (fun p : ℝ × M₀ => (g p.1).inner p.2 (Y p.1 p.2) (X p.2))
  velocityPairingWithX : MDiffAt
    (fun y : M₀ => (g t).inner y (Ydot y) (X y)) x
/-- Differentiate the actual covariant-derivative commutator under an
intrinsic Ricci flow.  The fixed-field derivatives come from the Koszul
formula, while the two nested terms use the explicit spacetime regularity
packages above.  No generic connection-variation predicate or curvature
evolution equation is an input. -/
theorem hasDerivAt_curvatureAux_of_intrinsicRicciFlow_and_jointRegularity
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [IsManifold I₀ ((3 : ℕ∞) + 1) M₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (hcovTwo : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 2)
    (hcovTwoAll : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 2)
    {X Y Z : Π y : M₀, TM₀ y} (x : M₀)
    (hX : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% X))
    (hY : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% Y))
    (hZ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% Z))
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% U) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% V) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hregularityYZ : IntrinsicRicciMovingSectionRegularity
      g t x X (fun τ : ℝ => (cov τ).along Y Z)
      (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (Y y) (Z y)))
    (hregularityXZ : IntrinsicRicciMovingSectionRegularity
      g t x Y (fun τ : ℝ => (cov τ).along X Z)
      (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (X y) (Z y))) :
    (letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
     letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
       g.slice_isContMDiffRiemannianBundle t
     let core : InnerProductSpace.Core ℝ (TM₀ x) :=
       ((g t).toRiemannianMetric).toCore x
     letI : NormedAddCommGroup (TM₀ x) :=
       core.toNormedAddCommGroupOfTopology
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : InnerProductSpace ℝ (TM₀ x) :=
       InnerProductSpace.ofCoreOfTopology core
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : AddCommGroup (TM₀ x) :=
       (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
     letI : Module ℝ (TM₀ x) :=
       (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
     letI : TopologicalSpace (TM₀ x) :=
       (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
     HasDerivAt (fun τ : ℝ => (cov τ).curvatureAux X Y Z x)
       (intrinsicRicciCurvatureAuxVelocity g cov t (hcov t) x X Y Z) t) := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ := by infer_instance
  let core : InnerProductSpace.Core ℝ (TM₀ x) :=
    ((g t).toRiemannianMetric).toCore x
  letI : NormedAddCommGroup (TM₀ x) :=
    core.toNormedAddCommGroupOfTopology
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : InnerProductSpace ℝ (TM₀ x) :=
    InnerProductSpace.ofCoreOfTopology core
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : AddCommGroup (TM₀ x) :=
    (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
  letI : Module ℝ (TM₀ x) :=
    (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
  letI : TopologicalSpace (TM₀ x) :=
    (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
  let A := intrinsicRicciConnectionVariation g cov t (hcov t)
  let sigmaYZ : ℝ → Π y : M₀, TM₀ y :=
    fun τ y => (cov τ).along Y Z y
  let sigmaXZ : ℝ → Π y : M₀, TM₀ y :=
    fun τ y => (cov τ).along X Z y
  let A_YZ : Π y : M₀, TM₀ y := fun y => A y (Y y) (Z y)
  let A_XZ : Π y : M₀, TM₀ y := fun y => A y (X y) (Z y)
  have spatialMDiffOfContMDiff
      (W : Π y : M₀, TM₀ y)
      (hW : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
        (fun y => TotalSpace.mk' E₀ y (W y))) :
      ∀ y, MDiffAt (T% W) y := by
    have hWcont : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1 (T% W) := by
      simpa using hW
    intro y
    exact (hWcont y).mdifferentiableAt one_ne_zero
  have hRicciSpacePairing : ∀ (U V : Π y : M₀, TM₀ y),
      (∀ y, MDiffAt (T% U) y) → (∀ y, MDiffAt (T% V) y) →
      ∀ y : M₀, MDiffAt
        (fun z : M₀ => RicciFlow.intrinsicRicciBilinearAt
          (I := I₀) (M := M₀) g t z (U z) (V z)) y := by
    intro U V hU hV y
    exact intrinsicRicciPairing_mdifferentiableAt_of_covariantDerivative_two
      (g := g) (cov := cov) hcov hLevi t hcovTwo hU hV y
  have hjointFixedPairing' :
      ∀ (U V : Π y : M₀, TM₀ y),
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
          (fun y => TotalSpace.mk' E₀ y (U y)) →
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
          (fun y => TotalSpace.mk' E₀ y (V y)) →
        ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
          (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)) := by
    intro U V hU hV
    exact hjointFixedPairing U V (by simpa using hU) (by simpa using hV)
  have hRicciSpacePairing' :
      ∀ (U V : Π y : M₀, TM₀ y),
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
          (fun y => TotalSpace.mk' E₀ y (U y)) →
        ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 1
          (fun y => TotalSpace.mk' E₀ y (V y)) →
        MDiffAt
          (fun y : M₀ => RicciFlow.intrinsicRicciBilinearAt
            (I := I₀) (M := M₀) g t y (U y) (V y)) x := by
    intro U V hU hV
    exact hRicciSpacePairing U V
      (spatialMDiffOfContMDiff U hU) (spatialMDiffOfContMDiff V hV) x
  have hX₂ := hX.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZ₂ := hZ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hX₁ := hX₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hY₁ := hY₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hXbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (X y)) := by
    simpa using hX₂
  have hYbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (Y y)) := by
    simpa using hY₂
  have hZbundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (Z y)) := by
    simpa using hZ₂
  have hinnerYZtime : ∀ y : M₀,
      HasDerivAt (fun τ : ℝ => sigmaYZ τ y) (A_YZ y) t := by
    intro y
    have hfixed :=
      hasDerivAt_along_fixed_of_intrinsicRicciFlow_and_jointRegularity
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
        (hcovTwo := hcovTwo) (x := y) (X := Y) (Y := Z)
        hYbundle hZbundle hjointFixedPairing'
        (fun U V hU hV => hRicciSpacePairing U V hU hV y)
    simpa [sigmaYZ, A_YZ, A, intrinsicRicciConnectionVariation] using hfixed
  have hinnerXZtime : ∀ y : M₀,
      HasDerivAt (fun τ : ℝ => sigmaXZ τ y) (A_XZ y) t := by
    intro y
    have hfixed :=
      hasDerivAt_along_fixed_of_intrinsicRicciFlow_and_jointRegularity
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
        (hcovTwo := hcovTwo) (x := y) (X := X) (Y := Z)
        hXbundle hZbundle hjointFixedPairing'
        (fun U V hU hV => hRicciSpacePairing U V hU hV y)
    simpa [sigmaXZ, A_XZ, A, intrinsicRicciConnectionVariation] using hfixed
  have hinnerYZslice : ∀ τ : ℝ,
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y => TotalSpace.mk' E₀ y (sigmaYZ τ y)) := by
    intro τ
    letI : ContMDiffCovariantDerivative (cov τ) 2 := hcovTwoAll τ
    have htemp : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (T% ((cov τ).along Y Z)) :=
      (cov τ).contMDiff_along hY₂ hZ
    simpa [sigmaYZ] using htemp
  have hinnerXZslice : ∀ τ : ℝ,
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (fun y => TotalSpace.mk' E₀ y (sigmaXZ τ y)) := by
    intro τ
    letI : ContMDiffCovariantDerivative (cov τ) 2 := hcovTwoAll τ
    have htemp : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
        (T% ((cov τ).along X Z)) :=
      (cov τ).contMDiff_along hX₂ hZ
    simpa [sigmaXZ] using htemp
  have houter₁ :=
    hasDerivAt_along_moving_of_intrinsicRicciFlow_and_jointRegularity_canonical
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
      (hcovTwo := hcovTwo) (X := X) (Y := sigmaYZ) (Ydot := A_YZ) (x := x)
      hX₂ hinnerYZslice hinnerYZtime hregularityYZ.jointSection
      (by simpa [A_YZ, A, intrinsicRicciConnectionVariation] using
        hregularityYZ.spatialVelocity)
      (fun W hW => by
        simpa [sigmaYZ] using hregularityYZ.jointPairingRight W hW)
      (fun W hW => by
        simpa [A_YZ, A, intrinsicRicciConnectionVariation] using
          hregularityYZ.velocityPairingRight W hW)
      (fun W hW => hjointFixedPairing' X W hXbundle hW)
      (fun _ _ => by
        simpa [sigmaYZ] using hregularityYZ.jointPairingWithX)
      (by
        simpa [A_YZ, A, intrinsicRicciConnectionVariation] using
          hregularityYZ.velocityPairingWithX)
      hjointFixedPairing' hRicciSpacePairing'
  have houter₂ :=
    hasDerivAt_along_moving_of_intrinsicRicciFlow_and_jointRegularity_canonical
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
      (hcovTwo := hcovTwo) (X := Y) (Y := sigmaXZ) (Ydot := A_XZ) (x := x)
      hY₂ hinnerXZslice hinnerXZtime hregularityXZ.jointSection
      (by simpa [A_XZ, A, intrinsicRicciConnectionVariation] using
        hregularityXZ.spatialVelocity)
      (fun W hW => by
        simpa [sigmaXZ] using hregularityXZ.jointPairingRight W hW)
      (fun W hW => by
        simpa [A_XZ, A, intrinsicRicciConnectionVariation] using
          hregularityXZ.velocityPairingRight W hW)
      (fun W hW => hjointFixedPairing' Y W hYbundle hW)
      (fun _ _ => by
        simpa [sigmaXZ] using hregularityXZ.jointPairingWithX)
      (by
        simpa [A_XZ, A, intrinsicRicciConnectionVariation] using
          hregularityXZ.velocityPairingWithX)
      hjointFixedPairing' hRicciSpacePairing'
  have hbracket : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (T% (VectorField.mlieBracket I₀ X Y)) := by
    simpa using (ContDiff.mlieBracket_vectorField (I := I₀)
      (m := (2 : ℕ∞)) (n := (3 : ℕ∞)) hX hY (by norm_num))
  have hbracketBundle : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2
      (fun y => TotalSpace.mk' E₀ y (VectorField.mlieBracket I₀ X Y y)) := by
    simpa using hbracket
  have houter₃ :=
    hasDerivAt_along_fixed_of_intrinsicRicciFlow_and_jointRegularity
      (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
      (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
      (hcovTwo := hcovTwo) (x := x)
      (X := VectorField.mlieBracket I₀ X Y) (Y := Z)
      hbracketBundle hZbundle hjointFixedPairing'
      (fun U V hU hV => hRicciSpacePairing U V hU hV x)
  exact (houter₁.sub houter₂).sub houter₃
/- The raw commutator derivative above is the derivative of the genuine
curvature tensor once its three fixed inputs are chosen by smooth extension.
This is the interface consumed by the Ricci and curvature-operator evolution
proofs; the velocity is still the actual one induced by the intrinsic Ricci
variation of the metric. -/
theorem hasDerivAt_curvatureTensor_of_intrinsicRicciFlow_and_jointRegularity
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [IsManifold I₀ ((3 : ℕ∞) + 1) M₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (hcovTwo : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 2)
    (hcovTwoAll : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 2)
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% U) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% V) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    {x : M₀} {a b c : TM₀ x}
    (hregularityYZ : IntrinsicRicciMovingSectionRegularity
      g t x (smoothExtend (I := I₀) (F := E₀)
        (V := TangentSpace I₀) x a)
      (fun τ : ℝ => (cov τ).along
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x b)
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x c))
      (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x b y)
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x c y)))
    (hregularityXZ : IntrinsicRicciMovingSectionRegularity
      g t x (smoothExtend (I := I₀) (F := E₀)
        (V := TangentSpace I₀) x b)
      (fun τ : ℝ => (cov τ).along
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x a)
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x c))
      (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x a y)
        (smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x c y))) :
    (letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
     letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
       g.slice_isContMDiffRiemannianBundle t
     let core : InnerProductSpace.Core ℝ (TM₀ x) :=
       ((g t).toRiemannianMetric).toCore x
     letI : NormedAddCommGroup (TM₀ x) :=
       core.toNormedAddCommGroupOfTopology
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : InnerProductSpace ℝ (TM₀ x) :=
       InnerProductSpace.ofCoreOfTopology core
         ((g t).toRiemannianMetric.continuousAt x)
         ((g t).toRiemannianMetric.isVonNBounded x)
     letI : AddCommGroup (TM₀ x) :=
       (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
     letI : Module ℝ (TM₀ x) :=
       (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
     letI : TopologicalSpace (TM₀ x) :=
       (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
     HasDerivAt
       (fun τ : ℝ => TimeDependentCovariantDerivative.curvatureTensor
         (I := I₀) (M := M₀) cov hcov τ x a b c)
       (TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
         (I := I₀) (M := M₀) cov
         (intrinsicRicciConnectionVariation g cov t (hcov t)) t x a b c) t) := by
  letI : RiemannianBundle TM₀ := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I₀ 1 E₀ TM₀ :=
    g.slice_isContMDiffRiemannianBundle t
  let core : InnerProductSpace.Core ℝ (TM₀ x) :=
    ((g t).toRiemannianMetric).toCore x
  letI : NormedAddCommGroup (TM₀ x) :=
    core.toNormedAddCommGroupOfTopology
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : InnerProductSpace ℝ (TM₀ x) :=
    InnerProductSpace.ofCoreOfTopology core
      ((g t).toRiemannianMetric.continuousAt x)
      ((g t).toRiemannianMetric.isVonNBounded x)
  letI : AddCommGroup (TM₀ x) :=
    (inferInstance : NormedAddCommGroup (TM₀ x)).toAddCommGroup
  letI : Module ℝ (TM₀ x) :=
    (inferInstance : InnerProductSpace ℝ (TM₀ x)).toModule
  letI : TopologicalSpace (TM₀ x) :=
    (inferInstance : PseudoMetricSpace (TM₀ x)).toUniformSpace.toTopologicalSpace
  let X : Π y : M₀, TM₀ y :=
    smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x a
  let Y : Π y : M₀, TM₀ y :=
    smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x b
  let Z : Π y : M₀, TM₀ y :=
    smoothExtend (I := I₀) (F := E₀) (V := TangentSpace I₀) x c
  have hX : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% X) := by
    simpa [X] using smoothExtend_contMDiff_three
      (I := I₀) (E := E₀) (M := M₀) x a
  have hY : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% Y) := by
    simpa [Y] using smoothExtend_contMDiff_three
      (I := I₀) (E := E₀) (M := M₀) x b
  have hZ : ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 3 (T% Z) := by
    simpa [Z] using smoothExtend_contMDiff_three
      (I := I₀) (E := E₀) (M := M₀) x c
  have hraw := hasDerivAt_curvatureAux_of_intrinsicRicciFlow_and_jointRegularity
    (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
    (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
    (hcovTwo := hcovTwo) (hcovTwoAll := hcovTwoAll)
    (X := X) (Y := Y) (Z := Z) x hX hY hZ
    hjointFixedPairing
    (by simpa [X, Y, Z] using hregularityYZ)
    (by simpa [X, Y, Z] using hregularityXZ)
  simpa [TimeDependentCovariantDerivative.curvatureTensorTimeVelocity,
    intrinsicRicciCurvatureAuxVelocity, intrinsicRicciConnectionVariation,
    TimeDependentCovariantDerivative.curvatureTensor_apply,
    CovariantDerivative.curvatureTensor_apply, X, Y, Z, smoothExtend_apply] using hraw

/-- The pointwise derivative of the actual curvature tensor is automatically
multilinear: each time-slice curvature tensor is multilinear, and uniqueness
of derivatives transfers those identities to its velocity. -/
theorem exists_curvatureTensorVelocityLinearMap_of_hasDerivAt
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    {t : ℝ}
    (velocity : ∀ x : M₀, TM₀ x → TM₀ x → TM₀ x → TM₀ x)
    (hvelocity :
      letI : Bundle.RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      ∀ (x : M₀) (a b c : TM₀ x),
        HasDerivAt
          (fun τ => TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b c)
          (velocity x a b c) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    ∃ curvatureVelocity : ∀ x : M₀,
        TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x,
      ∀ (x : M₀) (a b c : TM₀ x),
        curvatureVelocity x a b c = velocity x a b c := by
  letI : Bundle.RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hAddLeft (x : M₀) (a a' b c : TM₀ x) :
      velocity x (a + a') b c = velocity x a b c + velocity x a' b c := by
    have hsum := hvelocity x (a + a') b c
    have ha := hvelocity x a b c
    have ha' := hvelocity x a' b c
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x (a + a') b c =
          TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a b c +
            TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a' b c := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x (a + a') b c =
        (cov τ).curvatureTensor x a b c + (cov τ).curvatureTensor x a' b c
      exact congrArg (fun L : TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x => L b c)
          (((cov τ).curvatureTensor x).map_add a a')
    exact (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (ha.add ha')
  have hSmulLeft (x : M₀) (r : ℝ) (a b c : TM₀ x) :
      velocity x (r • a) b c = r • velocity x a b c := by
    have hscaled := hvelocity x (r • a) b c
    have ha := hvelocity x a b c
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x (r • a) b c =
          r • TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b c := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x (r • a) b c =
        r • (cov τ).curvatureTensor x a b c
      exact congrArg (fun L : TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x => L b c)
          (((cov τ).curvatureTensor x).map_smul r a)
    exact (hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (ha.const_smul r)
  have hAddMiddle (x : M₀) (a b b' c : TM₀ x) :
      velocity x a (b + b') c = velocity x a b c + velocity x a b' c := by
    have hsum := hvelocity x a (b + b') c
    have hb := hvelocity x a b c
    have hb' := hvelocity x a b' c
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a (b + b') c =
          TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a b c +
            TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a b' c := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x a (b + b') c =
        (cov τ).curvatureTensor x a b c + (cov τ).curvatureTensor x a b' c
      exact congrArg (fun L : TM₀ x →ₗ[ℝ] TM₀ x => L c)
        (((cov τ).curvatureTensor x a).map_add b b')
    exact (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (hb.add hb')
  have hSmulMiddle (x : M₀) (a : TM₀ x) (r : ℝ) (b c : TM₀ x) :
      velocity x a (r • b) c = r • velocity x a b c := by
    have hscaled := hvelocity x a (r • b) c
    have hb := hvelocity x a b c
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a (r • b) c =
          r • TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b c := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x a (r • b) c =
        r • (cov τ).curvatureTensor x a b c
      exact congrArg (fun L : TM₀ x →ₗ[ℝ] TM₀ x => L c)
        (((cov τ).curvatureTensor x a).map_smul r b)
    exact (hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (hb.const_smul r)
  have hAddRight (x : M₀) (a b c c' : TM₀ x) :
      velocity x a b (c + c') = velocity x a b c + velocity x a b c' := by
    have hsum := hvelocity x a b (c + c')
    have hc := hvelocity x a b c
    have hc' := hvelocity x a b c'
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b (c + c') =
          TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a b c +
            TimeDependentCovariantDerivative.curvatureTensor
              (I := I₀) (M := M₀) cov hcov τ x a b c' := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x a b (c + c') =
        (cov τ).curvatureTensor x a b c + (cov τ).curvatureTensor x a b c'
      exact ((cov τ).curvatureTensor x a b).map_add c c'
    exact (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (hc.add hc')
  have hSmulRight (x : M₀) (a b : TM₀ x) (r : ℝ) (c : TM₀ x) :
      velocity x a b (r • c) = r • velocity x a b c := by
    have hscaled := hvelocity x a b (r • c)
    have hc := hvelocity x a b c
    have hpoint (τ : ℝ) :
        TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b (r • c) =
          r • TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b c := by
      letI : ContMDiffCovariantDerivative
          (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
          (V := TangentSpace I₀) (cov τ) 1 := hcov τ
      change (cov τ).curvatureTensor x a b (r • c) =
        r • (cov τ).curvatureTensor x a b c
      exact ((cov τ).curvatureTensor x a b).map_smul r c
    exact (hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => (hpoint τ).symm)).unique (hc.const_smul r)
  refine ⟨fun x =>
    { toFun := fun a =>
        { toFun := fun b =>
            { toFun := fun c => velocity x a b c
              map_add' := by
                intro c c'
                exact hAddRight x a b c c'
              map_smul' := by
                intro r c
                exact hSmulRight x a b r c }
          map_add' := by
            intro b b'
            ext c
            exact hAddMiddle x a b b' c
          map_smul' := by
            intro r b
            ext c
            exact hSmulMiddle x a r b c }
      map_add' := by
        intro a a'
        ext b c
        exact hAddLeft x a a' b c
      map_smul' := by
        intro r a
        ext b c
        exact hSmulLeft x r a b c }, ?_⟩
  intro x a b c
  rfl

/-- Assemble the actual pointwise curvature derivatives obtained from mixed
Ricci-flow regularity into one multilinear curvature-tensor velocity.  The
regularity of both nested covariant derivatives remains explicit; this
theorem supplies a genuine tensor to the intrinsic Ricci trace bridge, not a
curvature-evolution equation. -/
theorem exists_intrinsicRicciCurvatureTensorVelocity_of_jointRegularity
    [ContMDiffVectorBundle 3 E₀ (TangentSpace I₀ : M₀ → Type _) I₀]
    [IsManifold I₀ ((3 : ℕ∞) + 1) M₀]
    [CompactSpace M₀] [Nonempty M₀]
    (g : TimeDependentRiemannianMetric (I := I₀) (M := M₀))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (gdot : RicciFlow.MetricTensorFamily (I := I₀) (M := M₀))
    (s : Set ℝ)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I₀) (M := M₀) g cov hcov gdot s)
    {t : ℝ} (ht : t ∈ s)
    (hcovTwo : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov t) 2)
    (hcovTwoAll : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I₀) (M := M₀) (F := E₀)
      (V := TangentSpace I₀) (cov τ) 2)
    (hjointFixedPairing : ∀ (U V : Π y : M₀, TM₀ y),
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% U) →
      ContMDiff I₀ (I₀.prod 𝓘(ℝ, E₀)) 2 (T% V) →
      ContMDiff (𝓘(ℝ).prod I₀) 𝓘(ℝ) 2
        (fun p : ℝ × M₀ => (g p.1).inner p.2 (U p.2) (V p.2)))
    (hregularityYZ : ∀ (x : M₀) (a b c : TM₀ x),
      IntrinsicRicciMovingSectionRegularity g t x
        (smoothExtend (I := I₀) (F := E₀)
          (V := TangentSpace I₀) x a)
        (fun τ : ℝ => (cov τ).along
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x b)
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x c))
        (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x b y)
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x c y)))
    (hregularityXZ : ∀ (x : M₀) (a b c : TM₀ x),
      IntrinsicRicciMovingSectionRegularity g t x
        (smoothExtend (I := I₀) (F := E₀)
          (V := TangentSpace I₀) x b)
        (fun τ : ℝ => (cov τ).along
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x a)
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x c))
        (fun y : M₀ => intrinsicRicciConnectionVariation g cov t (hcov t) y
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x a y)
          (smoothExtend (I := I₀) (F := E₀)
            (V := TangentSpace I₀) x c y))) :
    letI : Bundle.RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    ∃ curvatureVelocity : ∀ x : M₀,
        TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x →ₗ[ℝ] TM₀ x,
      (∀ (x : M₀) (a b c : TM₀ x),
        curvatureVelocity x a b c =
          TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
            (I := I₀) (M := M₀) cov
            (intrinsicRicciConnectionVariation g cov t (hcov t)) t x a b c) ∧
      (∀ (x : M₀) (a b c : TM₀ x),
        HasDerivAt
          (fun τ => TimeDependentCovariantDerivative.curvatureTensor
            (I := I₀) (M := M₀) cov hcov τ x a b c)
          (curvatureVelocity x a b c) t) ∧
      RicciFlow.HasIntrinsicRicciTimeDerivativeAt
        (I := I₀) (M := M₀) g
        (curvatureTensorVelocityRicci curvatureVelocity) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I₀ : M₀ → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  let velocity : ∀ x : M₀, TM₀ x → TM₀ x → TM₀ x → TM₀ x :=
    fun x a b c =>
      TimeDependentCovariantDerivative.curvatureTensorTimeVelocity
        (I := I₀) (M := M₀) cov
        (intrinsicRicciConnectionVariation g cov t (hcov t)) t x a b c
  have hrawDerivative : ∀ (x : M₀) (a b c : TM₀ x),
      HasDerivAt
        (fun τ => TimeDependentCovariantDerivative.curvatureTensor
          (I := I₀) (M := M₀) cov hcov τ x a b c)
        (velocity x a b c) t := by
    intro x a b c
    simpa [velocity] using
      (hasDerivAt_curvatureTensor_of_intrinsicRicciFlow_and_jointRegularity
        (g := g) (cov := cov) (hcov := hcov) (hLevi := hLevi)
        (gdot := gdot) (s := s) (hflow := hflow) (t := t) ht
        (hcovTwo := hcovTwo) (hcovTwoAll := hcovTwoAll)
        (hjointFixedPairing := hjointFixedPairing)
        (x := x) (a := a) (b := b) (c := c)
        (hregularityYZ x a b c) (hregularityXZ x a b c))
  obtain ⟨curvatureVelocity, hvelocity⟩ :=
    exists_curvatureTensorVelocityLinearMap_of_hasDerivAt
      (g := g) (cov := cov) (hcov := hcov) (t := t)
      velocity hrawDerivative
  refine ⟨curvatureVelocity, ?_, ?_, ?_⟩
  · intro x a b c
    simpa [velocity] using hvelocity x a b c
  · intro x a b c
    exact (hrawDerivative x a b c).congr_deriv
      (hvelocity x a b c).symm
  · exact hasIntrinsicRicciTimeDerivativeAt_of_curvatureTensorTimeDerivative
      g cov hcov hLevi curvatureVelocity (by
        intro x a b c
        exact (hrawDerivative x a b c).congr_deriv
          (hvelocity x a b c).symm)

end CyclicVariation

end CovariantDerivative.TimeDependentRiemannianMetric
