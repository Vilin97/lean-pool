/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyKoszulVariation

/-!
# Moving-section connection variation from Koszul data

The curvature commutator differentiates a connection on a time-dependent inner
section, not only on a section which is constant in time.  This file isolates
the exact scalar bridge needed for that step.  A derivative certificate for
the moving Koszul expression yields the vector-valued connection variation by
metric duality.  No curvature evolution equation is assumed here.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/- The scalar moving-section identity is just the slicewise Koszul formula,
with the time derivative left as an explicit certificate. -/
theorem hasDerivAt_metricConnectionPairing_of_movingKoszulExpression
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    {t : ℝ} {X : Π y : M, TM y}
    (σ : ℝ → Π y : M, TM y) {Z : Π y : M, TM y} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ∀ τ : ℝ, ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (σ τ y)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (Z y)))
    (C : TM x)
    (hKoszulRhs : HasDerivAt
      (fun τ : ℝ => metricKoszulExpression (I := I) (M := M)
        g τ X (σ τ) Z x)
      (2 * ((hdot x ((cov t).along X (σ t) x) (Z x)) +
        (g t).inner x
          C (Z x))) t) :
    HasDerivAt
      (fun τ : ℝ => (g τ).inner x
        ((cov τ).along X (σ τ) x) (Z x))
      (hdot x ((cov t).along X (σ t) x) (Z x) +
        (g t).inner x C (Z x)) t := by
  have hkoszul (τ : ℝ) :
      2 * (g τ).inner x ((cov τ).along X (σ τ) x) (Z x) =
        metricKoszulExpression (I := I) (M := M) g τ X (σ τ) Z x := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    have hk := _root_.CovariantDerivative.koszul_formula
      (I := I) (E := E) (M := M) (cov := cov τ) (hLevi τ)
      (x := x) hX (hσ τ) hZ
    have hinner (y : M) (u v : TM y) :
        (g τ).inner y u v = Inner.inner ℝ u v := rfl
    simpa [metricKoszulExpression, hinner] using hk
  have hfunction :
      (fun τ : ℝ => (g τ).inner x
        ((cov τ).along X (σ τ) x) (Z x)) =
        (fun τ : ℝ => (1 / 2 : ℝ) *
          metricKoszulExpression (I := I) (M := M) g τ X (σ τ) Z x) := by
    funext τ
    apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
    calc
      2 * (g τ).inner x ((cov τ).along X (σ τ) x) (Z x) =
          metricKoszulExpression (I := I) (M := M) g τ X (σ τ) Z x :=
        hkoszul τ
      _ = 2 * ((1 / 2 : ℝ) *
          metricKoszulExpression (I := I) (M := M) g τ X (σ τ) Z x) := by
        ring
  rw [hfunction]
  have hscaled := hKoszulRhs.const_mul (1 / 2 : ℝ)
  exact hscaled.congr_deriv (by ring)

/- The moving scalar pairings determine the vector derivative.  This is the
coordinate-free part of the bridge: positive-definiteness is used only by the
existing finite-dimensional metric-duality theorem. -/
theorem hasDerivAt_along_moving_of_movingKoszulPairings
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E)
      (V := (TangentSpace I : M → Type _)) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov)
    (A : ∀ y : M, TM y → TM y → TM y)
    (hdot : ∀ y : M, TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ)
    {t : ℝ} {X : Π y : M, TM y} (σ : ℝ → Π y : M, TM y)
    (σdot : Π y : M, TM y) {x : M}
    (hmetric : ∀ (y : M) (u v : TM y),
      HasDerivAt (fun τ : ℝ => (g τ).inner y u v) (hdot y u v) t)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (X y)))
    (hσ : ∀ τ : ℝ, ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (σ τ y)))
    (hKoszulRhs : ∀ (Z : Π y : M, TM y),
      ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (Z y)) →
      HasDerivAt
        (fun τ : ℝ => metricKoszulExpression (I := I) (M := M)
          g τ X (σ τ) Z x)
        (2 * (hdot x ((cov t).along X (σ t) x) (Z x) +
          (g t).inner x
            ((cov t).along X σdot x + A x (X x) (σ t x)) (Z x))) t) :
    HasDerivAt
      (fun τ : ℝ => (cov τ).along X (σ τ) x)
      ((cov t).along X σdot x + A x (X x) (σ t x)) t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  have hmetricSwap (τ : ℝ) (u v : TM x) :
      (g τ).inner x u v = (g τ).inner x v u := by
    letI : RiemannianBundle TM := ⟨(g τ).toRiemannianMetric⟩
    change Inner.inner ℝ u v = Inner.inner ℝ v u
    exact (real_inner_comm u v).symm
  have hdotSwap (u v : TM x) : hdot x u v = hdot x v u := by
    have hleft := hmetric x u v
    have hfunction : (fun τ : ℝ => (g τ).inner x u v) =
        (fun τ : ℝ => (g τ).inner x v u) := by
      funext τ
      exact hmetricSwap τ u v
    rw [hfunction] at hleft
    exact hleft.unique (hmetric x v u)
  let C : TM x :=
    (cov t).along X σdot x + A x (X x) (σ t x)
  have hpair : ∀ v : TM x,
      HasDerivAt
        (fun τ : ℝ => (g τ).inner x v
          ((cov τ).along X (σ τ) x))
        (hdot x v ((cov t).along X (σ t) x) +
          (g t).inner x v C) t := by
    intro v
    let Z : Π y : M, TM y :=
      CovariantDerivative.smoothExtend
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hZ₂ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z) := by
      simpa [Z] using CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x v
    have hconn :=
      hasDerivAt_metricConnectionPairing_of_movingKoszulExpression
        (I := I) (M := M) g cov hcov hLevi hdot (t := t)
        (X := X) σ (Z := Z) (x := x) hX hσ
        (hZ₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) C (hKoszulRhs Z hZ₂)
    have hfunction :
        (fun τ : ℝ => (g τ).inner x v
          ((cov τ).along X (σ τ) x)) =
          (fun τ : ℝ => (g τ).inner x
            ((cov τ).along X (σ τ) x) v) := by
      funext τ
      exact hmetricSwap τ v ((cov τ).along X (σ τ) x)
    rw [hfunction]
    have hderiv :
        hdot x ((cov t).along X (σ t) x) (Z x) +
            (g t).inner x C (Z x) =
          hdot x v ((cov t).along X (σ t) x) +
            (g t).inner x v C := by
      have hZx : Z x = v := by
        simp [Z, CovariantDerivative.smoothExtend_apply]
      rw [hZx]
      rw [hdotSwap]
      exact congrArg
        (fun w => ((hdot x) v) ((cov t).along X (σ t) x) + w)
        (hmetricSwap t C v)
    simpa [Z, CovariantDerivative.smoothExtend_apply] using
      hconn.congr_deriv hderiv
  exact hasDerivAt_vector_of_metric_pairings
    (I := I) (M := M) g hdot hmetric (t := t) x
    (fun τ : ℝ => (cov τ).along X (σ τ) x) C hpair

end CovariantDerivative.TimeDependentRiemannianMetric
