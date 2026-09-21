/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalizedCoefficientScaling
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderCauchyOperator

/-!
# Localized finite-cylinder coefficients

This file specializes the compactly supported scaling estimates to the three
coefficient types of a finite-cylinder second-order parabolic operator.  The
principal coefficient is frozen outside the cutoff region, while the first-
and zeroth-order coefficients are cut off and carry their parabolic scaling
weights `r` and `r²`.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance finiteLocalizedFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteLocalizedFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteLocalizedSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteLocalizedSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteLocalizedPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteLocalizedPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteLocalizedFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteLocalizedFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] E) →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α Bχ Kχ R : ℝ}

/-- Principal coefficient frozen to `A c` away from the normalized cutoff. -/
def finiteLocalizedPrincipalCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKA : 0 ≤ KA) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ)
    (A : X → ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hA : ∀ z z', ‖A z - A z'‖ ≤ KA * dist z z') :
    PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :=
  ParabolicC0AlphaSpace.constL
      (X := X) (α := α) (s := parabolicFiniteCylinder X t₀ T) (A c) +
    ParabolicC0AlphaSpace.localizedCenteredRescale
      hBχ hKχ hKA hR hα hα1 χ A c r
      (parabolicFiniteCylinder X t₀ T) hχ hχlip hχsupp hA

@[simp] theorem toFun_finiteLocalizedPrincipalCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKA : 0 ≤ KA) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ)
    (A : X → ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hA : ∀ z z', ‖A z - A z'‖ ≤ KA * dist z z')
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteLocalizedPrincipalCoefficient
          (t₀ := t₀) (T := T)
          hBχ hKχ hKA hR hα hα1 χ A c r hχ hχlip hχsupp hA) z =
      A c + χ z.2 • (A (c + r • z.2) - A c) := by
  rfl

/-- The localized principal field differs from its frozen field by exactly
the centered cutoff-rescaled oscillation. -/
theorem finiteLocalizedPrincipalCoefficient_sub_frozen
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKA : 0 ≤ KA) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ)
    (A : X → ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hA : ∀ z z', ‖A z - A z'‖ ≤ KA * dist z z') :
    finiteLocalizedPrincipalCoefficient
        (t₀ := t₀) (T := T)
        hBχ hKχ hKA hR hα hα1 χ A c r hχ hχlip hχsupp hA -
      ParabolicC0AlphaSpace.constL
        (X := X) (α := α) (s := parabolicFiniteCylinder X t₀ T) (A c) =
      ParabolicC0AlphaSpace.localizedCenteredRescale
        hBχ hKχ hKA hR hα hα1 χ A c r
        (parabolicFiniteCylinder X t₀ T) hχ hχlip hχsupp hA := by
  simp [finiteLocalizedPrincipalCoefficient]

/-- Explicit order-`|r|` norm bound for the principal oscillation. -/
theorem norm_finiteLocalizedPrincipalCoefficient_sub_frozen_le
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKA : 0 ≤ KA) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ)
    (A : X → ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hA : ∀ z z', ‖A z - A z'‖ ≤ KA * dist z z') :
    ‖finiteLocalizedPrincipalCoefficient
        (t₀ := t₀) (T := T)
        hBχ hKχ hKA hR hα hα1 χ A c r hχ hχlip hχsupp hA -
      ParabolicC0AlphaSpace.constL
        (X := X) (α := α) (s := parabolicFiniteCylinder X t₀ T) (A c)‖ ≤
      |r| * (3 * Bχ * KA * R + Bχ * KA + Kχ * KA * R) := by
  rw [finiteLocalizedPrincipalCoefficient_sub_frozen]
  exact ParabolicC0AlphaSpace.norm_localizedCenteredRescale_le
    hBχ hKχ hKA hR hα hα1 χ A c r _ hχ hχlip hχsupp hA

/-- Cutoff first-order coefficient with its normalized parabolic weight `r`. -/
def finiteLocalizedFirstCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBB : 0 ≤ BB) (hKB : 0 ≤ KB)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (B : X → ((X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hBb : ∀ z, ‖B z‖ ≤ BB)
    (hBlip : ∀ z z', ‖B z - B z'‖ ≤ KB * dist z z') :
    FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :=
  r • ParabolicC0AlphaSpace.localizedRescale
    hBχ hKχ hBB hKB hα hα1 χ B c r
    (parabolicFiniteCylinder X t₀ T) hχ hχlip hBb hBlip

@[simp] theorem toFun_finiteLocalizedFirstCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBB : 0 ≤ BB) (hKB : 0 ≤ KB)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (B : X → ((X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hBb : ∀ z, ‖B z‖ ≤ BB)
    (hBlip : ∀ z z', ‖B z - B z'‖ ≤ KB * dist z z')
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteLocalizedFirstCoefficient
          (t₀ := t₀) (T := T)
          hBχ hKχ hBB hKB hα hα1 χ B c r hχ hχlip hBb hBlip) z =
      r • (χ z.2 • B (c + r • z.2)) := by
  rfl

/-- Explicit norm bound for the normalized first-order coefficient. -/
theorem norm_finiteLocalizedFirstCoefficient_le
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBB : 0 ≤ BB) (hKB : 0 ≤ KB)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (B : X → ((X →L[ℝ] E) →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hBb : ∀ z, ‖B z‖ ≤ BB)
    (hBlip : ∀ z z', ‖B z - B z'‖ ≤ KB * dist z z') :
    ‖finiteLocalizedFirstCoefficient
        (t₀ := t₀) (T := T)
        hBχ hKχ hBB hKB hα hα1 χ B c r hχ hχlip hBb hBlip‖ ≤
      |r| * (3 * Bχ * BB + Bχ * KB * |r| + Kχ * BB) := by
  rw [finiteLocalizedFirstCoefficient, norm_smul, Real.norm_eq_abs]
  gcongr
  exact ParabolicC0AlphaSpace.norm_localizedRescale_le
    hBχ hKχ hBB hKB hα hα1 χ B c r _ hχ hχlip hBb hBlip

/-- Cutoff zeroth-order coefficient with its normalized parabolic weight `r²`. -/
def finiteLocalizedZeroCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBC : 0 ≤ BC) (hKC : 0 ≤ KC)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (C : X → (E →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hCb : ∀ z, ‖C z‖ ≤ BC)
    (hClip : ∀ z z', ‖C z - C z'‖ ≤ KC * dist z z') :
    ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α) :=
  r ^ 2 • ParabolicC0AlphaSpace.localizedRescale
    hBχ hKχ hBC hKC hα hα1 χ C c r
    (parabolicFiniteCylinder X t₀ T) hχ hχlip hCb hClip

@[simp] theorem toFun_finiteLocalizedZeroCoefficient
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBC : 0 ≤ BC) (hKC : 0 ≤ KC)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (C : X → (E →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hCb : ∀ z, ‖C z‖ ≤ BC)
    (hClip : ∀ z z', ‖C z - C z'‖ ≤ KC * dist z z')
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (finiteLocalizedZeroCoefficient
          (t₀ := t₀) (T := T)
          hBχ hKχ hBC hKC hα hα1 χ C c r hχ hχlip hCb hClip) z =
      r ^ 2 • (χ z.2 • C (c + r • z.2)) := by
  rfl

/-- Explicit norm bound for the normalized zeroth-order coefficient. -/
theorem norm_finiteLocalizedZeroCoefficient_le
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ)
    (hBC : 0 ≤ BC) (hKC : 0 ≤ KC)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (C : X → (E →L[ℝ] E))
    (c : X) (r : ℝ)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hCb : ∀ z, ‖C z‖ ≤ BC)
    (hClip : ∀ z z', ‖C z - C z'‖ ≤ KC * dist z z') :
    ‖finiteLocalizedZeroCoefficient
        (t₀ := t₀) (T := T)
        hBχ hKχ hBC hKC hα hα1 χ C c r hχ hχlip hCb hClip‖ ≤
      r ^ 2 * (3 * Bχ * BC + Bχ * KC * |r| + Kχ * BC) := by
  rw [finiteLocalizedZeroCoefficient, norm_smul, Real.norm_eq_abs, abs_sq]
  gcongr
  exact ParabolicC0AlphaSpace.norm_localizedRescale_le
    hBχ hKχ hBC hKC hα hα1 χ C c r _ hχ hχlip hCb hClip

end FiniteParabolicC2AlphaBanach
end AnalyticPDE
end RicciFlow
