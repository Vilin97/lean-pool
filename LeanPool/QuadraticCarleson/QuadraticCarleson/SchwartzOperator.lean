/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PVFourier
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticKernelLimit

/-!
# Quadratic Carleson operators on Schwartz functions

The singular integral in the paper is unambiguous on Schwartz functions when
defined by pairing the quadratically modulated principal-value tempered
distribution with `y ↦ f (x - y)`.  This file defines that action and proves
that it is exactly the limit of the paper's symmetric truncations.  It then
defines the full and lacunary pointwise suprema.
-/

open Filter MeasureTheory
open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson

/-- The Schwartz test function `y ↦ f (x - y)` occurring in convolution with
the principal-value kernel. -/
noncomputable def schwartzFlipTranslate (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  (schwartzReflection f).compSubConstCLM ℂ x

@[simp]
theorem schwartzFlipTranslate_apply (f : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    schwartzFlipTranslate f x y = f (x - y) := by
  simp [schwartzFlipTranslate, schwartzReflection_apply]

/-- The paper's fixed-modulation quadratic Hilbert transform, defined
canonically by the tempered distribution `e(λy²) · p.v. (1/y)`. -/
noncomputable def quadraticHilbertSchwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  quadraticKernelDistribution modulation (schwartzFlipTranslate f x)

/-- The distributional action has exactly the paper's symmetrically truncated
integrals before passage to the principal-value limit. -/
theorem quadraticKernelTruncationAction_flipTranslate
    (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticKernelTruncationAction modulation ε (schwartzFlipTranslate f x) =
      quadraticHilbertTrunc modulation ε f x := by
  rw [quadraticKernelTruncationAction_eq_integral]
  unfold quadraticHilbertTrunc
  apply integral_congr_ae
  filter_upwards with y
  simp only [schwartzFlipTranslate_apply]
  ring

/-- On every Schwartz function, the canonical distributional definition is
the ordinary symmetric principal value stated in the paper. -/
theorem hasQuadraticPrincipalValue_schwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasQuadraticPrincipalValue modulation f x
      (quadraticHilbertSchwartz modulation f x) := by
  unfold HasQuadraticPrincipalValue
  simpa only [quadraticKernelTruncationAction_flipTranslate,
    quadraticHilbertSchwartz] using
      tendsto_quadraticKernelTruncationAction modulation (schwartzFlipTranslate f x)

/-- The dyadic modulation `2^n`, for an arbitrary integer exponent. -/
noncomputable def dyadicModulation (n : ℤ) : ℝ :=
  (2 : ℝ) ^ n

theorem dyadicModulation_pos (n : ℤ) : 0 < dyadicModulation n := by
  exact zpow_pos (by norm_num) n

/-- The full quadratic Carleson operator on Schwartz functions.  The value is
extended nonnegative real so an unbounded supremum is represented faithfully. -/
noncomputable def quadraticCarlesonSchwartz (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ≥0∞ :=
  ⨆ modulation : ℝ, ENNReal.ofReal ‖quadraticHilbertSchwartz modulation f x‖

/-- The lacunary quadratic Carleson operator, with modulation set `2^ℤ`. -/
noncomputable def lacunaryQuadraticCarlesonSchwartz
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℤ, ENNReal.ofReal
    ‖quadraticHilbertSchwartz (dyadicModulation n) f x‖

theorem quadraticHilbertSchwartz_le_quadraticCarlesonSchwartz
    (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ENNReal.ofReal ‖quadraticHilbertSchwartz modulation f x‖ ≤
      quadraticCarlesonSchwartz f x :=
  le_iSup (fun a : ℝ ↦ ENNReal.ofReal ‖quadraticHilbertSchwartz a f x‖) modulation

theorem quadraticHilbertSchwartz_le_lacunaryQuadraticCarlesonSchwartz
    (n : ℤ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ENNReal.ofReal ‖quadraticHilbertSchwartz (dyadicModulation n) f x‖ ≤
      lacunaryQuadraticCarlesonSchwartz f x :=
  le_iSup (fun m : ℤ ↦
    ENNReal.ofReal ‖quadraticHilbertSchwartz (dyadicModulation m) f x‖) n

/-- The lacunary operator is pointwise dominated by the full operator. -/
theorem lacunaryQuadraticCarlesonSchwartz_le
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    lacunaryQuadraticCarlesonSchwartz f x ≤ quadraticCarlesonSchwartz f x := by
  apply iSup_le
  intro n
  exact quadraticHilbertSchwartz_le_quadraticCarlesonSchwartz
    (dyadicModulation n) f x

end QuadraticCarleson
