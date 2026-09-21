/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ContinuousMapCalculus
public import LeanPool.PoincareGeometry.LichnerowiczObata.DifferentiableFixedPoint
public import LeanPool.PoincareGeometry.LichnerowiczObata.PathPrimitive
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth parameter dependence of the Picard equation at time zero

The time parameter scales a fixed unit-interval path. The state derivative
of the Picard operator vanishes at time zero, so the implicit-function theorem
applies without a separately assumed smooth flow.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "PE" => C(Icc (0 : ℝ) 1, E)

/-- The scaled Picard equation `α(s) = x + τ ∫₀ˢ v(α(t)) dt`. -/
def picardPathOperator (v : C(E, E)) (z : (E × ℝ) × PE) : PE :=
  ContinuousMap.const _ z.1.1 + z.1.2 • unitPathPrimitiveCLM (continuousMapSuperposition v z.2)

theorem contDiff_picardPathOperator (n : ℕ) (v : C(E, E)) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (picardPathOperator v) := by
  have hC : ContDiff ℝ n (fun z : (E × ℝ) × PE => ContinuousMap.const (Icc (0 : ℝ) 1) z.1.1) :=
    (ContinuousLinearMap.const (R := ℝ) (M := E) (Icc (0 : ℝ) 1)).contDiff.comp
      (contDiff_fst.comp contDiff_fst)
  have hP : ContDiff ℝ n (fun u : PE => unitPathPrimitiveCLM (continuousMapSuperposition v u)) :=
    (unitPathPrimitiveCLM (E := E)).contDiff.comp (contDiff_continuousMapSuperposition n v hv)
  exact hC.add ((contDiff_snd.comp contDiff_fst).smul (hP.comp contDiff_snd))

/-- A continuous local solution of the actual Picard equation inherits the
vector field's smoothness at zero elapsed time. This result still requires
constructing the path-valued solution from the existing ODE flow. -/
theorem contDiffAt_picard_solution_zero (n : ℕ) (hn : n ≠ 0)
    (v : C(E, E)) (hv : ContDiff ℝ n v) {φ : E × ℝ → PE} {x : E}
    (hφ : ContinuousAt φ (x, 0))
    (hfix : ∀ᶠ y in 𝓝 (x, (0 : ℝ)), picardPathOperator v (y, φ y) = φ y) :
    ContDiffAt ℝ n φ (x, 0) := by
  let P : PE → PE := fun u => unitPathPrimitiveCLM (continuousMapSuperposition v u)
  let C : E →L[ℝ] PE := ContinuousLinearMap.const (R := ℝ) (M := E) (Icc (0 : ℝ) 1)
  let A : (E × ℝ) →L[ℝ] PE :=
    C ∘L ContinuousLinearMap.fst ℝ E ℝ +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (P (φ (x, 0)))
  have hnn : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn
  have hPC : ContDiff ℝ n P :=
    (unitPathPrimitiveCLM (E := E)).contDiff.comp (contDiff_continuousMapSuperposition n v hv)
  have hconst : HasStrictFDerivAt (fun z : (E × ℝ) × PE => C z.1.1)
      ((C ∘L ContinuousLinearMap.fst ℝ E ℝ) ∘L ContinuousLinearMap.fst ℝ (E × ℝ) PE)
      ((x, 0), φ (x, 0)) :=
    ((C ∘L ContinuousLinearMap.fst ℝ E ℝ) ∘L ContinuousLinearMap.fst ℝ (E × ℝ) PE).hasStrictFDerivAt
  have ht : HasStrictFDerivAt (fun z : (E × ℝ) × PE => z.1.2)
      ((ContinuousLinearMap.snd ℝ E ℝ) ∘L ContinuousLinearMap.fst ℝ (E × ℝ) PE)
      ((x, 0), φ (x, 0)) :=
    ((ContinuousLinearMap.snd ℝ E ℝ) ∘L ContinuousLinearMap.fst ℝ (E × ℝ) PE).hasStrictFDerivAt
  have hp := (hPC.contDiffAt.hasStrictFDerivAt hnn).comp ((x, (0 : ℝ)), φ (x, 0))
    (hasStrictFDerivAt_snd (p := ((x, (0 : ℝ)), φ (x, 0))))
  have hT : HasStrictFDerivAt (picardPathOperator v) (A.coprod 0) ((x, 0), φ (x, 0)) := by
    have hd := hconst.add (ht.smul hp)
    convert hd using 1 <;> first | rfl |
      (apply ContinuousLinearMap.ext; intro z; apply ContinuousMap.ext; intro t; simp [A, C])
  exact contDiffAt_fixedPoint hnn (contDiff_picardPathOperator n v hv).contDiffAt hT
    (lt_of_eq_of_lt ContinuousLinearMap.opNorm_zero zero_lt_one) hφ hfix

end LichnerowiczObata
