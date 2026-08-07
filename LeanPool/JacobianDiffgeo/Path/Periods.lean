/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Path.HomotopySquare
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Periods of a holomorphic 1-form along a loop (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §6). Carrier decision (CC9
alignment): based loops `Path x x`, with descent to `Path.Homotopic.Quotient x x` available via
`pathIntegralQ`. This unit does not define the period subgroup (jacobian-construction's job); it
exports the loop-algebra lemmas that make `AddSubgroup.closure (Set.range (periodVector b))`
well-behaved.

Main declarations:
* `RS.period γ η` — abbreviation for `pathIntegral γ η` on a based loop.
* `RS.period_trans/symm/refl/congr_homotopic/conj`.
* `RS.periodVector b γ` — the period vector w.r.t. a basis `b` of `Form1 X`, with
  `periodVector_trans/symm/refl`.
-/

open scoped ContDiff Manifold
open IsManifold Module

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x x' : X}

/-- The period of a 1-form along a loop. -/
noncomputable abbrev period (γ : Path x x) (η : Form1 X) : ℂ := pathIntegral γ η

theorem period_trans (γ γ' : Path x x) (η : Form1 X) :
    period (γ.trans γ') η = period γ η + period γ' η := pathIntegral_trans γ γ' η

theorem period_symm (γ : Path x x) (η : Form1 X) : period γ.symm η = -period γ η :=
  pathIntegral_symm γ η

theorem period_refl (η : Form1 X) : period (Path.refl x) η = 0 := pathIntegral_refl x η

theorem period_congr_homotopic {γ γ' : Path x x} (h : γ.Homotopic γ') (η : Form1 X) :
    period γ η = period γ' η := pathIntegral_congr_homotopic h η

/-- Conjugation invariance: periods are basepoint-independent along a connecting path. -/
theorem period_conj (σ : Path x' x) (γ : Path x x) (η : Form1 X) :
    period ((σ.trans γ).trans σ.symm) η = period γ η := by
  change pathIntegral ((σ.trans γ).trans σ.symm) η = pathIntegral γ η
  rw [pathIntegral_trans, pathIntegral_trans, pathIntegral_symm]
  ring

/-- Period vector w.r.t. a basis of `Form1 X` (CC9 feed). -/
noncomputable def periodVector {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    Fin n → ℂ := fun i => period γ (b i)

theorem periodVector_trans {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ γ' : Path x x) :
    periodVector b (γ.trans γ') = periodVector b γ + periodVector b γ' := by
  funext i
  change period (γ.trans γ') (b i) = period γ (b i) + period γ' (b i)
  exact period_trans γ γ' (b i)

theorem periodVector_symm {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    periodVector b γ.symm = -periodVector b γ := by
  funext i
  change period γ.symm (b i) = -period γ (b i)
  exact period_symm γ (b i)

@[simp] theorem periodVector_refl {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) :
    periodVector b (Path.refl x) = 0 := by
  funext i
  change period (Path.refl x) (b i) = 0
  exact period_refl (b i)

end RS

end
