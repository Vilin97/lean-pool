/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm

/-! # Source hypotheses of the `L²_x → L¹` analyticity bridge

The two source estimates that feed the composed-analyticity bridge: the all-orders `L∞_t L²_x`
part of `e.Tm.reg.upgrade` and the flow bound `e.flow.for.ergodic`.
-/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.AnalyticBridge

open AVenhance

/-- `e.Tm.reg.upgrade`, the `L∞_t L²_x` part, for every order `n` (multi-index form, `t ∈ [0,1]`),
with constant `A` and length scale `ρ = e^{1+γ/2}`. -/
def TmRegUpgradeLinfL2 (A ρ : ℝ) (θ₀ : Vec 2 → ℝ) (T : ℝ → Vec 2 → ℝ) : Prop :=
  ∀ n : ℕ, ∀ i : Fin n → Fin 2, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => iteratedFDeriv ℝ n (T t) x (fun j => basisVec (i j)))) ≤
      A * Real.sqrt (l2NormSq θ₀) * n.factorial * (A / ρ) ^ n

/-- `e.flow.for.ergodic` (7066–7071) for one flow slice `X`, length scale `e = ε_{m-1}`. -/
def FlowForErgodicBound (A e : ℝ) (X : Vec 2 → Vec 2) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    AVenhance.FaaDiBruno.derivativeSup n X ≤ ENNReal.ofReal (A * n.factorial * (A / e) ^ (n - 1))

end AVenhance.Infra.Section5.AnalyticBridge

end
