/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds

/-! Source-form hypotheses for the Section 2 material estimates.

The quantitative bounds here are stated as hypotheses; they are discharged for all
material orders in `MaterialGoalAllOrders`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

/-- Coordinatewise material iterates of a vector field, using the scalar
material derivative already used for Jacobian entries. -/
def materialIterateVector (b : ℝ → Vec 2 → Vec 2) (ell : ℕ)
    (F : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x i => constructionMaterialIterate b ell (fun r y => F r y i) t x

/-- One coordinate of the material derivative of the spatial gradient of a
vector field. -/
def materialIterateGradientEntry (b : ℝ → Vec 2 → Vec 2) (ell : ℕ)
    (F : ℝ → Vec 2 → Vec 2) (i j : Fin 2) : ℝ → Vec 2 → ℝ :=
  constructionMaterialIterate b ell
    (fun r x => fderiv ℝ (F r) x (basisVec j) i)

/-- `p.material.goal` in coordinate Fréchet-derivative form at one scale.
The second line is stated on its defined range `n ≥ 1`, since the paper's
display `∇^(n-1)` is undefined at `n = 0`. -/
structure PMaterialGoalSourceData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (Cmat : ℝ) (m : ℕ) : Prop where
  constant_ge_one : 1 ≤ Cmat
  velocity_material_bound : ∀ n ell : ℕ,
    1 ≤ n + ell → n + ell ≤ Nstar β → ∀ t : ℝ, ∀ x : Vec 2,
      ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (materialIterateVector (streamVel (Φ m)) ell (streamVel (Φ m)) t)
          x (fun k => basisVec (J k))‖ ≤
            Cmat * epsilon β I.Λ m ^ (β - 1) *
              (epsilon β I.Λ m ^ (β - 2)) ^ ell *
              (epsilon β I.Λ m)⁻¹ ^ n
  gradient_material_bound : ∀ n ell : ℕ,
    1 ≤ n → n + ell ≤ Nstar β → ∀ t : ℝ, ∀ x : Vec 2,
      ∀ i j : Fin 2, ∀ J : Fin (n - 1) → Fin 2,
        ‖iteratedFDeriv ℝ (n - 1)
          (materialIterateGradientEntry (streamVel (Φ m)) ell
            (streamVel (Φ m)) i j t) x (fun k => basisVec (J k))‖ ≤
              Cmat * epsilon β I.Λ m ^ (β - 2) *
                (epsilon β I.Λ m ^ (β - 2)) ^ ell *
                (epsilon β I.Λ m)⁻¹ ^ (n - 1)

/-- Iteration of an ordinary time derivative, for the displayed
`∂ₜ^ell` in `c.material.goal`. -/
def iteratedTimeDerivative {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] :
    ℕ → (ℝ → α) → ℝ → α
  | 0, f => f
  | ell + 1, f => fun t => deriv (iteratedTimeDerivative ell f) t

/-- The inverse Jacobian pulled back along the forward flow, as in the
left-hand side of `c.material.goal`. -/
noncomputable def inverseJacobianPulledBack {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) (s r : ℝ)
    (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  constructionFlowInvJacobian hseq m r s
    (constructionFlow hseq m (s + r) x s)

/-- `c.material.goal` in componentwise form at one scale. Its quantitative
input is recorded separately from `PMaterialGoalSourceData` until the
space-time chain-rule argument from `p.material.goal` is formalized. -/
structure CMaterialGoalSourceData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ)
    (Cmat : ℝ) (m : ℕ) : Prop where
  pulled_inverse_jacobian_bound : ∀ s r : ℝ,
    |r| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
          ‖iteratedFDeriv ℝ n
            (fun y => iteratedTimeDerivative ell
              (fun q => inverseJacobianPulledBack hseq m s q y
                (basisVec j) i) r)
            x (fun k => basisVec (J k))‖ ≤
              Cmat * (epsilon β I.Λ m)⁻¹ ^ n *
                (epsilon β I.Λ m ^ (β - 2)) ^ ell

end AVenhance.Infra.Construction
