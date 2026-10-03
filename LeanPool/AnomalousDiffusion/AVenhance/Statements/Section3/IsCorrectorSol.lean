/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet

/-! Statement file: `IsCorrectorSol` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `e.parabcorr.k` (label 2791) for one direction `e ∈ ℝ²`:
`∂_t χ - κ Δχ + ζ̂_{m,l_k} ζ_{m,k} u_{m,k} · (e + ∇χ) = 0` on `ℝ × ℝ²`, and
`χ = 0` for `t < t*_{m,k} = (-2/3 + k) τ_m`. -/
def IsCorrectorSol (κ : ℝ) (m : ℕ) (k : ℤ) (e : Vec 2) (χ : ℝ → Vec 2 → ℝ) : Prop :=
  (∀ t x, HasDerivAt (fun s => χ s x)
    (κ * spaceLap (χ t) x - I.zetaProd m k t *
      ∑ i : Fin 2, uShear β I.Λ m k x i * (e i + spaceGrad (χ t) x i)) t) ∧
  (∀ t x, t < (-(2 / 3) + (k : ℝ)) * tau β I.Λ m → χ t x = 0)

end Ingredients
end AVenhance
