/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FiniteMaterialTelescope
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm

/-! source endpoint potentials and the finite `H_m` telescope. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The endpoint flux potential at order `r`, namely
`div Σ_n A_{m,n,r} q_{m,n,r}`. -/
def hmEndpoint (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (r : ℕ) (t : ℝ) (x : Vec 2) : ℝ :=
  vecDiv (fun y i => ∑ n ∈ Finset.range (Nstar β),
    ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κ n T r t y i j k * I.qMNR κ m n r t j k) x

/-- The sum for `H_m` telescopes to its endpoint potentials once
the source-specific per-index `A`/`q` transport rule is proved. The rule
`hstep` is the remaining analytic input; this wrapper only performs the finite
sum differentiation and telescope. -/
theorem frozen_hm_material_telescope
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (x : Vec 2) (Dt : ℕ → ℝ)
    (LH : ℕ → Vec 2 →L[ℝ] ℝ)
    (hDt : ∀ r ∈ Finset.range (Jcut β),
      HasDerivAt (fun s => I.Hmr hΦ m κ T r s x) (Dt r) t)
    (hDx : ∀ r ∈ Finset.range (Jcut β),
      HasFDerivAt (I.Hmr hΦ m κ T r t) (LH r) x)
    (hstep : ∀ r ∈ Finset.range (Jcut β),
      Dt r + LH r (b t x) =
        hmEndpoint I hΦ m κ T (r + 1) t x -
          hmEndpoint I hΦ m κ T r t x) :
    deriv (fun s => I.Hm hΦ m κ T s x) t +
      fderiv ℝ (I.Hm hΦ m κ T t) x (b t x) =
        hmEndpoint I hΦ m κ T (Jcut β) t x -
          hmEndpoint I hΦ m κ T 0 t x := by
  change deriv (fun s => ∑ r ∈ Finset.range (Jcut β),
      I.Hmr hΦ m κ T r s x) t +
    fderiv ℝ (fun y => ∑ r ∈ Finset.range (Jcut β),
      I.Hmr hΦ m κ T r t y) x (b t x) = _
  exact finite_material_sum_telescope (Jcut β)
    (fun r => I.Hmr hΦ m κ T r)
    (hmEndpoint I hΦ m κ T) b Dt LH t x hDt hDx hstep

end AVenhance.Infra.Section5

end
