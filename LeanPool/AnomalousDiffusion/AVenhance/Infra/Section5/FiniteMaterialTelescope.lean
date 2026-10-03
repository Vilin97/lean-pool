/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient

/-! Finite telescoping for source-style material derivatives. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- If each summand's material derivative is the next minus current endpoint
potential, the material derivative of the finite sum is the terminal minus
initial potential. For the source, the summands are `H_{m,r}` and the
potentials are `div Σ_n A_{m,n,r} q_{m,n,r}`; proving their per-index rule
from the `A` and `q` recursions remains source-specific work. -/
theorem finite_material_sum_telescope
    (J : ℕ) (U B : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2)
    (Dt : ℕ → ℝ) (LH : ℕ → Vec 2 →L[ℝ] ℝ)
    (t : ℝ) (x : Vec 2)
    (hDt : ∀ r ∈ Finset.range J,
      HasDerivAt (fun s => U r s x) (Dt r) t)
    (hDx : ∀ r ∈ Finset.range J,
      HasFDerivAt (U r t) (LH r) x)
    (hstep : ∀ r ∈ Finset.range J,
      Dt r + LH r (b t x) = B (r + 1) t x - B r t x) :
    deriv (fun s => ∑ r ∈ Finset.range J, U r s x) t +
      fderiv ℝ (fun y => ∑ r ∈ Finset.range J, U r t y) x (b t x) =
        B J t x - B 0 t x := by
  let S : Finset ℕ := Finset.range J
  have htimeFun : (fun s => ∑ r ∈ S, U r s x) =
      ∑ r ∈ S, fun s => U r s x := by
    funext s
    exact (Finset.sum_apply s S (fun r s => U r s x)).symm
  have hspaceFun : (fun y => ∑ r ∈ S, U r t y) =
      ∑ r ∈ S, fun y => U r t y := by
    funext y
    exact (Finset.sum_apply y S (fun r y => U r t y)).symm
  have htime : HasDerivAt (fun s => ∑ r ∈ S, U r s x)
      (∑ r ∈ S, Dt r) t := by
    rw [htimeFun]
    apply HasDerivAt.sum
    intro r hr
    exact hDt r (by simpa [S] using hr)
  have hspace : HasFDerivAt (fun y => ∑ r ∈ S, U r t y)
      (∑ r ∈ S, LH r) x := by
    rw [hspaceFun]
    apply HasFDerivAt.sum
    intro r hr
    exact hDx r (by simpa [S] using hr)
  have htel : ∀ n : ℕ,
      (∑ r ∈ Finset.range n, (B (r + 1) t x - B r t x)) =
        B n t x - B 0 t x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        rw [ih]
        ring
  have htelJ := htel J
  calc
    deriv (fun s => ∑ r ∈ Finset.range J, U r s x) t +
        fderiv ℝ (fun y => ∑ r ∈ Finset.range J, U r t y) x (b t x) =
      (∑ r ∈ S, Dt r) + ∑ r ∈ S, LH r (b t x) := by
        rw [htime.deriv, hspace.fderiv]
        simp only [sum_apply]
    _ = ∑ r ∈ S, (Dt r + LH r (b t x)) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ r ∈ S, (B (r + 1) t x - B r t x) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hstep r (by simpa [S] using hr)
    _ = B J t x - B 0 t x := by simpa [S] using htelJ

end AVenhance.Infra.Section5
