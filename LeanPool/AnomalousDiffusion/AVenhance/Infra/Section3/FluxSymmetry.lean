/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.TimeMemorySymmetry

/-! The time shift by two large cells exchanges the active flux direction. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The small shear cutoff is invariant under shifting time by two large cells
and its integer mode by twice the number of small cells in a large cell. -/
theorem zetaMK_add_twoCellCount {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (t : ℝ) :
    I.zetaMK m (k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ))
      (t + 2 * tauPP β I.Λ m) = I.zetaMK m k t := by
  have hτ := Infra.Ingredients.tau_pos (m := m)
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hratio := Infra.Ingredients.tauPP_eq_cellCount_mul_tau
    (β := β) (Λ := I.Λ) (m := m) hm
  change I.zeta ((t + 2 * tauPP β I.Λ m -
      ((k + 2 * (Infra.Ingredients.tauCellCount β I.Λ m : ℤ) : ℤ) : ℝ) *
        tau β I.Λ m) / tau β I.Λ m) =
    I.zeta ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m)
  rw [hratio]
  push_cast
  field_simp [ne_of_gt hτ]
  ring_nf

/-- Entrywise covariance of the fixed-time flux under the large-cell time shift
and coordinate swap. -/
theorem flux_add_twoCellCount_swap {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) (i j : Fin 2) :
    I.flux κ m (t + 2 * tauPP β I.Λ m) i j =
      I.flux κ m t (if i = 0 then 1 else 0) (if j = 0 then 1 else 0) := by
  classical
  let p := Infra.Ingredients.tauCellCount β I.Λ m
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · rcases hex with ⟨⟨k, hodd⟩, hzk⟩
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hodd with ⟨n, hn⟩
      omega
    have hkshift : (k + 2 * (p : ℤ)) % 4 =
        if k % 4 = 1 then 3 else 1 := by
      have hp := tauCellCount_mod_four β I.Λ m
      by_cases hk1 : k % 4 = 1
      · simp only [hk1, ite_true]
        omega
      · have hk3 : k % 4 = 3 := by
          rcases hmod with hk | hk
          · exact (hk1 hk).elim
          · exact hk
        simp only [hk1, ite_false]
        omega
    have hzkshift : I.zetaMK m (k + 2 * (p : ℤ))
        (t + 2 * tauPP β I.Λ m) ≠ 0 := by
      rw [zetaMK_add_twoCellCount I hm k t]
      exact hzk
    have hzprod := zetaProd_add_twoCellCount I hm k t
    have hmemory := corrTime_add_twoCellCount I hm κ k t
    have hcoeff :
        2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
          I.zetaProd m (k + 2 * (p : ℤ)) (t + 2 * tauPP β I.Λ m) *
          I.corrTime κ m (k + 2 * (p : ℤ)) (t + 2 * tauPP β I.Λ m) =
        2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
          I.zetaProd m k t * I.corrTime κ m k t := by
      rw [hzprod, hmemory]
    have hfluxOld : I.flux κ m t =
        κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
            I.zetaProd m k t * I.corrTime κ m k t) •
              (if k % 4 = 1 then Matrix.single 1 1 1
                else Matrix.single 0 0 1) := by
      rcases hmod with hk | hk
      · rw [flux_active_one I hm κ k t hk hzk]
        simp [hk]
      · rw [flux_active_three I hm κ k t hk hzk]
        simp [hk]
    have hfluxNew : I.flux κ m (t + 2 * tauPP β I.Λ m) =
        κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
            I.zetaProd m k t * I.corrTime κ m k t) •
              (if k % 4 = 1 then Matrix.single 0 0 1
                else Matrix.single 1 1 1) := by
      rcases hmod with hk | hk
      · have hnew : (k + 2 * (p : ℤ)) % 4 = 3 := by
          rw [hkshift]
          simp [hk]
        rw [flux_active_three I hm κ (k + 2 * (p : ℤ))
          (t + 2 * tauPP β I.Λ m) hnew hzkshift]
        rw [hcoeff]
        simp [hk]
      · have hnew : (k + 2 * (p : ℤ)) % 4 = 1 := by
          rw [hkshift]
          simp [hk]
        rw [flux_active_one I hm κ (k + 2 * (p : ℤ))
          (t + 2 * tauPP β I.Λ m) hnew hzkshift]
        rw [hcoeff]
        simp [hk]
    rw [hfluxNew, hfluxOld]
    rcases hmod with hk | hk
    · fin_cases i <;> fin_cases j <;>
        simp [hk, Matrix.smul_apply]
    · fin_cases i <;> fin_cases j <;>
        simp [hk, Matrix.smul_apply]
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    have hzeroShift : ∀ k : ℤ, Odd k →
        I.zetaMK m k (t + 2 * tauPP β I.Λ m) = 0 := by
      intro k hk
      let k' := k - 2 * (p : ℤ)
      have hodd' : Odd k' := by
        rcases hk with ⟨n, hn⟩
        refine ⟨n - p, ?_⟩
        dsimp [k']
        omega
      have hz := hzero k' hodd'
      have hshift := zetaMK_add_twoCellCount I hm k' t
      have hidx : k' + 2 * (p : ℤ) = k := by
        dsimp [k']
        ring
      rw [hidx] at hshift
      rw [hshift]
      exact hz
    rw [flux_eq_kappa_of_no_odd_active I hm κ t hzero,
      flux_eq_kappa_of_no_odd_active I hm κ (t + 2 * tauPP β I.Λ m)
        hzeroShift]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply]

/-- A second simultaneous time shift restores each flux entry, so the
fixed-time flux has period `4 τ''_m`. -/
theorem flux_fourCell_periodic {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t : ℝ) (i j : Fin 2) :
    I.flux κ m (t + 2 * tauPP β I.Λ m + 2 * tauPP β I.Λ m) i j =
      I.flux κ m t i j := by
  let swap : Fin 2 → Fin 2 := fun a => if a = 0 then 1 else 0
  calc
    I.flux κ m (t + 2 * tauPP β I.Λ m + 2 * tauPP β I.Λ m) i j =
        I.flux κ m (t + 2 * tauPP β I.Λ m) (swap i) (swap j) := by
          simpa [swap] using flux_add_twoCellCount_swap I hm κ
            (t + 2 * tauPP β I.Λ m) i j
    _ = I.flux κ m t (swap (swap i)) (swap (swap j)) := by
          simpa [swap] using flux_add_twoCellCount_swap I hm κ t
            (swap i) (swap j)
    _ = I.flux κ m t i j := by
          fin_cases i <;> fin_cases j <;> rfl

end AVenhance.Infra.Section3
