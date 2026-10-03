/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMTimeRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxSymmetry

/-! Time continuity of the homogenized flux from the active shear formula. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace AVenhance.Infra.Section3

open AVenhance

/-- Scalar coefficient of a flux mode, including its cutoff and time corrector. -/
def FluxTimeRegularity.fluxModeCoefficient {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 *
    I.zetaProd m k t * I.corrTime κ m k t

/-- Diagonal matrix direction selected by the flux mode index. -/
def FluxTimeRegularity.fluxModeDirection (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k % 4 = 1 then Matrix.single 1 1 1
  else if k % 4 = 3 then Matrix.single 0 0 1
  else 0

/-- Matrix-valued flux term obtained from one mode coefficient and direction. -/
def FluxTimeRegularity.fluxModeTerm {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  FluxTimeRegularity.fluxModeCoefficient I κ m k t • FluxTimeRegularity.fluxModeDirection k

theorem FluxTimeRegularity.fluxModeTerm_continuous {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) :
    Continuous (fun t => FluxTimeRegularity.fluxModeTerm I κ m k t) := by
  have hz := zetaProd_continuous I (m := m) k
  have hc := corrTime_continuous I (m := m) κ k
  have hcoef : Continuous (fun t => FluxTimeRegularity.fluxModeCoefficient I κ m k t) := by
    dsimp [FluxTimeRegularity.fluxModeCoefficient]
    exact (continuous_const.mul hz).mul hc
  exact hcoef.smul continuous_const

theorem FluxTimeRegularity.flux_eq_active_mode_series {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ) :
    I.flux κ m t = κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ∑' k : ℤ, FluxTimeRegularity.fluxModeTerm I κ m k t := by
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k}, I.zetaMK m k.1 t ≠ 0
  · obtain ⟨⟨k, hkodd⟩, hzk⟩ := hex
    have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
      rcases hkodd with ⟨n, hn⟩
      omega
    have htail (l : ℤ) (hl : l ≠ k) : FluxTimeRegularity.fluxModeTerm I κ m l t = 0 := by
      by_cases hodd : Odd l
      · have hxi0 := xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne
          I hm hkodd hodd hl t hzk
        have hzeta0 : I.zetaMK m l t = 0 := by
          by_contra hne
          have hxi1 := xiMK_eq_one_of_zetaMK_ne_zero I hm l t hne
          rw [hxi0] at hxi1
          norm_num at hxi1
        simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeCoefficient,
            Ingredients.zetaProd,
          hzeta0]
      · have hnot1 : l % 4 ≠ 1 := by
          intro h
          rcases Int.even_or_odd l with he | ho
          · rcases he with ⟨z, hz⟩
            omega
          · exact hodd ho
        have hnot3 : l % 4 ≠ 3 := by
          intro h
          rcases Int.even_or_odd l with he | ho
          · rcases he with ⟨z, hz⟩
            omega
          · exact hodd ho
        simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeDirection, hnot1, hnot3]
    rw [tsum_eq_single k htail]
    rcases hmod with hmod | hmod
    · rw [flux_active_one I hm κ k t hmod hzk]
      simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeCoefficient,
          FluxTimeRegularity.fluxModeDirection, hmod]
    · rw [flux_active_three I hm κ k t hmod hzk]
      simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeCoefficient,
          FluxTimeRegularity.fluxModeDirection, hmod]
  · have hzero : ∀ k : ℤ, Odd k → I.zetaMK m k t = 0 := by
      intro k hk
      by_contra hne
      exact hex ⟨⟨k, hk⟩, hne⟩
    have hterms : (fun k : ℤ => FluxTimeRegularity.fluxModeTerm I κ m k t) = fun _ => 0 := by
      funext k
      by_cases hk1 : k % 4 = 1
      · have hkodd : Odd k := by
          rcases Int.even_or_odd k with he | ho
          · rcases he with ⟨z, hz⟩
            omega
          · exact ho
        simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeDirection,
            FluxTimeRegularity.fluxModeCoefficient,
          Ingredients.zetaProd, hzero k hkodd]
      · by_cases hk3 : k % 4 = 3
        · have hkodd : Odd k := by
            rcases Int.even_or_odd k with he | ho
            · rcases he with ⟨z, hz⟩
              omega
            · exact ho
          simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeDirection,
              FluxTimeRegularity.fluxModeCoefficient,
            Ingredients.zetaProd, hk3, hzero k hkodd]
        · simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeDirection, hk1, hk3]
    rw [hterms]
    simp [flux_eq_kappa_of_no_odd_active I hm κ t hzero]

theorem FluxTimeRegularity.fluxModeTerm_eq_zero_of_xi_zero {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (hxi : I.xiMK m k t = 0) : FluxTimeRegularity.fluxModeTerm I κ m k t = 0 := by
  by_cases hk1 : k % 4 = 1
  · have hzk0 : I.zetaMK m k t = 0 := by
      by_contra hz
      have hone := xiMK_eq_one_of_zetaMK_ne_zero I hm k t hz
      rw [hxi] at hone
      norm_num at hone
    simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeCoefficient,
        FluxTimeRegularity.fluxModeDirection,
      Ingredients.zetaProd, hk1, hzk0]
  · by_cases hk3 : k % 4 = 3
    · have hzk0 : I.zetaMK m k t = 0 := by
        by_contra hz
        have hone := xiMK_eq_one_of_zetaMK_ne_zero I hm k t hz
        rw [hxi] at hone
        norm_num at hone
      simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeCoefficient,
          FluxTimeRegularity.fluxModeDirection,
        hk3, Ingredients.zetaProd, hzk0]
    · simp [FluxTimeRegularity.fluxModeTerm, FluxTimeRegularity.fluxModeDirection, hk1, hk3]

theorem FluxTimeRegularity.fluxModeTerm_eq_bounded_sum {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ t₀ t : ℝ) (N : ℕ)
    (hN : (|t₀| + 1) / tau β I.Λ m + 2 < (N : ℝ))
    (ht : t ∈ Set.Icc (t₀ - 1) (t₀ + 1)) :
    (∑' k : ℤ, FluxTimeRegularity.fluxModeTerm I κ m k t) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), FluxTimeRegularity.fluxModeTerm I κ m k t := by
  classical
  apply tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
  intro k hk
  have hnot : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := hk
  have hterm0 : FluxTimeRegularity.fluxModeTerm I κ m k t = 0 := by
    by_contra hne
    have hxi : I.xiMK m k t ≠ 0 := by
      intro hzero
      exact hne (FluxTimeRegularity.fluxModeTerm_eq_zero_of_xi_zero I hm κ k t hzero)
    have hreal := xiMK_index_abs_bound I t₀ t k ht hxi
    have hN' : |(k : ℝ)| < (N : ℝ) := lt_of_le_of_lt hreal (by linarith)
    have hkiR := abs_le.mp (le_of_lt hN')
    have hkiZ : -(N : ℤ) ≤ k ∧ k ≤ N := by exact_mod_cast hkiR
    exact hnot (Finset.mem_Icc.mpr hkiZ)
  exact hterm0

/-- Every fixed flux entry is continuous in time. The active-mode formula
reduces the spatial average to a locally finite sum of scalar memory terms. -/
theorem flux_entry_time_continuous {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (i j : Fin 2) :
    Continuous (fun t => I.flux κ m t i j) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  obtain ⟨N, hN⟩ := exists_nat_gt ((|t₀| + 1) / tau β I.Λ m + 2)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hlocal : ∀ᶠ t in 𝓝 t₀,
      I.flux κ m t i j =
        (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          ∑ k ∈ S, FluxTimeRegularity.fluxModeTerm I κ m k t) i j := by
    filter_upwards [Ioo_mem_nhds (by linarith : t₀ - 1 < t₀)
      (by linarith : t₀ < t₀ + 1)] with t ht
    have htIcc : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [FluxTimeRegularity.flux_eq_active_mode_series I hm κ t]
    rw [FluxTimeRegularity.fluxModeTerm_eq_bounded_sum I hm κ t₀ t N hN htIcc]
  have hterm (k : ℤ) : Continuous (fun t => FluxTimeRegularity.fluxModeTerm I κ m k t i j) := by
    have h := FluxTimeRegularity.fluxModeTerm_continuous I (m := m) κ k
    have heval : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact heval.comp h
  have hsum : Continuous (fun t =>
      (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, FluxTimeRegularity.fluxModeTerm I κ m k t) i j) := by
    have hmatrix : Continuous (fun t =>
        κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          ∑ k ∈ S, FluxTimeRegularity.fluxModeTerm I κ m k t) := by
      exact continuous_const.add (continuous_finsetSum _
        (fun k _ => FluxTimeRegularity.fluxModeTerm_continuous I (m := m) κ k))
    have heval : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact heval.comp hmatrix
  have hevent : (fun t =>
      (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ∑ k ∈ S, FluxTimeRegularity.fluxModeTerm I κ m k t) i j) =ᶠ[𝓝 t₀]
      (fun t => I.flux κ m t i j) := by
    filter_upwards [hlocal] with t ht
    exact ht.symm
  exact hsum.continuousAt.congr hevent

end AVenhance.Infra.Section3
