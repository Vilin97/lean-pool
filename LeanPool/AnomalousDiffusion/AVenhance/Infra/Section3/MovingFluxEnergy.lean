/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMSupport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxMatrix

/-! The transition-window memory tail in the moving-cutoff energy. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

theorem MovingFluxEnergy.xi_mem_Icc {β : ℝ} (I : Ingredients β) (t : ℝ) :
    0 ≤ I.xi t ∧ I.xi t ≤ 1 := by
  constructor
  · have hnonneg : 0 ≤ indIcc (-(3 / 4 : ℝ)) (3 / 4) t := by
      by_cases ht : t ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) <;>
        simp [indIcc, ht]
    exact hnonneg.trans (I.ind_le_xi t)
  · have hle := I.xi_le_ind t
    have hInd : indIcc (-(5 / 4 : ℝ)) (5 / 4) t ≤ 1 := by
      by_cases ht : t ∈ Set.Icc (-(5 / 4 : ℝ)) (5 / 4) <;>
        simp [indIcc, ht]
    exact hle.trans hInd

/-- The scaled odd transition cutoffs also form a nonnegative partition of
unity. -/
theorem xiMK_odd_partition {β : ℝ} (I : Ingredients β) {m : ℕ}
    (_hm : 1 ≤ m) (t : ℝ) :
    ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t = 1 := by
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hsum := I.xi_partition (t / tau β I.Λ m)
  have hfun : (fun k : {k : ℤ // Odd k} => I.xiMK m k.1 t) =
      fun k => I.xi (t / tau β I.Λ m - (k.1 : ℝ)) := by
    funext k
    change I.xi ((t - (k.1 : ℝ) * tau β I.Λ m) / tau β I.Λ m) = _
    congr 1
    field_simp [ne_of_gt hτ]
  rw [hfun]
  exact hsum

/-- Every scaled transition cutoff lies in `[0,1]`. -/
theorem xiMK_mem_Icc {β : ℝ} (I : Ingredients β) {m : ℕ}
    (_hm : 1 ≤ m) (k : ℤ) (t : ℝ) : I.xiMK m k t ∈ Set.Icc 0 1 := by
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  change I.xi ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ∈ Set.Icc 0 1
  exact MovingFluxEnergy.xi_mem_Icc I _

theorem xiMK_odd_support_finite {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (t : ℝ) :
    {k : {k : ℤ // Odd k} | I.xiMK m k.1 t ≠ 0}.Finite := by
  apply Set.Finite.preimage (f := fun k : {k : ℤ // Odd k} => k.1)
    (s := {j : ℤ | I.xiMK m j t ≠ 0})
  · intro k _ l _ h
    exact Subtype.ext h
  · exact AVenhance.Infra.Section3.xiMK_support_finite I (m := m) hm t

/-- The squared transition weights have total mass at most one. -/
theorem xiMK_odd_sq_tsum_le_one {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (t : ℝ) :
    ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t ^ 2 ≤ 1 := by
  let ξ : {k : ℤ // Odd k} → ℝ := fun k => I.xiMK m k.1 t
  have hfinite : {k : {k : ℤ // Odd k} | ξ k ≠ 0}.Finite := by
    simpa [ξ] using xiMK_odd_support_finite I hm t
  have hsummable : Summable ξ := summable_of_hasFiniteSupport hfinite
  have hsquare : Summable (fun k => ξ k ^ 2) := by
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro k hk
    by_contra hξ
    have hξ0 : ξ k = 0 := not_ne_iff.mp hξ
    simp [hξ0] at hk
  have hpoint (k : {k : ℤ // Odd k}) : ξ k ^ 2 ≤ ξ k := by
    have hξ := xiMK_mem_Icc I hm k.1 t
    dsimp [ξ]
    nlinarith [mul_le_mul_of_nonneg_left hξ.2 hξ.1]
  have hsum := Summable.tsum_le_tsum hpoint hsquare hsummable
  have hpartition : ∑' k : {k : ℤ // Odd k}, ξ k = 1 := by
    simpa [ξ] using xiMK_odd_partition I hm t
  simpa [ξ, hpartition] using hsum

/-- The cutoff-weighted memory square appearing in the diagonal moving energy. -/
def movingCutoffMemoryEnergy {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑' k : {k : ℤ // Odd k},
    I.xiMK m k.1 t ^ 2 * I.corrTime κ m k.1 t ^ 2

/-- Trace of the nonnegative diagonal corrector-energy correction obtained by
the source's active-shear gradient-square formula. -/
def movingCutoffEnergyTrace {β : ℝ} (I : Ingredients β)
    (κ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ *
    movingCutoffMemoryEnergy I κ m t

theorem MovingFluxEnergy.movingCutoffMemoryEnergy_summable {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (t : ℝ) :
    Summable (fun k : {k : ℤ // Odd k} =>
      I.xiMK m k.1 t ^ 2 * I.corrTime κ m k.1 t ^ 2) := by
  apply summable_of_hasFiniteSupport
  apply (xiMK_odd_support_finite I hm t).subset
  intro k hk
  by_contra hxi
  have hxi0 : I.xiMK m k.1 t = 0 := not_ne_iff.mp hxi
  simp [hxi0] at hk

/-- If no small forcing window is active, every memory mode is in its
transition tail.  Its cutoff-weighted squared memory is bounded by the square
of the one-mode relaxation error; the partition of unity sums these tails
without an index-count loss. -/
theorem movingCutoffMemoryEnergy_tail_bound {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (t : ℝ) (hforce : ∀ k : {k : ℤ // Odd k}, I.zetaProd m k.1 t = 0) :
    movingCutoffMemoryEnergy I κ m t ≤
      ((((I.Czeta + I.Chat) / tau β I.Λ m) /
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) ^ 2) ^ 2) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let D := (I.Czeta + I.Chat) / tau β I.Λ m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (add_nonneg (by linarith [I.one_le_Czeta])
      (by linarith [I.one_le_Chat])) hτ.le
  have hmemory (k : {k : ℤ // Odd k}) :
      |I.corrTime κ m k.1 t| ≤ D / ρ ^ 2 := by
    have herr := corrTime_forcingError_le I hm κ hκ k.1 t
    have hscale :
        ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) = D / ρ := by
      dsimp [D, ρ]
      field_simp [ne_of_gt hκ, ne_of_gt hε, ne_of_gt hτ]
    rw [hforce k] at herr
    have herr' : |ρ * I.corrTime κ m k.1 t| ≤ D / ρ := by
      rw [hscale] at herr
      simpa [ρ, abs_neg] using herr
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).2
    have hmul : ρ * |I.corrTime κ m k.1 t| ≤ D / ρ := by
      simpa [abs_mul, abs_of_pos hρ] using herr'
    calc
      |I.corrTime κ m k.1 t| * ρ ^ 2 =
          ρ * (ρ * |I.corrTime κ m k.1 t|) := by ring
      _ ≤ ρ * (D / ρ) := mul_le_mul_of_nonneg_left hmul hρ.le
      _ = D := by field_simp
  have hweights := xiMK_odd_sq_tsum_le_one I hm t
  have hterms := MovingFluxEnergy.movingCutoffMemoryEnergy_summable I hm κ t
  have hmajorSummable : Summable (fun k : {k : ℤ // Odd k} =>
      I.xiMK m k.1 t ^ 2 * (D / ρ ^ 2) ^ 2) := by
    apply summable_of_hasFiniteSupport
    apply (xiMK_odd_support_finite I hm t).subset
    intro k hk
    by_contra hxi
    have hxi0 : I.xiMK m k.1 t = 0 := not_ne_iff.mp hxi
    simp [hxi0] at hk
  have hpoint (k : {k : ℤ // Odd k}) :
      I.xiMK m k.1 t ^ 2 * I.corrTime κ m k.1 t ^ 2 ≤
        I.xiMK m k.1 t ^ 2 * (D / ρ ^ 2) ^ 2 := by
    have hξ : 0 ≤ I.xiMK m k.1 t ^ 2 := sq_nonneg _
    have hmSq := (sq_le_sq₀ (abs_nonneg (I.corrTime κ m k.1 t))
      (div_nonneg hD (sq_nonneg ρ))).2 (hmemory k)
    calc
      I.xiMK m k.1 t ^ 2 * I.corrTime κ m k.1 t ^ 2 =
          I.xiMK m k.1 t ^ 2 * |I.corrTime κ m k.1 t| ^ 2 := by rw [sq_abs]
      _ ≤ I.xiMK m k.1 t ^ 2 * (D / ρ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hmSq hξ
  have hsum := Summable.tsum_le_tsum hpoint hterms hmajorSummable
  rw [show (fun k : {k : ℤ // Odd k} =>
      I.xiMK m k.1 t ^ 2 * (D / ρ ^ 2) ^ 2) =
      fun k => (D / ρ ^ 2) ^ 2 * I.xiMK m k.1 t ^ 2 by
        funext k
        ring] at hsum
  rw [tsum_mul_left] at hsum
  dsimp [movingCutoffMemoryEnergy, D, ρ]
  calc
    (∑' k : {k : ℤ // Odd k},
      I.xiMK m k.1 t ^ 2 * I.corrTime κ m k.1 t ^ 2) ≤
        (D / ρ ^ 2) ^ 2 * ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t ^ 2 := hsum
    _ ≤ (D / ρ ^ 2) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hweights (sq_nonneg _)
    _ = (D / ρ ^ 2) ^ 2 := by ring

/-- In a transition window with no active forcing, the full nonnegative
corrector-energy trace is quadratically small.  Under the source condition
`ε_m² ≤ κ τ_m / 2`, this implies the one-power error scale in
`l.flux.to.energy`. -/
theorem movingCutoffEnergyTrace_tail_bound {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (t : ℝ) (hforce : ∀ k : {k : ℤ // Odd k}, I.zetaProd m k.1 t = 0)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    movingCutoffEnergyTrace I κ m t ≤
      ((I.Czeta + I.Chat) ^ 2 / (64 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  let D := (I.Czeta + I.Chat) / tau β I.Λ m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hratio : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ∧
      epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1 / 2 := by
    constructor
    · positivity
    · apply (div_le_iff₀ (mul_pos hκ hτ)).2
      nlinarith [hcondition]
  have htail := movingCutoffMemoryEnergy_tail_bound I hm κ hκ t hforce
  have hscale :
      8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ * (D / ρ ^ 2) ^ 2 =
        ((I.Czeta + I.Chat) ^ 2 / (32 * Real.pi ^ 4)) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ 2 := by
    dsimp [D, ρ]
    field_simp [ne_of_gt hκ, ne_of_gt hτ, ne_of_gt hε]
    ring
  have hconst : 0 ≤ ((I.Czeta + I.Chat) ^ 2 / (32 * Real.pi ^ 4)) *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by positivity
  calc
    movingCutoffEnergyTrace I κ m t =
        8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ *
          movingCutoffMemoryEnergy I κ m t := rfl
    _ ≤ 8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ * (D / ρ ^ 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ = ((I.Czeta + I.Chat) ^ 2 / (32 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ 2 := hscale
    _ ≤ ((I.Czeta + I.Chat) ^ 2 / (32 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (1 / 2) * (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
      have hr := hratio.2
      have hr0 := hratio.1
      have hrSq : (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ 2 ≤
          (1 / 2) * (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
        nlinarith [mul_nonneg hr0 (by linarith :
          0 ≤ 1 / 2 - epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m))]
      calc
        _ ≤ ((I.Czeta + I.Chat) ^ 2 / (32 * Real.pi ^ 4)) *
            (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
              ((1 / 2) * (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m))) :=
          mul_le_mul_of_nonneg_left hrSq hconst
        _ = _ := by ring
    _ = ((I.Czeta + I.Chat) ^ 2 / (64 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by ring

/-- Uniform version of the inactive-window energy tail.  Its constant is
independent of the particular ingredient once the cutoff derivative fields
are bounded by `C₀`. -/
theorem movingCutoffEnergyTrace_tail_bound_uniform {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (t : ℝ) (hforce : ∀ k : {k : ℤ // Odd k}, I.zetaProd m k.1 t = 0)
    (hcondition : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m / 2) :
    movingCutoffEnergyTrace I κ m t ≤
      (C₀ ^ 2 / (16 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  have hbase := movingCutoffEnergyTrace_tail_bound I hm κ hκ t hforce hcondition
  have hCz0 : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hCh0 : 0 ≤ I.Chat := by linarith [I.one_le_Chat]
  have hC00 : 0 ≤ C₀ := le_trans hCz0 hCz
  have hτ : 0 < tau β I.Λ m := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hratio0 : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) :=
    div_nonneg (sq_nonneg _) (mul_nonneg hκ.le hτ.le)
  have hsum : I.Czeta + I.Chat ≤ 2 * C₀ := by linarith
  have hsum0 : 0 ≤ I.Czeta + I.Chat := add_nonneg hCz0 hCh0
  have hsq : (I.Czeta + I.Chat) ^ 2 ≤ (2 * C₀) ^ 2 := by
    exact (sq_le_sq₀ hsum0 (mul_nonneg (by norm_num) hC00)).2 hsum
  have hscale : 0 ≤
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
        (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by positivity
  calc
    movingCutoffEnergyTrace I κ m t ≤
      ((I.Czeta + I.Chat) ^ 2 / (64 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := hbase
    _ ≤ ((2 * C₀) ^ 2 / (64 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
      have hden : 0 < 64 * Real.pi ^ 4 := by positivity
      gcongr
    _ = (C₀ ^ 2 / (16 * Real.pi ^ 4)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by ring

/-- When one small-scale forcing cutoff is active, the moving corrector-energy
trace contains only that mode: its cutoff weight is one and every other odd
transition weight is zero. -/
theorem movingCutoffEnergyTrace_eq_active_mode {β : ℝ}
    (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (k : ℤ) (hk : Odd k) (t : ℝ) (hzk : I.zetaMK m k t ≠ 0) :
    movingCutoffEnergyTrace I κ m t =
      8 * Real.pi ^ 4 * a β I.Λ m ^ 2 * κ *
        I.corrTime κ m k t ^ 2 := by
  have htail (l : {l : ℤ // Odd l}) (hne : l ≠ ⟨k, hk⟩) :
      I.xiMK m l.1 t ^ 2 * I.corrTime κ m l.1 t ^ 2 = 0 := by
    have hkl : l.1 ≠ k := by
      intro heq
      apply hne
      exact Subtype.ext heq
    have hzero := xiMK_eq_zero_of_zetaMK_ne_zero_of_odd_ne
      I hm hk l.2 hkl t hzk
    simp [hzero]
  have hxi := xiMK_eq_one_of_zetaMK_ne_zero I hm k t hzk
  unfold movingCutoffEnergyTrace movingCutoffMemoryEnergy
  rw [tsum_eq_single ⟨k, hk⟩ htail]
  simp [hxi]

/-- The active diagonal flux entry differs from the moving corrector-energy
trace by the cutoff-derivative error. The displayed constant is uniform over
all ingredients whose two derivative constants are bounded by `C₀`. -/
theorem movingFluxEnergy_active_entry_error {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ)
    (k : ℤ) (t : ℝ) (hk : k % 4 = 1 ∨ k % 4 = 3)
    (hzk : I.zetaMK m k t ≠ 0) :
    |(if k % 4 = 1 then I.flux κ m t 1 1 else I.flux κ m t 0 0) -
        κ - movingCutoffEnergyTrace I κ m t| ≤
      ((C₀ + C₀) / (4 * Real.pi ^ 2)) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
          (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
  have htrace := movingCutoffEnergyTrace_eq_active_mode I hm κ k
    (by
      rcases hk with h1 | h3
      · rcases Int.even_or_odd k with he | ho
        · rcases he with ⟨z, hz⟩
          omega
        · exact ho
      · rcases Int.even_or_odd k with he | ho
        · rcases he with ⟨z, hz⟩
          omega
        · exact ho) t hzk
  rcases hk with h1 | h3
  · have hflux := flux_active_one I hm κ k t h1 hzk
    have hbalance := activeFluxEnergyBalance_one_cutoff_error I hm κ hκ k t h1
    have hfluxEq : I.flux κ m t 1 1 - κ =
        spaceAvg (fun x : Vec 2 => I.zetaProd m k t * psi β I.Λ m k x *
          spaceGrad (fun y => I.chiMK κ m k t y 1) x 0) := by
      rw [hflux]
      simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.add_apply,
          Matrix.smul_apply,
    Matrix.one_apply_eq, Matrix.single_apply_same, add_sub_cancel_left]
      exact (spaceAvg_cross_one I hm κ k t h1
        (ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le))).symm
    have henergyEq : movingCutoffEnergyTrace I κ m t = κ *
        spaceAvg (fun x : Vec 2 =>
          spaceGrad (fun y => I.chiMK κ m k t y 1) x 0 ^ 2) := by
      rw [htrace, spaceAvg_chiMK_gradient_sq_one I hm κ k t h1]
      ring
    have hbound : |I.flux κ m t 1 1 - κ - movingCutoffEnergyTrace I κ m t| ≤
        ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
      rw [hfluxEq, henergyEq]
      exact hbalance
    have hC : I.Czeta + I.Chat ≤ C₀ + C₀ := add_le_add hCz hCh
    have hR : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) :=
      div_nonneg (sq_nonneg _) (mul_nonneg hκ.le (I.tau_pos' m).le)
    simpa [h1] using hbound.trans (by gcongr)
  · have hflux := flux_active_three I hm κ k t h3 hzk
    have hbalance := activeFluxEnergyBalance_three_cutoff_error I hm κ hκ k t h3
    have hfluxEq : I.flux κ m t 0 0 - κ =
        spaceAvg (fun x : Vec 2 => I.zetaProd m k t * psi β I.Λ m k x *
          (-spaceGrad (fun y => I.chiMK κ m k t y 0) x 1)) := by
      rw [hflux]
      simp only [Fin.isValue, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.add_apply,
          Matrix.smul_apply,
    Matrix.one_apply_eq, Matrix.single_apply_same, add_sub_cancel_left, mul_neg]
      have hcross := spaceAvg_cross_three I hm κ k t h3
        (ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le))
      convert hcross.symm using 1; congr 1; ext x; ring
    have henergyEq : movingCutoffEnergyTrace I κ m t = κ *
        spaceAvg (fun x : Vec 2 =>
          spaceGrad (fun y => I.chiMK κ m k t y 0) x 1 ^ 2) := by
      rw [htrace, spaceAvg_chiMK_gradient_sq_three I hm κ k t h3]
      ring
    have hbound : |I.flux κ m t 0 0 - κ - movingCutoffEnergyTrace I κ m t| ≤
        ((I.Czeta + I.Chat) / (4 * Real.pi ^ 2)) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / (2 * κ)) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) := by
      rw [hfluxEq, henergyEq]
      exact hbalance
    have hC : I.Czeta + I.Chat ≤ C₀ + C₀ := add_le_add hCz hCh
    have hR : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) :=
      div_nonneg (sq_nonneg _) (mul_nonneg hκ.le (I.tau_pos' m).le)
    simpa [h3] using hbound.trans (by gcongr)

end AVenhance.Infra.Section3
