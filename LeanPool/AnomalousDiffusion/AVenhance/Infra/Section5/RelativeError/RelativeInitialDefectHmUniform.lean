/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectActualSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectSourceScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectGradientUniform

/-! Uniform relative Hm bound on the first positive half-cell. The actual
endpoint estimates use the one-letter mixed budget through terminal Jcut. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section4
open AVenhance.Infra.Section5.LeftToShow
namespace AVenhance.Infra.Section5.RelativeError

/-- Actual normalized endpoint gradient profiles imply a uniform positive-time
Hm estimate. Constants and the threshold precede the ingredient package. -/
theorem relative_initial_Hm_uniform_of_gradient_profiles (β C₀ CA : ℝ) (hCA : 0 ≤ CA) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∃ Λ₀ : ℝ,
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λ₀ ≤ (I.Λ : ℝ) → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, ∀ hΦ : IsStreamSeq I Φ,
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ → ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
      ∀ (g : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ) (T : ℕ → ℝ → Vec 2 → ℝ),
      IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) g θprev →
      I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) g θprev T →
      ∀ S : ℝ, 0 ≤ S →
      (∀ r, r ≤ Jcut β → ∀ n ∈ Finset.range (Nstar β),
        eLpNorm (amnrSpatialGradientTensor I hΦ m (I.kappaSeq κ M m)
          (T (Nstar β)) n r) 2 (volume.restrict timeCube) ≤
        ENNReal.ofReal (CA * S * (epsilon β I.Λ m ^ 2 / I.kappaSeq κ M m) /
          Real.sqrt (I.kappaSeq κ M (m - 1)) *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) * ((tauP β I.Λ m)⁻¹) ^ r)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) (tauPP β I.Λ m / 2),
        Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
          CH * epsilon β I.Λ (m - 1) ^ delta β * S := by
  obtain ⟨K, hK1, hK⟩ := left_to_show_scales β C₀
  obtain ⟨c, C, hc, hcC, hA5⟩ := l_recurse β C₀
  obtain ⟨Λc, hcond⟩ := left_to_show_condition β C₀
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hC0 : 0 ≤ C := (hc.trans hcC).le
  let CE := 2 * ((Nstar β : ℝ) * (8 * (4 * Real.pi ^ 2 * max C₀ 0) * CA * K))
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨2 * CE * Real.sqrt C, by positivity, max Λc (4 ^ (1 / delta β)), ?_⟩
  intro I hz hx hh hΛ₀ Φ hΦ κ hκp M hM hperm m hm hmM g θprev T hθ hT S hS hprofile t ht
  have hm1 : 1 ≤ m := by omega
  have hΛc := (le_max_left Λc (4 ^ (1 / delta β))).trans hΛ₀
  have hbig := (le_max_right Λc (4 ^ (1 / delta β))).trans hΛ₀
  obtain ⟨hκm, hκle, -, hX, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm hmM
  have hν : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hκle
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
  have hτ := I.tau_pos' m
  have hcondm := hcond I hz hx hh hΛc κ hκp M hM hperm m hm hmM
  have hratio : epsilon β I.Λ m ^ 2 / (I.kappaSeq κ M m * tau β I.Λ m) ≤ 1 := by
    apply (div_le_one (mul_pos hκm hτ)).mpr
    exact hcondm.trans (half_le_self (mul_pos hκm hτ).le)
  have hE4 := leh_epsilon_rpow_delta_le I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m - 1) (by omega) hbig
  have htime : 8 * tau β I.Λ m / tauP β I.Λ m ≤ 1 := by
    have hr := (time_ratio_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := m) hm1).2
    rw [mul_div_assoc]
    have hh' : 8 * (tau β I.Λ m / tauP β I.Λ m) ≤ 1 / 2 := by
      nlinarith only [hr, hE4]
    exact hh'.trans (by norm_num)
  let L := epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))
  have hL : 0 ≤ L := Real.rpow_nonneg he.le _
  have hsource := relative_initial_material_source_L2_of_gradient_profiles I hΦ hm1 hκm hν
    hθ hT (hz.trans (le_max_left C₀ 0)) hCA hL hS hratio htime hX hprofile
  have hsource' : eLpNorm (fun z : ℝ × Vec 2 =>
      AVenhance.Infra.Section5.hmEndpoint I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) (Jcut β) z.1 z.2 -
        AVenhance.Infra.Section5.hmEndpoint I hΦ m (I.kappaSeq κ M m) (T (Nstar β)) 0 z.1 z.2) 2
      (volume.restrict timeCube) ≤ ENNReal.ofReal (CE * Real.sqrt (I.kappaSeq κ M (m - 1)) * L *
          S) := by
    convert hsource using 1
    congr 1
    dsimp [CE, L]
    ring
  have hback := relative_initial_Hm_backward_of_source_L2 I hΦ hm1 hκm hθ hT
    (by positivity : 0 ≤ CE * Real.sqrt (I.kappaSeq κ M (m - 1)) * L * S)
    (relative_initial_half_cell_lt_one I hm1) hsource' t ht
  have hνupper := ((hA5 I hz hx hh κ hκp M hM hperm).1
    (m - 1) (by omega) (by omega)).2
  have hνL := relative_initial_diffusivity_rate_cancel he hνupper
  have hat := (amplitude_tauPP_bounds I.one_lt_beta I.beta_lt I.two_pow_seven_le
    (m := m) hm1).2
  have hτPP : 0 ≤ tauPP β I.Λ m :=
    (Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hatpp : tauPP β I.Λ m * a β I.Λ (m - 1) ≤
      (2 : ℝ) ^ (-25 : ℤ) * epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    simpa only [mul_comm] using hat
  have hat' : tauPP β I.Λ m * a β I.Λ (m - 1) ≤ epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
    hatpp.trans (by
      exact mul_le_of_le_one_left (Real.rpow_nonneg he.le _)
        (by norm_num : (2 : ℝ) ^ (-25 : ℤ) ≤ 1))
  have hpow : (epsilon β I.Λ (m - 1) ^ delta β) ^ 2 =
      epsilon β I.Λ (m - 1) ^ (2 * delta β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have hscale : (tauPP β I.Λ m / 2) * I.kappaSeq κ M (m - 1) * L ^ 2 ≤
      C * (epsilon β I.Λ (m - 1) ^ delta β) ^ 2 := by
    calc
      _ = (tauPP β I.Λ m / 2) * (I.kappaSeq κ M (m - 1) * L ^ 2) := by ring
      _ ≤ (tauPP β I.Λ m / 2) * (C * a β I.Λ (m - 1)) :=
        mul_le_mul_of_nonneg_left hνL (by positivity)
      _ ≤ tauPP β I.Λ m * (C * a β I.Λ (m - 1)) :=
        mul_le_mul_of_nonneg_right (half_le_self hτPP) (by
          have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
          positivity)
      _ = C * (tauPP β I.Λ m * a β I.Λ (m - 1)) := by ring
      _ ≤ C * epsilon β I.Λ (m - 1) ^ (2 * delta β) :=
        mul_le_mul_of_nonneg_left hat' hC0
      _ = _ := by rw [hpow]
  exact hback.trans (relative_initial_source_time_absorb (by positivity) hν.le hL hCE
    hC0 (Real.rpow_nonneg he.le _) hS hscale)

end AVenhance.Infra.Section5.RelativeError
