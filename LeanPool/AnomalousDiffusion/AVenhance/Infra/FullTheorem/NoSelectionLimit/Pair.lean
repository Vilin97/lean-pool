/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Middle

/-! # The pair estimate: `θ(κ_j)` and `θ(κ_{j'})` are close in sup-`L²`

Five-term splitting: tail (`tail_sup`), one step of the step-down estimate, the middle term (two
    diffusivities, flip-flop
parity), the telescoped step-down steps of the longer chain, tail. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem pair_bound (β C₀ : ℝ) :
    ∃ Λc ρ : ℝ, 0 < ρ ∧ ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ →
      Λc ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ φ : ℝ → Vec 2 → ℝ, (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, (t = 1 / 2 ∨ t = 2) →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ θ : ℝ → ℝ → Vec 2 → ℝ,
        (∀ j : ℕ, IsWeakSolution (streamVel φ) (kfam β I.Λ t j) θ₀ (θ (kfam β I.Λ t j))) →
      ∀ j : ℕ, 1 ≤ j → mTheta0 β I.Λ R ≤ 2 * j + 1 →
        K * epsilon β I.Λ (2 * j) ^ ρ ≤ 2 →
      ∀ j' : ℕ, j ≤ j' → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => θ (kfam β I.Λ t j) s x - θ (kfam β I.Λ t j') s x)) ≤
          K * (epsilon β I.Λ (2 * j) ^ tailExp β + epsilon β I.Λ (2 * j) ^ delta β +
            epsilon β I.Λ (2 * j) ^ ρ) * Real.sqrt (l2NormSq θ₀) := by
  obtain ⟨Cs, Λa, hCs, hstep⟩ := step_sup β C₀
  obtain ⟨c₁, Λw, hc₁, hW⟩ := window_with β C₀
  obtain ⟨ρ, Cf, Λf, hρ, hFF⟩ := Contracts.flipFlop_contract β C₀
  refine ⟨max (max Λa Λw) (max Λf ((2 : ℝ) ^ (1 / (β - gamma β)))), ρ, hρ, ?_⟩
  intro I hz hx hh hΛ Φ hΦ φ htend
  have hβ1 := I.one_lt_beta
  have hβ2 := I.beta_lt
  have hΛ7 := I.two_pow_seven_le
  have hΛa : Λa ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hΛ
  have hΛw : Λw ≤ (I.Λ : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hΛ
  have hΛf : Λf ≤ (I.Λ : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛs : (2 : ℝ) ^ (1 / (β - gamma β)) ≤ (I.Λ : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  obtain ⟨Ct, Bφ, hCt, hBφ, htail, hφm, hφp, hφd, hbm, hbp, hdiv, hbb⟩ := limit_package hΦ htend
  have hε : ∀ n, 0 < epsilon β I.Λ n := fun n => Infra.Cutoff.epsilon_pos hβ1 hβ2 hΛ7
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ1 hβ2
  have ha : 0 < tailExp β := tailExp_pos hβ1 hβ2
  set Kt := 2 * Ct * (1 + Infra.Ingredients.supergeoConstant β) ^ β with hKt
  have hA := Infra.Section5.RelativeError.supergeoConstant_nonneg' hβ1 hβ2
  have hKt0 : 0 ≤ Kt := by positivity
  set Sδ := 1 / (1 - (I.Λ : ℝ) ^ (-delta β)) with hSδ
  have hΛ1 : (1 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast hΛ7
    linarith
  have hSδ0 : 0 ≤ Sδ := by
    have h1 : (I.Λ : ℝ) ^ (-delta β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hΛ1 (by linarith)
    exact one_div_nonneg.2 (by linarith)
  set Cf' := max Cf 0 with hCf'
  have hCf'0 : 0 ≤ Cf' := le_max_right _ _
  refine ⟨2 * Kt + Cs * (1 + Sδ) + 4 * Cf', by positivity, ?_⟩
  intro t ht R hR θ₀ hθ₀ hper hmean han θ hθ j hj hm₀ hsmall j' hjj' s hs
  have hm2 : 2 ≤ mTheta0 β I.Λ R := (mTheta0_isLeast hβ1 hβ2 hΛ7 hR).1.1
  set N0 := Real.sqrt (l2NormSq θ₀) with hN0
  have hN00 : 0 ≤ N0 := Real.sqrt_nonneg _
  set E := epsilon β I.Λ (2 * j) with hE
  have hE0 : 0 < E := hε _
  -- the two chains
  have hκj := kfam_mem ht j (hε _).le
  have hκj' := kfam_mem ht j' (hε _).le
  have hκjp := kfam_mem_permissible ht j (hε _).le
  have hκjp' := kfam_mem_permissible ht j' (hε _).le
  obtain ⟨θ1, hch1⟩ := chain_exists hW hc₁ hz hx hh hΛw hΦ hκjp (by omega) hκj hR hm₀ hθ₀ hper
  obtain ⟨θ2, hch2⟩ := chain_exists hW hc₁ hz hx hh hΛw hΦ hκjp' (by omega) hκj' hR
    (by omega) hθ₀ hper
  -- continuity and `L²` membership of slices
  have hc1 : ∀ n, mTheta0 β I.Λ R - 1 ≤ n → n ≤ 2 * j + 1 → Continuous (θ1 n s) :=
    fun n h1 h2 => IsClassicalSol.continuous_slice (hch1 n h1 h2).2 hs.1
  have hc2 : ∀ n, mTheta0 β I.Λ R - 1 ≤ n → n ≤ 2 * j' + 1 → Continuous (θ2 n s) :=
    fun n h1 h2 => IsClassicalSol.continuous_slice (hch2 n h1 h2).2 hs.1
  have hm1 : ∀ n, mTheta0 β I.Λ R - 1 ≤ n → n ≤ 2 * j + 1 → MemL2On unitCube (θ1 n s) :=
    fun n h1 h2 => Infra.Section5.Integration.memL2On_unitCube_of_continuous (hc1 n h1 h2)
  have hm2' : ∀ n, mTheta0 β I.Λ R - 1 ≤ n → n ≤ 2 * j' + 1 → MemL2On unitCube (θ2 n s) :=
    fun n h1 h2 => Infra.Section5.Integration.memL2On_unitCube_of_continuous (hc2 n h1 h2)
  obtain ⟨Dθ, hDθ⟩ := hθ j
  obtain ⟨Dθ', hDθ'⟩ := hθ j'
  have hmθ : MemL2On unitCube (θ (kfam β I.Λ t j) s) := (hDθ.1 s hs).2
  have hmθ' : MemL2On unitCube (θ (kfam β I.Λ t j') s) := (hDθ'.1 s hs).2
  -- tails
  have hθ1M : IsClassicalSol (streamVel (Φ (2 * j + 1))) (kfam β I.Λ t j) (fun _ _ => 0) θ₀
      (θ1 (2 * j + 1)) := by
    have := (hch1 (2 * j + 1) (by omega) le_rfl).2
    rwa [kappaSeq_top] at this
  have hθ2M : IsClassicalSol (streamVel (Φ (2 * j' + 1))) (kfam β I.Λ t j') (fun _ _ => 0) θ₀
      (θ2 (2 * j' + 1)) := by
    have := (hch2 (2 * j' + 1) (by omega) le_rfl).2
    rwa [kappaSeq_top] at this
  have hP1 := tail_sup hCt hΦ htail hφm hφp hφd hbm hbp hdiv hbb (M := 2 * j + 1) (by omega)
    (permitted_bounds hβ1 hβ2 hΛ7 hΛs (by omega) hκj).1 hθ₀ hper ⟨Dθ, hDθ⟩ hθ1M s hs
  have hP5 := tail_sup hCt hΦ htail hφm hφp hφd hbm hbp hdiv hbb (M := 2 * j' + 1) (by omega)
    (permitted_bounds hβ1 hβ2 hΛ7 hΛs (by omega) hκj').1 hθ₀ hper ⟨Dθ', hDθ'⟩ hθ2M s hs
  -- one step of the step-down estimate
  have hP2 := hstep I hz hx hh hΛa Φ hΦ _ hκjp (2 * j + 1) (by omega) hκj R hR θ₀ hθ₀ hper hmean
    han (2 * j + 1) hm₀ le_rfl (θ1 (2 * j + 1)) (θ1 (2 * j + 1 - 1))
    (hch1 _ (by omega) le_rfl).2 (hch1 _ (by omega) (by omega)).2 s hs
  simp only [Nat.add_sub_cancel] at hP2
  -- the middle term
  have hFFj := hFF I hz hx hh hΛf t ht (2 * j + 1) (by omega) (2 * j) (by omega) (by omega)
  have hFFj' := hFF I hz hx hh hΛf t ht (2 * j' + 1) (by omega) (2 * j) (by omega) (by omega)
  have hpar1 : ((-1 : ℝ)) ^ (2 * j + 1 - 1 - 2 * j) = 1 := by
    have : 2 * j + 1 - 1 - 2 * j = 0 := by omega
    rw [this]; simp
  have hpar2 : ((-1 : ℝ)) ^ (2 * j' + 1 - 1 - 2 * j) = 1 := by
    have : 2 * j' + 1 - 1 - 2 * j = 2 * (j' - j) := by omega
    rw [this, pow_mul]; simp
  rw [hpar1, one_mul] at hFFj
  rw [hpar2, one_mul] at hFFj'
  have hDpos : 0 < Real.sqrt (9 / 80) * epsilon β I.Λ (2 * j) ^ (β + gamma β) := by
    have := hε (2 * j)
    positivity
  have hd : 2 * (Cf' * E ^ ρ) ≤ 1 := by
    have hρE : 0 ≤ E ^ ρ := Real.rpow_nonneg hE0.le _
    have : 4 * Cf' * E ^ ρ ≤ 2 := by
      have h1 : (2 * Kt + Cs * (1 + Sδ) + 4 * Cf') * E ^ ρ ≤ 2 := hsmall
      have h2 : 0 ≤ (2 * Kt + Cs * (1 + Sδ)) * E ^ ρ := by positivity
      linarith
    linarith
  have hFFj1 : |Real.log (I.kappaSeq (kfam β I.Λ t j) (2 * j + 1) (2 * j) /
      (Real.sqrt (9 / 80) * epsilon β I.Λ (2 * j) ^ (β + gamma β))) -
      Real.log (t * Real.sqrt (80 / 9))| ≤ Cf' * E ^ ρ :=
    hFFj.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hE0.le _))
  have hFFj2 : |Real.log (I.kappaSeq (kfam β I.Λ t j') (2 * j' + 1) (2 * j) /
      (Real.sqrt (9 / 80) * epsilon β I.Λ (2 * j) ^ (β + gamma β))) -
      Real.log (t * Real.sqrt (80 / 9))| ≤ Cf' * E ^ ρ :=
    hFFj'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hE0.le _))
  have hP3 := middle_bound (streamSeq_isAdmissible hΦ (2 * j))
    (hch1 (2 * j) (by omega) (by omega)).1 (hch2 (2 * j) (by omega) (by omega)).1 hDpos hFFj1
    hFFj2 hd hθ₀ hper (hch1 (2 * j) (by omega) (by omega)).2 (hch2 (2 * j) (by omega) (by omega)).2
    hs
  -- the telescoped steps of the longer chain
  have hP4 := chain_sup (f := θ2) (c := fun n => Cs * epsilon β I.Λ (n - 1) ^ delta β * N0)
    (ℓ := 2 * j) (t := s) (2 * j' + 1) (by omega)
    (fun n h1 h2 => hc2 n (by omega) h2)
    (fun n h1 h2 => hstep I hz hx hh hΛa Φ hΦ _ hκjp' (2 * j' + 1) (by omega) hκj' R hR θ₀ hθ₀
      hper hmean han n (by omega) h2 (θ2 n) (θ2 (n - 1)) (hch2 n (by omega) h2).2
      (hch2 (n - 1) (by omega) (by omega)).2 s hs)
  have hsum : ∑ n ∈ Finset.Ioc (2 * j) (2 * j' + 1), Cs * epsilon β I.Λ (n - 1) ^ delta β * N0 ≤
      Cs * N0 * (Sδ * E ^ delta β) := by
    have e : ∑ n ∈ Finset.Ioc (2 * j) (2 * j' + 1), Cs * epsilon β I.Λ (n - 1) ^ delta β * N0 =
        Cs * N0 * ∑ n ∈ Finset.Ioc (2 * j) (2 * j' + 1), epsilon β I.Λ (n - 1) ^ delta β := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    have := eps_sum_tail_le I hδ (2 * j) (2 * j' + 1)
    refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) (by positivity)
    rw [hSδ]; ring
  -- combine
  have hmM' : MemL2On unitCube (θ2 (2 * j' + 1) s) := hm2' _ (by omega) le_rfl
  have t1 := sqrt_l2_tri hmθ (hm1 (2 * j + 1) (by omega) le_rfl) hmθ'
  have t2 := sqrt_l2_tri (hm1 (2 * j + 1) (by omega) le_rfl) (hm1 (2 * j) (by omega) (by omega))
    hmθ'
  have t3 := sqrt_l2_tri (hm1 (2 * j) (by omega) (by omega)) (hm2' (2 * j) (by omega) (by omega))
    hmθ'
  have t4 := sqrt_l2_tri (hm2' (2 * j) (by omega) (by omega)) hmM' hmθ'
  have c4 := sqrt_l2_comm (θ2 (2 * j) s) (θ2 (2 * j' + 1) s)
  have c5 := sqrt_l2_comm (θ (kfam β I.Λ t j') s) (θ2 (2 * j' + 1) s)
  have hanti : ∀ n, 2 * j ≤ n → epsilon β I.Λ n ≤ E := fun n hn =>
    Infra.Section5.RelativeError.epsilon_antitone hβ1 hβ2 hΛ7 hn
  have hx1 : epsilon β I.Λ (2 * j + 1) ^ tailExp β ≤ E ^ tailExp β :=
    Real.rpow_le_rpow (hε _).le (hanti _ (by omega)) ha.le
  have hx2 : epsilon β I.Λ (2 * j' + 1) ^ tailExp β ≤ E ^ tailExp β :=
    Real.rpow_le_rpow (hε _).le (hanti _ (by omega)) ha.le
  have hy0 : 0 ≤ E ^ delta β := Real.rpow_nonneg hE0.le _
  have hx0 : 0 ≤ E ^ tailExp β := Real.rpow_nonneg hE0.le _
  have hz0 : 0 ≤ E ^ ρ := Real.rpow_nonneg hE0.le _
  have b1 : Real.sqrt (l2NormSq (fun x => θ (kfam β I.Λ t j) s x - θ1 (2 * j + 1) s x)) ≤
      Kt * E ^ tailExp β * N0 :=
    hP1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx1 hKt0) hN00)
  have b5 : Real.sqrt (l2NormSq (fun x => θ2 (2 * j' + 1) s x - θ (kfam β I.Λ t j') s x)) ≤
      Kt * E ^ tailExp β * N0 := by
    rw [sqrt_l2_comm]
    exact hP5.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 hKt0) hN00)
  have b4 : Real.sqrt (l2NormSq (fun x => θ2 (2 * j) s x - θ2 (2 * j' + 1) s x)) ≤
      Cs * N0 * (Sδ * E ^ delta β) := by
    rw [sqrt_l2_comm]
    exact hP4.trans hsum
  have b2 : Real.sqrt (l2NormSq (fun x => θ1 (2 * j + 1) s x - θ1 (2 * j) s x)) ≤
      Cs * E ^ delta β * N0 := hP2
  have b3 : Real.sqrt (l2NormSq (fun x => θ1 (2 * j) s x - θ2 (2 * j) s x)) ≤
      4 * (Cf' * E ^ ρ) * N0 := hP3
  have hfin : 0 ≤ N0 * ((Cs * (1 + Sδ) + 4 * Cf') * E ^ tailExp β +
      (2 * Kt + 4 * Cf') * E ^ delta β + (2 * Kt + Cs * (1 + Sδ)) * E ^ ρ) := by
    positivity
  linarith [t1, t2, t3, t4, b1, b2, b3, b4, b5, hfin]

end AVenhance.Infra.FullTheorem
