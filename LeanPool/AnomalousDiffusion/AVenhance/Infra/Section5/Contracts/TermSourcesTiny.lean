/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyContract

/-! # `TinyHMinusSourceContract` producer (`e.monster.est.tiny`, `enhance.tex` 7848–7930)

`tinyHMinusSource_contract` produces `TinyHMinusSourceContract` at an abstract amplitude `B`,
conditionally on three contracts at the same amplitude: `SourceErrorDContract` (`d_m`),
`VIncrementContract` (the increments of the `T`-iterates, hence `e_{m-1}` and
`∇∇·e_{m-1}`) and `TinyMeanZeroContract` (mean of `tinyNondivergencePart`).

The proof follows the source: `hMinusOneNorm_tiny_le_of_components` splits `tiny` into the
divergence part (bounded by `‖d + e‖_{L²}`) and the nondivergence part (bounded in `L²` by
`sup|χTilde| · ‖∇∇·e‖_{L²}`); `e = -B ∇V` is expanded by the ordered Leibniz rule with the
    coefficient
jets of `B = K_m - κ_{m-1} + s_{m-1}`; the factor `x^{δ N*}` of the last increment beats every
negative power of `ε_{m-1}` (`sc_delta_Nstar_budget`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section4

/-- `a_m² ε_m⁴ = ε_m^{2β}`, hence `a_m² ε_m⁴/κ_m ≤ K κ_{m-1}` gives `ε_m^{2β} ≤ K κ_{m-1} κ_m`. -/
theorem sc_K2_rpow {β : ℝ} (I : Ingredients β) (m : ℕ) {κm κp K : ℝ} (hκm : 0 < κm)
    (h : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κm ≤ K * κp) :
    epsilon β I.Λ m ^ (2 * β) ≤ K * κp * κm := by
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have h1 : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 = epsilon β I.Λ m ^ (2 * β) := by
    unfold a
    rw [sc_rpow_sq hε, ← Real.rpow_natCast (epsilon β I.Λ m) 4, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  rw [h1, div_le_iff₀ hκm] at h
  linarith

/-- **`TinyHMinusSourceContract` producer** (`e.monster.est.tiny`), at abstract amplitude `B`. -/
theorem tinyHMinusSource_contract (β C₀ Cd Cs : ℝ) (hCd : 0 ≤ Cd) (hCs : 0 ≤ Cs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B → ∀ Rθ : ℝ, epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ Rθ →
        SourceErrorDContract I hΦ m (I.kappaSeq κ M m) T Cd B →
        VIncrementContract I m (I.kappaSeq κ M (m - 1)) T Cs Rθ B →
        TinyMeanZeroContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T →
        TinyHMinusSourceContract I hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) T C B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro I
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨CB, hCB0, C₁₁, hCB⟩ := sc_coeff_profile β C₀
  have hK0 : 0 ≤ K := by linarith
  have hbud := sc_delta_Nstar_budget hb.1 hb.2
  have hδ1 := Infra.Ingredients.delta_le_one_sixteenth hb.1 hb.2
  have hδ0 := Infra.Ingredients.delta_pos hb.1 hb.2
  have hγ0 := Infra.Ingredients.gamma_pos hb.1 hb.2
  have hγ1 := sc_gamma_le_one hb.1 hb.2
  have hq1 := Infra.Ingredients.one_lt_q hb.1 hb.2
  set Cs' : ℝ := max 1 Cs with hCs'
  set F : ℝ := (((2 * Nstar β + 2).factorial : ℕ) : ℝ) with hF
  set Y : ℝ := 2 ^ 22 * Cs' ^ 2 * F * (Cs ^ 3) ^ ((Nstar β : ℝ) / 2) with hY
  set Cc : ℝ := 16 + 2 * ((2 * Real.pi)⁻¹) ^ 2 * (5184 * K ^ 2 * 14336) with hCc
  set CZ : ℝ := Y * 2 ^ β * K * Real.sqrt K with hCZ
  have hY0 : 0 ≤ Y := by positivity
  have hCZ0 : 0 ≤ CZ := by positivity
  refine ⟨2 * Cd + Real.sqrt (7 * Cc) * CB * CZ, by positivity, max C₁₁ 128, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT
    B hB Rθ hRθ hDc hVc hmean
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, hκpK, hK2, -, hK4, -⟩ := hK I hz hx hh κ hκp M hM hperm m hm2 hmM
  have hκp0 : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hΛ' : C₁₁ ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hΛ
  set κm := I.kappaSeq κ M m with hκm_def
  set κp := I.kappaSeq κ M (m - 1) with hκp_def
  set x := epsilon β I.Λ (m - 1) with hxdef
  set εm := epsilon β I.Λ m with hεm_def
  have hx0 : 0 < x := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hx1 : x ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hεm0 : 0 < εm := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hN1 := sc_one_le_Nstar I.one_lt_beta I.beta_lt
  -- the radius `r`
  set r : ℝ := 2 * ((2 ^ 10 / x) / x ^ (2 * delta β)) with hr
  have hr1 : 1 ≤ r := by
    have hxd : x ^ (2 * delta β) ≤ 1 := Real.rpow_le_one hx0.le hx1 (by positivity)
    have hxd0 : 0 < x ^ (2 * delta β) := Real.rpow_pos_of_pos hx0 _
    have h1 : 1 ≤ (2 ^ 10 / x) / x ^ (2 * delta β) := by
      rw [le_div_iff₀ hxd0, one_mul, le_div_iff₀ hx0]
      nlinarith
    rw [hr]
    linarith
  -- coefficient jets
  have hjets : ∀ (t : ℝ) (y : Vec 2) (p : List (Fin 2)) (j k : Fin 2),
      |iterateMatrixWord (scCoeff I hΦ m κm κp t) p y j k| ≤
        (κp * CB) * (p.length.factorial : ℝ) * r ^ p.length :=
    fun t y p j k => hCB I hz hx hh hΛ' Φ hΦ κ hκp M hM hperm m hm2 hmM t y p j k
  have hbcoef : ∀ (t : ℝ) (y : Vec 2) (j k : Fin 2), |scCoeff I hΦ m κm κp t y j k| ≤ κp * CB := by
    intro t y j k
    have h := hjets t y [] j k
    simpa [iterateMatrixWord, iterateSpatialWord] using h
  have hD0 : 0 ≤ κp * CB := mul_nonneg hκp0.le hCB0
  have hbd : 0 ≤ Cd * x ^ (2 * delta β) * Real.sqrt κm * B := by positivity
  have hmain := sc_tiny_time_bound I hΦ hm2 hκm hθprev hT hmean hbd hDc
    (b := κp * CB) (cχ := K) (D := κp * CB) (r := r)
    (fun t _ y j k => hbcoef t y j k)
    (fun t _ k y j => sc_chiTilde_le I hΦ (by omega) hK0 hκm hK4 k t y j)
    hD0 hr1 (fun t _ y p _ j k => hjets t y p j k)
  unfold TinyHMinusSourceContract
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the energy bound from `VIncrementContract`
  set A : ℝ := (Cs ^ 3 * x ^ (2 * delta β)) ^ ((Nstar β : ℝ) / 2) with hA
  have hA0 : 0 ≤ A :=
    Real.rpow_nonneg (mul_nonneg (pow_nonneg hCs 3) (Real.rpow_nonneg hx0.le _)) _
  set L' : ℝ := Cs' * x ^ (-(1 + gamma β / 2)) with hL'
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  set G : ℝ := B * A * F * L' ^ 2 with hG
  have hG0 : 0 ≤ G := by positivity
  have hQw : ∀ w ∈ scWords2, Real.sqrt κp * Real.sqrt
      (spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w)) ≤ G :=
    fun w hw => sc_Q_le I m T hCs hB hRθ hVc hw
  set c : ℝ := 16 * (κp * CB) ^ 2 + 2 * ((2 * Real.pi)⁻¹) ^ 2 *
    (5184 * K ^ 2 * (14336 * (κp * CB) ^ 2 * r ^ 4)) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hsum := sc_sqrt_sum_le hκp0 hG0 hc0
    (Q := fun w => spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w))
    (fun w => sc_spaceTimeGradNormSq_nonneg _) hQw
  have hcle : c ≤ Cc * ((κp * CB) ^ 2 * r ^ 4) := sc_c_le hr1
  -- the scale arithmetic
  have hchain := sc_Z_chain (x := x) (δ := delta β) (γ := gamma β) (Cs := Cs) (Cs' := Cs')
    (F := F) (N := (Nstar β : ℝ)) hx0 hCs
  have hpow : x ^ q β ≤ 2 * εm := by
    have := LeftToShow.epsilon_pred_pow_q_div_two_le hb.1 hb.2 I.two_pow_seven_le hm2
    linarith
  have hε2 : εm ^ (2 * β) ≤ K * κp * κm := sc_K2_rpow I m hκm hK2
  have hE : delta β + q β * β ≤ delta β * (Nstar β : ℝ) - 4 - 4 * delta β - gamma β := by
    linarith
  have hZ := sc_Z_core hx0 hx1 hεm0 hκm hκp0 hK1 hκpK (by linarith [hb.1]) hpow hε2 hE hY0
  have hfin := sc_final_chain (x := x) (sk := Real.sqrt κm) (S :=
    ∑ w ∈ scWords2, spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w))
    (E := x ^ (delta β * (Nstar β : ℝ) - 4 - 4 * delta β - gamma β)) hκp0 hCB0 hB hG0
    (by positivity) hcle hsum hG hchain hZ
  have hxd : x ^ (2 * delta β) ≤ x ^ delta β :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hsq0 := Real.sqrt_nonneg κm
  have hdd : Cd * x ^ (2 * delta β) * Real.sqrt κm * B ≤ Cd * x ^ delta β * Real.sqrt κm * B := by
    gcongr
  calc 2 * (Cd * x ^ (2 * delta β) * Real.sqrt κm * B) + Real.sqrt (c *
        ∑ w ∈ scWords2, spaceTimeGradNormSq (scWordGrad (iterateIncrement T (Nstar β)) w))
      ≤ 2 * (Cd * x ^ delta β * Real.sqrt κm * B) +
        Real.sqrt (7 * Cc) * CB * B * (CZ * x ^ delta β * Real.sqrt κm) :=
        add_le_add (by linarith) hfin
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
