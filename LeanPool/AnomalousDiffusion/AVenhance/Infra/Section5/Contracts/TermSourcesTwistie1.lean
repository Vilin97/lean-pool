/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Scale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyCoeff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # `Twistie1HMinusSourceContract` producer (`e.monster.est.5`, `enhance.tex` 7371–7460)

`twistie1HMinusSource_contract` produces `Twistie1HMinusSourceContract` at an abstract amplitude `B`
conditionally on the contracts `TPositiveJetsContract` (slice jets of `T`), `TGradientContract`,
`FirstOrderGradJetContract`, `SecondOrderGradJetContract` (space-time `L²` of `∇ ∂^w T`,
`|w| ≤ 2`, at the same amplitude `B`) and `Twistie1MeanZeroContract` (total mean zero).

The proof follows the source: the ergodic lemma with the choice `e.fg.choice.1` gives, for each
`(k, j)`, a main term `ε_m ‖f‖_{L²} ‖g‖_{L²}` and an exponentially small term
(`centered_frozen_hMinusOneNorm_le_of_fastPeriodicProduct_flow`); the main term is
`ε_m · ε_m^{1-γ} · ‖∇ ∇·((K_m + s_{m-1}) ∇T)‖_{L²}` with
`‖∇ ∇·((K_m + s_{m-1}) ∇T)‖ ≲ √κ_{m-1} ε_{m-1}^{-(2+γ)} B`, and the scale exponent is `8δ ≥ δ`
(`se_main_scale`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
  AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

private theorem twistie1HMinusSource_contract_S1 :
  ∀ (β A : ℝ), (0 : ℝ) ≤ A →
  let A' : ℝ := max A (2048 : ℝ);
  ∀ (I : Ingredients β) (κ : ℝ) (M m : ℕ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (B : ℝ), (0 : ℝ) ≤ B →
  let κp : ℝ := I.kappaSeq κ M (m - (1 : ℕ));
  TGradientContract β κp T A B → FirstOrderGradJetContract I m κp T A B →
    SecondOrderGradJetContract I m κp T A B →
  let x : ℝ := epsilon β I.Λ (m - (1 : ℕ));
  (0 : ℝ) < x →
  let L : ℝ := A' / x ^ ((1 : ℝ) + gamma β / (2 : ℝ));
  A / x ^ ((1 : ℝ) + gamma β / (2 : ℝ)) ≤ L → ∀ w ∈ scWords2, √κp * √(spaceTimeGradNormSq
    (scWordGrad (T (Nstar β)) w)) ≤ A * B * L ^ w.length
    := by
  intro β A hA A' I κ M m T B hB κp hTg hF1 hF2 x hx0 L hAρL w hw
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  simp only [scWords2, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq (scWordGrad (T (Nstar β)) [])) ≤
        A * B := hTg
    simpa using h
  · have h : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
        (scWordGrad (T (Nstar β)) [0])) ≤ A * (A / x ^ (1 + gamma β / 2)) * B := hF1 0
    refine h.trans ?_
    simp only [List.length_cons, List.length_nil, zero_add, pow_one]
    calc A * (A / x ^ (1 + gamma β / 2)) * B = A * B * (A / x ^ (1 + gamma β / 2)) := by ring
      _ ≤ A * B * L := mul_le_mul_of_nonneg_left hAρL hAB
  · have h : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
        (scWordGrad (T (Nstar β)) [1])) ≤ A * (A / x ^ (1 + gamma β / 2)) * B := hF1 1
    refine h.trans ?_
    simp only [List.length_cons, List.length_nil, zero_add, pow_one]
    calc A * (A / x ^ (1 + gamma β / 2)) * B = A * B * (A / x ^ (1 + gamma β / 2)) := by ring
      _ ≤ A * B * L := mul_le_mul_of_nonneg_left hAρL hAB
  all_goals
    have h2 : ∀ i j : Fin 2, Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
        (scWordGrad (T (Nstar β)) [i, j])) ≤ A * B * L ^ 2 := by
      intro i j
      have h : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
          (scWordGrad (T (Nstar β)) [i, j])) ≤ A * (A / x ^ (1 + gamma β / 2)) ^ 2 * B :=
        hF2 i j
      refine h.trans ?_
      calc A * (A / x ^ (1 + gamma β / 2)) ^ 2 * B = A * B * (A / x ^ (1 + gamma β / 2)) ^ 2 := by
            ring
        _ ≤ A * B * L ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAρL 2) hAB
    exact h2 _ _

private theorem twistie1HMinusSource_contract_conclusion2 :
  ∀ (β C₀ A : ℝ), (0 : ℝ) ≤ A → (1 : ℝ) < β → β < (4 / 3 : ℝ) → ∀ (K : ℝ), (1 : ℝ) ≤ K → ∀ (CB :
    ℝ), (0 : ℝ) ≤ CB → ∀ (C₁₁ : ℝ), (∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤
    C₀ → C₁₁ ≤ (↑I.Λ : ℝ) → ∀ (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (hΦ : IsStreamSeq I Φ), ∀ κ ∈
    permissibleSet β I.Λ, ∀ (M : ℕ), (1 : ℕ) ≤ M → κ ∈ permittedInterval β I.Λ M → ∀ (m : ℕ), (2
    : ℕ) ≤ m → m ≤ M → ∀ (t : ℝ) (x : Vec (2 : ℕ)) (p : List (Fin (2 : ℕ))) (j k : Fin (2 : ℕ)),
    |iterateMatrixWord (fun (y : Vec (2 : ℕ)) => I.Kmat (I.kappaSeq κ M m) m t - I.kappaSeq κ M
    (m - (1 : ℕ)) • (1 : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℝ) + I.sMat hΦ m (I.kappaSeq κ M m)
    t y) p x j k| ≤ I.kappaSeq κ M (m - (1 : ℕ)) * CB * (↑p.length.factorial : ℝ) * ((2 : ℝ) *
    ((2 : ℝ) ^ (10 : ℕ) / epsilon β I.Λ (m - (1 : ℕ)) / epsilon β I.Λ (m - (1 : ℕ)) ^ ((2 : ℝ) *
    delta β))) ^ p.length) → ∀ (Ck : ℝ), (0 : ℝ) < delta β → gamma β ≤ (1 : ℝ) → (2 : ℝ) * delta
    β ≤ q β - (1 : ℝ) - gamma β / (2 : ℝ) → (4 : ℝ) * delta β ≤ gamma β → (0 : ℝ) ≤ Ck →
  let A' : ℝ := max A (2048 : ℝ);
  (2048 : ℝ) ≤ A' → A ≤ A' → (0 : ℝ) < A' →
  let seC : ℝ := seCE;
  seC = seCE → (0 : ℝ) ≤ seC → ∀ (M₁ : ℝ), (0 : ℝ) ≤ M₁ → (∀ (x Z : ℝ), (0 : ℝ) < x → (1 : ℝ) /
    ((2 : ℝ) ^ (15 : ℕ) * A' * K) / (4096 : ℝ) * x ^ (-((2 : ℝ) * delta β)) ≤ Z → Real.exp (-Z)
    * (x ^ ((3 : ℝ) + (3 : ℝ) * gamma β / (2 : ℝ) + q β * β))⁻¹ ≤ M₁ * x ^ delta β) →
  let Cmain : ℝ := K ^ ((2 : ℝ) - gamma β) * (√Ck * √K * (2 : ℝ) ^ ((β + gamma β) / (2 : ℝ)));
  let CA : ℝ := (4 : ℝ) * seC * K * √(100352 : ℝ) * (CB + (1 : ℝ)) * A * A' ^ (2 : ℕ) * Cmain;
  let CBt : ℝ := seC * (2048 : ℝ) * (40 : ℝ) * K * (CB + (1 : ℝ)) * A * A' ^ (3 : ℕ) * K * M₁ *
    ((2 : ℝ) ^ β * K);
  ∀ (I : Ingredients β), I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → ∀ (Φ : ℕ → ℝ → Vec (2 : ℕ) →
    ℝ) (hΦ : IsStreamSeq I Φ), ∀ κ ∈ permissibleSet β I.Λ, ∀ (M : ℕ), (1 : ℕ) ≤ M → κ ∈
    permittedInterval β I.Λ M → ∀ (θ₀ : Vec (2 : ℕ) → ℝ), ∀ m ≤ M, ∀ (θprev : ℝ → Vec (2 : ℕ) →
    ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (B : ℝ), (0 : ℝ) ≤ B → TPositiveJetsContract I m T A B → (2
    : ℕ) ≤ m → C₁₁ ≤ (↑I.Λ : ℝ) →
  let κm : ℝ := I.kappaSeq κ M m;
  Twistie1MeanZeroContract I hΦ m κm T → (0 : ℝ) < κm →
  let κp : ℝ := I.kappaSeq κ M (m - (1 : ℕ));
  IsClassicalSol (streamVel (Φ (m - (1 : ℕ)))) κp (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ))
    θ₀ θprev → TGradientContract β κp T A B → FirstOrderGradJetContract I m κp T A B →
    SecondOrderGradJetContract I m κp T A B → κp ≤ K → (0 : ℝ) < κp → I.IsTIterates hΦ m κm κp
    θ₀ θprev T →
  let x : ℝ := epsilon β I.Λ (m - (1 : ℕ));
  let εm : ℝ := epsilon β I.Λ m;
  a β I.Λ m * εm ^ (2 : ℕ) / κm ≤ K * εm ^ (-gamma β) → εm ≤ K * x ^ q β → (0 : ℝ) < x → x ≤ (1
    : ℝ) → (0 : ℝ) < εm → εm ≤ (1 : ℝ) → x ^ ((2 : ℝ) * delta β) ≤ (1 / 8 : ℝ) →
    (↑(ergodicFrequency β I.Λ m) : ℝ) = εm⁻¹ → (1 : ℝ) / ((2 : ℝ) ^ (15 : ℕ) * A' * K) * x ^
    (-(q β - (1 : ℝ) - gamma β / (2 : ℝ))) ≤ ((16 : ℝ) * (A' / x ^ ((1 : ℝ) + gamma β / (2 :
    ℝ))))⁻¹ / (2 : ℝ) ^ (11 : ℕ) * εm⁻¹ → (2 : ℝ) ≤ ((16 : ℝ) * (A' / x ^ ((1 : ℝ) + gamma β /
    (2 : ℝ))))⁻¹ / (2 : ℝ) ^ (11 : ℕ) * (↑(ergodicFrequency β I.Λ m) : ℝ) → κp ≤ Ck * x ^ (β +
    gamma β) → εm ^ (β + gamma β) ≤ K * κm → εm ^ ((2 : ℝ) * β) ≤ K * κp * κm →
    Twistie1HMinusSourceContract I hΦ m κm T ((72 : ℝ) * √(2 : ℝ) * (CA + CBt)) B
    := by
  intro β C₀ A hA hβ1 hβ2 K hK1 CB hCB0 C₁₁ hCB Ck hδ hγ1 hδp h4δ hCk0 A' hA'1 hAA' hA'0 seC hseC
      hseC0 M₁ hM₁0 hM₁ Cmain CA CBt I hz hx hh Φ hΦ κ hκp M hM hperm θ₀ m hmM θprev T B hB hTj
      hm2 hΛC₁₁ κm hmean hκm κp hθprev hTg hF1 hF2 hκpK hκp0 hT x εm hK4 hK5 hx0 hx1 hεm0 hεm1
      hxsmall hN hrN hr2 hκpA hκmL hK2'
  have hlow : x ^ q β ≤ 2 * εm := by
    have := LeftToShow.epsilon_pred_pow_q_div_two_le hβ1 hβ2 I.two_pow_seven_le hm2
    linarith
  have hqβ := se_kappa_lower (x := x) (εm := εm) (κm := κm) (κp := κp) (K := K) (q := q β)
    (β := β) hx0 hεm0 hκm hK1 (by linarith) hlow hκpK hK2'
  -- the common rate `L`
  set L : ℝ := A' / x ^ (1 + gamma β / 2) with hLdef
  have hxg : 0 < x ^ (1 + gamma β / 2) := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 < L := by positivity
  obtain ⟨hL1', hL2'⟩ := se_rate_le (γ := gamma β) (δ := delta β) (A' := A' / 2) hx0 hx1
    (by norm_num; linarith) (by linarith) hδ.le
  have hhalf : A' / 2 / x ^ (1 + gamma β / 2) = L / 2 := by rw [hLdef]; ring
  have hL1 : 2 ^ 10 / x ≤ L := by rw [hhalf] at hL1'; linarith
  have hL2 : 2 * ((2 ^ 10 / x) / x ^ (2 * delta β)) ≤ L := by rw [hhalf] at hL2'; linarith
  have hAρL : A / x ^ (1 + gamma β / 2) ≤ L :=
    div_le_div_of_nonneg_right hAA' hxg.le
  -- the structure of `T`
  have hTc := tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hTs : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ContDiff ℝ ∞ (T (Nstar β) t) := fun t ht =>
    tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.1.le
  have hTper : ∀ t ∈ Set.Ioo (0 : ℝ) 1, IsZ2Periodic (T (Nstar β) t) := fun t ht =>
    tIterate_periodic I hΦ hT hθprev le_rfl ht.1.le
  have hBb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j w y,
      |amnrSpaceWord w (fun z => (I.Kmat κm m t + I.sMat hΦ m κm t z) i j) y| ≤
        (κp * (CB + 1)) * w.length.factorial * L ^ w.length := by
    intro t _ i j w y
    exact se_B_jets I hΦ m κm κp t (CB := CB) (r := 2 * ((2 ^ 10 / x) / x ^ (2 * delta β))) (L := L)
      hκp0.le hCB0 (by positivity) hL2
      (fun y p j k => hCB I hz hx hh hΛC₁₁ Φ hΦ κ hκp M hM hperm m hm2 hmM t y p j k) i j w y
  have hTj' : RelativeError.PositiveTemperatureJets A (x ^ (1 + gamma β / 2)) B (T (Nstar β)) := hTj
  have hTb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w : List (Fin 2), 0 < w.length →
      eLpNorm (amnrSpaceWord w (T (Nstar β) t)) 2 (volume.restrict (Infra.Torus.unitCell 2)) ≤
        ENNReal.ofReal ((A * B) * w.length.factorial * L ^ w.length) := by
    intro t ht
    refine se_hTb_of_l2 (hTs t ht) ?_ (by positivity) hL0.le
    intro n i hn
    refine (hTj' n i hn t (Set.Ioo_subset_Icc_self ht)).trans ?_
    have hn0 : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
    have : A * B * (n.factorial : ℝ) * (A / x ^ (1 + gamma β / 2)) ^ n ≤
        A * B * (n.factorial : ℝ) * L ^ n := by
      apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAρL n)
      positivity
    exact this
  have htime := se_time_bound I hΦ hm2 hκm (T (Nstar β)) hTc hTs hTper hmean hxsmall
    (D := κp * (CB + 1)) (M := A * B) (L := L) (by positivity) (by positivity) hL1 hBb hTb hr2
  -- the word energies of `T`
  have hS : ∀ w ∈ scWords2, Real.sqrt κp *
      Real.sqrt (spaceTimeGradNormSq (scWordGrad (T (Nstar β)) w)) ≤ A * B * L ^ w.length := by
    exact @twistie1HMinusSource_contract_S1 β A hA I κ M m T B hB hTg hF1 hF2 hx0 hAρL
  have hU := se_U_le (κp := κp) (L := L) (A := A) (Bm := B) (CB1 := CB + 1) hκp0
    (by linarith) (mul_nonneg hA hB) (fun w => spaceTimeGradNormSq (scWordGrad (T (Nstar β)) w))
    (fun w _ => sc_spaceTimeGradNormSq_nonneg _) hS
  have hL2eq : L ^ 2 = A' ^ 2 * x ^ (-(2 + gamma β)) := se_L_sq hx0
  rw [hL2eq] at hU
  -- the exponentially small term
  have hxpow : x ^ (-(q β - 1 - gamma β / 2)) ≥ x ^ (-(2 * delta β)) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have hZ : (1 / (2 ^ 15 * A' * K) / 4096) * x ^ (-(2 * delta β)) ≤
      (16 * L)⁻¹ / 2 ^ 11 * (ergodicFrequency β I.Λ m : ℝ) / 4096 := by
    rw [hN]
    have h1 : (1 / (2 ^ 15 * A' * K)) * x ^ (-(2 * delta β)) ≤
        (1 / (2 ^ 15 * A' * K)) * x ^ (-(q β - 1 - gamma β / 2)) :=
      mul_le_mul_of_nonneg_left hxpow (by positivity)
    have h2 := h1.trans hrN
    calc (1 / (2 ^ 15 * A' * K) / 4096) * x ^ (-(2 * delta β))
        = ((1 / (2 ^ 15 * A' * K)) * x ^ (-(2 * delta β))) / 4096 := by ring
      _ ≤ ((16 * L)⁻¹ / 2 ^ 11 * εm⁻¹) / 4096 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact h2
  have hdec : Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096) *
      (x ^ (3 + 3 * gamma β / 2 + q β * β))⁻¹ ≤ M₁ * x ^ delta β := by
    have h := hM₁ x _ hx0 hZ
    have e : -((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096 =
        -((16 * L)⁻¹ / 2 ^ 11 * (ergodicFrequency β I.Λ m : ℝ) / 4096) := by ring
    rw [e]
    exact h
  have hEv0 := (Real.exp_pos (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096)).le
  have hdiv : seCE / (ergodicFrequency β I.Λ m : ℝ) = seCE * εm := by
    rw [hN, div_inv_eq_mul]
  have hu0 : 0 ≤ AVenhance.a β I.Λ m * εm ^ 2 / κm := by
    have : 0 ≤ AVenhance.a β I.Λ m := (Real.rpow_pos_of_pos hεm0 _).le
    positivity
  have hAterm := se_partA (x := x) (εm := εm) (κm := κm) (κp := κp) (K := K) (Ca := Ck)
    (A' := A') (CB1 := CB + 1) (Aj := A) (Bm := B) (CE := seCE)
    (u := AVenhance.a β I.Λ m * εm ^ 2 / κm) (c7 := Real.sqrt 100352)
    (U := ∑ w ∈ scWords2, (14336 * (κp * (CB + 1)) ^ 2 * (L ^ (2 - w.length)) ^ 2) *
      spaceTimeGradNormSq (scWordGrad (T (Nstar β)) w))
    (β := β) (γ := gamma β) (q := q β) (δ := delta β) hx0 hx1 hεm0 hκm hK1 hCk0 (by linarith)
    (by linarith) hlow hK5 hκpA hκmL (se_exponent_ge hβ1 hβ2) (by linarith) hA hB hseC0
    (Real.sqrt_nonneg _) hK4 hU
  have hBterm := se_partB (x := x) (εm := εm) (κm := κm) (κp := κp) (K := K) (A' := A')
    (CB1 := CB + 1) (Aj := A) (Bm := B) (CE := seCE) (u := AVenhance.a β I.Λ m * εm ^ 2 / κm)
    (M₁ := M₁) (c8 := 2 ^ β * K)
    (Ev := Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))
    (β := β) (γ := gamma β) (q := q β) (δ := delta β) hx0 hεm0 hεm1 hK1 hγ1 hκpK
    (by linarith) hA hB hseC0 hA'0.le hu0 hK4 hM₁0 hEv0 hdec hqβ
  unfold Twistie1HMinusSourceContract
  refine htime.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hdiv]
  calc 72 * Real.sqrt 2 * ((seCE * εm * 4 * (εm * (AVenhance.a β I.Λ m * εm ^ 2 / κm))) *
        Real.sqrt (∑ w ∈ scWords2, (14336 * (κp * (CB + 1)) ^ 2 * (L ^ (2 - w.length)) ^ 2) *
          spaceTimeGradNormSq (scWordGrad (T (Nstar β)) w)) +
        seC * (2048 * 40 * (κp * (CB + 1)) * (A * B) * L ^ 3) *
          (εm * (AVenhance.a β I.Λ m * εm ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096))
      = 72 * Real.sqrt 2 * ((4 * seCE * εm * (εm * (AVenhance.a β I.Λ m * εm ^ 2 / κm)) *
        Real.sqrt (∑ w ∈ scWords2, (14336 * (κp * (CB + 1)) ^ 2 * (L ^ (2 - w.length)) ^ 2) *
          spaceTimeGradNormSq (scWordGrad (T (Nstar β)) w))) +
        seCE * (2048 * 40 * (κp * (CB + 1)) * (A * B) * (A' / x ^ (1 + gamma β / 2)) ^ 3) *
          (εm * (AVenhance.a β I.Λ m * εm ^ 2 / κm)) *
          Real.exp (-((16 * L)⁻¹ / 2 ^ 11) * (ergodicFrequency β I.Λ m : ℝ) / 4096)) := by
        simp only [hseC]; ring
    _ ≤ 72 * Real.sqrt 2 * ((CA * x ^ delta β * Real.sqrt κm * B) +
          (CBt * x ^ delta β * Real.sqrt κm * B)) := by
        gcongr
    _ = _ := by ring

/-- **`Twistie1HMinusSourceContract` producer** (`e.monster.est.5`), at abstract amplitude `B`. -/
theorem twistie1HMinusSource_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁ (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
      ∀ B : ℝ, 0 ≤ B →
        TPositiveJetsContract I m T A B →
        TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
        FirstOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B →
        SecondOrderGradJetContract I m (I.kappaSeq κ M (m - 1)) T A B →
        Twistie1MeanZeroContract I hΦ m (I.kappaSeq κ M m) T →
        Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro I
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb
  obtain ⟨hβ1, hβ2⟩ := hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨CB, hCB0, C₁₁, hCB⟩ := sc_coeff_profile β C₀
  obtain ⟨c, Ck, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  have hK0 : 0 < K := by linarith
  have hδ := Infra.Ingredients.delta_pos hβ1 hβ2
  have hγ0 := Infra.Ingredients.gamma_pos hβ1 hβ2
  have hγ1 := sc_gamma_le_one hβ1 hβ2
  have hq1 := Infra.Ingredients.one_lt_q hβ1 hβ2
  have hp0 : 0 < q β - 1 - gamma β / 2 := Infra.Numeric.kill_half_gamma hβ1 hβ2
  have hδp := RelativeError.corrector_second_term_exponent hβ1 hβ2
  have h4δ := Infra.Ingredients.four_delta_le_gamma hβ1 hβ2
  have hCk0 : 0 ≤ Ck := (hc.trans hcC).le
  set A' : ℝ := max A 2048 with hA'
  have hA'1 : 2048 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  have hA'0 : 0 < A' := by linarith
  set seC : ℝ := seCE with hseC
  have hseC0 : 0 ≤ seC := seCE_nonneg
  -- the exponential-decay constant
  obtain ⟨M₁, hM₁0, hM₁⟩ := sb_exp_decay_le (q := 3 + 3 * gamma β / 2 + q β * β) (δ := delta β)
    (c := (1 / (2 ^ 15 * A' * K)) / 4096) (by have := hq1; nlinarith) hδ (by positivity)
  set Cmain : ℝ := K ^ (2 - gamma β) * (Real.sqrt Ck * Real.sqrt K * 2 ^ ((β + gamma β) / 2))
    with hCmain
  set CA : ℝ := 4 * seC * K * Real.sqrt 100352 * (CB + 1) * A * A' ^ 2 * Cmain with hCA
  set CBt : ℝ := seC * 2048 * 40 * K * (CB + 1) * A * A' ^ 3 * K * M₁ * (2 ^ β * K) with hCBt
  have hCmain0 : 0 ≤ Cmain := by rw [hCmain]; positivity
  have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
  have hCBt0 : 0 ≤ CBt := by rw [hCBt]; positivity
  refine ⟨72 * Real.sqrt 2 * (CA + CBt), by positivity,
    max C₁₁ (max (8 ^ (1 / (2 * delta β))) ((2 ^ 16 * A' * K) ^ (1 / (q β - 1 - gamma β / 2)))),
    ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκp M hM hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT
    B hB hTj hTg hF1 hF2 hmean
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, hκpK, hK2, -, hK4, hK5⟩ := hK I hz hx hh κ hκp M hM hperm m hm2 hmM
  have hκp0 : 0 < I.kappaSeq κ M (m - 1) := hκm.trans_le hmono
  have hΛC₁₁ : C₁₁ ≤ (I.Λ : ℝ) := le_trans (le_max_left _ _) hΛ
  have hΛ8 : (8 : ℝ) ^ (1 / (2 * delta β)) ≤ (I.Λ : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛ
  have hΛsep : (2 ^ 16 * A' * K) ^ (1 / (q β - 1 - gamma β / 2)) ≤ (I.Λ : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛ
  have hΛpos : (0 : ℝ) < I.Λ := by
    have : (128 : ℝ) ≤ I.Λ := by exact_mod_cast I.two_pow_seven_le
    linarith
  set κm := I.kappaSeq κ M m with hκm_def
  set κp := I.kappaSeq κ M (m - 1) with hκp_def
  set x := epsilon β I.Λ (m - 1) with hxdef
  set εm := epsilon β I.Λ m with hεm_def
  have hx0 : 0 < x := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hx1 : x ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hεm0 : 0 < εm := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hεm1 : εm ≤ 1 := Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  have hxΛ : x ≤ ((I.Λ : ℝ))⁻¹ :=
    LeftToShow.epsilon_le_inv_Lambda hβ1 hβ2 I.two_pow_seven_le (m := m - 1) (by omega)
  -- smallness and separation
  have hxsmall : x ^ (2 * delta β) ≤ 1 / 8 := by
    have h := se_rpow_neg_ge (x := x) (Λ := (I.Λ : ℝ)) (p := 2 * delta β) (c := 8) hx0 hxΛ hΛpos
      (by linarith) (by norm_num) hΛ8
    rw [Real.rpow_neg hx0.le] at h
    have hy : 0 < x ^ (2 * delta β) := Real.rpow_pos_of_pos hx0 _
    rw [le_inv_comm₀ (by norm_num) hy] at h
    simpa using h
  have hsepx : 2 ^ 16 * A' * K ≤ x ^ (-(q β - 1 - gamma β / 2)) :=
    se_rpow_neg_ge hx0 hxΛ hΛpos hp0 (by positivity) hΛsep
  have hN : (ergodicFrequency β I.Λ m : ℝ) = εm⁻¹ := ergodicFrequency_cast β I.Λ m
  have hrN := se_radius_freq (x := x) (εm := εm) (K := K) (A' := A') (q := q β) (γ := gamma β)
    hx0 hεm0 hK1 (by linarith) hK5
  have hr2 : 2 ≤ (16 * (A' / x ^ (1 + gamma β / 2)))⁻¹ / 2 ^ 11 * (ergodicFrequency β I.Λ m : ℝ)
      := by
    rw [hN]
    refine le_trans ?_ hrN
    have h1 : (1 / (2 ^ 15 * A' * K)) * (2 ^ 16 * A' * K) = 2 := by field_simp
    calc (2 : ℝ) = (1 / (2 ^ 15 * A' * K)) * (2 ^ 16 * A' * K) := h1.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsepx (by positivity)
  -- diffusivity upper bound for `κ_{m-1}` and the lower bounds for `κ_m`
  have hA5 := hrec I hz hx hh κ (Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM, hperm⟩⟩) M hM hperm
  have hκpA : κp ≤ Ck * x ^ (β + gamma β) := by
    have h := (hA5.1 (m - 1) (by omega) (by omega)).2
    have e : AVenhance.a β I.Λ (m - 1) * x ^ (2 + gamma β) = x ^ (β + gamma β) := by
      unfold AVenhance.a; rw [← Real.rpow_add hx0]; congr 1; ring
    rw [e] at h
    exact h
  have heA : AVenhance.a β I.Λ m * εm ^ 2 = εm ^ β := by
    unfold AVenhance.a
    rw [← Real.rpow_two, ← Real.rpow_add hεm0]
    congr 1; ring
  have hκmL : εm ^ (β + gamma β) ≤ K * κm := by
    have h := hK4
    rw [heA, div_le_iff₀ hκm] at h
    have h2 : εm ^ (β + gamma β) = εm ^ β * εm ^ gamma β := Real.rpow_add hεm0 _ _
    have h3 : εm ^ (-gamma β) * εm ^ gamma β = 1 := by
      rw [← Real.rpow_add hεm0, neg_add_cancel, Real.rpow_zero]
    have hg0 : 0 ≤ εm ^ gamma β := Real.rpow_nonneg hεm0.le _
    calc εm ^ (β + gamma β) = εm ^ β * εm ^ gamma β := h2
      _ ≤ (K * εm ^ (-gamma β) * κm) * εm ^ gamma β := mul_le_mul_of_nonneg_right h hg0
      _ = K * κm * (εm ^ (-gamma β) * εm ^ gamma β) := by ring
      _ = K * κm := by rw [h3, mul_one]
  have hK2' : εm ^ (2 * β) ≤ K * κp * κm := by
    have hh : AVenhance.a β I.Λ m ^ 2 * εm ^ 4 = εm ^ (2 * β) := by
      unfold AVenhance.a
      rw [sc_rpow_sq hεm0, ← Real.rpow_natCast εm 4, ← Real.rpow_add hεm0]
      congr 1; push_cast; ring
    rw [hh, div_le_iff₀ hκm] at hK2
    linarith
  exact @twistie1HMinusSource_contract_conclusion2 β C₀ A hA hβ1 hβ2 K hK1 CB hCB0 C₁₁ hCB Ck hδ
      hγ1 hδp h4δ hCk0 hA'1 hAA' hA'0 hseC hseC0 M₁ hM₁0 hM₁ I hz hx hh Φ hΦ κ hκp M hM hperm θ₀ m
      hmM θprev T B hB hTj hm2 hΛC₁₁ hmean hκm hθprev hTg hF1 hF2 hκpK hκp0 hT hK4 hK5 hx0 hx1
      hεm0 hεm1 hxsmall hN hrN hr2 hκpA hκmL hK2'
end AVenhance.Infra.Section5.Contracts
end
