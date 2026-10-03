/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffSlice
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.Produced
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth

/-! # `Cutoff1SourceContract` producer (`e.monster.est.3`, `enhance.tex` 7329–7364)

Conditional on `TGradientContract β κ_{m-1} T A B` (same amplitude `B`): on the support of
`ξ'_{m,k}` the corrector is exponentially small (`sb_corrTime_nonneg_le_decay`), so that
`‖cutoff1‖_{L²} ≲ e^{-c ε_{m-1}^{-2δ}} a_m ε_m ‖∇T‖_{L²}`; the scale package turns this into
`C ε_{m-1}^δ √κ_m B`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- Abstract-real core: the sharp constant of the pointwise bound is `≲ x^δ √(κ_m κ_{m-1})`. -/
theorem sb_scalar_core {a εm E κm κp x K Cx M q δ : ℝ} (hK : 1 ≤ K) (hx : 0 < x)
    (hεm : 0 < εm) (hκm : 0 < κm)
    (h4 : a ^ 2 * εm ^ 4 / κm ≤ K * κp)
    (hq : x ^ q / 2 ≤ εm)
    (hE : E * (x ^ q)⁻¹ ≤ M * x ^ δ) (hE0 : 0 ≤ E) (hCx : 0 ≤ Cx) :
    Cx * (a * εm) * E ≤ Cx * (Real.sqrt K * Real.sqrt κm * Real.sqrt κp * (2 * (M * x ^ δ))) := by
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx _
  have h1 : (a * εm ^ 2) ^ 2 ≤ K * κm * κp := by
    have := (div_le_iff₀ hκm).1 h4
    nlinarith
  have h2 : a * εm ^ 2 ≤ Real.sqrt K * Real.sqrt κm * Real.sqrt κp := by
    rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le h1
  have h3 : (εm)⁻¹ ≤ 2 * (x ^ q)⁻¹ := by
    rw [inv_eq_one_div, div_le_iff₀ hεm]
    have : 1 ≤ 2 * (x ^ q)⁻¹ * εm := by
      have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * (x ^ q)⁻¹)
      calc (1 : ℝ) = 2 * (x ^ q)⁻¹ * (x ^ q / 2) := by field_simp
        _ ≤ _ := this
    linarith
  have h5 : a * εm = (a * εm ^ 2) * (εm)⁻¹ := by field_simp
  have hsq : 0 ≤ Real.sqrt K * Real.sqrt κm * Real.sqrt κp := by positivity
  calc Cx * (a * εm) * E = Cx * ((a * εm ^ 2) * (εm)⁻¹ * E) := by rw [← h5]; ring
    _ ≤ Cx * ((Real.sqrt K * Real.sqrt κm * Real.sqrt κp) * (2 * (x ^ q)⁻¹) * E) := by
        apply mul_le_mul_of_nonneg_left _ hCx
        apply mul_le_mul_of_nonneg_right _ hE0
        exact mul_le_mul h2 h3 (inv_nonneg.2 hεm.le) hsq
    _ = Cx * (Real.sqrt K * Real.sqrt κm * Real.sqrt κp * (2 * (E * (x ^ q)⁻¹))) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hCx
        apply mul_le_mul_of_nonneg_left _ hsq
        linarith

/-- **`Cutoff1SourceContract` producer** (`e.monster.est.3`), at abstract amplitude `B`, from the
`T`-gradient contract at the same amplitude. -/
theorem cutoff1Source_contract (β C₀ A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ C₁ : ℝ, OnA7Instances β C₀ C₁
      (fun I _Φ hΦ κ M _R _θ₀ m _θprev T =>
        ∀ B : ℝ, 0 ≤ B →
          TGradientContract β (I.kappaSeq κ M (m - 1)) T A B →
          Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C B) := by
  by_cases hb : 1 < β ∧ β < 4 / 3
  swap
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro I
    exact absurd ⟨I.one_lt_beta, I.beta_lt⟩ hb
  obtain ⟨K, hK1, hK⟩ := LeftToShow.left_to_show_scales β C₀
  have hδ := Infra.Ingredients.delta_pos hb.1 hb.2
  have hq1 := Infra.Ingredients.one_lt_q hb.1 hb.2
  have hKpos : 0 < K := by linarith
  obtain ⟨M, hM0, hMdec⟩ := sb_exp_decay_le (q := q β) (δ := delta β)
    (c := Real.pi ^ 2 / (3 * K)) (by linarith) hδ (by positivity)
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨64 * C₀' * Real.sqrt K * M * A, by positivity, 0, ?_⟩
  intro I hz hx hh _ Φ hΦ κ hκp M' hM' hperm R hR θ₀ _ _ _ _ m hm hmM θprev T hθprev hT
  obtain ⟨hm2, hκm⟩ := onA7_basic I hperm hR hm
  obtain ⟨-, hmono, -, h4, h5, -, -⟩ := hK I hz hx hh κ hκp M' hM' hperm m hm2 hmM
  intro B hB hTg
  have hκp' : 0 < I.kappaSeq κ M' (m - 1) := hκm.trans_le hmono
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hx0 : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have ha : 0 ≤ a β I.Λ m := (Real.rpow_pos_of_pos hε _).le
  -- regularity of the terminal iterate
  have hTj := Infra.Section4.tIterate_contDiffOn_nonneg I hΦ hT hθprev (i := Nstar β) le_rfl
  have hslice : ∀ t, 0 < t → ContDiff ℝ ∞ (T (Nstar β) t) := fun t ht =>
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  set κm := I.kappaSeq κ M' m with hκm_def
  set κp := I.kappaSeq κ M' (m - 1) with hκp_def
  set x := epsilon β I.Λ (m - 1) with hxdef
  set E : ℝ := Real.exp (-(4 * Real.pi ^ 2 * κm / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12)))
    with hEdef
  -- the constant of the pointwise bound
  set P : ℝ := 64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) * E with hPdef
  have hCxi : I.Cxi ≤ C₀' := hx.trans (le_max_left _ _)
  have hCxi0 : 0 ≤ I.Cxi := by linarith [I.one_le_Cxi]
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  -- decay of the exponential
  have hZ : Real.pi ^ 2 / (3 * K) * x ^ (-(2 * delta β)) ≤
      4 * Real.pi ^ 2 * κm / epsilon β I.Λ m ^ 2 * (tau β I.Λ m / 12) := by
    have hx2 : 0 < x ^ (2 * delta β) := Real.rpow_pos_of_pos hx0 _
    have h5' : 1 / (K * x ^ (2 * delta β)) ≤ κm * tau β I.Λ m / epsilon β I.Λ m ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := (div_le_iff₀ (mul_pos hκm hτ)).1 h5
      nlinarith
    rw [Real.rpow_neg hx0.le]
    calc Real.pi ^ 2 / (3 * K) * (x ^ (2 * delta β))⁻¹
        = Real.pi ^ 2 / 3 * (1 / (K * x ^ (2 * delta β))) := by field_simp
      _ ≤ Real.pi ^ 2 / 3 * (κm * tau β I.Λ m / epsilon β I.Λ m ^ 2) := by gcongr
      _ = _ := by field_simp; ring
  have hEdec := hMdec x _ hx0 hZ
  have hq2 := LeftToShow.epsilon_pred_pow_q_div_two_le hb.1 hb.2 I.two_pow_seven_le hm2
  have hcore := sb_scalar_core (a := a β I.Λ m) (εm := epsilon β I.Λ m) (E := E) (κm := κm)
    (κp := κp) (x := x) (K := K) (Cx := 64 * Real.pi * I.Cxi)
    (M := M) (q := q β) (δ := delta β) hK1 hx0 hε hκm h4 hq2 hEdec
    (Real.exp_pos _).le (by positivity)
  -- slicewise bound
  have hslab : ∀ t ∈ Set.Ioo (0 : ℝ) 1, l2NormSq (cutoff1 I hΦ m κm (T (Nstar β)) t) ≤
      P ^ 2 * gradNormSq (fun y => spaceGrad (T (Nstar β) t) y) := fun t ht =>
    sb_l2NormSq_cutoff1_le I hΦ hm2 hκm.le (hslice t ht.1)
  have hL2 := sb_l2_timeL2_le hTj hP0 hslab
  unfold Cutoff1SourceContract
  refine hL2.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hst0 : 0 ≤ Real.sqrt (spaceTimeGradNormSq (fun t y => spaceGrad (T (Nstar β) t) y)) :=
    Real.sqrt_nonneg _
  have hTg' : Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
      (fun t y => spaceGrad (T (Nstar β) t) y)) ≤ A * B := hTg
  have hPle : P ≤ 64 * Real.pi * C₀' * (Real.sqrt K * Real.sqrt κm * Real.sqrt κp *
      (2 * (M * x ^ delta β))) := by
    have h := hcore
    rw [hPdef]
    calc 64 * Real.pi * I.Cxi * (a β I.Λ m * epsilon β I.Λ m) * E
        = (64 * Real.pi * I.Cxi) * (a β I.Λ m * epsilon β I.Λ m) * E := by ring
      _ ≤ (64 * Real.pi * I.Cxi) * (Real.sqrt K * Real.sqrt κm * Real.sqrt κp *
          (2 * (M * x ^ delta β))) := h
      _ ≤ _ := by
          have : 0 ≤ Real.sqrt K * Real.sqrt κm * Real.sqrt κp * (2 * (M * x ^ delta β)) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right hCxi this, Real.pi_pos]
  have hsp : 0 < Real.sqrt κp := Real.sqrt_pos.2 hκp'
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * P * Real.sqrt (spaceTimeGradNormSq
        (fun t y => spaceGrad (T (Nstar β) t) y))
      ≤ (2 * Real.pi)⁻¹ * (64 * Real.pi * C₀' * (Real.sqrt K * Real.sqrt κm * Real.sqrt κp *
          (2 * (M * x ^ delta β)))) * Real.sqrt (spaceTimeGradNormSq
        (fun t y => spaceGrad (T (Nstar β) t) y)) := by gcongr
    _ = 64 * C₀' * Real.sqrt K * M * x ^ delta β * Real.sqrt κm *
          (Real.sqrt κp * Real.sqrt (spaceTimeGradNormSq
            (fun t y => spaceGrad (T (Nstar β) t) y))) := by
        field_simp
    _ ≤ 64 * C₀' * Real.sqrt K * M * x ^ delta β * Real.sqrt κm * (A * B) := by
        apply mul_le_mul_of_nonneg_left hTg'
        have : 0 ≤ x ^ delta β := Real.rpow_nonneg hx0.le _
        positivity
    _ = 64 * C₀' * Real.sqrt K * M * A * x ^ delta β * Real.sqrt κm * B := by ring

end AVenhance.Infra.Section5.Contracts
end
