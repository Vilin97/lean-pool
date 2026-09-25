/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailSelected

/-! # Bad Scale Prefactor Gap -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open Filter
open scoped Topology

/-!
# Prefactor absorption for stretched-exponential bad-scale tails

The selected bad-scale tail still has a deterministic prefactor-gap condition.
This file proves the real-variable fact behind its eventual discharge:
linear/exponential-in-`q` prefactors are absorbed by a geometric
stretched-exponential gap.
-/

noncomputable section

theorem tendsto_exp_neg_const_mul_pow
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (fun n : ℕ => Real.exp (-(c * ρ ^ n))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ρ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hρ
  have hmul : Tendsto (fun n : ℕ => c * ρ ^ n) atTop atTop :=
    hpow.const_mul_atTop hc
  have hneg : Tendsto (fun n : ℕ => -(c * ρ ^ n)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  exact Real.tendsto_exp_atBot.comp hneg

private theorem tendsto_linear_ratio :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcongr :
      (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) =
        fun n : ℕ => 1 + (1 : ℝ) / ((n : ℝ) + 1) := by
    funext n
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [hcongr]
  simpa using (tendsto_const_nhds.add hinv)

theorem summable_linear_pow_mul_exp_neg_const_mul_pow
    {M W c ρ : ℝ} (hM : 0 < M) (hW : 0 < W)
    (hc : 0 < c) (hρ : 1 < ρ) :
    Summable fun n : ℕ =>
      M * (((n : ℝ) + 1) * W ^ n) * Real.exp (-(c * ρ ^ n)) := by
  let f : ℕ → ℝ :=
    fun n => M * (((n : ℝ) + 1) * W ^ n) * Real.exp (-(c * ρ ^ n))
  have hf_pos : ∀ n : ℕ, 0 < f n := by
    intro n
    dsimp [f]
    positivity
  refine summable_of_ratio_test_tendsto_lt_one (f := f) (l := 0)
    (by norm_num) ?_ ?_
  · filter_upwards with n
    exact ne_of_gt (hf_pos n)
  · have hratio_eq :
        (fun n : ℕ => ‖f (n + 1)‖ / ‖f n‖) =ᶠ[atTop]
          fun n : ℕ =>
            (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              W * Real.exp (-(c * (ρ - 1) * ρ ^ n)) := by
      filter_upwards with n
      have hn_pos : 0 < (n : ℝ) + 1 := by positivity
      have hW_pow_pos : 0 < W ^ n := pow_pos hW n
      have hρ_pow_pos : 0 < ρ ^ n := pow_pos (lt_trans zero_lt_one hρ) n
      have hf_n_pos := hf_pos n
      have hf_succ_pos := hf_pos (n + 1)
      have hW_ne : W ≠ 0 := hW.ne'
      have hW_pow_ne : W ^ n ≠ 0 := ne_of_gt hW_pow_pos
      have hM_ne : M ≠ 0 := hM.ne'
      calc
        ‖f (n + 1)‖ / ‖f n‖
            = f (n + 1) / f n := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos hf_succ_pos, abs_of_pos hf_n_pos]
        _ = (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              W * Real.exp (-(c * (ρ - 1) * ρ ^ n)) := by
              dsimp [f]
              rw [pow_succ W n, pow_succ ρ n]
              field_simp [hn_pos.ne', hM_ne, hW_ne, hW_pow_ne, Real.exp_ne_zero]
              have hexp_eq :
                  Real.exp (-(c * ρ ^ n * ρ)) =
                    Real.exp (-(c * ρ ^ n)) *
                      Real.exp (-(c * (ρ - 1) * ρ ^ n)) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [hexp_eq]
              simp only [Nat.cast_add, Nat.cast_one]
              ring_nf
    refine Tendsto.congr' hratio_eq.symm ?_
    have hfrac := tendsto_linear_ratio
    have hexp :=
      tendsto_exp_neg_const_mul_pow
        (c := c * (ρ - 1)) (ρ := ρ)
        (mul_pos hc (sub_pos.mpr hρ)) hρ
    have hprod :
        Tendsto
          (fun n : ℕ =>
            (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              W * Real.exp (-(c * (ρ - 1) * ρ ^ n)))
          atTop (𝓝 (1 * W * 0)) :=
      (hfrac.mul tendsto_const_nhds).mul hexp
    simpa using hprod

theorem tendsto_linear_pow_mul_exp_neg_const_mul_pow
    {M W c ρ : ℝ} (hM : 0 ≤ M) (hW : 0 < W)
    (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (fun n : ℕ =>
      M * (((n : ℝ) + 1) * W ^ n) * Real.exp (-(c * ρ ^ n))) atTop (𝓝 0) := by
  by_cases hM_zero : M = 0
  · simp [hM_zero]
  · have hM_pos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM_zero)
    exact (summable_linear_pow_mul_exp_neg_const_mul_pow
      hM_pos hW hc hρ).tendsto_atTop_zero

/-- A linear/exponential prefactor is eventually bounded by the exponential of
a positive geometric gap. -/
theorem exists_forall_ge_linear_pow_le_exp_const_mul_pow
    {M W c ρ : ℝ} (hM : 0 ≤ M) (hW : 0 < W)
    (hc : 0 < c) (hρ : 1 < ρ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (c * ρ ^ q) := by
  have htend :=
    tendsto_linear_pow_mul_exp_neg_const_mul_pow
      (M := M) (W := W) (c := c) (ρ := ρ) hM hW hc hρ
  have hevent :
      ∀ᶠ q : ℕ in atTop,
        M * (((q : ℝ) + 1) * W ^ q) *
            Real.exp (-(c * ρ ^ q)) ≤ 1 :=
    htend.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hevent
  refine ⟨Q, ?_⟩
  intro q hq
  have hq' := hQ q hq
  have hexp_pos : 0 < Real.exp (c * ρ ^ q) := Real.exp_pos _
  have hmul :=
    mul_le_mul_of_nonneg_right hq' hexp_pos.le
  have hcancel :
      Real.exp (-(c * ρ ^ q)) * Real.exp (c * ρ ^ q) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    M * (((q : ℝ) + 1) * W ^ q)
        = M * (((q : ℝ) + 1) * W ^ q) *
            Real.exp (-(c * ρ ^ q)) * Real.exp (c * ρ ^ q) := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ 1 * Real.exp (c * ρ ^ q) := hmul
    _ = Real.exp (c * ρ ^ q) := by ring

theorem exists_forall_ge_prefactor_le_exp_gap_of_linear_pow_bound
    {pref gap : ℕ → ℝ} {M W c ρ : ℝ}
    (hM : 0 ≤ M) (hW : 0 < W) (hc : 0 < c) (hρ : 1 < ρ)
    (hpref : ∀ q : ℕ, pref q ≤ M * (((q : ℝ) + 1) * W ^ q))
    (hgap : ∀ q : ℕ, c * ρ ^ q ≤ gap q) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → pref q ≤ Real.exp (gap q) := by
  obtain ⟨Q, hQ⟩ :=
    exists_forall_ge_linear_pow_le_exp_const_mul_pow
      (M := M) (W := W) (c := c) (ρ := ρ) hM hW hc hρ
  refine ⟨Q, ?_⟩
  intro q hq
  calc
    pref q ≤ M * (((q : ℝ) + 1) * W ^ q) := hpref q
    _ ≤ Real.exp (c * ρ ^ q) := hQ q hq
    _ ≤ Real.exp (gap q) := Real.exp_le_exp.mpr (hgap q)

theorem rpow_three_nat_div_eq_inv_rpow_mul
    {B η : ℝ} (q : ℕ) (hB : 0 < B) :
    (((3 : ℝ) ^ (q : ℝ) / B) ^ η) =
      B ^ (-η) * (((3 : ℝ) ^ η) ^ q) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h3q_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
    (Real.rpow_pos_of_pos h3 _).le
  calc
    (((3 : ℝ) ^ (q : ℝ) / B) ^ η)
        = ((3 : ℝ) ^ (q : ℝ)) ^ η / B ^ η := by
          exact Real.div_rpow h3q_nonneg hB.le η
    _ = (3 : ℝ) ^ ((q : ℝ) * η) / B ^ η := by
          rw [← Real.rpow_mul h3.le]
    _ = (3 : ℝ) ^ (η * (q : ℝ)) * B ^ (-η) := by
          rw [Real.rpow_neg hB.le]
          ring_nf
    _ = B ^ (-η) * (((3 : ℝ) ^ η) ^ q) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul h3.le]
          ring_nf

theorem rpow_three_nat_div_gap_eq
    {Btail Blead η : ℝ} (q : ℕ) (hBlead : 0 < Blead) (hBtail : 0 < Btail) :
    (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
        (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η) =
      (Blead ^ (-η) - Btail ^ (-η)) * (((3 : ℝ) ^ η) ^ q) := by
  rw [rpow_three_nat_div_eq_inv_rpow_mul q hBlead,
    rpow_three_nat_div_eq_inv_rpow_mul q hBtail]
  ring

theorem inv_rpow_sub_pos_of_lt
    {Btail Blead η : ℝ}
    (hBlead : 0 < Blead) (hBtail : 0 < Btail)
    (hη : 0 < η) (hlt : Blead < Btail) :
    0 < Blead ^ (-η) - Btail ^ (-η) := by
  have hpow_lt : Blead ^ η < Btail ^ η :=
    Real.rpow_lt_rpow hBlead.le hlt hη
  have hpowB_pos : 0 < Blead ^ η := Real.rpow_pos_of_pos hBlead η
  have hpowT_pos : 0 < Btail ^ η := Real.rpow_pos_of_pos hBtail η
  have hinv_lt : (Btail ^ η)⁻¹ < (Blead ^ η)⁻¹ :=
    (inv_lt_inv₀ hpowT_pos hpowB_pos).2 hpow_lt
  rw [Real.rpow_neg hBlead.le, Real.rpow_neg hBtail.le]
  linarith

theorem geometric_gap_le_rpow_three_nat_div_gap
    {Btail Blead η c ρ : ℝ} {q : ℕ}
    (hBlead : 0 < Blead) (hBtail : 0 < Btail)
    (hc : c ≤ Blead ^ (-η) - Btail ^ (-η))
    (hρ : ρ ≤ (3 : ℝ) ^ η)
    (hc_nonneg : 0 ≤ c) (hρ_nonneg : 0 ≤ ρ) :
    c * ρ ^ q ≤
      (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
        (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η) := by
  have hbase_nonneg : 0 ≤ (3 : ℝ) ^ η :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) η).le
  have hpow_le : ρ ^ q ≤ ((3 : ℝ) ^ η) ^ q :=
    pow_le_pow_left₀ hρ_nonneg hρ q
  calc
    c * ρ ^ q
        ≤ (Blead ^ (-η) - Btail ^ (-η)) * (((3 : ℝ) ^ η) ^ q) := by
          exact mul_le_mul hc hpow_le (pow_nonneg hρ_nonneg q)
            (le_trans hc_nonneg hc)
    _ =
      (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
        (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η) := by
          rw [rpow_three_nat_div_gap_eq q hBlead hBtail]

theorem max_zero_mul_le_mul_max_zero
    {a c : ℝ} (ha : 0 ≤ a) :
    max 0 (a * c) ≤ a * max 0 c := by
  by_cases hc : c ≤ 0
  · have hac : a * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hc
    have hleft : max 0 (a * c) = 0 := max_eq_left hac
    rw [hleft]
    exact mul_nonneg ha (le_max_left 0 c)
  · have hc_nonneg : 0 ≤ c := le_of_not_ge hc
    have hleft : max 0 (a * c) = a * c :=
      max_eq_right (mul_nonneg ha hc_nonneg)
    have hright : max 0 c = c := max_eq_right hc_nonneg
    rw [hleft, hright]

theorem selected_prefactor_le_linear_pow
    {Ctop Cbottom S Kbottom Kcrude w W M : ℝ} {q : ℕ}
    (hw_nonneg : 0 ≤ w) (hW_one : 1 ≤ W) (hwW : w ≤ W)
    (hM :
      max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude) ≤ M) :
    max 0 Ctop +
          max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
          max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
      M * ((((q : ℝ) + 1) * W ^ q)) := by
  let F : ℝ := ((q : ℝ) + 1) * W ^ q
  have hqplus_nonneg : 0 ≤ ((q + 1 : ℕ) : ℝ) := by positivity
  have hqplus_eq : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
  have hW_nonneg : 0 ≤ W := le_trans zero_le_one hW_one
  have hWq_nonneg : 0 ≤ W ^ q := pow_nonneg hW_nonneg q
  have hwq_nonneg : 0 ≤ w ^ q := pow_nonneg hw_nonneg q
  have hwq_le : w ^ q ≤ W ^ q := pow_le_pow_left₀ hw_nonneg hwW q
  have hF_nonneg : 0 ≤ F := mul_nonneg (by positivity) hWq_nonneg
  have hF_one : 1 ≤ F := by
    have hq_one : 1 ≤ (q : ℝ) + 1 := by
      have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
      linarith
    have hWq_one : 1 ≤ W ^ q := one_le_pow₀ hW_one
    have hmul := mul_le_mul hq_one hWq_one zero_le_one
      (by linarith : 0 ≤ (q : ℝ) + 1)
    simpa [F] using hmul
  have htop :
      max 0 Ctop ≤ F * max 0 Ctop := by
    have hcoef : 0 ≤ max 0 Ctop := le_max_left 0 Ctop
    nlinarith
  have hbottom₁ :
      max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) ≤
        F * max 0 (Cbottom * Kbottom) := by
    have ha_nonneg : 0 ≤ ((q + 1 : ℕ) : ℝ) * w ^ q :=
      mul_nonneg hqplus_nonneg hwq_nonneg
    have hrewrite :
        ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom =
          (((q + 1 : ℕ) : ℝ) * w ^ q) * (Cbottom * Kbottom) := by ring
    rw [hrewrite]
    calc
      max 0 ((((q + 1 : ℕ) : ℝ) * w ^ q) * (Cbottom * Kbottom))
          ≤ (((q + 1 : ℕ) : ℝ) * w ^ q) *
              max 0 (Cbottom * Kbottom) :=
            max_zero_mul_le_mul_max_zero ha_nonneg
      _ ≤ F * max 0 (Cbottom * Kbottom) := by
            have hfactor :
                ((q + 1 : ℕ) : ℝ) * w ^ q ≤ F := by
              dsimp [F]
              rw [hqplus_eq]
              exact mul_le_mul_of_nonneg_left hwq_le (by positivity)
            exact mul_le_mul_of_nonneg_right hfactor
              (le_max_left 0 (Cbottom * Kbottom))
  have hbottom₂ :
      max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
        F * max 0 (S * Kcrude) := by
    have ha_nonneg : 0 ≤ ((q + 1 : ℕ) : ℝ) * w ^ q :=
      mul_nonneg hqplus_nonneg hwq_nonneg
    have hrewrite :
        ((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude =
          (((q + 1 : ℕ) : ℝ) * w ^ q) * (S * Kcrude) := by ring
    rw [hrewrite]
    calc
      max 0 ((((q + 1 : ℕ) : ℝ) * w ^ q) * (S * Kcrude))
          ≤ (((q + 1 : ℕ) : ℝ) * w ^ q) *
              max 0 (S * Kcrude) :=
            max_zero_mul_le_mul_max_zero ha_nonneg
      _ ≤ F * max 0 (S * Kcrude) := by
            have hfactor :
                ((q + 1 : ℕ) : ℝ) * w ^ q ≤ F := by
              dsimp [F]
              rw [hqplus_eq]
              exact mul_le_mul_of_nonneg_left hwq_le (by positivity)
            exact mul_le_mul_of_nonneg_right hfactor
              (le_max_left 0 (S * Kcrude))
  calc
    max 0 Ctop +
          max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
          max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude)
        ≤ F * max 0 Ctop + F * max 0 (Cbottom * Kbottom) +
            F * max 0 (S * Kcrude) := by
          linarith
    _ = F * (max 0 Ctop + max 0 (Cbottom * Kbottom) +
          max 0 (S * Kcrude)) := by ring
    _ ≤ F * M := mul_le_mul_of_nonneg_left hM hF_nonneg
    _ = M * (((q : ℝ) + 1) * W ^ q) := by
          dsimp [F]
          ring

/-- Concrete eventual prefactor gap for the selected bad-scale component
prefactors. -/
theorem exists_forall_ge_selected_prefactor_gap
    {Ctop Cbottom S Kbottom Kcrude w Blead Btail η : ℝ}
    (hBlead : 0 < Blead) (hBtail : 0 < Btail)
    (hη : 0 < η) (hlt : Blead < Btail) (hw_nonneg : 0 ≤ w) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
            max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
        Real.exp
          ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
            (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  let W : ℝ := max 1 w
  let M : ℝ :=
    max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude))
  let c : ℝ := Blead ^ (-η) - Btail ^ (-η)
  let ρ : ℝ := (3 : ℝ) ^ η
  have hW_pos : 0 < W := by
    dsimp [W]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 w)
  have hW_one : 1 ≤ W := by
    dsimp [W]
    exact le_max_left 1 w
  have hwW : w ≤ W := by
    dsimp [W]
    exact le_max_right 1 w
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact le_trans zero_le_one (le_max_left 1 _)
  have hM_bound :
      max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude) ≤ M := by
    dsimp [M]
    exact le_max_right 1 _
  have hc_pos : 0 < c := by
    simpa [c] using inv_rpow_sub_pos_of_lt hBlead hBtail hη hlt
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη
  have hρ_nonneg : 0 ≤ ρ := le_of_lt (lt_trans zero_lt_one hρ_gt)
  obtain ⟨Q, hQ⟩ :=
    exists_forall_ge_prefactor_le_exp_gap_of_linear_pow_bound
      (pref := fun q : ℕ =>
        max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
            max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude))
      (gap := fun q : ℕ =>
        (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
          (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η))
      (M := M) (W := W) (c := c) (ρ := ρ)
      hM_nonneg hW_pos hc_pos hρ_gt
      (by
        intro q
        exact selected_prefactor_le_linear_pow
          (Ctop := Ctop) (Cbottom := Cbottom) (S := S)
          (Kbottom := Kbottom) (Kcrude := Kcrude)
          (w := w) (W := W) (M := M) (q := q)
          hw_nonneg hW_one hwW hM_bound)
      (by
        intro q
        exact geometric_gap_le_rpow_three_nat_div_gap
          (Blead := Blead) (Btail := Btail) (η := η)
          (c := c) (ρ := ρ) (q := q)
          hBlead hBtail (le_rfl : c ≤ Blead ^ (-η) - Btail ^ (-η))
          (le_rfl : ρ ≤ (3 : ℝ) ^ η) hc_pos.le hρ_nonneg)
  exact ⟨Q, hQ⟩

end

end Section57
end Ch05
end Book
end Homogenization
