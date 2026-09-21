/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePrefactorGap

/-! # Bad Scale Prefactor Gap Quantitative -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open Filter
open scoped Topology

/-!
# Quantitative prefactor absorption

The earlier prefactor absorption lemma used a `Tendsto` argument and returned
only an eventual threshold.  This file keeps the same deterministic
absorption, but makes the law-dependent part of the threshold explicit through
`max 0 (-log c)`, where `c` is the geometric gap coefficient.  Constants
coming from the finite probe family remain in one law-independent natural
threshold.
-/

noncomputable section

theorem linear_le_exp_linear_eventually
    {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∃ R : ℕ, ∀ q : ℕ, R ≤ q → C * (q : ℝ) ≤ Real.exp (γ * (q : ℝ)) := by
  by_cases hC_zero : C = 0
  · refine ⟨0, ?_⟩
    intro q _
    simp [hC_zero, (Real.exp_pos (γ * (q : ℝ))).le]
  · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC_zero)
    have hγ_ne : γ ≠ 0 := hγ.ne'
    have hscale :
        Tendsto
          (fun q : ℕ => (C / γ) * ((γ * (q : ℝ)) * Real.exp (-(γ * (q : ℝ)))))
          atTop (𝓝 0) := by
      have harg : Tendsto (fun q : ℕ => γ * (q : ℝ)) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.const_mul_atTop hγ
      have hbase :
          Tendsto (fun x : ℝ => x ^ (1 : ℕ) * Real.exp (-x)) atTop (𝓝 0) :=
        Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have hcomp :
          Tendsto
            (fun q : ℕ => (γ * (q : ℝ)) ^ (1 : ℕ) *
              Real.exp (-(γ * (q : ℝ)))) atTop (𝓝 0) :=
        hbase.comp harg
      simpa using hcomp.const_mul (C / γ)
    have hevent :
        ∀ᶠ q : ℕ in atTop,
          (C / γ) * ((γ * (q : ℝ)) * Real.exp (-(γ * (q : ℝ)))) ≤ 1 :=
      hscale.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
    refine ⟨R, ?_⟩
    intro q hq
    have hq' := hR q hq
    have hexp_pos : 0 < Real.exp (γ * (q : ℝ)) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hq' hexp_pos.le
    have hcancel :
        Real.exp (-(γ * (q : ℝ))) * Real.exp (γ * (q : ℝ)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    have hrewrite :
        (C / γ) * ((γ * (q : ℝ)) * Real.exp (-(γ * (q : ℝ)))) *
            Real.exp (γ * (q : ℝ)) =
          C * (q : ℝ) := by
      calc
        (C / γ) * ((γ * (q : ℝ)) * Real.exp (-(γ * (q : ℝ)))) *
            Real.exp (γ * (q : ℝ))
            = (C / γ) * (γ * (q : ℝ)) *
                (Real.exp (-(γ * (q : ℝ))) * Real.exp (γ * (q : ℝ))) := by
              ring
        _ = (C / γ) * (γ * (q : ℝ)) * 1 := by rw [hcancel]
        _ = C * (q : ℝ) := by
              field_simp [hγ_ne]
    calc
      C * (q : ℝ)
          = (C / γ) * ((γ * (q : ℝ)) * Real.exp (-(γ * (q : ℝ)))) *
              Real.exp (γ * (q : ℝ)) := hrewrite.symm
      _ ≤ 1 * Real.exp (γ * (q : ℝ)) := hmul
      _ = Real.exp (γ * (q : ℝ)) := by ring

theorem linear_prefactor_le_exp_linear
    {M W C₀ : ℝ} {q : ℕ}
    (hM : 1 ≤ M) (hW : 1 ≤ W)
    (hlogM : Real.log M ≤ (q : ℝ))
    (hC₀ : 2 + Real.log W ≤ C₀) :
    M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (C₀ * (q : ℝ)) := by
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hW_pos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hM_le : M ≤ Real.exp (q : ℝ) := by
    calc
      M = Real.exp (Real.log M) := by rw [Real.exp_log hM_pos]
      _ ≤ Real.exp (q : ℝ) := Real.exp_le_exp.mpr hlogM
  have hqplus_le : (q : ℝ) + 1 ≤ Real.exp (q : ℝ) := by
    simpa [add_comm] using Real.add_one_le_exp (q : ℝ)
  have hWpow_eq : W ^ q = Real.exp ((q : ℝ) * Real.log W) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos hW_pos]
    ring_nf
  have hprod :
      M * (((q : ℝ) + 1) * W ^ q) ≤
        Real.exp (q : ℝ) * (Real.exp (q : ℝ) *
          Real.exp ((q : ℝ) * Real.log W)) := by
    rw [hWpow_eq]
    have hinner' :
        ((q : ℝ) + 1) * Real.exp ((q : ℝ) * Real.log W) ≤
          Real.exp (q : ℝ) * Real.exp ((q : ℝ) * Real.log W) :=
      mul_le_mul_of_nonneg_right hqplus_le (Real.exp_pos _).le
    have hinner_nonneg :
        0 ≤ ((q : ℝ) + 1) * Real.exp ((q : ℝ) * Real.log W) := by
      positivity
    exact mul_le_mul hM_le hinner'
      hinner_nonneg (Real.exp_pos _).le
  calc
    M * (((q : ℝ) + 1) * W ^ q)
        ≤ Real.exp (q : ℝ) * (Real.exp (q : ℝ) *
          Real.exp ((q : ℝ) * Real.log W)) := hprod
    _ = Real.exp ((2 + Real.log W) * (q : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (C₀ * (q : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC₀ hq_nonneg)

theorem exp_half_log_mul_le_const_mul_pow_of_log_gap
    {c ρ : ℝ} {q : ℕ}
    (hc : 0 < c) (hρ : 1 < ρ)
    (hq :
      (2 * max 0 (-(Real.log c))) / Real.log ρ ≤ (q : ℝ)) :
    Real.exp ((Real.log ρ / 2) * (q : ℝ)) ≤ c * ρ ^ q := by
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ
  have hlogρ_pos : 0 < Real.log ρ := Real.log_pos hρ
  have hU_log : -(Real.log c) ≤ max 0 (-(Real.log c)) :=
    le_max_right 0 (-(Real.log c))
  have hU_le :
      max 0 (-(Real.log c)) ≤ (Real.log ρ / 2) * (q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hq (hlogρ_pos.le)
    have hlog_ne : Real.log ρ ≠ 0 := hlogρ_pos.ne'
    field_simp [hlog_ne] at hmul
    linarith
  have hlogc_lower : -(max 0 (-(Real.log c))) ≤ Real.log c := by
    linarith
  have hmain :
      (Real.log ρ / 2) * (q : ℝ) ≤ Real.log c + (q : ℝ) * Real.log ρ := by
    nlinarith
  calc
    Real.exp ((Real.log ρ / 2) * (q : ℝ))
        ≤ Real.exp (Real.log c + (q : ℝ) * Real.log ρ) :=
          Real.exp_le_exp.mpr hmain
    _ = c * ρ ^ q := by
          rw [Real.exp_add, Real.exp_log hc]
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hρ_pos]
          ring_nf

theorem linear_prefactor_le_exp_const_mul_pow_of_large
    {M W C₀ c ρ : ℝ} {R q : ℕ}
    (hM : 1 ≤ M) (hW : 1 ≤ W)
    (hc : 0 < c) (hρ : 1 < ρ)
    (hC₀ : 2 + Real.log W ≤ C₀)
    (hRlin : ∀ q : ℕ, R ≤ q →
      C₀ * (q : ℝ) ≤ Real.exp ((Real.log ρ / 2) * (q : ℝ)))
    (hqM : Nat.ceil (max 0 (Real.log M)) ≤ q)
    (hqR : R ≤ q)
    (hqc :
      Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ) ≤ q) :
    M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (c * ρ ^ q) := by
  have hlogM : Real.log M ≤ (q : ℝ) := by
    calc
      Real.log M ≤ max 0 (Real.log M) := le_max_right 0 (Real.log M)
      _ ≤ (Nat.ceil (max 0 (Real.log M)) : ℝ) := Nat.le_ceil _
      _ ≤ (q : ℝ) := by exact_mod_cast hqM
  have hpref_linear :
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (C₀ * (q : ℝ)) :=
    linear_prefactor_le_exp_linear hM hW hlogM hC₀
  have hCq_le : C₀ * (q : ℝ) ≤ Real.exp ((Real.log ρ / 2) * (q : ℝ)) :=
    hRlin q hqR
  have hthreshold :
      (2 * max 0 (-(Real.log c))) / Real.log ρ ≤ (q : ℝ) := by
    calc
      (2 * max 0 (-(Real.log c))) / Real.log ρ
          ≤ (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ) : ℝ) :=
            Nat.le_ceil _
      _ ≤ (q : ℝ) := by exact_mod_cast hqc
  have hexp_le :
      Real.exp ((Real.log ρ / 2) * (q : ℝ)) ≤ c * ρ ^ q :=
    exp_half_log_mul_le_const_mul_pow_of_log_gap hc hρ hthreshold
  exact hpref_linear.trans
    (Real.exp_le_exp.mpr (hCq_le.trans hexp_le))

/-- Quantitative version of `exists_forall_ge_selected_prefactor_gap`.  The
integer `R` is law-independent; all law dependence in the threshold is carried
by the explicit term involving `-log c`. -/
theorem exists_forall_ge_selected_prefactor_gap_quantitative
    {Ctop Cbottom S Kbottom Kcrude w Blead Btail η : ℝ}
    (hBlead : 0 < Blead) (hBtail : 0 < Btail)
    (hη : 0 < η) (hlt : Blead < Btail) (hw_nonneg : 0 ≤ w) :
    let W : ℝ := max 1 w
    let M : ℝ :=
      max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude))
    let c : ℝ := Blead ^ (-η) - Btail ^ (-η)
    let ρ : ℝ := (3 : ℝ) ^ η
    let C₀ : ℝ := 2 + Real.log W
    ∃ R : ℕ,
      (∀ q : ℕ, R ≤ q →
        C₀ * (q : ℝ) ≤ Real.exp ((Real.log ρ / 2) * (q : ℝ))) ∧
      ∀ q : ℕ,
        max (Nat.ceil (max 0 (Real.log M)))
            (max R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))) ≤ q →
        max 0 Ctop +
              max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
              max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
          Real.exp
            ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
              (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  intro W M c ρ C₀
  have hW_one : 1 ≤ W := by
    dsimp [W]
    exact le_max_left 1 w
  have hW_pos : 0 < W := lt_of_lt_of_le zero_lt_one hW_one
  have hwW : w ≤ W := by
    dsimp [W]
    exact le_max_right 1 w
  have hM_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left 1 _
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
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hlogW_nonneg : 0 ≤ Real.log W := Real.log_nonneg hW_one
    dsimp [C₀]
    linarith
  obtain ⟨R, hR⟩ :=
    linear_le_exp_linear_eventually
      (C := C₀) (γ := Real.log ρ / 2)
      hC₀_nonneg (by
        have hlogρ_pos : 0 < Real.log ρ := Real.log_pos hρ_gt
        positivity)
  refine ⟨R, hR, ?_⟩
  intro q hq
  have hqM :
      Nat.ceil (max 0 (Real.log M)) ≤ q :=
    (le_max_left _ _).trans hq
  have hqR : R ≤ q :=
    (le_max_left R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))).trans
      ((le_max_right _ _).trans hq)
  have hqc :
      Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ) ≤ q :=
    (le_max_right R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))).trans
      ((le_max_right _ _).trans hq)
  have hpref_linear :
      max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
            max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
        M * (((q : ℝ) + 1) * W ^ q) :=
    selected_prefactor_le_linear_pow
      (Ctop := Ctop) (Cbottom := Cbottom) (S := S)
      (Kbottom := Kbottom) (Kcrude := Kcrude)
      (w := w) (W := W) (M := M) (q := q)
      hw_nonneg hW_one hwW hM_bound
  have hpref_exp :
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (c * ρ ^ q) :=
    linear_prefactor_le_exp_const_mul_pow_of_large
      (M := M) (W := W) (C₀ := C₀) (c := c) (ρ := ρ)
      (R := R) (q := q)
      hM_one hW_one hc_pos hρ_gt
      (le_rfl : 2 + Real.log W ≤ C₀) hR hqM hqR hqc
  have hgap :
      c * ρ ^ q ≤
        (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
          (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η) :=
    geometric_gap_le_rpow_three_nat_div_gap
      (Blead := Blead) (Btail := Btail) (η := η)
      (c := c) (ρ := ρ) (q := q)
      hBlead hBtail (le_rfl : c ≤ Blead ^ (-η) - Btail ^ (-η))
      (le_rfl : ρ ≤ (3 : ℝ) ^ η) hc_pos.le hρ_nonneg
  exact hpref_linear.trans
    (hpref_exp.trans (Real.exp_le_exp.mpr hgap))

/-- Uniform-in-denominator version of the quantitative prefactor gap.  The
integer `R` is selected before the geometric gap coefficient, hence before any
probability law in downstream applications. -/
theorem exists_forall_ge_selected_prefactor_gap_quantitative_uniform
    {Ctop Cbottom S Kbottom Kcrude w η : ℝ}
    (hη : 0 < η) (hw_nonneg : 0 ≤ w) :
    let W : ℝ := max 1 w
    let M : ℝ :=
      max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude))
    let ρ : ℝ := (3 : ℝ) ^ η
    let C₀ : ℝ := 2 + Real.log W
    ∃ R : ℕ,
      (∀ q : ℕ, R ≤ q →
        C₀ * (q : ℝ) ≤ Real.exp ((Real.log ρ / 2) * (q : ℝ))) ∧
      ∀ {Blead Btail : ℝ},
        0 < Blead → 0 < Btail → Blead < Btail →
        let c : ℝ := Blead ^ (-η) - Btail ^ (-η)
        ∀ q : ℕ,
          max (Nat.ceil (max 0 (Real.log M)))
              (max R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))) ≤ q →
          max 0 Ctop +
                max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
                max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
            Real.exp
              ((((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
                (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)) := by
  intro W M ρ C₀
  have hW_one : 1 ≤ W := by
    dsimp [W]
    exact le_max_left 1 w
  have hW_pos : 0 < W := lt_of_lt_of_le zero_lt_one hW_one
  have hwW : w ≤ W := by
    dsimp [W]
    exact le_max_right 1 w
  have hM_one : 1 ≤ M := by
    dsimp [M]
    exact le_max_left 1 _
  have hM_bound :
      max 0 Ctop + max 0 (Cbottom * Kbottom) + max 0 (S * Kcrude) ≤ M := by
    dsimp [M]
    exact le_max_right 1 _
  have hρ_gt : 1 < ρ := by
    dsimp [ρ]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hη
  have hρ_nonneg : 0 ≤ ρ := le_of_lt (lt_trans zero_lt_one hρ_gt)
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hlogW_nonneg : 0 ≤ Real.log W := Real.log_nonneg hW_one
    dsimp [C₀]
    linarith
  obtain ⟨R, hR⟩ :=
    linear_le_exp_linear_eventually
      (C := C₀) (γ := Real.log ρ / 2)
      hC₀_nonneg (by
        have hlogρ_pos : 0 < Real.log ρ := Real.log_pos hρ_gt
        positivity)
  refine ⟨R, hR, ?_⟩
  intro Blead Btail hBlead hBtail hlt c q hq
  have hc_pos : 0 < c := by
    simpa [c] using inv_rpow_sub_pos_of_lt hBlead hBtail hη hlt
  have hqM :
      Nat.ceil (max 0 (Real.log M)) ≤ q :=
    (le_max_left _ _).trans hq
  have hqR : R ≤ q :=
    (le_max_left R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))).trans
      ((le_max_right _ _).trans hq)
  have hqc :
      Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ) ≤ q :=
    (le_max_right R (Nat.ceil ((2 * max 0 (-(Real.log c))) / Real.log ρ))).trans
      ((le_max_right _ _).trans hq)
  have hpref_linear :
      max 0 Ctop +
            max 0 (((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) * Kbottom) +
            max 0 (((q + 1 : ℕ) : ℝ) * (S * w ^ q) * Kcrude) ≤
        M * (((q : ℝ) + 1) * W ^ q) :=
    selected_prefactor_le_linear_pow
      (Ctop := Ctop) (Cbottom := Cbottom) (S := S)
      (Kbottom := Kbottom) (Kcrude := Kcrude)
      (w := w) (W := W) (M := M) (q := q)
      hw_nonneg hW_one hwW hM_bound
  have hpref_exp :
      M * (((q : ℝ) + 1) * W ^ q) ≤ Real.exp (c * ρ ^ q) :=
    linear_prefactor_le_exp_const_mul_pow_of_large
      (M := M) (W := W) (C₀ := C₀) (c := c) (ρ := ρ)
      (R := R) (q := q)
      hM_one hW_one hc_pos hρ_gt
      (le_rfl : 2 + Real.log W ≤ C₀) hR hqM hqR hqc
  have hgap :
      c * ρ ^ q ≤
        (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η) -
          (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η) :=
    geometric_gap_le_rpow_three_nat_div_gap
      (Blead := Blead) (Btail := Btail) (η := η)
      (c := c) (ρ := ρ) (q := q)
      hBlead hBtail (by simp [c])
      (le_rfl : ρ ≤ (3 : ℝ) ^ η) hc_pos.le hρ_nonneg
  exact hpref_linear.trans
    (hpref_exp.trans (Real.exp_le_exp.mpr hgap))

end

end Section57
end Ch05
end Book
end Homogenization
