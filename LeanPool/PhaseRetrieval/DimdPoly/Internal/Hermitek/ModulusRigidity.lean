/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # ModulusRigidity.lean
  Statement-only scaffold for modulus rigidity over a finite Hermite base point.

  Scaffolding notes:
  - `Rigidity/modulus_rigidity.md`
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis

/-! # ModulusRigidity -/


open Complex MeasureTheory Real Finset
open scoped Topology

noncomputable section

namespace HermitekLEAN

-- This rigidity file is proof-complete; suppress repetitive proof-script lint noise file-wide.

/-- If a unique top-order term survives asymptotically, its coefficient must vanish. -/
theorem leading_term_extraction :
    ∀ {N : ℕ} {α : ℂ} {q : ℝ → ℂ},
      (∀ ε : ℝ, 0 < ε → ∃ R0 : ℝ, ∀ r ≥ R0, ‖q r / (r ^ N : ℂ)‖ ≤ ε) →
        (∃ R0 : ℝ, ∀ r ≥ R0, α * (r ^ N : ℂ) + q r = 0) →
          α = 0 := by
  intro N α q hq hzero
  by_contra hα
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  obtain ⟨R1, hR1⟩ := hq (‖α‖ / 2) (by positivity)
  obtain ⟨R2, hR2⟩ := hzero
  let r : ℝ := max 1 (max R1 R2) + 1
  have hr1 : R1 ≤ r := by
    dsimp [r]
    linarith [le_max_left R1 R2, le_max_right 1 (max R1 R2)]
  have hr2 : R2 ≤ r := by
    dsimp [r]
    linarith [le_max_right R1 R2, le_max_right 1 (max R1 R2)]
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith [le_max_left 1 (max R1 R2)]
  have hsmall := hR1 r hr1
  have hzero_r := hR2 r hr2
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hr_pos)
  have hpow : (r ^ N : ℂ) ≠ 0 := pow_ne_zero N hr_ne
  have hdiv : q r / (r ^ N : ℂ) = -α := by
    have hqeq : q r = -(α * (r ^ N : ℂ)) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using hzero_r
    rw [hqeq]
    field_simp [hpow]
  rw [hdiv, norm_neg] at hsmall
  have : ‖α‖ ≤ ‖α‖ / 2 := hsmall
  nlinarith

-- to_mathlib: Mathlib/Algebra/BigOperators/Intervals
/-- Reindex a finite sum over `Icc N (N + L - 1)` to `Fin L`. -/
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m hm
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a ha b hb hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    change N + (n - N) = n
    omega
  · intro m hm
    simp

private def finiteCoeffSeq {d : ℕ} (a : Fin (d + 1) → ℂ) : ℕ → ℂ :=
  fun n => if h : n < d + 1 then a ⟨n, h⟩ else 0

private theorem hermiteSeries_finiteCoeffSeq {k d : ℕ} (a : Fin (d + 1) → ℂ) :
    hermiteSeries k (finiteCoeffSeq a) = finiteHermiteSum k a := by
  funext z
  unfold hermiteSeries finiteHermiteSum finiteCoeffSeq
  rw [tsum_eq_sum (s := Finset.range (d + 1))]
  · have hleft :
        (∑ x : Fin (d + 1), if (x : ℕ) ≤ d then a x * Phi k x.1 z else 0) =
          ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hnle : (n : ℕ) ≤ d := Nat.le_of_lt_succ n.is_lt
        simp [hnle]
    have hsum :=
      Fin.sum_univ_eq_sum_range
        (fun x : ℕ => (if h : x < d + 1 then a ⟨x, h⟩ else 0) * Phi k x z) (d + 1)
    calc
      ∑ x ∈ Finset.range (d + 1), (if h : x < d + 1 then a ⟨x, h⟩ else 0) * Phi k x z =
          ∑ x : Fin (d + 1), if (x : ℕ) ≤ d then a x * Phi k x.1 z else 0 := by
            simpa [Nat.lt_succ_iff] using hsum.symm
      _ = ∑ n : Fin (d + 1), a n * Phi k n.1 z := hleft
  · intro n hn
    have hnot : ¬ n < d + 1 := by
      simpa [Finset.mem_range] using hn
    simp [hnot]

private theorem qkn_eventual_upper_bound (k n : ℕ) :
    ∃ R C : ℝ,
      1 ≤ R ∧ 0 < C ∧ ∀ r ≥ R, ‖(qkn k n r : ℂ)‖ ≤ C * r ^ n := by
  obtain ⟨c0, _, hc0⟩ := qkn_top_term_asymptotic k n
  obtain ⟨R0, hR0⟩ := hc0 1 zero_lt_one
  let C : ℝ := ‖(c0 : ℂ)‖ + 1
  refine ⟨max 1 R0, C, le_max_left 1 R0, by positivity, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left 1 R0) hr
  have hrR0 : R0 ≤ r := le_trans (le_max_right 1 R0) hr
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
  have hrpow_pos : 0 < r ^ n := pow_pos hr_pos _
  have hdiv_norm :
      ‖((qkn k n r : ℂ) / (r ^ n : ℂ))‖ = ‖(qkn k n r : ℂ)‖ / r ^ n := by
    rw [norm_div]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have happrox := hR0 r hrR0
  have hle_div : ‖(qkn k n r : ℂ)‖ / r ^ n ≤ C := by
    rw [← hdiv_norm]
    calc
      ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖
          ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - c0‖ + ‖c0‖ := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              norm_add_le (((qkn k n r : ℂ) / (r ^ n : ℂ)) - c0) c0
      _ ≤ 1 + ‖c0‖ := by
        gcongr
      _ = C := by
        simp [C, add_comm]
  have hmul := mul_le_mul_of_nonneg_right hle_div hrpow_nonneg
  have hrewrite : (‖(qkn k n r : ℂ)‖ / r ^ n) * r ^ n = ‖(qkn k n r : ℂ)‖ := by
    field_simp [hrpow_pos.ne']
  calc
    ‖(qkn k n r : ℂ)‖ = (‖(qkn k n r : ℂ)‖ / r ^ n) * r ^ n := hrewrite.symm
    _ ≤ C * r ^ n := hmul

private theorem qkn_eventual_lower_bound' (k n : ℕ) :
    ∃ R c : ℝ, 0 < c ∧ ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := by
  obtain ⟨c, hc_ne, hc⟩ := qkn_top_term_asymptotic k n
  have hc_norm : 0 < ‖(c : ℂ)‖ := by
    simp [hc_ne]
  obtain ⟨R0, hR0⟩ := hc (‖(c : ℂ)‖ / 2) (by positivity)
  refine ⟨max 1 R0, ‖(c : ℂ)‖ / 2, by positivity, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left 1 R0) hr
  have hrR0 : R0 ≤ r := le_trans (le_max_right 1 R0) hr
  have hclose := hR0 r hrR0
  rw [norm_sub_rev] at hclose
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hmain : ‖(c : ℂ)‖ / 2 ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ := by
    have haux := norm_le_norm_sub_add ((c : ℂ)) ((qkn k n r : ℂ) / (r ^ n : ℂ))
    linarith
  have hpow_nonzero : (r ^ n : ℂ) ≠ 0 := by
    exact pow_ne_zero n (by exact_mod_cast (ne_of_gt hr_pos))
  have hpow_norm : ‖(r ^ n : ℂ)‖ = r ^ n := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
  have hratio_mul :
      ((qkn k n r : ℂ) / (r ^ n : ℂ)) * (r ^ n : ℂ) = (qkn k n r : ℂ) := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hpow_nonzero, mul_one]
  calc
    (‖(c : ℂ)‖ / 2) * r ^ n ≤ ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ * r ^ n := by
      gcongr
    _ = ‖(qkn k n r : ℂ) / (r ^ n : ℂ)‖ * ‖(r ^ n : ℂ)‖ := by rw [hpow_norm]
    _ = ‖((qkn k n r : ℂ) / (r ^ n : ℂ)) * (r ^ n : ℂ)‖ := by rw [norm_mul]
    _ = ‖(qkn k n r : ℂ)‖ := by rw [hratio_mul]

private theorem coeff_eq_zero_of_qkn_eventual_bounds
    {k d n : ℕ} {g : ℕ → ℂ}
    (hdn : d < n)
    (hupper : ∃ R0 C : ℝ, 1 ≤ R0 ∧ ∀ r ≥ R0, ‖g n * (qkn k n r : ℂ)‖ ≤ C * r ^ d)
    (hlower : ∃ R c : ℝ, 0 < c ∧ ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖) :
    g n = 0 := by
  by_contra hg
  obtain ⟨R0, C, hR0, hC⟩ := hupper
  obtain ⟨R, c, hc, hR⟩ := hlower
  let C' : ℝ := max C 0
  have hC' : ∀ r ≥ R0, ‖g n * (qkn k n r : ℂ)‖ ≤ C' * r ^ d := by
    intro r hr
    have hmul : C * r ^ d ≤ C' * r ^ d := by
      have hr_nonneg : 0 ≤ r := le_trans zero_le_one (le_trans hR0 hr)
      have hpow_nonneg : 0 ≤ r ^ d := pow_nonneg hr_nonneg d
      nlinarith [le_max_left C 0, hpow_nonneg]
    exact le_trans (hC r hr) hmul
  have hgn : 0 < ‖g n‖ := norm_pos_iff.mpr hg
  let A : ℝ := c * ‖g n‖
  have hA : 0 < A := by positivity
  have hgrow : Filter.Tendsto (fun x : ℝ => A * x ^ (n - d)) Filter.atTop Filter.atTop := by
    exact (Filter.tendsto_const_mul_pow_atTop_iff).2 ⟨by omega, hA⟩
  obtain ⟨R', hR' : ∀ x ≥ R', C' + 1 ≤ A * x ^ (n - d)⟩ :=
    (Filter.tendsto_atTop_atTop.1 hgrow) (C' + 1)
  let r : ℝ := max R0 (max R R')
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact le_trans hR0 (le_max_left R0 (max R R'))
  have hrR0 : R0 ≤ r := by
    dsimp [r]
    exact le_max_left R0 (max R R')
  have hrR : R ≤ r := by
    dsimp [r]
    exact le_trans (le_max_left R R') (le_max_right R0 (max R R'))
  have hrR' : R' ≤ r := by
    dsimp [r]
    exact le_trans (le_max_right R R') (le_max_right R0 (max R R'))
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hq_lower : c * r ^ n ≤ ‖(qkn k n r : ℂ)‖ := hR r hrR
  have hmul_lower : A * r ^ n ≤ ‖g n * (qkn k n r : ℂ)‖ := by
    calc
      A * r ^ n = ‖g n‖ * (c * r ^ n) := by
        dsimp [A]
        ring
      _ ≤ ‖g n‖ * ‖(qkn k n r : ℂ)‖ := by
        gcongr
      _ = ‖g n * (qkn k n r : ℂ)‖ := by rw [norm_mul]
  have hineq : A * r ^ n ≤ C' * r ^ d := le_trans hmul_lower (hC' r hrR0)
  have hrd_pos : 0 < r ^ d := pow_pos hr_pos _
  have hpow_le : A * r ^ (n - d) ≤ C' := by
    have hineq'' : A * r ^ (d + (n - d)) ≤ C' * r ^ d := by
      simpa [Nat.add_sub_of_le (Nat.le_of_lt hdn)] using hineq
    have hineq' : (A * r ^ (n - d)) * r ^ d ≤ C' * r ^ d := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hineq''
    exact le_of_mul_le_mul_right hineq' hrd_pos
  have hpow_large : C' + 1 ≤ A * r ^ (n - d) := hR' r hrR'
  linarith

private theorem growth_forces_finite_of_eventual_qkn_bounds
    {k d : ℕ} {g : ℕ → ℂ}
    (hupper :
      ∀ n : ℕ,
        d < n →
          ∃ R C : ℝ, 1 ≤ R ∧ ∀ r ≥ R, ‖g n * (qkn k n r : ℂ)‖ ≤ C * r ^ d)
    (hlower :
      ∀ n : ℕ, d < n → ∃ R c : ℝ, 0 < c ∧ ∀ r ≥ R, c * r ^ n ≤ ‖(qkn k n r : ℂ)‖) :
    ∀ n : ℕ, d < n → g n = 0 := by
  intro n hn
  exact coeff_eq_zero_of_qkn_eventual_bounds hn (hupper n hn) (hlower n hn)

private theorem growth_forces_finite_of_qkn_top_term
    {k d : ℕ} {g : ℕ → ℂ}
    (hupper :
      ∀ n : ℕ,
        d < n →
          ∃ R C : ℝ, 1 ≤ R ∧ ∀ r ≥ R, ‖g n * (qkn k n r : ℂ)‖ ≤ C * r ^ d) :
    ∀ n : ℕ, d < n → g n = 0 := by
  intro n hn
  obtain ⟨R, c, hc, hR⟩ := qkn_eventual_lower_bound' k n
  exact coeff_eq_zero_of_qkn_eventual_bounds hn (hupper n hn) ⟨R, c, hc, hR⟩

private theorem circle_series_norm_eq_of_modulus_eq
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hmod : ∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖)
    (r : ℝ) (hr : 0 < r) (t : Circle) :
    ‖circleSeries k (hermiteCoeff k G) r t‖ = ‖finiteCirclePoly k r a t‖ := by
  have hGrep := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
  have hUrep := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
  have hnorm := hmod (circlePoint r t)
  rw [hGrep, hUrep] at hnorm
  have hL :
      ‖circleLeadingFactor k r * (fourier (-↑k)) t * circleSeries k (hermiteCoeff k G) r t‖ =
        ‖circleLeadingFactor k r‖ * ‖(fourier (-↑k)) t‖ *
          ‖circleSeries k (hermiteCoeff k G) r t‖ := by
    rw [norm_mul, norm_mul]
  have hR :
      ‖circleLeadingFactor k r * (fourier (-↑k)) t * finiteCirclePoly k r a t‖ =
        ‖circleLeadingFactor k r‖ * ‖(fourier (-↑k)) t‖ * ‖finiteCirclePoly k r a t‖ := by
    rw [norm_mul, norm_mul]
  rw [hL, hR] at hnorm
  have hfour : ‖(fourier (-↑k)) t‖ = 1 := by
    simp
  rw [hfour] at hnorm
  rw [mul_one] at hnorm
  have hfac : circleLeadingFactor k r ≠ 0 := by
    have hrealpos : 0 < ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) := by
      positivity
    have hnonzero : ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ) : ℝ) ≠ 0 := hrealpos.ne'
    simpa [circleLeadingFactor] using hnonzero
  have hfacnorm : ‖circleLeadingFactor k r‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hfac
  exact mul_left_cancel₀ hfacnorm hnorm

private theorem qkn_ratio_tendsto_zero {k i d : ℕ} (hi : i < d) :
    Filter.Tendsto (fun r : ℝ => ((qkn k i r : ℂ) / (qkn k d r : ℂ))) Filter.atTop (𝓝 (0 : ℂ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, R0, hC, hR0, hbound⟩ := qkn_ratio_control (k := k) (n := i) (d := d) hi
  have hC0 : Filter.Tendsto (fun r : ℝ => (C : ℝ) / r) Filter.atTop (𝓝 (0 : ℝ)) := by
    have hmul :
        Filter.Tendsto (fun r : ℝ => (C : ℝ) * r⁻¹) Filter.atTop (𝓝 ((C : ℝ) * 0)) := by
      exact
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (C : ℝ)) Filter.atTop (𝓝 (C : ℝ))).mul
        tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using hmul
  have hbound' : ∀ᶠ r in Filter.atTop, ‖((qkn k i r : ℂ) / (qkn k d r : ℂ))‖ ≤ C / r := by
    filter_upwards [Filter.eventually_ge_atTop R0] with r hr
    exact hbound r hr
  have hnonneg : ∀ᶠ r in Filter.atTop, 0 ≤ ‖((qkn k i r : ℂ) / (qkn k d r : ℂ))‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  exact squeeze_zero' hnonneg hbound' hC0

private theorem qkn_self_ratio_tendsto_one {k d : ℕ} :
    Filter.Tendsto (fun r : ℝ => ((qkn k d r : ℂ) / (qkn k d r : ℂ))) Filter.atTop (𝓝 (1 : ℂ)) := by
  obtain ⟨R0, hR0, hnonzero⟩ := qkn_eventually_nonzero k d
  have hEq :
      (fun r : ℝ => ((qkn k d r : ℂ) / (qkn k d r : ℂ))) =ᶠ[Filter.atTop] fun _ => (1 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop R0] with r hr
    have hne : (qkn k d r : ℂ) ≠ 0 := by
      exact_mod_cast hnonzero r hr
    field_simp [hne]
  exact hEq.tendsto

private theorem pair_coeff_normalized_tendsto
    {k d : ℕ} (a : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
  Filter.Tendsto
      (fun r : ℝ =>
        ∑ p : Fin (d + 1) × Fin (d + 1),
          a p.1 * star (a p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
            ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
      Filter.atTop (𝓝 (a ⟨d, Nat.lt_succ_self d⟩ * star (a n))) := by
  classical
  let topPair : Fin (d + 1) × Fin (d + 1) := (⟨d, Nat.lt_succ_self d⟩, n)
  let lim : Fin (d + 1) × Fin (d + 1) → ℂ :=
    fun p => if p = topPair then a ⟨d, Nat.lt_succ_self d⟩ * star (a n) else 0
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ p : Fin (d + 1) × Fin (d + 1),
            a p.1 * star (a p.2) *
              (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
              ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
        Filter.atTop (𝓝 (∑ p : Fin (d + 1) × Fin (d + 1), lim p)) := by
    refine tendsto_finsetSum
      (s := (Finset.univ : Finset (Fin (d + 1) × Fin (d + 1))))
      (f := fun p : Fin (d + 1) × Fin (d + 1) => fun r : ℝ =>
        a p.1 * star (a p.2) *
          (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
          ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
          ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
      (a := lim) ?_
    intro p hp
    by_cases htop : p = topPair
    · subst htop
      have hif :
          (if (d : ℤ) - (n.1 : ℤ) = (d : ℤ) - (n : ℤ) then (1 : ℂ) else 0) = 1 := by
        simp
      have hEq :
          (fun r : ℝ =>
            a ⟨d, Nat.lt_succ_self d⟩ * star (a n) *
              (if (d : ℤ) - (n.1 : ℤ) = (d : ℤ) - (n : ℤ) then 1 else 0) *
              ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ))) =ᶠ[Filter.atTop]
            fun _ => (lim topPair : ℂ) := by
        filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
        have hd : (qkn k d r : ℂ) ≠ 0 := by
          exact_mod_cast hd_nonzero r hrD
        have hn : (qkn k n.1 r : ℂ) ≠ 0 := by
          exact_mod_cast hn_nonzero r hrN
        have hselfd : ((qkn k d r : ℂ) / (qkn k d r : ℂ)) = 1 := by
          field_simp [hd]
        have hselfn : ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ)) = 1 := by
          field_simp [hn]
        rw [hif, hselfd, hselfn]
        simp [topPair, lim]
      exact hEq.tendsto
    · by_cases hdiff : (p.1.1 : ℤ) - (p.2.1 : ℤ) = (d : ℤ) - (n : ℤ)
      · have hnot_d : p.1.1 ≠ d := by
          intro hdi
          have hj : p.2.1 = n.1 := by omega
          exact htop (by
            ext <;> simp [topPair, hdi, hj])
        have hnot_n : p.2.1 ≠ n.1 := by
          intro hjn
          have hdi : p.1.1 = d := by omega
          exact htop (by
            ext <;> simp [topPair, hdi, hjn])
        have h1 : p.1.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ p.1.2) hnot_d
        have h2le : p.2.1 ≤ n.1 := by omega
        have h2 : p.2.1 < n.1 := lt_of_le_of_ne h2le hnot_n
        have hri := qkn_ratio_tendsto_zero (k := k) (i := p.1.1) (d := d) h1
        have hrj := qkn_ratio_tendsto_zero (k := k) (i := p.2.1) (d := n.1) h2
        have hprod0 :
            Filter.Tendsto
              (fun r : ℝ =>
                ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
                  ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
              Filter.atTop (𝓝 (0 : ℂ)) := by
          simpa using hri.mul hrj
        have hconst :
            Filter.Tendsto (fun _ : ℝ => a p.1 * star (a p.2)) Filter.atTop
              (𝓝 (a p.1 * star (a p.2))) := by
          exact tendsto_const_nhds
        have hzero0 :
            Filter.Tendsto
              (fun r : ℝ =>
                a p.1 * star (a p.2) *
                  ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
                  ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ)))
              Filter.atTop (𝓝 (0 : ℂ)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hconst.mul hprod0
        simpa [topPair, lim, hdiff, htop, mul_assoc, mul_left_comm, mul_comm] using hzero0
      · simp [lim, hdiff, htop]
  simpa [lim, topPair] using hsum

private theorem fourierCoeff_pair_expansion
    {D : ℕ} (c : Fin D → ℂ) (m : ℤ) :
    fourierCoeff (fun t : Circle =>
      ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
      ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) := by
  classical
  have hsumfun :
      (∑ p : Fin D × Fin D,
        fun t : Circle => c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) =
      fun t : Circle => ∑ p : Fin D × Fin D,
        c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
    ext t
    simp [Finset.sum_apply]
  have hsum := fourierCoeff.sum
    (s := (Finset.univ : Finset (Fin D × Fin D)))
    (f := fun p : Fin D × Fin D => fun t : Circle =>
      c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t)
    (by
      intro p hp
      have hcont :
          Continuous (fun t : Circle =>
            c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) := by
        continuity
      have hcf :
          HasCompactSupport (fun t : Circle =>
            c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) := by
        unfold HasCompactSupport
        exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (by
          intro x hx
          trivial)
      exact Continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) hcont hcf)
  rw [hsumfun] at hsum
  have hsum' := congrArg (fun F => F m) hsum
  have hsum'' :
      fourierCoeff (fun t : Circle =>
        ∑ p : Fin D × Fin D,
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
      ∑ p : Fin D × Fin D,
        fourierCoeff (fun t : Circle =>
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m := by
    simpa [Finset.sum_apply] using hsum'
  rw [hsum'']
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hfreq :
      fourierCoeff (T := T) (fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ))) m =
        if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0 := by
    have hpi :
        Pi.single (ι := ℤ) (M := fun _ => ℂ) ((p.1.1 : ℤ) - (p.2.1 : ℤ)) (1 : ℂ) m =
          if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0 := by
      by_cases h : (p.1.1 : ℤ) - (p.2.1 : ℤ) = m
      · subst h
        simp [Pi.single, Function.update]
      · have hneq : ¬ m = ((p.1.1 : ℤ) - (p.2.1 : ℤ)) := by
          intro hm
          exact h hm.symm
        simp [Pi.single, Function.update, h, hneq]
    simpa using
      (congrArg (fun F : ℤ → ℂ => F m)
        (fourierCoeff_fourier (T := T) ((p.1.1 : ℤ) - (p.2.1 : ℤ)))).trans hpi
  calc
    fourierCoeff (fun t : Circle =>
      c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t) m =
        c p.1 * star (c p.2) * fourierCoeff (T := T)
          (fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ))) m := by
            simpa [mul_assoc] using
              (fourierCoeff.const_mul (T := T)
                (f := fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)))
                (c := c p.1 * star (c p.2)) (n := m))
    _ = c p.1 * star (c p.2) * (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) := by
          rw [hfreq]

/-- Modulus equality against a finite Hermite sum forces vanishing of high Hermite coefficients. -/
/-
Blocker:
The imported asymptotic API already supplies both the lower growth of `qkn` and
the eventual upper bound for each fixed finite coefficient on the explicit
finite side. What is still missing is a way to connect a prescribed expansion

  `G = hermiteSeries k g`

to the circle-side coefficients for that same sequence `g`.

For the scaffolding-note theorem, the needed eventual upper bound on the canonical
Hermite coefficients comes from the circle representation of an `Hk` element
together with coefficient extraction on each circle. The exported theorem
`circle_representation` is only existential in the coefficient sequence, so the
statement below uses the canonical extractor `hermiteCoeff` directly.

So the explicit finite side is no longer the issue here: the helpers above
already identify `finiteHermiteSum k a` with a concrete finite-support
expansion and place it in `Hk`. The remaining work is the circle-side control
needed to force vanishing of the coefficients above degree `d`.

The frozen scaffolding note only needs coefficient vanishing for an `Hk` element once
the finite comparison function is fixed. The canonical extractor
`hermiteCoeff` already provides the coefficient sequence of `G`, so the public
contract below now states the exact theorem needed by scaffolding notes.
-/
theorem growth_forces_finite :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by
  intro k d a hTop G hG hmod n hn
  have hupper :
      ∃ R C : ℝ,
        1 ≤ R ∧
          ∀ r ≥ R, ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤ C * r ^ d := by
    classical
    have hq :
        ∀ i : Fin (d + 1),
          ∃ R C : ℝ,
            1 ≤ R ∧ 0 < C ∧ ∀ r ≥ R, ‖(qkn k i.1 r : ℂ)‖ ≤ C * r ^ i.1 := by
      intro i
      simpa using qkn_eventual_upper_bound k i.1
    choose R_i C_i hR_i hC_i hqi using hq
    have hnonemptyR : (Finset.univ.image R_i).Nonempty := by
      refine ⟨R_i ⟨d, Nat.lt_succ_self d⟩, ?_⟩
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hnonemptyC : (Finset.univ.image C_i).Nonempty := by
      refine ⟨C_i ⟨d, Nat.lt_succ_self d⟩, ?_⟩
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    let Rbar : ℝ := (Finset.univ.image R_i).max' hnonemptyR
    let Cmax : ℝ := (Finset.univ.image C_i).max' hnonemptyC
    have hRbar_ge : ∀ i : Fin (d + 1), R_i i ≤ Rbar := by
      intro i
      dsimp [Rbar]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hCmax_ge : ∀ i : Fin (d + 1), C_i i ≤ Cmax := by
      intro i
      dsimp [Cmax]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hCmax_pos : 0 < Cmax := by
      dsimp [Cmax]
      exact lt_of_lt_of_le (hC_i ⟨d, Nat.lt_succ_self d⟩) (hCmax_ge ⟨d, Nat.lt_succ_self d⟩)
    refine ⟨max 1 Rbar, (∑ i : Fin (d + 1), ‖a i‖) * Cmax, le_max_left _ _, ?_⟩
    intro r hr
    have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    have hrbar : Rbar ≤ r := le_trans (le_max_right _ _) hr
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hqmax : ∀ i : Fin (d + 1), ‖(qkn k i.1 r : ℂ)‖ ≤ Cmax * r ^ d := by
      intro i
      have hRi : R_i i ≤ r := le_trans (hRbar_ge i) hrbar
      have hq0 : ‖(qkn k i.1 r : ℂ)‖ ≤ C_i i * r ^ i.1 := hqi i r hRi
      have hCi : C_i i ≤ Cmax := hCmax_ge i
      have hi_le : i.1 ≤ d := Nat.le_of_lt_succ i.is_lt
      calc
        ‖(qkn k i.1 r : ℂ)‖ ≤ C_i i * r ^ i.1 := hq0
        _ ≤ Cmax * r ^ i.1 := by gcongr
        _ ≤ Cmax * r ^ d := by
              have hpow : r ^ i.1 ≤ r ^ d := pow_le_pow_right₀ hr1 hi_le
              have hCmax_nonneg : 0 ≤ Cmax := le_of_lt hCmax_pos
              exact mul_le_mul_of_nonneg_left hpow hCmax_nonneg
    have hconst :
        (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d =
          (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by
      have hmul :=
        congrArg (fun x : ℝ => x * r ^ d)
          (Finset.sum_mul (s := Finset.univ) (f := fun i : Fin (d + 1) => ‖a i‖) (a := Cmax))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul.symm
    have hpoly_bound :
        ∀ t : Circle, ‖finiteCirclePoly k r a t‖ ≤ (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
      intro t
      have hraw :
          ‖∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        calc
        ‖∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖
            ≤ ∑ i : Fin (d + 1), ‖a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t‖ := by
              exact norm_sum_le _ _
        _ = ∑ i : Fin (d + 1), ‖a i‖ * ‖(qkn k i.1 r : ℂ)‖ * ‖(fourier (i.1 : ℤ)) t‖ := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [norm_mul, norm_mul]
        _ ≤ ∑ i : Fin (d + 1), ‖a i‖ * Cmax * r ^ d := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hfour : ‖(fourier (i.1 : ℤ)) t‖ = 1 := by
                simp [fourier_apply]
              rw [hfour, mul_one]
              have hmul := mul_le_mul_of_nonneg_left (hqmax i) (norm_nonneg (a i))
              simpa [mul_assoc] using hmul
        _ = (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
              rw [Finset.sum_mul]
      have hsum :
          positiveTrigonometricPolynomial (frequencyBand 0 (d + 1)) (finiteCircleCoeff k r a) t =
            ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
        rw [show
          positiveTrigonometricPolynomial (frequencyBand 0 (d + 1)) (finiteCircleCoeff k r a) t =
            ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r a n * fourier (n : ℤ) t by rfl]
        have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
          simpa [HermiteLEAN.frequencyBand] using (show Finset.Icc 0 d = Finset.range (d + 1) by
            ext n
            simp [Finset.mem_Icc])
        rw [hband, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
        simp [finiteCircleCoeff, fourier_apply, hxle]
      rw [finiteCirclePoly, hsum]
      exact hraw
    have hpoint :
        ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤
          (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by
      have hbound : ∀ᵐ t ∂AddCircle.haarAddCircle,
          ‖fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        refine Filter.Eventually.of_forall ?_
        intro t
        rw [norm_smul]
        have hfour : ‖(fourier (-(n : ℤ))) t‖ = 1 := by
          simp [fourier_apply]
        rw [hfour, one_mul]
        rw [circle_series_norm_eq_of_modulus_eq (k := k) (d := d) (a := a) (G := G) hG hmod r
          hr_pos t]
        exact hpoly_bound t
      have hInt0 :
          ‖∫ t : Circle, fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t
              ∂AddCircle.haarAddCircle‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d := by
        simpa using
          MeasureTheory.norm_integral_le_of_norm_le_const
            (μ := AddCircle.haarAddCircle) (f := fun t : Circle =>
              fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t)
            (C := (∑ i : Fin (d + 1), ‖a i‖ * Cmax) * r ^ d) hbound
      have hInt :
          ‖∫ t : Circle, fourier (-(n : ℤ)) t • circleSeries k (hermiteCoeff k G) r t
              ∂AddCircle.haarAddCircle‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by
        simpa [hconst] using hInt0
      have hfour :
          fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ) =
            hermiteCoeff k G n * (qkn k n r : ℂ) := by
        simpa using
          (circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr_pos n)
      have hCoeffInt :
          ‖fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ)‖ ≤
            (∑ i : Fin (d + 1), ‖a i‖) * Cmax * r ^ d := by
        simpa [fourierCoeff] using hInt
      have hEq :
          ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ =
            ‖fourierCoeff (circleSeries k (hermiteCoeff k G) r) (n : ℤ)‖ := by
        rw [hfour]
      rw [hEq]
      exact hCoeffInt
    exact hpoint
  have hlower := qkn_eventual_lower_bound' k n
  exact coeff_eq_zero_of_qkn_eventual_bounds hn hupper hlower

/-- The coefficient relation `topA · conj(aₙ) = topB · conj(bₙ)` derived from the
pointwise modulus equality of two finite Hermite sums.  Extracted from
`finite_modulus_rigidity` to respect the proof size limit. -/
private lemma finite_modulus_coeff_rel {k d : ℕ} (a b : Fin (d + 1) → ℂ)
    (topA topB : ℂ) (htopA : topA = topCoeff a) (htopB : topB = topCoeff b)
    (hprod_expand : ∀ {D : ℕ} (c : Fin D → ℂ) (t : Circle),
      (∑ n : Fin D, c n * fourier (n : ℤ) t) *
          star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
        ∑ p : Fin D × Fin D,
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t)
    (hsumA : ∀ {r : ℝ}, 0 < r → ∀ t : Circle,
      finiteCirclePoly k r a t =
        ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t)
    (hsumB : ∀ {r : ℝ}, 0 < r → ∀ t : Circle,
      finiteCirclePoly k r b t =
        ∑ i : Fin (d + 1), b i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t)
    (hpoly_norm : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle, ‖finiteCirclePoly k r b t‖ = ‖finiteCirclePoly k r a t‖) :
    ∀ n : Fin (d + 1), topA * star (a n) = topB * star (b n) := by
  intro n
  let m : ℤ := (d : ℤ) - (n : ℤ)
  let rawA : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      a p.1 * star (a p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ)
  let rawB : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      b p.1 * star (b p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ)
  let Fa : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      a p.1 * star (a p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
        ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))
  let Fb : ℝ → ℂ := fun r =>
    ∑ p : Fin (d + 1) × Fin (d + 1),
      b p.1 * star (b p.2) *
        (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
        ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
        ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))
  have hAcoeff : ∀ r : ℝ, 0 < r →
      fourierCoeff (fun t : Circle =>
        finiteCirclePoly k r a t * star (finiteCirclePoly k r a t)) m = rawA r := by
    intro r hr
    have hprod_eq :
        (fun t : Circle =>
          finiteCirclePoly k r a t * star (finiteCirclePoly k r a t)) =
        fun t : Circle =>
          ∑ p : Fin (d + 1) × Fin (d + 1),
            (a p.1 * (qkn k p.1.1 r : ℂ)) *
              star (a p.2 * (qkn k p.2.1 r : ℂ)) *
                fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
      ext t
      rw [hsumA (r := r) hr t]
      simpa [mul_assoc, mul_left_comm, mul_comm, qkn_real] using
        (hprod_expand (D := d + 1)
          (c := fun i : Fin (d + 1) => a i * (qkn k i.1 r : ℂ)) t)
    have hcoeff :=
      congrArg (fun F : Circle → ℂ => fourierCoeff F m) hprod_eq
    simpa [rawA, m, mul_assoc, mul_left_comm, mul_comm, qkn_real] using
      (hcoeff.trans
        (fourierCoeff_pair_expansion (D := d + 1)
          (c := fun i : Fin (d + 1) => a i * (qkn k i.1 r : ℂ))
          (m := m)))
  have hBcoeff : ∀ r : ℝ, 0 < r →
      fourierCoeff (fun t : Circle =>
        finiteCirclePoly k r b t * star (finiteCirclePoly k r b t)) m = rawB r := by
    intro r hr
    have hprod_eq :
        (fun t : Circle =>
          finiteCirclePoly k r b t * star (finiteCirclePoly k r b t)) =
        fun t : Circle =>
          ∑ p : Fin (d + 1) × Fin (d + 1),
            (b p.1 * (qkn k p.1.1 r : ℂ)) *
              star (b p.2 * (qkn k p.2.1 r : ℂ)) *
                fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
      ext t
      rw [hsumB (r := r) hr t]
      simpa [mul_assoc, mul_left_comm, mul_comm, qkn_real] using
        (hprod_expand (D := d + 1)
          (c := fun i : Fin (d + 1) => b i * (qkn k i.1 r : ℂ)) t)
    have hcoeff :=
      congrArg (fun F : Circle → ℂ => fourierCoeff F m) hprod_eq
    simpa [rawB, m, mul_assoc, mul_left_comm, mul_comm, qkn_real] using
      (hcoeff.trans
        (fourierCoeff_pair_expansion (D := d + 1)
          (c := fun i : Fin (d + 1) => b i * (qkn k i.1 r : ℂ))
          (m := m)))
  have hraw_eq : ∀ r : ℝ, 0 < r → rawA r = rawB r := by
    intro r hr
    have hprod_eq :
        (fun t : Circle =>
          finiteCirclePoly k r a t * star (finiteCirclePoly k r a t)) =
        (fun t : Circle =>
          finiteCirclePoly k r b t * star (finiteCirclePoly k r b t)) := by
      ext t
      calc
        finiteCirclePoly k r a t * star (finiteCirclePoly k r a t) =
            ‖finiteCirclePoly k r a t‖ ^ 2 := by
              simpa using (RCLike.mul_conj (finiteCirclePoly k r a t))
        _ = ‖finiteCirclePoly k r b t‖ ^ 2 := by
              rw [hpoly_norm (r := r) hr t]
        _ = finiteCirclePoly k r b t * star (finiteCirclePoly k r b t) := by
              symm
              simpa using (RCLike.mul_conj (finiteCirclePoly k r b t))
    have hcoeff :=
      congrArg (fun F : Circle → ℂ => fourierCoeff F m) hprod_eq
    simpa [rawA, rawB] using (hAcoeff r hr).symm.trans (hcoeff.trans (hBcoeff r hr))
  obtain ⟨Rd, hRd, hRd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hRn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hEqFaFb : Fa =ᶠ[Filter.atTop] Fb := by
    filter_upwards [Filter.eventually_ge_atTop (max Rd Rn)] with r hr
    have h1 : 1 ≤ r := by
      have hmax : 1 ≤ max Rd Rn := le_trans hRd (le_max_left _ _)
      exact le_trans hmax hr
    have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one h1
    have hraw := hraw_eq r hr_pos
    have hd : (qkn k d r : ℂ) ≠ 0 := by
      exact_mod_cast hRd_nonzero r (le_trans (le_max_left _ _) hr)
    have hn : (qkn k n.1 r : ℂ) ≠ 0 := by
      exact_mod_cast hRn_nonzero r (le_trans (le_max_right _ _) hr)
    have hmulA' :
        (∑ p : Fin (d + 1) × Fin (d + 1),
          a p.1 * star (a p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
            ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))) *
          ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) =
        ∑ p : Fin (d + 1) × Fin (d + 1),
          a p.1 * star (a p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
            (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      field_simp [hd, hn]
    have hmulB' :
        (∑ p : Fin (d + 1) × Fin (d + 1),
          b p.1 * star (b p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
            ((qkn k p.1.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k p.2.1 r : ℂ) / (qkn k n.1 r : ℂ))) *
          ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) =
        ∑ p : Fin (d + 1) × Fin (d + 1),
          b p.1 * star (b p.2) *
            (if (p.1.1 : ℤ) - (p.2.1 : ℤ) = m then 1 else 0) *
            (qkn k p.1.1 r : ℂ) * (qkn k p.2.1 r : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      field_simp [hd, hn]
    have hmulA : Fa r * ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) = rawA r := by
      simpa [Fa, rawA, mul_assoc, mul_left_comm, mul_comm] using hmulA'
    have hmulB : Fb r * ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) = rawB r := by
      simpa [Fb, rawB, mul_assoc, mul_left_comm, mul_comm] using hmulB'
    have hD : ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) ≠ 0 := mul_ne_zero hd hn
    apply mul_right_cancel₀ hD
    calc
      Fa r * ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) = rawA r := hmulA
      _ = rawB r := hraw
      _ = Fb r * ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) := hmulB.symm
  have hFa_tendsto : Filter.Tendsto Fa Filter.atTop (𝓝 (topA * star (a n))) := by
    rw [htopA]
    exact pair_coeff_normalized_tendsto (k := k) (d := d) (a := a) (n := n)
  have hFb_tendsto : Filter.Tendsto Fb Filter.atTop (𝓝 (topB * star (b n))) := by
    rw [htopB]
    exact pair_coeff_normalized_tendsto (k := k) (d := d) (a := b) (n := n)
  have hlim : topA * star (a n) = topB * star (b n) := by
    have hFa' : Filter.Tendsto Fb Filter.atTop (𝓝 (topA * star (a n))) :=
      hFa_tendsto.congr' hEqFaFb
    exact tendsto_nhds_unique hFa' hFb_tendsto
  exact hlim

/-- Finite modulus rigidity up to a unimodular scalar. -/
theorem finite_modulus_rigidity :
    ∀ {k d : ℕ}
      (a b : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0),
        (∀ z : ℂ, ‖finiteHermiteSum k b z‖ = ‖finiteHermiteSum k a z‖) →
          ∃ w : ℂ, ‖w‖ = 1 ∧ finiteHermiteSum k b = w • finiteHermiteSum k a := by
  intro k d a b hTop hmod
  let topA : ℂ := topCoeff a
  let topB : ℂ := topCoeff b
  let w : ℂ := topB / topA
  have htopA : topA ≠ 0 := hTop
  have hprod_expand {D : ℕ} (c : Fin D → ℂ) (t : Circle) :
      (∑ n : Fin D, c n * fourier (n : ℤ) t) *
          star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
        ∑ p : Fin D × Fin D,
          c p.1 * star (c p.2) * fourier ((p.1.1 : ℤ) - (p.2.1 : ℤ)) t := by
    have hstar : star (∑ n : Fin D, c n * fourier (n : ℤ) t) =
        ∑ n : Fin D, star (c n * fourier (n : ℤ) t) := by
      simp
    have hconj : ∀ (x : Fin D) (t : Circle),
        (starRingEnd ℂ) ↑(AddCircle.toCircle ((x : ℕ) • t)) =
          ↑(AddCircle.toCircle (-((x : ℕ) • t))) := by
      intro x t
      rw [← Circle.coe_inv_eq_conj, ← AddCircle.toCircle_neg]
    rw [hstar, Fintype.sum_mul_sum]
    simp only [hconj, fourier_apply, natCast_zsmul, star_mul', RCLike.star_def, mul_assoc,
      mul_left_comm, mul_comm]
    rw [← Fintype.sum_prod_type']
    simp [mul_assoc, sub_eq_add_neg]
  have hsumA : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle,
        finiteCirclePoly k r a t =
          ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
    intro r hr t
    rw [finiteCirclePoly,
      show positiveTrigonometricPolynomial (frequencyBand 0 (d + 1))
          (finiteCircleCoeff k r a) t =
        ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r a n * fourier (n : ℤ) t by rfl]
    have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
      simpa [HermiteLEAN.frequencyBand] using (show Finset.Icc 0 d = Finset.range (d + 1) by
        ext n
        simp [Finset.mem_Icc])
    rw [hband, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
    simp [finiteCircleCoeff, fourier_apply, hxle]
  have hsumB : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle,
        finiteCirclePoly k r b t =
          ∑ i : Fin (d + 1), b i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
    intro r hr t
    rw [finiteCirclePoly,
      show positiveTrigonometricPolynomial (frequencyBand 0 (d + 1))
          (finiteCircleCoeff k r b) t =
        ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r b n * fourier (n : ℤ) t by rfl]
    have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
      simpa [HermiteLEAN.frequencyBand] using (show Finset.Icc 0 d = Finset.range (d + 1) by
        ext n
        simp [Finset.mem_Icc])
    rw [hband, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
    simp [finiteCircleCoeff, fourier_apply, hxle]
  have hpoly_norm : ∀ {r : ℝ}, 0 < r →
      ∀ t : Circle, ‖finiteCirclePoly k r b t‖ = ‖finiteCirclePoly k r a t‖ := by
    intro r hr t
    have hB := finiteHermiteSum_circle (k := k) (a := b) (r := r) hr t
    have hA := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
    have hnorm := hmod (circlePoint r t)
    rw [hB, hA] at hnorm
    have hL :
        ‖circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
            finiteCirclePoly k r b t‖ =
          ‖circleLeadingFactor k r‖ * ‖(fourier (-(k : ℤ))) t‖ *
            ‖finiteCirclePoly k r b t‖ := by
      rw [norm_mul, norm_mul]
    have hR :
        ‖circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
            finiteCirclePoly k r a t‖ =
          ‖circleLeadingFactor k r‖ * ‖(fourier (-(k : ℤ))) t‖ *
            ‖finiteCirclePoly k r a t‖ := by
      rw [norm_mul, norm_mul]
    rw [hL, hR] at hnorm
    have hfour : ‖(fourier (-(k : ℤ))) t‖ = 1 := by
      simp
    have hfac : circleLeadingFactor k r ≠ 0 := by
      have hrealpos : 0 < ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) := by
        positivity
      have hnonzero :
          ((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ) : ℝ) ≠ 0 := hrealpos.ne'
      simpa [circleLeadingFactor] using hnonzero
    have hfacnorm : ‖circleLeadingFactor k r‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hfac
    have hnorm' :
        ‖circleLeadingFactor k r‖ * ‖finiteCirclePoly k r b t‖ =
          ‖circleLeadingFactor k r‖ * ‖finiteCirclePoly k r a t‖ := by
      simpa [hfour] using hnorm
    exact mul_left_cancel₀ hfacnorm hnorm'
  have hcoeff_rel : ∀ n : Fin (d + 1), topA * star (a n) = topB * star (b n) :=
    finite_modulus_coeff_rel a b topA topB rfl rfl hprod_expand hsumA hsumB hpoly_norm
  have htop_rel : topA * star topA = topB * star topB := by
    have h := hcoeff_rel ⟨d, Nat.lt_succ_self d⟩
    exact h
  have hw_norm : ‖w‖ = 1 := by
    dsimp [w]
    have hmul : ‖topA‖ * ‖topA‖ = ‖topB‖ * ‖topB‖ := by
      simpa [norm_mul, norm_star] using congrArg norm htop_rel
    have hsq : ‖topA‖ ^ 2 = ‖topB‖ ^ 2 := by
      simpa [sq] using hmul
    have hnorm : ‖topA‖ = ‖topB‖ := by
      have hcases := (sq_eq_sq_iff_eq_or_eq_neg (a := ‖topA‖) (b := ‖topB‖)).mp hsq
      rcases hcases with h | h
      · exact h
      · exfalso
        have hb_nonneg : 0 ≤ ‖topB‖ := norm_nonneg _
        have ha_nonneg : 0 ≤ ‖topA‖ := norm_nonneg _
        have hb_zero : ‖topB‖ = 0 := by
          apply le_antisymm
          · linarith [h, ha_nonneg]
          · exact hb_nonneg
        have ha_zero : ‖topA‖ = 0 := by simpa [hb_zero] using h
        exact htopA (norm_eq_zero.mp ha_zero)
    have hb_norm : ‖topB‖ ≠ 0 := by
      have ha_norm : ‖topA‖ ≠ 0 := norm_ne_zero_iff.mpr htopA
      simpa [hnorm] using ha_norm
    rw [norm_div, hnorm]
    field_simp [hb_norm]
  have hw_conj : w * star w = 1 := by
    simpa [hw_norm] using (RCLike.mul_conj w)
  have hb_coeff : ∀ n : Fin (d + 1), b n = w * a n := by
    intro n
    have hrel := hcoeff_rel n
    have hw_top : topB = w * topA := by
      dsimp [w]
      field_simp [htopA]
    have hstarcoeff : star (a n) = w * star (b n) := by
      apply mul_left_cancel₀ htopA
      simpa [hw_top, mul_assoc, mul_left_comm, mul_comm] using hrel
    have hstarcoeff' : a n = star w * b n := by
      have h := congrArg star hstarcoeff
      simpa [star_mul, mul_assoc, mul_left_comm, mul_comm] using h
    calc
      b n = (w * star w) * b n := by
        rw [hw_conj, one_mul]
      _ = w * (star w * b n) := by
        rw [mul_assoc]
      _ = w * a n := by
        rw [hstarcoeff']
  have hfun : finiteHermiteSum k b = w • finiteHermiteSum k a := by
    funext z
    calc
      finiteHermiteSum k b z = ∑ n : Fin (d + 1), w * (a n * Phi k n.1 z) := by
        simp [finiteHermiteSum, hb_coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = w * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
        rw [Finset.mul_sum]
  refine ⟨w, hw_norm, hfun⟩

/-- Full modulus rigidity inside `H_k`. -/
theorem modulus_rigidity :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, ‖G z‖ = ‖finiteHermiteSum k a z‖) →
            ∃ w : ℂ, ‖w‖ = 1 ∧ G = w • finiteHermiteSum k a := by
  intro k d a hTop G hG hmod
  let b : Fin (d + 1) → ℂ := fun n => hermiteCoeff k G n.1
  have hvanish : ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by
    exact growth_forces_finite (k := k) (d := d) (a := a) hTop hG hmod
  have hcoeffs : hermiteCoeff k G = finiteCoeffSeq b := by
    funext n
    unfold finiteCoeffSeq
    by_cases hn : n < d + 1
    · simp [hn, b]
    · have hnd : d < n := by omega
      simp [hn, hvanish n hnd]
  have hG_eq : G = finiteHermiteSum k b := by
    calc
      G = hermiteSeries k (hermiteCoeff k G) := hermiteCoeff_expansion (k := k) (G := G) hG
      _ = hermiteSeries k (finiteCoeffSeq b) := by rw [hcoeffs]
      _ = finiteHermiteSum k b := (hermiteSeries_finiteCoeffSeq (k := k) (d := d) b).trans
        rfl
  have hmod' : ∀ z : ℂ, ‖finiteHermiteSum k b z‖ = ‖finiteHermiteSum k a z‖ := by
    intro z
    simpa [hG_eq] using hmod z
  obtain ⟨w, hw, hwb⟩ := finite_modulus_rigidity (k := k) (d := d) (a := a) (b := b) hTop hmod'
  refine ⟨w, hw, ?_⟩
  simpa [hG_eq] using hwb

/-- A complex number with zero real part is a real multiple of `I`. -/
private lemma exists_I_mul_of_re_eq_zero (z : ℂ) (hz : z.re = 0) :
    ∃ c : ℝ, z = Complex.I * (c : ℂ) := by
  refine ⟨z.im, ?_⟩
  apply Complex.ext <;> simp [hz]

/-- A nonzero top coefficient forces a nonzero finite Hermite sum. -/
private lemma finiteHermiteSum_nonzero
    {k d : ℕ} (a : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0) :
    finiteHermiteSum k a ≠ 0 := by
  intro hzero
  have hcoeff : hermiteCoeff k (finiteHermiteSum k a) d = topCoeff a := by
    simpa [topCoeff] using (hermiteCoeff_finiteHermiteSum (k := k) a d)
  have hcoeff0 : hermiteCoeff k (finiteHermiteSum k a) d = 0 := by
    rw [hzero]
    unfold hermiteCoeff weightedInner
    change (1 / Real.pi : ℂ) *
        ∫ z : ℂ, (0 : ℂ) * (starRingEnd ℂ) (Phi k d z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0
    simp
  exact hTop (hcoeff.symm.trans hcoeff0)

/-- A nonzero top coefficient forces positive weighted norm. -/
private lemma finiteHermiteSum_weightedNorm_pos
    {k d : ℕ} (a : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0) :
    0 < weightedNorm (finiteHermiteSum k a) := by
  have hne : finiteHermiteSum k a ≠ 0 := finiteHermiteSum_nonzero a hTop
  have hsq : 0 < weightedNormSq (finiteHermiteSum k a) := by
    rw [finiteHermiteSum_normSq]
    have hterm : 0 < ‖a ⟨d, Nat.lt_succ_self d⟩‖ ^ 2 := by
      have ha : a ⟨d, Nat.lt_succ_self d⟩ ≠ 0 := by
        simpa [topCoeff] using hTop
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr ha)
    have hle :
        ‖a ⟨d, Nat.lt_succ_self d⟩‖ ^ 2 ≤ ∑ n : Fin (d + 1), ‖a n‖ ^ 2 := by
      simpa using
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖a j‖)
          (by simp : ⟨d, Nat.lt_succ_self d⟩ ∈ (Finset.univ : Finset (Fin (d + 1)))))
    exact lt_of_lt_of_le hterm hle
  unfold weightedNorm
  exact Real.sqrt_pos.2 hsq

/-- Shifting a Fourier coefficient by a monomial. -/
private lemma fourierCoeff_mul_fourier
    (f : Circle → ℂ) (m n : ℤ) :
    fourierCoeff (fun t => f t * fourier n t) m = fourierCoeff f (m - n) := by
  simp [fourierCoeff, mul_assoc, mul_comm, sub_eq_add_neg]

/-- Fourier coefficients commute with conjugation up to the expected sign change. -/
private lemma fourierCoeff_star
    (f : Circle → ℂ) (m : ℤ) :
    fourierCoeff (fun t => star (f t)) m = star (fourierCoeff f (-m)) := by
  calc
    fourierCoeff (fun t => star (f t)) m
        = star (∫ t : Circle, fourier m t * f t ∂AddCircle.haarAddCircle) := by
          simpa [fourierCoeff, mul_comm, mul_left_comm, mul_assoc] using
            (integral_conj (μ := AddCircle.haarAddCircle)
              (f := fun t : Circle => fourier m t * f t))
    _ = star (fourierCoeff f (-m)) := by
          simp [fourierCoeff]

/-- Explicit Fourier expansion of a finite circle polynomial. -/
private theorem finiteCirclePoly_sum
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {r : ℝ} (_hr : 0 < r) (t : Circle) :
    finiteCirclePoly k r a t =
      ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t := by
  rw [finiteCirclePoly,
    show positiveTrigonometricPolynomial (frequencyBand 0 (d + 1)) (finiteCircleCoeff k r a) t =
      ∑ n ∈ frequencyBand 0 (d + 1), finiteCircleCoeff k r a n * fourier (n : ℤ) t by rfl]
  have hband : frequencyBand 0 (d + 1) = Finset.range (d + 1) := by
    simpa [HermiteLEAN.frequencyBand] using
      (show Finset.Icc 0 d = Finset.range (d + 1) by
        ext n
        simp [Finset.mem_Icc])
  rw [hband, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxle : (x : ℕ) ≤ d := Nat.le_of_lt_succ x.is_lt
  simp [finiteCircleCoeff, fourier_apply, hxle]

/-- Conjugating a finite circle polynomial flips its Fourier modes. -/
private theorem star_finiteCirclePoly_sum
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {r : ℝ} (hr : 0 < r) (t : Circle) :
    star (finiteCirclePoly k r a t) =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) * fourier (-(i.1 : ℤ)) t := by
  rw [finiteCirclePoly_sum (k := k) (a := a) (r := r) hr t]
  have hstar :
      star (∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t) =
        ∑ i : Fin (d + 1), star (a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t) := by
    simp
  rw [hstar]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hconj :
      (starRingEnd ℂ) ↑(AddCircle.toCircle ((i : ℕ) • t)) =
        ↑(AddCircle.toCircle (-((i : ℕ) • t))) := by
    rw [← Circle.coe_inv_eq_conj, ← AddCircle.toCircle_neg]
  simp [qkn_real, fourier_apply, hconj, mul_assoc, mul_left_comm, mul_comm]

/-- The normalized circle series is continuous at each fixed radius. -/
private lemma continuous_circleSeries_hermiteCoeff
    {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (r : ℝ) (hr : 0 < r) :
    Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) := by
  rcases hermite_series_locally_uniform (k := k) (G := G) hG with ⟨g, hg, hcontG⟩
  have hCirclePoint : Continuous (fun t : Circle => circlePoint r t) := by
    unfold circlePoint
    exact continuous_const.mul (fourier (1 : ℤ)).continuous
  have hcontGt : Continuous (fun t : Circle => G (circlePoint r t)) :=
    hcontG.comp hCirclePoint
  have hnonzero : (circleLeadingFactor k r : ℂ) ≠ 0 := by
    dsimp [circleLeadingFactor]
    exact_mod_cast
      (div_ne_zero (ne_of_gt (pow_pos hr k))
        (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0))
  have hEq :
      circleSeries k (hermiteCoeff k G) r =
        fun t : Circle =>
          (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            G (circlePoint r t) := by
    funext t
    have hfour : (fourier (k : ℤ) t : ℂ) * (fourier (-(k : ℤ)) t : ℂ) = 1 := by
      rw [← fourier_add]
      simp
    have hrepr :=
      circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
    have hcancel :
        (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            ((circleLeadingFactor k r : ℂ) * (fourier (-(k : ℤ)) t : ℂ) *
              circleSeries k (hermiteCoeff k G) r t)
          = circleSeries k (hermiteCoeff k G) r t := by
      calc
        (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            ((circleLeadingFactor k r : ℂ) * (fourier (-(k : ℤ)) t : ℂ) *
              circleSeries k (hermiteCoeff k G) r t)
            =
            ((circleLeadingFactor k r : ℂ)⁻¹ * (circleLeadingFactor k r : ℂ)) *
              ((fourier (k : ℤ) t : ℂ) * fourier (-(k : ℤ)) t : ℂ) *
                circleSeries k (hermiteCoeff k G) r t := by
                  ring_nf
        _ = circleSeries k (hermiteCoeff k G) r t := by
              have htmp :=
                congrArg
                  (fun z : ℂ =>
                    ((circleLeadingFactor k r : ℂ)⁻¹ * (circleLeadingFactor k r : ℂ)) *
                      z * circleSeries k (hermiteCoeff k G) r t)
                  hfour
              simpa [hnonzero, mul_assoc] using htmp
    calc
      circleSeries k (hermiteCoeff k G) r t
          = (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
              ((circleLeadingFactor k r : ℂ) * (fourier (-(k : ℤ)) t : ℂ) *
                circleSeries k (hermiteCoeff k G) r t) := by
                  exact hcancel.symm
      _ = (circleLeadingFactor k r : ℂ)⁻¹ * (fourier (k : ℤ) t : ℂ) *
            G (circlePoint r t) := by
            rw [hrepr]
  rw [hEq]
  have hcontFour : Continuous (fun t : Circle => (fourier (k : ℤ) t : ℂ)) :=
    (fourier (k : ℤ)).continuous
  exact (continuous_const.mul hcontFour).mul hcontGt

/-- Fourier coefficients of the mixed circle product against a finite base point. -/
private theorem fourierCoeff_circleSeries_mul_star_finiteCirclePoly
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (m : ℤ) :
    fourierCoeff (fun t : Circle =>
      circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) m =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
        fourierCoeff (circleSeries k (hermiteCoeff k G) r) (m + i.1) := by
  have hfun :
      (fun t : Circle => circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) =
        fun t : Circle =>
          ∑ i : Fin (d + 1),
            (star (a i) * (qkn k i.1 r : ℂ)) *
              (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t) := by
    funext t
    rw [star_finiteCirclePoly_sum a hr t, mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [hfun]
  have hsum :=
    fourierCoeff.sum
      (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) =>
        fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t))
      (by
        intro i hi
        have hcont :
            Continuous (fun t : Circle =>
              (star (a i) * (qkn k i.1 r : ℂ)) *
                (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) := by
          have hc : Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) :=
            continuous_circleSeries_hermiteCoeff hG r hr
          continuity
        have hcs :
            HasCompactSupport (fun t : Circle =>
              (star (a i) * (qkn k i.1 r : ℂ)) *
                (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) := by
          unfold HasCompactSupport
          exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (by
            intro x hx
            trivial)
        exact Continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) hcont hcs)
  have hsum' := congrArg (fun F => F m) hsum
  rw [show (∑ i : Fin (d + 1),
        fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) =
      (fun t : Circle =>
        ∑ i : Fin (d + 1),
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) by
      funext t
      simp [Finset.sum_apply]] at hsum'
  simp only [Finset.sum_apply] at hsum'
  rw [hsum']
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    fourierCoeff
        (fun t : Circle =>
          (star (a i) * (qkn k i.1 r : ℂ)) *
            (circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)) m
      = (star (a i) * (qkn k i.1 r : ℂ)) *
          fourierCoeff (fun t : Circle =>
            circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t) m := by
            simpa using
              (fourierCoeff.const_mul (T := T)
                (f := fun t : Circle =>
                  circleSeries k (hermiteCoeff k G) r t * fourier (-(i.1 : ℤ)) t)
                (c := star (a i) * (qkn k i.1 r : ℂ)) (n := m))
    _ = (star (a i) * (qkn k i.1 r : ℂ)) *
          fourierCoeff (circleSeries k (hermiteCoeff k G) r) (m + i.1) := by
            rw [fourierCoeff_mul_fourier]
            norm_num

/-- Positive Fourier modes of the mixed circle product are explicit coefficient sums. -/
private theorem fourierCoeff_circleSeries_mul_star_finiteCirclePoly_nat
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    fourierCoeff (fun t : Circle =>
      circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) ell =
      ∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
        (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ)) := by
  rw [fourierCoeff_circleSeries_mul_star_finiteCirclePoly a hG hr ell]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hcoeff :=
    circleSeries_fourierCoeff_hermiteCoeff
      (k := k) (G := G) hG (r := r) hr (ell + i.1)
  simpa [Int.ofNat_eq_natCast, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
    add_comm]
    using congrArg (fun z => star (a i) * (qkn k i.1 r : ℂ) * z) hcoeff

/-- The normalized circle series has no negative Fourier coefficients. -/
private lemma circleSeries_neg_fourierCoeff_eq_zero
    {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) :
    ∀ m : ℕ, fourierCoeff (circleSeries k (hermiteCoeff k G) r) (-(m + 1 : ℤ)) = 0 := by
  intro m
  let fcont : C(Circle, ℂ) :=
    ⟨circleSeries k (hermiteCoeff k G) r, continuous_circleSeries_hermiteCoeff hG r hr⟩
  let fLp := ContinuousMap.toLp (p := 2) AddCircle.haarAddCircle ℂ fcont
  let s : ℤ → ℝ := fun n => ‖fourierCoeff fLp n‖ ^ 2
  have hsummable : Summable s := by
    simpa [s, fLp] using (hasSum_sq_fourierCoeff fLp).summable
  have hsummable_nat : Summable (fun n : ℕ => s n) :=
    hsummable.comp_injective Nat.cast_injective
  have hsummable_neg : Summable (fun n : ℕ => s (-(n + 1 : ℤ))) := by
    have hneginj : Function.Injective (fun n : ℕ => (-(n + 1 : ℤ))) := by
      intro x y h
      have h' : Int.negSucc x = Int.negSucc y := by
        simpa [Int.negSucc] using h
      exact Int.negSucc.inj h'
    exact hsummable.comp_injective hneginj
  have hparseval :
      ∑' n : ℤ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    have hIntEq :
        ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle =
          circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
      unfold circleL2Sq
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toAEEqFun (μ := AddCircle.haarAddCircle) fcont] with t ht
      simp [fcont, fLp, ht]
    calc
      ∑' n : ℤ, s n = ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle := by
        simpa [s] using (tsum_sq_fourierCoeff fLp)
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := hIntEq
  have hcoeff : ∀ n : ℕ, fourierCoeff fLp n = hermiteCoeff k G n * (qkn k n r : ℂ) := by
    intro n
    calc
      fourierCoeff fLp n = fourierCoeff fcont n := fourierCoeff_toLp (f := fcont) n
      _ = hermiteCoeff k G n * (qkn k n r : ℂ) :=
          circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr n
  have hnat_eq :
      ∑' n : ℕ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    have hqabs : ∀ n : ℕ, |qkn k n r| ^ 2 = qkn k n r ^ 2 := by
      intro n
      simp
    calc
      ∑' n : ℕ, s n = ∑' n : ℕ, ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ^ 2 := by
        simp [s, hcoeff]
      _ = ∑' n : ℕ, (|qkn k n r| * ‖hermiteCoeff k G n‖) ^ 2 := by
        congr with n
        simp [mul_comm]
      _ = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * qkn k n r ^ 2 := by
        congr with n
        calc
          (|qkn k n r| * ‖hermiteCoeff k G n‖) ^ 2 =
              |qkn k n r| ^ 2 * ‖hermiteCoeff k G n‖ ^ 2 := by
                ring
          _ = qkn k n r ^ 2 * ‖hermiteCoeff k G n‖ ^ 2 := by
                rw [hqabs]
          _ = ‖hermiteCoeff k G n‖ ^ 2 * qkn k n r ^ 2 := by ring
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
        simpa [circleL2Sq] using
          (circleSeries_l2_identity_hermiteCoeff (k := k) (G := G) hG (r := r) hr).symm
  have hsplit :
      ∑' n : ℤ, s n = ∑' n : ℕ, s n + ∑' n : ℕ, s (-(n + 1 : ℤ)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tsum_of_nat_of_neg_add_one (f := s) hsummable_nat hsummable_neg)
  have hneg_sum_zero : ∑' n : ℕ, s (-(n + 1 : ℤ)) = 0 := by
    linarith [hparseval, hnat_eq, hsplit]
  have htermle : s (-(m + 1 : ℤ)) ≤ ∑' n : ℕ, s (-(n + 1 : ℤ)) := by
    exact hsummable_neg.le_tsum m (by
      intro n hn
      dsimp [s]
      positivity)
  have hsq : s (-(m + 1 : ℤ)) = 0 := by
    have hle : s (-(m + 1 : ℤ)) ≤ 0 := by
      calc
        s (-(m + 1 : ℤ)) ≤ ∑' n : ℕ, s (-(n + 1 : ℤ)) := htermle
        _ = 0 := hneg_sum_zero
    exact le_antisymm hle (by positivity)
  have hsqLp : fourierCoeff fLp (-(m + 1 : ℤ)) = 0 := by
    have hsq' : ‖fourierCoeff fLp (-(m + 1 : ℤ))‖ ^ 2 = 0 := by
      simpa [s] using hsq
    have hnorm : ‖fourierCoeff fLp (-(m + 1 : ℤ))‖ = 0 := by
      exact sq_eq_zero_iff.mp hsq'
    exact norm_eq_zero.mp hnorm
  have hsq' : fourierCoeff fcont (-(m + 1 : ℤ)) = 0 := by
    exact (fourierCoeff_toLp (f := fcont) (-(m + 1 : ℤ))).symm.trans hsqLp
  exact hsq'

/-- Positive Fourier modes of the conjugate mixed product only keep indices `i ≥ ell`. -/
private theorem fourierCoeff_star_circleSeries_mul_star_finiteCirclePoly_nat
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    fourierCoeff (fun t : Circle =>
      star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell =
      ∑ i : Fin (d + 1),
        if _h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
        else 0 := by
  calc
    fourierCoeff (fun t : Circle =>
        star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell
      = star (fourierCoeff (fun t : Circle =>
          circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) (-ell)) := by
            simpa using
              (fourierCoeff_star
                (f := fun t : Circle =>
                  circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))
                (m := (ell : ℤ)))
    _ = star
          (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
            fourierCoeff (circleSeries k (hermiteCoeff k G) r) ((-(ell : ℤ)) + i.1)) := by
          rw [fourierCoeff_circleSeries_mul_star_finiteCirclePoly (a := a) hG hr (-ell)]
    _ = ∑ i : Fin (d + 1),
          star
            (star (a i) * (qkn k i.1 r : ℂ) *
              fourierCoeff (circleSeries k (hermiteCoeff k G) r) ((-(ell : ℤ)) + i.1)) := by
          simp
    _ = ∑ i : Fin (d + 1),
          if h : ell ≤ i.1 then
            star (hermiteCoeff k G (i.1 - ell)) * a i *
              ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases h : ell ≤ i.1
          · have hidx : (-(ell : ℤ)) + i.1 = ((i.1 - ell : ℕ) : ℤ) := by omega
            rw [hidx,
              circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr (i.1 - ell)]
            simp [h, qkn_real, mul_assoc, mul_left_comm, mul_comm]
          · have hidx : (-(ell : ℤ)) + i.1 = -((ell - i.1 - 1 : ℕ) + 1 : ℤ) := by omega
            rw [hidx,
              circleSeries_neg_fourierCoeff_eq_zero
                (k := k) (G := G) hG (r := r) hr (ell - i.1 - 1)]
            simp [h]

/-- Vanishing real part forces a purely imaginary scalar multiple. -/
private theorem circleSeries_neg_fourierCoeff_eq_zero_aux
    {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ} (hr : 0 < r) :
    ∀ m : ℕ, fourierCoeff (circleSeries k (hermiteCoeff k G) r) (-(m + 1 : ℤ)) = 0 := by
  intro m
  let fcont : C(Circle, ℂ) :=
    ⟨circleSeries k (hermiteCoeff k G) r, continuous_circleSeries_hermiteCoeff hG r hr⟩
  let fLp := ContinuousMap.toLp (p := 2) AddCircle.haarAddCircle ℂ fcont
  let s : ℤ → ℝ := fun n => ‖fourierCoeff fLp n‖ ^ 2
  have hsummable : Summable s := by
    simpa [s, fLp] using (hasSum_sq_fourierCoeff fLp).summable
  have hsummable_nat : Summable (fun n : ℕ => s n) :=
    hsummable.comp_injective Nat.cast_injective
  have hsummable_neg : Summable (fun n : ℕ => s (-(n + 1 : ℤ))) := by
    have hneginj : Function.Injective (fun n : ℕ => (-(n + 1 : ℤ))) := by
      intro x y h
      have h' : Int.negSucc x = Int.negSucc y := by
        simpa [Int.negSucc] using h
      exact Int.negSucc.inj h'
    exact hsummable.comp_injective hneginj
  have hparseval :
      ∑' n : ℤ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    have hIntEq :
        ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle =
          circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
      unfold circleL2Sq
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toAEEqFun (μ := AddCircle.haarAddCircle) fcont] with t ht
      simp [fcont, fLp, ht]
    calc
      ∑' n : ℤ, s n = ∫ t : Circle, ‖fLp t‖ ^ 2 ∂AddCircle.haarAddCircle := by
        simpa [s] using (tsum_sq_fourierCoeff fLp)
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := hIntEq
  have hcoeff : ∀ n : ℕ, fourierCoeff fLp n = hermiteCoeff k G n * (qkn k n r : ℂ) := by
    intro n
    calc
      fourierCoeff fLp n = fourierCoeff fcont n := fourierCoeff_toLp (f := fcont) n
      _ = hermiteCoeff k G n * (qkn k n r : ℂ) :=
          circleSeries_fourierCoeff_hermiteCoeff (k := k) (G := G) hG (r := r) hr n
  have hnat_eq :
      ∑' n : ℕ, s n = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
    have hqabs : ∀ n : ℕ, |qkn k n r| ^ 2 = qkn k n r ^ 2 := by
      intro n
      simp
    calc
      ∑' n : ℕ, s n = ∑' n : ℕ, ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ^ 2 := by
        simp [s, hcoeff]
      _ = ∑' n : ℕ, (|qkn k n r| * ‖hermiteCoeff k G n‖) ^ 2 := by
        congr with n
        simp [mul_comm]
      _ = ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * qkn k n r ^ 2 := by
        congr with n
        calc
          (|qkn k n r| * ‖hermiteCoeff k G n‖) ^ 2 =
              |qkn k n r| ^ 2 * ‖hermiteCoeff k G n‖ ^ 2 := by
                ring
          _ = qkn k n r ^ 2 * ‖hermiteCoeff k G n‖ ^ 2 := by
                rw [hqabs]
          _ = ‖hermiteCoeff k G n‖ ^ 2 * qkn k n r ^ 2 := by ring
      _ = circleL2Sq (circleSeries k (hermiteCoeff k G) r) := by
        simpa [circleL2Sq] using
          (circleSeries_l2_identity_hermiteCoeff (k := k) (G := G) hG (r := r) hr).symm
  have hsplit :
      ∑' n : ℤ, s n = ∑' n : ℕ, s n + ∑' n : ℕ, s (-(n + 1 : ℤ)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (tsum_of_nat_of_neg_add_one (f := s) hsummable_nat hsummable_neg)
  have hneg_sum_zero : ∑' n : ℕ, s (-(n + 1 : ℤ)) = 0 := by
    linarith [hparseval, hnat_eq, hsplit]
  have htermle : s (-(m + 1 : ℤ)) ≤ ∑' n : ℕ, s (-(n + 1 : ℤ)) := by
    exact hsummable_neg.le_tsum m (by
      intro n hn
      dsimp [s]
      positivity)
  have hsq : s (-(m + 1 : ℤ)) = 0 := by
    have hle : s (-(m + 1 : ℤ)) ≤ 0 := by
      calc
        s (-(m + 1 : ℤ)) ≤ ∑' n : ℕ, s (-(n + 1 : ℤ)) := htermle
        _ = 0 := hneg_sum_zero
    exact le_antisymm hle (by positivity)
  have hsqLp : fourierCoeff fLp (-(m + 1 : ℤ)) = 0 := by
    have hsq' : ‖fourierCoeff fLp (-(m + 1 : ℤ))‖ ^ 2 = 0 := by
      simpa [s] using hsq
    have hnorm : ‖fourierCoeff fLp (-(m + 1 : ℤ))‖ = 0 := by
      exact sq_eq_zero_iff.mp hsq'
    exact norm_eq_zero.mp hnorm
  have hsq' : fourierCoeff fcont (-(m + 1 : ℤ)) = 0 := by
    exact (fourierCoeff_toLp (f := fcont) (-(m + 1 : ℤ))).symm.trans hsqLp
  exact hsq'

/-- A complex number with zero real part is anti-self-adjoint. -/
private lemma add_star_eq_zero_of_re_zero (z : ℂ) (hz : z.re = 0) : z + star z = 0 := by
  have h := Complex.add_conj z
  rw [hz] at h
  norm_num at h
  simpa using h

/-- A real scalar and a unit Fourier factor can be cancelled from a product and its conjugate. -/
private lemma scalar_factorization (c f s p : ℂ)
    (hc : star c = c) (hf : star f * f = 1) :
    (c * f * s) * star (c * f * p) = (c * c) * (s * star p) := by
  calc
    (c * f * s) * star (c * f * p)
        = c * f * s * (star p * (star f * star c)) := by
            simp [star_mul, mul_assoc]
    _ = c * f * s * (star p * (star f * c)) := by rw [hc]
    _ = c * c * (f * star f) * (s * star p) := by ring
    _ = (c * c) * (s * star p) := by
          rw [mul_comm f (star f), hf, mul_one]

/-- After cancelling the common circle factors, the product has zero real part iff it is
`x + star x = 0`. -/
private theorem circleSeries_star_finiteCirclePoly_add_star_eq_zero
    {k d : ℕ} (a : Fin (d + 1) → ℂ)
    {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0)
    {r : ℝ} (hr : 0 < r) (t : Circle) :
    circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
      star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)) = 0 := by
  let c : ℂ := circleLeadingFactor k r
  let f : ℂ := (fourier (-(k : ℤ)) t : ℂ)
  let s : ℂ := circleSeries k (hermiteCoeff k G) r t
  let p : ℂ := finiteCirclePoly k r a t
  have hGrep := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
  have hUrep := finiteHermiteSum_circle (k := k) (a := a) (r := r) hr t
  have hz : Complex.re ((c * f * s) * star (c * f * p)) = 0 := by
    simpa [c, f, s, p, hGrep, hUrep, mul_assoc] using hzero (circlePoint r t)
  have hmain : (c * f * s) * star (c * f * p) + star ((c * f * s) * star (c * f * p)) = 0 :=
    add_star_eq_zero_of_re_zero _ hz
  have hc : star c = c := by
    simp [c, circleLeadingFactor]
  have hf : star f * f = 1 := by
    have hmul : star f * f = ‖f‖ ^ 2 := by
      simpa [sq] using (RCLike.conj_mul f)
    rw [hmul, show ‖f‖ = 1 by simp [f]]
    norm_num
  have hcc : star (c * c) = c * c := by simp [hc]
  have hx : (c * f * s) * star (c * f * p) = (c * c) * (s * star p) :=
    scalar_factorization c f s p hc hf
  have hxstar : star ((c * f * s) * star (c * f * p)) = (c * c) * star (s * star p) := by
    rw [hx, star_mul, hcc]
    simp [mul_comm, mul_assoc]
  have hfact : (c * c) * (s * star p) + (c * c) * star (s * star p) = 0 := by
    have hrew : star ((c * c) * (s * star p)) = (c * c) * star (s * star p) := by
      rw [star_mul, hcc]
      simp [mul_comm, mul_assoc]
    rw [hx, hrew] at hmain
    exact hmain
  have hcpos : 0 < (((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) : ℝ) := by
    positivity
  have hcnz : (c * c) ≠ 0 := by
    have hcz : c ≠ 0 := by
      have hnonzero : (((r ^ k) / Real.sqrt ((Nat.factorial k : ℕ) : ℝ)) : ℝ) ≠ 0 := hcpos.ne'
      simpa [c, circleLeadingFactor] using hnonzero
    exact mul_ne_zero hcz hcz
  have hsplit : (c * c) * ((s * star p) + star (s * star p)) = 0 := by
    simpa [mul_add, mul_assoc] using hfact
  exact (mul_eq_zero.mp hsplit).resolve_left hcnz

/-- The positive `ell`-th Fourier mode of the real-part identity gives an explicit sum relation. -/
private theorem positive_mode_mixed_eq_zero
    {k d : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ}
    (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0)
    {r : ℝ} (hr : 0 < r) (ell : ℕ) :
    (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
      (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ))) +
    (∑ i : Fin (d + 1),
      if _h : ell ≤ i.1 then
        star (hermiteCoeff k G (i.1 - ell)) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ))
      else 0) = 0 := by
  have hfun :
      (fun t : Circle =>
        circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
          star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) =
      fun _ : Circle => (0 : ℂ) := by
    funext t
    simpa using circleSeries_star_finiteCirclePoly_add_star_eq_zero
      (k := k) (d := d) (a := a) hG hzero hr t
  have hcoeff0 :
      fourierCoeff
        (fun t : Circle =>
          circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
            star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)))
        ell = 0 := by
    rw [hfun]
    simp [fourierCoeff]
  let f : Circle → ℂ :=
    fun t : Circle => circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)
  let g : Circle → ℂ := fun t : Circle => star (f t)
  have hp : Continuous (fun t : Circle => finiteCirclePoly k r a t) := by
    let F : Circle → ℂ :=
      fun t : Circle => ∑ i : Fin (d + 1), a i * (qkn k i.1 r : ℂ) * fourier (i.1 : ℤ) t
    have hF : Continuous F := by
      classical
      refine continuous_finsetSum _ ?_
      intro i hi
      continuity
    have hEq : (fun t : Circle => finiteCirclePoly k r a t) = F := by
      funext t
      simp [F, finiteCirclePoly_sum (k := k) (a := a) (r := r) hr t]
    rw [hEq]
    exact hF
  have hf : Integrable f AddCircle.haarAddCircle := by
    have hcont : Continuous f := by
      have hc : Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) :=
        continuous_circleSeries_hermiteCoeff hG r hr
      exact hc.mul hp.star
    have hcs : HasCompactSupport f := by
      unfold HasCompactSupport
      exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (by
        intro x hx
        trivial)
    exact Continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) hcont hcs
  have hg : Integrable g AddCircle.haarAddCircle := by
    have hcont : Continuous g := by
      have hc' : Continuous (fun t : Circle => circleSeries k (hermiteCoeff k G) r t) :=
        continuous_circleSeries_hermiteCoeff hG r hr
      have hc : Continuous f := hc'.mul hp.star
      exact hc.star
    have hcs : HasCompactSupport g := by
      unfold HasCompactSupport
      exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (by
        intro x hx
        trivial)
    exact Continuous.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) hcont hcs
  have hadd :
      fourierCoeff
          (fun t : Circle =>
            circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t) +
              star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))) ell =
        fourierCoeff
            (fun t : Circle =>
              circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t))
            ell +
          fourierCoeff
            (fun t : Circle =>
              star (circleSeries k (hermiteCoeff k G) r t * star (finiteCirclePoly k r a t)))
            ell := by
    have haddfun := fourierCoeff.add (T := T) (f := f) (g := g) hf hg
    exact congrArg (fun F => F ell) haddfun
  rw [hadd,
    fourierCoeff_circleSeries_mul_star_finiteCirclePoly_nat (a := a) hG hr ell,
    fourierCoeff_star_circleSeries_mul_star_finiteCirclePoly_nat (a := a) hG hr ell] at hcoeff0
  simpa using hcoeff0

/-- The leading positive-mode sum converges to the contribution of the top index `i = d`. -/
private theorem positive_mode_main_sum_tendsto
    {k d ell : ℕ} (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ} :
    Filter.Tendsto
      (fun r : ℝ =>
        ∑ i : Fin (d + 1),
          star (a i) * hermiteCoeff k G (ell + i.1) *
            (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
      Filter.atTop
      (𝓝 (star (topCoeff a) * hermiteCoeff k G (d + ell))) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ i : Fin (d + 1),
            star (a i) * hermiteCoeff k G (ell + i.1) *
              (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
        Filter.atTop
        (𝓝
          (∑ i : Fin (d + 1), if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        star (a i) * hermiteCoeff k G (ell + i.1) *
          (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ))))
      (a := fun i : Fin (d + 1) =>
        if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0) ?_
    intro i hi
    by_cases hid : i.1 = d
    · have hratio : Filter.Tendsto
          (fun r : ℝ =>
            ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (ell + d) r : ℂ) / (qkn k (d + ell) r : ℂ)))
          Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [Nat.add_comm] using (qkn_self_ratio_tendsto_one (k := k) (d := d)).mul
          (qkn_self_ratio_tendsto_one (k := k) (d := d + ell))
      have hi_eq : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hid
      subst hi_eq
      simpa [topCoeff, Nat.add_comm, mul_assoc] using
        ((tendsto_const_nhds :
          Filter.Tendsto
            (fun _ : ℝ => star (a ⟨d, Nat.lt_succ_self d⟩) * hermiteCoeff k G (d + ell))
            Filter.atTop _).mul hratio)
    · have hi_lt : i.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hid
      have hless : ell + i.1 < d + ell := by omega
      have hratio : Filter.Tendsto
          (fun r : ℝ =>
            ((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ)))
          Filter.atTop (𝓝 (0 : ℂ)) := by
        simpa using (qkn_ratio_tendsto_zero (k := k) (i := i.1) (d := d) hi_lt).mul
          (qkn_ratio_tendsto_zero (k := k) (i := ell + i.1) (d := d + ell) hless)
      simpa [hid, mul_assoc] using
        ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => star (a i) * hermiteCoeff k G (ell + i.1))
            Filter.atTop _).mul hratio)
  have htop :
      (∑ i : Fin (d + 1), if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0) =
        star (topCoeff a) * hermiteCoeff k G (d + ell) := by
    let i0 : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
    have hsum0 :
        (∑ i : Fin (d + 1), if i = i0 then star (a i) * hermiteCoeff k G (d + ell) else 0) =
          star (a i0) * hermiteCoeff k G (d + ell) := by
      simp [i0]
    calc
      (∑ i : Fin (d + 1), if i.1 = d then star (a i) * hermiteCoeff k G (d + ell) else 0)
        = ∑ i : Fin (d + 1), if i = i0 then star (a i) * hermiteCoeff k G (d + ell) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hi0 : i = i0
            · have hid0 : i.1 = d := by
                simp [hi0, i0]
              simp [hi0, i0]
            · have hne : i.1 ≠ d := by
                intro hid
                apply hi0
                exact Fin.ext hid
              simp [hi0, hne]
      _ = star (a i0) * hermiteCoeff k G (d + ell) := hsum0
      _ = star (topCoeff a) * hermiteCoeff k G (d + ell) := by
            simp [topCoeff, i0]
  rw [htop] at hsum
  exact hsum

/-- The lower-index correction terms in the positive-mode relation vanish after normalization. -/
private theorem positive_mode_error_sum_tendsto_zero
    {k d ell : ℕ} (hEll : 1 ≤ ell) (a : Fin (d + 1) → ℂ) {G : ℂ → ℂ} :
    Filter.Tendsto
      (fun r : ℝ =>
        ∑ i : Fin (d + 1),
        if _h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
      Filter.atTop (𝓝 (0 : ℂ)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ =>
          ∑ i : Fin (d + 1),
            if h : ell ≤ i.1 then
              star (hermiteCoeff k G (i.1 - ell)) * a i *
                (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
                  ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
            else 0)
        Filter.atTop (𝓝 (∑ _ : Fin (d + 1), (0 : ℂ))) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        if h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
      (a := fun _ : Fin (d + 1) => (0 : ℂ)) ?_
    intro i hi
    by_cases h : ell ≤ i.1
    · have hi_lt : i.1 < d + ell := by omega
      have hlt : i.1 - ell < d := by
        have hi_le : i.1 ≤ d := Nat.le_of_lt_succ i.2
        omega
      have hratio : Filter.Tendsto
          (fun r : ℝ =>
            ((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
          Filter.atTop (𝓝 (0 : ℂ)) := by
        simpa using (qkn_ratio_tendsto_zero (k := k) (i := i.1) (d := d + ell) hi_lt).mul
          (qkn_ratio_tendsto_zero (k := k) (i := i.1 - ell) (d := d) hlt)
      simpa [h, mul_assoc] using
        ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => star (hermiteCoeff k G (i.1 - ell)) * a i)
            Filter.atTop _).mul hratio)
    · simp [h]
  simpa using hsum

/-- Positive Fourier modes force all coefficients above the top degree to vanish. -/
private theorem high_coeff_vanish
    {k d ell : ℕ} (hEll : 1 ≤ ell) (a : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0)
    {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hzero : ∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0) :
    hermiteCoeff k G (d + ell) = 0 := by
  let F : ℝ → ℂ :=
    fun r : ℝ =>
      (∑ i : Fin (d + 1),
        star (a i) * hermiteCoeff k G (ell + i.1) *
          (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
            ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ)))) +
      (∑ i : Fin (d + 1),
        if h : ell ≤ i.1 then
          star (hermiteCoeff k G (i.1 - ell)) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
              ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
        else 0)
  have hFtendsto :
      Filter.Tendsto F Filter.atTop (𝓝 (star (topCoeff a) * hermiteCoeff k G (d + ell))) := by
    have hsum : Filter.Tendsto
        (fun r : ℝ =>
          (∑ i : Fin (d + 1),
            star (a i) * hermiteCoeff k G (ell + i.1) *
              (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (ell + i.1) r : ℂ) / (qkn k (d + ell) r : ℂ)))) +
          (∑ i : Fin (d + 1),
            if h : ell ≤ i.1 then
              star (hermiteCoeff k G (i.1 - ell)) * a i *
                (((qkn k i.1 r : ℂ) / (qkn k (d + ell) r : ℂ)) *
                  ((qkn k (i.1 - ell) r : ℂ) / (qkn k d r : ℂ)))
            else 0))
        Filter.atTop (𝓝 (star (topCoeff a) * hermiteCoeff k G (d + ell) + 0)) := by
      simpa using
        (positive_mode_main_sum_tendsto (k := k) (d := d) (ell := ell) (a := a) (G := G)).add
        (positive_mode_error_sum_tendsto_zero (k := k) (d := d) (ell := ell) hEll (a := a) (G := G))
    simpa [F] using hsum
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k (d + ell)
  have hFzero : F =ᶠ[Filter.atTop] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
    have hd : (qkn k d r : ℂ) ≠ 0 := by
      exact_mod_cast hd_nonzero r hrD
    have hn : (qkn k (d + ell) r : ℂ) ≠ 0 := by
      exact_mod_cast hn_nonzero r hrN
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_trans hRd hrD)
    have hraw := positive_mode_mixed_eq_zero (k := k) (d := d) (a := a) hG hzero (r := r) hr ell
    have hEq : ((qkn k d r : ℂ) * (qkn k (d + ell) r : ℂ)) * F r = 0 := by
      have hNorm :
          ((qkn k d r : ℂ) * (qkn k (d + ell) r : ℂ)) * F r =
            (∑ i : Fin (d + 1), star (a i) * (qkn k i.1 r : ℂ) *
              (hermiteCoeff k G (ell + i.1) * (qkn k (ell + i.1) r : ℂ))) +
            (∑ i : Fin (d + 1), if h : ell ≤ i.1 then
              star (hermiteCoeff k G (i.1 - ell)) * a i *
                ((qkn k i.1 r : ℂ) * (qkn k (i.1 - ell) r : ℂ)) else 0) := by
        dsimp [F]
        rw [mul_add]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [hd, hn]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases h : ell ≤ i.1
          · simp [h]
            field_simp [hd, hn]
          · simp [h]
      exact hNorm.trans hraw
    have hdenom : ((qkn k d r : ℂ) * (qkn k (d + ell) r : ℂ)) ≠ 0 := mul_ne_zero hd hn
    exact (mul_eq_zero.mp hEq).resolve_left hdenom
  have hzero_tendsto : Filter.Tendsto F Filter.atTop (𝓝 (0 : ℂ)) := by
    simpa using hFzero.tendsto
  have hlim : star (topCoeff a) * hermiteCoeff k G (d + ell) = 0 := by
    simpa [zero_add] using
      (tendsto_nhds_unique (f := F) (l := Filter.atTop) hFtendsto hzero_tendsto)
  have htopstar : star (topCoeff a) ≠ 0 := by
    exact mt star_eq_zero.mp hTop
  exact (mul_eq_zero.mp hlim).resolve_left htopstar

/-- For finite Hermite sums, the positive mode `d - n` isolates the mixed top/lower coefficient
relation. -/
private def finitePositiveModeMainSum
    (k d : ℕ) (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) (r : ℝ) : ℂ :=
  ∑ i : Fin (d + 1),
    star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
      (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
        ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ)))

/-- The main normalized positive-mode sum converges to the top/lower coefficient interaction. -/
private theorem finite_positive_mode_main_tendsto
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
    Filter.Tendsto
      (fun r : ℝ => finitePositiveModeMainSum k d a b n r)
      Filter.atTop (𝓝 (star (a n) * b ⟨d, Nat.lt_succ_self d⟩)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ => finitePositiveModeMainSum k d a b n r)
        Filter.atTop
        (𝓝
          (∑ i : Fin (d + 1),
            if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
          (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
            ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ))))
      (a := fun i : Fin (d + 1) =>
        if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0) ?_
    intro i hi
    by_cases hi_eq : i.1 = n.1
    · have hi_eq' : i = n := Fin.ext hi_eq
      subst i
      have hidx : d - n.1 + n.1 = d := by omega
      have hlt : d - n.1 + n.1 < d + 1 := by omega
      have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k n.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
                ((qkn k (d - n.1 + n.1) r : ℂ) / (qkn k d r : ℂ)))
            Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [hidx] using (qkn_self_ratio_tendsto_one (k := k) (d := n.1)).mul
          (qkn_self_ratio_tendsto_one (k := k) (d := d))
      simpa [finitePositiveModeMainSum, hidx, hlt, mul_assoc] using
        ((tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℝ => star (a n) * b ⟨d, Nat.lt_succ_self d⟩) Filter.atTop _).mul hratio)
    · by_cases hi_lt : i.1 < n.1
      · have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
                ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ)))
            Filter.atTop (𝓝 (0 : ℂ)) := by
          have hless1 : i.1 < n.1 := hi_lt
          have hless2 : d - n.1 + i.1 < d := by omega
          simpa using (qkn_ratio_tendsto_zero (k := k) (i := i.1) (d := n.1) hless1).mul
            (qkn_ratio_tendsto_zero (k := k) (i := d - n.1 + i.1) (d := d) hless2)
        have hlt : d - n.1 + i.1 < d + 1 := by omega
        simpa [hi_eq, hi_lt, hlt, finitePositiveModeMainSum, mul_assoc] using
          ((tendsto_const_nhds : Filter.Tendsto
            (fun _ : ℝ => star (a i) * b ⟨d - n.1 + i.1, by omega⟩) Filter.atTop _).mul hratio)
      · have hconst0 :
            Filter.Tendsto
              (fun r : ℝ =>
                star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
                  (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
                    ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ))))
              Filter.atTop (𝓝 (0 : ℂ)) := by
          have hEq : (fun r : ℝ =>
              star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
                (((qkn k i.1 r : ℂ) / (qkn k n.1 r : ℂ)) *
                  ((qkn k (d - n.1 + i.1) r : ℂ) / (qkn k d r : ℂ)))) = fun _ : ℝ => (0 : ℂ) := by
            funext r
            have hnot : ¬ d - n.1 + i.1 < d + 1 := by
              have hi_gt : n.1 < i.1 := by omega
              omega
            simp [hnot]
          rw [hEq]
          exact tendsto_const_nhds
        simpa [hi_eq, finitePositiveModeMainSum] using hconst0
  have htop :
      (∑ i : Fin (d + 1), if i.1 = n.1 then star (a i) * b ⟨d, Nat.lt_succ_self d⟩ else 0) =
        star (a n) * b ⟨d, Nat.lt_succ_self d⟩ := by
    classical
    rw [Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      have hne : i.1 ≠ n.1 := by
        intro h
        apply hin
        exact Fin.ext h
      simp [hne]
    · intro hn
      exact False.elim (hn (Finset.mem_univ n))
  rw [htop] at hsum
  exact hsum

private def finitePositiveModeErrorSum
    (k d : ℕ) (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) (r : ℝ) : ℂ :=
  ∑ i : Fin (d + 1),
    if h : d - n.1 ≤ i.1 then
      star (b ⟨i.1 - (d - n.1), by
        have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
        omega⟩) * a i *
        (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
          ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
    else 0

/-- The normalized correction terms in the finite positive-mode relation vanish except at the top
index. -/
private theorem finite_positive_mode_error_tendsto
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) :
    Filter.Tendsto
      (fun r : ℝ => finitePositiveModeErrorSum k d a b n r)
      Filter.atTop (𝓝 (star (b n) * a ⟨d, Nat.lt_succ_self d⟩)) := by
  have hsum :
      Filter.Tendsto
        (fun r : ℝ => finitePositiveModeErrorSum k d a b n r)
        Filter.atTop
        (𝓝 (∑ i : Fin (d + 1), if i.1 = d then star (b n) * a i else 0)) := by
    refine tendsto_finsetSum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i : Fin (d + 1) => fun r : ℝ =>
        if h : d - n.1 ≤ i.1 then
          star (b ⟨i.1 - (d - n.1), by
            have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i *
            (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
              ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
        else 0)
      (a := fun i : Fin (d + 1) => if i.1 = d then star (b n) * a i else 0) ?_
    intro i hi
    by_cases hi_eq : i.1 = d
    · have hi_eq' : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hi_eq
      subst i
      have hidx : d - (d - n.1) = n.1 := by omega
      have hge : d - n.1 ≤ d := by omega
      have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k d r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (d - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
            Filter.atTop (𝓝 (1 : ℂ)) := by
        simpa [hidx] using (qkn_self_ratio_tendsto_one (k := k) (d := d)).mul
          (qkn_self_ratio_tendsto_one (k := k) (d := n.1))
      simpa [finitePositiveModeErrorSum, hidx, hge, mul_assoc] using
        ((tendsto_const_nhds : Filter.Tendsto
          (fun _ : ℝ => star (b n) * a ⟨d, Nat.lt_succ_self d⟩) Filter.atTop _).mul hratio)
    · have hi_lt : i.1 < d := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hi_eq
      by_cases hi_ge : d - n.1 ≤ i.1
      · have hratio :
          Filter.Tendsto
            (fun r : ℝ =>
              ((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))
            Filter.atTop (𝓝 (0 : ℂ)) := by
          have hless : i.1 < d := hi_lt
          have hle2 : i.1 - (d - n.1) ≤ n.1 := by omega
          have hneq2 : i.1 - (d - n.1) ≠ n.1 := by omega
          have hless2 : i.1 - (d - n.1) < n.1 := lt_of_le_of_ne hle2 hneq2
          simpa using (qkn_ratio_tendsto_zero (k := k) (i := i.1) (d := d) hless).mul
            (qkn_ratio_tendsto_zero (k := k) (i := i.1 - (d - n.1)) (d := n.1) hless2)
        simpa [hi_eq, hi_ge, finitePositiveModeErrorSum, mul_assoc] using
          ((tendsto_const_nhds : Filter.Tendsto
            (fun _ : ℝ => star (b ⟨i.1 - (d - n.1), by
              have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
              omega⟩) * a i) Filter.atTop _).mul hratio)
      · simp [hi_eq, hi_ge]
  have htop :
      (∑ i : Fin (d + 1), if i.1 = d then star (b n) * a i else 0) =
        star (b n) * a ⟨d, Nat.lt_succ_self d⟩ := by
    let i0 : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro i hi hi0
      have hne : i.1 ≠ d := by
        intro h
        apply hi0
        exact Fin.ext h
      simp [hne]
    · intro hi0
      exact False.elim (hi0 (Finset.mem_univ i0))
  rw [htop] at hsum
  exact hsum

private theorem finite_positive_mode_main_raw
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ} :
    (∑ i : Fin (d + 1),
      star (a i) * (qkn k i.1 r : ℂ) *
        (hermiteCoeff k (finiteHermiteSum k b) (d - n.1 + i.1) * (qkn k (d - n.1 + i.1) r : ℂ))) =
    ∑ i : Fin (d + 1),
      star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
        ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hidx : d - n.1 + i.1 < d + 1
  · simp [hermiteCoeff_finiteHermiteSum, hidx, mul_assoc, mul_left_comm, mul_comm]
  · simp [hermiteCoeff_finiteHermiteSum, hidx, mul_left_comm, mul_comm]

private theorem finite_positive_mode_error_raw
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ} :
    (∑ i : Fin (d + 1),
      if _h : d - n.1 ≤ i.1 then
        star (hermiteCoeff k (finiteHermiteSum k b) (i.1 - (d - n.1))) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
      else 0) =
    ∑ i : Fin (d + 1),
      if h : d - n.1 ≤ i.1 then
        star (b ⟨i.1 - (d - n.1), by
          have _hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
          omega⟩) * a i *
          ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
      else 0 := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : d - n.1 ≤ i.1
  · have hlt : i.1 - (d - n.1) < d + 1 := by
      have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
      omega
    simp [h, hermiteCoeff_finiteHermiteSum, hlt]
  · simp [h]

private theorem finitePositiveModeMainSum_mul_den
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ}
    (hd : (qkn k d r : ℂ) ≠ 0) (hn : (qkn k n.1 r : ℂ) ≠ 0) :
    ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeMainSum k d a b n r =
      ∑ i : Fin (d + 1),
        star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
          ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ)) := by
  unfold finitePositiveModeMainSum
  rw [mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hidx : d - n.1 + i.1 < d + 1
  · simp [hidx, mul_assoc, mul_comm]
    field_simp [hd, hn]
  · simp [hidx]

private theorem finitePositiveModeErrorSum_mul_den
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1)) {r : ℝ}
    (hd : (qkn k d r : ℂ) ≠ 0) (hn : (qkn k n.1 r : ℂ) ≠ 0) :
    ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeErrorSum k d a b n r =
      ∑ i : Fin (d + 1),
        if h : d - n.1 ≤ i.1 then
          star (b ⟨i.1 - (d - n.1), by
            have _hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i *
            ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
        else 0 := by
  unfold finitePositiveModeErrorSum
  rw [mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : d - n.1 ≤ i.1
  · have hcalc :
        ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) *
            (star (b ⟨i.1 - (d - n.1), by
              have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
              omega⟩) * a i *
              (((qkn k i.1 r : ℂ) / (qkn k d r : ℂ)) *
                ((qkn k (i.1 - (d - n.1)) r : ℂ) / (qkn k n.1 r : ℂ)))) =
          star (b ⟨i.1 - (d - n.1), by
            have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
            omega⟩) * a i * ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ)) := by
      field_simp [hd, hn]
    simpa [h, mul_assoc, mul_left_comm, mul_comm] using hcalc
  · simp [h]

private theorem finite_positive_mode_relation
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (n : Fin (d + 1))
    (hzero : ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0) :
    star (a n) * b ⟨d, Nat.lt_succ_self d⟩ + star (b n) * a ⟨d, Nat.lt_succ_self d⟩ = 0 := by
  let ell : ℕ := d - n.1
  let F : ℝ → ℂ :=
    fun r : ℝ => finitePositiveModeMainSum k d a b n r + finitePositiveModeErrorSum k d a b n r
  have hFtendsto : Filter.Tendsto F Filter.atTop
      (𝓝 (star (a n) * b ⟨d, Nat.lt_succ_self d⟩ + star (b n) * a ⟨d, Nat.lt_succ_self d⟩)) := by
    have hsum := (finite_positive_mode_main_tendsto (k := k) (d := d) a b n).add
      (finite_positive_mode_error_tendsto (k := k) (d := d) a b n)
    simpa [F] using hsum
  obtain ⟨Rd, hRd, hd_nonzero⟩ := qkn_eventually_nonzero k d
  obtain ⟨Rn, hRn, hn_nonzero⟩ := qkn_eventually_nonzero k n.1
  have hFzero : F =ᶠ[Filter.atTop] fun _ : ℝ => (0 : ℂ) := by
    have hG : finiteHermiteSum k b ∈ Hk k := finiteHermiteSum_mem_Hk k b
    filter_upwards [Filter.eventually_ge_atTop Rd, Filter.eventually_ge_atTop Rn] with r hrD hrN
    have hd : (qkn k d r : ℂ) ≠ 0 := by
      exact_mod_cast hd_nonzero r hrD
    have hn : (qkn k n.1 r : ℂ) ≠ 0 := by
      exact_mod_cast hn_nonzero r hrN
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_trans hRd hrD)
    have hraw := positive_mode_mixed_eq_zero (k := k) (d := d) (a := a) (G := finiteHermiteSum k b)
      hG hzero (r := r) hr ell
    have hraw0 :
        (∑ i : Fin (d + 1),
          star (a i) * (qkn k i.1 r : ℂ) *
            (hermiteCoeff k (finiteHermiteSum k b) (d - n.1 + i.1) *
              (qkn k (d - n.1 + i.1) r : ℂ))) +
        (∑ i : Fin (d + 1),
          if h : d - n.1 ≤ i.1 then
            star (hermiteCoeff k (finiteHermiteSum k b) (i.1 - (d - n.1))) * a i *
              ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
          else 0) = 0 := by
      simpa [ell] using hraw
    rw [finite_positive_mode_main_raw (k := k) (d := d) (a := a) (b := b) n (r := r),
      finite_positive_mode_error_raw (k := k) (d := d) (a := a) (b := b) n (r := r)] at hraw0
    have hEq : ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * F r = 0 := by
      calc
        ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * F r
            = ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeMainSum k d a b n r +
                ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) * finitePositiveModeErrorSum k d a b n r := by
                  dsimp [F]
                  ring
        _ = (∑ i : Fin (d + 1),
              star (a i) * (if h : d - n.1 + i.1 < d + 1 then b ⟨d - n.1 + i.1, h⟩ else 0) *
                ((qkn k i.1 r : ℂ) * (qkn k (d - n.1 + i.1) r : ℂ))) +
              (∑ i : Fin (d + 1),
                if h : d - n.1 ≤ i.1 then
                  star (b ⟨i.1 - (d - n.1), by
                    have hi' : i.1 ≤ d := Nat.le_of_lt_succ i.2
                    omega⟩) * a i * ((qkn k i.1 r : ℂ) * (qkn k (i.1 - (d - n.1)) r : ℂ))
                else 0) := by
                  rw [finitePositiveModeMainSum_mul_den (k := k) (d := d) (a := a) (b := b) n hd hn,
                    finitePositiveModeErrorSum_mul_den (k := k) (d := d) (a := a) (b := b) n hd hn]
        _ = 0 := hraw0
    have hdenom : ((qkn k d r : ℂ) * (qkn k n.1 r : ℂ)) ≠ 0 := mul_ne_zero hd hn
    exact (mul_eq_zero.mp hEq).resolve_left hdenom
  have hzero_tendsto : Filter.Tendsto F Filter.atTop (𝓝 (0 : ℂ)) := by
    simpa using hFzero.tendsto
  simpa [zero_add] using (tendsto_nhds_unique (f := F) (l := Filter.atTop) hFtendsto hzero_tendsto)

/-- Vanishing real part against a finite Hermite sum forces a purely imaginary scalar multiple. -/
private theorem finite_real_part_rigidity
    {k d : ℕ} (a b : Fin (d + 1) → ℂ) (hTop : topCoeff a ≠ 0)
    (hzero : ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0) :
    ∃ c : ℝ, finiteHermiteSum k b = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) := by
  let top : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
  let lam : ℂ := b top / a top
  have htopA : a top ≠ 0 := by
    simpa [top, topCoeff] using hTop
  have htop_eq : b top = lam * a top := by
    dsimp [lam]
    field_simp [htopA]
  have hrel : ∀ n : Fin (d + 1), star (a n) * b top + star (b n) * a top = 0 := by
    intro n
    simpa [top] using finite_positive_mode_relation (k := k) a b n hzero
  have hlam_add_star : lam + star lam = 0 := by
    have hrel_top := hrel top
    have hsq_nonzero : star (a top) * a top ≠ 0 := by
      exact mul_ne_zero (mt star_eq_zero.mp htopA) htopA
    have htmp : (lam + star lam) * (star (a top) * a top) = 0 := by
      calc
        (lam + star lam) * (star (a top) * a top)
            = star (a top) * (lam * a top) + star (lam * a top) * a top := by
                rw [star_mul]
                ring_nf
        _ = star (a top) * b top + star (b top) * a top := by rw [htop_eq]
        _ = 0 := hrel_top
    exact (mul_eq_zero.mp htmp).resolve_right hsq_nonzero
  have hlam_re : lam.re = 0 := by
    have hre := congrArg Complex.re hlam_add_star
    simp at hre
    linarith
  obtain ⟨c, hc⟩ := exists_I_mul_of_re_eq_zero lam hlam_re
  have hstar_lam : star lam = -lam := by
    simp [hc, mul_comm]
  have hb_coeff : ∀ n : Fin (d + 1), b n = lam * a n := by
    intro n
    have hrel' : star (b n) + lam * star (a n) = 0 := by
      have htmp' : (star (b n) + lam * star (a n)) * a top = 0 := by
        calc
          (star (b n) + lam * star (a n)) * a top
              = star (a n) * (lam * a top) + star (b n) * a top := by
                  ring_nf
          _ = star (a n) * b top + star (b n) * a top := by rw [htop_eq]
          _ = 0 := hrel n
      exact (mul_eq_zero.mp htmp').resolve_right htopA
    have hstar := congrArg star hrel'
    have htmp : b n + star lam * a n = 0 := by
      simpa [star_add, star_mul, mul_assoc, mul_left_comm, mul_comm] using hstar
    have htmp' : b n = -(star lam * a n) := by
      exact eq_neg_iff_add_eq_zero.mpr htmp
    calc
      b n = -(star lam * a n) := htmp'
      _ = lam * a n := by simp [hstar_lam, neg_mul, neg_neg]
  refine ⟨c, ?_⟩
  funext z
  calc
    finiteHermiteSum k b z
        = ∑ n : Fin (d + 1), (lam * a n) * Phi k n.1 z := by
            simp [finiteHermiteSum, hb_coeff]
    _ = lam * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ = (Complex.I * (c : ℂ)) * ∑ n : Fin (d + 1), a n * Phi k n.1 z := by
          simp [hc]
    _ = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) z := by
          simp [finiteHermiteSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
            mul_left_comm]

theorem real_part_rigidity :
    ∀ {k d : ℕ}
      (a : Fin (d + 1) → ℂ)
      (_hTop : topCoeff a ≠ 0)
      {G : ℂ → ℂ},
        G ∈ Hk k →
          (∀ z : ℂ, Complex.re (G z * star (finiteHermiteSum k a z)) = 0) →
            ∃ c : ℝ, G = ((Complex.I * (c : ℂ)) • finiteHermiteSum k a) := by
  intro k d a hTop G hG hzero
  let b : Fin (d + 1) → ℂ := fun n => hermiteCoeff k G n.1
  have hvanish : ∀ n : ℕ, d < n → hermiteCoeff k G n = 0 := by
    intro n hn
    have hEll : 1 ≤ n - d := by omega
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hn)] using
      (high_coeff_vanish (k := k) (d := d) (ell := n - d) (a := a) hEll hTop hG hzero)
  have htrunc : G = truncate k d G := by
    apply truncate_unique (k := k) (J := d) (G := G) (H := G) hG
    intro n
    by_cases hn : n < d + 1
    · simp [hn]
    · have hnd : d < n := by omega
      simp [hn, hvanish n hnd]
  have hG_eq : G = finiteHermiteSum k b := by
    calc
      G = truncate k d G := htrunc
      _ = finiteHermiteSum k b := by
            simp [truncate_eq_finiteHermiteSum, b]
  have hzero' :
      ∀ z : ℂ, Complex.re (finiteHermiteSum k b z * star (finiteHermiteSum k a z)) = 0 := by
    intro z
    simpa [hG_eq] using hzero z
  obtain ⟨c, hfin⟩ := finite_real_part_rigidity (k := k) (d := d) (a := a) (b := b) hTop hzero'
  refine ⟨c, ?_⟩
  simpa [hG_eq] using hfin

end HermitekLEAN
