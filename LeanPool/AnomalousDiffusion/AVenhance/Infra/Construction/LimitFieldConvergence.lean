/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitSeries

/-! Pointwise construction of the limit stream from the explicit stream-regularity
increment estimate, with the tail bound used in §5.4. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Construction

/-- The geometric constant in the tail estimate, depending only on the
exponent and scale parameter. -/
def streamLimitTailConstant {β : ℝ} (I : Ingredients β) : ℝ :=
  10 / (1 - (I.Λ : ℝ) ^ (-β))

theorem LimitFieldConvergence.streamLimitTailConstant_pos {β : ℝ} (I : Ingredients β) :
    0 < streamLimitTailConstant I := by
  have hq : (I.Λ : ℝ) ^ (-β) < 1 :=
    inverse_lambda_rpow_lt_one I (by linarith [I.one_lt_beta])
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-β) := by linarith
  exact div_pos (by norm_num) hden

theorem LimitFieldConvergence.streamLimitTailConstant_ge_one {β : ℝ} (I : Ingredients β) :
    1 ≤ streamLimitTailConstant I := by
  have hq : (I.Λ : ℝ) ^ (-β) < 1 :=
    inverse_lambda_rpow_lt_one I (by linarith [I.one_lt_beta])
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-β) := by linarith
  have hq0 : 0 ≤ (I.Λ : ℝ) ^ (-β) := by positivity
  rw [streamLimitTailConstant]
  apply (le_div_iff₀ hden).2
  linarith

theorem LimitFieldConvergence.streamLimitTailConstant_le_eleven {β : ℝ} (I : Ingredients β) :
    streamLimitTailConstant I ≤ 11 := by
  have hΛnat : 2 ^ 7 ≤ I.Λ := I.two_pow_seven_le
  norm_num at hΛnat
  have hΛ : 128 ≤ (I.Λ : ℝ) := by exact_mod_cast hΛnat
  have hLam1 : 1 ≤ (I.Λ : ℝ) := by linarith
  have hβ : 1 ≤ β := le_of_lt I.one_lt_beta
  have hpow : (I.Λ : ℝ) ≤ (I.Λ : ℝ) ^ β := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLam1 hβ
  have hq : (I.Λ : ℝ) ^ (-β) ≤ 1 / 128 := by
    rw [Real.rpow_neg (by positivity)]
    have hp : 0 < (I.Λ : ℝ) ^ β := Real.rpow_pos_of_pos (by linarith) β
    have hinv := (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 128)).2
      (le_trans hΛ hpow)
    simpa [one_div] using hinv
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-β) := by
    have hq' : (I.Λ : ℝ) ^ (-β) < 1 :=
      inverse_lambda_rpow_lt_one I (by linarith [I.one_lt_beta])
    linarith
  rw [streamLimitTailConstant]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem LimitFieldConvergence.streamIncrement_telescope {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (m k : ℕ) (t : ℝ) (x : Vec 2) :
    Φ (m + k) t x - Φ m t x =
      ∑ j ∈ Finset.range k, (Φ (m + j + 1) t x - Φ (m + j) t x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_succ]
      rw [← ih]
      ring

/-- A finite tail of the sequence is bounded by the infinite geometric tail
from its first omitted scale. -/
theorem streamIncrement_tail_le {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) (m k : ℕ) (t : ℝ) (x : Vec 2) :
    |Φ (m + k) t x - Φ m t x| ≤
      streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β := by
  rw [LimitFieldConvergence.streamIncrement_telescope m k t x]
  calc
    |∑ j ∈ Finset.range k, (Φ (m + j + 1) t x - Φ (m + j) t x)| ≤
        ∑ j ∈ Finset.range k,
          |Φ (m + j + 1) t x - Φ (m + j) t x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ 10 * ∑ j ∈ Finset.range k,
          epsilon β I.Λ (m + j + 1) ^ β := by
      calc
        _ ≤ ∑ j ∈ Finset.range k,
              (10 * epsilon β I.Λ (m + j + 1) ^ β) :=
          Finset.sum_le_sum fun j hj => by
            have hinc := streamIncrement_norm_le hseq hreg
              (m := m + j + 1) (by omega) t x
            simpa [Real.norm_eq_abs, Nat.add_sub_cancel] using hinc
        _ = 10 * ∑ j ∈ Finset.range k,
              epsilon β I.Λ (m + j + 1) ^ β := by rw [Finset.mul_sum]
    _ ≤ streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β := by
      have hsum := epsilon_rpow_sum_bound I (by linarith [I.one_lt_beta]) (m + 1) k
      have hscale : (∑ j ∈ Finset.range k,
          epsilon β I.Λ ((m + 1) + j) ^ β) ≤
            epsilon β I.Λ (m + 1) ^ β /
              (1 - (I.Λ : ℝ) ^ (-β)) := by
        simpa [Nat.add_assoc] using hsum
      have h10 := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 10)
      simpa [streamLimitTailConstant, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h10

/-- The pointwise sequence of stream fields is Cauchy, uniformly in the
space-time point. -/
theorem streamField_cauchySeq {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) (t : ℝ) (x : Vec 2) :
    CauchySeq (fun m => Φ m t x) := by
  rw [Metric.cauchySeq_iff']
  intro r hr
  have hA : 0 < streamLimitTailConstant I := LimitFieldConvergence.streamLimitTailConstant_pos I
  have hsmall : ∀ᶠ n : ℕ in atTop,
      streamLimitTailConstant I * epsilon β I.Λ n ^ β < r := by
    have htend : Tendsto (fun n : ℕ =>
        streamLimitTailConstant I * epsilon β I.Λ n ^ β) atTop (𝓝 0) := by
      simpa [mul_comm] using
        (epsilon_rpow_tendsto_zero I (by linarith [I.one_lt_beta])).const_mul
          (streamLimitTailConstant I)
    exact htend.eventually (Iio_mem_nhds hr)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hsmall)
  refine ⟨N, ?_⟩
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have htail := streamIncrement_tail_le hseq hreg N k t x
  have hmono := epsilon_rpow_antitone (s := β) I (by linarith [I.one_lt_beta])
    (m := N) (n := N + 1) (by omega)
  have hA0 : 0 ≤ streamLimitTailConstant I := hA.le
  calc
    dist (Φ (N + k) t x) (Φ N t x) = |Φ (N + k) t x - Φ N t x| := by
      rw [dist_eq_norm, Real.norm_eq_abs]
    _ ≤ streamLimitTailConstant I * epsilon β I.Λ (N + 1) ^ β := htail
    _ ≤ streamLimitTailConstant I * epsilon β I.Λ N ^ β :=
      mul_le_mul_of_nonneg_left hmono hA0
    _ < r := hN N (le_rfl : N ≤ N)

/-- The explicit stream-regularity bounds produce a pointwise limit stream. -/
theorem exists_streamLimit {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) :
    ∃ φ : ℝ → Vec 2 → ℝ,
      ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)) := by
  let φ : ℝ → Vec 2 → ℝ := fun t x =>
    Classical.choose (cauchySeq_tendsto_of_complete (streamField_cauchySeq hseq hreg t x))
  refine ⟨φ, ?_⟩
  intro t x
  exact Classical.choose_spec
    (cauchySeq_tendsto_of_complete (streamField_cauchySeq hseq hreg t x))

/-- The pointwise limit has the geometric tail estimate from (e.def.b). -/
theorem streamLimit_tail_bound {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (m : ℕ) (t : ℝ) (x : Vec 2) :
    |φ t x - Φ m t x| ≤
      streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β := by
  have hcont : Tendsto (fun n => |Φ n t x - Φ m t x|) atTop
      (𝓝 |φ t x - Φ m t x|) :=
    (hlim t x).sub_const (Φ m t x) |>.abs
  have hbound : ∀ᶠ n : ℕ in atTop,
      |Φ n t x - Φ m t x| ≤
        streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β := by
    have hbound' : ∀ n : ℕ, m ≤ n →
        |Φ n t x - Φ m t x| ≤
          streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β := by
      intro n hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
      subst n
      exact streamIncrement_tail_le hseq hreg m k t x
    exact eventually_atTop.2 ⟨m, hbound'⟩
  exact le_of_tendsto hcont hbound

/-- A uniform version of the pointwise tail estimate, with a constant that
does not depend on the chosen Ingredients object. -/
theorem streamLimit_tail_bound_uniform {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (m : ℕ) (t : ℝ) (x : Vec 2) :
    |φ t x - Φ m t x| ≤ 11 * epsilon β I.Λ (m + 1) ^ β := by
  calc
    |φ t x - Φ m t x| ≤
        streamLimitTailConstant I * epsilon β I.Λ (m + 1) ^ β :=
      streamLimit_tail_bound hseq hreg hlim m t x
    _ ≤ 11 * epsilon β I.Λ (m + 1) ^ β :=
      mul_le_mul_of_nonneg_right (LimitFieldConvergence.streamLimitTailConstant_le_eleven I)
        (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le (m := m + 1)).le _)

end AVenhance.Infra.Construction
