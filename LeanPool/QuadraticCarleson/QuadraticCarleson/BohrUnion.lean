/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.BohrIntersection

/-!
# Unions of consecutive dyadic Bohr sets

The proposition following Lemma `l:bohrintersection` is proved first for an
exact block of `B` consecutive dyadic frequencies, starting at exponent `M`,
and then for arbitrary real endpoints and lengths by rounding inward. The
displayed logarithmic interval is interpreted in base two, as required by
the later identities `floor(log(λ/A)/N) = k` and `2^(Nk)A ≤ λ < 2^(N(k+1))A`.

The explicit thresholds are `M ≥ 2`, `B ≥ 1`, and `0 < c < 1/10`; this radius
range includes the paper's `c < 10^(-10)`. The absolute lower-bound
constants are `1/768` for integer blocks and `1/1536` for real windows. The
uniform consequence quantifies an arbitrary fixed `a > 0` with `Bc ≥ a`.
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace QuadraticCarleson

/-- The finite block of localized Bohr sets with dyadic frequencies
`2^M, 2^(M+1), …, 2^(M+B-1)`. -/
def dyadicBohrUnion (M B : ℕ) (c : ℝ) : Set ℝ :=
  ⋃ j ∈ Finset.range B, bohrSet (2 ^ (M + j)) c

theorem measurableSet_dyadicBohrUnion (M B : ℕ) (c : ℝ) :
    MeasurableSet (dyadicBohrUnion M B c) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_bohrSet _ _

theorem dyadicBohrUnion_subset_Ico (M B : ℕ) (c : ℝ) :
    dyadicBohrUnion M B c ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  apply iUnion₂_subset
  intro j _
  exact bohrSet_subset_Ico _ _

/-- The finite-family second-moment inequality, obtained by applying
Cauchy–Schwarz to the sum of indicators and the indicator of their union. -/
theorem sum_measure_sq_le_union_mul_sum_inter {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (E : ι → Set α)
    (hE : ∀ i, MeasurableSet (E i)) (hfin : ∀ i, μ (E i) ≠ ∞) :
    (∑ i ∈ s, μ.real (E i)) ^ 2 ≤
      μ.real (⋃ i ∈ s, E i) * ∑ i ∈ s, ∑ j ∈ s, μ.real (E i ∩ E j) := by
  classical
  let U := ⋃ i ∈ s, E i
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion s fun i _ => hE i
  have hUf : μ U ≠ ∞ := by
    apply ne_of_lt
    exact (measure_biUnion_finset_le s E).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ => (hfin i).lt_top)
  let e : ι → Lp ℝ 2 μ := fun i => indicatorConstLp 2 (hE i) (hfin i) (1 : ℝ)
  let u : Lp ℝ 2 μ := indicatorConstLp 2 hUm hUf (1 : ℝ)
  let f : Lp ℝ 2 μ := ∑ i ∈ s, e i
  have heu : ∀ i ∈ s, ⟪e i, u⟫_ℝ = μ.real (E i) := by
    intro i hi
    rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (hE i) hUm (hfin i) hUf]
    congr 1
    apply inter_eq_left.mpr
    exact subset_iUnion₂_of_subset i hi Subset.rfl
  have hfu : ⟪f, u⟫_ℝ = ∑ i ∈ s, μ.real (E i) := by
    simp only [f, sum_inner]
    exact Finset.sum_congr rfl heu
  have hff : ⟪f, f⟫_ℝ = ∑ i ∈ s, ∑ j ∈ s, μ.real (E i ∩ E j) := by
    simp only [f, sum_inner, inner_sum, e,
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [inter_comm]
  have huu : ⟪u, u⟫_ℝ = μ.real U := by
    simp only [u, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, inter_self]
  have hcs := real_inner_mul_inner_self_le f u
  rw [hfu, hff, huu] at hcs
  simpa only [pow_two, mul_comm] using hcs

/-- The ratio form of the finite-family second-moment lower bound displayed
in the paper. A zero denominator is harmless under Lean's division convention. -/
theorem sum_measure_sq_div_sum_inter_le_union {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (E : ι → Set α)
    (hE : ∀ i, MeasurableSet (E i)) (hfin : ∀ i, μ (E i) ≠ ∞) :
    (∑ i ∈ s, μ.real (E i)) ^ 2 /
      (∑ i ∈ s, ∑ j ∈ s, μ.real (E i ∩ E j)) ≤ μ.real (⋃ i ∈ s, E i) := by
  let Q := ∑ i ∈ s, ∑ j ∈ s, μ.real (E i ∩ E j)
  change (∑ i ∈ s, μ.real (E i)) ^ 2 / Q ≤ _
  have hQ : 0 ≤ Q := by
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg fun _ _ => measureReal_nonneg
  rcases eq_or_lt_of_le hQ with hQzero | hQpos
  · rw [← hQzero, div_zero]
    exact measureReal_nonneg
  · apply (div_le_iff₀ hQpos).mpr
    exact sum_measure_sq_le_union_mul_sum_inter μ s E hE hfin

private def bohrCell (n j : ℕ) (c : ℝ) : Set ℝ :=
  Ico (((n : ℝ) + j) / (4 * n)) (((n : ℝ) + j + c) / (4 * n))

private theorem bohrCell_subset {n j : ℕ} {c : ℝ}
    (hn : 0 < n) (hj : j < n) (hc : c ≤ 1) :
    bohrCell n j c ⊆ bohrSet (4 * n) c := by
  intro x hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 4 * n := by positivity
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx₁ := (div_le_iff₀ hden).mp hx.1
  have hx₂ := (lt_div_iff₀ hden).mp hx.2
  constructor
  · constructor <;> nlinarith
  · have hfract : Int.fract ((4 * n : ℕ) * x : ℝ) =
        4 * (n : ℝ) * x - ((n : ℝ) + j) := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by nlinarith, by nlinarith, ⟨(n + j : ℕ), ?_⟩⟩
      push_cast
      ring
    change min (Int.fract ((4 * n : ℕ) * x : ℝ))
      (1 - Int.fract ((4 * n : ℕ) * x : ℝ)) ≤ c
    rw [hfract]
    exact (min_le_left _ _).trans (by nlinarith)

/-- An explicit single-set lower bound at frequencies divisible by four.
Only the right-hand half of each Bohr interval is needed. -/
theorem bohrSet_four_mul_volume_real_ge {n : ℕ} {c : ℝ}
    (hn : 0 < n) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    c / 4 ≤ volume.real (bohrSet (4 * n) c) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 4 * n := by positivity
  have hdisj : PairwiseDisjoint (↑(Finset.range n) : Set ℕ) (fun j => bohrCell n j c) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi₁ := (div_le_iff₀ hden).mp hxi.1
    have hi₂ := (lt_div_iff₀ hden).mp hxi.2
    have hj₁ := (div_le_iff₀ hden).mp hxj.1
    have hj₂ := (lt_div_iff₀ hden).mp hxj.2
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      linarith
    · have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      linarith
  have hcell : ∀ j, volume.real (bohrCell n j c) = c / (4 * n) := by
    intro j
    dsimp [bohrCell]
    rw [Real.volume_real_Ico_of_le]
    · ring
    · exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hsub : (⋃ j ∈ Finset.range n, bohrCell n j c) ⊆ bohrSet (4 * n) c := by
    apply iUnion₂_subset
    intro j hj
    exact bohrCell_subset hn (Finset.mem_range.mp hj) hc
  calc
    c / 4 = (n : ℝ) * (c / (4 * n)) := by field_simp
    _ = ∑ j ∈ Finset.range n, volume.real (bohrCell n j c) := by simp [hcell]
    _ = volume.real (⋃ j ∈ Finset.range n, bohrCell n j c) := by
      symm
      exact measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_Ico)
        (fun _ _ => by simp [bohrCell])
    _ ≤ volume.real (bohrSet (4 * n) c) :=
      measureReal_mono hsub
        (measure_ne_top_of_subset (bohrSet_subset_Ico (4 * n) c) (by simp))

/-- A uniform lower bound for every dyadic frequency at least four. -/
theorem bohrSet_dyadic_volume_real_ge {a : ℕ} {c : ℝ}
    (ha : 2 ≤ a) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    c / 4 ≤ volume.real (bohrSet (2 ^ a) c) := by
  have heq : 2 ^ a = 4 * 2 ^ (a - 2) := by
    conv_lhs => rw [show a = 2 + (a - 2) by omega]
    rw [pow_add]
    norm_num
  rw [heq]
  exact bohrSet_four_mul_volume_real_ge (by positivity) hc0 hc

private noncomputable def dyadicGcdRatio (M i j : ℕ) : ℝ :=
  (Nat.gcd (2 ^ (M + i)) (2 ^ (M + j)) : ℝ) /
    (max (2 ^ (M + i)) (2 ^ (M + j)) : ℕ)

private theorem dyadicGcdRatio_comm (M i j : ℕ) :
    dyadicGcdRatio M i j = dyadicGcdRatio M j i := by
  simp only [dyadicGcdRatio, Nat.gcd_comm, max_comm]

private theorem dyadicGcdRatio_of_le (M : ℕ) {i j : ℕ} (hij : i ≤ j) :
    dyadicGcdRatio M i j = (2 : ℝ) ^ i / 2 ^ j := by
  have hdvd : 2 ^ (M + i) ∣ 2 ^ (M + j) := pow_dvd_pow 2 (by omega)
  have hle : 2 ^ (M + i) ≤ 2 ^ (M + j) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [dyadicGcdRatio, Nat.gcd_eq_left hdvd, max_eq_right hle]
  push_cast
  simp only [pow_add]
  field_simp

private theorem dyadicGcdRatio_self (M i : ℕ) : dyadicGcdRatio M i i = 1 := by
  rw [dyadicGcdRatio_of_le M le_rfl]
  exact div_self (by positivity)

private theorem sum_two_pow_le (B : ℕ) :
    ∑ i ∈ Finset.range B, (2 : ℝ) ^ i ≤ 2 ^ B := by
  induction B with
  | zero => norm_num
  | succ B ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

private theorem sum_dyadicGcdRatio_last_le (M B : ℕ) :
    ∑ i ∈ Finset.range B, dyadicGcdRatio M i B ≤ 1 := by
  have heq : (∑ i ∈ Finset.range B, dyadicGcdRatio M i B) =
      (∑ i ∈ Finset.range B, (2 : ℝ) ^ i) / 2 ^ B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    exact dyadicGcdRatio_of_le M (Finset.mem_range.mp hi).le
  rw [heq, div_le_one (by positivity)]
  exact sum_two_pow_le B

/-- The dyadic gcd correction has only linear total mass in the block length. -/
theorem sum_dyadic_gcd_ratio_le (M B : ℕ) :
    (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
      (Nat.gcd (2 ^ (M + i)) (2 ^ (M + j)) : ℝ) /
        (max (2 ^ (M + i)) (2 ^ (M + j)) : ℕ)) ≤ 3 * B := by
  change (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, dyadicGcdRatio M i j) ≤ 3 * B
  induction B with
  | zero => simp
  | succ B ih =>
    have hr := sum_dyadicGcdRatio_last_le M B
    have hc : ∑ i ∈ Finset.range B, dyadicGcdRatio M B i ≤ 1 := by
      simpa only [dyadicGcdRatio_comm M B] using hr
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib,
      dyadicGcdRatio_self, Nat.cast_add, Nat.cast_one]
    linarith

/-- The quantitative second-moment bound used in the paper's Bohr-union proof. -/
theorem dyadicBohr_second_moment_le (M B : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < 1 / 10) :
    (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
      volume.real (bohrSet (2 ^ (M + i)) c ∩ bohrSet (2 ^ (M + j)) c)) ≤
      48 * (((B : ℝ) * c) ^ 2 + (B : ℝ) * c) := by
  have hgcd := sum_dyadic_gcd_ratio_le M B
  have hbound : (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
      volume.real (bohrSet (2 ^ (M + i)) c ∩ bohrSet (2 ^ (M + j)) c)) ≤
      ∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
        16 * (c ^ 2 + c * dyadicGcdRatio M i j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simpa only [dyadicGcdRatio, mul_div_assoc] using
      bohrSet_inter_volume_real_le (k := 2 ^ (M + i)) (m := 2 ^ (M + j))
        (by positivity) (by positivity) hc0 hc
  have hsum : (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
        16 * (c ^ 2 + c * dyadicGcdRatio M i j)) =
      16 * (((B : ℝ) * c) ^ 2 + c *
        ∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, dyadicGcdRatio M i j) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hsum] at hbound
  change (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, dyadicGcdRatio M i j) ≤ 3 * B at hgcd
  nlinarith [mul_le_mul_of_nonneg_left hgcd hc0, sq_nonneg ((B : ℝ) * c)]

/-- The paper's Bohr-union lower bound, with threshold `M ≥ 2` and absolute
constant `1/768`. The theorem holds on the larger radius range `0 < c < 1/10`. -/
theorem dyadicBohrUnion_volume_real_ge {M B : ℕ} {c : ℝ}
    (hM : 2 ≤ M) (hB : 0 < B) (hc0 : 0 < c) (hc : c < 1 / 10) :
    ((B : ℝ) * c) ^ 2 / (768 * (((B : ℝ) * c) ^ 2 + (B : ℝ) * c)) ≤
      volume.real (dyadicBohrUnion M B c) := by
  let t : ℝ := B * c
  have ht : 0 < t := by dsimp [t]; positivity
  let S : ℝ := ∑ i ∈ Finset.range B, volume.real (bohrSet (2 ^ (M + i)) c)
  let Q : ℝ := ∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B,
    volume.real (bohrSet (2 ^ (M + i)) c ∩ bohrSet (2 ^ (M + j)) c)
  let V : ℝ := volume.real (dyadicBohrUnion M B c)
  have hV : 0 ≤ V := measureReal_nonneg
  have hS : t / 4 ≤ S := by
    calc
      t / 4 = ∑ _i ∈ Finset.range B, c / 4 := by simp [t]; ring
      _ ≤ S := by
        apply Finset.sum_le_sum
        intro i hi
        exact bohrSet_dyadic_volume_real_ge (by omega) hc0.le (by linarith)
  have hS0 : 0 ≤ S := (by positivity : 0 ≤ t / 4).trans hS
  have hQ : Q ≤ 48 * (t ^ 2 + t) := dyadicBohr_second_moment_le M B hc0.le hc
  have hcs : S ^ 2 ≤ V * Q :=
    sum_measure_sq_le_union_mul_sum_inter volume (Finset.range B)
      (fun i => bohrSet (2 ^ (M + i)) c)
      (fun i => measurableSet_bohrSet _ _)
      (fun i => measure_ne_top_of_subset (bohrSet_subset_Ico _ _) (by simp))
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hQ hV)
  change t ^ 2 / (768 * (t ^ 2 + t)) ≤ V
  apply (div_le_iff₀ (by positivity : 0 < 768 * (t ^ 2 + t))).mpr
  nlinarith [sq_nonneg (S - t / 4)]

/-- Explicit meaning of the paper's uniform lower bound: if `Bc ≥ a > 0`,
the measure is at least `a / (768 (a+1))`, independently of `M,B,c`. -/
theorem dyadicBohrUnion_volume_real_ge_uniform {M B : ℕ} {c a : ℝ}
    (hM : 2 ≤ M) (hB : 0 < B) (ha : 0 < a)
    (hac : a ≤ (B : ℝ) * c) (hc : c < 1 / 10) :
    a / (768 * (a + 1)) ≤ volume.real (dyadicBohrUnion M B c) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hc0 : 0 < c := by nlinarith
  have ht : 0 < (B : ℝ) * c := mul_pos hB' hc0
  calc
    a / (768 * (a + 1)) ≤
        ((B : ℝ) * c) ^ 2 / (768 * (((B : ℝ) * c) ^ 2 + (B : ℝ) * c)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hac)]
    _ ≤ volume.real (dyadicBohrUnion M B c) := dyadicBohrUnion_volume_real_ge hM hB hc0 hc

/-- In particular, a radius at least the reciprocal of the block length
gives the absolute lower bound `1/1536`. -/
theorem dyadicBohrUnion_volume_real_ge_of_inv_le {M B : ℕ} {c : ℝ}
    (hM : 2 ≤ M) (hB : 0 < B) (hcB : (B : ℝ)⁻¹ ≤ c) (hc : c < 1 / 10) :
    (1 : ℝ) / 1536 ≤ volume.real (dyadicBohrUnion M B c) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hBc : (1 : ℝ) ≤ (B : ℝ) * c := by
    have h := mul_le_mul_of_nonneg_left hcB hB'.le
    simpa [ne_of_gt hB'] using h
  have h := dyadicBohrUnion_volume_real_ge_uniform hM hB (by norm_num : (0 : ℝ) < 1) hBc hc
  norm_num at h
  exact h

/-- The real-endpoint logarithmic window in the paper, expressed using the
dyadic exponent: `M ≤ log₂(2^n) < M+B`. -/
def dyadicBohrLogUnion (M B c : ℝ) : Set ℝ :=
  ⋃ n : ℕ, ⋃ (_ : M ≤ (n : ℝ) ∧ (n : ℝ) < M + B), bohrSet (2 ^ n) c

theorem measurableSet_dyadicBohrLogUnion (M B c : ℝ) :
    MeasurableSet (dyadicBohrLogUnion M B c) := by
  apply MeasurableSet.iUnion
  intro n
  exact MeasurableSet.iUnion fun _ => measurableSet_bohrSet _ _

/-- The exponent-window definition is exactly the paper's base-two
logarithmic condition, with its positive-natural convention on exponents. -/
theorem mem_dyadicBohrLogUnion_iff {M B c x : ℝ} (hM : 0 < M) :
    x ∈ dyadicBohrLogUnion M B c ↔
      ∃ n : ℕ, 0 < n ∧ Real.logb 2 (2 ^ n : ℝ) ∈ Ico M (M + B) ∧
        x ∈ bohrSet (2 ^ n) c := by
  have hlog : ∀ n : ℕ, Real.logb 2 (2 ^ n : ℝ) = n := by
    intro n
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  constructor
  · intro hx
    obtain ⟨n, hn, hx⟩ := mem_iUnion₂.mp hx
    have hnpos : 0 < n := by exact_mod_cast hM.trans_le hn.1
    exact ⟨n, hnpos, by simpa only [hlog, Set.mem_Ico] using hn, hx⟩
  · rintro ⟨n, hn, hlogn, hx⟩
    exact mem_iUnion₂.mpr ⟨n, by simpa only [hlog, Set.mem_Ico] using hlogn, hx⟩

theorem dyadicBohrLogUnion_subset_Ico (M B c : ℝ) :
    dyadicBohrLogUnion M B c ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  apply iUnion₂_subset
  intro n _
  exact bohrSet_subset_Ico _ _

/-- An integer block inside an arbitrary real logarithmic window. -/
theorem dyadicBohrUnion_ceil_floor_subset {M B c : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) :
    dyadicBohrUnion ⌈M⌉₊ ⌊B⌋₊ c ⊆ dyadicBohrLogUnion M B c := by
  intro x hx
  obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
  have hj' : (j : ℝ) + 1 ≤ (⌊B⌋₊ : ℕ) := by exact_mod_cast Finset.mem_range.mp hj
  have hlow := Nat.le_ceil M
  have hupp := Nat.ceil_lt_add_one hM
  have hfloor := Nat.floor_le hB
  apply mem_iUnion₂.mpr
  refine ⟨⌈M⌉₊ + j, ?_, hx⟩
  push_cast
  constructor
  · linarith [Nat.cast_nonneg (α := ℝ) j]
  · linarith

/-- The Bohr-union proposition for real logarithmic endpoints and lengths.
Rounding the endpoints costs at most a factor of two in the absolute constant. -/
theorem dyadicBohrLogUnion_volume_real_ge {M B c : ℝ}
    (hM : 2 ≤ M) (hB : 1 ≤ B) (hc0 : 0 < c) (hc : c < 1 / 10) :
    (B * c) ^ 2 / (1536 * ((B * c) ^ 2 + B * c)) ≤
      volume.real (dyadicBohrLogUnion M B c) := by
  have hM0 : 0 ≤ M := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hL : 2 ≤ ⌈M⌉₊ := by
    exact_mod_cast (hM.trans (Nat.le_ceil M))
  have hN : 0 < ⌊B⌋₊ := Nat.floor_pos.mpr hB
  have hN1 : (1 : ℝ) ≤ (⌊B⌋₊ : ℕ) := by exact_mod_cast hN
  have hhalf : B / 2 ≤ (⌊B⌋₊ : ℕ) := by linarith [Nat.lt_floor_add_one B]
  have ht : 0 < B * c := mul_pos (by linarith) hc0
  have hac : B * c / 2 ≤ (⌊B⌋₊ : ℕ) * c := by
    nlinarith [mul_le_mul_of_nonneg_right hhalf hc0.le]
  have hblock := dyadicBohrUnion_volume_real_ge_uniform hL hN
    (by positivity : 0 < B * c / 2) hac hc
  have hmono : volume.real (dyadicBohrUnion ⌈M⌉₊ ⌊B⌋₊ c) ≤
      volume.real (dyadicBohrLogUnion M B c) :=
    measureReal_mono (dyadicBohrUnion_ceil_floor_subset hM0 hB0)
      (measure_ne_top_of_subset (dyadicBohrLogUnion_subset_Ico M B c) (by simp))
  calc
    (B * c) ^ 2 / (1536 * ((B * c) ^ 2 + B * c)) ≤
        (B * c / 2) / (768 * (B * c / 2 + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_pos ht (sq_pos_of_pos ht)]
    _ ≤ volume.real (dyadicBohrUnion ⌈M⌉₊ ⌊B⌋₊ c) := hblock
    _ ≤ volume.real (dyadicBohrLogUnion M B c) := hmono

/-- The uniform version for real logarithmic windows, valid with any fixed
positive lower bound `a` for the product `Bc`. -/
theorem dyadicBohrLogUnion_volume_real_ge_uniform {M B c a : ℝ}
    (hM : 2 ≤ M) (hB : 1 ≤ B) (ha : 0 < a)
    (hac : a ≤ B * c) (hc : c < 1 / 10) :
    a / (1536 * (a + 1)) ≤ volume.real (dyadicBohrLogUnion M B c) := by
  have hB' : 0 < B := by linarith
  have hc0 : 0 < c := by nlinarith
  have ht : 0 < B * c := mul_pos hB' hc0
  calc
    a / (1536 * (a + 1)) ≤
        (B * c) ^ 2 / (1536 * ((B * c) ^ 2 + B * c)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hac)]
    _ ≤ volume.real (dyadicBohrLogUnion M B c) :=
      dyadicBohrLogUnion_volume_real_ge hM hB hc0 hc

/-- The real-window lower bound in the extended nonnegative real codomain
of Lebesgue measure. -/
theorem dyadicBohrLogUnion_volume_ge {M B c : ℝ}
    (hM : 2 ≤ M) (hB : 1 ≤ B) (hc0 : 0 < c) (hc : c < 1 / 10) :
    ENNReal.ofReal ((B * c) ^ 2 / (1536 * ((B * c) ^ 2 + B * c))) ≤
      volume (dyadicBohrLogUnion M B c) := by
  have hfinite : volume (dyadicBohrLogUnion M B c) ≠ ∞ :=
    measure_ne_top_of_subset (dyadicBohrLogUnion_subset_Ico M B c) (by simp)
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact dyadicBohrLogUnion_volume_real_ge hM hB hc0 hc

end QuadraticCarleson
