/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
/-
The code in namespace `Codex` was machine generated.
-/
module

public import LeanPool.Superorthogonality.LeanSuperorthogonality.Defs

import LeanPool.Superorthogonality.LeanSuperorthogonality.PointwiseEstimate

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*}

variable {r : ℕ}

namespace Codex

private abbrev pointwiseFamily (f : ι → α → ℂ) (r : ℕ) (x : α) :
    Fin (2 * r) → ι → ℂ :=
  fun i j ↦ if i < r then f j x else star (f j x)

omit [MeasurableSpace α] in
private lemma summable_norm_pointwiseFamily [Finite ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    ∀ i : Fin (2 * r), Summable fun j : ι ↦ ‖pointwiseFamily f r x i j‖ := by
  letI := Fintype.ofFinite ι
  intro i
  exact Summable.of_finite

omit [MeasurableSpace α] in
private lemma pointwise_estimate_conjugated [Finite ι] (f : ι → α → ℂ)
    (hr : 1 ≤ r) (x : α) :
    ‖Q (pointwiseFamily f r x) - ∏ i, s (pointwiseFamily f r x i)‖ₑ ≤
      (((2 * r)! - 1 : ENNReal) * (B (k := 2 * r) (by omega) (pointwiseFamily f r x)) ^ 2 *
        (max (A (k := 2 * r) (by omega) (pointwiseFamily f r x))
          (B (k := 2 * r) (by omega) (pointwiseFamily f r x))) ^ (2 * r - 2)) := by
  exact pointwise_estimate (k := 2 * r) (by omega) (pointwiseFamily f r x)
    (summable_norm_pointwiseFamily f r x)

omit [MeasurableSpace α] in
private lemma tsum_fintype_apply [Fintype ι] (f : ι → α → ℂ) (x : α) :
    (∑' j, f j) x = ∑ j : ι, f j x := by
  simp [tsum_fintype]

omit [MeasurableSpace α] in
private lemma s_pointwiseFamily_eq [Finite ι] (f : ι → α → ℂ) (r : ℕ) (x : α)
    (i : Fin (2 * r)) :
    ‖s (pointwiseFamily f r x i)‖ = ‖(∑' j, f j) x‖ := by
  letI := Fintype.ofFinite ι
  by_cases hi : i < r
  · simp [s, pointwiseFamily, hi, tsum_fintype_apply]
  · have hstar :
        (∑ j : ι, (starRingEnd ℂ) (f j x)) = (starRingEnd ℂ) (∑ j : ι, f j x) := by
      exact (map_sum (starRingEnd ℂ) (fun j : ι ↦ f j x) Finset.univ).symm
    have hs :
        s (pointwiseFamily f r x i) = (starRingEnd ℂ) (∑ j : ι, f j x) := by
      rw [s, tsum_fintype]
      simp only [pointwiseFamily, hi, ↓reduceIte]
      exact hstar
    rw [hs]
    simpa [tsum_fintype_apply] using norm_star (∑ j : ι, f j x)

omit [MeasurableSpace α] in
private lemma A_pointwiseFamily [Finite ι] (f : ι → α → ℂ) (hr : 1 ≤ r) (x : α) :
    A (k := 2 * r) (by omega) (pointwiseFamily f r x) = ‖(∑' j, f j) x‖ₑ := by
  letI := Fintype.ofFinite ι
  classical
  unfold A
  let T : Finset ℝ := Finset.univ.image fun i ↦ ‖s (pointwiseFamily f r x i)‖
  rw [← ofReal_norm]
  change ENNReal.ofReal (T.max' _) = ENNReal.ofReal ‖(∑' j, f j) x‖
  congr 1
  apply le_antisymm
  · rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact le_of_eq (s_pointwiseFamily_eq f r x i)
  · let i0 : Fin (2 * r) := ⟨0, by omega⟩
    calc
      ‖(∑' j, f j) x‖ = ‖s (pointwiseFamily f r x i0)‖ := by
        rw [s_pointwiseFamily_eq]
      _ ≤ T.max' _ := by
        have hmem : ‖s (pointwiseFamily f r x i0)‖ ∈ T := by
          change ‖s (pointwiseFamily f r x i0)‖ ∈
            (Finset.univ.image fun i : Fin (2 * r) ↦ ‖s (pointwiseFamily f r x i)‖)
          exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
        exact Finset.le_max' T _ hmem

private lemma eLpNorm_count_two_fintype [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] (a : ι → ℂ) :
    eLpNorm a 2 (Measure.count : Measure ι) =
      ENNReal.ofReal ((∑ j : ι, ‖a j‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [lintegral_count, tsum_fintype]
  have hsum_nonneg : 0 ≤ ∑ j : ι, ‖a j‖ ^ 2 := by
    exact Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖a j‖
  have hsum :
      (∑ j : ι, ‖a j‖ₑ ^ (2 : ENNReal).toReal) =
        ENNReal.ofReal (∑ j : ι, ‖a j‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (a j))
        (by norm_num : 0 ≤ (2 : ENNReal).toReal)]
      congr 1
      norm_num
    · intro j hj
      exact sq_nonneg ‖a j‖
  rw [hsum]
  rw [show 1 / (2 : ENNReal).toReal = (2 : ℝ)⁻¹ by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg hsum_nonneg (by norm_num : 0 ≤ (2 : ℝ)⁻¹)]

omit [MeasurableSpace α] in
private lemma sqfct_fintype [Fintype ι] (f : ι → α → ℂ) (x : α) :
    sqfct f x = ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
  simp [sqfct, tsum_fintype]

omit [MeasurableSpace α] in
private lemma B_pointwiseFamily [Finite ι] (f : ι → α → ℂ) (hr : 1 ≤ r) (x : α) :
    B (k := 2 * r) (by omega) (pointwiseFamily f r x) = ENNReal.ofReal (sqfct f x) := by
  letI := Fintype.ofFinite ι
  letI : MeasurableSpace ι := ⊤
  letI : MeasureSpace ι := { volume := Measure.count }
  haveI : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  unfold B
  rw [sqfct_fintype]
  let T : Finset ENNReal :=
    Finset.univ.image fun i ↦ eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι)
  have hcoord (i : Fin (2 * r)) :
      eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι) =
        ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
    by_cases hi : i < r
    · have hfun : pointwiseFamily f r x i = fun j : ι ↦ f j x := by
        funext j
        simp [pointwiseFamily, hi]
      rw [hfun]
      exact eLpNorm_count_two_fintype (a := fun j : ι ↦ f j x)
    · have hfun : pointwiseFamily f r x i = fun j : ι ↦ star (f j x) := by
        funext j
        simp [pointwiseFamily, hi]
      rw [hfun]
      simpa using eLpNorm_count_two_fintype (a := fun j : ι ↦ star (f j x))
  change T.max' _ = ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹)
  apply le_antisymm
  · rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact le_of_eq (hcoord i)
  · let i0 : Fin (2 * r) := ⟨0, by omega⟩
    calc
      ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹)
          = eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) := by
        rw [hcoord]
      _ ≤ T.max' _ := by
        have hmem :
            eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) ∈ T := by
          change eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) ∈
            (Finset.univ.image fun i : Fin (2 * r) ↦
              eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι))
          exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
        exact Finset.le_max' T _ hmem

omit [MeasurableSpace α] in
private lemma enorm_prod_s_pointwiseFamily [Finite ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    ‖∏ i : Fin (2 * r), s (pointwiseFamily f r x i)‖ₑ =
      ‖(∑' j, f j) x‖ₑ ^ (2 * r) := by
  letI := Fintype.ofFinite ι
  rw [← ofReal_norm, norm_prod]
  have hprod :
      (∏ i : Fin (2 * r), ‖s (pointwiseFamily f r x i)‖) =
        ‖(∑' j, f j) x‖ ^ (2 * r) := by
    simp_rw [s_pointwiseFamily_eq f r x]
    simp
  rw [hprod, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

omit [MeasurableSpace α] in
private lemma s_pointwiseFamily_eq_ite [Finite ι] (f : ι → α → ℂ) (r : ℕ) (x : α)
    (i : Fin (2 * r)) :
    s (pointwiseFamily f r x i) =
      if i < r then (∑' j, f j) x else star ((∑' j, f j) x) := by
  letI := Fintype.ofFinite ι
  by_cases hi : i < r
  · simp [s, pointwiseFamily, hi, tsum_fintype_apply]
  · have hstar :
        (∑ j : ι, (starRingEnd ℂ) (f j x)) = (starRingEnd ℂ) (∑ j : ι, f j x) := by
      exact (map_sum (starRingEnd ℂ) (fun j : ι ↦ f j x) Finset.univ).symm
    rw [if_neg hi]
    calc
      s (pointwiseFamily f r x i) = ∑ j : ι, (starRingEnd ℂ) (f j x) := by
        simp [s, pointwiseFamily, hi, tsum_fintype]
      _ = (starRingEnd ℂ) (∑ j : ι, f j x) := hstar
      _ = star ((∑' j, f j) x) := by
        rw [tsum_fintype_apply]
        rfl

omit [MeasurableSpace α] in
private lemma prod_s_pointwiseFamily_eq_ofReal_norm_pow [Finite ι] (f : ι → α → ℂ)
    (r : ℕ) (x : α) :
    (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
      (‖(∑' j, f j) x‖ ^ (2 * r) : ℂ) := by
  letI := Fintype.ofFinite ι
  let z : ℂ := (∑' j, f j) x
  have hsplit :
      (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
        (∏ n ∈ Finset.range (2 * r), if n < r then z else star z) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro n hn
    have hnlt : n < 2 * r := by simpa using hn
    rw [dif_pos hnlt]
    rw [s_pointwiseFamily_eq_ite f r x ⟨n, hnlt⟩]
  rw [hsplit]
  have htwo : 2 * r = r + r := by omega
  rw [htwo, Finset.prod_range_add]
  have hleft :
      (∏ x ∈ Finset.range r, if x < r then z else star z) = z ^ r := by
    calc
      (∏ x ∈ Finset.range r, if x < r then z else star z)
          = ∏ _x ∈ Finset.range r, z := by
            apply Finset.prod_congr rfl
            intro x hx
            rw [if_pos (Finset.mem_range.mp hx)]
      _ = z ^ r := by
            rw [Finset.prod_const, Finset.card_range]
  have hright :
      (∏ x ∈ Finset.range r, if r + x < r then z else star z) = (star z) ^ r := by
    calc
      (∏ x ∈ Finset.range r, if r + x < r then z else star z)
          = ∏ _x ∈ Finset.range r, star z := by
            apply Finset.prod_congr rfl
            intro x hx
            have hnot : ¬ r + x < r := Nat.not_lt_of_ge (Nat.le_add_right r x)
            rw [if_neg hnot]
      _ = (star z) ^ r := by
            rw [Finset.prod_const, Finset.card_range]
  rw [hleft, hright, ← mul_pow]
  rw [show z * star z = ((‖z‖ : ℝ) : ℂ) ^ 2 by simpa using Complex.mul_conj' z]
  rw [← pow_mul]
  rw [htwo]

omit [MeasurableSpace α] in
private lemma pointwise_bound_sqfct [Finite ι] (f : ι → α → ℂ)
    (hr : 1 ≤ r) (x : α) :
    ‖Q (pointwiseFamily f r x) - ∏ i, s (pointwiseFamily f r x i)‖ₑ ≤
      (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) := by
  letI := Fintype.ofFinite ι
  simpa [A_pointwiseFamily f hr x, B_pointwiseFamily f hr x] using
    pointwise_estimate_conjugated f hr x

omit [MeasurableSpace α] in
private lemma Q_pointwiseFamily_eq_finsum [Fintype ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    Q (pointwiseFamily f r x) =
      ∑ j : Fin (2 * r) → ι,
        indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j := by
  classical
  rw [Q, tsum_fintype]

private lemma integrable_Q_summand {f : ι → α → ℂ} (hf : TypeIVSuperorthogonal μ f r)
    (j : Fin (2 * r) → ι) :
    Integrable (fun x ↦ indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j) μ := by
  classical
  by_cases hdist : j ∈ set_all_distinct (2 * r)
  · simpa [Set.indicator, hdist, set_all_distinct] using hf.integrable_cprod j hdist
  · simp [hdist]

private lemma integral_Q_pointwiseFamily_eq_zero [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    ∫ x, Q (pointwiseFamily f r x) ∂μ = 0 := by
  classical
  letI := Fintype.ofFinite ι
  have hfun :
      (fun x ↦ Q (pointwiseFamily f r x)) =
        fun x ↦ ∑ j : Fin (2 * r) → ι,
          indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j := by
    funext x
    exact Q_pointwiseFamily_eq_finsum f r x
  rw [show (∫ x, Q (pointwiseFamily f r x) ∂μ) =
      ∫ x, (∑ j : Fin (2 * r) → ι,
          indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j) ∂μ by rw [hfun]]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_eq_zero
    intro j hj
    by_cases hdist : j ∈ set_all_distinct (2 * r)
    · simpa [Set.indicator, hdist, set_all_distinct] using hf.superorthogonal j hdist
    · simp [hdist]
  · intro j hj
    exact integrable_Q_summand (μ := μ) hf j

private lemma integrable_Q_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    Integrable (fun x ↦ Q (pointwiseFamily f r x)) μ := by
  classical
  letI := Fintype.ofFinite ι
  rw [show (fun x ↦ Q (pointwiseFamily f r x)) =
      fun x ↦ ∑ j : Fin (2 * r) → ι,
        indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j by
    funext x
    exact Q_pointwiseFamily_eq_finsum f r x]
  exact integrable_finsetSum Finset.univ fun j _ ↦ integrable_Q_summand (μ := μ) hf j

omit [MeasurableSpace α] in
private lemma sqfct_nonneg [Finite ι] (f : ι → α → ℂ) (x : α) :
    0 ≤ sqfct f x := by
  letI := Fintype.ofFinite ι
  rw [sqfct_fintype]
  positivity

omit [MeasurableSpace α] in
private lemma norm_le_sqfct [Finite ι] (f : ι → α → ℂ) (j : ι) (x : α) :
    ‖f j x‖ ≤ sqfct f x := by
  letI := Fintype.ofFinite ι
  rw [sqfct_fintype]
  have hsum_nonneg : 0 ≤ ∑ k : ι, ‖f k x‖ ^ 2 := by
    exact Finset.sum_nonneg fun k _ ↦ sq_nonneg ‖f k x‖
  rw [show (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by rfl]
  rw [Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hsum_nonneg (by norm_num : (0 : ℝ) < 2)]
  simpa using Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖f k x‖) (Finset.mem_univ j)

private lemma aestronglyMeasurable_tsum_finite [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    AEStronglyMeasurable (∑' j, f j) μ := by
  letI := Fintype.ofFinite ι
  rw [show (∑' j, f j) = ∑ j : ι, f j by
    funext x
    simpa only [Finset.sum_apply] using tsum_fintype_apply f x]
  exact Finset.aestronglyMeasurable_sum _ fun j _ ↦ (hf.measurable j).aestronglyMeasurable

private lemma memLp_component_of_sqfct [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) (j : ι) :
    MemLp (f j) (2 * r) μ := by
  letI := Fintype.ofFinite ι
  exact hsq.of_le (hf.measurable j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [Real.norm_of_nonneg (sqfct_nonneg f x)] using norm_le_sqfct f j x)

private lemma memLp_tsum_of_sqfct [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    MemLp (∑' j, f j) (2 * r) μ := by
  letI := Fintype.ofFinite ι
  rw [show (∑' j, f j) = ∑ j : ι, f j by
    funext x
    simpa only [Finset.sum_apply] using tsum_fintype_apply f x]
  exact memLp_finsetSum' Finset.univ fun j _ ↦ memLp_component_of_sqfct (μ := μ) hf hsq j

private lemma integrable_prod_s_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    Integrable (fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) μ := by
  letI := Fintype.ofFinite ι
  rw [show (fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
      fun x ↦ (‖(∑' j, f j) x‖ ^ (2 * r) : ℂ) by
    funext x
    exact prod_s_pointwiseFamily_eq_ofReal_norm_pow f r x]
  have hF : MemLp (∑' j, f j) (↑(2 * r) : ENNReal) μ := by
    simpa [Nat.cast_mul] using memLp_tsum_of_sqfct (μ := μ) hf hsq
  simpa [Complex.ofReal_pow] using
    Integrable.ofReal (𝕜 := ℂ) (hF.integrable_norm_pow (by omega : 2 * r ≠ 0))

private lemma enorm_integral_prod_s_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    ‖∫ x, (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) ∂μ‖ₑ =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  let F : α → ℂ := ∑' j, f j
  have hF : MemLp F (↑(2 * r) : ENNReal) μ := by
    simpa [F, Nat.cast_mul] using memLp_tsum_of_sqfct (μ := μ) hf hsq
  have hpow_int : Integrable (fun x ↦ ‖F x‖ ^ (2 * r)) μ :=
    hF.integrable_norm_pow (by omega : 2 * r ≠ 0)
  have hpow_nonneg : 0 ≤ᵐ[μ] fun x ↦ ‖F x‖ ^ (2 * r) :=
    Filter.Eventually.of_forall fun x ↦ pow_nonneg (norm_nonneg _) _
  calc
    ‖∫ x, (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) ∂μ‖ₑ
        = ‖∫ x, ((‖F x‖ : ℂ) ^ (2 * r)) ∂μ‖ₑ := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            simpa [F, tsum_fintype_apply] using prod_s_pointwiseFamily_eq_ofReal_norm_pow f r x
    _ = ‖((∫ x, ‖F x‖ ^ (2 * r) ∂μ : ℝ) : ℂ)‖ₑ := by
          congr 1
          rw [show (∫ x, ((‖F x‖ : ℂ) ^ (2 * r)) ∂μ) =
              ∫ x, ((‖F x‖ ^ (2 * r) : ℝ) : ℂ) ∂μ by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              simp [Complex.ofReal_pow]]
          rw [integral_complex_ofReal]
    _ = ENNReal.ofReal (∫ x, ‖F x‖ ^ (2 * r) ∂μ) := by
          rw [← ofReal_norm]
          rw [Complex.norm_of_nonneg (MeasureTheory.integral_nonneg fun x ↦
            pow_nonneg (norm_nonneg (F x)) _)]
    _ = ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ (2 * r)) ∂μ := by
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpow_int hpow_nonneg
    _ = ∫⁻ x, ‖F x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            calc
              ENNReal.ofReal (‖F x‖ ^ (2 * r)) = ENNReal.ofReal ‖F x‖ ^ (2 * r) := by
                rw [ENNReal.ofReal_pow (norm_nonneg _)]
              _ = ‖F x‖ₑ ^ (2 * r) := by
                rw [ofReal_norm]
              _ = ‖F x‖ₑ ^ ((2 * r : ℕ) : ℝ) := by
                rw [ENNReal.rpow_natCast]

private lemma lintegral_sum_norm_pow_le_pointwise_bound [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ) ≤
      ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ := by
  letI := Fintype.ofFinite ι
  let P : α → ℂ := fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)
  let R : α → ℂ := fun x ↦ Q (pointwiseFamily f r x)
  have hRint : Integrable R μ := by
    simpa [R] using integrable_Q_pointwiseFamily (μ := μ) (r := r) hf
  have hPint : Integrable P μ := by
    simpa [P] using integrable_prod_s_pointwiseFamily (μ := μ) (r := r) hr hf hsq
  have hRzero : ∫ x, R x ∂μ = 0 := by
    simpa [R] using integral_Q_pointwiseFamily_eq_zero (μ := μ) (r := r) hf
  have hdiff : ∫ x, R x - P x ∂μ = - ∫ x, P x ∂μ := by
    rw [integral_sub hRint hPint, hRzero, zero_sub]
  calc
    (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ)
        = ‖∫ x, P x ∂μ‖ₑ := by
          rw [enorm_integral_prod_s_pointwiseFamily (μ := μ) (r := r) hr hf hsq]
    _ = ‖∫ x, R x - P x ∂μ‖ₑ := by
          rw [hdiff]
          simp
    _ ≤ ∫⁻ x, ‖R x - P x‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm (fun x ↦ R x - P x)
    _ ≤ ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ := by
          apply lintegral_mono
          intro x
          simpa [R, P] using pointwise_bound_sqfct f hr x

private lemma eLpNorm_tsum_pow_eq_lintegral [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (_hf : TypeIVSuperorthogonal μ f r)
    (_hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  have hcast : (2 * r : ENNReal) = ((2 * r : NNReal) : ENNReal) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  simpa [Nat.cast_mul] using
    eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := (∑' j, f j)) (p := (2 * r : NNReal))
      (by exact_mod_cast (by omega : 2 * r ≠ 0))

private lemma eLpNorm_sqfct_pow_eq_lintegral [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) :
    eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  have hcast : (2 * r : ENNReal) = ((2 * r : NNReal) : ENNReal) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  calc
    eLpNorm (sqfct f) ↑(2 * (r : NNReal)) μ ^ ((2 * r : ℕ) : ℝ)
        = ∫⁻ x, ‖sqfct f x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          simpa [Nat.cast_mul] using
            eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := sqfct f) (p := (2 * r : NNReal))
              (by exact_mod_cast (by omega : 2 * r ≠ 0))
    _ = ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            have hbase : ‖sqfct f x‖ₑ = ENNReal.ofReal (sqfct f x) := by
              rw [← ofReal_norm, Real.norm_of_nonneg (sqfct_nonneg f x)]
            change ‖sqfct f x‖ₑ ^ ((2 * r : ℕ) : ℝ) =
              (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ)
            rw [hbase]

private lemma eLpNorm_tsum_pow_eq_lintegral_nat [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ := by
  rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) hr hf hsq]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) =
      ‖(∑' j, f j) x‖ₑ ^ (2 * r)
    exact ENNReal.rpow_natCast _ (2 * r)

private lemma eLpNorm_sqfct_pow_eq_lintegral_nat [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) :
    eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ := by
  rw [eLpNorm_sqfct_pow_eq_lintegral (μ := μ) (f := f) hr]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) =
      (ENNReal.ofReal (sqfct f x)) ^ (2 * r)
    exact ENNReal.rpow_natCast _ (2 * r)

omit [MeasurableSpace α] in
private lemma ennreal_sq_mul_max_pow_le (hr : 1 ≤ r) (a b K : ENNReal) :
    K * b ^ 2 * (max a b) ^ (2 * r - 2) ≤
      K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h]
    calc
      K * b ^ 2 * b ^ (2 * r - 2) = K * b ^ (2 * r) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
        gcongr
        exact (le_self_add : b ^ (2 * r) ≤ b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2))
  · have hbale : b ≤ a := le_of_not_ge h
    rw [max_eq_left hbale]
    calc
      K * b ^ 2 * a ^ (2 * r - 2) = K * (b ^ 2 * a ^ (2 * r - 2)) := by
        rw [mul_assoc]
      _ ≤ K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
        gcongr
        exact (le_add_self : b ^ 2 * a ^ (2 * r - 2) ≤
          b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2))

omit [MeasurableSpace α] in
private lemma ennreal_pow_two_mul_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ (2 * r)) ^ (1 / (r : ℝ)) = x ^ 2 := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 / (r : ℝ)) = 2 by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    rw [Nat.cast_mul]
    field_simp [hr0]
    norm_num]
  exact ENNReal.rpow_natCast x 2

omit [MeasurableSpace α] in
private lemma ennreal_pow_two_mul_one_sub_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ (2 * r)) ^ (1 - 1 / (r : ℝ)) = x ^ (2 * r - 2) := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 - 1 / (r : ℝ)) = ((2 * r - 2 : ℕ) : ℝ) by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hcast : ((2 * r - 2 : ℕ) : ℝ) = (2 : ℝ) * r - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r)]
      norm_num [Nat.cast_mul]
    rw [hcast]
    rw [Nat.cast_mul]
    field_simp [hr0]
    ring]
  exact ENNReal.rpow_natCast x (2 * r - 2)

omit [MeasurableSpace α] in
private lemma ennreal_rpow_two_mul_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ ((2 * r : ℕ) : ℝ)) ^ (1 / (r : ℝ)) = x ^ 2 := by
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 / (r : ℝ)) = 2 by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    rw [Nat.cast_mul]
    field_simp [hr0]
    norm_num]
  exact ENNReal.rpow_natCast x 2

omit [MeasurableSpace α] in
private lemma ennreal_rpow_two_mul_one_sub_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ ((2 * r : ℕ) : ℝ)) ^ (1 - 1 / (r : ℝ)) = x ^ (2 * r - 2) := by
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 - 1 / (r : ℝ)) = ((2 * r - 2 : ℕ) : ℝ) by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hcast : ((2 * r - 2 : ℕ) : ℝ) = (2 : ℝ) * r - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r)]
      norm_num [Nat.cast_mul]
    rw [hcast]
    rw [Nat.cast_mul]
    field_simp [hr0]
    ring]
  exact ENNReal.rpow_natCast x (2 * r - 2)

private lemma lintegral_pointwise_bound_le_split [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ) ≤
      ((2 * r)! - 1 : ENNReal) *
        ((∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) +
          ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
            ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) := by
  letI := Fintype.ofFinite ι
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  let S : α → ENNReal := fun x ↦ ENNReal.ofReal (sqfct f x)
  let A : α → ENNReal := fun x ↦ ‖(∑' j, f j) x‖ₑ
  have hSae : AEMeasurable S μ := hsq.aemeasurable.ennreal_ofReal
  have hAae : AEMeasurable A μ :=
    (aestronglyMeasurable_tsum_finite (μ := μ) hf).aemeasurable.enorm
  have hsplit_ae :
      AEMeasurable (fun x ↦ S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2)) μ :=
    (hSae.pow_const (2 * r)).add ((hSae.pow_const 2).mul (hAae.pow_const (2 * r - 2)))
  calc
    (∫⁻ x, K * S x ^ 2 * (max (A x) (S x)) ^ (2 * r - 2) ∂μ)
        ≤ ∫⁻ x, K * (S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2)) ∂μ := by
          apply lintegral_mono
          intro x
          exact ennreal_sq_mul_max_pow_le hr (A x) (S x) K
    _ = K * ∫⁻ x, S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2) ∂μ := by
          rw [lintegral_const_mul'' K hsplit_ae]
    _ = K * ((∫⁻ x, S x ^ (2 * r) ∂μ) +
          ∫⁻ x, S x ^ 2 * A x ^ (2 * r - 2) ∂μ) := by
          rw [lintegral_add_left' (hSae.pow_const (2 * r))]

private lemma lintegral_mixed_le_lintegral_powers [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) ≤
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
        (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) := by
  letI := Fintype.ofFinite ι
  let S : α → ENNReal := fun x ↦ ENNReal.ofReal (sqfct f x)
  let A : α → ENNReal := fun x ↦ ‖(∑' j, f j) x‖ₑ
  have hSae : AEMeasurable S μ := hsq.aemeasurable.ennreal_ofReal
  have hAae : AEMeasurable A μ :=
    (aestronglyMeasurable_tsum_finite (μ := μ) hf).aemeasurable.enorm
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hp : 0 ≤ 1 / (r : ℝ) := by positivity
  have hq : 0 ≤ 1 - 1 / (r : ℝ) := by
    have hinvle : 1 / (r : ℝ) ≤ 1 := by
      simpa [one_div] using (inv_le_one_of_one_le₀ hrR)
    linarith
  have hpq : 1 / (r : ℝ) + (1 - 1 / (r : ℝ)) = 1 := by ring
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
    (f := fun x ↦ S x ^ (2 * r)) (g := fun x ↦ A x ^ (2 * r))
    (hSae.pow_const (2 * r)) (hAae.pow_const (2 * r)) hp hq hpq
  calc
    (∫⁻ x, S x ^ 2 * A x ^ (2 * r - 2) ∂μ)
        = ∫⁻ x, (S x ^ (2 * r)) ^ (1 / (r : ℝ)) *
            (A x ^ (2 * r)) ^ (1 - 1 / (r : ℝ)) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change S x ^ 2 * A x ^ (2 * r - 2) =
              (S x ^ (2 * r)) ^ (1 / (r : ℝ)) *
                (A x ^ (2 * r)) ^ (1 - 1 / (r : ℝ))
            rw [ennreal_pow_two_mul_inv hr (S x), ennreal_pow_two_mul_one_sub_inv hr (A x)]
    _ ≤ (∫⁻ x, S x ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
        (∫⁻ x, A x ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) := hholder

private lemma eLpNorm_tsum_power_le [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) ≤
      ((2 * r)! - 1 : ENNReal) *
        (eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) +
          eLpNorm (sqfct f) (2 * r) μ ^ 2 *
            eLpNorm (∑' j, f j) (2 * r) μ ^ (2 * r - 2)) := by
  letI := Fintype.ofFinite ι
  let N : ENNReal := eLpNorm (∑' j, f j) (2 * r) μ
  let M : ENNReal := eLpNorm (sqfct f) (2 * r) μ
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  have hmixed :
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) ≤
      M ^ 2 * N ^ (2 * r - 2) := by
    calc
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ)
          ≤ (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
              (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) :=
            lintegral_mixed_le_lintegral_powers (μ := μ) hr hf hsq
      _ = (M ^ ((2 * r : ℕ) : ℝ)) ^ (1 / (r : ℝ)) *
            (N ^ ((2 * r : ℕ) : ℝ)) ^ (1 - 1 / (r : ℝ)) := by
            rw [← eLpNorm_sqfct_pow_eq_lintegral_nat (μ := μ) (f := f) hr]
            rw [← eLpNorm_tsum_pow_eq_lintegral_nat (μ := μ) hr hf hsq]
      _ = M ^ 2 * N ^ (2 * r - 2) := by
            rw [ennreal_rpow_two_mul_inv hr M, ennreal_rpow_two_mul_one_sub_inv hr N]
  calc
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ)
        = ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) hr hf hsq]
    _ ≤ ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ :=
          lintegral_sum_norm_pow_le_pointwise_bound (μ := μ) hr hf hsq
    _ ≤ K * ((∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) +
          ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
            ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) := by
          simpa [K] using lintegral_pointwise_bound_le_split (μ := μ) hr hf hsq
    _ ≤ K * (M ^ ((2 * r : ℕ) : ℝ) + M ^ 2 * N ^ (2 * r - 2)) := by
          gcongr
          · rw [← eLpNorm_sqfct_pow_eq_lintegral_nat (μ := μ) (f := f) hr]

omit [MeasurableSpace α] in
private lemma C_sq_of_two_le (hr : 2 ≤ r) :
    C r ^ 2 = (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
  rw [C]
  · rw [mul_pow]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [show ((2 : ℝ)⁻¹) * ((2 : ℕ) : ℝ) = 1 by norm_num]
    rw [ENNReal.rpow_one]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [show ((2 : ℝ)⁻¹) * ((2 : ℕ) : ℝ) = 1 by norm_num]
    rw [ENNReal.rpow_one]
  · omega

omit [MeasurableSpace α] in
private lemma one_le_two_mul_factorial_sub_one (hr : 2 ≤ r) :
    (1 : ENNReal) ≤ (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
  have hnat : 1 ≤ (2 * r)! - 1 := by
    have hfact : 1 < (2 * r)! := by
      rw [Nat.one_lt_factorial]
      omega
    omega
  have hK : (1 : ENNReal) ≤ (((2 * r)! - 1 : ℕ) : ENNReal) := by
    exact_mod_cast hnat
  calc
    (1 : ENNReal) ≤ (((2 * r)! - 1 : ℕ) : ENNReal) := hK
    _ ≤ (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
      have hmul : (1 : ENNReal) * (((2 * r)! - 1 : ENNReal)) ≤
          (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
        gcongr
        norm_num
      simpa using hmul

omit [MeasurableSpace α] in
private lemma ennreal_absorb_sqfct (hr : 2 ≤ r) {N M : ENNReal} (hNtop : N ≠ ⊤)
    (hpow : N ^ ((2 * r : ℕ) : ℝ) ≤
      (((2 * r)! - 1 : ENNReal) *
        (M ^ ((2 * r : ℕ) : ℝ) + M ^ 2 * N ^ (2 * r - 2)))) :
    N ≤ C r * M := by
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  have hr1 : 1 ≤ r := le_trans (by norm_num : 1 ≤ 2) hr
  have hp2 : 2 * r = 2 + (2 * r - 2) := by omega
  have hNpow_nat :
      N ^ (2 * r) ≤ K * (M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)) := by
    simpa only [K, ENNReal.rpow_natCast] using hpow
  have hsq : N ^ 2 ≤ (2 : ENNReal) * K * M ^ 2 := by
    by_cases hNM : N ≤ M
    · calc
        N ^ 2 ≤ M ^ 2 := by gcongr
        _ ≤ ((2 : ENNReal) * K) * M ^ 2 := by
          have hcoef : (1 : ENNReal) ≤ (2 : ENNReal) * K := by
            simpa [K] using one_le_two_mul_factorial_sub_one hr
          calc
            M ^ 2 = (1 : ENNReal) * M ^ 2 := by rw [one_mul]
            _ ≤ ((2 : ENNReal) * K) * M ^ 2 := by
              exact _root_.mul_le_mul_left hcoef (M ^ 2)
        _ = (2 : ENNReal) * K * M ^ 2 := by rw [mul_assoc]
    · have hMN : M ≤ N := le_of_not_ge hNM
      have hNpos : N ≠ 0 := by
        exact ne_of_gt (lt_of_le_of_lt bot_le (lt_of_not_ge hNM))
      have hfac_ne0 : N ^ (2 * r - 2) ≠ 0 := ENNReal.pow_ne_zero hNpos _
      have hfac_ne_top : N ^ (2 * r - 2) ≠ ⊤ := ENNReal.pow_ne_top hNtop
      have hMpow_le : M ^ (2 * r) ≤ M ^ 2 * N ^ (2 * r - 2) := by
        calc
          M ^ (2 * r) = M ^ 2 * M ^ (2 * r - 2) := by
            rw [← pow_add]
            congr 1
          _ ≤ M ^ 2 * N ^ (2 * r - 2) := by
            gcongr
      have hsum_le :
          M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2) ≤
            (2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2)) := by
        calc
          M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)
              ≤ M ^ 2 * N ^ (2 * r - 2) + M ^ 2 * N ^ (2 * r - 2) := by
                gcongr
          _ = (2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2)) := by
                simp [two_mul]
      have hmain :
          N ^ (2 * r) ≤ ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
        calc
          N ^ (2 * r) ≤ K * (M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)) := hNpow_nat
          _ ≤ K * ((2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2))) := by
            gcongr
          _ = ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
            ring
      have hmain' : N ^ 2 * N ^ (2 * r - 2) ≤
          ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
        calc
          N ^ 2 * N ^ (2 * r - 2) = N ^ (2 * r) := by
            rw [← pow_add]
            congr 1
            omega
          _ ≤ ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := hmain
      exact (ENNReal.mul_le_mul_iff_left hfac_ne0 hfac_ne_top).mp hmain'
  apply (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).mp
  calc
    N ^ 2 ≤ (2 : ENNReal) * K * M ^ 2 := hsq
    _ = (C r * M) ^ 2 := by
      rw [mul_pow, C_sq_of_two_le hr]

private lemma eLpNorm_tsum_le_sqfct_of_one [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f 1) (hsq : MemLp (sqfct f) 2 μ) :
    eLpNorm (∑' j, f j) 2 μ ≤ eLpNorm (sqfct f) 2 μ := by
  letI := Fintype.ofFinite ι
  have htwoone : (2 * ((1 : ℕ) : ENNReal)) = (2 : ENNReal) := by norm_num
  have hsq' : MemLp (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ := by
    simpa [htwoone] using hsq
  have hpoint :
      (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ) ≤
        ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
    calc
      (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ)
          ≤ ∫⁻ x, (((2 * 1)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
              (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * 1 - 2)) ∂μ :=
            lintegral_sum_norm_pow_le_pointwise_bound (μ := μ) (r := 1) (by norm_num) hf hsq'
      _ = ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              let Sx := ENNReal.ofReal (sqfct f x)
              change (((2 * 1)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
                (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ 0) =
                  (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ)
              have hcoeff : (((2 * 1)! - 1 : ENNReal)) = 1 := by
                change ((2 : ENNReal) - 1) = 1
                exact ENNReal.sub_eq_of_eq_add (by norm_num) (by norm_num)
              rw [hcoeff]
              simp
  have hpow :
      eLpNorm (∑' j, f j) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) ≤
        eLpNorm (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) := by
    calc
      eLpNorm (∑' j, f j) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ)
          = ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
            rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) (r := 1) (by norm_num) hf hsq']
      _ ≤ ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := hpoint
      _ = eLpNorm (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) := by
            rw [← eLpNorm_sqfct_pow_eq_lintegral (μ := μ) (f := f) (r := 1) (by norm_num)]
  have hle := (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < ((2 * 1 : ℕ) : ℝ))).mp hpow
  simpa [htwoone] using hle

theorem sqfct_estimate_of_type_iv_superorthogonal_finite [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  := by
  letI := Fintype.ofFinite ι
  by_cases h1 : r = 1
  · subst r
    have hsq1 : MemLp (sqfct f) 2 μ := by
      simpa using hsq
    simpa [C] using eLpNorm_tsum_le_sqfct_of_one (μ := μ) (f := f) hf hsq1
  · have hr2 : 2 ≤ r := by omega
    have hNtop : eLpNorm (∑' j, f j) (2 * r) μ ≠ ⊤ :=
      (memLp_tsum_of_sqfct (μ := μ) hf hsq).eLpNorm_lt_top.ne
    exact ennreal_absorb_sqfct (r := r) hr2 hNtop
      (eLpNorm_tsum_power_le (μ := μ) hr hf hsq)

omit [MeasurableSpace α] in
private lemma C_lt_top (r : ℕ) : C r < ⊤ := by
  unfold C
  split
  · norm_num
  · exact ENNReal.mul_lt_top (by finiteness) (by finiteness)

omit [MeasurableSpace α] in
private lemma two_mul_natCast_ne_zero (hr : 1 ≤ r) :
    (2 * (r : ENNReal)) ≠ 0 := by
  norm_num
  exact Nat.cast_ne_zero.mpr (_root_.ne_of_gt (Nat.succ_le_iff.mp hr))

omit [MeasurableSpace α] in
private lemma two_mul_natCast_ne_top (r : ℕ) :
    (2 * (r : ENNReal)) ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top r)

private def sqtail (f : ι → α → ℂ) (s : Finset ι) (x : α) : ℝ :=
  ((∑' i : {j // j ∉ s}, ‖f i x‖ ^ 2) ^ (2 : ℝ)⁻¹)

omit [MeasurableSpace α] in
private def finsetComplSubtypeEquiv (s : Finset ι) :
    {j // j ∉ s} ≃ {j // j ∈ {k : ι | k ∉ s}} where
  toFun i := ⟨i, by simpa only [Set.mem_setOf_eq] using i.2⟩
  invFun i := ⟨i, by simpa only [Set.mem_setOf_eq] using i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

omit [MeasurableSpace α] in
private lemma tsum_finset_compl_eq_indicator (s : Finset ι) (a : ι → ℝ) :
    (∑' i : {j // j ∉ s}, a i) = ∑' i, ({j : ι | j ∉ s}.indicator a) i := by
  rw [← tsum_subtype {j : ι | j ∉ s} a]
  exact (finsetComplSubtypeEquiv (ι := ι) s).tsum_eq
    (fun i : {j // j ∈ {k : ι | k ∉ s}} ↦ a i)

private lemma aemeasurable_sqtail [Countable ι] {f : ι → α → ℂ} (hf : ∀ i, Measurable (f i))
    (s : Finset ι) : AEMeasurable (sqtail f s) μ := by
  have hterm : ∀ i : {j // j ∉ s}, AEMeasurable (fun x ↦ ‖f i x‖ ^ 2) μ := by
    intro i
    exact ((hf i).norm.pow_const (2 : ℕ)).aemeasurable
  exact (AEMeasurable.tsum hterm).pow_const _

omit [MeasurableSpace α] in
private lemma sqtail_nonneg {f : ι → α → ℂ} (s : Finset ι) (x : α) :
    0 ≤ sqtail f s x := by
  unfold sqtail
  exact Real.rpow_nonneg (tsum_nonneg fun i : {j // j ∉ s} ↦ sq_nonneg ‖f i x‖) _

omit [MeasurableSpace α] in
private lemma sqfct_nonneg_of_summable {f : ι → α → ℂ} (x : α) :
    0 ≤ sqfct f x := by
  unfold sqfct
  exact Real.rpow_nonneg (tsum_nonneg fun i ↦ sq_nonneg ‖f i x‖) _

private lemma sqtail_le_sqfct_ae {f : ι → α → ℂ}
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2) (s : Finset ι) :
    ∀ᵐ x ∂μ, sqtail f s x ≤ sqfct f x := by
  filter_upwards [hsum] with x hx
  have htail_summable :
      Summable fun i ↦ ({j : ι | j ∉ s}.indicator (fun j ↦ ‖f j x‖ ^ 2)) i := by
    refine Summable.of_nonneg_of_le (fun i ↦ ?_) (fun i ↦ ?_) hx
    · by_cases hi : i ∈ s <;> simp [hi]
    · by_cases hi : i ∈ s <;> simp [hi]
  have hle_sum :
      (∑' i : {j // j ∉ s}, ‖f i x‖ ^ 2) ≤
        ∑' i, ‖f i x‖ ^ 2 := by
    calc
      (∑' i : {j // j ∉ s}, ‖f i x‖ ^ 2)
          = ∑' i, ({j : ι | j ∉ s}.indicator (fun j ↦ ‖f j x‖ ^ 2)) i := by
            exact tsum_finset_compl_eq_indicator (s := s) (a := fun j ↦ ‖f j x‖ ^ 2)
      _ ≤ ∑' i, ‖f i x‖ ^ 2 :=
        htail_summable.tsum_le_tsum (fun i ↦ by by_cases hi : i ∈ s <;> simp [hi]) hx
  unfold sqtail sqfct
  exact Real.rpow_le_rpow (tsum_nonneg fun i : {j // j ∉ s} ↦ sq_nonneg ‖f i x‖)
    hle_sum (by positivity)

private lemma memLp_sqtail [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i))
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct f) (2 * r) μ) (s : Finset ι) :
    MemLp (sqtail f s) (2 * r) μ := by
  refine hsq.mono (aemeasurable_sqtail (μ := μ) hf s).aestronglyMeasurable ?_
  exact (sqtail_le_sqfct_ae (μ := μ) hsum s).mono fun x hx ↦ by
    simpa [Real.norm_of_nonneg (sqtail_nonneg s x),
      Real.norm_of_nonneg (sqfct_nonneg_of_summable x)] using hx

private lemma typeIV_restrict_finset {f : ι → α → ℂ} (hf : TypeIVSuperorthogonal μ f r)
    (s : Finset ι) :
    TypeIVSuperorthogonal μ (fun i : {j // j ∈ s} ↦ f i) r where
  measurable j := hf.measurable j
  integrable_cprod j hdist := by
    have hdist' : all_distinct (2 * r) (fun i ↦ (j i : ι)) := by
      intro a b hab hval
      exact hdist a b hab (Subtype.ext hval)
    simpa [cprod] using hf.integrable_cprod (fun i ↦ (j i : ι)) hdist'
  superorthogonal j hdist := by
    have hdist' : all_distinct (2 * r) (fun i ↦ (j i : ι)) := by
      intro a b hab hval
      exact hdist a b hab (Subtype.ext hval)
    simpa [cprod] using hf.superorthogonal (fun i ↦ (j i : ι)) hdist'

private lemma aemeasurable_sqfct_fintype {κ : Type*} [Finite κ] {g : κ → α → ℂ}
    (hg : ∀ i, Measurable (g i)) :
    AEMeasurable (sqfct g) μ := by
  letI := Fintype.ofFinite κ
  have hsum : Measurable fun x ↦ (∑ i, ‖g i x‖ ^ 2 : ℝ) := by
    exact Finset.measurable_fun_sum Finset.univ fun i _ ↦ (hg i).norm.pow_const (2 : ℕ)
  refine ((hsum.pow_const ((2 : ℝ)⁻¹)).aemeasurable).congr ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [sqfct_fintype]

private lemma sqfct_restrict_le_sqtail_ae {f : ι → α → ℂ}
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2) {s t : Finset ι}
    (hdisj : Disjoint t s) :
    ∀ᵐ x ∂μ, sqfct (fun i : {j // j ∈ t} ↦ f i) x ≤ sqtail f s x := by
  filter_upwards [hsum] with x hx
  let a : ι → ℝ := fun i ↦ ‖f i x‖ ^ 2
  let b : ι → ℝ := fun i ↦ ({j : ι | j ∉ s}.indicator a) i
  have hb_nonneg : ∀ i, 0 ≤ b i := by
    intro i
    by_cases hi : i ∈ s <;> simp [b, a, hi]
  have hb_le : ∀ i, b i ≤ a i := by
    intro i
    by_cases hi : i ∈ s <;> simp [b, a, hi]
  have hb_summable : Summable b := Summable.of_nonneg_of_le hb_nonneg hb_le hx
  have ht_sum_le :
      (∑ i ∈ t, a i) ≤ ∑' i : {j // j ∉ s}, ‖f i x‖ ^ 2 := by
    have hsum_eq : (∑ i ∈ t, a i) = ∑ i ∈ t, b i := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have his : i ∉ s := by
        exact fun hs ↦ (Finset.disjoint_left.mp hdisj) hi hs
      simp [b, a, his]
    calc
      (∑ i ∈ t, a i) = ∑ i ∈ t, b i := hsum_eq
      _ ≤ ∑' i, b i := hb_summable.sum_le_tsum t (fun i _ ↦ hb_nonneg i)
      _ = ∑' i : {j // j ∉ s}, ‖f i x‖ ^ 2 := by
        simpa [b, a] using
          (tsum_finset_compl_eq_indicator (ι := ι) s a).symm
  have htsum :
      (∑' i : {j // j ∈ t}, ‖f i x‖ ^ 2) = ∑ i ∈ t, a i := by
    simpa [a] using (Finset.tsum_subtype t (fun i ↦ ‖f i x‖ ^ 2))
  unfold sqfct sqtail
  rw [htsum]
  exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖f i x‖)
    ht_sum_le (by positivity)

private lemma eLpNorm_sqfct_restrict_le_sqtail {f : ι → α → ℂ}
    (_hf : ∀ i, Measurable (f i))
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2) {s t : Finset ι}
    (hdisj : Disjoint t s) :
    eLpNorm (sqfct (fun i : {j // j ∈ t} ↦ f i)) (2 * r) μ ≤
      eLpNorm (sqtail f s) (2 * r) μ := by
  letI : Fintype {j // j ∈ t} := Finset.fintypeCoeSort t
  refine eLpNorm_mono_ae ?_
  exact (sqfct_restrict_le_sqtail_ae (μ := μ) hsum hdisj).mono fun x hx ↦ by
    simpa [Real.norm_of_nonneg (sqfct_nonneg_of_summable x),
      Real.norm_of_nonneg (sqtail_nonneg s x)] using hx

private lemma memLp_sqfct_restrict_of_sqtail [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i))
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct f) (2 * r) μ) {s t : Finset ι} (hdisj : Disjoint t s) :
    MemLp (sqfct (fun i : {j // j ∈ t} ↦ f i)) (2 * r) μ := by
  letI : Fintype {j // j ∈ t} := Finset.fintypeCoeSort t
  refine (memLp_sqtail (μ := μ) hf hsum hsq s).mono
    (aemeasurable_sqfct_fintype (μ := μ) (fun i : {j // j ∈ t} ↦ hf i)).aestronglyMeasurable ?_
  exact (sqfct_restrict_le_sqtail_ae (μ := μ) hsum hdisj).mono fun x hx ↦ by
    simpa [Real.norm_of_nonneg (sqfct_nonneg_of_summable x),
      Real.norm_of_nonneg (sqtail_nonneg s x)] using hx

private lemma finset_sum_bound_by_sqtail [Countable ι] [Fact (1 ≤ (2 * (r : ENNReal)))]
    (hr : 1 ≤ r) {f : ι → Lp ℂ (2 * r) μ}
    (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) {s t : Finset ι}
    (hdisj : Disjoint t s) :
    ENNReal.ofReal ‖∑ i ∈ t, f i‖ ≤
      C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ := by
  letI : Fintype {j // j ∈ t} := Finset.fintypeCoeSort t
  letI : Finite {j // j ∈ t} := Finite.of_fintype _
  let g : {j // j ∈ t} → α → ℂ := fun i ↦ f i
  have hmem : MemLp (sqfct g) (2 * r) μ :=
    memLp_sqfct_restrict_of_sqtail (μ := μ) (r := r) (f := fun i ↦ (f i : α → ℂ))
      hf.measurable hsum hsq hdisj
  have hfinite := sqfct_estimate_of_type_iv_superorthogonal_finite (μ := μ) (r := r) hr
    (typeIV_restrict_finset (μ := μ) (r := r) hf t) hmem
  have hsum_ae :
      (⇑(∑ i ∈ t, f i) : α → ℂ) =ᵐ[μ] (∑' i, g i) := by
    refine (Lp.coeFn_fun_finsetSum t f).trans ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [tsum_fintype]
      rw [Finset.sum_apply]
      change (∑ i ∈ t, f i x) = ∑ i : {j // j ∈ t}, f i x
      exact (Finset.sum_coe_sort t (fun i ↦ f i x)).symm
  calc
    ENNReal.ofReal ‖∑ i ∈ t, f i‖ = eLpNorm (∑' i, g i) (2 * r) μ := by
      rw [ofReal_norm, Lp.enorm_def]
      exact eLpNorm_congr_ae hsum_ae
    _ ≤ C r * eLpNorm (sqfct g) (2 * r) μ := hfinite
    _ ≤ C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ := by
      gcongr
      exact eLpNorm_sqfct_restrict_le_sqtail (μ := μ) (r := r)
        (f := fun i ↦ (f i : α → ℂ)) hf.measurable hsum hdisj

private lemma finset_sum_norm_le_sqtail_toReal [Countable ι] [Fact (1 ≤ (2 * (r : ENNReal)))]
    (hr : 1 ≤ r) {f : ι → Lp ℂ (2 * r) μ}
    (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) {s t : Finset ι}
    (hdisj : Disjoint t s) :
    ‖∑ i ∈ t, f i‖ ≤
      (C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ).toReal := by
  have hbound := finset_sum_bound_by_sqtail (μ := μ) (r := r) hr hf hsum hsq hdisj
  have htail_ne_top :
      eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ ≠ ⊤ :=
    (memLp_sqtail (μ := μ) (r := r) (f := fun i ↦ (f i : α → ℂ))
      hf.measurable hsum hsq s).eLpNorm_lt_top.ne
  have hprod_ne_top :
      C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_of_lt (C_lt_top r)) htail_ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hprod_ne_top).1 hbound

private lemma finset_sum_norm_le_sqfct_toReal [Countable ι] [Fact (1 ≤ (2 * (r : ENNReal)))]
    (hr : 1 ≤ r) {f : ι → Lp ℂ (2 * r) μ}
    (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) (t : Finset ι) :
    ‖∑ i ∈ t, f i‖ ≤
      (C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ).toReal := by
  have hbound := finset_sum_bound_by_sqtail (μ := μ) (r := r) hr hf hsum hsq
    (s := ∅) (t := t) (Finset.disjoint_empty_right t)
  have htail_le :
      eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) ∅) (2 * r) μ ≤
        eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ := by
    refine eLpNorm_mono_ae ?_
    exact (sqtail_le_sqfct_ae (μ := μ)
      (f := fun i ↦ (f i : α → ℂ)) hsum ∅).mono fun x hx ↦ by
        simpa [Real.norm_of_nonneg (sqtail_nonneg ∅ x),
          Real.norm_of_nonneg (sqfct_nonneg_of_summable x)] using hx
  have hbound_full :
      ENNReal.ofReal ‖∑ i ∈ t, f i‖ ≤
        C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ := by
    calc
      ENNReal.ofReal ‖∑ i ∈ t, f i‖
          ≤ C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) ∅) (2 * r) μ := hbound
      _ ≤ C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ := by
        gcongr
  have hprod_ne_top :
      C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_of_lt (C_lt_top r)) hsq.eLpNorm_lt_top.ne
  exact (ENNReal.ofReal_le_iff_le_toReal hprod_ne_top).1 hbound_full

private lemma tendsto_eLpNorm_sqtail_atTop_zero [Countable ι] (hr : 1 ≤ r)
    {f : ι → Lp ℂ (2 * r) μ}
    (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) :
    Filter.Tendsto (fun s : Finset ι ↦ eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ)
      Filter.atTop (nhds 0) := by
  let p : ENNReal := 2 * (r : ENNReal)
  have hp0 : p ≠ 0 := two_mul_natCast_ne_zero hr
  have hptop : p ≠ ⊤ := two_mul_natCast_ne_top r
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have h_int_tendsto :
      Filter.Tendsto
        (fun s : Finset ι ↦
          ∫⁻ x, ‖sqtail (fun i ↦ (f i : α → ℂ)) s x‖ₑ ^ p.toReal ∂μ)
        Filter.atTop (nhds 0) := by
    have hfin : (∫⁻ x, ‖sqfct (fun i ↦ (f i : α → ℂ)) x‖ₑ ^ p.toReal ∂μ) ≠ ⊤ := by
      exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hsq.2).ne
    have hlim : ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun s : Finset ι ↦
            ‖sqtail (fun i ↦ (f i : α → ℂ)) s x‖ₑ ^ p.toReal)
          Filter.atTop (nhds 0) := by
      filter_upwards [hsum] with x hx
      have htail_sum :
          Filter.Tendsto
            (fun s : Finset ι ↦
              ∑' i : {j // j ∉ s}, ‖(f i : α → ℂ) x‖ ^ 2)
            Filter.atTop (nhds 0) := by
        exact tendsto_tsum_compl_atTop_zero (fun i : ι ↦ ‖(f i : α → ℂ) x‖ ^ 2)
      have htail :
          Filter.Tendsto (fun s : Finset ι ↦ sqtail (fun i ↦ (f i : α → ℂ)) s x)
            Filter.atTop (nhds 0) := by
        have hpow := (Real.continuous_rpow_const (by positivity : 0 ≤ (2 : ℝ)⁻¹)).tendsto 0
        simpa [sqtail, Function.comp_def, Real.zero_rpow (by positivity : (2 : ℝ)⁻¹ ≠ 0)]
          using hpow.comp htail_sum
      have henorm :
          Filter.Tendsto (fun s : Finset ι ↦ ‖sqtail (fun i ↦ (f i : α → ℂ)) s x‖ₑ)
            Filter.atTop (nhds (0 : ENNReal)) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp htail
      have hpow :
          Filter.Tendsto (fun y : ENNReal ↦ y ^ p.toReal) (nhds (0 : ENNReal)) (nhds 0) := by
        simpa [ENNReal.zero_rpow_of_pos hp_pos] using
          (ENNReal.continuous_rpow_const.tendsto (0 : ENNReal) :
            Filter.Tendsto (fun y : ENNReal ↦ y ^ p.toReal) (nhds 0)
              (nhds ((0 : ENNReal) ^ p.toReal)))
      simpa [Function.comp_def] using hpow.comp henorm
    haveI : Countable (Finset ι) := inferInstance
    have hdct := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ)
      (l := (Filter.atTop : Filter (Finset ι)))
      (F := fun s x ↦ ‖sqtail (fun i ↦ (f i : α → ℂ)) s x‖ₑ ^ p.toReal)
      (f := fun _x ↦ 0)
      (bound := fun x ↦ ‖sqfct (fun i ↦ (f i : α → ℂ)) x‖ₑ ^ p.toReal)
      (by
        exact Filter.Eventually.of_forall fun s ↦
          ((aemeasurable_sqtail (μ := μ) hf.measurable s).enorm.pow_const _))
      (by
        exact Filter.Eventually.of_forall fun s ↦
          (sqtail_le_sqfct_ae (μ := μ)
            (f := fun i ↦ (f i : α → ℂ)) hsum s).mono fun x hx ↦
              ENNReal.rpow_le_rpow
                (by simpa [enorm_le_iff_norm_le, Real.norm_of_nonneg (sqtail_nonneg s x),
                  Real.norm_of_nonneg (sqfct_nonneg_of_summable x)] using hx)
                (by positivity))
      hfin hlim
    simpa using hdct
  have hnorm :
      Filter.Tendsto
        (fun s : Finset ι ↦
          (∫⁻ x, ‖sqtail (fun i ↦ (f i : α → ℂ)) s x‖ₑ ^ p.toReal ∂μ) ^
            (1 / p.toReal))
        Filter.atTop (nhds 0) := by
    have hpow :
        Filter.Tendsto (fun y : ENNReal ↦ y ^ (1 / p.toReal))
          (nhds (0 : ENNReal)) (nhds 0) := by
      have hinv_pos : 0 < p.toReal⁻¹ := inv_pos.mpr hp_pos
      simpa [one_div, ENNReal.zero_rpow_of_pos hinv_pos] using
        (ENNReal.continuous_rpow_const.tendsto (0 : ENNReal) :
          Filter.Tendsto (fun y : ENNReal ↦ y ^ p.toReal⁻¹) (nhds 0)
            (nhds ((0 : ENNReal) ^ p.toReal⁻¹)))
    simpa [Function.comp_def] using hpow.comp h_int_tendsto
  have hpow0 : (0 : ENNReal) ^ (1 / p.toReal) = 0 :=
    by simpa [one_div] using ENNReal.zero_rpow_of_pos (inv_pos.mpr hp_pos)
  simpa [p, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpow0] using hnorm

theorem sqfct_estimate_of_type_iv_superorthogonal [Countable ι]
    [Fact (1 ≤ (2 * (r : ENNReal)))] (hr : 1 ≤ r)
    {f : ι → Lp ℂ (2 * r) μ} (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) :
    Summable f ∧ ENNReal.ofReal ‖∑' j, f j‖ ≤ C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ  := by
  have htail_tendsto :=
    tendsto_eLpNorm_sqtail_atTop_zero (μ := μ) (r := r) hr hf hsum hsq
  have hSummable : Summable f := by
    refine summable_iff_vanishing_norm.mpr ?_
    intro ε hε
    have hprod :
        Filter.Tendsto
          (fun s : Finset ι ↦
            C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ)
          Filter.atTop (nhds 0) := by
      simpa [mul_zero] using
        ENNReal.Tendsto.const_mul htail_tendsto (Or.inr (ne_of_lt (C_lt_top r)))
    have hreal :
        Filter.Tendsto
          (fun s : Finset ι ↦
            (C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ).toReal)
          Filter.atTop (nhds (0 : ℝ)) := by
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod
    have hsmall_eventually :
        ∀ᶠ s : Finset ι in Filter.atTop,
          (C r * eLpNorm (sqtail (fun i ↦ (f i : α → ℂ)) s) (2 * r) μ).toReal < ε :=
      hreal.eventually (gt_mem_nhds hε)
    rcases Filter.eventually_atTop.1 hsmall_eventually with ⟨s, hs⟩
    refine ⟨s, fun t hdisj ↦ ?_⟩
    exact lt_of_le_of_lt
      (finset_sum_norm_le_sqtail_toReal (μ := μ) (r := r) hr hf hsum hsq hdisj)
      (hs s le_rfl)
  refine ⟨hSummable, ?_⟩
  let B : ENNReal := C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ
  have hB_ne_top : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_of_lt (C_lt_top r)) hsq.eLpNorm_lt_top.ne
  have hpartial_bound : ∀ t : Finset ι, ‖∑ i ∈ t, f i‖ ≤ B.toReal := by
    intro t
    simpa [B] using
      finset_sum_norm_le_sqfct_toReal (μ := μ) (r := r) hr hf hsum hsq t
  have hsum_tendsto :
      Filter.Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, f i)
        Filter.atTop (nhds (∑' j, f j)) := by
    simpa [HasSum] using hSummable.hasSum
  have hnorm_tendsto :
      Filter.Tendsto (fun s : Finset ι ↦ ‖∑ i ∈ s, f i‖)
        Filter.atTop (nhds ‖∑' j, f j‖) :=
    hsum_tendsto.norm
  have hnorm_le : ‖∑' j, f j‖ ≤ B.toReal :=
    le_of_tendsto_of_tendsto' hnorm_tendsto tendsto_const_nhds hpartial_bound
  change ENNReal.ofReal ‖∑' j, f j‖ ≤ B
  exact (ENNReal.ofReal_le_iff_le_toReal hB_ne_top).2 hnorm_le

end Codex

end Superorthogonal

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
