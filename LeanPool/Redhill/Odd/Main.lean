/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import LeanPool.Redhill.Odd.Pell
import LeanPool.Redhill.Odd.Subsum
import LeanPool.Redhill.Common.Conjectures

/-!
# The odd case (Theorem 1.13)
-/


namespace OddCase

variable {n : ℕ} {F : Finset ℕ} {k : ℕ}

variable (n F k) in
/-- The sequence of `(n + 5)`-tuples **completely** contained in `factorFreeTuples F n`
(for `n` even and `0, 1, 2, 5, 10 ∉ F`) and having qualities tending to `5 / 3`. -/
def tupPell : Fin (n + 5) → ℤ :=
  tup n F ((pell (Y n F ^ 2) k).1 * Y n F)

lemma injective_tupPell : (tupPell n F).Injective := fun i j e ↦ by
  replace e := congr($e (Fin.natAdd n 4))
  simp only [tupPell, tup_natAdd_four, neg_inj] at e
  norm_cast at e
  rw [pow_left_inj (by decide), add_left_inj, Nat.mul_left_inj Y_pos.ne'] at e
  exact strictMono_pell_fst.injective e

lemma strongSSC_tupPell : StrongSSC (tupPell n F k) := by
  apply strongSSC_tup
  simp_rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.le_mul_of_pos_left _ pell_fst_pos

lemma tupPell_mem_factorFreeTuples (hn : Even n) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    tupPell n F k ∈ factorFreeTuples F (n + 5) := by
  simp_rw [factorFreeTuples, Set.mem_setOf_eq, strongSSC_tupPell, tupPell, sum_tup, true_and]
  exact ⟨pairwiseCoprime_tup hn (dvd_mul_left ..), not_dvd_tup (dvd_mul_left ..) dF⟩

lemma maxAbs_tupPell : maxAbs (tupPell n F k) = ((pell (Y n F ^ 2) k).1 * Y n F + 1) ^ 5 :=
  maxAbs_tup (Nat.le_mul_of_pos_left _ pell_fst_pos)

section Quality

open UniqueFactorizationMonoid

lemma radical_tupPell_dvd :
    ∃ C > 0, ∀ k, radical (∏ i, tupPell n F k i) ∣
      C * (((pell (Y n F ^ 2) k).1 * Y n F) ^ 2 - 1) * (pell (Y n F ^ 2) k).2 := by
  simp_rw [Fin.prod_univ_add, Fin.prod_univ_five, tupPell, tup_castAdd, tup_natAdd_zero,
    tup_natAdd_one, tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, ← mul_assoc,
    mul_neg, neg_mul, neg_neg]
  set S : ℕ := (∏ i : Fin n, primeChain (max 8 (F.sup id)) i.1) * (VW n F).v * (VW n F).w * 10
  have dS : S ∣ Y n F := by
    unfold S Y
    conv_rhs => simp only [mul_assoc, ← Fin.prod_univ_eq_prod_range]
    simp_rw [mul_comm 10, ← mul_assoc]
    iterate 3 apply mul_dvd_mul_right
    exact dvd_mul_left ..
  have pS : 0 < S := Nat.pos_of_dvd_of_pos dS Y_pos
  refine ⟨S * (Y n F ^ 2 + 1), mul_pos (mod_cast pS) (by positivity), fun k ↦ ?_⟩
  set x : ℤ := (pell (Y n F ^ 2) k).1 * Y n F
  rw [mul_right_comm _ ((x - 1) ^ 5), show (10 : ℤ) = (10 : ℕ) by rfl, ← Nat.cast_prod,
    ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
  change radical ((S : ℤ) * _ * _ * _) ∣ _
  rw [mul_right_comm, mul_assoc (S : ℤ), ← mul_pow, show (x - 1) * (x + 1) = x ^ 2 - 1 by ring,
    mul_right_comm _ _ (x ^ 2 - 1), mul_assoc (_ * _)]
  iterate 2 refine radical_mul_dvd.trans (mul_dvd_mul ?_ ?_)
  · exact radical_dvd_self
  · rw [radical_pow _ (by decide)]
    exact radical_dvd_self
  · rw [radical_pow _ two_ne_zero]
    simp only [x, ← Nat.cast_pow, ← Nat.cast_add_one, ← Nat.cast_mul, Int.radical_natCast,
      Int.natCast_dvd_natCast]
    exact radical_mul_pell_sq_add_one_dvd

/-- Upstreamable to core! -/
lemma _root_.Nat.one_lt_mul_iff' {m n : ℕ} : 1 < m * n ↔ 0 < m ∧ 1 < n ∨ 0 < n ∧ 1 < m := by
  rw [Nat.one_lt_mul_iff]
  lia

lemma radical_tupPell_le :
    ∃ C > 0, ∀ k, radical (∏ i, tupPell n F k i) ≤ C * ((pell (Y n F ^ 2) k).1 * Y n F) ^ 3 := by
  obtain ⟨C, Cpos, hC⟩ := radical_tupPell_dvd (n := n)
  refine ⟨C, Cpos, fun k ↦ ?_⟩
  have p₁ : 0 < ((pell (Y n F ^ 2) k).1 * Y n F : ℤ) ^ 2 - 1 := by
    rw [sub_pos, one_lt_sq_iff₀ (by positivity), ← Nat.cast_mul, Nat.one_lt_cast,
      Nat.one_lt_mul_iff']
    exact .inl ⟨pell_fst_pos, by grind [Y_lower_bound]⟩
  have p₂ : 0 < C * (((pell (Y n F ^ 2) k).1 * Y n F) ^ 2 - 1) * (pell (Y n F ^ 2) k).2 :=
    mul_pos (mul_pos Cpos p₁) (by simp [pell_snd_pos])
  apply (Int.le_of_dvd p₂ (hC k)).trans
  rw [pow_succ _ 2, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul (by lia) ?_ (by simp) (by simp [sq_nonneg])) Cpos.le
  rw [← Nat.cast_mul, Nat.cast_le]
  exact pell_snd_le_pell_fst.trans (by nlinarith [@Y_lower_bound n F])

lemma le_tupleQuality :
    ∃ C, ∀ k, .ofReal (5 * Real.log ((pell (Y n F ^ 2) k).1 * Y n F : ℕ) /
      (C + 3 * Real.log ((pell (Y n F ^ 2) k).1 * Y n F : ℕ))) ≤
    tupleQuality (tupPell n F k) := by
  obtain ⟨C, Cpos, hC⟩ := @radical_tupPell_le n F
  refine ⟨Real.log C, fun k ↦ ?_⟩
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tupPell]
  set x : ℕ := (pell (Y n F ^ 2) k).1 * Y n F
  have xpos : 0 < x := mul_pos pell_fst_pos Y_pos
  apply div_le_div₀
  · positivity
  · rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, mul_le_mul_iff_right₀ (by simp)]
    exact Real.log_le_log (by rwa [Nat.cast_pos]) (by rw [Nat.cast_le]; exact Nat.le_succ _)
  · apply Real.log_pos
    rw [← Int.cast_one, Int.cast_lt, Int.one_lt_radical_iff]
    exact strongSSC_tupPell.one_lt_natAbs_prod (by lia)
  · have cubenz : (x ^ 3 : ℝ) ≠ 0 := by
      apply pow_ne_zero
      rw [Nat.cast_ne_zero]
      lia
    rw [show (3 : ℝ) = (3 : ℕ) by rfl, ← Real.log_pow,
      ← Real.log_mul (by rw [Int.cast_ne_zero]; lia) cubenz]
    exact Real.log_le_log (mod_cast Int.radical_pos _) (mod_cast hC k)

open Filter in
lemma liminf_tupleQuality_tupPell : 5 / 3 ≤ liminf (tupleQuality ∘ tupPell n F) atTop := by
  obtain ⟨C, hC⟩ := @le_tupleQuality n F
  refine le_of_eq_of_le ?_ (liminf_le_liminf (.of_forall hC))
  have e₁ : (5 / 3 : ENNReal) = ENNReal.ofReal (5 / 3) := by
    simp [ENNReal.ofReal_div_of_pos zero_lt_three]
  rw [e₁]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  let f (k : ℕ) := Real.log ((pell (Y n F ^ 2) k).1 * Y n F : ℕ)
  change Tendsto ((fun x ↦ 5 * x / (C + 3 * x)) ∘ f) atTop (nhds (5 / 3))
  have ttf : Tendsto f atTop atTop := by
    refine Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ?_)
    refine (strictMono_pell_fst.mul_const Y_pos).tendsto_atTop
  refine Tendsto.comp ?_ ttf
  apply Tendsto.congr' (f₁ := fun x ↦ 5 / (C * x⁻¹ + 3))
  · exact (eventually_ne_atTop 0).mp (.of_forall fun _ _ ↦ by field)
  · refine tendsto_const_nhds.div ?_ three_ne_zero
    nth_rw 2 [show 3 = C * 0 + 3 by simp]
    exact (tendsto_inv_atTop_zero.const_mul _).add_const _

end Quality

end OddCase

open OddCase

/-- Theorem 1.13. -/
theorem quality_factorFreeTuples_ge_of_odd_of_disjoint
    {n : ℕ} {F : Finset ℕ} (hn : 5 ≤ n ∧ Odd n) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    5 / 3 ≤ quality (factorFreeTuples F n) := by
  rw [le_iff_exists_add'] at hn
  obtain ⟨⟨n, rfl⟩, pn⟩ := hn
  replace pn : Even n := by grind
  exact quality_ge_of_liminf_univ ⟨_, injective_tupPell⟩
    (fun k ↦ tupPell_mem_factorFreeTuples pn dF) liminf_tupleQuality_tupPell

theorem not_ramaekersConjecture_odd_ge_five {n : ℕ} (hn : 5 ≤ n ∧ Odd n) :
    ¬RamaekersConjecture n := by
  have := quality_factorFreeTuples_ge_of_odd_of_disjoint hn (Finset.disjoint_empty_right _)
    |>.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
