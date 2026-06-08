/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.RingTheory.Radical.NatInt
import LeanPool.Redhill.Common.Conjectures
import LeanPool.Redhill.General.Coprime
import LeanPool.Redhill.General.Subsum

/-!
# The general case (Theorem 1.14)
-/


namespace GeneralCase

open Filter UniqueFactorizationMonoid

variable {n : ℕ} {F : Finset ℕ}

lemma tup_mem_factorFreeTuples (hF : ∀ f ∈ F, 3 ≤ f) :
    ∀ᶠ h in atTop, tup n F h ∈ factorFreeTuples F (n + 6) := by
  simp_rw [factorFreeTuples, Set.mem_setOf_eq, eventually_and]
  exact ⟨.of_forall fun h ↦ sum_tup, strongSSC_tup, pairwiseCoprime_tup,
    .of_forall fun h f mf ↦ not_dvd_tup mf (hF f mf)⟩

lemma radical_tup_dvd : ∃ C > 0, ∀ h,
    radical (∏ i, tup n F h i) ∣ C * (X F h ^ 2 + 10 * Y F ^ 3) * (X F h ^ 2 - Y F ^ 2) := by
  simp_rw [Fin.prod_univ_add, tup_castAdd, Fin.prod_univ_six, tup_natAdd_zero,
    tup_natAdd_one, tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, tup_natAdd_five,
    ← mul_assoc, mul_neg, neg_mul, neg_neg, ← Nat.cast_prod, ← Nat.cast_mul]
  set D := (∏ i : Fin n, primeChain (100 * Y F ^ 6) i.1) * (VW n F).v * (VW n F).w
  have Dpos : 0 < D := by
    iterate 2 refine Nat.mul_pos ?_ (by grind [(VW n F).m_lt_v, (VW n F).eq_add])
    exact Finset.prod_pos fun i _ ↦ by grind [primeChain_gt]
  refine ⟨D * (10 * Y F - 1) * (Y F + 1), ?_, fun h ↦ ?_⟩
  · refine mul_pos (mul_pos ?_ ?_) ?_ <;> grind [Y_pos]
  · iterate 2 rw [mul_right_comm _ (_ ^ 2)]
    rw [sq_sub_sq, mul_right_comm, ← mul_assoc]
    iterate 3 refine radical_mul_dvd.trans (mul_dvd_mul ?_ (radical_pow_dvd.trans radical_dvd_self))
    refine radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self ?_)
    rw [X, Nat.cast_pow, ← pow_mul, Nat.cast_add_one]
    exact radical_pow_dvd.trans radical_dvd_self

lemma radical_tup_le : ∃ C > 0, ∀ h, radical (∏ i, tup n F h i) ≤ C * X F h ^ 4 := by
  obtain ⟨C, Cpos, hC⟩ := @radical_tup_dvd n F
  have Ypos : 0 < Y F := Y_pos
  refine ⟨10 * Y F ^ 3 * C, by positivity, fun h ↦ (Int.le_of_dvd ?_ (hC h)).trans ?_⟩
  · apply mul_pos (mul_pos Cpos (by positivity))
    rw [sub_pos]
    exact_mod_cast Nat.pow_lt_pow_left Y_lt_X two_ne_zero
  · rw [show 10 * (Y F : ℤ) ^ 3 * C * X F h ^ 4 =
      C * (X F h ^ 2 * (10 * Y F ^ 3)) * X F h ^ 2 by ring]
    gcongr
    · rw [sub_nonneg]
      exact_mod_cast Nat.pow_le_pow_left Y_lt_X.le _
    · apply add_le_mul <;> norm_cast
      · exact (Nat.le_self_pow two_ne_zero _).trans' (by grind [Y_lt_X])
      · calc
          _ ≤ 10 * Y F := by lia
          _ ≤ _ := mul_le_mul_right (Nat.le_self_pow three_ne_zero _) 10
    · lia

lemma le_tupleQuality : ∃ C, ∀ᶠ h in atTop,
    .ofReal (5 * Real.log (X F h) / (C + 4 * Real.log (X F h))) ≤ tupleQuality (tup n F h) := by
  obtain ⟨C, Cpos, hC⟩ := @radical_tup_le n F
  refine ⟨Real.log C, ?_⟩
  filter_upwards [@maxAbs_tup n F, @strongSSC_tup n F] with h hma hssc
  apply ENNReal.ofReal_le_ofReal
  rw [hma]
  apply div_le_div₀
  · positivity
  · rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, mul_le_mul_iff_right₀ (by simp)]
    exact Real.log_le_log (by grind [Nat.cast_pos, Y_lt_X]) (mod_cast Nat.le_add_right ..)
  · apply Real.log_pos
    rw [← Int.cast_one, Int.cast_lt, Int.one_lt_radical_iff]
    exact hssc.one_lt_natAbs_prod (by lia)
  · rw [show (4 : ℝ) = (4 : ℕ) by rfl, ← Real.log_pow,
      ← Real.log_mul (mod_cast Cpos.ne') (mod_cast pow_ne_zero 4 (by grind [Y_lt_X]))]
    exact Real.log_le_log (mod_cast Int.radical_pos _) (mod_cast hC h)

lemma liminf_tupleQuality_tup : 5 / 4 ≤ liminf (tupleQuality ∘ tup n F) atTop := by
  obtain ⟨C, hC⟩ := @le_tupleQuality n F
  refine le_of_eq_of_le ?_ (liminf_le_liminf hC)
  have e₁ : (5 / 4 : ENNReal) = ENNReal.ofReal (5 / 4) := by
    simp [ENNReal.ofReal_div_of_pos zero_lt_four]
  rw [e₁]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  let f (h : ℕ) := Real.log (X F h)
  change Tendsto ((fun x ↦ 5 * x / (C + 4 * x)) ∘ f) atTop (nhds (5 / 4))
  have ttf : Tendsto f atTop atTop :=
    Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop.comp <|
      tendsto_atTop.mpr fun B ↦ (eventually_X_gt fun _ ↦ B).mono fun _ ↦ Nat.le_of_succ_le
  refine Tendsto.comp ?_ ttf
  apply Tendsto.congr' (f₁ := fun x ↦ 5 / (C * x⁻¹ + 4))
  · exact (eventually_ne_atTop 0).mp (.of_forall fun _ _ ↦ by field)
  · refine tendsto_const_nhds.div ?_ four_ne_zero
    nth_rw 2 [show 4 = C * 0 + 4 by simp]
    exact (tendsto_inv_atTop_zero.const_mul _).add_const _

end GeneralCase

open GeneralCase

/-- Theorem 1.14. -/
theorem quality_factorFreeTuples_ge {n : ℕ} {F : Finset ℕ} (hn : 6 ≤ n) (hF : ∀ f ∈ F, 3 ≤ f) :
    5 / 4 ≤ quality (factorFreeTuples F n) := by
  rw [le_iff_exists_add'] at hn
  obtain ⟨n, rfl⟩ := hn
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (tup_mem_factorFreeTuples (n := n) hF)
  refine quality_ge_of_liminf _ _ (Set.Ici_infinite (N₀ + 1))
    (fun i mi j mj e ↦ ?_) (fun h (hh : N₀ < h) ↦ hN₀ h hh.le) liminf_tupleQuality_tup
  replace e := congr($e (Fin.natAdd n 5))
  simp_rw [tup_natAdd_five, neg_inj] at e
  norm_cast at e
  rw [pow_left_inj (by decide), add_left_inj, X, X, Nat.pow_right_inj (by grind [Y_pos])] at e
  grind [Nat.factorial_inj']

theorem not_ramaekersConjecture_ge_six {n : ℕ} (hn : 6 ≤ n) : ¬RamaekersConjecture n := by
  have := quality_factorFreeTuples_ge (F := ∅) hn (by simp)
    |>.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
