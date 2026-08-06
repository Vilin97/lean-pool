/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Reduction

/-!
# Transpositions

This file characterizes the behavior of involutions $\sigma_S$ under the operations $\star$ and
$\triangleleft$. Its main purpose is to prove Theorem 8.7 from
[An extended Demazure product](https://arxiv.org/abs/2206.14227), as well as the last sentences of
Theorem A and the theorem labeled `thm:resL`, which describe the special case of $\sigma_S$ for
$S = \{n\}$ a singleton.
-/

namespace LeanPool.DemazureProduct


namespace Transpositions

/-- A set of integers contains no consecutive pair. This asymmetric formulation
is enough on `ℤ`: applying it to `n - 1` rules out `n - 1, n`. -/
def NoConsecutive (S : Set ℤ) : Prop :=
  ∀ n : ℤ, n ∈ S → n + 1 ∉ S

/-- A singleton has no consecutive pair. -/
private lemma noConsecutive_singleton (n : ℤ) : NoConsecutive ({n} : Set ℤ) := by
  -- Proof written by GPT 5.5.
  intro m hm hsucc
  simp_all

/-- The underlying function of $\sigma_S$: swap $n$ with $n + 1$ for every
$n \in S$, and fix all other integers. -/
noncomputable def sigmaFun (S : Set ℤ) (n : ℤ) : ℤ :=
  open Classical in
  if n ∈ S then n + 1 else if n - 1 ∈ S then n - 1 else n

private lemma sigmaFun_of_mem {S : Set ℤ} {n : ℤ} (hn : n ∈ S) :
    sigmaFun S n = n + 1 := by
  -- Proof written by GPT 5.5.
  simp only [sigmaFun, hn, if_true]

private lemma sigmaFun_of_pred_mem {S : Set ℤ} (hS : NoConsecutive S) {n : ℤ}
    (hn : n - 1 ∈ S) :
    sigmaFun S n = n - 1 := by
  -- Proof written by GPT 5.5.
  have hmem : n ∉ S := by
    intro h
    exact hS (n - 1) hn (by simpa only [sub_add_cancel] using h)
  simp only [sigmaFun, hmem, if_false, hn, if_true]

private lemma sigmaFun_of_not_mem {S : Set ℤ} {n : ℤ} (hn : n ∉ S) (hpred : n - 1 ∉ S) :
    sigmaFun S n = n := by
  -- Proof written by GPT 5.5.
  simp only [sigmaFun, hn, if_false, hpred]

private lemma not_succ_mem_of_noConsecutive {S : Set ℤ} (hS : NoConsecutive S)
    {n : ℤ} (hn : n ∈ S) : n + 1 ∉ S :=
  hS n hn

private lemma not_pred_mem_of_noConsecutive {S : Set ℤ} (hS : NoConsecutive S)
    {n : ℤ} (hn : n ∈ S) : n - 1 ∉ S := by
  -- Proof written by GPT 5.5.
  intro hpred
  have hbad := hS (n - 1) hpred
  simp_all

private lemma sigmaFun_involutive {S : Set ℤ} (hS : NoConsecutive S) :
    Function.Involutive (sigmaFun S) := by
  -- Proof written by GPT 5.5.
  intro n
  by_cases hn : n ∈ S
  · have hsucc : n + 1 ∉ S := not_succ_mem_of_noConsecutive hS hn
    simp only [sigmaFun, hn, if_true, hsucc, if_false, add_sub_cancel_right]
  · by_cases hpred : n - 1 ∈ S
    · simp only [sigmaFun, hn, if_false, hpred, if_true]
      omega
    · simp only [sigmaFun, hn, if_false, hpred]

private lemma sigmaFun_injective {S : Set ℤ} (hS : NoConsecutive S) :
    Function.Injective (sigmaFun S) :=
  (sigmaFun_involutive hS).injective

private lemma sigmaFun_surjective {S : Set ℤ} (hS : NoConsecutive S) :
    Function.Surjective (sigmaFun S) :=
  (sigmaFun_involutive hS).surjective

private lemma sigmaFun_asp (S : Set ℤ) : isAsp (sigmaFun S) := by
  -- Proof written by GPT 5.5.
  apply Set.Finite.subset (Set.finite_empty (α := ℤ))
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  exfalso
  unfold sigmaFun at hn
  split_ifs at hn
  · nlinarith [sq_nonneg (2 * n + 1)]
  · nlinarith [sq_nonneg (2 * n - 1)]
  · nlinarith [sq_nonneg n]

/-- The ASP permutation $\sigma_S$, exchanging each adjacent pair $n, n + 1$
for $n \in S$. -/
noncomputable def sigma (S : Set ℤ) (hS : NoConsecutive S) : AspPerm where
  func := sigmaFun S
  bijective := ⟨sigmaFun_injective hS, sigmaFun_surjective hS⟩
  asp := sigmaFun_asp S

@[simp] private lemma sigma_apply (S : Set ℤ) (hS : NoConsecutive S) (n : ℤ) :
    sigma S hS n = sigmaFun S n := rfl

private lemma sigma_apply_of_mem {S : Set ℤ} {hS : NoConsecutive S} {n : ℤ}
    (hn : n ∈ S) : sigma S hS n = n + 1 :=
  sigmaFun_of_mem hn

private lemma sigma_apply_of_pred_mem {S : Set ℤ} {hS : NoConsecutive S} {n : ℤ}
    (hn : n - 1 ∈ S) : sigma S hS n = n - 1 :=
  sigmaFun_of_pred_mem hS hn

private lemma sigma_apply_of_not_mem {S : Set ℤ} {hS : NoConsecutive S} {n : ℤ}
    (hn : n ∉ S) (hpred : n - 1 ∉ S) : sigma S hS n = n :=
  sigmaFun_of_not_mem hn hpred

private lemma sigma_involutive {S : Set ℤ} (hS : NoConsecutive S) :
    Function.Involutive (sigma S hS) :=
  sigmaFun_involutive hS

@[simp] private lemma sigma_inv {S : Set ℤ} (hS : NoConsecutive S) :
    (sigma S hS)⁻¹ = sigma S hS := by
  -- Proof written by GPT 5.5.
  apply AspPerm.ext.mpr
  funext n
  change Function.invFun (sigma S hS).func n = sigma S hS n
  apply (sigma S hS).injective
  rw [Function.rightInverse_invFun (sigma S hS).surjective n]
  exact Eq.symm <| sigma_involutive hS n

@[simp] lemma sigma_chi (S : Set ℤ) (hS : NoConsecutive S) :
    (sigma S hS).χ = 0 := by
  -- Proof written by GPT 5.5.
  have hχ := AspPerm.chi_dual (sigma S hS)
  rw [sigma_inv hS] at hχ
  omega

private lemma sigmaFun_bound (S : Set ℤ) (n : ℤ) :
    n - 1 ≤ sigmaFun S n ∧ sigmaFun S n ≤ n + 1 := by
  -- Proof written by GPT 5.5.
  unfold sigmaFun
  split_ifs <;> omega

private lemma sigma_apply_le_succ (S : Set ℤ) (hS : NoConsecutive S) (n : ℤ) :
    sigma S hS n ≤ n + 1 := by
  -- Proof written by GPT 5.5.
  change sigmaFun S n ≤ n + 1
  exact (sigmaFun_bound S n).2

private lemma pred_le_sigma_apply (S : Set ℤ) (hS : NoConsecutive S) (n : ℤ) :
    n - 1 ≤ sigma S hS n := by
  -- Proof written by GPT 5.5.
  change n - 1 ≤ sigmaFun S n
  exact (sigmaFun_bound S n).1

private lemma sigma_s_zero_of_lt (S : Set ℤ) (hS : NoConsecutive S) {a b : ℤ}
    (hab : a < b) :
    (sigma S hS).s a b = 0 := by
  -- Proof written by GPT 5.5.
  rw [(sigma S hS).s_eq_se_card]
  simp only [Nat.cast_eq_zero, Finset.card_eq_zero]
  ext n
  simp only [AspPerm.mem_se, ge_iff_le, Finset.notMem_empty, iff_false, not_and, not_lt]
  intro hbn
  have hge := pred_le_sigma_apply S hS n
  omega

private lemma sigma_s_of_gt (S : Set ℤ) (hS : NoConsecutive S) {a b : ℤ}
    (hba : b < a) :
    (sigma S hS).s a b = a - b := by
  -- Proof written by GPT 5.5.
  have hzero : (sigma S hS).s b a = 0 :=
    sigma_s_zero_of_lt S hS hba
  have hs := (sigma S hS).s_eq a b
  simp_all

private lemma sigma_s_diag (S : Set ℤ) (hS : NoConsecutive S) (b : ℤ) :
    (sigma S hS).s b b = Utils.oneIf (b - 1 ∈ S) := by
  -- Proof written by GPT 5.5.
  by_cases hb : b - 1 ∈ S
  · rw [(sigma S hS).s_eq_se_card]
    have hset : (sigma S hS).seFinset b b = {b} := by
      ext n
      simp only [AspPerm.mem_se, ge_iff_le, Finset.mem_singleton]
      constructor
      · rintro ⟨hbn, hσn⟩
        have hge := pred_le_sigma_apply S hS n
        omega
      · intro hn
        subst n
        constructor
        · omega
        · rw [sigma_apply_of_pred_mem (S := S) (hS := hS) hb]
          omega
    simp_all
  · rw [(sigma S hS).s_eq_se_card]
    have hset : (sigma S hS).seFinset b b = ∅ := by
      ext n
      simp only [AspPerm.mem_se, ge_iff_le, Finset.notMem_empty, iff_false, not_and,
        not_lt]
      intro hbn
      rcases eq_or_lt_of_le hbn with rfl | hlt
      · by_cases hbmem : b ∈ S
        · rw [sigma_apply_of_mem (S := S) (hS := hS) hbmem]
          omega
        · rw [sigma_apply_of_not_mem (S := S) (hS := hS) hbmem hb]
      · have hge := pred_le_sigma_apply S hS n
        omega
    simp_all

/-- The slipface of $\sigma_S$ is the identity slipface, incremented by 1 on diagonal entries
corresponding to the inversions.
-/
private lemma sigma_slipface (S : Set ℤ) (hS : NoConsecutive S) (a b : ℤ) :
    (sigma S hS).s a b =
      max 0 (a - b) + Utils.oneIf (a = b ∧ a - 1 ∈ S) := by
  -- Proof written by GPT 5.5.
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [show (sigma S hS).s a b = 0 by
      simpa using sigma_s_zero_of_lt S hS hab]
    have hmax : max 0 (a - b) = 0 := max_eq_left (by omega)
    have hne : a ≠ b := ne_of_lt hab
    simp only [hmax, Utils.oneIf, hne, false_and, if_false, add_zero]
  · subst a
    rw [show (sigma S hS).s b b = Utils.oneIf (b - 1 ∈ S) by
      simpa using sigma_s_diag S hS b]
    simp only [sub_self, max_eq_left (by omega : (0 : ℤ) ≤ 0), true_and, zero_add]
  · rw [show (sigma S hS).s a b = a - b by
      simpa using sigma_s_of_gt S hS hba]
    have hmax : max 0 (a - b) = a - b := max_eq_right (by omega)
    have hne : a ≠ b := ne_of_gt hba
    simp only [hmax, Utils.oneIf, hne, false_and, if_false, add_zero]

private lemma bend_set_sigma_cases (S : Set ℤ) (hS : NoConsecutive S) (b : ℤ) :
    SlipFace.bendSet (sigma S hS).s b =
      {l : ℤ |
        (b - 1 ∉ S ∧ l = b) ∨
          (b - 1 ∈ S ∧ (l = b - 1 ∨ l = b + 1))} := by
  -- Proof written by GPT 5.5.
  ext l
  have hmem_iff :
      l ∈ SlipFace.bendSet (sigma S hS).s b ↔
        sigma S hS (l - 1) < b ∧ b ≤ sigma S hS l := by
    simp only [SlipFace.bendSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hflat, hright⟩
      constructor
      · have hflat' :
            (sigma S hS).s ((l - 1) + 1) b = (sigma S hS).s (l - 1) b := by
          simpa only [sub_add_cancel] using hflat.symm
        have hcut := ((sigma S hS).a_step_eq_iff (l - 1) b).mp hflat'
        simpa only [sigma_inv hS] using hcut
      · have hnot : ¬ (sigma S hS)⁻¹ l < b := by
          intro hlt
          have hflat' : (sigma S hS).s (l + 1) b = (sigma S hS).s l b :=
            ((sigma S hS).a_step_eq_iff l b).mpr hlt
          exact hright hflat'.symm
        simpa only [sigma_inv hS] using not_lt.mp hnot
    · rintro ⟨hleft, hright⟩
      constructor
      · have hleft' : (sigma S hS)⁻¹ (l - 1) < b := by
          simpa only [sigma_inv hS] using hleft
        have hflat :
            (sigma S hS).s ((l - 1) + 1) b = (sigma S hS).s (l - 1) b :=
          ((sigma S hS).a_step_eq_iff (l - 1) b).mpr hleft'
        simpa only [sub_add_cancel] using hflat.symm
      · intro hsame
        have hlt : (sigma S hS)⁻¹ l < b :=
          ((sigma S hS).a_step_eq_iff l b).mp hsame.symm
        have hright' : b ≤ (sigma S hS)⁻¹ l := by
          simpa only [sigma_inv hS] using hright
        exact not_lt_of_ge hright' hlt
  rw [hmem_iff]
  simp only [Set.mem_ofPred_eq]
  by_cases hbprev : b - 1 ∈ S
  · simp only [hbprev, not_true_eq_false, false_and, true_and, false_or]
    have hσbprev : sigma S hS (b - 1) = b := by
      simpa only [sub_add_cancel] using
        (sigma_apply_of_mem (S := S) (hS := hS) (n := b - 1) hbprev)
    constructor
    · rintro ⟨hleft, hright⟩
      have hlower : b - 1 ≤ l := by
        have hle := sigma_apply_le_succ S hS l
        omega
      have hupper : l ≤ b + 1 := by
        have hle := pred_le_sigma_apply S hS (l - 1)
        omega
      have hne : l ≠ b := by
        intro hl
        simp_all
      omega
    · rintro (rfl | rfl)
      · constructor
        · have hle := sigma_apply_le_succ S hS (b - 1 - 1)
          omega
        · rw [hσbprev]
      · constructor
        · have hσb : sigma S hS (b + 1 - 1) = b - 1 := by
            simpa only [add_sub_cancel_right] using
              (sigma_apply_of_pred_mem (S := S) (hS := hS) (n := b) hbprev)
          simp_all
        · have hle := pred_le_sigma_apply S hS (b + 1)
          omega
  · simp only [hbprev, false_and, not_false_eq_true, true_and, or_false]
    have hσbprev_lt : sigma S hS (b - 1) < b := by
      by_cases hbprevprev : b - 2 ∈ S
      · have hσ : sigma S hS (b - 1) = b - 2 := by
          have hbpredpred : b - 1 - 1 ∈ S := by
            have harg : b - 1 - 1 = b - 2 := by ring
            rwa [harg]
          have hraw := sigma_apply_of_pred_mem (S := S) (hS := hS) (n := b - 1) hbpredpred
          omega
        simp_all
      · have hσ : sigma S hS (b - 1) = b - 1 := by
          have hbprevprev' : b - 1 - 1 ∉ S := by
            intro hmem
            exact hbprevprev (by
              have : b - 1 - 1 = b - 2 := by ring
              rwa [this] at hmem)
          exact sigma_apply_of_not_mem hbprev hbprevprev'
        simp_all
    have hb_le_σb : b ≤ sigma S hS b := by
      by_cases hb : b ∈ S
      · have hσ : sigma S hS b = b + 1 := sigma_apply_of_mem hb
        simp_all
      · have hσ : sigma S hS b = b := sigma_apply_of_not_mem hb hbprev
        rw [hσ]
    constructor
    · rintro ⟨hleft, hright⟩
      have hlower : b - 1 ≤ l := by
        have hle := sigma_apply_le_succ S hS l
        omega
      have hupper : l ≤ b + 1 := by
        have hle := pred_le_sigma_apply S hS (l - 1)
        omega
      rcases (by omega : l = b - 1 ∨ l = b ∨ l = b + 1) with rfl | rfl | rfl
      · omega
      · rfl
      · have hleft' : sigma S hS b < b := by
          simpa only [add_sub_cancel_right] using hleft
        omega
    · simp_all

/-- The bend set for $\sigma_S$ is the singleton $\{b\}$ when $b - 1 \notin S$.
This is one case of the computation of `L` in the proof of Lemma 3.17 (`lem:starTrans`) in
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/6.* -/
private lemma bend_set_sigma_of_not_pred_mem (S : Set ℤ) (hS : NoConsecutive S) {b : ℤ}
    (hb : b - 1 ∉ S) :
    SlipFace.bendSet (sigma S hS).s b = {b} := by
  -- Proof written by GPT 5.5.
  rw [bend_set_sigma_cases S hS b]
  simp_all

/-- The bend set for $\sigma_S$ is $\{b - 1, b + 1\}$ when $b - 1 \in S$.
This is one case of the computation of `L` in the proof of Lemma 3.17 (`lem:starTrans`) in
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/6.* -/
private lemma bend_set_sigma_of_pred_mem (S : Set ℤ) (hS : NoConsecutive S) {b : ℤ}
    (hb : b - 1 ∈ S) :
    SlipFace.bendSet (sigma S hS).s b = {l : ℤ | l = b - 1 ∨ l = b + 1} := by
  -- Proof written by GPT 5.5.
  rw [bend_set_sigma_cases S hS b]
  simp_all

@[simp] private lemma sigma_sf_dual (S : Set ℤ) (hS : NoConsecutive S) :
    (sigma S hS).s.dual = (sigma S hS).s := by
  -- Proof written by GPT 5.5.
  rw [AspPerm.s_dual, sigma_inv hS]

private lemma star_step_min_eq_oneIf (s : SlipFace) (a b : ℤ) :
    min (s a (b - 1)) (s a (b + 1) + 1) =
      s a b + Utils.oneIf (s a (b - 1) > s a b ∧ s a b = s a (b + 1)) := by
  -- Proof written by GPT 5.5.
  have hprev : s a b ≤ s a (b - 1) ∧ s a (b - 1) ≤ s a b + 1 := by
    simpa only [sub_add_cancel] using s.b_step a (b - 1)
  have hnext : s a (b + 1) ≤ s a b ∧ s a b ≤ s a (b + 1) + 1 :=
    s.b_step a b
  by_cases hcond : s a (b - 1) > s a b ∧ s a b = s a (b + 1)
  · have hone :
        Utils.oneIf (s a (b - 1) > s a b ∧ s a b = s a (b + 1)) = 1 := by
      simp only [Utils.oneIf]
      exact if_pos hcond
    have hleft : s a (b - 1) = s a b + 1 := by omega
    simp_all
  · have hzero :
        Utils.oneIf (s a (b - 1) > s a b ∧ s a b = s a (b + 1)) = 0 := by
      simp_all
    rw [hzero, add_zero]
    by_cases hleft : s a (b - 1) = s a b
    · simp_all
    · have hleft_gt : s a (b - 1) > s a b := by omega
      have hnext_ne : s a b ≠ s a (b + 1) := by
        simp_all
      have hright : s a (b + 1) + 1 = s a b := by omega
      simp_all

private lemma lres_step_max_eq_oneIf (s : SlipFace) (a b : ℤ) :
    max (s a (b - 1) - 1) (s a (b + 1)) =
      s a b - Utils.oneIf (s a (b - 1) = s a b ∧ s a b > s a (b + 1)) := by
  -- Proof written by GPT 5.5.
  have hprev : s a b ≤ s a (b - 1) ∧ s a (b - 1) ≤ s a b + 1 := by
    simpa only [sub_add_cancel] using s.b_step a (b - 1)
  have hnext : s a (b + 1) ≤ s a b ∧ s a b ≤ s a (b + 1) + 1 :=
    s.b_step a b
  by_cases hcond : s a (b - 1) = s a b ∧ s a b > s a (b + 1)
  · have hone :
        Utils.oneIf (s a (b - 1) = s a b ∧ s a b > s a (b + 1)) = 1 := by
      simp_all
    have hleft : s a (b - 1) - 1 = s a b - 1 := by omega
    have hright : s a (b + 1) = s a b - 1 := by omega
    rw [hone, hleft, hright, max_self]
  · have hzero :
        Utils.oneIf (s a (b - 1) = s a b ∧ s a b > s a (b + 1)) = 0 := by
      simp_all
    rw [hzero, sub_zero]
    by_cases hleft : s a (b - 1) = s a b
    · have hnot_gt : ¬ s a b > s a (b + 1) := by
        simp_all
      have hright : s a (b + 1) = s a b := by omega
      simp_all
    · have hleft' : s a (b - 1) - 1 = s a b := by omega
      simp_all

/-- The slipface $s \star \sigma_S$ is given by adding 1 to a certain pattern of entries of $s$.
The expression `Utils.oneIf P` is the indicator $\delta(P)$ in
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
*Lemma 3.17 (`lem:starTrans`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/6.* -/
theorem sf_star_sigma (S : Set ℤ) (hS : NoConsecutive S) (s : SlipFace) (a b : ℤ) :
    (s ⋆ (sigma S hS).s) a b =
        s a b
          + Utils.oneIf (b - 1 ∈ S ∧ s a (b - 1) > s a b ∧ s a b = s a (b + 1)) := by
  -- Proof written by GPT 5.5.
  by_cases hb : b - 1 ∈ S
  · have ht_left : (sigma S hS).s (b - 1) b = 0 := by
      rw [sigma_slipface S hS (b - 1) b]
      simp_all
    have ht_right : (sigma S hS).s (b + 1) b = 1 := by
      rw [sigma_slipface S hS (b + 1) b]
      simp_all
    have hstar_min :
        (s ⋆ (sigma S hS).s) a b =
          min (s a (b - 1)) (s a (b + 1) + 1) := by
      have hle_left : (s ⋆ (sigma S hS).s) a b ≤ s a (b - 1) := by
        simpa only [ht_left, add_zero] using
          SlipFace.star_val_le s (sigma S hS).s a b (b - 1)
      have hle_right : (s ⋆ (sigma S hS).s) a b ≤ s a (b + 1) + 1 := by
        simpa only [ht_right] using
          SlipFace.star_val_le s (sigma S hS).s a b (b + 1)
      have hle_min :
          (s ⋆ (sigma S hS).s) a b ≤ min (s a (b - 1)) (s a (b + 1) + 1) :=
        le_min hle_left hle_right
      obtain ⟨l, hl, hval⟩ := SlipFace.bend_set_witness s (sigma S hS).s a b
      rw [bend_set_sigma_of_pred_mem S hS hb] at hl
      simp only [Set.mem_ofPred_eq] at hl
      have hmin_le :
          min (s a (b - 1)) (s a (b + 1) + 1) ≤ (s ⋆ (sigma S hS).s) a b := by
        rcases hl with rfl | rfl
        · simp_all
        · simp_all
      exact le_antisymm hle_min hmin_le
    rw [hstar_min, star_step_min_eq_oneIf]
    simp only [hb, true_and]
  · obtain ⟨l, hl, hval⟩ := SlipFace.bend_set_witness s (sigma S hS).s a b
    rw [bend_set_sigma_of_not_pred_mem S hS hb] at hl
    simp only [Set.mem_singleton_iff] at hl
    subst l
    have ht_diag : (sigma S hS).s b b = 0 := by
      rw [sigma_slipface S hS b b]
      simp only [sub_self, max_self, true_and, hb, Utils.oneIf, if_false, add_zero]
    simp_all

/-- A formula for $s_\alpha \star \sigma_S$, specializing the more general `sf_star_sigma`.
*Lemma 3.17 (`lem:starTrans`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/6.* -/
theorem asp_star_sigma_sf (S : Set ℤ) (hS : NoConsecutive S) (α : AspPerm) (a b : ℤ) :
    (α.s ⋆ (sigma S hS).s) a b =
      α.s a b + Utils.oneIf (b - 1 ∈ S ∧ α (b - 1) < a ∧ a ≤ α b) := by
  -- Proof written by GPT 5.5.
  rw [sf_star_sigma S hS α.s a b]
  have hiff :
      (b - 1 ∈ S ∧ α.s a (b - 1) > α.s a b ∧ α.s a b = α.s a (b + 1)) ↔
        (b - 1 ∈ S ∧ α (b - 1) < a ∧ a ≤ α b) := by
    constructor
    · rintro ⟨hb, hprev, hnext⟩
      exact ⟨hb,
        (α.b_step_lt_iff a (b - 1)).mp (by simpa only [sub_add_cancel] using hprev),
        (α.b_step_eq_iff a b).mp hnext.symm⟩
    · rintro ⟨hb, hprev, hnext⟩
      exact ⟨hb,
        by simpa only [sub_add_cancel] using (α.b_step_lt_iff a (b - 1)).mpr hprev,
        ((α.b_step_eq_iff a b).mpr hnext).symm⟩
  rw [Utils.oneIf_congr hiff]

/-- A formula for $s \triangleleft \sigma_S$.

The expression `Utils.oneIf P` is the indicator $\delta(P)$ in
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
*Lemma 3.17 (`lem:starTrans`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/6.* -/
theorem sf_lres_sigma (S : Set ℤ) (hS : NoConsecutive S)
    (s : SlipFace) (a b : ℤ) :
    (s ◃ (sigma S hS).s) a b =
        s a b
          - Utils.oneIf (b - 1 ∈ S ∧ s a (b - 1) = s a b ∧ s a b > s a (b + 1)) := by
  -- Proof written by GPT 5.5.
  by_cases hb : b - 1 ∈ S
  · have ht_left : (sigma S hS).s.dual b (b - 1) = 1 := by
      rw [sigma_sf_dual S hS, sigma_slipface S hS b (b - 1)]
      have hmax : max 0 (b - (b - 1)) = 1 := by
        simp_all
      have hne : b ≠ b - 1 := ne_of_gt (sub_one_lt b)
      simp only [hmax, hne, false_and, Utils.oneIf, if_false, add_zero]
    have ht_right : (sigma S hS).s.dual b (b + 1) = 0 := by
      rw [sigma_sf_dual S hS, sigma_slipface S hS b (b + 1)]
      simp_all
    have hlres_max :
        (s ◃ (sigma S hS).s) a b =
          max (s a (b - 1) - 1) (s a (b + 1)) := by
      have hge_left :
          s a (b - 1) - 1 ≤ (s ◃ (sigma S hS).s) a b := by
        simpa only [SlipFace.lres_func_eq, ht_left] using
          SlipFace.lres_val_ge s (sigma S hS).s a b (b - 1)
      have hge_right :
          s a (b + 1) ≤ (s ◃ (sigma S hS).s) a b := by
        simpa only [SlipFace.lres_func_eq, ht_right, sub_zero] using
          SlipFace.lres_val_ge s (sigma S hS).s a b (b + 1)
      have hmax_le :
          max (s a (b - 1) - 1) (s a (b + 1)) ≤
            (s ◃ (sigma S hS).s) a b :=
        max_le hge_left hge_right
      obtain ⟨l, hl, hval⟩ := SlipFace.bend_set_witness_lres s (sigma S hS).s a b
      rw [bend_set_sigma_of_pred_mem S hS hb] at hl
      simp only [Set.mem_ofPred_eq] at hl
      have hlres_le :
          (s ◃ (sigma S hS).s) a b ≤ max (s a (b - 1) - 1) (s a (b + 1)) := by
        rcases hl with rfl | rfl
        · simp_all
        · simp_all
      exact le_antisymm hlres_le hmax_le
    rw [hlres_max, lres_step_max_eq_oneIf]
    simp only [hb, true_and]
  · obtain ⟨l, hl, hval⟩ := SlipFace.bend_set_witness_lres s (sigma S hS).s a b
    rw [bend_set_sigma_of_not_pred_mem S hS hb] at hl
    simp only [Set.mem_singleton_iff] at hl
    subst l
    have ht_diag : (sigma S hS).s.dual b b = 0 := by
      rw [sigma_sf_dual S hS, sigma_slipface S hS b b]
      simp only [sub_self, max_self, true_and, hb, Utils.oneIf, if_false, add_zero]
    simp_all

/-- A formula for $s_\alpha \triangleleft \sigma_S$. This is the ASP specialization of
`sf_residual_sigma`. *Lemma 3.17 (`lem:starTrans`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 6/6.* -/
theorem asp_residual_sigma_sf (S : Set ℤ) (hS : NoConsecutive S)
    (α : AspPerm) (a b : ℤ) :
    (α.s ◃ (sigma S hS).s) a b =
      α.s a b - Utils.oneIf (b - 1 ∈ S ∧ α b < a ∧ a ≤ α (b - 1)) := by
  -- Proof written by GPT 5.5.
  rw [sf_lres_sigma S hS α.s a b]
  have hiff :
      (b - 1 ∈ S ∧ α.s a (b - 1) = α.s a b ∧ α.s a b > α.s a (b + 1)) ↔
        (b - 1 ∈ S ∧ α b < a ∧ a ≤ α (b - 1)) := by
    constructor
    · rintro ⟨hb, hprev, hnext⟩
      exact ⟨hb, (α.b_step_lt_iff a b).mp hnext,
        (α.b_step_eq_iff a (b - 1)).mp (by simpa only [sub_add_cancel] using hprev.symm)⟩
    · rintro ⟨hb, hnext, hprev⟩
      exact ⟨hb,
        by
          have hflat := (α.b_step_eq_iff a (b - 1)).mpr hprev
          simpa only [sub_add_cancel] using hflat.symm,
        (α.b_step_lt_iff a b).mpr hnext⟩
  rw [Utils.oneIf_congr hiff]

/-- The subset of $S$ where right multiplication by $\sigma_S$ should increase the
permutation in Bruhat order. -/
def risingSet (α : AspPerm) (S : Set ℤ) : Set ℤ :=
  {n : ℤ | n ∈ S ∧ α n < α (n + 1)}

/-- The subset of $S$ where right multiplication by $\sigma_S$ should decrease the
permutation in Bruhat order. -/
def fallingSet (α : AspPerm) (S : Set ℤ) : Set ℤ :=
  {n : ℤ | n ∈ S ∧ α (n + 1) < α n}

private lemma noConsecutive_subset {S T : Set ℤ} (hS : NoConsecutive S) (hT : T ⊆ S) :
    NoConsecutive T := by
  -- Proof written by GPT 5.5.
  intro n hn hsucc
  exact hS n (hT hn) (hT hsucc)

private lemma noConsecutive_risingSet (α : AspPerm) {S : Set ℤ} (hS : NoConsecutive S) :
    NoConsecutive (risingSet α S) :=
  noConsecutive_subset hS (by intro n hn; exact hn.1)

private lemma noConsecutive_fallingSet (α : AspPerm) {S : Set ℤ} (hS : NoConsecutive S) :
    NoConsecutive (fallingSet α S) :=
  noConsecutive_subset hS (by intro n hn; exact hn.1)

/-- The rising and falling parts partition $S$. -/
private lemma risingSet_union_fallingSet (α : AspPerm) (S : Set ℤ) :
    risingSet α S ∪ fallingSet α S = S := by
  -- Proof written by GPT 5.5.
  ext n
  simp only [risingSet, fallingSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    rcases lt_trichotomy (α n) (α (n + 1)) with hlt | heq | hgt
    · exact Or.inl ⟨hn, hlt⟩
    · exact False.elim ((by omega : n ≠ n + 1) (α.injective heq))
    · exact Or.inr ⟨hn, hgt⟩

/-- The falling and rising parts partition $S$. -/
private lemma fallingSet_union_risingSet (α : AspPerm) (S : Set ℤ) :
    fallingSet α S ∪ risingSet α S = S := by
  -- Proof written by GPT 5.5.
  rw [Set.union_comm, risingSet_union_fallingSet α S]

/-- The rising and falling parts of $S$ are disjoint. -/
private lemma disjoint_risingSet_fallingSet (α : AspPerm) (S : Set ℤ) :
    Disjoint (risingSet α S) (fallingSet α S) := by
  -- Proof written by GPT 5.5.
  apply Set.disjoint_left.mpr
  intro n hnR hnF
  simp only [risingSet, fallingSet, Set.mem_ofPred_eq] at hnR hnF
  omega

private lemma risingSet_singleton_of_lt (α : AspPerm) (n : ℤ)
    (h : α n < α (n + 1)) :
    risingSet α ({n} : Set ℤ) = {n} := by
  -- Proof written by GPT 5.5.
  ext m
  constructor
  · intro hm
    exact hm.1
  · intro hm
    rw [Set.mem_singleton_iff] at hm
    subst m
    exact ⟨rfl, h⟩

private lemma fallingSet_singleton_of_lt (α : AspPerm) (n : ℤ)
    (h : α (n + 1) < α n) :
    fallingSet α ({n} : Set ℤ) = {n} := by
  -- Proof written by GPT 5.5.
  ext m
  constructor
  · intro hm
    exact hm.1
  · intro hm
    rw [Set.mem_singleton_iff] at hm
    subst m
    exact ⟨rfl, h⟩

/-- The inversion set of $\sigma_S$ is exactly the adjacent pairs
$(n,n+1)$ with $n \in S$. -/
private lemma sigma_inv_set_iff (S : Set ℤ) (hS : NoConsecutive S) (u v : ℤ) :
    ⟨u, v⟩ ∈ invSet (sigma S hS).func ↔ u ∈ S ∧ v = u + 1 := by
  -- Proof written by GPT 5.5.
  simp only [invSet, Set.mem_ofPred_eq, sigma_apply]
  constructor
  · rintro ⟨huv, hσ⟩
    have hupper : sigmaFun S u ≤ u + 1 := by
      simpa only [sigma_apply] using sigma_apply_le_succ S hS u
    have hlower : v - 1 ≤ sigmaFun S v := by
      simpa only [sigma_apply] using pred_le_sigma_apply S hS v
    have hv : v = u + 1 := by omega
    subst v
    constructor
    · by_contra hu
      have hσu_le : sigmaFun S u ≤ u := by
        by_cases hpred : u - 1 ∈ S
        · rw [sigmaFun_of_pred_mem hS hpred]
          omega
        · rw [sigmaFun_of_not_mem hu hpred]
      have hσsucc_ge : u + 1 ≤ sigmaFun S (u + 1) := by
        by_cases hsucc : u + 1 ∈ S
        · rw [sigmaFun_of_mem hsucc]
          omega
        · have hpred : (u + 1 : ℤ) - 1 ∉ S := by
            simpa only [add_sub_cancel_right] using hu
          rw [sigmaFun_of_not_mem hsucc hpred]
      omega
    · rfl
  · rintro ⟨hu, rfl⟩
    constructor
    · omega
    · have hpred : (u + 1 : ℤ) - 1 ∈ S := by
        simpa only [add_sub_cancel_right] using hu
      rw [sigmaFun_of_pred_mem hS hpred, sigmaFun_of_mem hu]
      omega

private lemma inv_set_sigma_singleton (n : ℤ) :
    invSet (sigma ({n} : Set ℤ) (noConsecutive_singleton n)) = {⟨n, n + 1⟩} := by
  -- Proof written by GPT 5.5.
  ext p
  rcases p with ⟨u, v⟩
  rw [sigma_inv_set_iff ({n} : Set ℤ) (noConsecutive_singleton n) u v]
  simp_all

private lemma eq_sigma_singleton_of_chi_eq_zero_of_inv_set_eq_singleton
    (σ : AspPerm) (n : ℤ) (hχ : σ.χ = 0)
    (hInv : invSet σ = {⟨n, n + 1⟩}) :
    σ = sigma ({n} : Set ℤ) (noConsecutive_singleton n) := by
  -- Proof written by GPT 5.5.
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · rw [hInv, inv_set_sigma_singleton n]
  · rw [hχ, sigma_chi]

private lemma sigmaFun_mul (S₁ S₂ : Set ℤ) (hDisj : Disjoint S₁ S₂)
    (hS : NoConsecutive (S₁ ∪ S₂)) (n : ℤ) :
    sigmaFun S₁ (sigmaFun S₂ n) = sigmaFun (S₁ ∪ S₂) n := by
  -- Proof written by GPT 5.5.
  have hD1 : ∀ m, m ∈ S₁ → m ∉ S₂ := Set.disjoint_left.mp hDisj
  have hD2 : ∀ m, m ∈ S₂ → m ∉ S₁ := Set.disjoint_right.mp hDisj
  have hNoLeft : ∀ m, m ∈ S₁ ∪ S₂ → m - 1 ∉ S₁ ∪ S₂ := by
    intro m hm hpred
    exact hS (m - 1) hpred (by simpa only [sub_add_cancel] using hm)
  by_cases h1 : n ∈ S₁
  · have h1' : n ∉ S₂ := hD1 n h1
    have h2 : n - 1 ∉ S₂ := by
      simp_all
    simp only [sigmaFun, h1', if_false, h2, h1, if_true, Set.mem_union,
      true_or]
  · by_cases h2 : n ∈ S₂
    · have h2' : n ∉ S₁ := hD2 n h2
      have h3 : n + 1 ∉ S₁ := by
        intro h
        exact hS n (Set.mem_union_right S₁ h2) (Set.mem_union_left S₂ h)
      have h4 : (n + 1 : ℤ) - 1 = n := add_sub_cancel_right n 1
      simp only [sigmaFun, h2', if_false, h2, if_true, h3, h4, Set.mem_union,
        false_or]
    · by_cases h3 : n - 1 ∈ S₁
      · have h3' : n - 1 ∉ S₂ := hD1 (n - 1) h3
        simp only [sigmaFun, h1, if_false, h2, h3', h3, if_true,
          Set.mem_union, false_or, true_or]
      · by_cases h4 : n - 1 ∈ S₂
        · have h5 : n - 1 ∉ S₁ := hD2 (n - 1) h4
          have h6 : (n - 1 : ℤ) - 1 ∉ S₁ := by
            simp_all
          simp only [sigmaFun, h1, if_false, h2, h4, if_true, h5, h6,
            Set.mem_union, false_or]
        · have h5 : n - 1 ∉ S₁ ∪ S₂ := by
            simp only [Set.mem_union, h3, h4, or_self, not_false_eq_true]
          simp only [sigmaFun, h1, if_false, h2, h3, h4, Set.mem_union,
            false_or, h5]

private lemma sigma_mul (S₁ S₂ : Set ℤ)
    (hS₁ : NoConsecutive S₁) (hS₂ : NoConsecutive S₂)
    (hDisj : Disjoint S₁ S₂) (hS : NoConsecutive (S₁ ∪ S₂)) :
    sigma S₁ hS₁ * sigma S₂ hS₂ = sigma (S₁ ∪ S₂) hS := by
  -- Proof written by GPT 5.5.
  apply AspPerm.ext.mpr
  funext n
  simp only [AspPerm.mul_apply, sigma_apply]
  exact sigmaFun_mul S₁ S₂ hDisj hS n

private lemma sigma_eq_of_set_eq {S T : Set ℤ} (hST : S = T)
    (hS : NoConsecutive S) (hT : NoConsecutive T) :
    sigma S hS = sigma T hT := by
  -- Proof written by GPT 5.5.
  simp_all

private lemma reducedProduct_sigma (S₁ S₂ : Set ℤ)
    (hS₁ : NoConsecutive S₁) (hS₂ : NoConsecutive S₂)
    (hDisj : Disjoint S₁ S₂) :
    AspPerm.ReducedProduct (sigma S₁ hS₁) (sigma S₂ hS₂) := by
  -- Proof written by GPT 5.5.
  rw [AspPerm.ReducedProduct]
  apply Set.disjoint_left.mpr
  rintro ⟨u, v⟩ h₁ h₂
  rw [sigma_inv hS₂] at h₂
  rw [sigma_inv_set_iff S₁ hS₁ u v] at h₁
  rw [sigma_inv_set_iff S₂ hS₂ u v] at h₂
  exact (Set.disjoint_left.mp hDisj) h₁.1 h₂.1

private lemma reducedProduct_alpha_sigma (α : AspPerm) (S : Set ℤ)
    (hS : NoConsecutive S) (hα : ∀ n, n ∈ S → α n < α (n + 1)) :
    AspPerm.ReducedProduct α (sigma S hS) := by
  -- Proof written by GPT 5.5.
  rw [AspPerm.ReducedProduct]
  apply Set.disjoint_left.mpr
  rintro ⟨u, v⟩ hαinv hσinv
  rw [sigma_inv hS] at hσinv
  rw [sigma_inv_set_iff S hS u v] at hσinv
  simp only [invSet, Set.mem_ofPred_eq] at hαinv
  rcases hσinv with ⟨hu, rfl⟩
  have hascent := hα u hu
  omega

private lemma sigma_le_weak_L_of_falling (α : AspPerm) (S : Set ℤ)
    (hS : NoConsecutive S) (hα : ∀ n, n ∈ S → α (n + 1) < α n) :
    (sigma S hS)⁻¹ ≤L α := by
  -- Proof written by GPT 5.5.
  intro p hp
  rcases p with ⟨u, v⟩
  rw [sigma_inv hS] at hp
  rw [sigma_inv_set_iff S hS u v] at hp
  rcases hp with ⟨hu, rfl⟩
  simp only [invSet, Set.mem_ofPred_eq]
  exact ⟨by omega, hα u hu⟩

private lemma star_sigma_eq_self (α : AspPerm) (S : Set ℤ) (hS : NoConsecutive S)
    (hα : ∀ n, n ∈ S → α (n + 1) < α n) :
    α ⋆ sigma S hS = α := by
  -- Proof written by GPT 5.5.
  apply AspPerm.eq_of_sf_eq
  apply (SF_ext _ _).mpr
  intro a b
  rw [AspPerm.star_spec, asp_star_sigma_sf S hS α a b]
  have hzero :
      Utils.oneIf (b - 1 ∈ S ∧ α (b - 1) < a ∧ a ≤ α b) = 0 := by
    simp only [Utils.oneIf]
    apply if_neg
    rintro ⟨hb, hlt, hle⟩
    have hfall := hα (b - 1) hb
    have hfall' : α b < α (b - 1) := by
      simpa only [sub_add_cancel] using hfall
    omega
  rw [hzero, add_zero]

private lemma residual_sigma_eq_self (α : AspPerm) (S : Set ℤ) (hS : NoConsecutive S)
    (hα : ∀ n, n ∈ S → α n < α (n + 1)) :
    α ◃ sigma S hS = α := by
  -- Proof written by GPT 5.5.
  apply AspPerm.eq_of_sf_eq
  apply (SF_ext _ _).mpr
  intro a b
  rw [AspPerm.lres_spec, asp_residual_sigma_sf S hS α a b]
  have hzero :
      Utils.oneIf (b - 1 ∈ S ∧ α b < a ∧ a ≤ α (b - 1)) = 0 := by
    simp only [Utils.oneIf]
    apply if_neg
    rintro ⟨hb, hlt, hle⟩
    have hrise := hα (b - 1) hb
    have hrise' : α (b - 1) < α b := by
      simpa only [sub_add_cancel] using hrise
    omega
  rw [hzero, sub_zero]

/-- *Theorem 8.7 (`thm:alphaStarSigma`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/4.* -/
theorem starSigma (α : AspPerm) (S : Set ℤ) (hS : NoConsecutive S) :
    α ⋆ sigma S hS =
        α * sigma (risingSet α S) (noConsecutive_risingSet α hS) := by
  -- Proof written by GPT 5.5.
  let R := risingSet α S
  let F := fallingSet α S
  let hR : NoConsecutive R := noConsecutive_risingSet α hS
  let hF : NoConsecutive F := noConsecutive_fallingSet α hS
  change α ⋆ sigma S hS = α * sigma R hR
  have hUnionFR : F ∪ R = S := by
    simpa only [F, R] using fallingSet_union_risingSet α S
  have hNoUnionFR : NoConsecutive (F ∪ R) := by
    simp_all
  have hDisjFR : Disjoint F R := by
    simpa only [F, R] using (disjoint_risingSet_fallingSet α S).symm
  have hMulFR : sigma F hF * sigma R hR = sigma S hS := by
    calc
      sigma F hF * sigma R hR = sigma (F ∪ R) hNoUnionFR :=
        sigma_mul F R hF hR hDisjFR hNoUnionFR
      _ = sigma S hS := sigma_eq_of_set_eq hUnionFR hNoUnionFR hS
  have hStarMulFR : sigma F hF ⋆ sigma R hR = sigma F hF * sigma R hR := by
    exact (ReducedProducts.star_eq_mul_iff_reducedProduct _ _).mpr
      (reducedProduct_sigma F R hF hR hDisjFR)
  calc
    α ⋆ sigma S hS = α ⋆ (sigma F hF * sigma R hR) := by rw [hMulFR]
    _ = α ⋆ (sigma F hF ⋆ sigma R hR) := by rw [hStarMulFR]
    _ = (α ⋆ sigma F hF) ⋆ sigma R hR := (AspPerm.star_assoc α _ _).symm
    _ = α ⋆ sigma R hR := by
      rw [star_sigma_eq_self α F hF]
      intro n hn
      exact hn.2
    _ = α * sigma R hR := by
      exact (ReducedProducts.star_eq_mul_iff_reducedProduct α _).mpr
        (reducedProduct_alpha_sigma α R hR (by
          intro n hn
          exact hn.2))

/-- *Theorem 8.7 (`thm:alphaStarSigma`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/4.* -/
theorem residualSigma (α : AspPerm) (S : Set ℤ) (hS : NoConsecutive S) :
    α ◃ sigma S hS =
        α * sigma (fallingSet α S) (noConsecutive_fallingSet α hS) := by
  -- Proof written by GPT 5.5.
  let R := risingSet α S
  let F := fallingSet α S
  let hR : NoConsecutive R := noConsecutive_risingSet α hS
  let hF : NoConsecutive F := noConsecutive_fallingSet α hS
  change α ◃ sigma S hS = α * sigma F hF
  have hUnionRF : R ∪ F = S := by
    simpa only [R, F] using risingSet_union_fallingSet α S
  have hNoUnionRF : NoConsecutive (R ∪ F) := by
    simp_all
  have hDisjRF : Disjoint R F := by
    simpa only [R, F] using disjoint_risingSet_fallingSet α S
  have hMulRF : sigma R hR * sigma F hF = sigma S hS := by
    calc
      sigma R hR * sigma F hF = sigma (R ∪ F) hNoUnionRF :=
        sigma_mul R F hR hF hDisjRF hNoUnionRF
      _ = sigma S hS := sigma_eq_of_set_eq hUnionRF hNoUnionRF hS
  have hStarMulRF : sigma R hR ⋆ sigma F hF = sigma R hR * sigma F hF := by
    exact (ReducedProducts.star_eq_mul_iff_reducedProduct _ _).mpr
      (reducedProduct_sigma R F hR hF hDisjRF)
  calc
    α ◃ sigma S hS = α ◃ (sigma R hR * sigma F hF) := by rw [hMulRF]
    _ = α ◃ (sigma R hR ⋆ sigma F hF) := by rw [hStarMulRF]
    _ = (α ◃ sigma R hR) ◃ sigma F hF :=
      (AspPerm.lres_assoc α _ _).symm
    _ = α ◃ sigma F hF := by
      rw [residual_sigma_eq_self α R hR]
      intro n hn
      exact hn.2
    _ = α * sigma F hF := by
      exact (ReducedProducts.lres_eq_mul_iff α _).mpr
        (sigma_le_weak_L_of_falling α F hF (by
          intro n hn
          exact hn.2))

/-- The simple-transposition case of the Demazure product: if $\sigma \in \mathrm{ASP}$
has shift zero and its only inversion is $(n,n+1)$, then right Demazure
multiplication by $\sigma$ follows the usual rule.

This is the last sentence of *Theorem A* of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), supplied by
*Theorem 8.7 (`thm:alphaStarSigma`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/4.* -/
theorem star_simple (α σ : AspPerm) (n : ℤ)
    (hχ : σ.χ = 0) (hInv : invSet σ = {⟨n, n + 1⟩}) :
    α ⋆ σ = if α n < α (n + 1) then α * σ else α := by
  -- Proof written by GPT 5.5.
  let T : Set ℤ := {n}
  let hT : NoConsecutive T := noConsecutive_singleton n
  have hσ : σ = sigma T hT :=
    eq_sigma_singleton_of_chi_eq_zero_of_inv_set_eq_singleton σ n hχ hInv
  rw [hσ]
  by_cases hα : α n < α (n + 1)
  · rw [if_pos hα]
    have hRise : risingSet α T = T := by
      simpa only [T] using risingSet_singleton_of_lt α n hα
    calc
      α ⋆ sigma T hT =
          α * sigma (risingSet α T) (noConsecutive_risingSet α hT) :=
            starSigma α T hT
      _ = α * sigma T hT := by
        rw [sigma_eq_of_set_eq hRise (noConsecutive_risingSet α hT) hT]
  · rw [if_neg hα]
    apply star_sigma_eq_self
    intro m hm
    have hm_eq : m = n := by simpa only [T, Set.mem_singleton_iff] using hm
    subst m
    have hne : α n ≠ α (n + 1) := by
      intro heq
      exact (ne_of_lt (lt_add_one n)) (α.injective heq)
    omega

/-- The simple-transposition case of left residual: if $\sigma \in \mathrm{ASP}$
has shift zero and its only inversion is $(n,n+1)$, then right residual by
$\sigma$ follows the usual rule.

This is the last sentence of *Theorem 1.1 (`thm:resL`)* of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), supplied by
*Theorem 8.7 (`thm:alphaStarSigma`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/4.* -/
theorem residual_simple (α σ : AspPerm) (n : ℤ)
    (hχ : σ.χ = 0) (hInv : invSet σ = {⟨n, n + 1⟩}) :
    α ◃ σ = if α (n + 1) < α n then α * σ else α := by
  -- Proof written by GPT 5.5.
  let T : Set ℤ := {n}
  let hT : NoConsecutive T := noConsecutive_singleton n
  have hσ : σ = sigma T hT :=
    eq_sigma_singleton_of_chi_eq_zero_of_inv_set_eq_singleton σ n hχ hInv
  rw [hσ]
  by_cases hα : α (n + 1) < α n
  · rw [if_pos hα]
    have hFall : fallingSet α T = T := by
      simpa only [T] using fallingSet_singleton_of_lt α n hα
    calc
      α ◃ sigma T hT =
          α * sigma (fallingSet α T) (noConsecutive_fallingSet α hT) :=
            residualSigma α T hT
      _ = α * sigma T hT := by
        rw [sigma_eq_of_set_eq hFall (noConsecutive_fallingSet α hT) hT]
  · rw [if_neg hα]
    apply residual_sigma_eq_self
    intro m hm
    have hm_eq : m = n := by simpa only [T, Set.mem_singleton_iff] using hm
    subst m
    have hne : α n ≠ α (n + 1) := by
      intro heq
      exact (ne_of_lt (lt_add_one n)) (α.injective heq)
    omega

end Transpositions

end LeanPool.DemazureProduct
