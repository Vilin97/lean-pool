/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.SourceAnariRezaeiMerge

/-! # Source Anari Rezaei List -/

@[expose] public section

namespace BeyondBethe

/-!
# Dimension reduction for the Anari--Rezaei functional

Lists expose the adjacent-merge induction without finite-index casts.  The
last part of the file identifies this list functional with the canonical
`Fin n` functional used by the rest of the development.
-/

/-- Sums each list entry times the logarithm of the suffix sum starting at that entry. -/
noncomputable def anariRezaeiRightScore : List ℝ → ℝ
  | [] => 0
  | x :: xs => x * Real.log ((x :: xs).sum) + anariRezaeiRightScore xs

/-- Sums the complement terms `(1 - x) * log (1 - x)` over a list. -/
noncomputable def anariRezaeiComplementScore (p : List ℝ) : ℝ :=
  (p.map fun x ↦ (1-x)*Real.log (1-x)).sum

/-- Adds forward and reverse suffix-log scores and subtracts twice the complement score. -/
noncomputable def anariRezaeiListPhi (p : List ℝ) : ℝ :=
  anariRezaeiRightScore p + anariRezaeiRightScore p.reverse -
    2*anariRezaeiComplementScore p

theorem anariRezaeiRightScore_merge
    (L R : List ℝ) (r s : ℝ) :
    anariRezaeiRightScore (L ++ r :: s :: R) -
        anariRezaeiRightScore (L ++ (r+s) :: R) =
      s*(Real.log (s+R.sum)-Real.log (r+s+R.sum)) := by
  induction L with
  | nil =>
      simp [anariRezaeiRightScore]
      ring
  | cons x L ih =>
      simp only [List.cons_append, anariRezaeiRightScore]
      have hsum : (x :: (L ++ r :: s :: R)).sum =
          (x :: (L ++ (r+s) :: R)).sum := by simp; ring
      rw [hsum]
      linarith [ih]

theorem anariRezaeiComplementScore_merge
    (L R : List ℝ) (r s : ℝ) :
    anariRezaeiComplementScore (L ++ r :: s :: R) -
        anariRezaeiComplementScore (L ++ (r+s) :: R) =
      (1-r)*Real.log (1-r) + (1-s)*Real.log (1-s) -
        (1-r-s)*Real.log (1-r-s) := by
  simp [anariRezaeiComplementScore]
  ring

/-- The expanded logarithmic gap for merging adjacent masses `r` and `s` with surrounding masses
`q` and `t`. -/
noncomputable def anariRezaeiMergeExpandedGap (q r s t : ℝ) : ℝ :=
  r*(Real.log (q+r)-Real.log (q+r+s)) +
    s*(Real.log (s+t)-Real.log (r+s+t)) -
    2*(1-r)*Real.log (1-r) -
    2*(1-s)*Real.log (1-s) +
    2*(1-r-s)*Real.log (1-r-s)

theorem anariRezaeiListPhi_merge (L R : List ℝ) (r s : ℝ) :
    anariRezaeiListPhi (L ++ r :: s :: R) -
        anariRezaeiListPhi (L ++ (r+s) :: R) =
      anariRezaeiMergeExpandedGap L.sum r s R.sum := by
  have hrevOld : (L ++ r :: s :: R).reverse =
      R.reverse ++ s :: r :: L.reverse := by simp
  have hrevNew : (L ++ (r+s) :: R).reverse =
      R.reverse ++ (s+r) :: L.reverse := by simp [add_comm]
  have hf := anariRezaeiRightScore_merge L R r s
  have hb := anariRezaeiRightScore_merge R.reverse L.reverse s r
  have hc := anariRezaeiComplementScore_merge L R r s
  have hb' :
      anariRezaeiRightScore (R.reverse ++ s :: r :: L.reverse) -
          anariRezaeiRightScore (R.reverse ++ (s+r) :: L.reverse) =
        r*(Real.log (L.sum+r)-Real.log (L.sum+r+s)) := by
    simpa [add_comm, add_left_comm, add_assoc] using hb
  rw [anariRezaeiListPhi, anariRezaeiListPhi, hrevOld, hrevNew,
    anariRezaeiMergeExpandedGap]
  linear_combination hf + hb' - 2*hc

theorem anariRezaeiMergeExpandedGap_nonpos
    {q r s t : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hsum : q+r+s+t = 1) (hC : r+s ≤ 14/25) :
    anariRezaeiMergeExpandedGap q r s t ≤ 0 := by
  by_cases hrz : r = 0
  · subst r
    rw [anariRezaeiMergeExpandedGap]
    norm_num
  · by_cases hsz : s = 0
    · subst s
      rw [anariRezaeiMergeExpandedGap]
      norm_num
    · have hr : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
      have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsz)
      have hqr : 0 < q+r := add_pos_of_nonneg_of_pos hq0 hr
      have hqrs : 0 < q+r+s := add_pos hqr hs
      have hst : 0 < s+t := add_pos_of_pos_of_nonneg hs ht0
      have hrst : 0 < r+s+t := add_pos_of_pos_of_nonneg (add_pos hr hs) ht0
      have heq : anariRezaeiMergeExpandedGap q r s t =
          anariRezaeiMergeGap q r s t := by
        rw [anariRezaeiMergeExpandedGap, anariRezaeiMergeGap,
          Real.log_div hqr.ne' hqrs.ne', Real.log_div hst.ne' hrst.ne']
      rw [heq]
      exact anariRezaeiMergeGap_nonpos hq0 hr0 hs0 ht0 hsum hC

theorem anariRezaeiListPhi_le_of_merge
    {L R : List ℝ} {r s : ℝ}
    (hL : ∀ x ∈ L, 0 ≤ x) (hR : ∀ x ∈ R, 0 ≤ x)
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hsum : (L ++ r :: s :: R).sum = 1)
    (hC : r+s ≤ 14/25) :
    anariRezaeiListPhi (L ++ r :: s :: R) ≤
      anariRezaeiListPhi (L ++ (r+s) :: R) := by
  have hLsum : 0 ≤ L.sum := List.sum_nonneg hL
  have hRsum : 0 ≤ R.sum := List.sum_nonneg hR
  have hquad : L.sum+r+s+R.sum = 1 := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil] at hsum
    linarith
  have hgap := anariRezaeiMergeExpandedGap_nonpos
    hLsum hr0 hs0 hRsum hquad hC
  rw [← anariRezaeiListPhi_merge] at hgap
  linarith

theorem anariRezaeiListPhi_two
    {q s : ℝ} (hsum : q+s = 1) :
    anariRezaeiListPhi [q,s] = binaryEntropy q := by
  have hs : s = 1-q := by linarith
  subst s
  simp [anariRezaeiListPhi, anariRezaeiRightScore,
    anariRezaeiComplementScore, binaryEntropy, Real.negMulLog_def]
  ring

theorem anariRezaeiListPhi_two_le
    {q s : ℝ} (hq0 : 0 ≤ q) (hs0 : 0 ≤ s)
    (hsum : q+s = 1) :
    anariRezaeiListPhi [q,s] ≤ Real.log 2 := by
  rw [anariRezaeiListPhi_two hsum]
  apply binaryEntropy_le_log_two hq0
  linarith

theorem anariRezaeiListPhi_three
    {q r s : ℝ} (hsum : q+r+s = 1) :
    anariRezaeiListPhi [q,r,s] = anariRezaeiPhiThree q s := by
  have hr : r = 1-q-s := by linarith
  subst r
  simp [anariRezaeiListPhi, anariRezaeiRightScore,
    anariRezaeiComplementScore, anariRezaeiPhiThree,
    Real.negMulLog_def]
  ring_nf
  rw [Real.log_one]
  ring

theorem anariRezaeiListPhi_three_le
    {q r s : ℝ} (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hsum : q+r+s = 1) :
    anariRezaeiListPhi [q,r,s] ≤ Real.log 2 := by
  by_cases hqr : q+r ≤ 14/25
  · calc
      anariRezaeiListPhi [q,r,s] ≤ anariRezaeiListPhi [q+r,s] := by
        simpa using anariRezaeiListPhi_le_of_merge
          (L := []) (R := [s]) (r := q) (s := r)
          (by simp) (by simpa) hq0 hr0 (by norm_num; linarith) hqr
      _ ≤ Real.log 2 := anariRezaeiListPhi_two_le
        (add_nonneg hq0 hr0) hs0 (by linarith)
  · by_cases hrs : r+s ≤ 14/25
    · calc
        anariRezaeiListPhi [q,r,s] ≤ anariRezaeiListPhi [q,r+s] := by
          simpa using anariRezaeiListPhi_le_of_merge
            (L := [q]) (R := []) (r := r) (s := s)
            (by simpa) (by simp) hr0 hs0 (by norm_num; linarith) hrs
        _ ≤ Real.log 2 := anariRezaeiListPhi_two_le
          hq0 (add_nonneg hr0 hs0) (by linarith)
    · rw [anariRezaeiListPhi_three hsum]
      apply anariRezaeiPhiThree_le_log_two hq0 hs0
      · linarith
      · linarith

private theorem anariRezaeiListPhi_le_log_two_fuel
    (fuel : ℕ) (p : List ℝ) (hlen : p.length ≤ fuel)
    (hp : ∀ x ∈ p, 0 ≤ x) (hsum : p.sum = 1) :
    anariRezaeiListPhi p ≤ Real.log 2 := by
  induction fuel generalizing p with
  | zero =>
      have hpempty : p = [] := List.length_eq_zero_iff.mp
        (Nat.eq_zero_of_le_zero hlen)
      subst p
      simp at hsum
  | succ fuel ih =>
      rcases p with _ | ⟨a, p⟩
      · simp at hsum
      rcases p with _ | ⟨b, p⟩
      · have ha : a = 1 := by simpa using hsum
        subst a
        simp [anariRezaeiListPhi, anariRezaeiRightScore,
          anariRezaeiComplementScore]
        exact Real.log_nonneg (by norm_num)
      rcases p with _ | ⟨c, p⟩
      · apply anariRezaeiListPhi_two_le
        · exact hp a (by simp)
        · exact hp b (by simp)
        · norm_num at hsum ⊢
          linarith
      rcases p with _ | ⟨d, R⟩
      · apply anariRezaeiListPhi_three_le
        · exact hp a (by simp)
        · exact hp b (by simp)
        · exact hp c (by simp)
        · norm_num at hsum ⊢
          linarith
      have ha : 0 ≤ a := hp a (by simp)
      have hb : 0 ≤ b := hp b (by simp)
      have hc : 0 ≤ c := hp c (by simp)
      have hd : 0 ≤ d := hp d (by simp)
      have hR : ∀ x ∈ R, 0 ≤ x := by
        intro x hx
        exact hp x (by simp [hx])
      have hRsum : 0 ≤ R.sum := List.sum_nonneg hR
      have hsum' : a+b+c+d+R.sum = 1 := by
        norm_num at hsum
        linarith
      by_cases hab : a+b ≤ 1/2
      · let p' := (a+b) :: c :: d :: R
        have hp' : ∀ x ∈ p', 0 ≤ x := by
          intro x hx
          simp only [p', List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · exact add_nonneg ha hb
          · exact hc
          · exact hd
          · exact hR x hx
        have hp'sum : p'.sum = 1 := by
          dsimp [p']
          norm_num
          linarith
        have hp'len : p'.length ≤ fuel := by
          dsimp [p']
          simp at hlen ⊢
          omega
        have hmerge : anariRezaeiListPhi (a :: b :: c :: d :: R) ≤
            anariRezaeiListPhi p' := by
          simpa [p'] using anariRezaeiListPhi_le_of_merge
            (L := []) (R := c :: d :: R) (r := a) (s := b)
            (by simp) (by
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | rfl | hx
              · exact hc
              · exact hd
              · exact hR x hx)
            ha hb (by norm_num; linarith) (hab.trans (by norm_num))
        exact hmerge.trans (ih p' hp'len hp' hp'sum)
      · have hcd : c+d ≤ 1/2 := by
          have hab' : 1/2 < a+b := lt_of_not_ge hab
          linarith
        let p' := a :: b :: (c+d) :: R
        have hp' : ∀ x ∈ p', 0 ≤ x := by
          intro x hx
          simp only [p', List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | hx
          · exact ha
          · exact hb
          · exact add_nonneg hc hd
          · exact hR x hx
        have hp'sum : p'.sum = 1 := by
          dsimp [p']
          norm_num
          linarith
        have hp'len : p'.length ≤ fuel := by
          dsimp [p']
          simp at hlen ⊢
          omega
        have hmerge : anariRezaeiListPhi (a :: b :: c :: d :: R) ≤
            anariRezaeiListPhi p' := by
          simpa [p'] using anariRezaeiListPhi_le_of_merge
            (L := [a,b]) (R := R) (r := c) (s := d)
            (by simp [ha, hb]) hR hc hd
            (by norm_num; linarith) (hcd.trans (by norm_num))
        exact hmerge.trans (ih p' hp'len hp' hp'sum)

/-- The sharp `log 2` bound for probability lists of arbitrary length. -/
theorem anariRezaeiListPhi_le_log_two_of_probability
    (p : List ℝ) (hp : ∀ x ∈ p, 0 ≤ x) (hsum : p.sum = 1) :
    anariRezaeiListPhi p ≤ Real.log 2 :=
  anariRezaeiListPhi_le_log_two_fuel p.length p le_rfl hp hsum

/-! ## Identification with the finite-coordinate functional -/

theorem list_sum_ofFn_eq_fin_sum {m : ℕ} (p : Fin m → ℝ) :
    (List.ofFn p).sum = ∑ i, p i := by
  induction m with
  | zero => simp [List.ofFn_zero]
  | succ m ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [List.sum_cons]
      rw [ih]

theorem anariRezaeiRightScore_ofFn {m : ℕ} (p : Fin m → ℝ) :
    anariRezaeiRightScore (List.ofFn p) =
      ∑ j, p j * Real.log (suffixMass p (Equiv.refl (Fin m)) j) := by
  induction m with
  | zero => simp [List.ofFn_zero, anariRezaeiRightScore, suffixMass]
  | succ m ih =>
      rw [List.ofFn_succ, anariRezaeiRightScore, Fin.sum_univ_succ]
      rw [ih (fun i ↦ p i.succ)]
      have hsum : (p 0 :: List.ofFn fun i ↦ p i.succ).sum = ∑ i, p i := by
        rw [List.sum_cons, list_sum_ofFn_eq_fin_sum, Fin.sum_univ_succ]
      have hzero : suffixMass p (Equiv.refl (Fin (m+1))) 0 = ∑ i, p i := by
        simp [suffixMass]
      rw [hsum, hzero]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      rw [suffixMass, suffixMass, Fin.sum_univ_succ]
      simp
      rfl

theorem anariRezaeiComplementScore_ofFn {m : ℕ} (p : Fin m → ℝ) :
    anariRezaeiComplementScore (List.ofFn p) =
      ∑ j, (1-p j)*Real.log (1-p j) := by
  rw [anariRezaeiComplementScore]
  rw [List.map_ofFn]
  simpa [Function.comp_def] using
    list_sum_ofFn_eq_fin_sum (fun j ↦ (1-p j)*Real.log (1-p j))

theorem ofFn_orderCoordinates_revPerm {m : ℕ} (p : Fin m → ℝ) :
    List.ofFn (orderCoordinates p Fin.revPerm) = (List.ofFn p).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hri
    rw [List.getElem_ofFn, List.getElem_reverse, List.getElem_ofFn]
    apply congrArg p
    apply Fin.ext
    simp [orderCoordinates, Fin.revPerm_apply, Fin.val_rev]
    omega

theorem anariRezaeiReverseScore_ofFn {m : ℕ} (p : Fin m → ℝ) :
    anariRezaeiRightScore (List.ofFn p).reverse =
      ∑ j, p j * Real.log
        (suffixMass p (reverseOrdering (Equiv.refl (Fin m))) j) := by
  let f : Fin m → ℝ := fun j ↦ p j * Real.log
    (suffixMass p (reverseOrdering (Equiv.refl (Fin m))) j)
  calc
    anariRezaeiRightScore (List.ofFn p).reverse =
        anariRezaeiRightScore
          (List.ofFn (orderCoordinates p Fin.revPerm)) := by
            rw [ofFn_orderCoordinates_revPerm]
    _ = ∑ i, orderCoordinates p Fin.revPerm i *
          Real.log (suffixMass (orderCoordinates p Fin.revPerm)
            (Equiv.refl (Fin m)) i) :=
      anariRezaeiRightScore_ofFn _
    _ = ∑ i, f (Fin.revPerm i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [suffixMass_orderCoordinates]
      rfl
    _ = ∑ j, f j := Equiv.sum_comp Fin.revPerm f
    _ = ∑ j, p j * Real.log
        (suffixMass p (reverseOrdering (Equiv.refl (Fin m))) j) := rfl

theorem anariRezaeiListPhi_ofFn {m : ℕ} (p : Fin m → ℝ) :
    anariRezaeiListPhi (List.ofFn p) = anariRezaeiPhi p := by
  rw [anariRezaeiListPhi, anariRezaeiPhi, pairedRowScore,
    anariRezaeiRightScore_ofFn, anariRezaeiReverseScore_ofFn,
    anariRezaeiComplementScore_ofFn]

/-- The source's sharp one-row inequality, now without an interface
hypothesis. -/
theorem anariRezaeiPhi_le_log_two
    {m : ℕ} (p : Fin m → ℝ) (hp : IsProbabilityVector p) :
    anariRezaeiPhi p ≤ Real.log 2 := by
  rw [← anariRezaeiListPhi_ofFn]
  apply anariRezaeiListPhi_le_log_two_of_probability
  · intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact hp.nonnegative i
  · rw [list_sum_ofFn_eq_fin_sum, hp.sum_eq_one]

theorem anariRezaeiRowInequality : AnariRezaeiRowInequality := by
  apply anariRezaeiRowInequality_of_phi
  intro m _hm p hp
  exact anariRezaeiPhi_le_log_two p hp

end BeyondBethe
