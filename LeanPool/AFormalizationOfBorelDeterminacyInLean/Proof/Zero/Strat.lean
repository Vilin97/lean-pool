/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.TreeLift

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.Strat

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section «Section1»

variable {R : Strategy (gameAsTrees hyp).2 Player.zero} (y : body (stratMap' R).pre.subtree)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def bodyTake (n : ℕ) : TreeLift hyp where
  R := R
  x := body.take (2 * k + 2 + n) y
  hlvl := by simp; omega
@[simp] lemma bodyTake_take (h : 2 * k + 2 ≤ m) :
  (bodyTake y n).take m (by omega) = bodyTake y (min (m - (2 * k + 2)) n) := by
  ext1 <;> simp; congr; omega
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def takeLift (n : ℕ) := (bodyTake y n).lift (by simp)
attribute [simp_lengths] bodyTake_x takeLift_x_coe
@[simp] lemma takeLift_mono : takeLift y m ≤ takeLift y n ↔ m ≤ n := by
  constructor <;> intro h
  · simpa using PreLift.length_mono h
  · ext1
    · ext1; simp [h]
    · rfl
@[simp] lemma takeLift_game : (takeLift y n).game = (takeLift y 0).game := by
  have h := Lift.eq_take_of_le <| (takeLift_mono y).mpr (Nat.zero_le n)
  rw [← h, Lift.take_toPreLift, PreLift.game_take]
lemma losable_of_losable_not_lost n (hL : (takeLift y n).Losable)
  (h' : ∀ m, ¬ (takeLift y m).Lost) m (hm : hL.2.num ≤ m + 1) : (takeLift y m).Losable := by
  have hc m : (takeLift y m).ConLong := by
    have := (bodyTake y m).conLong_or_lost; tauto
  use hc m; by_cases hW : WinningPrefix (takeLift y m).game Player.one
    ((body.take (2 * k + 2 + m) y).val.drop (2 * k + 1))
  · exact hW
  · have : hL.2.num ≤ n + 1 := by
      have hnum := hL.2.num_le_length
      have hlen : (List.drop (2 * k + 1) (takeLift y n).x.val).length = n + 1 := by
        simp
        omega
      exact hlen ▸ hnum
    let pnum := hL.2.num
    have hpnum : pnum ≤ n + 1 := this
    have hpnum_def : hL.2.num = pnum := rfl
    have hpmax : 1 ≤ max 1 pnum := le_max_left 1 pnum
    have hpmax_le_n : max 1 pnum ≤ n + 1 := by omega
    have hpmax_le_m : max 1 pnum ≤ m + 1 := by omega
    have htakeLen :
        2 * k + 2 + (2 * k + 1 + max 1 pnum - (2 * k + 2)) =
          min (2 * k + 2 + n) (2 * k + 1 + hL.2.num + (1 - pnum)) := by
      rw [hpnum_def]
      by_cases hpzero : pnum = 0
      · simp [hpzero]
      · have hpone : 1 ≤ pnum := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
        have hpmax_eq : max 1 pnum = pnum := max_eq_right hpone
        simp [hpmax_eq]
        omega
    have hW : (takeLift y m).Winnable := hW
    replace hW := hW.take (2 * k + 1 + max 1 pnum) (by omega)
    replace hL := hL.take (n := 1 - pnum) (by
      by_cases hpzero : pnum = 0
      · simp [pnum, hpzero]
      · have hpone : 1 ≤ pnum := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
        omega)
    simp_rw [takeLift] at hW hL
    rw [← TreeLift.lift_take _ (by omega) (by simp; omega)] at hW
    rw [← TreeLift.lift_take _ (by
      change 2 * k < 2 * k + 1 + pnum + (1 - pnum)
      by_cases hpzero : pnum = 0
      · omega
      · have hpone : 1 ≤ pnum := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
        omega) (by
      conv => simp
      change 2 * k + 2 ≤ 2 * k + 1 + pnum + (1 - pnum)
      by_cases hpzero : pnum = 0
      · omega
      · have hpone : 1 ≤ pnum := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
        omega)] at hL
    simp (disch := omega) only [bodyTake_take, min_eq_left] at hW hL
    cases hW (by
      convert hL.2 using 6
      all_goals
        ext1 <;> (conv => simp)
        try trivial
        rw [htakeLen]
        rfl)
lemma body_lost_of_losable n (h : (takeLift y n).Losable) (h' : ∀ m, ¬ (takeLift y m).Lost) :
  ⟨y.val, body_mono (subtree_sub _) y.prop⟩ ∉ G.payoff := by
  have hL := losable_of_losable_not_lost y n h h'
  have hb : (body.drop (2 * k + 1 + h.2.num) y).val ∈ body h.2.strat.pre.subtree := by
    apply mem_body_of_take (n + 1); intro m hm
    have := (bodyTake y (h.2.num + m - 1)).losable_subtree (h := by simp) (hL _ (by omega)) (by
      simp only [TreeLift.dropLast, takeLift_game, takeLift_x_coe, bodyTake_x,
        body.take_coe, Stream'.length_take, Nat.succ_add_sub_one, TreeLift.take_x,
        take_coe, Stream'.take_take, not_exists]
      intro h
      conv at h => simp
      simp_rw [bodyTake_take y h]; apply h')
    generalize_proofs pf1 pf2 pf3 at this
    simp only [takeLift_x_coe, bodyTake_x, body.take_coe, TreeLift.lift_toPreLift,
      TreeLift.preLift_x_coe, takeLift_game] at this
    generalize_proofs at this
    conv => simp [Stream'.take_drop]
    generalize_proofs pf4 pf5
    have hsub : pf3.strat.pre.subtree = pf1.strat.pre.subtree := by
      exact pf1.prefix_strat_subtree
        (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synthIsPosition)).drop _)
        (by as_aux_lemma => change _ = (takeLift y _).game; simp) rfl
    convert (hsub ▸ this) using 3
    · symm; apply WinningPrefix.prefix_num _
        (((Stream'.take_prefix _ _ _).mpr (by synthIsPosition)).drop _)
        (by change _ = (takeLift y _).game; simp) rfl
    · omega
  have hw := h.2.strat_winning hb
  generalize_proofs at hw
  simp only [takeLift_game, takeLift_x_coe, Player.payoff_residual,
    Player.residual_residual, List.length_append, List.length_take, List.length_drop,
    Stream'.length_take, div_add_self, Player.residual_even, Player.payoff_one,
    Set.preimage_compl] at hw
  simp only [takeLift_game, body.drop_coe, Set.mem_image, Subtype.exists,
    exists_and_right, exists_eq_right] at hw
  replace hw := hw.2; conv at hw => simp [PreLift.game_payoff, Nat.add_mod]
  generalize_proofs pf at hw
  have : ((y.val.take (2 * k + 2 + n)).drop (2 * k + 1)).take pf.num
    ++ₛ y.val.drop (2 * k + 1 + pf.num) = y.val.drop (2 * k + 1) := by
    have hnat : 2 * k + 2 + n = (2 * k + 1) + (1 + n) := by omega
    rw [← Stream'.drop_drop]
    conv => lhs; lhs; rhs; rw [hnat, ← Stream'.take_drop]
    rw [Stream'.take_take]
    have : pf.num ≤ 1 + n := by
      have := h.2.num_le_length; simp_rw [takeLift_game] at this; synthIsPosition
    simp [this, - Stream'.drop_drop]
  have hmem_tail : y.val.drop (2 * k + 1) ∈ body (takeLift y 0).game.tree := by
    apply mem_body_of_take (h.2.num + 1)
    intro n _
    convert (hL (n - 1) (by omega)).1
    · conv => simp [PreLift.ConLong, - Function.iterate_succ, Stream'.take_drop]
      congr! 3
      omega
  intro hy_pay
  apply hw
  constructor
  · change Stream'.take (2 * k + 1) y.val ++ₛ
        (List.take pf.num (List.drop (2 * k + 1) (Stream'.take (2 * k + 2 + n) y.val)) ++ₛ
          Stream'.drop (2 * k + 1 + pf.num) y.val) ∈ body G.tree
    rw [this, Stream'.append_take_drop]
    exact body_mono (subtree_sub _) y.prop
  · intro hcomp
    simp only [Set.mem_preimage, Set.mem_image, Subtype.exists,
      exists_and_right, exists_eq_right] at hcomp
    obtain ⟨_, hnot⟩ := hcomp
    apply hnot
    simpa [this, body.append, takeLift_x_coe, Stream'.append_take_drop] using hy_pay
lemma lost_of_body_lost (hy : ⟨y.val, body_mono (subtree_sub _) y.prop⟩ ∉ G.payoff) :
  ∃ m, (takeLift y m).Lost := by
  rw [← Subtype.val_injective.mem_set_image,
    ← (isClosed_image_payoff.mp hyp.closed).closure_eq,
    mem_closure_iff_nhds_basis (hasBasis_principalOpen y.val)] at hy
  conv at hy => simp
  obtain ⟨x, hx1, hx2⟩ := hy; use x.length
  apply TreeLift.lost_of_lost'; unfold Lift.Lost'
  rw [wonPosition_iff_disjoint, ← Set.subset_empty_iff]
  intro z ⟨h1, h2⟩
  conv at h1 => simp
  conv at h2 => simp
  apply hx2 z
  · exact h2.2
  · apply principalOpen_mono _ h1
    rw [principalOpen_iff_restrict] at hx1; rw [hx1]; simp
  · exact h2.1
lemma lost_of_losable n (h : (takeLift y n).Losable) : ∃ m, (takeLift y m).Lost := by
  by_cases h' : ∃ m, (takeLift y m).Lost
  · exact h'
  · exact lost_of_body_lost y (body_lost_of_losable y n h (by push Not at h'; exact h'))

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def wonLift (h : ∀ n, (takeLift y n).Winnable) : body R.pre.subtree :=
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
  ⟨(h k).toWLift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y k).wLift_mem_tree _ _⟩, by
    rw [List.length_take, min_eq_left]
    change k ≤ (h k).toWLift'.toWLLift.liftVal.length
    rw [WLLift.liftVal_length]
    simp⟩⟩, fun k ↦
    ((Lift.wLift_liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))).take k).trans (by
      convert List.take_prefix k (List.take (k + 1) (takeLift y (k + 1)).toWLift.liftVal)
        using 1
      simp [List.take_take])⟩
lemma wonLift_map h :
  (bodyFunctor.map π ⟨(wonLift y h).val, body_mono R.pre.subtree_sub (wonLift y h).prop⟩).val
  = y.val := by
  rw [treeHom_body]
  ext n'
  simp only [wonLift]
  let hlong : (takeLift y (n' + 1)).Winnable := h (n' + 1)
  change ((List.take (n' + 1) hlong.toWLift'.liftVal)[n']).1 = y.val n'
  rw [List.getElem_take]
  rw [WLLift.liftVal_lift_get]; simp [Stream'.get]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def lostLift (h : (takeLift y n).Lost) : body R.pre.subtree :=
  have h' k : (takeLift y (n + k)).Lost := h.lost_of_le ((takeLift_mono y).mpr (by omega))
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
  ⟨(h' k).toLLift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y (n + k)).lLift_mem_tree _ _⟩, by
    rw [List.length_take, min_eq_left]
    change k ≤ (h' k).toLLift'.toWLLift.liftVal.length
    rw [WLLift.liftVal_length]
    simp
    omega⟩⟩, fun k ↦
    ((Lift.lLift_liftVal_mono (h' k).1 ((takeLift_mono y).mpr (Nat.le_succ _))).take k).trans
      (by
        convert List.take_prefix k (List.take (k + 1) (h' (k + 1)).toLLift'.liftVal) using 1
        simp [List.take_take])⟩
lemma lostLift_map (h : (takeLift y n).Lost) :
  (bodyFunctor.map π ⟨(lostLift y h).val, body_mono R.pre.subtree_sub (lostLift y h).prop⟩).val
  = y.val := by
  rw [treeHom_body]
  ext n'
  simp only [lostLift]
  let hlong : (takeLift y (n + (n' + 1))).Lost :=
    h.lost_of_le ((takeLift_mono y).mpr (by omega))
  change ((List.take (n' + 1) hlong.toLLift'.liftVal)[n']).1 = y.val n'
  rw [List.getElem_take]
  rw [WLLift.liftVal_lift_get]; simp [Stream'.get]

lemma body_stratMap :
  ∃ x : body R.pre.subtree, (bodyFunctor.map π
    ⟨x.val, body_mono R.pre.subtree_sub x.prop⟩).val = y.val :=
  by
  classical
  exact if h : ∀ n, (takeLift y n).Winnable then ⟨wonLift y h, wonLift_map y h⟩
  else by
    obtain ⟨n, h⟩ := by simpa using h
    let ⟨n, h⟩ : ∃ n, (takeLift y n).Lost :=
      if h' : (takeLift y n).Lost then ⟨n, h'⟩
      else lost_of_losable y n ⟨by have := (bodyTake y n).conLong_or_lost; tauto, of_not_not h⟩
    exact ⟨lostLift y h, lostLift_map y h⟩

end «Section1»
end GaleStewartGame.BorelDet.Zero
