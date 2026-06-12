/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.PreLift

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.Lift

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section «Section1»
variable (H : Lift hyp)
namespace Lift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftShortWinStrat :
  QuasiStrategy (subAt H.game.tree [H.liftNode]) Player.one :=
  defensiveQuasi (H.game.residual [H.liftNode]) Player.one (H.game_pruned.sub _)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def toWLift : WLLift hyp where
  toLift := H
  liftTree := (liftShortWinStrat H).1.subtree
attribute [simp_lengths] toWLift_toLift
@[simp] lemma liftTree_take n h : (H.take n h).toWLift.liftTree = H.toWLift.liftTree := by
  change
    (defensiveQuasi ((H.take n h).game.residual [(H.take n h).liftNode]) Player.one _).1.subtree =
      (defensiveQuasi (H.game.residual [H.liftNode]) Player.one _).1.subtree
  have hG : (H.take n h).game.residual [(H.take n h).liftNode] =
      H.game.residual [H.liftNode] := by
    ext x <;> simp [PreLift.game_take H.toPreLift (n := n) (h := by omega),
      H.liftNode_take h]
  exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _
@[simp] lemma liftMediumVal_take n h :
  (H.take n h).toWLift.liftMediumVal = H.toWLift.liftMediumVal := by simp [WLLift.liftMediumVal]
@[simp] lemma liftVal_take n h : (H.take n h).toWLift.liftVal = H.toWLift.liftVal.take n := by
  by_cases H.x.val.length ≤ n
  · rw [Lift.take_of_length_le, List.take_of_length_le] <;> simp [*]
  · convert WLLift.liftVal_take_eq_of_tree _ _
    · simp; omega
    · apply Lift.take_le; exact h
    · simp
lemma wLift_liftVal_mono {H H' : Lift hyp} (h : H ≤ H') :
  H.toWLift.liftVal <+: H'.toWLift.liftVal := by
  rw [List.prefix_iff_eq_take, ← H'.liftVal_take _  (by simp)]
  simp_rw [WLLift.liftVal_length, toWLift_toLift]; congr; ext1; exact h.symm
namespace Winnable
variable (hW : H.Winnable)
variable {H}
include hW in lemma take n h : (H.take n h).Winnable := by
  intro ⟨m, hm⟩; apply hW; use min (2 * k + 1 + m) n - (2 * k + 1)
  have : 2 * k + 1 + (min (2 * k + 1 + m) n - (2 * k + 1)) = min (2 * k + 1 + m) n := by omega
  simpa only [List.take_drop, this, Lift.take_toPreLift, PreLift.game_take,
    PreLift.take_x, take_coe, List.take_take] using hm
include hW in lemma liftMedium_mem : H.toWLift.liftMediumVal ∈ T' := by
  dsimp [WLLift.liftMediumVal, Lift.liftNode]
  simp_rw [gameTree_concat]; use (H.R _ _ _).prop
  constructor
  · simp_rw (config := {singlePass := true}) [
      ← add_zero (2 * k + 1), List.getElem_drop', List.getElem_zero]
    -- TODO: diagnose why this unfolds `constTreeObj`.
    exact mem_of_prefix ⟨(H.x.val.drop (2 * k + 1)).tail, by simp⟩ hW.conLong
  · conv => simp
    right; rw [WinningCondition.concat]; refine ⟨?_, H.liftShortWinStrat, rfl⟩
    have h := (H.game.residual [H.liftNode]).gale_stewart_precise'
      (by
        exact isOpen_compl_iff.mpr (H.game_closed.preimage (body.append_con _)))
      (H.game_pruned.sub _)
      (by
        intro hS; apply hW; use 1
        have : (H.x.val.drop (2 * k + 1)).take 1 = [H.liftNode] := by
          rw [List.take_one_drop_eq_of_lt_length (by simp)]; rfl
        rw [this]
        change (H.game.residual [H.liftNode]).ExistsWinning Player.zero
        exact hS)
    simp_rw [pullSub_body, Set.image_subset_iff]
    apply subset_trans h
    conv => simp [PreLift.game_payoff]
    intro a ha
    rcases ha with ⟨haBody, haPay⟩
    have haBody' : (body.append [H.liftNode] a).val ∈
        body (subAt G.tree (H.x.val.take (2 * k + 1))) := by
      simpa [subAt_body] using haBody
    let x : body (subAt G.tree (H.x.val.take (2 * k + 1))) :=
      ⟨(body.append [H.liftNode] a).val, haBody'⟩
    have hxmem : x ∈ body.append (H.x.val.take (2 * k + 1)) ⁻¹' G.payoff := by
      by_contra hxnot
      exact haPay ⟨x, hxnot, rfl⟩
    use body.append (H.x.val.take (2 * k + 1)) x
    constructor
    · exact hxmem
    · change H.x.val.take (2 * k + 1) ++ₛ x.val =
        H.x.val.take (2 * k + 1 + 1) ++ₛ a.val
      rw [show H.x.val.take (2 * k + 1 + 1) =
          H.x.val.take (2 * k + 1) ++ [H.liftNode] by
        rw [← H.x.val.take_concat_get' (2 * k + 1) (by simp)]
        simp [Lift.liftNode]]
      simp [x, body.append]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toWLLift] def toWLift' : WLLift' hyp where
  toWLLift := H.toWLift
  hlift := by
    let ⟨n, hn⟩ := le_iff_exists_add.mp H.h'lvl_le
    induction n generalizing H with
    | zero =>
      rw [WLLift.liftVal, List.drop_of_length_le (by simp [hn])]
      simpa using hW.liftMedium_mem
    | succ n ih =>
      specialize ih (hW.take (2 * k + 2 + n) (by omega)); conv at ih => simp [hn]
      rw [H.toWLift.liftVal.eq_take_concat (2 * k + 2 + n) (by simpa)]
      conv => simp [- List.take_append_getElem]
      use ih; constructor
      · rw [getTree_eq' _ ih, mem_subAt]
        have htree : getTree' hyp (List.take (2 * k + 2)
            (List.take (2 * k + 2 + n) H.toWLift.liftVal)) = H.toWLift.liftTree := by
          rw [List.take_take]
          rw [(show min (2 * k + 2) (2 * k + 2 + n) = 2 * k + 2 by omega)]
          rw [WLLift.liftVal_take_medium]
          exact WLLift.getTree_liftMediumVal H.toWLift
        rw [htree]
        have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
          simp [hn]
        rw [(show H.x.val[2 * k + 2 + n] = (H.x.val.drop (2 * k + 2))[n]'hdrop by
          rw [List.getElem_drop'])]
        have hmap : List.map Prod.fst (List.drop (2 * k + 2)
            (List.take (2 * k + 2 + n) H.toWLift.liftVal)) =
            List.take n (List.drop (2 * k + 2) H.x.val) := by
          rw [List.drop_take]
          rw [(show 2 * k + 2 + n - (2 * k + 2) = n by omega)]
          calc
            List.map Prod.fst (List.take n (List.drop (2 * k + 2) H.toWLift.liftVal)) =
                List.take n
                  (List.map Prod.fst (List.drop (2 * k + 2) H.toWLift.liftVal)) := by
              rw [List.map_take]
            _ = List.take n (List.drop (2 * k + 2)
                  (List.map Prod.fst H.toWLift.liftVal)) := by
              rw [List.map_drop]
            _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
              rw [WLLift.liftVal_lift]
              simp [toWLift]
        convert take_mem (n := n + 1) (⟨_, WinningPrefix.mem_defensiveQuasi
            ⟨_, by
              change [H.liftNode] ++ H.x.val.drop (2 * k + 2) ∈ H.game.tree
              rw [List.singleton_append]
              simpa [PreLift.ConLong, Lift.liftNode] using hW.conLong⟩
            (by
              intro hwin
              apply hW
              simpa [Lift.liftNode] using hwin.winningPrefix_of_residual)
            _⟩ : H.toWLift.liftTree) using 1
        rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
        congr 1
      · conv => lhs; unfold WLLift.liftVal; rw [List.getElem_append_right (by simp)]
        rw [getTree_eq' _ ih]
        conv => simp [List.drop_take]
        congr
        · simp [List.take_take, WLLift.liftVal]
        · have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
            simp [hn]
          rw [(show H.x.val[2 * k + 2 + n] = (H.x.val.drop (2 * k + 2))[n]'hdrop by
            rw [List.getElem_drop'])]
          rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
          congr 1
          · symm
            calc
              List.map Prod.fst (List.take n (List.drop (2 * k + 2) H.toWLift.liftVal)) =
                  List.take n
                    (List.map Prod.fst (List.drop (2 * k + 2) H.toWLift.liftVal)) := by
                rw [List.map_take]
              _ = List.take n (List.drop (2 * k + 2)
                    (List.map Prod.fst H.toWLift.liftVal)) := by
                rw [List.map_drop]
              _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
                rw [WLLift.liftVal_lift]
                simp [toWLift]
attribute [simp_lengths] toWLift'_toWLLift
/-lemma extracted_1 {H : WLLift' hyp} (hp) (R) (h') :
  (ExtensionsAt.val' (ExtensionsAt.map π (x := H.lift)
    (y := @PreLift.x A inferInstance G k hyp H.toPreLift) h' (H.extension hp R))) =
    ... := by
    rw [ExtensionsAt.map_val'] --adding π fixes-/
lemma extension_conLong hp R : (hW.toWLift'.extensionLift hp R).ConLong := by
  have hm : H.x.val[2 * k + 1] :: (((hW.toWLift'.extensionMap hp R).val').drop (2 * k + 2))
    ∈ H.game.tree := by
    have hm' := by simpa using (mem_getTree (hW.toWLift'.extension hp R).valT').2
    have htake := ExtensionsAt.valT'_take_of_le (hW.toWLift'.extension hp R)
      (n := 2 * k + 2) (by
        change 2 * k + 2 ≤ H.toWLift.liftVal.length
        rw [WLLift.liftVal_length]
        exact H.h'lvl_le)
    erw [show List.take (2 * k + 2) (hW.toWLift'.extension hp R).val' =
        (Tree.take (2 * k + 2) hW.toWLift'.lift).val by
      exact congrArg Subtype.val htake] at hm'
    conv at hm' => simp [toWLift]
    have hsub := hm'.1
    have hval' : (hW.toWLift'.extensionMap hp R).val' =
        List.map Prod.fst (hW.toWLift'.extension hp R).val' := by
      change (ExtensionsAt.map (treeHom hyp) hW.toWLift'.lift_lift
          (hW.toWLift'.extension hp R)).val' =
        List.map Prod.fst (hW.toWLift'.extension hp R).val'
      exact ExtensionsAt.map_val' (treeHom hyp) hW.toWLift'.lift_lift
        (hW.toWLift'.extension hp R)
    rw [hval']
    rw [← List.singleton_append]
    rw [← liftNode]
    rw [← WLLift.liftMediumVal_length H.toWLift]
    exact hsub
  conv => simp [PreLift.ConLong]
  convert hm using 1
  rw [← List.getElem_cons_drop (by
    have hlen := ExtensionsAt.val'_length (hW.toWLift'.extensionMap hp R)
    change 2 * k + 1 < (hW.toWLift'.extensionMap hp R).val'.length
    rw [hlen]
    exact Nat.lt_of_lt_of_le H.h'lvl (Nat.le_succ _))]
  congr 1
  have ht : (hW.toWLift'.extensionMap hp R).val'.take (2 * k + 2) =
      H.x.val.take (2 * k + 2) := by
    exact WLLift'.extensionMap_take hW.toWLift' hp R (n := 2 * k + 2) (by simp)
  have hget := congrArg (fun xs : List A => xs[2 * k + 1]?) ht
  change (List.take (2 * k + 2) (hW.toWLift'.extensionMap hp R).val')[2 * k + 1]? =
      (List.take (2 * k + 2) H.x.val)[2 * k + 1]? at hget
  rw [List.getElem?_take, if_pos (by omega)] at hget
  rw [List.getElem?_take, if_pos (by omega)] at hget
  have hleft : 2 * k + 1 < (hW.toWLift'.extensionMap hp R).val'.length := by
    have hlen := ExtensionsAt.val'_length (hW.toWLift'.extensionMap hp R)
    rw [hlen]
    exact Nat.lt_of_lt_of_le H.h'lvl (Nat.le_succ _)
  rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem H.h'lvl] at hget
  exact Option.some.inj hget
end Winnable

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure LLift extends Lift hyp where
  lost' : toLift.Lost'
namespace LLift
variable (H : LLift hyp)
lemma losable (h : H.ConLong) : H.Losable := by
  use h; use H.x.val.length - (2 * k + 1); rw [List.take_of_length_le (by simp)]
  apply AllWinning.existsWinning _ (H.game_pruned.sub _); have hL := H.lost'
  conv at hL => simp [Lost', WonPosition, AllWinning]
  conv => simp [Lost', WonPosition, AllWinning]
  have hL' := Set.eq_univ_iff_forall.mp hL
  apply Set.eq_univ_iff_forall.mpr
  rintro ⟨x, hx⟩ hxp
  conv at hx => simp [Nat.add_mod]
  conv at hxp => simp [Nat.add_mod, PreLift.game_payoff]
  apply hL' ⟨x, by
    simpa [← Stream'.append_append_stream] using body_mono H.game_tree_sub hx⟩
  by_contra hnot
  apply hxp.2
  use ⟨List.drop (2 * k + 1) H.x.val ++ₛ x, by
    simpa [← Stream'.append_append_stream, List.take_append_drop] using
      body_mono H.game_tree_sub hx⟩
  constructor
  · intro hpay
    apply hnot
    simpa [body.append, ← Stream'.append_append_stream, List.take_append_drop] using hpay
  · rfl
lemma exists_prefix : ∃ n h, (H.take n h).Lost' :=
  ⟨H.x.val.length, H.h'lvl, by simpa using H.lost'⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def minLength := by
  classical
  exact Nat.find H.exists_prefix
@[simp] lemma minLength_le : H.minLength ≤ H.x.val.length (α := no_index _) := by
  classical
  exact Nat.find_le ⟨H.h'lvl, by simpa using H.lost'⟩
@[simp] lemma le_minLength : 2 * k + 2 ≤ H.minLength := by
  classical
  exact (Nat.find_spec H.exists_prefix).1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma lt_minLength : 2 * k + 1 < H.minLength := by have := H.le_minLength; omega
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def takeMin := H.take H.minLength H.le_minLength
@[simp] lemma takeMin_liftShort : H.takeMin.liftShort = H.liftShort := by
  simp [takeMin]
@[simp] lemma takeMin_game : H.takeMin.game = H.game := by simp [takeMin]
lemma min_prefix : H.takeMin.Lost' := by
  classical
  exact (Nat.find_spec H.exists_prefix).2
lemma le_of_take {n : ℕ} {h : 2 * k + 2 ≤ n} (hL : (H.take n h).Lost') :
  H.minLength ≤ n := by
  classical
  change Nat.find H.exists_prefix ≤ n
  exact Nat.find_le ⟨h, hL⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def toWLLift : WLLift hyp where
  toLift := H.toLift
  liftTree := pullSub (subAt G.tree H.takeMin.x.val) (H.takeMin.x.val.drop (2 * k + 2))
end LLift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def Lost'.mk {H : Lift hyp} (h : Lost' H) : LLift hyp := LLift.mk _ h
attribute [simp_lengths] LLift.toWLLift_toLift Lost'.mk_toLift

section «extend'»
variable {H}
variable {h} (hL : (H.take n h).Lost')
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def extend' : LLift hyp where
  toLift := H
  lost' := by
    change G.WonPosition H.x.val (Player.one.residual H.x.val)
    convert WonPosition.extend (H.x.val.drop n) hL using 1
    · exact (List.take_append_drop n H.x.val).symm
    · simp [Player.residual_residual, List.take_append_drop]
lemma extend'_le : (extend' (H := H) (n := n) (h := h) hL).minLength ≤ n :=
  (extend' (H := H) (n := n) (h := h) hL).le_of_take hL
@[simp] lemma minLength_extend' :
  (extend' (H := H) (n := n) (h := h) hL).minLength = hL.mk.minLength := by
  classical
  apply le_antisymm
  · exact Nat.find_mono fun m ⟨hm, hl⟩ ↦
      ⟨hm, (extend' (H := H.take m hm) (n := n) (h := h)
        (by simpa [min_comm] using hl : ((H.take m hm).take n h).Lost')).lost'⟩
  · apply Nat.find_le
    simp only [Lost'.mk_toLift, take_trans, LLift.le_minLength, exists_true_left]
    convert (extend' (H := H) (n := n) (h := h) hL).min_prefix
    simp [LLift.takeMin]; congr; simpa using extend'_le hL
lemma extend'_le' : hL.mk.minLength ≤ n := by simpa using extend'_le hL
@[simp] lemma takeMin_extend' :
  (extend' (H := H) (n := n) (h := h) hL).takeMin = hL.mk.takeMin := by
  simp [LLift.takeMin]; congr; simpa using extend'_le hL
@[simp] lemma liftTree_extend' :
  (extend' (H := H) (n := n) (h := h) hL).toWLLift.liftTree =
    hL.mk.toWLLift.liftTree := by
  simp [LLift.toWLLift, List.take_take, extend'_le' hL]
@[simp] lemma liftMediumVal_extend' :
  (extend' (H := H) (n := n) (h := h) hL).toWLLift.liftMediumVal =
    hL.mk.toWLLift.liftMediumVal := by
  simp [WLLift.liftMediumVal]
@[simp] lemma liftVal_extend' :
  (extend' (H := H) (n := n) (h := h) hL).toWLLift.liftVal.take n =
    hL.mk.toWLLift.liftVal := by
  by_cases H.x.val.length ≤ n
  · rw [List.take_of_length_le]
    · congr 2
      ext1
      simp only [extend'_toLift, Lost'.mk_toLift]
      rw [Lift.take_of_length_le]
      all_goals simpa
    · simpa
  · symm; convert WLLift.liftVal_take_eq_of_tree _ _
    · simp; omega
    · apply Lift.take_le; exact h
    · simp
end «extend'»

lemma lost'_of_le {H H' : Lift hyp} (h : H.Lost') (h' : H ≤ H') : H'.Lost' := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h
  exact (extend' (H := H') h).lost'
lemma lLift_liftVal_mono {H H' : Lift hyp} (h : H.Lost') (h' : H ≤ H') :
  h.mk.toWLLift.liftVal <+: (lost'_of_le h h').mk.toWLLift.liftVal := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h ⊢
  change h.mk.toWLLift.liftVal <+: _; rw [← liftVal_extend']; apply List.take_prefix
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Lost := ∃ (h : Lost' H), h.mk.takeMin.ConLong
namespace Lost
variable (hL : H.Lost)
variable {H}
lemma extend {h} (hL : (H.take n h).Lost) : H.Lost := by
  use (extend' (H := H) hL.1).lost'
  change (extend' (H := H) hL.1).takeMin.ConLong
  simpa using hL.2
lemma lost_of_le {H H' : Lift hyp} (h : H.Lost) (h' : H ≤ H') : H'.Lost := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h; exact h.extend
lemma liftMedium_mem : hL.1.mk.toWLLift.liftMediumVal ∈ T' := by
  dsimp [WLLift.liftMediumVal, Lift.liftNode, gameAsTrees]
  simp_rw [gameTree_concat]; use SetLike.coe_mem _; constructor
  · simp_rw (config := {singlePass := true}) [← add_zero (2 * k + 1),
      List.getElem_drop', List.getElem_zero]
    simpa [PreLift.game_tree] using
      mem_of_prefix ⟨(hL.1.mk.takeMin.x.val.drop (2 * k + 1)).tail, by
      simp only [LLift.takeMin_x_coe, Lost'.mk_toLift, List.tail_drop, List.cons_append,
        List.nil_append]
      rw [← List.getElem_take, List.getElem_cons_drop]
      simp⟩ hL.2
  · conv => simp
    left; rw [LosingCondition.concat]
    refine ⟨?_, ⟨hL.1.mk.takeMin.x.val.drop (2 * k + 2), ?_⟩, ?_⟩
    · conv => simp [LLift.toWLLift]
      rw [← Set.subset_empty_iff]
      rintro _ ⟨⟨z, hzb, hze⟩, ⟨_, _, rfl⟩⟩
      apply (wonPosition_iff_disjoint'.mp hL.1.mk.min_prefix).subset ⟨_, by simpa⟩
      use ⟨z, by simpa⟩; ext1
      simp_rw [← Stream'.append_append_stream] at hze
      rw [List.drop_take, ← List.take_add] at hze
      simpa using hze
    · rw [LLift.takeMin_x_coe]
      simp only [Lost'.mk_toLift, mem_subAt, List.cons_append, List.nil_append]
      rw [List.getElem_take', List.getElem_cons_drop]
      · simpa [PreLift.ConLong, PreLift.game_tree] using hL.2
      · simp
    · conv => simp [LLift.toWLLift]
      rw [List.append_cons, List.take_concat_get', List.drop_take, ← List.take_add]
      simp
lemma lift_mem n : hL.1.mk.toWLLift.liftMediumVal ++
  ((H.x.val.drop (2 * k + 2)).take n).zipInitsMap
  (fun a y ↦ ⟨a, subAt hL.1.mk.toWLLift.liftTree y⟩) ∈ T' := by
  induction n with
  | zero => simpa using hL.liftMedium_mem
  | succ n ih =>
    simp only [List.take_add_one, List.zipInitsMap_append, List.getElem?_drop] at ih ⊢
    by_cases hn : 2 * k + 2 + n ≥ H.x.val.length
    · erw [List.getElem?_eq_none_iff.mpr hn]
      simpa only [Option.toList_none, List.zipInitsMap_nil, List.append_nil] using ih
    · rw [List.getElem?_eq_getElem (by as_aux_lemma => omega)]; conv => simp [← List.append_assoc]
      use ih; rw [getTree_eq' _ ih]
      refine ⟨?_, by
        rw [List.take_left' (WLLift.liftMediumVal_length _)]
        simp only [WLLift.getTree_liftMediumVal, WLLift.liftMediumVal_length,
          List.drop_left', subAt_append]
        congr
        symm
        calc
          List.map Prod.fst
              ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap fun a y ↦
                (a, subAt hL.1.mk.toWLLift.liftTree y)) =
              (List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                (fun a _ ↦ a) := by
            exact (List.zipInitsMap_map
              (x := List.take n (List.drop (2 * k + 2) H.x.val))
              (f := fun a y ↦ (a, subAt hL.1.mk.toWLLift.liftTree y))
              (g := Prod.fst)).symm
          _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
            simp⟩
      rw [List.take_left' (WLLift.liftMediumVal_length _)]
      simp only [LLift.toWLLift, Lost'.mk_toLift, LLift.takeMin_x_coe,
        WLLift.getTree_liftMediumVal, WLLift.liftMediumVal_length, List.drop_left',
        mem_subAt]
      have htail_map : List.map Prod.fst
          ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap fun a y ↦
            (a, subAt (pullSub (subAt G.tree (List.take hL.1.mk.minLength H.x.val))
              (List.drop (2 * k + 2) (List.take hL.1.mk.minLength H.x.val))) y)) =
          List.take n (List.drop (2 * k + 2) H.x.val) := by
        calc
          List.map Prod.fst
              ((List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap fun a y ↦
                (a, subAt
                  (pullSub (subAt G.tree (List.take hL.1.mk.minLength H.x.val))
                    (List.drop (2 * k + 2) (List.take hL.1.mk.minLength H.x.val)))
                  y)) =
              (List.take n (List.drop (2 * k + 2) H.x.val)).zipInitsMap
                (fun a _ ↦ a) := by
            exact (List.zipInitsMap_map
              (x := List.take n (List.drop (2 * k + 2) H.x.val))
              (f := fun a y ↦
                (a, subAt
                  (pullSub (subAt G.tree (List.take hL.1.mk.minLength H.x.val))
                    (List.drop (2 * k + 2) (List.take hL.1.mk.minLength H.x.val)))
                  y))
              (g := Prod.fst)).symm
          _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
            simp
      have hmem : List.take n (List.drop (2 * k + 2) H.x.val) ++
          [H.x.val[2 * k + 2 + n]] ∈
          pullSub (subAt G.tree (List.take hL.1.mk.minLength H.x.val))
            (List.drop (2 * k + 2) (List.take hL.1.mk.minLength H.x.val)) := by
        by_cases hshort : 2 * k + 2 + n + 1 ≤ hL.1.mk.minLength
        · rw [mem_pullSub_short (by as_aux_lemma => simp; omega)]
          constructor
          · have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
              simp [List.length_drop]
              omega
            rw [(show H.x.val[2 * k + 2 + n] =
                (H.x.val.drop (2 * k + 2))[n]'hdrop by
              rw [List.getElem_drop'])]
            rw [List.take_concat_get']
            simp [List.drop_take]
            omega
          · simp only [mem_subAt, List.append_nil]
            exact hL.1.mk.takeMin.x.prop
        · rw [mem_pullSub_long (by as_aux_lemma => simp; omega)]
          use ((H.x.val.drop (2 * k + 2)).drop
            (hL.1.mk.minLength - (2 * k + 2))).take
            (2 * k + n + 3 - hL.1.mk.minLength), by
            apply take_mem ⟨_, _⟩
            simp [mem_subAt]
          have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
            simp [List.length_drop]
            omega
          rw [(show H.x.val[2 * k + 2 + n] =
              (H.x.val.drop (2 * k + 2))[n]'hdrop by
            rw [List.getElem_drop'])]
          rw [List.take_concat_get']
          erw [List.drop_take, ← List.take_add, List.take_eq_take_iff, List.length_drop]
          have := hL.1.mk.le_minLength
          omega
      convert hmem using 1
      exact congrArg (fun xs => xs ++ [H.x.val[2 * k + 2 + n]]) htail_map
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toWLLift] def toLLift' : WLLift' hyp where
  toWLLift := hL.1.mk.toWLLift
  hlift := by
    have h := hL.lift_mem (H.x.val.length - (2 * k + 2))
    rwa [List.take_of_length_le (by simp)] at h
attribute [simp_lengths] toLLift'_toWLLift
end Lost

namespace Losable
variable {H : Lift hyp} (h : H.Losable)
lemma extend {h} (hL : (H.take n h).Losable) (hc : H.ConLong) : H.Losable := by
  use hc; apply WinningPrefix.of_take; simpa [Losable, List.drop_take] using hL.2
lemma losable_of_le {H H' : Lift hyp} (h : H.Losable) (h' : H ≤ H') (hc : H'.ConLong) :
  H'.Losable := by
  simp_rw (config := {singlePass := true}) [← Lift.eq_take_of_le h'] at h; exact h.extend hc
lemma take (hn : 1 ≤ h.2.num + n) :
  (H.take (2 * k + 1 + h.2.num + n) (by as_aux_lemma => omega)).Losable := by
  use H.conLong_take (h := by omega) h.1
  replace h := h.2
  conv at h => simp [List.drop_take]
  conv => simp [List.drop_take]
  apply WinningPrefix.of_take (n := h.num)
  simpa (disch := omega) [List.take_take] using h.shrink
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def x' : (H.game.residual ((H.x.val.drop (2 * k + 1)).take h.2.num)).tree where
  val := H.x.val.drop (2 * k + 1 + h.2.num)
  property := by simpa [PreLift.ConLong] using h.1
attribute [simp_lengths] x'_coe
section «Section3»
variable (hp : IsPosition H.x.val Player.zero)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def a : ExtensionsAt h.x' := h.2.strat h.x' (by have := H.hlvl; synthIsPosition)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension : ExtensionsAt H.x where
  val := (h.a hp).val
  property := by simpa [subAt, ← List.append_assoc] using H.game_tree_sub (h.a hp).prop
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extensionPreLift : PreLift hyp where
  x := (h.extension hp).valT'
  R := H.R
  hlvl := by simp
lemma extensionPreLift_take :
  (h.extensionPreLift hp).take H.x.val.length H.hlvl = H.toPreLift := by
  ext1 <;> simp
@[simp] lemma extensionPreLift_game : (h.extensionPreLift hp).game = H.game := by
  rw [← h.extensionPreLift_take hp]; simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toPreLift] def extensionLift : Lift hyp where
  toPreLift := h.extensionPreLift hp
  h'lvl := by simp
  conShort := by
    rw [← PreLift.conShort_iff_take, extensionPreLift_take]
    · exact H.conShort
    · exact H.hlvl
lemma extensionLift_take :
  (h.extensionLift hp).take H.x.val.length H.h'lvl = H := by
  ext1; apply extensionPreLift_take
lemma extension_losable hp : (h.extensionLift hp).Losable := by
  apply extend
  · rw [extensionLift_take]
    exact h
  · unfold PreLift.ConLong
    conv => simp [extension, ExtensionsAt.val']
    rw [List.drop_append_of_le_length (by simp)]
    simpa [← List.append_assoc] using (h.a hp).prop
end «Section3»
end Losable

variable (H : Lift hyp) (hp : IsPosition H.x.val Player.zero)
  (R : ResStrategy ⟨_, T'⟩ Player.zero H.x.val.length)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def extension : ExtensionsAt H.x := by
  classical
  exact
    if h : H.Lost then h.toLLift'.extensionMap hp R
    else if h : H.Losable then h.extension hp
    else if h : H.Winnable then h.toWLift'.extensionMap hp R
    else Classical.choice (hyp.pruned H.x)
lemma extension_winnable (h : H.Winnable) :
  H.extension hp R = h.toWLift'.extensionMap hp R := by
  unfold extension; split_ifs with h' h'
  · cases h (h'.1.mk.losable h.conLong).2
  · cases h h'.2
  · rfl
end Lift

end «Section1»
end GaleStewartGame.BorelDet.Zero
