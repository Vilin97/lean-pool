/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.PreLift

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.Lift

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section «Section1»

namespace Lift'
variable (H : Lift' hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension (hp : IsPosition H.x.val Player.one)
    (R : ResStrategy (gameAsTrees hyp) Player.one H.x.val.length) :=
  R H.lift (by
    change H.liftVal.length % 2 = Player.one.toNat
    rw [H.liftVal_length]
    exact hp) (by
    change H.liftVal.length ≤ H.x.val.length
    rw [H.liftVal_length])
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extensionMap (hp : IsPosition H.x.val Player.one)
    (R : ResStrategy (gameAsTrees hyp) Player.one H.x.val.length) :=
  ExtensionsAt.map (treeHom hyp) H.lift_lift (H.extension hp R)
variable (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy (gameAsTrees hyp) Player.one H.x.val.length) (hR : R.res (by simp) = H.R)
@[simp] lemma extension_take :
  (H.extension hp R).val' (A := no_index _).take (α := no_index _)
    (H.x.val.length (α := no_index _))
  = H.liftVal := ExtensionsAt.val'_take_of_eq _ H.liftVal_length.symm
@[simp] lemma extensionMap_take (h : n ≤ H.x.val.length) :
  (H.extensionMap hp R).val' (A := no_index _).take (α := no_index _) n
  = H.x.val.take n := ExtensionsAt.val'_take_of_le _ h
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extensionLift : Lift hyp where
  x := (H.extensionMap hp R).valT'
  R := H.R
  hlvl := by
    have hlen := ExtensionsAt.val'_length (H.extensionMap hp R)
    change 2 * k < (H.extensionMap hp R).val'.length
    rw [hlen]
    exact Nat.lt_of_lt_of_le H.hlvl (Nat.le_succ _)
  liftTree := H.liftTree
  htree := by
    obtain ⟨S, hS⟩ := H.htree
    have htake : (H.extensionMap hp R).val'.take (2 * k + 1) =
        H.x.val.take (2 * k + 1) :=
      H.extensionMap_take hp R (n := 2 * k + 1) (by have := H.hlvl; omega)
    have hsub : subAt G.tree (H.x.val.take (2 * k + 1)) =
        subAt G.tree ((H.extensionMap hp R).val'.take (2 * k + 1)) :=
      congrArg (subAt G.tree) htake.symm
    use cast (congrArg (fun T => QuasiStrategy T Player.one) hsub) S
    rw [hS]; symm; apply cast_subtree hsub rfl
@[simp] lemma extensionLift_take :
  (H.extensionLift hp R).take (H.x.val.length (α := no_index _)) (by simp) = H.toLift := by
  ext1
  · ext1
    · exact ExtensionsAt.valT'_take _
    · rfl
  · rfl
@[simp] lemma extensionLift_liftShort : (H.extensionLift hp R).liftShort = H.liftShort := by
  rw [← extensionLift_take, Lift.liftShort_take]
@[simp] lemma extensionLift_wonPos : (H.extensionLift hp R).WonPos = H.WonPos := by
  rw [← extensionLift_take]
  conv => simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toLift] def extensionLift' : Lift' hyp where
  toLift := H.extensionLift hp R
  con := by
    let a : upA hyp := (H.extension hp R).val
    have hprop : H.lift.val ++ [a] ∈ gameTree hyp := (H.extension hp R).prop
    have hvalid := ((gameTree_concat H.lift.val a).mp hprop).2
    have h := hvalid.1
    erw [getTree_eq H.lift] at h; conv at h => simp
    conv => simp [Lift.Con, ExtensionsAt.val']
    by_cases hl : H.x.val.length = 2 * k + 1
    · have hlift : H.lift = H.liftVeryShort := by
        ext1
        exact H.liftVal_very_short hl
      rw [mem_pullSub_short (by
        rw [List.length_drop]
        simp only [List.length_singleton]
        change (H.extensionMap hp R).val'.length - (2 * k + 1) ≤ 1
        rw [ExtensionsAt.val'_length]
        calc
          H.x.val.length + 1 - (2 * k + 1) = 1 := by omega
          _ ≤ 1 := le_rfl)]
      constructor
      · conv => simp [hl, extensionMap]
        unfold extension Lift.liftShort
        have hpVeryShort : IsPosition H.liftVeryShort.val Player.one := by
          change H.liftVeryShort.val.length % 2 = Player.one.toNat
          rw [H.liftVeryShort_length]
          synthIsPosition
        have hleVeryShort : H.liftVeryShort.val.length ≤ H.x.val.length := by
          calc
            H.liftVeryShort.val.length = 2 * k + 1 := H.liftVeryShort_length
            _ ≤ H.x.val.length := by omega
        have hleVeryShortBound : H.liftVeryShort.val.length ≤ 2 * k + 1 := by
          rw [H.liftVeryShort_length]
        have hlast := ExtensionsAt.val'_get_last_of_eq
          (H.R H.liftVeryShort hpVeryShort hleVeryShortBound)
          (n := 2 * k + 1) H.liftVeryShort_length.symm
        have hlast1 := congrArg Prod.fst hlast
        simp only [ExtensionsAt.valT'_coe] at hlast1 ⊢
        erw [hlast1]
        rw [← hR]
        conv => simp [ResStrategy.res]
        have hval := ResStrategy.eval_val_congr' R R rfl H.lift H.liftVeryShort hlift
          (by
            change H.liftVal.length % 2 = Player.one.toNat
            rw [H.liftVal_length]
            exact hp)
          (by
            change H.liftVal.length ≤ H.x.val.length
            rw [H.liftVal_length])
        have hdrop :
            List.drop (2 * k + 1) (H.x.val ++ [(H.extension hp R).val.1]) =
              [(H.extension hp R).val.1] := by
          rw [List.drop_append_of_le_length (by omega : 2 * k + 1 ≤ H.x.val.length)]
          rw [List.drop_eq_nil_of_le (by omega : H.x.val.length ≤ 2 * k + 1)]
          rfl
        have hval1 : (H.extension hp R).val.1 =
            (R H.liftVeryShort hpVeryShort hleVeryShort).val.1 :=
          congrArg Prod.fst hval
        refine hdrop.symm ▸ ?_
        rw [hval1]
      · exact (getTree_ne_and_pruned H.liftShort).1
    · have hlong : 2 * k + 2 ≤ H.x.val.length := by
        have := H.hlvl
        omega
      rw [mem_pullSub_long (by
        rw [List.length_drop]
        simp only [List.length_singleton]
        change 1 ≤ (H.extensionMap hp R).val'.length - (2 * k + 1)
        rw [ExtensionsAt.val'_length]
        calc
          1 ≤ H.x.val.length + 1 - (2 * k + 1) := by omega)]
      use H.x.val.drop (2 * k + 2) ++ [(H.extension hp R).val.1]; constructor
      · have htail : List.map Prod.fst (List.drop (2 * k + 2) H.liftVal) =
            List.drop (2 * k + 2) H.x.val := by
          rw [List.map_drop, H.liftVal_lift]
        have htake : List.take (2 * k + 2) H.liftVal = H.liftShort.val := by
          rwa [H.liftVal_take_short]
        rwa [← htail, ← htake]
      · conv => lhs; rw [show (H.extensionMap hp R).val = (H.extension hp R).val.1 by
            simp [extensionMap]]
        have hdropAppend :
            List.drop (2 * k + 1) (H.x.val ++ [(H.extension hp R).val.1]) =
              List.drop (2 * k + 1) H.x.val ++ [(H.extension hp R).val.1] := by
          rw [List.drop_append_of_le_length (by omega : 2 * k + 1 ≤ H.x.val.length)]
        have hdropX :
            List.drop (2 * k + 1) H.x.val =
              [H.x.val[2 * k + 1]] ++ List.drop (2 * k + 2) H.x.val := by
          rw [List.drop_eq_getElem_cons (by omega)]
          rfl
        exact hdropAppend.trans <| by
          rw [hdropX]
          rw [H.conShort hlong]
          rfl
attribute [simp_lengths] extensionLift_x extensionLift'_toLift
lemma extensionLift'_game : (H.extensionLift' hp R hR).game = H.game := by
  have htake :
      (H.extensionMap hp R).val'.take (α := no_index _) (2 * k + 1) =
        H.x.val.take (α := no_index _) (2 * k + 1) :=
    H.extensionMap_take hp R (n := 2 * k + 1) (by have := H.hlvl; omega)
  ext x <;> conv => simp [PreLift.game]
  · exact htake ▸ Iff.rfl
  · intro y hy hxy
    exact htake ▸ Iff.rfl
@[simp] lemma extensionLift'_take :
  (H.extensionLift' hp R hR).take (H.x.val.length (α := no_index _)) (by simp) = H := by
  ext1; apply extensionLift_take
end Lift'

namespace PreLift
lemma Losable'.losable'_of_le {H H' : PreLift hyp} (hL : H'.Losable') (h : H ≤ H') :
  H.Losable' := by
  intro hW; apply hL; rw [← h] at hW; simp [List.drop_take] at hW; exact hW.of_take
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure LLift extends PreLift hyp where
  los : toPreLift.Losable'
namespace LLift
variable (H : LLift hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def S := defensiveQuasi H.game Player.one (hyp.pruned.sub _)
lemma S_winning : H.S.1.IsWinning :=
  H.game.gale_stewart_precise' H.game_open (hyp.pruned.sub _) (by
    intro h; apply H.los; use 0; simpa)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toPreLift liftTree] def toLift := H.extend H.S
attribute [simp_lengths] toLift_toPreLift
lemma toLift_mono {H H' : LLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.toLift.liftTree = H'.toLift.liftTree := by
  change (defensiveQuasi H.game Player.one (hyp.pruned.sub _)).1.subtree =
    (defensiveQuasi H'.game Player.one (hyp.pruned.sub _)).1.subtree
  have hG : H.game = H'.game := by
    rw [← h]
    ext x <;> simp [PreLift.game, List.take_take]
  exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _
lemma winning_condition : WinningCondition H.toLift.liftShort.val (by simp) := by
  rw [← not_losing]; apply _root_.not_imp_self.mp; intro hlos
  unfold LosingCondition; conv => simp [Set.eq_empty_iff_forall_notMem]
  intro _ u hu1 hu2
  have hget : getTree' hyp H.toLift.liftVeryShort.val = H.S.fst.subtree := by
    let node : (gameAsTrees hyp).fst := (H.x.val[2 * k]'H.hlvl, H.S.fst.subtree)
    change getTree' hyp ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++ [node]) =
      node.2
    exact getTree_concat ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val) node
  have hu1S : H.toLift.liftShort.val[2 * k + 1].1 :: u ∈ H.S.fst.subtree := by
    simpa [hget] using hu1
  let qS : QuasiStrategy (H.game.residual _).tree _ :=
    (H.game.defensiveQuasi Player.one (hyp.pruned.sub _)).residual
    (H.toLift.liftShort.val[2 * k + 1].1 :: u)
  have := not_imp_not.mpr (AllWinning.existsWinning (hP := (hyp.pruned.sub _).sub _))
    ((existsWinning_iff_quasi.mpr ⟨qS, H.S_winning.residual ⟨_, hu1S⟩⟩).not_both_winning
    (by simpa using subtree_sub _ hu1S))
  apply this
  simp only [Player.residual_cons, Player.residual_swap, Player.swap_one, Player.swap_zero]
  rw [AllWinning, Player.payoff_residual]
  conv => simp [Player.residual_cons, Player.residual_swap, Player.swap_one,
    Player.swap_zero, game_payoff]
  apply Set.eq_univ_iff_forall.mpr
  intro a
  have hWon : H.toLift.liftShort.val[2 * k + 1].1 :: u ∈ H.WonPos := by
    unfold WonPos; use defensiveQuasi H.game Player.one (hyp.pruned.sub _)
    unfold Lift.PreWonPos
    conv => simp
    use of_not_not hlos, rfl
    rw [List.append_cons]
    convert hu2 using 4
    · rfl
    · have hconcat := congrArg (List.map Prod.fst)
        (H.toLift.liftShort.val.eq_take_concat (2 * k + 1) (by simp))
      rw [hconcat]
      erw [List.map_append, List.map_singleton]
      rw [H.toLift.liftShort_val_take, H.toLift.liftVeryShort_val_map]
      rfl
  apply Set.mem_iUnion₂_of_mem hWon
  change (body.append (H.toLift.liftShort.val[2 * k + 1].1 :: u) a).val ∈
    principalOpen (H.toLift.liftShort.val[2 * k + 1].1 :: u)
  simp [body.append]
lemma concat_mem_tree {y a} (hp : IsPosition y Player.zero)
  (ha : H.x.val.take (2 * k + 1) ++ H.toLift.liftShort.val[2 * k + 1].1 :: (y ++ [a]) ∈
    G.tree)
  (hy : y ∈ getTree' hyp H.toLift.liftShort.val)
  (hw : ¬ H.game.WinningPosition (H.toLift.liftShort.val[2 * k + 1].1 :: y ++ [a])) :
  y ++ [a] ∈ getTree' hyp H.toLift.liftShort.val := by
  classical
  obtain ⟨_, S', hS⟩ := H.winning_condition
  rw [hS] at hy ⊢; rw [subtree_fair _ ⟨_, hy⟩ hp]; conv => simp [Lift.liftVeryShort]
  have hget : getTree' hyp H.toLift.liftVeryShort.val = H.S.fst.subtree := by
    let node : (gameAsTrees hyp).fst := (H.x.val[2 * k]'H.hlvl, H.S.fst.subtree)
    change getTree' hyp ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++ [node]) =
      node.2
    exact getTree_concat ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val) node
  have hyS : H.toLift.liftShort.val[2 * k + 1].1 :: y ∈ H.S.fst.subtree := by
    simpa [hget] using hy.1
  let node : upA hyp := (H.x.val[2 * k], H.S.fst.subtree)
  have htarget : getTree' hyp (pInvTreeHomMap hyp (H.x.val.take (2 * k)) ++ [node]) =
      H.S.fst.subtree := getTree_concat (pInvTreeHomMap hyp (H.x.val.take (2 * k))) node
  change H.toLift.liftShort.val[2 * k + 1].1 :: y ++ [a] ∈
    getTree' hyp (pInvTreeHomMap hyp (H.x.val.take (2 * k)) ++ [node])
  rw [htarget, subtree_compatible_iff _ ⟨_, hyS⟩ (by synthIsPosition)]
  have hx : (H.toLift.liftShort.val[2 * k + 1].1 :: y) ++ [a] ∈ H.game.tree := by
    change H.x.val.take (2 * k + 1) ++
      ((H.toLift.liftShort.val[2 * k + 1].1 :: y) ++ [a]) ∈ G.tree
    simpa [List.cons_append, List.append_assoc] using ha
  refine ⟨hx, ?_⟩
  change ⟨a, hx⟩ ∈
    (if {b : ExtensionsAt (H.S.fst.subtreeIncl
        ⟨H.toLift.liftShort.val[2 * k + 1].1 :: y, hyS⟩) |
          ¬ H.game.WinningPosition
            (H.toLift.liftShort.val[2 * k + 1].1 :: (y ++ [b.val]))}.Nonempty then
      {b : ExtensionsAt (H.S.fst.subtreeIncl
        ⟨H.toLift.liftShort.val[2 * k + 1].1 :: y, hyS⟩) |
          ¬ H.game.WinningPosition
            (H.toLift.liftShort.val[2 * k + 1].1 :: (y ++ [b.val]))}
    else Set.univ)
  conv => simp [Set.nonempty_def]
  intro _ _
  exact hw
end LLift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Losable (H : PreLift hyp) := ∃ h : H.Losable', (LLift.mk _ h).toLift.Con
lemma Losable.losable_of_le {H H' : PreLift hyp} (hL : H'.Losable) (h : H ≤ H') :
  H.Losable := by
  use hL.1.losable'_of_le h; (conv => rhs; rhs; lhs; rw [← h])
  convert hL.2.take (n := H.x.val.length) (h := by simp); ext1
  · simp
  · simp only [LLift.toLift_liftTree, LLift.S, Lift.take_liftTree]
    have hG : (H'.take H.x.val.length H.hlvl).game = H'.game := by
      ext x <;> simp [PreLift.game, List.take_take]
    exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _

/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def Losable.lift' {H : PreLift hyp} (h : H.Losable) := Lift'.mk _ h.2
attribute [simp_lengths] Losable.lift'_toLift

lemma Won.won_of_le {H H' : PreLift hyp} (hW : H.Won) (h : H ≤ H') : H'.Won := by
  rw [← h, Won, wonPos_take, take_x, take_coe, List.drop_take] at hW
  obtain ⟨u, hu, h⟩ := hW; exact ⟨u, hu, h.trans <| List.take_prefix _ _⟩
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure WLift extends PreLift hyp where
  won : toPreLift.Won
namespace WLift
variable (H : WLift hyp)
lemma winnable : H.Winnable := by
  let ⟨u, hu, hux⟩ := H.won; use u.length
  apply AllWinning.existsWinning _ ((hyp.pruned.sub _).sub _)
  rw [List.prefix_iff_eq_take] at hux
  rw [AllWinning, Player.payoff_residual]
  conv => simp [Player.residual_cons, Player.residual_swap, Player.swap_one,
    Player.swap_zero, game_payoff]
  apply Set.eq_univ_iff_forall.mpr
  intro a
  apply Set.mem_iUnion₂_of_mem hu
  change List.take u.length (List.drop (2 * k + 1) H.x.val) ++ₛ a ∈ principalOpen u
  convert principalOpen_append_nil a (List.take u.length (List.drop (2 * k + 1) H.x.val)) using 1
  exact congrArg principalOpen hux
lemma exists_prefix : ∃ n h, (H.take n h).Won := ⟨H.x.val.length, by simpa using H.won⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def minLength := by
  classical
  exact Nat.find H.exists_prefix
@[simp] lemma minLength_le : H.minLength ≤ H.x.val.length (α := no_index _) := by
  classical
  exact Nat.find_le ⟨H.hlvl, by simpa using H.won⟩
lemma le_minLength : 2 * k + 1 ≤ H.minLength := by
  classical
  exact (Nat.find_spec H.exists_prefix).1
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma le_minLength' : 2 * k ≤ H.minLength := le_trans (Nat.le_succ _) H.le_minLength
/-- Auxiliary declaration for the Borel determinacy formalization. -/
lemma lt_minLength : 2 * k < H.minLength := H.le_minLength
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def takeMin := H.take H.minLength H.lt_minLength
@[simp] lemma takeMin_wonPos : H.takeMin.WonPos = H.WonPos := by simp [takeMin]
lemma min_prefix : H.takeMin.Won := by
  classical
  exact (Nat.find_spec H.exists_prefix).2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def u : H.WonPos := ⟨H.min_prefix.choose, by simpa using H.min_prefix.choose_spec.1⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def S := H.u.prop.choose
lemma u_spec : H.u.val <+: H.takeMin.x.val.drop (2 * k + 1) := H.min_prefix.choose_spec.2
lemma u_spec' : H.u.val <+: H.x.val.drop (2 * k + 1) :=
  H.u_spec.trans <| (List.take_prefix _ _).drop _
lemma u_nil : H.u.val ≠ [] := H.u.prop.choose_spec.2.1.1
@[simp] lemma getTree_liftShort : getTree' hyp (H.extend H.S).liftShort.val =
  pullSub (subAt G.tree (H.x.val.take (2 * k + 1) ++ H.u.val)) H.u.val.tail :=
  H.u.prop.choose_spec.2.2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toPreLift liftTree] def toLift := H.extend H.S
lemma u_zero : H.u.val[0]'(by simpa [List.length_pos_iff] using H.u_nil)
  = H.toLift.liftShort.val[2 * k + 1].1 := H.u.prop.choose_spec.2.1.2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toLift] def toLift' : Lift' hyp where
  toLift := H.toLift
  con := by
    simp_rw [Lift.Con]; erw [WLift.getTree_liftShort]
    conv => simp
    have := H.hlvl; have hu := H.u_spec'
    by_cases hl : H.x.val.length = 2 * k + 1
    · rw [mem_pullSub_short (by simp [hl])]
      conv => simp [← hl]
      change H.u.val ∈ subAt G.tree H.x.val
      apply mem_of_prefix hu
      rw [← hl]
      simp
    · rw [mem_pullSub_long (by
        have := hu.length_le; synthIsPosition)]
      obtain ⟨z, hz⟩ := hu
      use z
      conv => simp [hz]
      rw [← (H.x.val.drop _).cons_head_tail (by synthIsPosition)]
      congr
      · conv => simp [List.head_drop, ← WLift.u_zero]
        change H.x.val[(2 * k + 1) + 0] = _
        rw [List.getElem_drop']; simp_rw [← hz]; rw [List.getElem_append_left]
      · apply_fun List.tail at hz; simp at hz; simp [← hz]
        simp [WLift.u_nil]
attribute [simp_lengths] toLift_toPreLift toLift'_toLift

universe u v in
lemma hEq_fst {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v}
  (x : @PSigma α β) (y : @PSigma α' β') (h : α = α') (h' : HEq β β') (h'' : HEq x y) :
  HEq x.fst y.fst := by subst h; cases h'; cases h''; rfl
lemma minLength_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.minLength = H'.minLength := by
  classical
  apply le_antisymm
  · apply Nat.find_le; use H'.le_minLength; convert H'.min_prefix
    rw [← h]
    conv => simp
    congr
    conv => simp
    apply Nat.find_le; use H.hlvl; rw [h]; exact H.won
  · apply Nat.find_mono; intro n ⟨hn, hW⟩; use hn
    apply hW.won_of_le; rw [← h]; simp; congr 1; have := length_mono h; omega
lemma takeMin_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.takeMin = H'.takeMin := by unfold takeMin; simp_rw [← minLength_eq_le h]; rw [← h]; simp
lemma u_eq_le {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) : HEq H.u H'.u := by
  unfold u; congr! 1
  · congr! 2; rw [← h]; simp
  · congr! 1; rw [takeMin_eq_le h]
@[simp] lemma u_min_prefix : (WLift.mk _ H.min_prefix).u.val = H.u.val := by
  have := u_eq_le (H := WLift.mk _ H.min_prefix) (H' := H) (by simp [takeMin])
  rwa [Subtype.heq_iff_coe_eq (by simp)] at this
lemma uprop' : (WLift.mk _ H.min_prefix).u.val ∈ H.takeMin.WonPos := by simp
lemma uprop'_choose : HEq H.u.prop.choose H.uprop'.choose := by
  congr 1
  · simp [List.take_take, WLift.le_minLength H]
  · congr! 1 with S1 S2 heq
    · simp [List.take_take, H.le_minLength]
    · rw [← cast_eq_iff_heq (e := by simp [List.take_take, H.le_minLength])] at heq
      have htake : H.takeMin.extend S2 = (H.extend S1).take H.minLength H.le_minLength := by
        rw [← heq]
        change (H.take H.minLength H.lt_minLength).extend
            (cast (by simp [List.take_take, H.lt_minLength]) S1) =
          (H.extend S1).take H.minLength H.le_minLength
        rw [PreLift.extend_take (h := H.lt_minLength)]
        simp
      have : (H.extend S1).liftShort = (H.takeMin.extend S2).liftShort := by
        rw [htake]
        exact (Lift.liftShort_take (H := H.extend S1) H.le_minLength).symm
      simp only [Lift.PreWonPos, ne_eq, extend_toPreLift, u_min_prefix, takeMin_x_coe]; congr! 6
      · simp [this]
      · simp [List.take_take, H.le_minLength]
  · apply proof_irrel_heq
lemma toLift_liftTree' : H.toLift.liftTree = H.uprop'.choose.1.subtree := by
  simp only [toLift_liftTree, S]
  congr! 1
  · simp [List.take_take, H.le_minLength]
  · apply hEq_fst
    · simp [List.take_take, H.le_minLength]
    · congr!
    · exact H.uprop'_choose
lemma toLift_mono {H H' : WLift hyp} (h : H.toPreLift ≤ H'.toPreLift) :
  H.toLift.liftTree = H'.toLift.liftTree := by
  simp_rw [toLift_liftTree']
  have hu := u_eq_le h
  rw [Subtype.heq_iff_coe_eq] at hu
  · congr! 1
    · rw [takeMin_eq_le h]
    · apply hEq_fst
      · rw [takeMin_eq_le h]
      · congr!
      · congr 1
        · congr
        · congr! 3
          · rw [takeMin_eq_le h]
          · congr! 3; rw [takeMin_eq_le h]
          · congr! 2; rw [takeMin_eq_le h]
        · apply proof_irrel_heq
  · rw [← h]
    simp
end WLift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toLift] def Won.lift' {H : PreLift hyp} (h : H.Won) := (WLift.mk _ h).toLift'
attribute [simp_lengths] Won.lift'_toLift

namespace Winnable
lemma winnable_of_le {H H' : PreLift hyp} (hW : H.Winnable) (h : H ≤ H') : H'.Winnable := by
  rw [← h] at hW; simp [Winnable, List.drop_take] at hW; exact hW.of_take
variable {H : PreLift hyp} (h : H.Winnable)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def takeMin := H.take (2 * k + 1 + h.num) (by omega)
lemma takeMin_winnable : h.takeMin.Winnable := by
  simpa [Winnable, takeMin, List.drop_take] using h.shrink
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def x' : (H.game.residual ((H.x.val.drop (2 * k + 1)).take h.num)).tree :=
  ⟨H.x.val.drop (2 * k + 1 + h.num), by simp [game]⟩
attribute [simp_lengths] x'_coe
variable (hp : IsPosition H.x.val Player.one)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def a : ExtensionsAt h.x' := h.strat h.x' (by have := H.hlvl; synthIsPosition)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension : ExtensionsAt H.x where
  val := (h.a hp).val
  property := by
    have h' := (h.a hp).prop; conv at h' => simp [game]; conv => simp [game]
    simp_rw [← List.drop_drop (j := 2 * k + 1), ← List.append_assoc _ _ [_],
      List.take_append_drop] at h'; exact h'
end Winnable

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension (H : PreLift hyp) (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy (gameAsTrees hyp) Player.one H.x.val.length) : ExtensionsAt H.x := by
  classical
  exact
    if h : H.Won then h.lift'.extensionMap hp R
    else if h : H.Winnable then h.extension hp
    else if h : H.Losable then h.lift'.extensionMap hp R
    else Classical.choice (hyp.pruned H.x)
lemma extension_losable {H : PreLift hyp} (h : H.Losable) hp R :
  H.extension hp R = h.lift'.extensionMap hp R := by
  unfold extension; split_ifs with h' h'
  · cases h.1 (WLift.mk _ h').winnable
  · cases h.1 h'
  · rfl
end PreLift

end «Section1»
end GaleStewartGame.BorelDet.One
