/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.Lift

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.TreeLift

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section «Section1»

/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def stratMap (lvl : ℕ) (R : ResStrategy (gameAsTrees hyp) Player.zero lvl) :
  ResStrategy (oldAsTrees hyp) Player.zero lvl := by
  classical
  exact fun x hp hlen ↦
    if hxlen : x.val.length ≤ 2 * k then
      (ResStrategy.fromMap (treeHom hyp)) (R.res hlen) x hp le_rfl
    else
      let pL : PreLift hyp :=
        ⟨x, Nat.lt_of_not_ge hxlen,
          R.res ((Nat.le_of_lt (Nat.lt_of_not_ge hxlen)).trans hlen)⟩
      if hpL : pL.ConShort then
        (Lift.mk pL (by
          have hgt := Nat.lt_of_not_ge hxlen
          have hpos := hp
          unfold pL
          change 2 * k + 1 < x.val.length
          have hne : x.val.length ≠ 2 * k + 1 := by
            intro hEq
            rw [IsPosition] at hpos
            rw [hEq] at hpos
            norm_num at hpos
          omega) hpL).extension hp (R.res hlen)
      else Classical.choice (hyp.pruned x)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def stratMap' (R : Strategy (gameTree hyp) Player.zero) : Strategy G.tree Player.zero :=
  fun x hp ↦ stratMap x.val.length ((strategyEquivSystem R).str _) x hp le_rfl
lemma stratMap'_short R x hp (hx : x.val.length ≤ 2 * k) :
  stratMap' R x hp = (ResStrategy.fromMap (treeHom hyp))
    ((strategyEquivSystem («T» := gameAsTrees hyp) R).str x.val.length)
    x hp le_rfl := by
  unfold stratMap' stratMap
  split_ifs with hxlen
  · rfl
  · exact (hxlen hx).elim

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext 900] structure TreeLift where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  R : Strategy (gameTree hyp) Player.zero
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  x : (stratMap' R).pre.subtree
  hlvl : 2 * k < x.val.length (α := no_index _)
namespace TreeLift
@[ext] lemma ext' {H H' : TreeLift hyp} (hR : H.R = H'.R) (hx : H.x.val = H'.x.val) : H = H' := by
  ext <;> [skip; rw [Subtype.heq_iff_coe_heq]] <;> simp [*]
variable (H : TreeLift hyp)
attribute [simp] hlvl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def preLift : PreLift hyp := ⟨subtreeIncl _ H.x,
  H.hlvl, (strategyEquivSystem H.R).str (2 * k)⟩
attribute [simp_lengths] preLift_x_coe
lemma pInv_fixing (h : n ≤ 2 * k) :
    Fixing (((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)).val.length) (treeHom hyp) := by
    apply Fixing.mon (f := treeHom hyp) (k := 2 * k) inferInstance
    simp only [subtreeIncl_coe, take_coe, List.length_take, min_le_iff, h, true_or]
lemma pInv_isPosition (h : n ≤ 2 * k) {p : Player} (hp : IsPosition (H.x.val.take n) p) :
    IsPosition
      ((pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h)).val) p := by
    rw [IsPosition] at hp ⊢
    rw [pInv_treeHom_val]
    · change (pInvTreeHomMap hyp (List.take n H.x.val)).length % 2 = p.toNat
      rwa [pInvTreeHomMap_len]
    · change (List.take n H.x.val).length ≤ 2 * k
      exact (List.length_take_le n H.x.val).trans h
lemma pInv_fixing_short :
    Fixing (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x)).val.length
      (treeHom hyp) := by
    apply Fixing.mon (f := treeHom hyp) (k := 2 * k) inferInstance
    simp [take_coe]
lemma pInv_isPosition_short :
      IsPosition
        ((pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
          H.pInv_fixing_short).val) Player.zero := by
    rw [IsPosition, pInv_treeHom_val]
    · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length % 2 =
        Player.zero.toNat
      rw [pInvTreeHomMap_len]
      simp [List.length_take, H.hlvl']
    · simp [take_coe]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def take (n : ℕ) (hk : 2 * k < n) : TreeLift hyp where
  R := H.R
  x := Tree.take n H.x
  hlvl := by simp [hk]
attribute [simp_lengths] preLift_x_coe take_x
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by ext1 <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [List.take_take, min_comm]
@[simp] lemma preLift_take hk : (H.take n hk).preLift = H.preLift.take n hk := by ext <;> simp
lemma conShort : H.preLift.ConShort := by
  dsimp [PreLift.ConShort, strategyEquivSystem, preLift,
    PreLift.liftShort, ResStrategy.res, res.val', ExtensionsAt.val']
  change H.x.val[2 * k] = _
  have hx := congr_arg Subtype.val <| subtree_compatible _ (Tree.take (2 * k) H.x)
    (a := H.x.val[2 * k]'H.hlvl) (by have := H.hlvl'; synthIsPosition) (by simp [Tree.take_mem])
  conv at hx => simp [stratMap'_short, strategyEquivSystem, ResStrategy.fromMap]
  simp_all only [ExtensionsAt.valT'_coe]
  have hbaseLen :
      (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
        H.pInv_fixing_short).val.length = 2 * k := by
    rw [pInv_treeHom_val]
    · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length = 2 * k
      rw [pInvTreeHomMap_len]
      simp [List.length_take, H.hlvl']
    · simp [take_coe]
  have hlast :
      ((H.R (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
        H.pInv_fixing_short) H.pInv_isPosition_short).val'[2 * k]'(by
          let a := H.R (pInv (treeHom hyp)
            (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
            H.pInv_fixing_short) H.pInv_isPosition_short
          have hbaseLen' :
              (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
                H.pInv_fixing_short).val.length = 2 * k := hbaseLen
          have htarget : a.val'.length = 2 * k + 1 := by
            calc
              a.val'.length =
                  (pInv (treeHom hyp)
                    (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
                    H.pInv_fixing_short).val.length + 1 := ExtensionsAt.val'_length a
              _ = 2 * k + 1 := by rw [hbaseLen']
          exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self (2 * k)) htarget.symm)).1 =
        (H.R (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
          H.pInv_fixing_short) H.pInv_isPosition_short).val.1 :=
    congrArg Prod.fst (ExtensionsAt.val'_get_last_of_eq _ hbaseLen.symm)
  erw [hlast]
  have harg :
      pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
        (H.pInv_fixing le_rfl) =
      pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
        H.pInv_fixing_short := by
    ext1
    rw [pInv_treeHom_val]
    · rw [pInv_treeHom_val]
      · change pInvTreeHomMap hyp (List.take (2 * k) H.x.val) =
          pInvTreeHomMap hyp (List.take (2 * k) H.x.val)
        rfl
      · change (List.take (2 * k) H.x.val).length ≤ 2 * k
        exact List.length_take_le (2 * k) H.x.val
    · change (List.take (2 * k) H.x.val).length ≤ 2 * k
      exact List.length_take_le (2 * k) H.x.val
  exact congrArg Prod.fst (Strategy.eval_val_congr H.R H.R rfl
    (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
      (H.pInv_fixing le_rfl))
    (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
      H.pInv_fixing_short)
    harg _)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift] def lift (h : 2 * k + 2 ≤ H.x.val.length) : Lift hyp where
  toPreLift := H.preLift
  h'lvl := h
  conShort := H.conShort
attribute [simp_lengths] lift_toPreLift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension (hp : IsPosition H.x.val Player.zero) :=
  (H.lift (by have := H.hlvl; synthIsPosition)).extension hp ((strategyEquivSystem H.R).str _)
@[congr] lemma extension_val_congr {H H' : TreeLift hyp} (h : H = H') {hp} :
  (H.extension hp).val = (H'.extension (by subst h; exact hp)).val := by
  subst h
  rfl
@[simp] lemma lift_take hk h' : (H.take n hk).lift h'
  = (H.lift (by as_aux_lemma => synthIsPosition)).take n
      (by as_aux_lemma => synthIsPosition) := by
  ext1; simp
lemma stratMap'_extend : stratMap' H.R (subtreeIncl _ H.x) = H.extension := by
  ext hp; dsimp [stratMap', stratMap]; split_ifs with h h'
  · change H.x.val.length ≤ 2 * k at h
    have := H.hlvl
    omega
  · rfl
  · cases h' H.conShort
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def dropLast (h : 2 * k + 2 ≤ H.x.val.length) := H.take (H.x.val.length - 1) (by omega)
attribute [simp_lengths] dropLast_x_coe

lemma x_mem_tree h (hp : IsPosition H.x.val Player.one) :
  H.x.val[H.x.val.length - 1]'(by as_aux_lemma => have := H.hlvl; omega)
  = ((H.dropLast h).extension (by as_aux_lemma => synthIsPosition)).val := by
  have hx := H.x.prop
  simp_rw (config := {singlePass := true})
    [H.x.val.eq_take_concat (H.x.val.length - 1) (by as_aux_lemma => have := H.hlvl; omega)] at hx
  replace hx := subtree_compatible _ (Tree.take _ H.x) (by as_aux_lemma => synthIsPosition) hx
  change _ = stratMap' (H.dropLast h).R ⟨(H.dropLast h).x.val, _⟩ _ at hx
  erw [stratMap'_extend] at hx; apply_fun Subtype.val at hx; exact hx
lemma x_mem_tree' h (hp : IsPosition H.x.val Player.one) :
  H.preLift.x = ((H.dropLast h).extension (by as_aux_lemma => synthIsPosition)).valT' := by
  ext1
  conv => simp [ExtensionsAt.val']
  rw [← H.x_mem_tree h hp, ← List.eq_take_concat]; omega

lemma conLong_or_lost : H.preLift.ConLong ∨ ∃ h, (H.lift h).Lost := by
  let ⟨n, hn⟩ := le_iff_exists_add.mp H.hlvl_le
  induction n generalizing H with
  | zero =>
    left
    rw [PreLift.ConLong, ← hn, List.drop_of_length_le (by simp)]
    exact (getTree_ne_and_pruned H.preLift.liftShort).1
  | succ n ih =>
    let Ht := H.dropLast (by omega)
    specialize ih Ht (by simp [Ht, hn])
    by_cases ih' : ∃ h, (Ht.lift h).Lost
    · right; use by omega
      have ⟨h', ih'⟩ := ih'; simp_rw [Ht, dropLast] at ih'
      rw [lift_take _ _ (by simpa [Ht] using h')] at ih'
      apply ih'.extend
    · left; conv at ih => simp [ih']
      by_cases hp : IsPosition H.x.val Player.zero
      · conv at ih => simp [PreLift.ConLong, Ht, dropLast, preLift_take, List.drop_take, hn]
        conv => simp [PreLift.ConLong, Ht, dropLast, preLift_take, List.drop_take, hn]
        rw [(H.x.val.drop (2 * k + 1)).eq_take_concat n (by simp [hn])]
        apply H.preLift.getTree_fair ih (by simp [IsPosition] at hp ⊢; omega) (by
          conv => simp [- List.getElem_drop]
          rw [← H.lift_toPreLift (by omega), Lift.liftShort_val_map]
          simpa [← List.take_add] using subtree_sub _ <| take_mem H.x)
      by_cases ih'' : ∃ h, (Ht.lift h).Losable
      · have hW : (Ht.lift (by dsimp [Ht]; synthIsPosition)).Losable := ih''.2
        conv at ih' => simp
        have hm := H.x_mem_tree' (by as_aux_lemma => omega) (by as_aux_lemma => synthIsPosition)
        conv at hm => simp [extension, Lift.extension, hW, ih', Ht]
        generalize_proofs _ _ hL hp at hm
        convert (hL.extension_losable hp).1; ext1
        · exact hm
        · rfl
      · have hW : (Ht.lift (by dsimp [Ht]; synthIsPosition)).Winnable :=
          fun hW ↦ ih'' ⟨by dsimp [Ht]; synthIsPosition, ⟨ih, hW⟩⟩
        have hm := H.x_mem_tree' (by as_aux_lemma => omega) (by as_aux_lemma => synthIsPosition)
        simp_rw [extension] at hm
        rw [Lift.extension_winnable _ _ _ hW] at hm
        convert hW.extension_conLong (by as_aux_lemma => dsimp [Ht] at *; synthIsPosition)
          ((strategyEquivSystem H.R).str _)
        ext1
        · ext1; simp_rw [hm]; rfl
        · rfl
variable {H} in
lemma lost_of_lost' {h} (hL : (H.lift h).Lost') : (H.lift h).Lost := by
    rcases H.conLong_or_lost with h' | h'
    · use hL; convert H.preLift.conLong_take (h := hL.mk.takeMin.hlvl) h'
      simp [Lift.LLift.takeMin]; congr; simpa using hL.mk.minLength_le
    · exact h'.2

lemma x_mem_tree_short' h' (h : n ≤ 2 * k) (hp : IsPosition (H.x.val.take n) Player.zero) :
    Tree.take (n + 1) (H.lift h').liftShort =
    (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
      (H.pInv_fixing h))
      (H.pInv_isPosition h hp)).valT' := by
  have hx := (Tree.take (n + 1) H.x).prop; have := H.hlvl
  rw [take_coe, ← List.take_concat_get' _ _ (by as_aux_lemma => omega)] at hx
  replace hx := subtree_compatible _ (Tree.take n H.x) hp hx
  simp only [Set.mem_singleton_iff] at hx
  rw [stratMap'_short _ _ _ (by
    simp only [subtreeIncl_coe, take_coe, List.length_take, min_le_iff, h, true_or])] at hx
  rcases h.lt_or_eq with h | rfl
  · have hvalT := congrArg (fun e ↦ e.valT') hx
    apply Fixing.inj (f := treeHom hyp) (ht := by
      apply Fixing.mon (f := treeHom hyp) (k := 2 * k) inferInstance
      rw [take_coe]
      exact (List.length_take_le (n + 1) (H.lift h').liftShort.val).trans (by omega))
    erw [take_apply (treeHom hyp), Lift.liftShort_lift]
    convert hvalT using 1
    case e'_1 => rfl
    case e'_2 =>
      apply heq_of_eq
      ext1
      conv => simp [take_coe, ExtensionsAt.valT', h.le]
      change List.take (n + 1) (List.take (2 * k + 1) H.x.val) =
        List.take n H.x.val ++ [H.x.val[n]]
      rw [List.take_take, min_eq_left (by omega)]
      exact (List.take_concat_get' H.x.val n (by omega)).symm
    case e'_3 =>
      apply heq_of_eq
      exact (ExtensionsAt.map_valT' (f := treeHom hyp)
        (x := pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
          (H.pInv_fixing h.le))
        (y := (stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (h := by simp_rw [cancel_pInv_right])
        (a := H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
          (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp))).symm
  · have harg :
        pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x) =
          pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
            (H.pInv_fixing h) := by
      ext1
      rw [pInv_treeHom_val]
      · rw [pInv_treeHom_val]
        · change pInvTreeHomMap hyp (List.take (2 * k) H.x.val) =
            pInvTreeHomMap hyp (List.take (2 * k) H.x.val)
          rfl
        · change (List.take (2 * k) H.x.val).length ≤ 2 * k
          exact List.length_take_le (2 * k) H.x.val
      · change (List.take (2 * k) H.x.val).length ≤ 2 * k
        exact List.length_take_le (2 * k) H.x.val
    have hval := Strategy.eval_val_congr H.R H.R rfl
      (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
      (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
        (H.pInv_fixing h))
      harg H.preLift.pInv_take_position
    ext1
    conv => simp [← List.take_append_getElem, ExtensionsAt.val']
    constructor <;> (conv => simp [PreLift.liftShort, strategyEquivSystem, ResStrategy.res])
    · change List.take (2 * k)
          (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
            H.preLift.pInv_take_position).val' =
        (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
          (H.pInv_fixing h)).val
      have htake :
          List.take (2 * k)
              (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
                H.preLift.pInv_take_position).val' =
            (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x)).val :=
        ExtensionsAt.val'_take_of_eq _ H.preLift.pInv_take_length.symm
      exact htake.trans (congrArg Subtype.val harg)
    · have hindex :
          2 * k <
            (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
              H.preLift.pInv_take_position).val'.length := by
        let a := H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
          H.preLift.pInv_take_position
        have htarget : a.val'.length = 2 * k + 1 := by
          calc
            a.val'.length =
                (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x)).val.length + 1 :=
              ExtensionsAt.val'_length a
            _ = 2 * k + 1 := by rw [H.preLift.pInv_take_length]
        exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self (2 * k)) htarget.symm
      have hlast :
          ((H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
            H.preLift.pInv_take_position).val'[2 * k]'hindex) =
            (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
              H.preLift.pInv_take_position).val :=
        ExtensionsAt.val'_get_last_of_eq _ H.preLift.pInv_take_length.symm
      change ((H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.preLift.x))
        H.preLift.pInv_take_position).val'[2 * k]'hindex) =
        (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take (2 * k) H.x))
          (H.pInv_fixing h)) (H.pInv_isPosition h hp)).val
      exact hlast.trans hval
lemma x_mem_tree_short h' (h : n ≤ 2 * k) (hp : IsPosition (H.x.val.take n) Player.zero) :
    (H.lift h').liftShort.val[n]'(by simpa [Nat.lt_iff_add_one_le]) =
    (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
      (H.pInv_fixing h))
      (H.pInv_isPosition h hp)).val := by
  have hget := congr_arg (fun x ↦ x.val[n]?) (H.x_mem_tree_short' h' h hp)
  conv at hget => simp
  apply Option.some_injective
  erw [← List.getElem?_eq_getElem (by simpa [Nat.lt_iff_add_one_le]), hget,
    List.getElem?_eq_getElem (by
      have hlen := h_length_pInv (f := treeHom hyp)
        ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)) (H.pInv_fixing h)
      have hnbase :
          n = (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
            (H.pInv_fixing h)).val.length := by
        calc
          n = ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)).val.length := by
            simp [subtreeIncl_coe, take_coe, List.length_take]
            omega
          _ = (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
              (H.pInv_fixing h)).val.length := hlen.symm
      rw [ExtensionsAt.val'_length]
      exact hnbase ▸ Nat.lt_succ_self _)]
  erw [ExtensionsAt.val'_get_last_of_eq _ (by
    have hlen := h_length_pInv (f := treeHom hyp)
      ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)) (H.pInv_fixing h)
    calc
      n = ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)).val.length := by
        simp [subtreeIncl_coe, take_coe, List.length_take]
        omega
      _ = (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
          (H.pInv_fixing h)).val.length := hlen.symm)]

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def WinnableOrLost := ∃ h, (H.lift h).Winnable ∨ (H.lift h).Lost
variable (hWL : H.WinnableOrLost)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def wLLift' := by
  classical
  exact
    if hW : (H.lift hWL.1).Winnable then
      hW.toWLift'
    else
      have hL : (H.lift hWL.1).Lost := by unfold WinnableOrLost at hWL; tauto
      hL.toLLift'
@[simp, simp_lengths] lemma wLLift'_to_lift : (H.wLLift' hWL).toLift = H.lift hWL.1 := by
  unfold wLLift'; split_ifs <;> rfl
lemma wLift'_eq_wLLift' {h} (hW : (H.lift h).Winnable) :
  hW.toWLift' = (H.wLLift' ⟨h, Or.inl hW⟩) := by
  unfold wLLift'; split_ifs <;> rfl
lemma lLift'_eq_wLLift' {h} (hL : (H.lift h).Lost) :
  hL.toLLift' = H.wLLift' ⟨h, Or.inr hL⟩ := by
  unfold wLLift'; split_ifs with h
  · cases h (hL.1.mk.losable h.conLong).2
  · rfl

lemma lift_mem_tree_short n (hn : n < 2 * k + 1) hp :
  (H.wLLift' hWL).liftVal[n]'(by as_aux_lemma => simp; have := H.hlvl; omega) =
  (H.R (Tree.take n ((H.wLLift' hWL).lift)) hp).val := by
  have hl := H.x.prop.2 (y := H.x.val.take n)
    (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
    (by simpa using List.take_prefix _ _) (by as_aux_lemma => synthIsPosition)
  conv => lhs; rw [List.getElem_take' _ hn]
  simp only [WLLift.liftVal_take_short, wLLift'_to_lift]
  erw [H.x_mem_tree_short _ (by as_aux_lemma => omega)
    (by as_aux_lemma => synthIsPosition)]
  congr!
  apply Fixing.inj (f := treeHom hyp) (ht := by
    apply Fixing.mon (f := treeHom hyp) (k := 2 * k) inferInstance
    have hlen := h_length_pInv (f := treeHom hyp)
      ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
      (H.pInv_fixing (by omega))
    calc
      (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
          (H.pInv_fixing (by omega))).val.length =
        ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)).val.length := hlen
      _ ≤ 2 * k := by
        simp [subtreeIncl_coe, take_coe, List.length_take]
        omega)
  ext1
  rw [cancel_pInv_right]
  erw [take_apply (treeHom hyp), WLLift'.lift_lift]
  simp [subtreeIncl_coe, take_coe, wLLift'_to_lift]
  rfl
lemma wLift'_eq_wLLift'_long {h} (hW : (H.lift h).Winnable) hp :
  (H.R (Tree.take n hW.toWLift'.lift) hp).val
  = (H.R (Tree.take n (H.wLLift' ⟨h, Or.inl hW⟩).lift)
    (by as_aux_lemma => synthIsPosition)).val := by simp_rw [wLift'_eq_wLLift']
lemma lLift'_eq_wLLift'_long {h} (hL : (H.lift h).Lost) hp :
  (H.R (Tree.take n hL.toLLift'.lift) hp).val
  = (H.R (Tree.take n (H.wLLift' ⟨h, Or.inr hL⟩).lift)
    (by as_aux_lemma => synthIsPosition)).val := by simp_rw [lLift'_eq_wLLift']

lemma get_eq_get_take (hn : n < H.x.val.length) (hk : 2 * k ≤ n) : H.x.val[n] =
  (H.take (n + 1) (by as_aux_lemma => omega)).x.val[
    (H.take (n + 1) (by as_aux_lemma => omega)).x.val.length - 1]'
    (by as_aux_lemma => simp; omega) := by simp; congr; omega
lemma wLift_mem_tree h (hW : (H.lift h).Winnable) : hW.toWLift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using hW.toWLift'.hlift)
  intro n _ _ _ _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · change _ = H.R (Tree.take n hW.toWLift'.lift) _; ext1
    simp_rw [wLift'_eq_wLLift', wLift'_eq_wLLift'_long]
    apply H.lift_mem_tree_short _ _ hn'
  · apply extensionsAt_ext_fst (x := Tree.take n hW.toWLift'.lift) _ _
      (by as_aux_lemma => synthIsPosition)
    conv => simp; rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition)]
    unfold extension
    rw [Lift.extension_winnable (h := by as_aux_lemma => simpa [dropLast] using hW.take _ _)]
    conv => simp [WLLift'.extensionMap, WLLift'.extension, strategyEquivSystem]
    congr! 1
    apply Strategy.eval_val_congr
    · rfl
    · ext1
      simp only [dropLast, take_coe, take_trans, lift_take, WLLift'.lift_coe,
        Lift.Winnable.toWLift'_toWLLift, Lift.liftVal_take, subtreeIncl_coe,
        List.take_eq_take_iff]
      synthIsPosition
--show statements about extension map in common setting?
lemma lLift_mem_tree h (hL : (H.lift h).Lost) : hL.toLLift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using hL.toLLift'.hlift)
  intro n hn _ _ _
  simp only [Lift.Lost.toLLift'_toWLLift]
  rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · change _ = H.R (Tree.take n hL.toLLift'.lift) _; apply Subtype.ext
    simp_rw [lLift'_eq_wLLift'_long, ← H.lift_mem_tree_short ⟨h, Or.inr hL⟩ _ hn',
      ← lLift'_eq_wLLift' _ hL]; rfl
  by_cases hL' : (((H.take n (by as_aux_lemma => omega))).lift
      (by as_aux_lemma => synthIsPosition)).Lost'
  · apply extensionsAt_ext_fst (x := Tree.take n hL.toLLift'.lift) _ _
      (by as_aux_lemma => synthIsPosition)
    conv => simp
    generalize_proofs --not for performance
    rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition)]
    dsimp [extension, Lift.extension]; split
    · conv => simp [WLLift'.extensionMap, WLLift'.extension, strategyEquivSystem]
      congr! 1
      apply Strategy.eval_val_congr
      · rfl
      · ext1
        simp only [dropLast, take_x, take_coe, List.length_take, take_trans, lift_take,
          subtreeIncl_coe, WLLift'.lift_coe]
        generalize_proofs _ prf
        simp (disch := omega) only [min_eq_left, min_eq_right] at prf
        change _ = ((H.lift h).extend' prf.1).toWLLift.liftVal.take n
        simp only [Lift.Lost.toLLift'_toWLLift]
        have hnx : n < H.x.val.length := by simpa [Lift.Lost.toLLift'_toWLLift] using hn
        convert (Lift.liftVal_extend' prf.1).symm using 2
        · ext1
          · simp [hnx]
          · simp [Lift.LLift.toWLLift, Lift.Lost'.mk, Lift.LLift.takeMin, take_coe, hnx,
              ]
        all_goals omega
    · rename_i _ hif; cases hif (lost_of_lost' (by
        conv at hL' => simp [dropLast]
        conv => simp [dropLast]
        convert hL'; synthIsPosition))
  · simp at hn
    apply extensionsAt_eq_of_lost (x := Tree.take n hL.toLLift'.lift) hL.toLLift'.lift
      (List.take_prefix _ _) (by as_aux_lemma => synthIsPosition)
    · unfold Lift.Lost' at hL'; convert hL' using 2
      · change (treeHom hyp (Tree.take n hL.toLLift'.lift)).val =
          ((H.take n (by omega)).lift (by synthIsPosition)).x.val
        rw [take_apply (treeHom hyp)]
        simp [Lift.Lost.toLLift'_toWLLift, WLLift'.lift_lift, take_coe, lift_take]
        rfl
      · synthIsPosition
    · let hLost := hL
      have hLost' := hLost.1
      unfold Lift.Lost' at hLost'
      convert hLost' using 1
      · change (treeHom hyp hLost.toLLift'.lift).val = (H.lift h).x.val
        rw [WLLift'.lift_lift]
        simp [Lift.Lost.toLLift'_toWLLift]
      · synthIsPosition

lemma losable_subtree {h} (hL : (H.lift h).Losable) (hnL : ¬ ∃ h', ((H.dropLast h).lift h').Lost) :
  H.x.val.drop (2 * k + 1 + hL.2.num) ∈ hL.2.strat.pre.subtree := by
  apply subtree_induction (S := ⊤) (by
    refine ⟨?_, ?_⟩
    · simp only [lift_toPreLift, preLift_x_coe, residual_tree, mem_subAt,
        List.drop_take_append_drop]
      exact hL.1
    · intros
      exact Set.mem_univ _)
  intro n hn _ _ _
  conv at hn => simp
  conv => simp
  have htr := (H.take (2 * k + 1 + hL.2.num + n + 1) (by as_aux_lemma => omega)).x_mem_tree
    (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition); conv at htr => simp
  simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel] at htr
  apply Subtype.ext; dsimp; rw [htr]
  simp only [dropLast, take_x, take_coe, List.length_take, take_trans, tsub_le_iff_right,
    min_le_iff, le_add_iff_nonneg_right, zero_le, true_or, min_eq_right, lift_toPreLift,
    preLift_x_coe]; simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel]
  generalize_proofs pf1 pf2
  have : ((H.take (2 * k + 1 + pf1.num + n) pf2).lift (by synthIsPosition)).Losable :=
    hL.take (by synthIsPosition)
  dsimp [extension, Lift.extension]; split_ifs with hi
  · cases hnL ⟨by synthIsPosition, by
      apply hi.lost_of_le
      conv => simp [dropLast]
      exact (Lift.take_le_take _ _ _).mpr (Or.inl (by
        rw [hL.2.prefix_num (by simp) (by simp) rfl]
        have hbound : n + (2 * k + 1 + hL.2.num) < H.x.val.length := Nat.lt_sub_iff_add_lt.mp hn
        omega))
      ⟩
  · symm; unfold Lift.Losable.extension Lift.Losable.a Lift.Losable.x'
    apply this.2.prefix_strat_apply' ((List.take_prefix _ _).drop _) (by simp) rfl
    · conv => simp [List.take_drop]
      congr 2
      generalize_proofs pf3
      exact pf3.prefix_num ((List.take_prefix _ _).drop _) rfl rfl
end TreeLift

end «Section1»
end GaleStewartGame.BorelDet.Zero
