/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.Lift

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.Strat

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section «Section1»

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def stratMap (lvl : ℕ) (R : ResStrategy (gameAsTrees hyp) Player.one lvl) :
  ResStrategy (oldAsTrees hyp) Player.one lvl := fun x hp hlen ↦
  if hxlen : x.val.length ≤ 2 * k then (ResStrategy.fromMap (treeHom hyp)) (R.res hlen) x hp le_rfl
  else
    let pL : PreLift hyp :=
      ⟨x, Nat.lt_of_not_ge hxlen,
        R.res ((Nat.succ_le_of_lt (Nat.lt_of_not_ge hxlen)).trans hlen)⟩
    pL.extension hp (R.res hlen)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def stratMap' (R : Strategy (gameTree hyp) Player.one) : Strategy G.tree Player.one :=
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
  R : Strategy (gameTree hyp) Player.one
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  x : (stratMap' R).pre.subtree
  hlvl : 2 * k < x.val.length (α := no_index _)
namespace TreeLift
variable (H : TreeLift hyp)
@[ext] lemma ext' {H H' : TreeLift hyp} (hR : H.R = H'.R) (hx : H.x.val = H'.x.val) : H = H' := by
  ext
  · simp [hR]
  · rw [Subtype.heq_iff_coe_heq rfl (by simp [hR])]
    simpa
attribute [simp] TreeLift.hlvl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps!] def preLift : PreLift hyp := ⟨subtreeIncl _ H.x,
  H.hlvl, (strategyEquivSystem H.R).str (2 * k + 1)⟩
attribute [simp_lengths] preLift_x_coe
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def take (n : ℕ) (hk : 2 * k < n) : TreeLift hyp where
  R := H.R
  x := Tree.take n H.x
  hlvl := by simp [hk]
attribute [simp_lengths] take_x
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by ext1 <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [List.take_take, min_comm]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma preLift_take hk : (H.take n hk).preLift = H.preLift.take n hk := by ext <;> simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension hp := H.preLift.extension hp ((strategyEquivSystem H.R).str _)
@[congr] lemma extension_val_congr {H H' : TreeLift hyp} (h : H = H') {hp} :
  (H.extension hp).val = (H'.extension (by subst h; exact hp)).val := by
  subst h
  rfl
lemma stratMap'_extend : stratMap' H.R (subtreeIncl _ H.x) = H.extension := by
  ext hp; dsimp [stratMap', stratMap]; split_ifs with h
  · change H.x.val.length ≤ 2 * k at h
    have := H.hlvl
    omega
  · rfl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! -isSimp] def dropLast (h : 2 * k + 2 ≤ H.x.val.length) :=
  H.take (H.x.val.length - 1) (by omega)
@[simp, simp_lengths] lemma dropLast_x {h} :
  (H.dropLast h).x = Tree.take (H.x.val.length - 1) H.x := rfl

lemma x_mem_tree h (hp : IsPosition H.x.val Player.zero) :
  H.x.val[H.x.val.length - 1]'(by as_aux_lemma => have := H.hlvl; omega)
  = ((H.dropLast h).extension (by as_aux_lemma => synthIsPosition)).val := by
  have hx := H.x.prop
  simp_rw (config := {singlePass := true})
    [H.x.val.eq_take_concat (H.x.val.length - 1) (by as_aux_lemma => have := H.hlvl; omega)] at hx
  replace hx := subtree_compatible _ (Tree.take _ H.x) (by as_aux_lemma => synthIsPosition) hx
  change _ = stratMap' (H.dropLast h).R ⟨(H.dropLast h).x.val, _⟩ _ at hx
  erw [stratMap'_extend] at hx; apply_fun Subtype.val at hx; exact hx
lemma x_mem_tree' h (hp : IsPosition H.x.val Player.zero) :
  H.preLift.x = ((H.dropLast h).extension (by as_aux_lemma => synthIsPosition)).valT' := by
  ext1
  conv => simp [ExtensionsAt.val']
  rw [← H.x_mem_tree h hp, ← List.eq_take_concat]; omega

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

lemma losable_or_winnable :
  H.preLift.Losable ∨ H.preLift.Winnable := by
  let ⟨n, hn⟩ := le_iff_exists_add.mp H.hlvl_le
  induction n generalizing H with
  | zero =>
    -- TODO: explain why this stronger disjunction helps the following `tauto`.
    suffices H.preLift.Losable ∨ H.preLift.Winnable ∨ H.preLift.Won by
      have (h : H.preLift.Won) : H.preLift.Winnable := (PreLift.WLift.mk _ h).winnable; tauto
    have := Lift.con_of_short (hyp := hyp); tauto
  | succ n ih =>
    let hlong' : 2 * k + 2 ≤ H.x.val.length := by synthIsPosition
    let Ht := H.dropLast hlong'
    rcases ih Ht (by dsimp [Ht]; synthIsPosition) with ih | ih
    · have : ¬ H.preLift.Winnable → ¬ Ht.preLift.Winnable := by
        intro hw h; apply hw; exact h.winnable_of_le (by simp [Ht, dropLast])
      have : ¬ H.preLift.Won → ¬ Ht.preLift.Won := by
        intro hw h; apply hw; exact h.won_of_le (by simp [Ht, dropLast])
      suffices H.preLift.Losable ∨ H.preLift.Winnable ∨ H.preLift.Won by
        have (h : H.preLift.Won) : H.preLift.Winnable := (PreLift.WLift.mk _ h).winnable; tauto
      suffices ¬ Ht.preLift.Winnable → ¬ Ht.preLift.Won → ¬ H.preLift.Winnable
        → H.preLift.Losable' → H.preLift.Losable by tauto
      intro hnW hnW' hnW'' h; use h
      by_cases IsPosition H.x.val Player.one
      · let HL := PreLift.LLift.mk _ h
        by_cases hc : HL.toLift.Con
        · exact hc
        · have hlif : (PreLift.LLift.mk _ ih.1).toLift =
            HL.toLift.take (2 * k + 1 + n) (by as_aux_lemma => omega) := by
            ext1
            · simp [HL, Ht, dropLast, hn]
            · dsimp [HL, PreLift.LLift.S]
              have hG : Ht.preLift.game = H.preLift.game := by simp [Ht, dropLast]
              exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _
          have ⟨hcs, hcl⟩ :=
            (Lift.con_short_long _ (by simp_rw [Ht]; synthIsPosition)).mp ih.lift'.con
          conv at hcs => simp [hlif, List.drop_take]
          conv at hcl => simp [hlif, List.drop_take]
          conv at hc => simp [HL.toLift.con_short_long (by dsimp [HL]; synthIsPosition), hcs]
          have hnat1 : 2 * k + 1 + n - (2 * k + 2) = n - 1 := by omega
          rw [hnat1] at hcl
          have hnat3 : n - 1 + 1 = n := by synthIsPosition
          have hnat2 : 2 * k + 1 + n = 2 * k + 2 + (n - 1) := by omega
          have hlist : HL.toLift.liftShort.val[2 * k + 1].1
            :: ((H.x.val.drop (2 * k + 2)).take (n - 1)
            ++ [H.x.val[2 * k + 1 + n]]) = H.x.val.drop (2 * k + 1) := by
            simp_rw [hnat2]; nth_rw 2 [List.getElem_drop']
            rw [List.take_concat_get', (H.x.val.drop _).take_of_length_le (by synthIsPosition)]
            simp [hcs, HL]
          have hcm := HL.concat_mem_tree (a := H.x.val[2 * k + 1 + n]) (by
            unfold HL; synthIsPosition) (by
            simpa [hlist, HL] using subtree_sub _ H.x.prop) hcl (by
              intro h; apply hnW''; use n + 1
              simp_rw [WinningPosition] at h
              convert h using 2
              · simp [hlist, hn, HL]
              · synthIsPosition)
          conv at hcm => simp [hnat2, HL]
          rw [List.getElem_drop', List.take_concat_get', List.take_of_length_le
            (by synthIsPosition)] at hcm
          cases hc hcm
      · convert (ih.lift'.extensionLift' (by simp_rw [Ht]; synthIsPosition)
          ((strategyEquivSystem Ht.R).str Ht.preLift.x.val.length) (by rfl)).con
        ext1
        · ext1
          · have hm := H.x_mem_tree' hlong' (by as_aux_lemma => synthIsPosition)
            conv at hm => simp [Ht, extension, PreLift.extension_losable (h := ih),
              PreLift.Losable.lift']
            generalize_proofs _ _ hL hp at hm
            exact hm
          · rfl
        · change (defensiveQuasi H.preLift.game Player.one (hyp.pruned.sub _)).1.subtree = _
          have hG : H.preLift.game = Ht.preLift.game := by simp [Ht, dropLast]
          exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _
    · exact Or.inr (ih.winnable_of_le (by simp [Ht, dropLast]))

lemma x_mem_tree_short' (h : n < 2 * k) (hp : IsPosition (H.x.val.take n) Player.one) :
  Tree.take (n + 1) (pInv (treeHom hyp)
    (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x)) H.pInv_fixing_short) =
  (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
    (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp)).valT' := by
  have hx := (Tree.take (n + 1) H.x).prop; have := H.hlvl
  rw [take_coe, ← List.take_concat_get' _ _ (by as_aux_lemma => omega)] at hx
  replace hx := subtree_compatible _ (Tree.take n H.x) hp hx
  simp only [Set.mem_singleton_iff] at hx
  rw [stratMap'_short _ _ _ (by
    simp only [subtreeIncl_coe, take_coe, List.length_take, min_le_iff, h.le, true_or])] at hx
  have hvalT := congrArg (fun e ↦ e.valT') hx
  apply Fixing.inj (f := treeHom hyp) (ht := by
    apply Fixing.mon (f := treeHom hyp) (k := 2 * k) inferInstance
    have hlen := h_length_pInv (f := treeHom hyp)
      (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x)) H.pInv_fixing_short
    have htakeLen :
        (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x)).val.length ≤ 2 * k := by
      simp [take_coe]
    have hpInvLen :
        (pInv (treeHom hyp) (Tree.take (2 * k) ((stratMap' H.R).pre.subtreeIncl H.x))
      H.pInv_fixing_short).val.length ≤ 2 * k := hlen.trans_le htakeLen
    rw [take_coe]
    simpa only [List.length_take] using min_le_iff.mpr (Or.inr hpInvLen))
  erw [take_apply (treeHom hyp)]
  rw [cancel_pInv_right]
  refine Eq.trans ?_ (hvalT.trans ?_)
  · ext1
    conv => simp [subtreeIncl_coe, take_coe, ExtensionsAt.valT', ExtensionsAt.val']
    rw [min_eq_left (by omega)]
    rfl
  · exact ExtensionsAt.map_valT' (f := treeHom hyp)
      (x := pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h.le))
      (y := (stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
      (h := by simp_rw [cancel_pInv_right])
      (a := H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp))
lemma x_mem_tree_short (h : n < 2 * k) (hp : IsPosition (H.x.val.take n) Player.one) :
  (pInvTreeHomMap hyp (H.x.val.take (2 * k)))[n]'(by simpa) =
  (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
    (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp)).val := by
  have hget := congr_arg (fun x ↦ x.val[n]?) (H.x_mem_tree_short' h hp)
  conv at hget => simp
  apply Option.some_injective
  have hHlvl := H.hlvl
  have hnbase :
      n = (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h.le)).val.length := by
    have hlen := h_length_pInv (f := treeHom hyp)
      ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)) (H.pInv_fixing h.le)
    calc
      n = ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x)).val.length := by
        simp [subtreeIncl_coe, take_coe, List.length_take]
        omega
      _ = (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
          (H.pInv_fixing h.le)).val.length := hlen.symm
  have hmapLen : (pInvTreeHomMap hyp (H.x.val.take (2 * k))).length = 2 * k := by
    rw [pInvTreeHomMap_len]
    simp [List.length_take, H.hlvl']
  rw [List.getElem?_eq_getElem (by
    exact Nat.lt_of_lt_of_eq h hmapLen.symm)] at hget
  have hrhs :
      (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp)).val'[n]? =
      some (H.R (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
        (H.pInv_fixing h.le)) (H.pInv_isPosition h.le hp)).val := by
    rw [List.getElem?_eq_getElem (by
      rw [ExtensionsAt.val'_length]
      exact hnbase ▸ Nat.lt_succ_self _)]
    exact congrArg some (ExtensionsAt.val'_get_last_of_eq _ hnbase)
  exact hget.trans hrhs

lemma get_eq_get_take (hn : n < H.x.val.length) (hk : 2 * k ≤ n) : H.x.val[n] =
  (H.take (n + 1) (by as_aux_lemma => omega)).x.val[
    (H.take (n + 1) (by as_aux_lemma => omega)).x.val.length - 1]'
    (by as_aux_lemma => simp; omega) := by simp; congr; omega
lemma wLift_mem_tree (h : H.preLift.Won) : h.lift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using h.lift'.lift.prop)
  have := H.hlvl; intro n hnLift _ hp _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · change _ = H.R (Tree.take n h.lift'.lift) _; ext1
    have hl := H.x.prop.2 (y := H.x.val.take n)
      (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
      (by simpa using List.take_prefix _ _) (by as_aux_lemma => synthIsPosition)
    conv => lhs; simp (config := {singlePass := true}) only [List.getElem_take' _ hn',
      Lift.liftVal_take_short]
    conv => simp [Lift.liftVeryShort]
    have hnShort : n < 2 * k := by synthIsPosition
    have hpShort : IsPosition (H.x.val.take n) Player.one := by as_aux_lemma => synthIsPosition
    have hxShort := H.x_mem_tree_short hnShort hpShort
    have hmapLen : (pInvTreeHomMap hyp (H.x.val.take (2 * k))).length = 2 * k := by
      rw [pInvTreeHomMap_len]
      simp [List.length_take, H.hlvl']
    trans (pInvTreeHomMap hyp (H.x.val.take (2 * k)))[n]'(by
      exact Nat.lt_of_lt_of_eq hnShort hmapLen.symm)
    · exact List.getElem_append_left (by
        exact Nat.lt_of_lt_of_eq hnShort hmapLen.symm)
    · convert hxShort using 1
      apply Strategy.eval_val_congr
      · rfl
      · apply Fixing.inj (f := π) (ht := by
          apply Fixing.mon (f := π) (k := 2 * k) inferInstance
          change (List.take n h.lift'.liftVal).length ≤ 2 * k
          exact (List.length_take_le n h.lift'.liftVal).trans hnShort.le)
        ext1
        change List.map Prod.fst (List.take n h.lift'.liftVal) =
          ((treeHom hyp) (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
            (H.pInv_fixing hnShort.le))).val
        rw [cancel_pInv_right]
        change List.map Prod.fst (List.take n h.lift'.liftVal) = List.take n H.x.val
        rw [List.map_take, h.lift'.liftVal_lift]
        simp [PreLift.Won.lift'_toLift]
  rcases hn'.eq_or_lt with rfl | hn'
  · conv => simp
    apply Subtype.ext
    conv => lhs; simp [Lift.liftVal]
    split_ifs
    · synthIsPosition
    · rw [List.getElem_append_left (by synthIsPosition)]
      conv => simp [Lift.liftShort, strategyEquivSystem]
      erw [ExtensionsAt.val'_get_last_of_eq _ (by simp)]
      exact Strategy.eval_val_congr H.R H.R rfl _ _ (by ext1; simp) (by simp [IsPosition])
  · apply extensionsAt_ext_fst (x := Tree.take n h.lift'.lift) _ _
      (by as_aux_lemma => synthIsPosition)
    by_cases hW : (H.take n (by as_aux_lemma => omega)).preLift.Won
    · rw [h.lift'.liftVal_lift_get (by as_aux_lemma => synthIsPosition)]; conv => simp
      rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
        x_mem_tree _ (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition)]
      dsimp [extension, PreLift.extension]; split
      · conv => simp [Lift'.extensionMap, Lift'.extension, strategyEquivSystem]
        congr! 1
        apply Strategy.eval_val_congr
        · rfl
        · ext1
          simp only [dropLast, take_coe, take_trans, preLift_take, Lift'.lift_coe, subtreeIncl_coe]
          rw [← Lift.liftVal_take _ _ (by as_aux_lemma => omega)]
          congr 1; ext1
          · conv => simp
            congr
            synthIsPosition
          · apply PreLift.WLift.toLift_mono; simp
      · rename_i _ hif
        cases hif (by as_aux_lemma =>
          conv at hW => simp [dropLast]
          conv => simp [dropLast]
          convert hW
          synthIsPosition)
    · let H' := PreLift.WLift.mk _ h; have hux := H'.u_spec'
      have hshortLen : H'.toLift.liftShort.val.length = 2 * k + 2 := Lift.liftShort_length H'.toLift
      have hul : H'.u.val.length > n - (2 * k + 1) := by
        conv at hW => simp [PreLift.Won]
        by_contra
        cases hW H'.u (by simp)
          (List.prefix_of_prefix_length_le hux ((List.take_prefix _ _).drop _)
          (by have := hux.length_le; synthIsPosition))
      change _ = (H.R ⟨h.lift'.liftVal.take n, _⟩ _).val.1
      generalize_proofs _ _ pf2
      have hR := mem_getTree (H.R ⟨h.lift'.liftVal.take n, pf2⟩ (by
        synthIsPosition)).valT'
      conv at hR => simp
      rw [ExtensionsAt.val'_take_of_le _ (by as_aux_lemma => synthIsPosition)] at hR
      conv at hR => simp (disch := omega) [List.take_take]
      erw [h.lift'.liftVal_take_short (by as_aux_lemma => synthIsPosition)] at hR
      erw [H'.getTree_liftShort] at hR
      conv at hR => simp
      rw [mem_pullSub_short (by
        rw [List.length_map]
        change (H.R ⟨List.take n H'.toLift.liftVal, pf2⟩ hp).val'.length ≤
          (List.map Prod.fst H'.toLift.liftShort.val ++ H'.u.val.tail).length
        rw [ExtensionsAt.val'_length]
        conv => simp [List.length_append, List.length_map, List.length_take]
        left
        change n < H'.toLift.liftShort.val.length + (H'.u.val.length - 1)
        have htarget : H'.toLift.liftShort.val.length + (H'.u.val.length - 1) =
            2 * k + 2 + (H'.u.val.length - 1) := by rw [hshortLen]
        exact Nat.lt_of_lt_of_eq (by omega) htarget.symm)] at hR
      replace hR := hR.1; conv at hR => simp [List.prefix_iff_eq_take]
      conv => rhs; erw [← ExtensionsAt.val'_get_last,
        ← List.getElem_map Prod.fst (h := by
          rw [List.length_map]
          change (List.take n h.lift'.liftVal).length <
            (H.R ⟨List.take n h.lift'.liftVal, pf2⟩ hp).val'.length
          rw [ExtensionsAt.val'_length]
          simp [List.length_take])]
      simp_rw (config := {singlePass := true}) [PreLift.Won.lift'_toLift, hR]
      conv => simp; erw [List.getElem_append_right (by
        rw [List.length_map]
        change H'.toLift.liftShort.val.length ≤ min n H.x.val.length
        simp only [Lift.liftShort_length, le_inf_iff]
        constructor
        · exact Nat.succ_le_of_lt hn'
        · have hnX : n < H.x.val.length := by simpa [PreLift.Won.lift'_toLift] using hnLift
          exact (Nat.succ_le_of_lt hn').trans (Nat.le_of_lt hnX))]
      conv => lhs; erw [h.lift'.liftVal_lift_get (by as_aux_lemma => synthIsPosition)]
      conv => simp
      rw [List.prefix_iff_eq_take] at hux; simp_rw (config := {singlePass := true}) [hux]
      rw [List.getElem_take, List.getElem_drop]
      congr 1
      change n = 2 * k + 1 + (min n H.x.val.length - H'.toLift.liftShort.val.length + 1)
      rw [hshortLen]
      have hnX : n < H.x.val.length := by simpa [PreLift.Won.lift'_toLift] using hnLift
      rw [min_eq_left hnX.le]
      omega

lemma lLift_mem_tree (h : H.preLift.Losable) :
  h.lift'.liftVal ∈ H.R.pre.subtree := by
  apply subtree_induction (S := ⊤) (by simpa using h.lift'.lift.prop)
  have := H.hlvl; intro n hnLift _ hp _; rcases lt_or_ge n (2 * k + 1) with hn' | hn'
  · change _ = H.R (Tree.take n h.lift'.lift) _; ext1
    have hl := H.x.prop.2 (y := H.x.val.take n)
      (a := H.x.val[n]'(by as_aux_lemma => have := H.hlvl; omega))
      (by simpa using List.take_prefix _ _) (by as_aux_lemma => synthIsPosition)
    conv => lhs; simp (config := {singlePass := true}) only [List.getElem_take' _ hn',
      Lift.liftVal_take_short]
    conv => simp [Lift.liftVeryShort]
    have hnShort : n < 2 * k := by synthIsPosition
    have hpShort : IsPosition (H.x.val.take n) Player.one := by as_aux_lemma => synthIsPosition
    have hxShort := H.x_mem_tree_short hnShort hpShort
    have hmapLen : (pInvTreeHomMap hyp (H.x.val.take (2 * k))).length = 2 * k := by
      rw [pInvTreeHomMap_len]
      simp [List.length_take, H.hlvl']
    trans (pInvTreeHomMap hyp (H.x.val.take (2 * k)))[n]'(by
      exact Nat.lt_of_lt_of_eq hnShort hmapLen.symm)
    · exact List.getElem_append_left (by
        exact Nat.lt_of_lt_of_eq hnShort hmapLen.symm)
    · convert hxShort using 1
      apply Strategy.eval_val_congr
      · rfl
      · apply Fixing.inj (f := π) (ht := by
          apply Fixing.mon (f := π) (k := 2 * k) inferInstance
          change (List.take n h.lift'.liftVal).length ≤ 2 * k
          exact (List.length_take_le n h.lift'.liftVal).trans hnShort.le)
        ext1
        change List.map Prod.fst (List.take n h.lift'.liftVal) =
          ((treeHom hyp) (pInv (treeHom hyp) ((stratMap' H.R).pre.subtreeIncl (Tree.take n H.x))
            (H.pInv_fixing hnShort.le))).val
        rw [cancel_pInv_right]
        change List.map Prod.fst (List.take n h.lift'.liftVal) = List.take n H.x.val
        rw [List.map_take, h.lift'.liftVal_lift]
        simp [PreLift.Losable.lift'_toLift]
  rcases hn'.eq_or_lt with rfl | hn'
  · conv => simp
    apply Subtype.ext
    conv => lhs; simp [Lift.liftVal]
    split_ifs
    · synthIsPosition
    · rw [List.getElem_append_left (by synthIsPosition)]
      conv => simp [Lift.liftShort, strategyEquivSystem]
      erw [ExtensionsAt.val'_get_last_of_eq _ (by simp)]
      exact Strategy.eval_val_congr H.R H.R rfl _ _ (by ext1; simp) (by simp [IsPosition])
  · apply extensionsAt_ext_fst (x := Tree.take n h.lift'.lift) _ _
      (by as_aux_lemma => synthIsPosition)
    rw [h.lift'.liftVal_lift_get (by synthIsPosition)]; conv => simp
    rw [H.get_eq_get_take _ (by as_aux_lemma => omega),
      x_mem_tree _ (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition)]
    unfold extension
    rw [PreLift.extension_losable (h := h.losable_of_le (by simp [dropLast]))]
    conv => simp [Lift'.extensionMap, Lift'.extension, strategyEquivSystem]
    congr! 1
    apply Strategy.eval_val_congr
    · rfl
    · ext1
      simp only [dropLast, take_coe, take_trans, preLift_take, Lift'.lift_coe,
        PreLift.Losable.lift'_toLift, subtreeIncl_coe]
      rw [← Lift.liftVal_take _ _ (by as_aux_lemma => omega)]
      have hnX : n < H.x.val.length := by simpa [PreLift.Losable.lift'_toLift] using hnLift
      congr 1
      ext1
      · simp_rw [PreLift.LLift.toLift_toPreLift, Lift.take_toPreLift]
        congr
        simp [take_coe, hnX]
      · have htake : min (n + 1) ((List.take (n + 1) H.x.val).length - 1) = n := by
          rw [List.length_take, min_eq_left (Nat.succ_le_of_lt hnX)]
          omega
        change
          (defensiveQuasi
            (H.preLift.take
              (min (n + 1) ((List.take (n + 1) H.x.val).length - 1))
              (by rw [htake]; omega)).game
            Player.one (hyp.pruned.sub _)).1.subtree = _
        have hG :
            (H.preLift.take (min (n + 1) ((List.take (n + 1) H.x.val).length - 1)) (by
              rw [htake]
              omega)).game = H.preLift.game := by rw [PreLift.game_take]
        exact Game.defensiveQuasi_subtree (hG := hG) (hp := rfl) _

lemma take_winnable (h : H.preLift.Winnable) n :
  (H.take (2 * k + 1 + h.num + n) (by as_aux_lemma => omega)).preLift.Winnable :=
  h.takeMin_winnable.winnable_of_le (by
    rw [PreLift.Winnable.takeMin, TreeLift.preLift_take]
    exact (PreLift.take_le_take (H := H.preLift) (hm := by omega) (hn := by omega)).mpr
      (Or.inl (by omega)))
lemma winnable_subtree (hL : H.preLift.Winnable) (hnL : ¬ ∃ h, (H.dropLast h).preLift.Won) :
  H.x.val.drop (2 * k + 1 + hL.num) ∈ hL.strat.pre.subtree := by
  apply subtree_induction (S := ⊤) (by
    refine ⟨?_, ?_⟩
    · conv => simp [PreLift.game_tree, residual_tree]
      exact subtree_sub _ H.x.prop
    · intros
      exact Set.mem_univ _)
  intro n hn _ _ _
  conv at hn => simp
  conv => simp
  have htr := (H.take (2 * k + 1 + hL.num + n + 1) (by as_aux_lemma => omega)).x_mem_tree
    (by as_aux_lemma => synthIsPosition) (by as_aux_lemma => synthIsPosition); conv at htr => simp
  simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel] at htr
  apply Subtype.ext; dsimp; rw [htr]
  simp only [dropLast, take_x, take_coe, List.length_take, take_trans, tsub_le_iff_right,
    min_le_iff, le_add_iff_nonneg_right, zero_le, true_or, min_eq_right, preLift_x_coe]
  simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel]
  have := H.take_winnable hL n
  dsimp [extension, PreLift.extension]; split_ifs with hi
  · cases hnL ⟨by synthIsPosition, by
      have hbound : n + (2 * k + 1 + hL.num) < H.x.val.length := Nat.lt_sub_iff_add_lt.mp hn
      apply hi.won_of_le
      conv => simp [dropLast, - PreLift.le_def]
      exact (PreLift.take_le_take _ _ _).mpr (Or.inl (by
        rw [hL.prefix_num _ (by simp) rfl]
        · omega
        · rfl))⟩
  · symm; unfold PreLift.Winnable.extension PreLift.Winnable.a PreLift.Winnable.x'
    apply this.prefix_strat_apply' ((List.take_prefix _ _).drop _) (by simp) rfl
    · conv => simp [List.take_drop]
      generalize_proofs pf1 pf2
      congr 2
      exact pf2.prefix_num
        ((List.take_prefix (2 * k + 1 + pf1.num + n) H.x.val).drop (2 * k + 1))
        rfl rfl
  · rename_i _ hnotWinnable _
    exact (hnotWinnable this).elim
  · rename_i _ hnotWinnable _
    exact (hnotWinnable this).elim
end TreeLift

variable {R : Strategy (gameAsTrees hyp).2 Player.one} (y : body (stratMap' R).pre.subtree)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def bodyTake (n : ℕ) : TreeLift hyp where
  R := R
  x := body.take (2 * k + 1 + n) y
  hlvl := by synthIsPosition
@[simp] lemma bodyTake_take (h : 2 * k + 1 ≤ m) :
  (bodyTake y n).take m (by omega) = bodyTake y (min (m - (2 * k + 1)) n) := by
  ext1 <;> simp; congr; omega
attribute [simp_lengths] bodyTake_x
lemma takeLift_mono : (bodyTake y m).preLift ≤ (bodyTake y n).preLift ↔ m ≤ n := by
  constructor <;> intro h
  · simpa using PreLift.length_mono h
  · ext1
    · ext1; simp [h]
    · rfl
@[simp] lemma takeLift_wonPos : (bodyTake y n).preLift.WonPos = (bodyTake y 0).preLift.WonPos := by
  rw [← (takeLift_mono y).mpr (Nat.zero_le n), PreLift.wonPos_take]
@[simp] lemma takeLift_game : (bodyTake y n).preLift.game = (bodyTake y 0).preLift.game := by
  rw [← (takeLift_mono y).mpr (Nat.zero_le n), PreLift.game_take]

lemma won_of_winnable n (h : (bodyTake y n).preLift.Winnable) :
  ∃ m, (bodyTake y m).preLift.Won := by
  by_cases h' : ∃ m, (bodyTake y m).preLift.Won
  · exact h'
  · have hb : (body.drop (2 * k + 1 + h.num) y).val ∈ body h.strat.pre.subtree := by
      apply mem_body_of_take (n + 1); intro m hm
      have := (bodyTake y (h.num + m)).winnable_subtree
        (h.winnable_of_le ((takeLift_mono y).mpr (by omega))) (by
        conv at h' => simp [TreeLift.dropLast, - TreeLift.preLift_take]
        conv => simp [TreeLift.dropLast, - TreeLift.preLift_take]
        intro _; rw [bodyTake_take _ (by synthIsPosition)]
        apply h')
      conv at this => simp [Stream'.take_drop]
      conv => simp [Stream'.take_drop]
      generalize_proofs pf1 pf2 pf3 at this
      have hsub : pf1.strat.pre.subtree = h.strat.pre.subtree := h.prefix_strat_subtree
          (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synthIsPosition)).drop _)
          (by simp) rfl
      simp_rw [add_assoc] at this ⊢; convert (hsub ▸ this) using 4
      exact (WinningPrefix.prefix_num _
        (((Stream'.take_prefix _ _ _).mpr (by as_aux_lemma => synthIsPosition)).drop _)
        (by simp) rfl).symm
    have hw := h.strat_winning hb
    conv at hw => simp [PreLift.game_tree, PreLift.game_payoff]
    obtain ⟨u, hu1, hu2⟩ := hw.2
    obtain ⟨v, rfl⟩ := hu1
    simp only [Set.mem_iUnion, Set.mem_preimage] at hu2
    obtain ⟨hv1, hv2⟩ := hu2
    use v.length
    conv => simp [PreLift.Won]
    use v, hv1
    conv =>
      simp [← Stream'.take_drop, List.prefix_iff_eq_take, Stream'.take_take,
        - Function.iterate_succ]
    rw [principalOpen_iff_restrict] at hv2; convert hv2 using 2
    conv => simp [List.take_drop]
    rw [← Stream'.drop_append_of_le_length _ _ _ (by simp)]
    generalize_proofs pf; suffices pf.num ≤ n by simp [this]
    simpa using pf.num_le_length

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def wonLift (h : (bodyTake y n).preLift.Won) : body R.pre.subtree :=
  have h' k : (bodyTake y (n + k)).preLift.Won := h.won_of_le ((takeLift_mono y).mpr (by omega))
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
      ⟨(h' k).lift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y _).wLift_mem_tree _⟩, by
        rw [List.length_take, min_eq_left]
        change k ≤ (h' k).lift'.toLift.liftVal.length
        rw [Lift.liftVal_length]
        simp [PreLift.Won.lift'_toLift, bodyTake]
        omega⟩⟩, fun k ↦
      ((Lift.liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))
        (PreLift.WLift.toLift_mono ((takeLift_mono y).mpr (Nat.le_succ _)))).take k).trans
      ((h' (k + 1)).lift'.liftVal.take_prefix_take_left (Nat.le_succ _))⟩
lemma wonLift_map (h : (bodyTake y n).preLift.Won) :
  (bodyFunctor.map π ⟨(wonLift y h).val, body_mono R.pre.subtree_sub (wonLift y h).prop⟩).val
  = y.val := by
  rw [treeHom_body]
  ext n'
  simp only [wonLift]
  let hlong : (bodyTake y (n + (n' + 1))).preLift.Won :=
    h.won_of_le ((takeLift_mono y).mpr (by omega))
  change ((List.take (n' + 1) hlong.lift'.liftVal)[n']).1 = y.val n'
  rw [List.getElem_take]
  rw [Lift'.liftVal_lift_get] <;> simp [Stream'.get]; omega
/-- Auxiliary declaration for the Borel determinacy formalization. -/
  def lostLift (h : ∀ n, (bodyTake y n).preLift.Losable) : body R.pre.subtree :=
    bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
      ⟨(h k).lift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y _).lLift_mem_tree _⟩, by
        rw [List.length_take, min_eq_left]
        change k ≤ (h k).lift'.toLift.liftVal.length
        rw [Lift.liftVal_length]
        simp [PreLift.Losable.lift'_toLift, bodyTake]⟩⟩, fun k ↦
      ((Lift.liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))
        (PreLift.LLift.toLift_mono ((takeLift_mono y).mpr (Nat.le_succ _)))).take k).trans
      ((h (k + 1)).lift'.liftVal.take_prefix_take_left (Nat.le_succ _))⟩
lemma lostLift_map (h : ∀ n, (bodyTake y n).preLift.Losable) :
  (bodyFunctor.map π ⟨(lostLift y h).val, body_mono R.pre.subtree_sub (lostLift y h).prop⟩).val
  = y.val := by
  rw [treeHom_body]
  ext n'
  simp only [lostLift]
  let hlong : (bodyTake y (n' + 1)).preLift.Losable := h (n' + 1)
  change ((List.take (n' + 1) hlong.lift'.liftVal)[n']).1 = y.val n'
  rw [List.getElem_take]
  rw [Lift'.liftVal_lift_get] <;> simp [Stream'.get]; omega

lemma body_stratMap {G : Game A} {k : ℕ} {hyp : Hyp G k}
  {R : Strategy (gameAsTrees hyp).2 Player.one} (y : body (stratMap' R).pre.subtree) :
  ∃ x : body R.pre.subtree, (bodyFunctor.map π
    ⟨x.val, body_mono R.pre.subtree_sub x.prop⟩).val = y.val := by
  classical
  exact if h : ∀ n, (bodyTake y n).preLift.Losable then ⟨lostLift y h, lostLift_map y h⟩
  else by
    obtain ⟨n, h⟩ := by simpa using h
    have : ∃ n, (bodyTake y n).preLift.Won := by
      have := (bodyTake y n).losable_or_winnable; have := won_of_winnable y n; tauto
    let ⟨n, h⟩ := this
    exact ⟨wonLift y h, wonLift_map y h⟩

end «Section1»
end GaleStewartGame.BorelDet.One
