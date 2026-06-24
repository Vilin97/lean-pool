/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.CoveringClosedGame
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.WinAsap

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.PreLift

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet.One
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section «Section1»

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext] structure PreLift where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  x : G.tree
  hlvl : 2 * k < x.val.length (α := no_index _)
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  R : ResStrategy (gameAsTrees hyp) Player.one (2 * k + 1)
namespace PreLift
variable (H : PreLift hyp)
attribute [simp] hlvl
lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by simp
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]
lemma pInv_take_length :
    (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length (α := no_index _) = 2 * k := by
  rw [pInv_treeHom_val]
  · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length = 2 * k
    rw [pInvTreeHomMap_len]
    simp
  · simp
lemma gameTree_eq :
    subAt (getTree' hyp (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val)
      [H.x.val[2 * k]'H.hlvl] =
  subAt G.tree (H.x.val.take (2 * k + 1)) := by
  rw [pInv_treeHom_val]
  · rw [getTree_pInvTreeHomMap, Game.residual_tree, subAt_append]
    congr 1
    change List.take (2 * k) H.x.val ++ [H.x.val[2 * k]] =
      List.take (2 * k + 1) H.x.val
    exact H.x.val.take_concat_get' (2 * k) H.hlvl
  · simp

/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def take (n : ℕ) (h : 2 * k < n) : PreLift hyp where
  x := Tree.take n H.x
  hlvl := by simp [h]
  R := H.R
attribute [simp_lengths] take_x
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1 <;> [ext1; skip] <;> simp [h']
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [min_comm]

@[simps] instance : LE (PreLift hyp) where
  le p q := q.take p.x.val.length p.hlvl = p
lemma length_mono {p q : PreLift hyp} (h : p ≤ q) : p.x.val.length ≤ q.x.val.length := by
  -- This is not registered as a `gcongr` lemma because of the dependent projections.
  rw [← h]; simp
instance : PartialOrder (PreLift hyp) where
  le_refl := by simp
  le_trans _ _ _ pq qr := by have := length_mono pq; rw [← qr] at pq; simpa [this] using pq
  le_antisymm _ _ pq qp := by
    ext1 <;> [ext1; skip] <;> rw [← pq]
    · simpa using length_mono qp
    · simp
lemma take_le {h} : H.take n h ≤ H := by
  dsimp [LE.le]
  ext1
  · ext1
    simp [PreLift.take]
  · rfl
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n := by
  (conv => lhs; dsimp [LE.le]); simp [PreLift.ext_iff]
end PreLift

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure Lift extends PreLift hyp where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  liftTree : tree A
  htree : ∃ S : QuasiStrategy (subAt G.tree (x.val.take (2 * k + 1))) Player.one,
    liftTree = S.1.subtree
@[simps] instance : Preorder (Lift hyp) where
  le p q := p.toPreLift ≤ q.toPreLift
  le_refl _ := le_rfl (α := PreLift hyp)
  le_trans _ _ _ := le_trans (α := PreLift hyp)
namespace Lift
variable (H : Lift hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftVeryShort : gameTree hyp where
  val := (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
    [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]
  property := by
    apply (gameTree_concat (hyp := hyp)
      (x := (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val)
      (a := ⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩)).mpr
    constructor
    · exact (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).prop
    · have hlen : (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length = 2 * k :=
        H.toPreLift.pInv_take_length
      rw [validExt_zero hlen]
      constructor
      · rw [pInv_treeHom_val]
        · rw [getTree_pInvTreeHomMap]
          change List.take (2 * k) H.x.val ++ [H.x.val[2 * k]] ∈ G.tree
          rw [H.x.val.take_concat_get' (2 * k) H.hlvl]
          exact Tree.take_mem H.x
        · simp
      · rw [H.gameTree_eq]
        exact H.htree
@[simp, simp_lengths] lemma liftVeryShort_length :
  H.liftVeryShort.val.length (α := no_index _) = 2 * k + 1 := by
  simp only [liftVeryShort]
  change List.length ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
    [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]) = 2 * k + 1
  rw [List.length_append, H.toPreLift.pInv_take_length]
  simp
@[simp] lemma liftVeryShort_val_map :
  H.liftVeryShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 1) := by
  calc
    H.liftVeryShort.val.map Prod.fst =
        (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.map Prod.fst ++
          [H.x.val[2 * k]] :=
      List.map_append ..
    _ = H.x.val.take (2 * k) ++ [H.x.val[2 * k]] := by
      congr 1
      change (treeHom hyp (pInv (treeHom hyp) (Tree.take (2 * k) H.x))).val =
        H.x.val.take (2 * k)
      rw [cancel_pInv_right]
      rfl
    _ = H.x.val.take (2 * k + 1) := by
      rw [show 2 * k + 1 = 2 * k + 1 by rfl]
      exact H.x.val.take_concat_get' (2 * k) (by have := H.hlvl; omega)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftShort : gameTree hyp := (H.R H.liftVeryShort
  (by
    change H.liftVeryShort.val.length % 2 = Player.one.toNat
    rw [H.liftVeryShort_length]
    synthIsPosition)
  (by
    change H.liftVeryShort.val.length ≤ 2 * k + 1
    rw [H.liftVeryShort_length])).valT'
@[simp, simp_lengths] lemma liftShort_length :
  H.liftShort.val.length (α := no_index _) = 2 * k + 2 := by
  have hlen := ExtensionsAt.val'_length
    (H.R H.liftVeryShort (by
      change H.liftVeryShort.val.length % 2 = Player.one.toNat
      rw [H.liftVeryShort_length]
      synthIsPosition) (by
      change H.liftVeryShort.val.length ≤ 2 * k + 1
      rw [H.liftVeryShort_length]))
  change
    (H.R H.liftVeryShort (by
      change H.liftVeryShort.val.length % 2 = Player.one.toNat
      rw [H.liftVeryShort_length]
      synthIsPosition) (by
      change H.liftVeryShort.val.length ≤ 2 * k + 1
      rw [H.liftVeryShort_length])).val'.length = 2 * k + 2
  rw [hlen]
  change H.liftVeryShort.val.length + 1 = 2 * k + 2
  rw [H.liftVeryShort_length]
@[simp] lemma liftShort_val_take :
  H.liftShort.val.take (α := no_index _) (2 * k + 1) = H.liftVeryShort :=
  ExtensionsAt.val'_take_of_eq _ H.liftVeryShort_length.symm
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftVal := if H.x.val.length = 2 * k + 1 then H.liftVeryShort.val
  else H.liftShort.val ++
  (H.x.val.drop (2 * k + 2)).zipInitsMap
    (fun a y ↦ ⟨a, subAt (getTree' hyp H.liftShort.val) y⟩)
lemma liftVal_very_short (h : H.x.val.length = 2 * k + 1) : H.liftVal = H.liftVeryShort.val := by
  unfold liftVal; split_ifs; rfl
@[simp, simp_lengths] lemma liftVal_length :
  H.liftVal.length (α := no_index _) = H.x.val.length := by
  have := H.hlvl; simp_rw [liftVal]; split_ifs <;> synthIsPosition
@[simp] lemma liftVal_take_short (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftVal.take (α := no_index _) (2 * k + 2) = H.liftShort.val := by
  unfold liftVal; split_ifs
  · omega
  · simp
@[simp] lemma liftVal_take_veryShort :
  H.liftVal.take (α := no_index _) (2 * k + 1) = H.liftVeryShort.val := by
  conv => simp [liftVal, liftShort]
  split_ifs
  · simp
  · rw [List.take_append_of_le_length (by
      change 2 * k + 1 ≤ H.liftShort.val.length
      rw [H.liftShort_length]
      omega)]
    exact H.liftShort_val_take
@[simp] lemma liftVal_take_init (h : n ≤ 2 * k) :
  H.liftVal.take (α := no_index _) n = pInvTreeHomMap hyp (H.x.val.take n) := by
  have hmin : n = min n (2 * k + 1) := by omega
  rw [hmin, ← List.take_take, liftVal_take_veryShort]
  simp only [liftVeryShort]
  calc
    List.take n ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
        [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]) =
        List.take n (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val :=
      List.take_append_of_le_length (by
        rw [H.toPreLift.pInv_take_length]
        exact h)
    _ = pInvTreeHomMap hyp (H.x.val.take (min n (2 * k + 1))) := by
      rw [pInv_treeHom_val]
      · change List.take n (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)) =
          pInvTreeHomMap hyp (H.x.val.take (min n (2 * k + 1)))
        rw [pInvTreeHomMap, List.zipInitsMap_take]
        congr 1
        rw [List.take_take]
        rw [min_eq_left h, min_eq_left (by omega : n ≤ 2 * k + 1)]
      · simp
-- for u drop (2 * k + 1)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def PreWonPos (u : List A) := LosingCondition H.liftShort.val (by simp) ∧
  (∃ (h : u ≠ []), u[0]'(by simpa [List.length_pos_iff]) = H.liftShort.val[2 * k + 1].1) ∧
  getTree' hyp H.liftShort.val =
    pullSub (subAt G.tree (H.x.val.take (2 * k + 1) ++ u)) u.tail

/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift liftTree] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift hyp where
  toPreLift := H.toPreLift.take n (by omega)
  liftTree := H.liftTree
  htree := by
    obtain ⟨S, hS⟩ := H.htree; use cast (by simp [List.take_take, h]) S
    rw [hS]; symm; apply cast_subtree (by simp [List.take_take, h]) rfl
attribute [simp_lengths] take_toPreLift
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply PreLift.take_of_length_le <;> omega; rfl
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1
  · simp
  · rfl
@[simp] lemma liftVeryShort_take h : (H.take n h).liftVeryShort = H.liftVeryShort := by
  ext1
  simp only [liftVeryShort, take_toPreLift, take_liftTree, PreLift.take_x, take_coe]
  congr 1
  · rw [pInv_treeHom_val]
    · rw [pInv_treeHom_val]
      · change pInvTreeHomMap hyp (List.take (2 * k) (List.take n H.x.val)) =
          pInvTreeHomMap hyp (List.take (2 * k) H.x.val)
        rw [List.take_take, min_eq_left (by omega : 2 * k ≤ n)]
      · change (List.take (2 * k) H.x.val).length ≤ 2 * k
        exact List.length_take_le (2 * k) H.x.val
    · change (List.take (2 * k) (List.take n H.x.val)).length ≤ 2 * k
      exact List.length_take_le (2 * k) (List.take n H.x.val)
  · simp
@[simp] lemma liftShort_take h : (H.take n h).liftShort = H.liftShort := by
  apply tree_ext
  simpa [liftShort] using congrArg Subtype.val (ResStrategy.eval_valT'_congr' H.R H.R rfl
    (H.take n h).liftVeryShort H.liftVeryShort (H.liftVeryShort_take h) _ _)
@[simp] lemma liftVal_take n h :
  (H.take n h).liftVal = H.liftVal.take n := by
  unfold Lift.liftVal; split_ifs
  · simpa
  · have : n = 2 * k + 1 := by synthIsPosition
    rw [List.take_append_of_le_length (by simp [this])]; simp [this]
  · synthIsPosition
  · conv => simp [List.take_append, List.drop_take, List.zipInitsMap_take]
    have := H.hlvl; synthIsPosition
@[simp] lemma preWonPos_take h u :
  (H.take n h).PreWonPos u ↔ H.PreWonPos u := by simp [PreWonPos, List.take_take, h]
lemma take_le {h} : H.take n h ≤ H := H.toPreLift.take_le (h := h)
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n :=
  H.toPreLift.take_le_take hm hn
lemma eq_take {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H = H'.take H.x.val.length (by simp) := by
  ext1
  · exact h.symm
  · exact ht
lemma liftVal_mono {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H.liftVal <+: H'.liftVal := by rw [eq_take h ht]; simpa using List.take_prefix _ _

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Con := H.x.val.drop (2 * k + 1) ∈
  pullSub (getTree' hyp H.liftShort.val) [H.liftShort.val[2 * k + 1].1]
lemma Con.take h (h' : H.Con) : (H.take n h).Con := by
  simpa [Lift.Con, List.drop_take] using take_mem ⟨_, h'⟩
lemma con_of_short (h : H.x.val.length = 2 * k + 1) : H.Con := by
  simpa [Con, ← h] using (getTree_ne_and_pruned _).1
lemma con_short_long (h : 2 * k + 2 ≤ H.x.val.length) : H.Con ↔
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] ∧
  H.x.val.drop (2 * k + 2) ∈ getTree' hyp H.liftShort.val := by
  simp [Con, pullSub, List.take_one_drop_eq_of_lt_length h, eq_comm]
  tauto
end Lift

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure Lift' extends Lift hyp where
  con : toLift.Con
instance : Preorder (Lift' hyp) where
  le p q := p.toLift ≤ q.toLift
  le_refl _ := le_rfl (α := Lift hyp)
  le_trans _ _ _ := le_trans (α := Lift hyp)
namespace Lift'
variable (H : Lift' hyp)
lemma conShort (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] :=
  ((H.con_short_long h).mp H.con).1
lemma conLong : H.x.val.drop (2 * k + 2) ∈ getTree' hyp H.liftShort.val := by
  simpa [add_comm, ← add_assoc] using H.con.2
@[simp] lemma liftShort_val_map (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 2) := by
  rw [H.liftShort.val.eq_take_concat (2 * k + 1) (by simp)]
  calc
    List.map Prod.fst (List.take (2 * k + 1) H.liftShort.val ++
        [H.liftShort.val[2 * k + 1]]) =
        List.map Prod.fst (List.take (2 * k + 1) H.liftShort.val) ++
          [H.liftShort.val[2 * k + 1].1] :=
      List.map_append ..
    _ = H.x.val.take (2 * k + 1) ++ [H.x.val[2 * k + 1]] := by
      congr 1
      · exact congrArg (List.map Prod.fst) H.liftShort_val_take |>.trans
          H.liftVeryShort_val_map
      · exact congrArg List.singleton (H.conShort h)
    _ = H.x.val.take (2 * k + 2) :=
      H.x.val.take_concat_get' (2 * k + 1) (by omega)
@[simp] lemma liftVal_lift : H.liftVal.map (α := no_index _) Prod.fst = H.x.val := by
  unfold Lift.liftVal
  split_ifs with hshort
  · rw [H.liftVeryShort_val_map]
    exact List.take_of_length_le (by omega)
  · have hlong : 2 * k + 2 ≤ H.x.val.length := by
      have := H.hlvl
      omega
    let tail : List (upA hyp) :=
      (H.x.val.drop (2 * k + 2)).zipInitsMap
        (fun a y ↦ ⟨a, subAt (getTree' hyp H.liftShort.val) y⟩)
    change List.map Prod.fst (H.liftShort.val ++ tail) = H.x.val
    calc
      List.map Prod.fst (H.liftShort.val ++ tail) =
          H.liftShort.val.map Prod.fst ++ tail.map Prod.fst :=
        List.map_append ..
      _ = H.liftShort.val.map Prod.fst ++ H.x.val.drop (2 * k + 2) := by
        congr 1
        change List.map Prod.fst
            ((H.x.val.drop (2 * k + 2)).zipInitsMap fun a y ↦
              (a, subAt (getTree' hyp H.liftShort.val) y)) =
          H.x.val.drop (2 * k + 2)
        rw [← List.zipInitsMap_map]
        simp
      _ = H.x.val := by
        rw [H.liftShort_val_map hlong]
        exact List.take_append_drop (2 * k + 2) H.x.val
@[simp] lemma liftVal_lift_get (h : n < H.x.val.length) :
  (H.liftVal[n]'(by simp [h])).1 = H.x.val[n]'(by simpa) := by
  have hlift : n < H.liftVal.length := by simpa [H.liftVal_length] using h
  have hget := congrArg (fun xs ↦ xs[n]?) H.liftVal_lift
  change (H.liftVal.map Prod.fst)[n]? = H.x.val[n]? at hget
  rw [List.getElem?_eq_getElem (by simpa [List.length_map] using hlift)] at hget
  rw [List.getElem?_eq_getElem h] at hget
  have hget' := Option.some.inj hget
  rw [List.getElem_map] at hget'
  exact hget'

/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift' hyp where
  toLift := H.toLift.take n (by omega)
  con := H.con.take _ _
attribute [simp_lengths] take_toLift
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply Lift.take_of_length_le <;> omega
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp

/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def lift : gameTree hyp where
  val := H.liftVal
  property := by
    let ⟨n, hn⟩ := le_iff_exists_add.mp (Nat.add_one_le_iff.mpr H.hlvl)
    induction n generalizing H with
    | zero => simp [Lift.liftVal, hn]
    | succ n ih =>
      specialize ih (H.take (2 * k + 1 + n) (by omega)); conv at ih => simp [hn]
      rcases n with _ | n
      · simp at hn; simp [Lift.liftVal, ← hn]; simp [hn]
      · rw [H.liftVal.eq_take_concat (2 * k + 1 + (n + 1)) (by synthIsPosition)]
        have hnat : 2 * k + 1 + (n + 1) = (2 * k + 2) + n := by omega
        conv => simp [- List.take_append_getElem]
        use ih; constructor
        · conv => simp [getTree_eq' _ ih, hn]
          simp_rw [hnat]
          rw [List.drop_take]
          convert take_mem (n := n + 1) ⟨_, H.conLong⟩ using 1
          · rw [List.take_take]
            rw [show min (2 * k + 2) (2 * k + 2 + n) = 2 * k + 2 by omega]
            exact congrArg (getTree' hyp) (H.liftVal_take_short (by omega))
          · have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
              simp [hn]
              omega
            rw [show H.x.val[2 * k + 2 + n] = (H.x.val.drop (2 * k + 2))[n]'hdrop by
              rw [List.getElem_drop']]
            rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
            congr 1
            rw [show 2 * k + 2 + n - (2 * k + 2) = n by omega]
            calc
              List.map Prod.fst (List.take n (List.drop (2 * k + 2) H.liftVal)) =
                  List.take n (List.map Prod.fst (List.drop (2 * k + 2) H.liftVal)) := by
                rw [List.map_take]
              _ = List.take n (List.drop (2 * k + 2) (List.map Prod.fst H.liftVal)) := by
                rw [List.map_drop]
              _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
                rw [H.liftVal_lift]
        · split_ifs
          · synthIsPosition
          · synthIsPosition
          · conv => lhs; unfold Lift.liftVal
            conv => simp [hn]
            rw [List.getElem_append_right (by synthIsPosition), getTree_eq' _ ih]
            conv => simp (disch := omega) [List.take_take, hnat]
            congr 2
            rw [List.drop_take]
            rw [show 2 * k + 2 + n - (2 * k + 2) = n by omega]
            have hdrop : n < (List.drop (2 * k + 2) H.x.val).length := by
              simp [hn]
              omega
            rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
            congr 1
            · symm
              calc
                List.map Prod.fst (List.take n (List.drop (2 * k + 2) H.liftVal)) =
                    List.take n (List.map Prod.fst (List.drop (2 * k + 2) H.liftVal)) := by
                  rw [List.map_take]
                _ = List.take n (List.drop (2 * k + 2) (List.map Prod.fst H.liftVal)) := by
                  rw [List.map_drop]
                _ = List.take n (List.drop (2 * k + 2) H.x.val) := by
                  rw [H.liftVal_lift]
            · rw [List.getElem_drop']
lemma lift_lift : treeHom hyp H.lift = H.x := tree_ext H.liftVal_lift
attribute [simp_lengths] lift_coe
end Lift'

namespace PreLift
variable (H : PreLift hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift liftTree] def extend --weird simps! error message
  (S : QuasiStrategy (subAt G.tree (H.x.val.take (2 * k + 1))) Player.one) : Lift hyp where
  toPreLift := H
  liftTree := S.1.subtree
  htree := ⟨S, rfl⟩
attribute [simp_lengths] extend_toPreLift
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def WonPos := {u | ∃ S, (H.extend S).PreWonPos u}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps -isSimp] def game : Game A where
  tree := subAt G.tree (H.x.val.take (2 * k + 1))
  payoff := Subtype.val ⁻¹' ⋃ u ∈ H.WonPos, principalOpen u
lemma game_open : IsOpen H.game.payoff := IsOpen.preimage
  continuous_subtype_val (isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ principalOpen_isOpen _)
lemma extend_take h S : (H.take n h).extend S =
  (H.extend (cast (by simp [List.take_take, h]) S)).take n h := by
  ext1
  · rfl
  · simp only [extend_liftTree, Lift.take_liftTree]
    symm
    apply cast_subtree (by simp [List.take_take, h]) rfl
@[simp] lemma wonPos_take h : (H.take n h).WonPos = H.WonPos := by
  ext; conv => simp [WonPos, extend_take]
  generalize_proofs pf; rw [(cast_bijective pf).surjective.exists]
@[simp] lemma game_take h : (H.take n h).game = H.game := by
  ext1 <;> simp [game, List.take_take, h]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Won := ∃ u ∈ H.WonPos, u <+: H.x.val.drop (2 * k + 1)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Winnable := WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Losable' := ¬ WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))
end PreLift

end «Section1»
end GaleStewartGame.BorelDet.One
