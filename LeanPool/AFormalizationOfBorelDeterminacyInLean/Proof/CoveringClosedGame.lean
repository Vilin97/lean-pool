/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Covering

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.CoveringClosedGame

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame.BorelDet
open Stream'.Discrete Descriptive Tree
open CategoryTheory
noncomputable section «Section1»

variable {A : Type*}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure Hyp (G : Game A) (k : ℕ) where
  closed : IsClosed G.payoff
  pruned : IsPruned G.tree
  nonempty : [] ∈ G.tree
variable {G : Game A} {k : ℕ} (hyp : Hyp G k)
--the second component is the residual tree of valid extensions
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def upA (hyp : Hyp G k) :=
  let _ : IsClosed G.payoff := hyp.closed
  A × tree A
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev A' {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} := upA hyp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def getTree' (hyp : Hyp G k) (x : List (upA hyp)) := match x.getLast? with
  | none => G.tree
  | some a => a.2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev getTree {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} (x : List A') :=
  getTree' hyp x
variable {hyp}
@[simp] lemma getTree_nil : getTree' hyp ([] : List (upA hyp)) = G.tree := rfl
@[simp] lemma getTree_concat x (a : upA hyp) : getTree' hyp (x ++ [a]) = a.2 := by
  simp [getTree']

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def LosingCondition (x : List (upA hyp)) (h : x.length = 2 * k + 2) :=
  body (pullSub (getTree' hyp x) (x.map Prod.fst)) ∩ G.payoff = ∅ ∧
  ∃ y : subAt (getTree' hyp (x.take (2 * k + 1))) [x[2 * k + 1].1],
    getTree' hyp x = pullSub (subAt G.tree (x.map Prod.fst ++ y)) y
lemma LosingCondition.concat {x : List (upA hyp)} {a h} :
  LosingCondition (x ++ [a]) h ↔
  body (pullSub a.2 (x.map Prod.fst ++ [a.1])) ∩ G.payoff = ∅ ∧
  ∃ y : subAt (getTree' hyp x) [a.1], a.2
  = pullSub (subAt G.tree (x.map Prod.fst ++ a.1 :: y)) y := by
  have hxlen : x.length = 2 * k + 1 := by simpa using h
  have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
  unfold LosingCondition
  simp [hxlen, hmap, Stream'.cons_append_stream, List.append_assoc]
lemma LosingCondition.of_concat {x : List (upA hyp)} {a h} (H : LosingCondition (x ++ [a]) h) :
  ∃ y : subAt (getTree' hyp x) [a.1], a.2
  = pullSub (subAt G.tree (x.map Prod.fst ++ a.1 :: y)) y := (concat.mp H).2
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def WinningCondition (x : List (upA hyp)) (h : x.length = 2 * k + 2) :=
  body (pullSub (getTree' hyp x) (x.map Prod.fst)) ⊆ G.payoff ∧
  ∃ S' : QuasiStrategy (subAt (getTree' hyp (x.take (2 * k + 1))) [x[2 * k + 1].1])
    Player.one, getTree' hyp x = S'.1.subtree
lemma cast_subtree {A} {T T' : tree A} {p p'} (hT : T = T') (hp : p = p') (S : QuasiStrategy T p) :
  (cast (by rw [hT, hp]) S : QuasiStrategy T' p').1.subtree = S.1.subtree := by subst hT hp; rfl
lemma WinningCondition.concat {x : List (upA hyp)} {a h} :
  WinningCondition (x ++ [a]) h ↔
  body (pullSub a.2 (x.map Prod.fst ++ [a.1])) ⊆ G.payoff ∧
  ∃ S' : QuasiStrategy (subAt (getTree' hyp x) [a.1]) Player.one, a.2
  = S'.1.subtree := by
  have hxlen : x.length = 2 * k + 1 := by simpa using h
  have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
  unfold WinningCondition
  conv => simp [hmap, Stream'.cons_append_stream]
  intro _
  constructor <;> (
    intro ⟨S, he⟩; use cast (by simp [hxlen]) S
    rw [cast_subtree (by simp [hxlen]) rfl]; simpa)
lemma WinningCondition.of_concat {x : List (upA hyp)} {a h} (H : WinningCondition (x ++ [a]) h) :
  ∃ S' : QuasiStrategy (subAt (getTree' hyp x) [a.1]) Player.one, a.2
  = S'.1.subtree := (concat.mp H).2

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def ValidExt (x : List (upA hyp)) (a : upA hyp) := [a.1] ∈ getTree' hyp x ∧
  if x.length = 2 * k then
    ∃ S : QuasiStrategy (subAt (getTree' hyp x) [a.1]) Player.one, a.2 = S.1.subtree
  else if h : x.length = 2 * k + 1 then
    LosingCondition (x ++ [a]) (by simpa) ∨ WinningCondition (x ++ [a]) (by simpa)
  else a.2 = subAt (getTree' hyp x) [a.1]
@[simp] lemma validExt_zero {x : List (upA hyp)} {a : upA hyp} (h : x.length = 2 * k) :
  ValidExt x a ↔ [a.1] ∈ getTree' hyp x ∧
  ∃ S : QuasiStrategy (subAt (getTree' hyp x) [a.1]) Player.one, a.2 = S.1.subtree := by
  simp [ValidExt, h]
@[simp] lemma validExt_one {x : List (upA hyp)} {a : upA hyp} (h : x.length = 2 * k + 1) :
  ValidExt x a ↔ [a.1] ∈ getTree' hyp x ∧
 (LosingCondition (x ++ [a]) (by simpa) ∨ WinningCondition (x ++ [a]) (by simpa)) := by
  simp [ValidExt, h]
@[simp] lemma validExt_short {x : List (upA hyp)} {a : upA hyp} (h : x.length < 2 * k) :
  ValidExt x a ↔ [a.1] ∈ getTree' hyp x ∧ a.2 = subAt (getTree' hyp x) [a.1] := by
  unfold ValidExt; split_ifs <;> (try omega); simp
@[simp] lemma validExt_long {x : List (upA hyp)} {a : upA hyp} (h : 2 * k + 2 ≤ x.length) :
  ValidExt x a ↔ [a.1] ∈ getTree' hyp x ∧ a.2 = subAt (getTree' hyp x) [a.1] := by
  unfold ValidExt; split_ifs <;> (try omega); simp

variable (hyp)
/-- the tree of the unraveled game of a closed game -/
def gameTree : tree (upA hyp) where
  val := {x | List.reverseRecOn x True (fun x a hx ↦ hx ∧ ValidExt x a)}
  property _ := by simp; tauto
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def oldAsTrees (hyp : Hyp G k) : Trees :=
  let _ : IsClosed G.payoff := hyp.closed
  ⟨A, G.tree⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def gameAsTrees (hyp : Hyp G k) : Trees := ⟨upA hyp, gameTree hyp⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev T {A : Type*} {G : Game A} : tree A := G.tree
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev T' {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} : tree (upA hyp) := gameTree hyp
variable {hyp}
lemma gameTree_ne : [] ∈ gameTree hyp := by simp [gameTree]
@[simp] lemma gameTree_concat (x : List (upA hyp)) (a : upA hyp) :
  x ++ [a] ∈ gameTree hyp ↔ x ∈ gameTree hyp ∧ ValidExt x a := by simp [gameTree]
lemma getTree_sub (x : gameTree hyp) :
  getTree' hyp x.val ≤ subAt G.tree (x.val.map Prod.fst) := by
  have ⟨x, h⟩ := x
  induction x using List.reverseRecOn with
  | nil =>
    intro y hy
    exact hy
  | append_singleton x a ih =>
    conv at h => simp
    conv => simp
    have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
    obtain ⟨h, ⟨_, h2⟩⟩ := h; split_ifs at h2
    · obtain ⟨S, h2⟩ := h2; rw [hmap, h2, ← subAt_append]
      apply le_trans S.1.subtree_sub
      gcongr; exact ih h
    · rcases h2 with h2 | h2
      · obtain ⟨y, h2⟩ := h2.of_concat; rw [hmap, h2, List.append_cons, ← subAt_append]
        apply pullSub_subAt
      · obtain ⟨S', h2⟩ := h2.of_concat; rw [hmap, h2, ← subAt_append]
        apply le_trans S'.1.subtree_sub
        gcongr; exact ih h
    · rw [hmap, h2, ← subAt_append]; gcongr; exact ih h
lemma getTree_ne_and_pruned (x : gameTree hyp) :
  [] ∈ getTree' hyp x.val ∧ IsPruned (getTree' hyp x.val) := by
  have ⟨x, h⟩ := x
  induction x using List.reverseRecOn with
  | nil => exact ⟨hyp.nonempty, hyp.pruned⟩
  | append_singleton x a ih =>
    conv at h => simp
    conv => simp
    obtain ⟨h, ⟨h1, h2⟩⟩ := h; split_ifs at h2
    · obtain ⟨S, h2⟩ := h2; simpa [h2, h1] using S.subtree_isPruned ((ih h).2.sub _)
    · rcases h2 with h2 | h2
      · obtain ⟨⟨y, hy⟩, h2⟩ := h2.of_concat
        simpa [h2] using ⟨getTree_sub ⟨x, h⟩ hy, (hyp.pruned.sub _).pullSub y⟩
      · obtain ⟨S', h2⟩ := h2.of_concat; simpa [h2, h1] using S'.subtree_isPruned ((ih h).2.sub _)
    · simp [h2, h1, IsPruned.sub, ih h]

section «Section2»
variable {x : gameTree hyp} {h : x.val.length = 2 * k + 2}
namespace LosingCondition
variable (H : LosingCondition x.val h)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def y : getTree' hyp x.val where
  val := H.2.choose.val
  property := by
    obtain ⟨x, hx⟩ := x
    rcases x.eq_nil_or_concat' with rfl | ⟨xs, a, rfl⟩
    · simp at h
    · conv at h => simp
      conv => lhs; rw [H.2.choose_spec]
      rw [mem_pullSub_self]
      have hmap : List.map Prod.fst (xs ++ [a]) = xs.map Prod.fst ++ [a.1] := List.map_append ..
      have hy : a.1 :: H.2.choose.val ∈ getTree' hyp xs := by simpa [h] using H.2.choose.prop
      simpa [subAt, hmap, List.append_assoc] using getTree_sub ⟨xs, mem_of_append hx⟩ hy
lemma y_spec : getTree' hyp x.val
  = pullSub (subAt G.tree (x.val.map Prod.fst ++ H.y.val)) H.y.val := H.2.choose_spec
end LosingCondition
namespace WinningCondition
variable (H : WinningCondition x.val h)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def S : QuasiStrategy (subAt (getTree' hyp (x.val.take (2 * k + 1)))
  [x.val[2 * k + 1].1]) Player.one := H.2.choose
lemma S_spec : getTree' hyp x.val = H.S.1.subtree := H.2.choose_spec
end WinningCondition

variable (x h) in
lemma lose_or_win : LosingCondition x.val h ∨ WinningCondition x.val h := by
  let ⟨x, hx⟩ := x; rcases x.eq_nil_or_concat' with rfl | ⟨_, _, rfl⟩ <;> simp at h
  simp [gameTree, h] at hx; tauto
@[simp] lemma not_winning : ¬ WinningCondition x.val h ↔ LosingCondition x.val h := by
  constructor
  · have := lose_or_win x h; tauto
  · intro ⟨H, _⟩ ⟨H', _⟩
    rw [← Set.inter_eq_left, H, Eq.comm, ← Set.not_nonempty_iff_eq_empty,
      IsPruned.body_ne_iff_ne] at H'
    · apply H'; simp only [pullSub_ne]; exact (getTree_ne_and_pruned x).1
    · apply IsPruned.pullSub; exact (getTree_ne_and_pruned x).2
@[simp] lemma not_losing : ¬ LosingCondition x.val h ↔ WinningCondition x.val h := by
  rw [← not_iff_not, not_not, not_winning]
end «Section2»

variable (hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def treeHom : gameAsTrees hyp ⟶ oldAsTrees hyp where
  toFun x := ⟨x.val.map Prod.fst, by
    have h : [] ∈ subAt _ _ := getTree_sub x (getTree_ne_and_pruned x).1
    change x.val.map Prod.fst ∈ G.tree
    simpa [subAt] using h⟩
  monotone' _ _ h := h.map Prod.fst
  h_length := fun x ↦ by
    exact List.length_map (f := Prod.fst) (as := x.val)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev π {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} :
    gameAsTrees hyp ⟶ oldAsTrees hyp :=
  treeHom hyp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def pInvTreeHomMap (hyp : Hyp G k) (x : List A) : List (upA hyp) :=
  x.zipInitsMap (fun a y ↦ (a, (G.residual y).tree))
variable {hyp}
lemma treeHom_val x : (treeHom hyp x).val = x.val.map Prod.fst := by
  change (⟨x.val.map Prod.fst, _⟩ : G.tree).val = x.val.map Prod.fst
  rfl
lemma treeHom_body (x : body (gameTree hyp)) :
  ((bodyFunctor.map (treeHom hyp)) x).val = x.val.map Prod.fst := by
  ext n
  rw [bodyMap_spec_res']
  change (List.map Prod.fst (Stream'.take (n + 1) (x : Stream' (upA hyp))))[n] =
    (Stream'.map Prod.fst (x : Stream' (upA hyp))).get n
  simp
lemma T'_snd_small' (x : gameTree hyp) (h : x.val.length ≤ 2 * k) :
  getTree' hyp x.val = subAt G.tree (x.val.map Prod.fst) := by
  have ⟨x, hx⟩ := x
  induction x using List.reverseRecOn with
  | nil => ext y; rfl
  | append_singleton x a ih =>
    conv at h => simp
    conv at hx => simp
    conv => simp
    rw [validExt_short h] at hx
    have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
    rw [hmap, hx.2.2, ih hx.1 h.le, subAt_append]
lemma T'_snd_small {x a} (h : x ++ [a] ∈ gameTree hyp) (h' : x.length < 2 * k) :
  a.2 = (G.residual (x.map Prod.fst ++ [a.1])).tree := by
  have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
  simpa [Game.residual_tree, hmap] using T'_snd_small' ⟨_, h⟩ (by simpa using h')
@[simp] lemma pInvTreeHomMap_nil : pInvTreeHomMap hyp [] = [] := by simp [pInvTreeHomMap]
@[simp] lemma pInvTreeHomMap_concat (x : List A) (a : A) :
  pInvTreeHomMap hyp (x ++ [a])
  = pInvTreeHomMap hyp x ++ [⟨a, (G.residual (x ++ [a])).tree⟩] := by simp [pInvTreeHomMap]
@[simp, simp_lengths] lemma pInvTreeHomMap_len (x : List A) :
  (pInvTreeHomMap hyp x).length = x.length := by simp [pInvTreeHomMap]
@[simp] lemma getTree_pInvTreeHomMap (x : List A) :
  getTree' hyp (pInvTreeHomMap hyp x) = (G.residual x).tree := by
  rcases x.eq_nil_or_concat with rfl | ⟨_, _, rfl⟩ <;> simp
variable (hyp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def pInvTreeHom : (Tree.res (2 * k)).obj ⟨_, G.tree⟩ ⟶
    (Tree.res (2 * k)).obj ⟨_, gameTree hyp⟩ where
  toFun x := ⟨pInvTreeHomMap hyp x.val, by
    have ⟨x, h⟩ := x
    induction x using List.reverseRecOn with
    | nil =>
      change pInvTreeHomMap hyp ([] : List A) ∈ ↑((res (2 * k)).obj ⟨upA hyp, gameTree hyp⟩).snd
      rw [pInvTreeHomMap_nil]
      exact ⟨gameTree_ne, by simp⟩
    | append_singleton x a ih =>
      specialize ih (mem_of_append h)
      simp only at ih ⊢
      have hxlt : x.length < 2 * k := by
        have hxle : (x ++ [a]).length ≤ 2 * k := h.2
        simp only [List.length_append, List.length_cons, List.length_nil] at hxle; omega
      constructor
      · have hconcat := pInvTreeHomMap_concat (hyp := hyp) (x := x) (a := a)
        have hvalid : ValidExt (pInvTreeHomMap hyp x) ⟨a, (G.residual (x ++ [a])).tree⟩ := by
          have hplen : (pInvTreeHomMap hyp x).length < 2 * k := by
            rwa [pInvTreeHomMap_len]
          rw [validExt_short hplen]
          constructor
          · rw [getTree_pInvTreeHomMap, Game.residual_tree]
            change x ++ [a] ∈ G.tree
            exact h.1
          · simp [getTree_pInvTreeHomMap, Game.residual_tree, subAt_append]
            rfl
        have hmem : pInvTreeHomMap hyp x ++ [⟨a, (G.residual (x ++ [a])).tree⟩] ∈
            gameTree hyp :=
          (gameTree_concat (pInvTreeHomMap hyp x)
            ⟨a, (G.residual (x ++ [a])).tree⟩).mpr ⟨ih.1, hvalid⟩
        exact hconcat.symm ▸ hmem
      · have hlen := h.2
        simpa [pInvTreeHomMap_len] using hlen⟩
  monotone' x y h := h.zipInitsMap _ _ _
  h_length := fun x ↦ pInvTreeHomMap_len (hyp := hyp) x.val
@[simp] lemma pInvTreeHom_val (x : (Tree.res (2 * k)).obj ⟨_, G.tree⟩) :
  (pInvTreeHom hyp x).val = pInvTreeHomMap hyp x.val := rfl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def treeHomRes : (Tree.res (2 * k)).obj ⟨_, gameTree hyp⟩ ≅
    (Tree.res (2 * k)).obj ⟨_, G.tree⟩ where
  hom := (Tree.res (2 * k)).map (treeHom hyp)
  inv := pInvTreeHom hyp
  hom_inv_id := by
    apply LenHom.ext
    funext x
    apply Subtype.ext
    rcases x with ⟨x, h⟩
    change pInvTreeHomMap hyp (List.map Prod.fst x) = x
    induction x using List.reverseRecOn with
    | nil => rfl
    | append_singleton x a ih =>
      have hx : x ++ [a] ∈ gameTree hyp := h.1
      have hxprev : x ∈ gameTree hyp := mem_of_append hx
      have hsmall : x.length < 2 * k := by
        have hxle : (x ++ [a]).length ≤ 2 * k := h.2
        simp only [List.length_append, List.length_cons, List.length_nil] at hxle; omega
      have hmap : List.map Prod.fst (x ++ [a]) = List.map Prod.fst x ++ [a.1] := List.map_append ..
      rw [hmap, pInvTreeHomMap_concat, ih ⟨hxprev, hsmall.le⟩]
      cases a
      congr
      exact (T'_snd_small hx hsmall).symm
  inv_hom_id := by
    apply LenHom.ext
    funext x
    apply Subtype.ext
    rcases x with ⟨x, h⟩
    change List.map Prod.fst (pInvTreeHomMap hyp x) = x
    change List.map Prod.fst (x.zipInitsMap fun a y ↦ (a, subAt G.tree y)) = x
    rw [← List.zipInitsMap_map]
    simp
instance treeHom_fixing : Tree.Fixing (2 * k) (treeHom hyp) := ⟨Iso.isIso_hom (treeHomRes hyp)⟩
@[simp] lemma pInv_treeHom_val x (h : x.val.length ≤ 2 * k) :
  (pInv (treeHom hyp) x).val = pInvTreeHomMap hyp x.val := by
  change _ = (res.val' (pInvTreeHom hyp ⟨x.val, ⟨x.prop, h⟩⟩)).val
  congr 1
  have hf : Fixing (pInv (treeHom hyp) x).val.length (treeHom hyp) := by
    rw [h_length_pInv]
    exact (treeHom_fixing hyp).mon h
  apply Fixing.inj (treeHom hyp) _ _ hf
  rw [cancel_pInv_right]
  ext1
  change x.val = List.map Prod.fst (pInvTreeHomMap hyp x.val)
  rw [pInvTreeHomMap]
  have hmap : ∀ xs : List A,
      xs = List.map Prod.fst (xs.zipInitsMap fun a y => (a, (G.residual y).tree)) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => rfl
    | append_singleton xs a ih =>
      rw [List.zipInitsMap_concat, List.map_append, ← ih]
      rfl
  exact hmap x.val

variable {hyp}
lemma gameTree_isPruned : IsPruned <| gameTree hyp := by
  intro ⟨x, hx⟩; obtain ⟨hne, hPr⟩ := (getTree_ne_and_pruned ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := hPr ⟨[], hne⟩; dsimp at ha
  by_cases hlen : x.length = 2 * k + 1
  · simp only [ExtensionsAt, upA, nonempty_subtype, Prod.exists]
    use a
    by_cases h : ∃ y : body (subAt (getTree' hyp x) [a]),
      x.map Prod.fst ++ [a] ++ₛ y.val ∉ Subtype.val '' G.payoff
    · have ⟨y, hy⟩ := h
      rw [← (Game.isClosed_image_payoff.mp hyp.closed).closure_eq,
        mem_closure_iff_nhds_basis (hasBasis_principalOpen' (2 * k + 1 + 1) _)] at hy
      conv at hy => simp
      obtain ⟨n, hn, hy⟩ := hy; obtain ⟨n, rfl⟩ := le_iff_exists_add.mp (Nat.add_one_le_iff.mpr hn)
      let u : subAt (getTree' hyp x) [a] := body.take n y
      let b : tree A := pullSub (subAt G.tree (x.map Prod.fst ++ a :: u.val)) u.val
      refine ⟨b, ?_⟩
      change x ++ ([⟨a, b⟩] : List (upA hyp)) ∈ gameTree hyp
      rw [gameTree_concat, validExt_one hlen]
      refine ⟨hx, ha, Or.inl ?_⟩
      rw [LosingCondition.concat]
      constructor
      · change body (pullSub b (x.map Prod.fst ++ [a])) ∩ G.payoff = ∅
        dsimp [b]
        simp_rw [pullSub_body, Set.image_image, ← Set.subset_empty_iff]
        rintro x ⟨⟨z, _, rfl⟩, ⟨⟨x', hx'⟩, hxp, rfl⟩⟩; apply hy _ hx' hxp; use z
        have ht :
            Stream'.take ((x.map Prod.fst).length + (1 + n))
                (x.map Prod.fst ++ₛ Stream'.cons a y.val) = x.map Prod.fst ++ [a] ++ u.val := by
          rw [← Stream'.append_take (x := x.map Prod.fst) (a := Stream'.cons a y.val)
            (n := 1 + n)]
          rw [show 1 + n = n + 1 by omega, Stream'.take_succ_cons]
          simp [u]
        rw [← hlen, ← x.length_map Prod.fst, Nat.add_assoc]
        change Stream'.take ((x.map Prod.fst).length + (1 + n))
            (x.map Prod.fst ++ₛ Stream'.cons a y.val) ++ₛ z =
          x.map Prod.fst ++ [a] ++ₛ (u.val ++ₛ z)
        rw [ht]
        simp [← Stream'.append_append_stream, List.append_assoc]
      · exact ⟨u, rfl⟩
    · let S : QuasiStrategy (subAt (getTree' hyp x) [a]) Player.one :=
        ⟨⊤, PreStrategy.top_isQuasi (hPr.sub _)⟩
      let b : tree A := S.1.subtree
      refine ⟨b, ?_⟩
      change x ++ ([⟨a, b⟩] : List (upA hyp)) ∈ gameTree hyp
      rw [gameTree_concat, validExt_one hlen]
      refine ⟨hx, ha, Or.inr ?_⟩
      rw [WinningCondition.concat]
      constructor
      · simpa [Set.subset_def, S, b] using h
      · exact ⟨S, rfl⟩
  · use (a, subAt (getTree' hyp x) [a])
    by_cases hlen' : x.length = 2 * k
    · conv => simp [hx, ValidExt, hlen', ha]
      use ⟨⊤, PreStrategy.top_isQuasi (hPr.sub _)⟩, PreStrategy.top_subtree.symm
    · simpa [hx, ValidExt, hlen, hlen']

variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def game : Game (upA hyp) where
  tree := gameTree hyp
  payoff := (bodyFunctor.map (treeHom hyp))⁻¹' G.payoff
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev G' {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} : Game (upA hyp) := game hyp
lemma getTree_eq' (x : List (upA hyp)) (h : x ∈ gameTree hyp) : getTree' hyp x
  = subAt (getTree' hyp (x.take (2 * k + 2))) ((x.drop (2 * k + 2)).map Prod.fst) := by
  rcases le_or_gt x.length (2 * k + 2) with h | h
  · ext y
    simp_rw [List.take_of_length_le h, List.drop_eq_nil_iff.mpr h, subAt]
    change y ∈ getTree' hyp x ↔ y ∈ getTree' hyp x
    rfl
  · have hex : ∃ y z, x = y ++ z ∧ y.length = 2 * k + 2 :=
      ⟨x.take (2 * k + 2), x.drop (2 * k + 2), by simpa using h.le⟩
    obtain ⟨x, y, rfl, hxl⟩ := hex; clear h
    induction y using List.reverseRecOn with
    | nil =>
      ext z
      conv => simp [← hxl, subAt]
      change z ∈ getTree' hyp x ↔ z ∈ getTree' hyp x
      rfl
    | append_singleton y a ih =>
      specialize ih (mem_of_append (by simpa))
      conv at ih => simp [hxl]
      have hvalid : ValidExt (x ++ y) a :=
        ((gameTree_concat (hyp := hyp) (x ++ y) a).mp
          (by simpa [List.append_assoc] using h)).2
      rw [validExt_long (by simp [hxl])] at hvalid
      conv => simp [hxl]
      have hmap : List.map Prod.fst (y ++ [a]) = List.map Prod.fst y ++ [a.1] := List.map_append ..
      rw [← List.append_assoc, getTree_concat, hvalid.2, ih,
        hmap, ← subAt_append]
lemma getTree_eq (x : gameTree hyp) : getTree' hyp x.val
  = subAt (getTree' hyp (x.val.take (2 * k + 2))) ((x.val.drop (2 * k + 2)).map Prod.fst) :=
  getTree_eq' x.val x.prop
lemma mem_getTree (x : gameTree hyp) : x.val.map Prod.fst ∈
  pullSub (getTree' hyp (x.val.take (2 * k + 2))) ((x.val.take (2 * k + 2)).map Prod.fst) := by
  have h := by simpa [getTree_eq] using (getTree_ne_and_pruned x).1
  constructor
  · have ht : List.take (List.map Prod.fst (List.take (2 * k + 2) x.val)).length
          (List.map Prod.fst x.val)
        = List.map Prod.fst (List.take (2 * k + 2) x.val) := by
      rw [List.length_map]
      simp [List.map_take]
    exact ht.symm ▸ (List.prefix_refl (List.map Prod.fst (List.take (2 * k + 2) x.val)))
  · have hd : List.drop (List.map Prod.fst (List.take (2 * k + 2) x.val)).length
          (List.map Prod.fst x.val)
        = List.map Prod.fst (List.drop (2 * k + 2) x.val) := by
      rw [List.length_map, List.length_take]
      rcases le_or_gt x.val.length (2 * k + 2) with hl | hl
      · simp
      · simp [List.map_drop]
    exact hd.symm ▸ h

lemma wins_iff_answer (x : body (game hyp).tree) :
  x ∈ (game hyp).payoff ↔ WinningCondition (x.val.take (2 * k + 2)) (by simp) := by
  have hmem : (bodyFunctor.map (treeHom hyp) x).val ∈
      ((x.val.take (2 * k + 2)).map Prod.fst ++ₛ ·)
    '' body (getTree' hyp (x.val.take (2 * k + 2))) := by
    use (x.val.drop (2 * k + 2)).map Prod.fst
    constructor
    · apply mem_body_of_take 0; intro n _
      rw [← Stream'.map_take]
      have htd : Stream'.take n (Stream'.drop (2 * k + 2) x.val)
          = List.drop (2 * k + 2) (Stream'.take (2 * k + 2 + n) x.val) :=
        Stream'.take_drop (m := 2 * k + 2) (n := n) (a := x.val)
      have hmtd := congrArg (List.map Prod.fst) htd
      exact hmtd.symm ▸ by
        have hm := (mem_getTree (body.take (2 * k + 2 + n) x)).2
        have hdrop : List.drop (Stream'.take (2 * k + 2) x.val).length
              (List.map Prod.fst (Stream'.take (2 * k + 2 + n) x.val))
            = List.map Prod.fst (List.drop (2 * k + 2) (Stream'.take (2 * k + 2 + n) x.val)) := by
          rw [← List.map_drop]
          congr
          exact Stream'.length_take (2 * k + 2) x.val
        exact hdrop ▸ by
          convert hm using 1
          · conv => simp [body.take_coe, Stream'.take_take, Nat.add_comm]
            trivial
          · conv => simp [body.take_coe, Stream'.take_take, Nat.add_comm]
            congr
            exact (Stream'.length_take (2 + 2 * k) x.val).symm
    · change List.map Prod.fst (Stream'.take (2 * k + 2) x.val) ++ₛ
          Stream'.map Prod.fst (Stream'.drop (2 * k + 2) x.val) =
        (bodyFunctor.map (treeHom hyp) x).val
      rw [← Stream'.map_append_stream, Stream'.append_take_drop]
      exact (treeHom_body (hyp := hyp) x).symm
  constructor <;> intro h
  · apply (not_losing (x := body.take (2 * k + 2) x)).mp
    intro ⟨h', _⟩; rw [← Set.subset_empty_iff] at h'
    have hbody :
        ((ConcreteCategory.hom (bodyFunctor.map (treeHom hyp))) x).val ∈
          body (pullSub (getTree' hyp (Stream'.take (2 * k + 2) x.val))
            (List.map Prod.fst (Stream'.take (2 * k + 2) x.val))) := by
      rwa [pullSub_body]
    exact h' (a := (bodyFunctor.map (treeHom hyp) x).val)
      ⟨hbody, by simpa⟩
  · change (bodyFunctor.map (treeHom hyp) x) ∈ G.payoff
    have hbody :
        ((ConcreteCategory.hom (bodyFunctor.map (treeHom hyp))) x).val ∈
          body (pullSub (getTree' hyp (Stream'.take (2 * k + 2) x.val))
            (List.map Prod.fst (Stream'.take (2 * k + 2) x.val))) := by
      rwa [pullSub_body]
    exact Subtype.val_injective.mem_set_image.mp (h.1 hbody)
instance : TopologicalSpace (upA hyp) := ⊥
instance : DiscreteTopology (upA hyp) where eq_bot := rfl
lemma payoff_clopen : IsClopen (game hyp).payoff := by
  classical
  let f : (Stream' (upA hyp)) → Bool :=
    (fun x ↦ ∃ h, WinningCondition x h) ∘ Stream'.take (2 * k + 2)
  suffices Continuous f by
    constructor
    · convert IsClosed.preimage continuous_subtype_val
        (IsClosed.preimage this (isClosed_discrete ({true} : Set Bool)))
      ext; simp [- game_payoff, - game_tree, wins_iff_answer, f]
    · convert IsOpen.preimage continuous_subtype_val
        (IsOpen.preimage this (isOpen_discrete ({true} : Set Bool)))
      ext; simp [- game_payoff, - game_tree, wins_iff_answer, f]
  --TODO generalize, how to phrase?
  let _ : TopologicalSpace (List (upA hyp)) := ⊥
  have : DiscreteTopology (List (upA hyp)) := ⟨rfl⟩
  apply continuous_bot.comp
  rw [(isTopologicalBasis_singletons _).continuous_iff]
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  by_cases h : x.length = 2 * k + 2
  · convert principalOpen_isOpen x
    ext
    simp [principalOpen_iff_restrict, h, Eq.comm]
  · convert isOpen_empty; rw [← Set.subset_empty_iff]; intro x hx
    apply h; simpa using congr_arg List.length hx.symm


lemma T'_snd_medium' (x : gameTree hyp) (h : x.val.length = 2 * k + 1) :
  ∃ S : QuasiStrategy (G.residual (x.val.map Prod.fst)).tree Player.one,
  getTree' hyp x.val = S.1.subtree := by
  have ⟨x, hx⟩ := x
  rcases x.eq_nil_or_concat' with rfl | ⟨x, a, rfl⟩
  · simp at h
  · conv at h => simp
    conv at hx => simp [ValidExt, h]
    rw [getTree_concat]
    convert hx.2.2 using 1
    rw [Game.residual_tree]
    have hmap : List.map Prod.fst (x ++ [a]) = x.map Prod.fst ++ [a.1] := List.map_append ..
    rw [hmap, ← subAt_append, ← T'_snd_small' ⟨x, hx.1⟩ (by simp [h])]
@[simp] lemma treeHom_extensions_val {x} (a : ExtensionsAt x) {y} (h : treeHom hyp x = y) :
  (ExtensionsAt.map (treeHom hyp) h a).val = a.val.1 := by
  have hval' : (ExtensionsAt.map (treeHom hyp) h a).val' = a.val'.map Prod.fst := by
    rw [ExtensionsAt.map_val']
    rfl
  have hlast := congrArg List.getLast? hval'
  have hleft : (ExtensionsAt.map (treeHom hyp) h a).val'.getLast? =
      some (ExtensionsAt.map (treeHom hyp) h a).val :=
    List.getLast?_append_of_ne_nil _ (by simp)
  have hright : (a.val'.map Prod.fst).getLast? = some a.val.1 := by
    change (List.map Prod.fst (x.val ++ [a.val])).getLast? = some a.val.1
    have hmap : List.map Prod.fst (x.val ++ [a.val]) = x.val.map Prod.fst ++ [a.val.1] :=
      List.map_append ..
    rw [hmap]
    exact List.getLast?_append_of_ne_nil _ (by simp)
  exact Option.some.inj (hleft.symm.trans (hlast.trans hright))
lemma extensionsAt_ext_fst {x : (game hyp).tree} (a b : ExtensionsAt x)
  (hx : 2 * k + 2 ≤ x.val.length) (h : a.val.1 = b.val.1) : a = b := by
  ext; apply Prod.ext h
  have ha := a.prop; have hb := b.prop
  conv at ha => simp [hx]
  conv at hb => simp [hx]
  rw [ha.2, hb.2, h]

lemma getTree_lost
  {x : (game hyp).tree} (y : (game hyp).tree) (h : x.val <+: y.val)
  (hxl : x.val.length = 2 * k + 2) --TODO synth le fails since update
  (hL : G.WonPosition (y.val.map Prod.fst) (Player.one.residual y.val)) :
  LosingCondition (hyp := hyp) x hxl := by
  apply not_winning.mp; intro hW
  conv at hL =>
    simp (config := {contextual := true}) [Game.wonPosition_iff_disjoint, Player.residual]
  rw [← Set.subset_empty_iff] at hL
  obtain ⟨a, ha1, ha2⟩ := isPruned_iff_principalOpen_ne.mp gameTree_isPruned y
  refine hL (a := (bodyFunctor.map (treeHom hyp) ⟨a, ha2⟩).val) ⟨?_, ?_⟩
  · rw [principalOpen_iff_restrict, treeHom_body, ← Stream'.map_take]
    rw [List.length_map]
    exact congrArg (List.map Prod.fst) ((principalOpen_iff_restrict _ _).mp ha1)
  · have hp :
        (if (y.val.length % 2 = 0) then
            (if (y.val.length % 2 = 0) then Player.one else Player.zero).swap
          else
            (if (y.val.length % 2 = 0) then Player.one else Player.zero).swap.swap).payoff G =
          G.payoff := by
      by_cases hy : y.val.length % 2 = 0 <;> simp [hy]
    have hbody : (bodyFunctor.map (treeHom hyp) ⟨a, ha2⟩).val ∈
        body (pullSub (getTree' hyp x.val) (x.val.map Prod.fst)) := by
      conv => simp
      use (a.map Prod.fst).drop (2 * k + 2)
      have hax : x.val = a.take (2 * k + 2) := by
        rw [(principalOpen_iff_restrict _ _).mp (principalOpen_mono h ha1)]; simp [hxl]
      constructor
      · apply mem_body_of_take 0; intro n _
        rw [Stream'.take_drop, ← Stream'.map_take]
        have hm := (mem_getTree ⟨a.take (2 * k + 2 + n), take_mem_body ha2 _⟩).2
        have hdrop : List.drop (Stream'.take (2 * k + 2) a).length
              (List.map Prod.fst (Stream'.take (2 * k + 2 + n) a)) =
            List.drop (2 * k + 2) (List.map Prod.fst (Stream'.take (2 * k + 2 + n) a)) := by
          congr
          exact Stream'.length_take (2 * k + 2) a
        exact hdrop ▸ by
          convert hm using 1
          · conv => simp [hax, Stream'.take_take, Nat.add_comm]
            trivial
          · conv => simp [hax, Stream'.take_take, Nat.add_comm]
            congr
            exact (Stream'.length_take (2 + 2 * k) a).symm
      · rw [hax]
        have htakeMap : List.map Prod.fst (Stream'.take (2 * k + 2) a) =
            Stream'.take (2 * k + 2) (Stream'.map Prod.fst a) :=
          Stream'.map_take (a := a) (n := 2 * k + 2) Prod.fst
        exact htakeMap.symm ▸ by
          change Stream'.take (2 * k + 2) (Stream'.map Prod.fst a) ++ₛ
              Stream'.drop (2 * k + 2) (Stream'.map Prod.fst a) =
            (bodyFunctor.map (treeHom hyp) ⟨a, ha2⟩).val
          rw [Stream'.append_take_drop]
          exact (treeHom_body (hyp := hyp) ⟨a, ha2⟩).symm
    have hpay : (bodyFunctor.map (treeHom hyp) ⟨a, ha2⟩) ∈ G.payoff :=
      Subtype.val_injective.mem_set_image.mp (hW.1 hbody)
    apply Subtype.val_injective.mem_set_image.mpr
    change (bodyFunctor.map (treeHom hyp) ⟨a, ha2⟩) ∈
      (if (y.val.length % 2 = 0) then
          (if (y.val.length % 2 = 0) then Player.one else Player.zero).swap
        else
          (if (y.val.length % 2 = 0) then Player.one else Player.zero).swap.swap).payoff G
    rwa [hp]
lemma LosingCondition.not_lost_short {x : (game hyp).tree} (hxl : 2 * k + 2 ≤ x.val.length)
  (H : LosingCondition (Tree.take (2 * k + 2) x).val (by simpa))
  (hnL : ¬ G.WonPosition (x.val.map Prod.fst) (Player.one.residual x.val)) :
  x.val.length + 1 ≤ 2 * k + 2 + H.y.val.length := by
  by_contra hlen; apply hnL
  have hx := mem_getTree x; erw [H.y_spec] at hx
  let u := List.map Prod.fst (List.take (2 * k + 2) x.val) ++ H.y.val
  rw [pullSub_append] at hx
  change List.map Prod.fst x.val ∈ pullSub (subAt G.tree u) u at hx
  have htakeLen : (List.take (2 * k + 2) x.val).length = 2 * k + 2 := by simp [hxl]
  have hlong : (List.take (2 * k + 2) x.val).length + H.y.val.length ≤ x.val.length := by omega
  have hlongMap : u.length ≤ (List.map Prod.fst x.val).length := by
    calc
      u.length = (List.take (2 * k + 2) x.val).length + H.y.val.length := by
        simp [u, List.length_map]
        rfl
      _ ≤ x.val.length := hlong
      _ = (List.map Prod.fst x.val).length := by
        rw [List.length_map]
        rfl
  rw [mem_pullSub_long (T := subAt G.tree u) (x := u) (y := List.map Prod.fst x.val)
    hlongMap] at hx
  obtain ⟨z, _, hze⟩ := hx; have hW := H.1
  simp_rw [H.y_spec, pullSub_append, pullSub_body, subAt_body] at hW
  have hU : G.WonPosition u (Player.one.residual u) := by
    rw [Game.wonPosition_iff_disjoint]
    simp_rw [Set.image_preimage_eq_range_inter, Set.inter_assoc, take_coe] at hW
    have hp : ((Player.one.residual u).swap).residual u = Player.zero := by
      rw [Player.residual_swap, Player.residual_residual]
      simp
    rw [hp]
    rw [Player.payoff_zero]
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    rw [Set.eq_empty_iff_forall_notMem] at hW
    apply hW s
    constructor
    · rcases hs.1 with ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rcases hs.2 with ⟨b, hb, rfl⟩
      exact ⟨b.prop, ⟨b, hb, rfl⟩⟩
  have hUz := Game.WonPosition.extend z (G := G) (p := Player.one.residual u) (x := u) hU
  rw [Player.residual_residual] at hUz
  rw [← hze] at hUz
  convert hUz using 1
  simp [Player.residual, List.length_map]
  rfl
lemma extensionsAt_eq_of_lost
  {x : (game hyp).tree} (y : (game hyp).tree) (h : x.val <+: y.val)
  (hxl : 2 * k + 2 ≤ x.val.length)
  (hnL : ¬ G.WonPosition (x.val.map Prod.fst) (Player.one.residual x.val))
  (hL : G.WonPosition (y.val.map Prod.fst) (Player.one.residual y.val))
  {a b : ExtensionsAt x} : a = b := by
  let H := getTree_lost y (x := Tree.take (2 * k + 2) x)
    ((x.val.take_prefix _).trans h) (by simpa) hL
  have hlen := H.not_lost_short hxl hnL
  apply extensionsAt_ext_fst _ _ hxl
  have ha := mem_getTree a.valT'; have hb := mem_getTree b.valT'
  have Hys := H.y_spec; conv at Hys => simp
  conv at ha => simp (disch := omega) [ExtensionsAt.val', List.take_append_of_le_length, Hys]
  conv at hb => simp (disch := omega) [ExtensionsAt.val', List.take_append_of_le_length, Hys]
  let u := List.map Prod.fst (List.take (2 * k + 2) x.val) ++ H.y.val
  change List.map Prod.fst (x.val ++ [a.val]) ∈ pullSub (subAt G.tree u) u at ha
  change List.map Prod.fst (x.val ++ [b.val]) ∈ pullSub (subAt G.tree u) u at hb
  have htakeLen : (List.take (2 * k + 2) x.val).length = 2 * k + 2 := by simp [hxl]
  have hulen : u.length = 2 * k + 2 + H.y.val.length := by
    simp only [u, List.length_append, List.length_map]
    exact congrArg (· + H.y.val.length) htakeLen
  have hextlen : ∀ c : ExtensionsAt x,
      (List.map Prod.fst (x.val ++ [c.val])).length = x.val.length + 1 := fun c => by
    change (List.map Prod.fst c.val').length = x.val.length + 1
    rw [List.length_map]
    exact ExtensionsAt.val'_length c
  have hlast : ∀ c : ExtensionsAt x,
      (List.map Prod.fst (x.val ++ [c.val])).getLast? = some c.val.1 := fun c => by
    have hmap : List.map Prod.fst (x.val ++ [c.val]) = x.val.map Prod.fst ++ [c.val.1] :=
      List.map_append ..
    rw [hmap]
    exact List.getLast?_append_of_ne_nil _ (by simp)
  have hshortA : (List.map Prod.fst (x.val ++ [a.val])).length ≤ u.length := by
    rw [hextlen a, hulen]; omega
  have hshortB : (List.map Prod.fst (x.val ++ [b.val])).length ≤ u.length := by
    rw [hextlen b, hulen]; omega
  rw [mem_pullSub_short (T := subAt G.tree u) (x := u)
    (y := List.map Prod.fst (x.val ++ [a.val])) hshortA] at ha
  rw [mem_pullSub_short (T := subAt G.tree u) (x := u)
    (y := List.map Prod.fst (x.val ++ [b.val])) hshortB] at hb
  have hlenEq : (List.map Prod.fst (x.val ++ [a.val])).length =
      (List.map Prod.fst (x.val ++ [b.val])).length := by
    rw [hextlen a, hextlen b]
  rcases List.prefix_or_prefix_of_prefix ha.1 hb.1 with h | h
  · have he := congrArg List.getLast? (h.eq_of_length hlenEq)
    rw [hlast a, hlast b] at he
    exact Option.some.inj he
  · symm
    have he := congrArg List.getLast? (h.eq_of_length hlenEq.symm)
    rw [hlast b, hlast a] at he
    exact Option.some.inj he

end «Section1»
end GaleStewartGame.BorelDet
