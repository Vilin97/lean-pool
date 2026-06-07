/-
Copyright (c) 2026 György Kurucz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: György Kurucz
-/
import Mathlib.Data.Set.Operations
import Mathlib.Order.KonigLemma

import LeanPool.LeanModelChecking.LTL_NBW_Statement
import LeanPool.LeanModelChecking.ABW

def ABW.toNBW {S Q} (A : ABW S Q) : NBW S := {
  Q := (Set Q) × (Set Q)
  q₀ := {({A.q₀}, ∅)}
  δ := fun (X, W) s (X', W') =>
    (∀ q ∈ X, PositiveBool.Sat X' (A.δ q s)) ∧ (
      (W = ∅ ∧ W' = X' \ A.F) ∨
      (W ≠ ∅ ∧ ∃ W'', (
        W' = W'' \ A.F ∧ W'' ⊆ X' ∧ (∀ q ∈ W, PositiveBool.Sat W'' (A.δ q s))
      ))
    )
  F := { (_, W) | W = ∅ }
}

theorem ABW.toNBW.lang_sub {S Q} {A : ABW S Q} {w : Nat → S} : (ABW.toNBW A).language w → A.language w := by
  simp [ABW.language, NBW.language, NBW.run]
  intros p h1 h2 h3
  let X i := (p i).fst
  let W i := (p i).snd
  let G : RunDAG A w := {
    V := { (q, i) : _ | q ∈ X i }
    E := { ((q, i), q') : _ | (q ∈ X i \ W i ∧ q' ∈ X (i + 1)) ∨ (q ∈ X i ∩ W i ∧ q' ∈ X (i + 1) ∩ (A.F ∪ W (i + 1))) }
    edge_closure := by grind
    p_root := by grind [ABW.toNBW]
    p_sat := by
      simp
      intros q i h10
      specialize h2 i
      rcases h2 with ⟨h11, h12⟩
      specialize h11 q h10
      grind
  }
  exists G
  simp [RunDAG.accepting, DAG.path]
  intros pp b hp1
  have h4 : ∀ i, W (b + i) = ∅ → ∀ n, pp (i + n + 1) ∈ W (b + i + n + 1) ∨ ∃ j, i ≤ j ∧ j ≤ b + i + n + 1 ∧ pp j ∈ A.F := by
    intros i hw n
    induction n <;> grind [ABW.toNBW]
  intros i
  rcases h3 (b + i) with ⟨start, start_gt, hstart⟩
  rcases h3 (start + 1) with ⟨endi, end_gt, hend⟩
  have eq2 : start = b + (start - b) := by omega
  specialize h4 (start - b) (eq2 ▸ hstart) (endi - start - 1)
  rcases h4 with h4 | ⟨j, h4⟩
  · exfalso
    simp [W] at h4
    rw [show (b + (start - b) + (endi - start - 1) + 1)= endi by omega] at h4
    rw [hend] at h4
    contradiction
  · grind

lemma lemma1 {α : Type} {a b c : Set α} {h : Disjoint a b} : a = (a ∪ (b ∩ c)) \ b := by
  rw [Set.union_diff_distrib]
  rw [Disjoint.sdiff_eq_right h.symm]
  rw [←Set.sdiff_inter_right_comm]
  simp

def level {S Q} {A : ABW S Q} {w : Nat → S} {G : RunDAG A w} (i : Nat) : Set Q := { q | (q, i) ∈ G.V }

structure LevelGraph where
  level : Nat → Type
  E : (i : Nat) → level i → level (i + 1) → Prop
  ex_parent : ∀ i (v : level (i + 1)), ∃ (v' : level i), E i v' v
  fin : ∀ i, Finite (level i)
  nonempty : ∀ i, Nonempty (level i)

namespace LevelGraph

structure Path (G : LevelGraph) where
  f : ∀ i, G.level i
  p : ∀ i, G.E i (f i) (f (i + 1))

section
variable {G : LevelGraph}

noncomputable def ancestor {i j} (hij : i ≤ j) (v : G.level j) : G.level i :=
  if eq : i = j then
    eq ▸ v
  else
    ancestor (show i ≤ (j - 1) by omega) (G.ex_parent (j - 1) ((show (j - 1) + 1 = j by omega) ▸ v)).choose

lemma ancestor_refl {i} (v : G.level i) : ancestor rfl.le v = v := by simp [ancestor]

lemma ancestor_1 {i j} (hij : i ≤ j) (v : G.level (j + 1)) : ancestor hij (G.ex_parent j v).choose = ancestor (show i ≤ j + 1 by omega) v := by
  rewrite (occs := .pos [2]) [ancestor.eq_def]
  by_cases eq : i = j
  · subst eq; simp
  · simp [show i ≠ j + 1 by omega]

lemma ancestor_trans {i j k} (hij : i ≤ j) (hjk : j ≤ k) (v : G.level k) : ancestor hij (ancestor hjk v) = ancestor (hij.trans hjk) v := by
  induction k
  · have i0 : i = 0 := by omega
    have j0 : j = 0 := by omega
    subst i0
    subst j0
    unfold ancestor
    simp
    apply ancestor_refl
  next k IH =>
    by_cases jeq : j = k + 1
    · subst jeq
      rw [ancestor_refl]
    · specialize IH (by omega) (G.ex_parent k v).choose
      rwa [ancestor_1, ancestor_1] at IH

end

lemma choose_eq {α} {p : α → Prop} (P : ∃ a, p a) {a} (eq : P.choose = a) : p a := eq ▸ P.choose_spec
lemma ex_path (G : LevelGraph) : Nonempty (Path G) := by
  have := G.fin
  have := G.nonempty
  obtain ⟨f, pf⟩ := exists_seq_forall_proj_of_forall_finite
    (@ancestor G)
    (@ancestor_refl G)
    (@ancestor_trans G)
    (by intros; apply Subtype.finite)
  exists ?_
  intros i
  specialize pf (show i ≤ i + 1 by omega)
  unfold ancestor at pf
  simp at pf
  rw [ancestor_refl] at pf
  have := choose_eq _ pf
  assumption

end LevelGraph

open Classical in
def helper.p {S Q} {A : ABW S Q} {w : Nat → S} {G : RunDAG A w} : Nat → (Set Q) × (Set Q)
| 0 => ({A.q₀}, ∅)
| i + 1 =>
  let X' := level (G := G) (i + 1)
  let (_, W) := p (G := G) i
  let W' :=
    if W = ∅ then
      X' \ A.F
    else
      { y' | y' ∉ A.F ∧ ∃ y, y ∈ W ∧ (y, i) ∈ G.V ∧ (y', i + 1) ∈ G.V ∧ ((y, i), y') ∈ G.E }
  (X', W')

theorem ABW.toNBW.lang_sup {S Q} {A : ABW S Q} [Finite Q] {w : Nat → S} : A.language w → (ABW.toNBW A).language w := by
  simp [ABW.language, RunDAG.accepting]
  intros G G_acc
  let p := helper.p (G := G)
  have p_path : A.toNBW.run p w := by
    simp [ABW.toNBW, NBW.run]
    constructor
    · apply Set.mem_singleton
    · intros n
      induction n
      next =>
        constructor
        · intros q Hqin
          simp [p, helper.p, level] at Hqin ⊢
          subst Hqin
          obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ G.p_root
          apply PositiveBool.Sat.monotone _ p_sat
          rw [Set.subset_def]
          intros q' q'Y
          have := G.edge_closure ((A.q₀, 0), q')
          grind
        · simp [p, helper.p, level]
      next n IH =>
        rcases IH with ⟨h1, IH⟩
        constructor
        · simp [p, helper.p, level] at *
          intros q hinV
          obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ hinV
          apply PositiveBool.Sat.monotone _ p_sat
          rw [Set.subset_def]
          intros q' q'Y
          have := G.edge_closure ((q, n + 1), q')
          grind
        · rcases IH with ⟨hW, h2⟩ | ⟨hW, ⟨W'', ⟨h2, h3, h4⟩⟩⟩
          · rw [h2]
            simp
            by_cases hinf : ((helper.p (G := G) (n + 1)).1 ⊆ A.F)
            · left
              rw [←Set.diff_eq_empty] at hinf
              refine ⟨hinf, ?_⟩
              simp [p, helper.p, level, hW] at hinf ⊢
              intros; contradiction
            · right
              have hW2 : (p (n + 1)).2 ≠ ∅ := by
                rw [h2]
                intro H
                rw [Set.diff_eq_empty] at H
                contradiction
              rw [←Set.diff_eq_empty] at hinf
              refine ⟨hinf, ?_⟩
              exists (p (n + 2)).2 ∪ (A.F ∩ (p (n + 2)).1)
              simp
              refine ⟨?_, ?_, ?_⟩
              · simp [p, helper.p]
                grind
              · simp [p, helper.p, level]
                grind
              · intros q qp1 qp2
                simp [p, helper.p, level] at qp1
                obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ qp1
                apply PositiveBool.Sat.monotone _ p_sat
                intros x xY
                simp [p] at *
                have := G.edge_closure ((q, n + 1), x)
                simp [helper.p, hW, level]
                grind
          · by_cases hinf : (W'' ⊆ A.F)
            · grind [helper.p]
            · right
              have hW2 : (p (n + 1)).2 ≠ ∅ := by
                rw [h2]
                intro H
                rw [Set.diff_eq_empty] at H
                contradiction
              refine ⟨hW2, ?_⟩
              exists (p (n + 2)).2 ∪ (A.F ∩ (p (n + 2)).1)
              simp
              refine ⟨?_, ?_, ?_⟩
              · simp [p, helper.p]
                grind
              · simp [p, helper.p, level]
                grind
              · intros q qp1
                simp [p, helper.p, level, hW] at qp1
                obtain ⟨qp1, b, qp2, qp3, qp4, qp5⟩ := qp1
                obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ qp4
                apply PositiveBool.Sat.monotone _ p_sat
                intros x xY
                have := G.edge_closure ((q, n + 1), x)
                simp [p, helper.p, level]
                grind
  exists p
  refine ⟨p_path, ?_⟩

  have W_not_F : ∀ i, (p i).2 ∩ A.F = ∅ := by
    intros i; cases i <;> simp [p, helper.p]; grind
  by_contra H
  unfold ABW.toNBW at H
  simp at H
  rcases H with ⟨n, W_nonempty⟩

  let S' : LevelGraph := {
    level i := { v // v ∈ (p (n + i)).2 }
    E i v v' := ((v.val, n + i), v'.val) ∈ G.E
    ex_parent i v := by
      specialize W_nonempty (n + i) (by omega)
      rcases v with ⟨v, vp⟩
      simp [p, helper.p, W_nonempty] at vp
      obtain ⟨_, y, yW, yE⟩ := vp
      exists ⟨y, by assumption⟩
      apply yE.right.right
    fin i := Subtype.finite
    nonempty i := by
      simp
      specialize W_nonempty (n + i) (by omega)
      grind
  }

  obtain ⟨⟨bad_path_f, bad_path_path⟩⟩ := S'.ex_path

  obtain ⟨j, jn, jF⟩ := G_acc (fun i => bad_path_f i) (by
    simp [DAG.path]
    simp [S'] at bad_path_path
    exists n
  ) n

  simp [S'] at bad_path_f
  specialize W_not_F (n + j)
  rw [←Set.disjoint_iff_inter_eq_empty] at W_not_F
  rw [Set.disjoint_left] at W_not_F
  specialize W_not_F (bad_path_f j).prop
  contradiction

theorem ABW.toNBW.lang_eq {S Q} (A : ABW S Q) [Finite Q] : A.language = (ABW.toNBW A).language := by
  funext; apply propext
  exact ⟨ABW.toNBW.lang_sup, ABW.toNBW.lang_sub⟩
