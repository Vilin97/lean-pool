/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Dominate
import LeanPool.IsoGraph.ForMathlib.Array

/-!
# The running invariants of the optimality induction

The depth-first search prunes three ways — invariant pruning, orbit pruning and backjumping — and
each needs its own reason why the leaves it skips were already accounted for.  This file sets up
the bookkeeping for the third and hardest one, backjumping.

* `take_getElemD`, `pathPre_of_take` — `PathPre` and "the first `j` entries agree" say the same
  thing.
* `ancReach_full`, `ancReach_push`, `ancReach_child` — the leaves below the depth-`j` ancestor of a
  path, related to `Reach` at the node itself and to `SubR` at one of its children.
* `mem_usableAutos` — the generators the search is willing to prune with really do fix the path.
* `Rec` / `Pth` / `Jmp` / `JmpC` — the invariants themselves.  `Jmp` says every branch a recorded
  leaf went down and the current path has already left behind consists of keys the caller has
  already accounted for; `JmpC` is the variant that holds while a node works through its own
  children.
* `leaf_abort_dom` — the payoff: the backjump a leaf update requests never skips a leaf that is
  not already dominated.  This is `jump_sound` fed by `Jmp`.
-/

namespace IsoGraph
namespace Canon

/-! ## Prefixes -/

theorem pathPre_of_take {a b : Array Nat} (hab : a.size ≤ b.size)
    (h : a.toList.take a.size = b.toList.take a.size) : PathPre a b :=
  ⟨hab, fun _ hi => take_getElemD h hi hi⟩

theorem take_of_pathPre {a b : Array Nat} (h : PathPre a b) :
    a.toList.take a.size = b.toList.take a.size :=
  take_toList_eq (Nat.le_refl _) h.1 h.2

/-! ## Ancestors -/

theorem ancReach_full {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) (k : List (List UInt64)) :
    ancReach n f path path.size k ↔ Reach n f invPath p k := by
  rw [ancReach, show path.toList.take path.size = path.toList by simp, h.nodePath_eq]

theorem ancReach_push {n : Nat} {f : Nat → Nat → Bool} (path : Array Nat) (v j : Nat)
    (hj : j ≤ path.size) (k : List (List UInt64)) :
    ancReach n f (path.push v) j k ↔ ancReach n f path j k :=
  ancReach_congr (by
    rw [Array.toList_push, List.take_append_of_le_length (by simpa using hj)]) k

theorem ancReach_child {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) (v : Nat)
    (k : List (List UInt64)) :
    ancReach n f (path.push v) (path.size + 1) k ↔ SubR n f invPath p v k := by
  rw [ancReach, Array.toList_push,
    show (path.toList ++ [v]).take (path.size + 1) = path.toList ++ [v] by simp,
    nodePath_append, h.nodePath_eq]
  exact Iff.rfl

/-! ## Usable automorphisms -/

theorem mem_usableAutos {autos : Array (Array Nat)} {path : Array Nat} {g : Array Nat}
    (h : g ∈ usableAutos autos path) :
    g ∈ autos ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]! := by
  rw [usableAutos] at h
  split at h
  · rename_i he
    rw [Array.isEmpty_iff] at he
    rw [he] at h
    simp at h
  · rw [Array.mem_filter] at h
    refine ⟨h.1, fun i hi => ?_⟩
    have := h.2
    simp only [Array.all_eq_true, beq_iff_eq] at this
    rw [getElem!_pos path i hi]
    exact this i hi

/-! ## The running invariants -/

/-- A leaf the state records. -/
def Rec (st : St) (l : Leaf) : Prop := st.best = some l ∨ st.first = some l

/-- No recorded leaf lies below the current node. -/
def Pth (st : St) (path : Array Nat) : Prop := ∀ l, Rec st l → ¬ PathPre path l.path

/-- **The backjump invariant**, relative to a target predicate `P` on leaf keys.  Every branch a
recorded leaf went down and that the current path has already left behind consists entirely of
keys satisfying `P`.  At the use site `P` is "dominated by the incumbent, or already accounted
for by the caller". -/
def Jmp (n : Nat) (f : Nat → Nat → Bool) (P : List (List UInt64) → Prop) (path : Array Nat)
    (st : St) : Prop :=
  ∀ l, Rec st l → ∀ j, j < path.size → j < l.path.size →
    path.toList.take j = l.path.toList.take j → path[j]! ≠ l.path[j]! →
      ∀ k, ancReach n f l.path (j + 1) k → P k

/-- The same, also covering the branches leaving the current node itself: what holds while a node
is working through its children. -/
def JmpC (n : Nat) (f : Nat → Nat → Bool) (P : List (List UInt64) → Prop) (path : Array Nat)
    (st : St) : Prop :=
  ∀ l, Rec st l → ∀ j, j ≤ path.size → j < l.path.size →
    path.toList.take j = l.path.toList.take j → (j < path.size → path[j]! ≠ l.path[j]!) →
      ∀ k, ancReach n f l.path (j + 1) k → P k

theorem JmpC.child {n : Nat} {f : Nat → Nat → Bool} {P : List (List UInt64) → Prop} {st : St}
    {path : Array Nat} (h : JmpC n f P path st) (v : Nat) : Jmp n f P (path.push v) st := by
  intro l hl j hj hjl htake hne k hk
  rw [Array.size_push] at hj
  have hjp : j ≤ path.size := by omega
  refine h l hl j hjp hjl ?_ (fun _ => ?_) k hk
  · rw [Array.toList_push, List.take_append_of_le_length (by simpa using hjp)] at htake
    exact htake
  · rwa [push_getElemD_lt path v (by assumption)] at hne

theorem JmpC.of_jmp {n : Nat} {f : Nat → Nat → Bool} {P : List (List UInt64) → Prop} {st : St}
    {path : Array Nat} (h : Jmp n f P path st) (hp : Pth st path) : JmpC n f P path st := by
  intro l hl j hjle hjl htake hne k hk
  rcases Nat.lt_or_ge j path.size with hlt | hge
  · exact h l hl j hlt hjl htake (hne hlt) k hk
  · have hjp : j = path.size := by omega
    subst hjp
    exact absurd (pathPre_of_take (by omega) htake) (hp l hl)

/-! ## The leaf case of the optimality induction -/

theorem Node.ancestor' {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {ip : Array UInt64}
    {p : Part} (h : Node n f path ip p) (j : Nat) (hj : j ≤ path.size) :
    Node n f (path.extract 0 j) (nodePath n f (path.toList.take j)).1
      (nodePath n f (path.toList.take j)).2 := by
  obtain ⟨iq, q, hq⟩ := h.ancestor j hj
  have he : nodePath n f (path.toList.take j) = (iq, q) := by
    have := hq.nodePath_eq
    rwa [show (path.extract 0 j).toList = path.toList.take j by simp] at this
  rw [he]
  exact hq

/-- **The backjump a leaf update requests is covered by the jump invariant.** -/
theorem leaf_abort_dom {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (hnode : Node n f path invPath p) {st : St}
    {P : List (List UInt64) → Prop}
    (hgood : StGood n f st) (hpth : Pth st path) (hjmp : Jmp n f P path st) {j : Nat}
    (hab : (leafUpdate (Graph.ofOracle n f) path invPath p.lab st).abortTo = some j) :
    j < path.size ∧ ∀ k, ancReach n f path (j + 1) k → P k := by
  obtain ⟨z, hrec, hcert, hjeq⟩ := leafUpdate_abort hab
  have hrec' : Rec st z := hrec.symm
  obtain ⟨q2, hq2, htc2, _, hcert2⟩ : LeafNode n f z := hrec.elim (hgood.2.1 z) (hgood.1 z)
  have hcp := commonPrefix_le path z.path
  -- the branch point is strictly inside the current path
  have hjlt : j < path.size := by
    rcases Nat.lt_or_ge j path.size with h | h
    · exact h
    · exfalso
      have hjs : j = path.size := by omega
      refine hpth z hrec' (pathPre_of_take (by omega) ?_)
      rw [← hjs, hjeq]
      exact commonPrefix_take path z.path
  -- and strictly inside the recorded leaf's path
  have hjlt2 : j < z.path.size := by
    rcases Nat.lt_or_ge j z.path.size with h | h
    · exact h
    · exfalso
      have hjz : j = z.path.size := by omega
      have hnp : nodePath n f (path.toList.take j) = (z.invPath, q2) := by
        rw [hjeq] at hjz ⊢
        rw [commonPrefix_take path z.path, hjz,
          show z.path.toList.take z.path.size = z.path.toList by simp]
        exact hq2.nodePath_eq
      exact hnode.ancestor_targetCell j hjlt (by rw [hnp]; exact htc2)
  refine ⟨hjlt, fun k hk => ?_⟩
  -- move the leaf key across to the recorded leaf's branch
  have htake : path.toList.take j = z.path.toList.take j := by
    rw [hjeq]; exact commonPrefix_take path z.path
  have hq : Node n f (path.extract 0 j) (nodePath n f (path.toList.take j)).1
      (nodePath n f (path.toList.take j)).2 := hnode.ancestor' j (by omega)
  have hcerteq : certOf (Graph.ofOracle n f) p.lab = certOf (Graph.ofOracle n f) q2.lab := by
    rw [← hcert2]; exact lexCmpU64_eq_iff.1 hcert
  have hk' : ancReach n f z.path (j + 1) k := by
    rw [ancReach, nodePath_take_succ n f z.path hjlt2, ← htake]
    have := jump_sound (path1 := path) (path2 := z.path) hnode hq2 hq hcerteq
      (by rw [hjeq]) hjlt hjlt2
      (by rw [ancReach, nodePath_take_succ n f path hjlt] at hk; exact hk)
    exact this
  exact hjmp z hrec' j hjlt hjlt2 htake
    (by rw [hjeq]; exact commonPrefix_ne (by omega)) k hk'

end Canon
end IsoGraph
