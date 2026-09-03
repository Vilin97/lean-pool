/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Pinned
import LeanPool.IsoGraph.ForMathlib.Array

/-!
# Backjumping is sound

When the search finds a leaf whose certificate ties the incumbent's, it harvests the automorphism
`autoOf` relating the two labellings and then *backjumps*: it abandons every branch between the
current leaf and the deepest node the two leaves share.  This file justifies that.

* `commonPrefix*` — the elementary facts about `Canon.commonPrefix`, which measures how much of
  two leaves' paths coincide.
* `auto_path` — the harvested automorphism follows the paths.  If two nodes agree on their first
  `j` individualised vertices then `autoOf` sends the `j`-th choice of one to the `j`-th choice of
  the other.  This is where `Pinned` pays off: `Node.pin` parks both choices at the same *position*
  in the labelling, so `autoOf_get` reads off the correspondence.
* `Node.ancestor` — every prefix of a node's path is itself a node.
* `jump_sound` — the payoff.  Let `q` be the shared depth-`j` node.  Then `autoOf` fixes `q`
  pointwise and maps `q`'s child along `path1` to `q`'s child along `path2`, so the two subtrees
  have exactly the same set of leaf keys.  Everything still to be found under the first is
  therefore already recorded under the second — the branch depth-first search has *finished*.
-/

namespace IsoGraph
namespace Canon

/-! ## The longest common prefix -/

theorem commonPrefixFrom_ge (a b : Array Nat) (m : Nat) :
    ∀ (fuel i : Nat), i ≤ m → i ≤ commonPrefixFrom a b m fuel i
  | 0, i, _ => Nat.le_refl i
  | fuel + 1, i, hi => by
    rw [commonPrefixFrom]
    split
    · exact hi
    · split
      · exact Nat.le_trans (Nat.le_succ i) (commonPrefixFrom_ge a b m fuel (i + 1) (by omega))
      · exact Nat.le_refl i

theorem commonPrefixFrom_le (a b : Array Nat) (m : Nat) :
    ∀ (fuel i : Nat), i ≤ m → commonPrefixFrom a b m fuel i ≤ m
  | 0, i, hi => hi
  | fuel + 1, i, hi => by
    rw [commonPrefixFrom]
    split
    · exact Nat.le_refl m
    · split
      · exact commonPrefixFrom_le a b m fuel (i + 1) (by omega)
      · exact hi

theorem commonPrefixFrom_eq (a b : Array Nat) (m : Nat) :
    ∀ (fuel i k : Nat), i ≤ k → k < commonPrefixFrom a b m fuel i → a[k]! = b[k]!
  | 0, i, k, hik, hk => by rw [commonPrefixFrom] at hk; omega
  | fuel + 1, i, k, hik, hk => by
    rw [commonPrefixFrom] at hk
    split at hk
    · rename_i him
      have := commonPrefixFrom_ge a b m (fuel + 1) i (by omega)
      omega
    · split at hk
      · rename_i heq
        rcases Nat.lt_or_ge k (i + 1) with h1 | h1
        · have hki : k = i := by omega
          subst hki; simpa using heq
        · exact commonPrefixFrom_eq a b m fuel (i + 1) k h1 hk
      · omega

theorem commonPrefixFrom_ne (a b : Array Nat) (m : Nat) :
    ∀ (fuel i : Nat), i ≤ m → m ≤ i + fuel → commonPrefixFrom a b m fuel i < m →
      a[commonPrefixFrom a b m fuel i]! ≠ b[commonPrefixFrom a b m fuel i]!
  | 0, i, _, _, hlt => by rw [commonPrefixFrom] at hlt ⊢; omega
  | fuel + 1, i, hi, hf, hlt => by
    rw [commonPrefixFrom] at hlt ⊢
    split at hlt
    · omega
    · rename_i him
      split at hlt
      · rw [ite_eq_right him, ite_eq_left ‹_›]
        exact commonPrefixFrom_ne a b m fuel (i + 1) (by omega) (by omega) hlt
      · rename_i hne
        rw [ite_eq_right him, ite_eq_right hne]
        simpa using hne

theorem commonPrefix_le (a b : Array Nat) : commonPrefix a b ≤ min a.size b.size :=
  commonPrefixFrom_le a b _ _ 0 (Nat.zero_le _)

theorem commonPrefix_eq {a b : Array Nat} {k : Nat} (h : k < commonPrefix a b) : a[k]! = b[k]! :=
  commonPrefixFrom_eq a b _ _ 0 k (Nat.zero_le _) h

theorem commonPrefix_ne {a b : Array Nat} (h : commonPrefix a b < min a.size b.size) :
    a[commonPrefix a b]! ≠ b[commonPrefix a b]! :=
  commonPrefixFrom_ne a b _ _ 0 (Nat.zero_le _) (by omega) h

/-- The paths of two leaves agree strictly before their longest common prefix. -/
theorem commonPrefix_take (a b : Array Nat) :
    a.toList.take (commonPrefix a b) = b.toList.take (commonPrefix a b) := by
  have h := commonPrefix_le a b
  exact take_toList_eq (by omega) (by omega) fun k hk => commonPrefix_eq hk

/-! ## The automorphism relating two leaves maps one branch onto the other -/

theorem Part.WF.lab_permArr {n : Nat} {p : Part} (hp : Part.WF n p) : PermArr n p.lab :=
  ⟨hp.labSize, hp.labLt, fun i hi j hj h => by
    have h1 := hp.posLab i hi
    have h2 := hp.posLab j hj
    rw [h] at h1; omega⟩

/-- **The harvested automorphism follows the paths.**  If two nodes agree on their first `j`
individualised vertices, the permutation `autoOf` builds from their labellings sends the `j`-th
choice of one to the `j`-th choice of the other — because `Node.pin` parks both at the same
position. -/
theorem auto_path {n : Nat} {f : Nat → Nat → Bool} {path1 path2 : Array Nat}
    {ip1 ip2 : Array UInt64} {p1 p2 : Part} (h1 : Node n f path1 ip1 p1)
    (h2 : Node n f path2 ip2 p2) {j : Nat} (hj1 : j < path1.size) (hj2 : j < path2.size)
    (hpre : path1.toList.take j = path2.toList.take j) :
    (autoOf n p1.lab p2.lab)[path1[j]!]! = path2[j]! := by
  have hq1 := h1.pin j hj1
  have hq2 := h2.pin j hj2
  rw [← hpre] at hq2
  rw [← hq1.lab, autoOf_get h1.wf.lab_permArr hq1.lt, hq2.lab]

/-! ## Ancestors -/

/-- Every prefix of a node's path is itself a node. -/
theorem Node.ancestor {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {ip : Array UInt64}
    {p : Part} (h : Node n f path ip p) :
    ∀ j, j ≤ path.size → ∃ iq q, Node n f (path.extract 0 j) iq q := by
  induction h with
  | root =>
    intro j hj
    simp only [Array.size_empty, Nat.le_zero] at hj
    subst hj
    rw [show (#[] : Array Nat).extract 0 0 = #[] by simp]
    exact ⟨_, _, Node.root⟩
  | @step path ip p c v hnode hc hv hcell ih =>
    intro j hj
    rw [Array.size_push] at hj
    rcases Nat.lt_or_ge j (path.size + 1) with h1 | h1
    · obtain ⟨iq, q, hq⟩ := ih j (by omega)
      exact ⟨iq, q, by rwa [push_extract (by omega)]⟩
    · have hjp : j = path.size + 1 := by omega
      subst hjp
      rw [show (path.push v).extract 0 (path.size + 1) = path.push v by
        rw [show path.size + 1 = (path.push v).size by simp, extract_self]]
      exact ⟨_, _, Node.step hnode hc hv hcell⟩

/-! ## Backjumping is sound -/

/-- **The key lemma behind the backjump.**  Two leaves with equal certificates differ by an
automorphism `γ`.  If `j` is the length of their common path prefix and `q` the depth-`j` node they
share, then `γ` fixes `q` and sends `q`'s child `path1[j]` to `q`'s child `path2[j]`.  So every leaf
key still to be found below the first branch already occurs below the second — which is the branch
depth-first search has *already finished*. -/
theorem jump_sound {n : Nat} {f : Nat → Nat → Bool} {path1 path2 : Array Nat}
    {ip1 ip2 iq : Array UInt64} {p1 p2 q : Part} {j : Nat} {k : List (List UInt64)}
    (h1 : Node n f path1 ip1 p1) (h2 : Node n f path2 ip2 p2)
    (hq : Node n f (path1.extract 0 j) iq q)
    (hcert : certOf (Graph.ofOracle n f) p1.lab = certOf (Graph.ofOracle n f) p2.lab)
    (hj : j ≤ commonPrefix path1 path2) (hj1 : j < path1.size) (hj2 : j < path2.size)
    (hreach : Reach n f (childInv (Graph.ofOracle n f) iq q path1[j]!)
      (child (Graph.ofOracle n f) q path1[j]!).1 k) :
    Reach n f (childInv (Graph.ofOracle n f) iq q path2[j]!)
      (child (Graph.ofOracle n f) q path2[j]!).1 k := by
  have hcp := commonPrefix_le path1 path2
  have hg : IsAutoArr n f (autoOf n p1.lab p2.lab) :=
    autoOf_isAuto h1.wf.lab_permArr h2.wf.lab_permArr hcert
  -- `γ` fixes every vertex of the shared prefix
  have hfix : ∀ i, i < (path1.extract 0 j).size →
      (autoOf n p1.lab p2.lab)[(path1.extract 0 j)[i]!]! = (path1.extract 0 j)[i]! := by
    intro i hi
    rw [extract_size (by omega)] at hi
    rw [extract_getElemD hi]
    have heq : path1.toList.take i = path2.toList.take i :=
      take_toList_eq (by omega) (by omega) fun m hm => commonPrefix_eq (by omega)
    rw [auto_path h1 h2 (by omega) (by omega) heq]
    exact (commonPrefix_eq (k := i) (by omega)).symm
  have he : PartEquiv n (fun x => (autoOf n p1.lab p2.lab)[x]!) q q :=
    hq.auto_partEquiv hg hfix
  -- and sends the first branch to the second
  have hmap : (autoOf n p1.lab p2.lab)[path1[j]!]! = path2[j]! :=
    auto_path h1 h2 hj1 hj2 (take_toList_eq (by omega) (by omega)
      fun m hm => commonPrefix_eq (by omega))
  rw [← hmap]
  exact reach_child_auto hg hq.wf he (h1.path_lt j hj1) hreach

end Canon
end IsoGraph
