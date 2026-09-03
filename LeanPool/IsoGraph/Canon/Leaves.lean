/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Jump

/-!
# The leaves and generators a state holds

Bookkeeping for the optimality proof, one layer above `Jump.lean`.

* `commonPrefix_comm` — the backjump depth does not depend on which of the two leaves is "current".
* `ancReach` — the leaves below the depth-`j` ancestor of a path, phrased through `nodePath` so
  that it only depends on `path.toList.take j`.  `Node.ancestor_targetCell` says an interior node
  of a path is never a leaf, which is what rules out one leaf's path being a prefix of another's.
* `Chld` / `SubR` / `reach_iff_subR` — a node's leaves are exactly the leaves of its children,
  and `mem_extract_cell'` identifies the children with the entries of the child list.
* `invAuto` — the inverse of a permutation array, needed because orbit pruning has to move leaves
  *back* along a generator.
* `LeafNode` / `StGood` / `dfsNode_good` — every leaf a state records is a genuine leaf of the
  tree, and every generator it records is a genuine automorphism.
-/

namespace IsoGraph
namespace Canon

/-! ## `commonPrefix` is symmetric -/

theorem commonPrefixFrom_comm (a b : Array Nat) (m : Nat) :
    ∀ (fuel i : Nat), commonPrefixFrom a b m fuel i = commonPrefixFrom b a m fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    rw [commonPrefixFrom, commonPrefixFrom]
    have hb : (a[i]! == b[i]!) = (b[i]! == a[i]!) := by
      by_cases h : a[i]! = b[i]!
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hb, commonPrefixFrom_comm a b m fuel (i + 1)]

theorem commonPrefix_comm (a b : Array Nat) : commonPrefix a b = commonPrefix b a := by
  simp only [commonPrefix]
  rw [Nat.min_comm b.size a.size]
  exact commonPrefixFrom_comm a b _ _ 0

/-! ## Ancestors as a function of the path -/

theorem nodePath_take_succ (n : Nat) (f : Nat → Nat → Bool) (path : Array Nat) {j : Nat}
    (hj : j < path.size) :
    nodePath n f (path.toList.take (j + 1))
      = (childInv (Graph.ofOracle n f) (nodePath n f (path.toList.take j)).1
           (nodePath n f (path.toList.take j)).2 path[j]!,
         (child (Graph.ofOracle n f) (nodePath n f (path.toList.take j)).2 path[j]!).1) := by
  have hlen : j < path.toList.length := by simpa using hj
  have he : path.toList.take (j + 1) = path.toList.take j ++ [path[j]!] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlen]
    congr 1
    rw [getElem!_pos path j hj]
    simp
  rw [he, nodePath_append]

/-- The leaves below the depth-`j` ancestor of `path`. -/
def ancReach (n : Nat) (f : Nat → Nat → Bool) (path : Array Nat) (j : Nat)
    (k : List (List UInt64)) : Prop :=
  Reach n f (nodePath n f (path.toList.take j)).1 (nodePath n f (path.toList.take j)).2 k

theorem ancReach_congr {n : Nat} {f : Nat → Nat → Bool} {a b : Array Nat} {j : Nat}
    (h : a.toList.take j = b.toList.take j) (k : List (List UInt64)) :
    ancReach n f a j k ↔ ancReach n f b j k := by rw [ancReach, ancReach, h]

/-- Interior nodes of a path are not leaves. -/
theorem Node.ancestor_targetCell {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) :
    ∀ j, j < path.size → (nodePath n f (path.toList.take j)).2.targetCell n ≠ none := by
  induction h with
  | root => intro j hj; simp at hj
  | @step path invPath p c v hnode hc hv hcell ih =>
    intro j hj
    rw [Array.size_push] at hj
    rcases Nat.lt_or_ge j path.size with h1 | h1
    · rw [Array.toList_push, List.take_append_of_le_length (by simpa using Nat.le_of_lt h1)]
      exact ih j h1
    · have hjp : j = path.size := by omega
      subst hjp
      rw [Array.toList_push, show (path.toList ++ [v]).take path.size = path.toList by simp,
        show (nodePath n f path.toList).2 = p from congrArg Prod.snd hnode.nodePath_eq, hc]
      simp

/-! ## Children -/

/-- `w` is a child of the node `p`: a vertex of its target cell. -/
def Chld (n : Nat) (p : Part) (w : Nat) : Prop :=
  ∃ c, p.targetCell n = some c ∧ w < n ∧ p.cst[p.pos[w]!]! = c

/-- The leaves below the child `w`. -/
def SubR (n : Nat) (f : Nat → Nat → Bool) (invPath : Array UInt64) (p : Part) (w : Nat)
    (k : List (List UInt64)) : Prop :=
  Reach n f (childInv (Graph.ofOracle n f) invPath p w) (child (Graph.ofOracle n f) p w).1 k

theorem reach_iff_subR {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    {c : Nat} (htc : p.targetCell n = some c) (k : List (List UInt64)) :
    Reach n f invPath p k ↔ ∃ w, Chld n p w ∧ SubR n f invPath p w k := by
  constructor
  · intro h
    cases h with
    | leaf htc' => rw [htc] at htc'; exact absurd htc' (by simp)
    | step hc hv hcell h => exact ⟨_, ⟨_, hc, hv, hcell⟩, h⟩
  · rintro ⟨w, ⟨c', hc', hw, hcell⟩, h⟩
    exact Reach.step hc' hw hcell h

/-- Membership in the child list is exactly `Chld`. -/
theorem mem_extract_cell' {n : Nat} {p : Part} (hp : Part.WF n p) {c v : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (hv : v < n) (hcell : p.cst[p.pos[v]!]! = c) :
    v ∈ (p.lab.extract c p.cen[c]!).toList := by
  have hposlt : p.pos[v]! < n := hp.posLt v hv
  have hmem : p.cst[c]! ≤ p.pos[v]! ∧ p.pos[v]! < p.cen[c]! :=
    (hp.cst_eq_iff hc hposlt).1 (by rw [hcell, hcst])
  rw [hcst] at hmem
  have hlab : p.lab[p.pos[v]!]! = v := hp.labPos v hv
  have hidx : p.pos[v]! - c < (p.lab.extract c p.cen[c]!).size := by
    simp only [Array.size_extract, hp.labSize]; omega
  have hget : (p.lab.extract c p.cen[c]!)[p.pos[v]! - c]! = p.lab[c + (p.pos[v]! - c)]! := by
    rw [getElem!_pos (p.lab.extract c p.cen[c]!) (p.pos[v]! - c) hidx,
      getElem!_pos p.lab (c + (p.pos[v]! - c)) (by rw [hp.labSize]; omega)]
    exact Array.getElem_extract _
  rw [show c + (p.pos[v]! - c) = p.pos[v]! by omega, hlab] at hget
  have hm := getElemD_mem hidx
  rw [hget] at hm
  exact Array.mem_def.mp hm

/-! ## Which automorphisms a leaf update can add -/

theorem addAuto_mem {st : St} {g x : Array Nat} (h : x ∈ (st.addAuto g).autos) :
    x ∈ st.autos ∨ x = g := by
  rw [St.addAuto] at h
  repeat' split at h
  all_goals first
    | exact Or.inl h
    | simpa using h

theorem addAuto_P {P : Array Nat → Prop} {st : St} {a : Array Nat}
    (hst : ∀ g ∈ st.autos, P g) (ha : P a) : ∀ g ∈ (st.addAuto a).autos, P g := by
  intro g hg
  rcases addAuto_mem hg with h | h
  · exact hst g h
  · exact h ▸ ha

/-- Every automorphism a leaf update adds is `autoOf` against one of the recorded leaves. -/
theorem leafUpdate_autos {P : Array Nat → Prop} {G : Graph} {path : Array Nat}
    {invPath : Array UInt64} {lab : Array Nat} {st : St} (hst : ∀ g ∈ st.autos, P g)
    (hl : ∀ l, (st.first = some l ∨ st.best = some l) → lexCmpU64 (certOf G lab) l.cert = .eq →
      P (autoOf G.n lab l.lab)) :
    ∀ g ∈ (leafUpdate G path invPath lab st).autos, P g := by
  rw [leafUpdate]
  simp only [Id.run]
  repeat' split
  all_goals first
    | exact hst
    | exact addAuto_P hst (hl _ (Or.inl (by assumption)) (by simp_all))
    | exact addAuto_P hst (hl _ (Or.inr (by assumption)) (by simp_all))
    | exact addAuto_P (addAuto_P hst (hl _ (Or.inl (by assumption)) (by simp_all)))
        (hl _ (Or.inr (by simp only [addAuto_best] at *; assumption)) (by simp_all))

/-! ## Inverse automorphisms -/

theorem range_permArr (n : Nat) : PermArr n (Array.range n) := by
  refine ⟨by simp, fun i hi => ?_, fun i hi j hj h => ?_⟩
  · rw [getElem!_pos (Array.range n) i (by simpa using hi)]; simpa using hi
  · rw [getElem!_pos (Array.range n) i (by simpa using hi),
      getElem!_pos (Array.range n) j (by simpa using hj)] at h
    simpa using h

/-- The inverse of a permutation array, built with the same machinery as `autoOf`. -/
def invAuto (n : Nat) (g : Array Nat) : Array Nat := autoOf n g (Array.range n)

theorem invAuto_get {n : Nat} {g : Array Nat} (hg : PermArr n g) {i : Nat} (hi : i < n) :
    (invAuto n g)[g[i]!]! = i := by
  rw [invAuto, autoOf_get hg hi, getElem!_pos (Array.range n) i (by simpa using hi)]
  simp

theorem invAuto_isAuto {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g) :
    IsAutoArr n f (invAuto n g) := by
  refine ⟨autoOf_permArr hg.perm (range_permArr n), fun u hu v hv => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hg.perm.surj hu
  obtain ⟨b, hb, rfl⟩ := hg.perm.surj hv
  rw [invAuto_get hg.perm ha, invAuto_get hg.perm hb]
  exact (hg.adj a ha b hb).symm

/-! ## The leaves the search records are genuine tree leaves -/

/-- `l` really is a leaf of the search tree: its path individualises down to a discrete
partition, and its labelling and certificate are that partition's. -/
def LeafNode (n : Nat) (f : Nat → Nat → Bool) (l : Leaf) : Prop :=
  ∃ p, Node n f l.path l.invPath p ∧ p.targetCell n = none ∧ l.lab = p.lab ∧
    l.cert = certOf (Graph.ofOracle n f) p.lab

theorem LeafNode.permArr {n : Nat} {f : Nat → Nat → Bool} {l : Leaf} (h : LeafNode n f l) :
    PermArr n l.lab := by
  obtain ⟨p, hp, _, hlab, _⟩ := h
  rw [hlab]; exact hp.wf.lab_permArr

theorem LeafNode.cert_eq {n : Nat} {f : Nat → Nat → Bool} {l : Leaf} (h : LeafNode n f l) :
    l.cert = certOf (Graph.ofOracle n f) l.lab := by
  obtain ⟨p, _, _, hlab, hc⟩ := h
  rw [hc, hlab]

/-- Everything a state remembers is genuine: both recorded leaves, and every generator. -/
def StGood (n : Nat) (f : Nat → Nat → Bool) (st : St) : Prop :=
  (∀ l, st.best = some l → LeafNode n f l) ∧ (∀ l, st.first = some l → LeafNode n f l) ∧
    (∀ g ∈ st.autos, IsAutoArr n f g)

theorem unwind_autos (path : Array Nat) (st : St) : (unwind path st).autos = st.autos := by
  rw [unwind]
  split
  · split <;> rfl
  · rfl

theorem StGood.unwind {n : Nat} {f : Nat → Nat → Bool} {st : St} (h : StGood n f st)
    (path : Array Nat) : StGood n f (Canon.unwind path st) :=
  ⟨fun l hb => h.1 l ((unwind_best path st) ▸ hb),
   fun l hf => h.2.1 l ((unwind_first path st) ▸ hf),
   fun g hg => h.2.2 g ((unwind_autos path st) ▸ hg)⟩

theorem pruneNode_good {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') (hst : StGood n f st) : StGood n f st' := by
  rw [pruneNode] at h
  split at h
  · cases h; exact hst
  · split at h
    · exact absurd h (by simp)
    · cases h; exact ⟨by simp, hst.2.1, hst.2.2⟩
    · cases h; exact hst

theorem leafUpdate_good {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {lab : Array Nat} {st : St}
    (hl : LeafNode n f ⟨path, invPath, certOf (Graph.ofOracle n f) lab, lab⟩)
    (hst : StGood n f st) :
    StGood n f (leafUpdate (Graph.ofOracle n f) path invPath lab st) := by
  refine ⟨fun l hb => ?_, fun l hf => ?_, ?_⟩
  · rcases leafUpdate_best (Graph.ofOracle n f) path invPath lab st with h | h
    · exact hst.1 l (h ▸ hb)
    · rw [h] at hb; cases hb; exact hl
  · rcases leafUpdate_first (Graph.ofOracle n f) path invPath lab st with h | h
    · exact hst.2.1 l (h ▸ hf)
    · rw [h] at hf; cases hf; exact hl
  · refine leafUpdate_autos hst.2.2 (fun l hlm hcert => ?_)
    have hln : LeafNode n f l := hlm.elim (hst.2.1 l) (hst.1 l)
    refine autoOf_isAuto hl.permArr hln.permArr ?_
    rw [← hln.cert_eq]
    exact lexCmpU64_eq_iff.1 hcert

/-- **Everything the search records is genuine.** -/
theorem dfsNode_good (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      Node n f path invPath p → StGood n f st →
        StGood n f (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      Node n f path invPath p → StGood n f st →
        StGood n f (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      Node n f path invPath p → (∀ v ∈ verts, Chld n p v) → StGood n f st →
        StGood n f (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => intro path invPath p st _ hst; rw [dfsNode]; exact hst
  case refine_2 =>
    intro path invPath p st fuel habort _ hst
    rw [dfsNode_abort habort]; exact hst
  case refine_3 =>
    intro path invPath p st fuel habort hprune _ hst
    rw [dfsNode_pruned (by simpa using habort) hprune]; exact hst
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc hnode hst
    rw [dfsNode_leaf (by simpa using habort) hprune htc]
    have hst1 : StGood n f st1 := pruneNode_good hprune hst
    exact leafUpdate_good ⟨p, hnode, htc, rfl, rfl⟩ hst1
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 s htc verts orb ih hnode hst
    rw [dfsNode_branch (by simpa using habort) hprune htc]
    have hp : Part.WF n p := hnode.wf
    have hst1 : StGood n f st1 := pruneNode_good hprune hst
    refine ih hnode (fun v hv => ⟨s, htc, mem_extract_lt hp hv, ?_⟩) hst1
    exact mem_extract_cell hp (targetCell_lt n p s htc) (targetCell_cst hp htc) hv
  case refine_6 =>
    intro fuel path invPath p processed orb st _ _ hst
    rw [dfsChildren_nil]; exact hst
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort _ _ hst
    rw [dfsChildren_abort habort]; exact hst
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hnode hverts hst
    rw [dfsChildren_marked (by simpa using habort) hmark]
    exact ih hnode (fun w hw => hverts w (List.mem_cons_of_mem _ hw)) hst
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 hnode hverts hst
    obtain ⟨c, htc, hv, hcell⟩ := hverts v (by simp)
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by
      rw [childInv, hchild]
    have hnode' : Node n f (path.push v) childInv' p'' := by
      have h := Node.step hnode htc hv hcell
      rw [hcinv] at h
      simpa only [hchild] using h
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    exact (ih1 hnode' hst).unwind path
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 hnode hverts hst
    obtain ⟨c, htc, hv, hcell⟩ := hverts v (by simp)
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by
      rw [childInv, hchild]
    have hnode' : Node n f (path.push v) childInv' p'' := by
      have h := Node.step hnode htc hv hcell
      rw [hcinv] at h
      simpa only [hchild] using h
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    exact ih2 hnode (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      ((ih1 hnode' hst).unwind path)

end Canon
end IsoGraph
