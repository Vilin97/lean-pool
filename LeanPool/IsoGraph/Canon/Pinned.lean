/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Paths

/-!
# Individualised vertices stay where they were put

Refinement rearranges vertices *inside* cells and never across them.  A vertex that has been
individualised sits alone in a cell, so from that moment on it never moves again: this file
follows a singleton cell through `splitCell`, `splitCellsFrom`, `refineStep`, `refineLoop`,
`refine`, `individualize` and `child`, exactly as `Progress.lean` follows cell starts.

The payoff is `Node.pin`.  Write `pinPos n f (path.take j)` for the start of the target cell of
the depth-`j` ancestor of a node — a position that depends on the first `j` individualised
vertices but not on the `j`-th.  Then at *every* descendant, position `pinPos n f (path.take j)`
holds the vertex individualised at depth `j`.  So two leaves whose paths agree up to depth `j`
park their depth-`j` choices at the *same* position, which is what makes the permutation relating
two equal-certificate leaves visibly map one branch onto the other.

Along the way `nodePath` makes a node an honest function of its path (`Node.det`).
-/

namespace IsoGraph
namespace Canon

/-- Position `c` is a singleton cell of `p`, and the vertex sitting there is `v`. -/
structure Pinned (n : Nat) (p : Part) (c v : Nat) : Prop where
  /-- The position is in range. -/
  lt : c < n
  /-- The cell starts here. -/
  cst : p.cst[c]! = c
  /-- …and ends immediately after. -/
  cen : p.cen[c]! = c + 1
  /-- The vertex parked here. -/
  lab : p.lab[c]! = v

theorem splitCell_pinned {n : Nat} {cnt : Array Nat} {c0 c v : Nat} {st : SplitState}
    (hinv : SplitInv n cnt st) (hc0 : c0 < n) (hcst0 : st.cst[c0]! = c0)
    (hpin : Pinned n st.part c v) : Pinned n (splitCell cnt c0 st).part c v := by
  have hok := splitCell_spec hinv.wf hc0 hcst0 hinv.bcZero hinv.cntLt
  set p' := (splitCell cnt c0 st).part with hp'
  by_cases hcc : c = c0
  · subst hcc
    -- the pinned position *is* the cell being split, and a singleton cell cannot split
    have hv : v < n := hpin.lab ▸ hinv.wf.labLt c hpin.lt
    have hposv : st.part.pos[v]! = c := by
      have h := hinv.wf.posLab c hpin.lt
      rwa [show st.part.lab[c]! = v from hpin.lab] at h
    have hmem := hok.pos_mem v hv (by rw [hposv]) (by
      rw [hposv, show st.part.cen[c]! = c + 1 from hpin.cen]; omega)
    rw [show st.part.cen[c]! = c + 1 from hpin.cen] at hmem
    have hpos' : p'.pos[v]! = c := by omega
    have hcst' : p'.cst[c]! = c := splitCell_cst_self hinv hc0 hcst0
    have hlab' : p'.lab[c]! = v := by
      have h := hok.wf.labPos v hv; rwa [hpos'] at h
    refine ⟨hpin.lt, hcst', ?_, hlab'⟩
    rcases Nat.lt_or_ge (c + 1) n with hn | hn
    · have h1 : st.part.cst[c + 1]! = c + 1 :=
        cst_succ hinv.wf (show st.part.cen[c]! = c + 1 from hpin.cen) hn
      have h2 : p'.cst[c + 1]! = c + 1 := by
        rw [hok.cst_ne (c + 1) hn (Or.inr (by rw [show st.part.cen[c]! = c + 1 from hpin.cen]))]
        exact h1
      by_contra hne
      have h3 : c < p'.cen[c]! := hok.wf.ltCen c hpin.lt
      have h4 := hok.wf.cellCst c hpin.lt (c + 1) (by omega) (by omega)
      omega
    · have h1 : p'.cen[c]! ≤ n := hok.wf.cenLe c hpin.lt
      have h2 : c < p'.cen[c]! := hok.wf.ltCen c hpin.lt
      omega
  · -- the pinned position lies outside the cell being split, so nothing there moves
    have hout : c < c0 ∨ st.cen[c0]! ≤ c := by
      by_contra hcon
      push Not at hcon
      have h := hinv.wf.cellCst c0 hc0 c (by rw [show st.part.cst[c0]! = c0 from hcst0]; omega)
        (by exact hcon.2)
      rw [show st.part.cst[c0]! = c0 from hcst0,
        show st.part.cst[c]! = c from hpin.cst] at h
      exact hcc h
    have hout' : c < c0 ∨ st.part.cen[c0]! ≤ c := hout
    exact ⟨hpin.lt, by rw [hok.cst_ne c hpin.lt hout']; exact hpin.cst,
      by rw [hok.cen_ne c hpin.lt hout']; exact hpin.cen,
      by rw [hok.lab_ne c hpin.lt hout']; exact hpin.lab⟩

theorem splitCellsFrom_pinned {n : Nat} {cnt cells : Array Nat} {c v : Nat}
    (hnd : cells.toList.Nodup) :
    ∀ (fuel j : Nat) (st : SplitState), SplitInv n cnt st →
      (∀ j', j ≤ j' → j' < cells.size → cells[j']! < n ∧ st.cst[cells[j']!]! = cells[j']!) →
      Pinned n st.part c v → Pinned n (splitCellsFrom cnt cells fuel j st).part c v
  | 0, _, _, _, _, hpin => hpin
  | fuel + 1, j, st, hinv, hst, hpin => by
    rw [splitCellsFrom]
    split
    · exact hpin
    · rename_i hj
      have hjs : j < cells.size := by omega
      have h1 := (hst j (by omega) hjs).1
      have h2 := (hst j (by omega) hjs).2
      refine splitCellsFrom_pinned hnd fuel (j + 1) _ (splitCell_inv hinv h1 h2)
        (fun j' ha hb => ⟨(hst j' (by omega) hb).1, splitCell_start hinv h1 h2
          (hst j' (by omega) hb).1 (nodup_getElemD_ne hnd hb hjs (by omega))
          (hst j' (by omega) hb).2⟩)
        (splitCell_pinned hinv h1 h2 hpin)

theorem refineStep_pinned {n : Nat} {f : Nat → Nat → Bool} {p : Part} {c v : Nat}
    (hp : Part.WF n p) {s : Nat} (hs : s < n) (hcst : p.cst[s]! = s) (inW : Array Bool)
    (tr : UInt64) (hpin : Pinned n p c v) :
    Pinned n (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).1 c v := by
  obtain ⟨cnt, touched, hc⟩ : ∃ cnt touched, countFrom (Graph.ofOracle n f) p.lab p.cen[s]!
      (p.cen[s]! - s) s (Scratch.empty n).cnt #[] = (cnt, touched) := ⟨_, _, rfl⟩
  have hc' : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cnt, touched) := hc
  by_cases hemp : touched.isEmpty = true
  · rw [refineStep_eq_empty hc hemp]; exact hpin
  · obtain ⟨hit, collected, hcl⟩ : ∃ hit collected,
        collectFrom p.pos p.cst touched touched.size 0 (Scratch.empty n).hit #[]
          = (hit, collected) := ⟨_, _, rfl⟩
    have hcl' : collectFrom p.pos p.cst touched touched.size 0 (Array.replicate n false) #[]
        = (hit, collected) := hcl
    obtain ⟨st, hst⟩ : ∃ st, splitCellsFrom cnt (sortNats collected) (sortNats collected).size 0
        { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW := inW,
          tr := mixN tr s, bc := (Scratch.empty n).bc } = st := ⟨_, rfl⟩
    have htn : ∀ v ∈ touched, v < n := countFrom_touched_lt' f p s hc'
    obtain ⟨hcolnd, hcolstart⟩ := collect_start hp htn hcl'
    have hinv0 : SplitInv n cnt
        { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen,
          inW := inW, tr := mixN tr s, bc := (Scratch.empty n).bc } :=
      splitInv_init hp hs hcst hc' inW (mixN tr s)
    have hnd : (sortNats collected).toList.Nodup := (sortNats_perm collected).nodup_iff.2 hcolnd
    have hstart : ∀ j', 0 ≤ j' → j' < (sortNats collected).size →
        (sortNats collected)[j']! < n ∧ p.cst[(sortNats collected)[j']!]!
          = (sortNats collected)[j']! := by
      intro j' _ h2
      exact hcolstart _ (sortNats_mem.1 (getElemD_mem h2))
    have := splitCellsFrom_pinned (n := n) (c := c) (v := v) hnd (sortNats collected).size 0 _
      hinv0 hstart hpin
    rw [hst] at this
    rw [refineStep_eq hc hemp hcl hst]
    exact this

theorem refineLoop_pinned {n : Nat} {f : Nat → Nat → Bool} {c v : Nat} :
    ∀ (fuel : Nat) (p : Part) (inW : Array Bool) (tr : UInt64), Part.WF n p → Pinned n p c v →
      Pinned n (refineLoop (Graph.ofOracle n f) fuel p inW tr (Scratch.empty n)).1 c v
  | 0, _, _, _, _, hpin => hpin
  | fuel + 1, p, inW, tr, hp, hpin => by
    cases hfs : firstSet inW with
    | none => rw [refineLoop_none hfs]; exact hpin
    | some s =>
      by_cases hg : s < n ∧ p.cst[s]! = s
      · obtain ⟨hsn, hcs⟩ := hg
        obtain ⟨p1, i1, t1, sc1, hstep⟩ : ∃ p1 i1 t1 sc1, refineStep (Graph.ofOracle n f) p
          (inW.set! s false) s tr (Scratch.empty n) = (p1, i1, t1, sc1) := ⟨_, _, _, _, rfl⟩
        have hwf := refineStep_wf (f := f) hp hsn hcs (inW.set! s false) tr
        have hpin1 := refineStep_pinned (f := f) hp hsn hcs (inW.set! s false) tr hpin
        rw [hstep] at hwf hpin1
        rw [refineLoop_step hfs (by simp [hcs, hsn]) hstep, show sc1 = Scratch.empty n from hwf.2]
        exact refineLoop_pinned fuel p1 i1 t1 hwf.1 hpin1
      · by_cases hsn : s < n
        · have hcs : ¬(p.cst[s]! = s) := fun h => hg ⟨hsn, h⟩
          rw [refineLoop_skip hfs (by simp [hcs])]
          exact refineLoop_pinned fuel p (inW.set! s false) tr hp hpin
        · rw [refineLoop_skip hfs (by simp [hsn])]
          exact refineLoop_pinned fuel p (inW.set! s false) tr hp hpin

theorem refine_pinned {n : Nat} {f : Nat → Nat → Bool} {p : Part} {c v : Nat} (hp : Part.WF n p)
    (inW : Array Bool) (tr : UInt64) (hpin : Pinned n p c v) :
    Pinned n (refine (Graph.ofOracle n f) p inW tr).1 c v := by
  rw [refine]; exact refineLoop_pinned _ p inW tr hp hpin

/-! ## Individualisation pins the vertex it splits off -/

theorem individualize_pinned_new {n : Nat} {p : Part} {v : Nat} (hp : Part.WF n p) (hv : v < n) :
    Pinned n (individualize p v).1 (individualize p v).2 v := by
  have hd : IndivData n p v p.pos[v]! p.cst[p.pos[v]!]! p.cen[p.pos[v]!]! p.lab[p.cst[p.pos[v]!]!]!
    := ⟨hv, rfl, rfl, rfl, rfl⟩
  rw [individualize_snd]
  refine ⟨hd.cLt hp, ?_, ?_, ?_⟩
  · rw [individualize_cst_getElemD hp hd, ite_eq_right (by omega)]; exact hd.cstc hp
  · rw [individualize_cen_getElemD hp hd, ite_eq_left rfl]
  · rw [individualize_lab_getElemD hp hd]
    split
    · rename_i hci
      rw [hci, hp.labPos v hv]
    · rw [ite_eq_left rfl]

theorem individualize_pinned {n : Nat} {p : Part} {v c v' : Nat} (hp : Part.WF n p) (hv : v < n)
    (hpin : Pinned n p c v') : Pinned n (individualize p v).1 c v' := by
  have hd : IndivData n p v p.pos[v]! p.cst[p.pos[v]!]! p.cen[p.pos[v]!]! p.lab[p.cst[p.pos[v]!]!]!
    := ⟨hv, rfl, rfl, rfl, rfl⟩
  have hiLt := hd.iLt hp
  have hcLe := hd.cLe hp
  have hcLt := hd.cLt hp
  have hiEc := hd.iLtEc hp
  by_cases hvv : v = v'
  · -- the pinned vertex is the one being individualised: its cell is already a singleton
    subst hvv
    have hposv : p.pos[v]! = c := by rw [← hpin.lab]; exact hp.posLab c hpin.lt
    have hcc : p.cst[p.pos[v]!]! = c := by rw [hposv]; exact hpin.cst
    have hec : p.cen[p.pos[v]!]! = c + 1 := by rw [hposv]; exact hpin.cen
    refine ⟨hpin.lt, ?_, ?_, ?_⟩
    · rw [individualize_cst_getElemD hp hd, ite_eq_right (by rw [hcc, hec]; omega)]; exact hpin.cst
    · rw [individualize_cen_getElemD hp hd, ite_eq_left hcc.symm, hcc]
    · rw [individualize_lab_getElemD hp hd, ite_eq_left hposv.symm, hcc, hpin.lab]
  · -- a different vertex: the pinned singleton is untouched by the split
    have hine : p.pos[v]! ≠ c := by
      intro h
      exact hvv (by rw [← hp.labPos v hv, h, hpin.lab])
    have hcne : p.cst[p.pos[v]!]! ≠ c := by
      intro h
      have := (hp.cst_eq_iff hpin.lt hiLt).1 (by rw [h, hpin.cst])
      rw [hpin.cst, hpin.cen] at this
      omega
    refine ⟨hpin.lt, ?_, ?_, ?_⟩
    · rw [individualize_cst_getElemD hp hd]
      split
      · rename_i hmem
        exact absurd ((hd.cst_eq hp (by omega) hmem.2).symm.trans hpin.cst) hcne
      · exact hpin.cst
    · rw [individualize_cen_getElemD hp hd, ite_eq_right (fun h => hcne h.symm)]; exact hpin.cen
    · rw [individualize_lab_getElemD hp hd, ite_eq_right (fun h => hine h.symm),
        ite_eq_right (fun h => hcne h.symm)]
      exact hpin.lab

theorem child_pinned {n : Nat} {f : Nat → Nat → Bool} {p : Part} {v c v' : Nat} (hp : Part.WF n p)
    (hv : v < n) (hpin : Pinned n p c v') :
    Pinned n (child (Graph.ofOracle n f) p v).1 c v' := by
  rw [child]
  exact refine_pinned (individualize_wf' hp hv) _ _ (individualize_pinned hp hv hpin)

/-- **Individualising `v` pins it at the start of its cell, for good.**  Refinement never moves a
vertex out of its cell, and `{v}` is a cell, so every descendant of this child has `v` sitting at
position `cst[pos[v]]`. -/
theorem child_pinned_new {n : Nat} {f : Nat → Nat → Bool} {p : Part} {v : Nat} (hp : Part.WF n p)
    (hv : v < n) : Pinned n (child (Graph.ofOracle n f) p v).1 p.cst[p.pos[v]!]! v := by
  rw [child, ← individualize_snd p v]
  exact refine_pinned (individualize_wf' hp hv) _ _ (individualize_pinned_new hp hv)

/-! ## A node is a function of its path -/

/-- The node reached by individualising `path`, in order, from the root.  `Node` is the graph of
this function (`Node.nodePath_eq`); having it as an actual function is what lets two branches of
the search that share a path prefix be identified. -/
def nodePath (n : Nat) (f : Nat → Nat → Bool) (path : List Nat) : Array UInt64 × Part :=
  path.foldl (fun s v =>
    (childInv (Graph.ofOracle n f) s.1 s.2 v, (child (Graph.ofOracle n f) s.2 v).1))
    (rootInv n f, rootPart n f)

theorem nodePath_append (n : Nat) (f : Nat → Nat → Bool) (path : List Nat) (v : Nat) :
    nodePath n f (path ++ [v])
      = (childInv (Graph.ofOracle n f) (nodePath n f path).1 (nodePath n f path).2 v,
          (child (Graph.ofOracle n f) (nodePath n f path).2 v).1) := by
  rw [nodePath, List.foldl_append]; rfl

theorem Node.nodePath_eq {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) :
    nodePath n f path.toList = (invPath, p) := by
  induction h with
  | root => rfl
  | @step path invPath p c v _ _ _ _ ih =>
    rw [Array.toList_push, nodePath_append, ih]

/-- **Determinism.**  Two runs that individualise the same vertices in the same order sit at the
same node. -/
theorem Node.det {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath invPath' : Array UInt64}
    {p p' : Part} (h : Node n f path invPath p) (h' : Node n f path invPath' p') :
    invPath = invPath' ∧ p = p' := by
  have := h.nodePath_eq.symm.trans h'.nodePath_eq
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-! ## Every individualised vertex is pinned at a position fixed by the path prefix -/

/-- The position at which the depth-`j` individualisation is parked: the start of the target cell
of the depth-`j` ancestor.  It depends only on the first `j` entries of the path. -/
def pinPos (n : Nat) (f : Nat → Nat → Bool) (path : List Nat) : Nat :=
  ((nodePath n f path).2.targetCell n).getD 0

/-- **Individualised vertices stay put.**  At any node, the vertex individualised at depth `j` sits
at position `pinPos n f (path.take j)` — a position determined by the path *prefix*, not by the
vertex.  This is what makes two leaves comparable position by position. -/
theorem Node.pin {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} (h : Node n f path invPath p) :
    ∀ j, j < path.size → Pinned n p (pinPos n f (path.toList.take j)) path[j]! := by
  induction h with
  | root => intro j hj; simp at hj
  | @step path invPath p c v hnode hc hv hcell ih =>
    intro j hj
    rw [Array.size_push] at hj
    rcases Nat.lt_or_ge j path.size with h1 | h1
    · rw [Array.toList_push, List.take_append_of_le_length (by simpa using Nat.le_of_lt h1),
        push_getElemD_lt path v h1]
      exact child_pinned hnode.wf hv (ih j h1)
    · have hjp : j = path.size := by omega
      subst hjp
      rw [Array.toList_push, push_getElemD_eq,
        show (path.toList ++ [v]).take path.size = path.toList by simp]
      have hnp : (nodePath n f path.toList).2 = p := congrArg Prod.snd hnode.nodePath_eq
      have hpp : pinPos n f path.toList = c := by rw [pinPos, hnp, hc]; rfl
      rw [hpp, ← hcell]
      exact child_pinned_new hnode.wf hv

end Canon
end IsoGraph
