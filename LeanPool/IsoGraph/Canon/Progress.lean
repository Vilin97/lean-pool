/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Node
import LeanPool.IsoGraph.ForMathlib.Array

/-!
# Refinement splits cells, so the search terminates with a leaf in hand

The fuel of the search is `n + 1`, and `canonical` falls back on the identity labelling if the
search comes back empty-handed.  This file rules that out.

The measure is the number of cells, `numCells`.  Individualising a vertex of a non-singleton cell
creates a new cell start, and refinement never *merges* cells — that is `Refines`, proved by
following the cell starts through `splitCell`, `splitCellsFrom`, `refineStep` and `refineLoop`.
So each level of the tree has at least one more cell than its parent (`numCells_child`), the tree
has depth at most `n`, and the fuel is enough (`dfsNode_best`).  The other thing needed is that
the *first* child of a node is never orbit-pruned, which holds because the orbit mark starts out
empty and is only refreshed when an automorphism has been found — which happens only at a leaf.
-/

namespace IsoGraph
namespace Canon

/-! ### Refinement only splits cells -/

/-- `q` refines `p`: every cell of `p` is a union of cells of `q`.  Since a cell is determined by
its start position (`Part.WF.cst_eq_iff`), this is the same as saying every cell start of `p` is
still a cell start of `q`. -/
def Refines (n : Nat) (q p : Part) : Prop := ∀ i, i < n → p.cst[i]! = i → q.cst[i]! = i

theorem Refines.refl {n : Nat} (p : Part) : Refines n p p := fun _ _ h => h

theorem Refines.trans {n : Nat} {p q r : Part} (h1 : Refines n q r) (h2 : Refines n p q) :
    Refines n p r := fun i hi h => h2 i hi (h1 i hi h)

/-- The cell being split keeps its start: the first fragment starts where the cell did. -/
theorem splitCell_cst_self {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hinv : SplitInv n cnt st) (hc : c < n) (hcst : st.cst[c]! = c) :
    (splitCell cnt c st).cst[c]! = c := by
  have hok := splitCell_spec hinv.wf hc hcst hinv.bcZero hinv.cntLt
  set p' := (splitCell cnt c st).part with hp'
  have hwf' : Part.WF n p' := hok.wf
  have hle : p'.cst[c]! ≤ c := hwf'.cstLe c hc
  change p'.cst[c]! = c
  by_contra hne
  set j := p'.cst[c]! with hj
  have hjc : j < c := by omega
  have hjn : j < n := by omega
  -- `j` is a cell start of `p'`, hence of `st.part`, since it lies left of the split cell
  have hjstart : p'.cst[j]! = j := by
    have := hwf'.cellCst c hc j (by rw [← hj]) (by have := hwf'.ltCen c hc; omega)
    rw [this, ← hj]
  have hjst : st.cst[j]! = j := by
    have h := hok.cst_ne j hjn (Or.inl hjc)
    rw [show st.part.cst[j]! = st.cst[j]! from rfl] at h
    rw [← h]; exact hjstart
  -- but then `c` would lie in `j`'s cell, contradicting `cst[c] = c`
  have hcen : st.cen[j]! ≤ c := by
    by_contra hcon
    have := hinv.wf.cellCst j hjn c (by rw [show st.part.cst[j]! = j from hjst]; omega) (by
      rw [show st.part.cen[j]! = st.cen[j]! from rfl]; omega)
    rw [show st.part.cst[j]! = j from hjst, show st.part.cst[c]! = c from hcst] at this
    omega
  have hcen' : p'.cen[j]! = st.cen[j]! := by
    have h := hok.cen_ne j hjn (Or.inl hjc)
    rw [show st.part.cen[j]! = st.cen[j]! from rfl] at h
    exact h
  have h2 := hwf'.cellCen c hc j (by rw [← hj]) (by have := hwf'.ltCen c hc; omega)
  have h3 := hwf'.ltCen c hc
  omega

/-- Splitting one cell leaves every cell start in place. -/
theorem splitCell_refines {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hinv : SplitInv n cnt st) (hc : c < n) (hcst : st.cst[c]! = c) :
    Refines n (splitCell cnt c st).part st.part := by
  intro i hi hstart
  by_cases hic : i = c
  · subst hic; exact splitCell_cst_self hinv hc hcst
  · exact splitCell_start hinv hc hcst hi hic hstart

theorem splitCellsFrom_refines {n : Nat} {cnt cells : Array Nat} (hnd : cells.toList.Nodup) :
    ∀ (fuel j : Nat) (st : SplitState), SplitInv n cnt st →
      (∀ j', j ≤ j' → j' < cells.size → cells[j']! < n ∧ st.cst[cells[j']!]! = cells[j']!) →
      Refines n (splitCellsFrom cnt cells fuel j st).part st.part
  | 0, _, st, _, _ => Refines.refl _
  | fuel + 1, j, st, hinv, hst => by
    rw [splitCellsFrom]
    split
    · exact Refines.refl _
    · rename_i hj
      have hjs : j < cells.size := by omega
      have h1 := (hst j (by omega) hjs).1
      have h2 := (hst j (by omega) hjs).2
      refine Refines.trans (splitCell_refines hinv h1 h2)
        (splitCellsFrom_refines hnd fuel (j + 1) _ (splitCell_inv hinv h1 h2) fun j' ha hb => ?_)
      exact ⟨(hst j' (by omega) hb).1, splitCell_start hinv h1 h2 (hst j' (by omega) hb).1
        (nodup_getElemD_ne hnd hb hjs (by omega)) (hst j' (by omega) hb).2⟩

theorem refineStep_refines {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p) {s : Nat}
    (hs : s < n) (hcst : p.cst[s]! = s) (inW : Array Bool) (tr : UInt64) :
    Refines n (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).1 p := by
  obtain ⟨cnt, touched, hc⟩ : ∃ cnt touched, countFrom (Graph.ofOracle n f) p.lab p.cen[s]!
      (p.cen[s]! - s) s (Scratch.empty n).cnt #[] = (cnt, touched) := ⟨_, _, rfl⟩
  have hc' : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cnt, touched) := hc
  by_cases hemp : touched.isEmpty = true
  · rw [refineStep_eq_empty hc hemp]; exact Refines.refl _
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
    have := splitCellsFrom_refines (n := n) hnd (sortNats collected).size 0 _ hinv0 hstart
    rw [hst] at this
    rw [refineStep_eq hc hemp hcl hst]
    exact this

theorem refineLoop_refines {n : Nat} {f : Nat → Nat → Bool} :
    ∀ (fuel : Nat) (p : Part) (inW : Array Bool) (tr : UInt64), Part.WF n p →
      Refines n (refineLoop (Graph.ofOracle n f) fuel p inW tr (Scratch.empty n)).1 p
  | 0, _, _, _, _ => Refines.refl _
  | fuel + 1, p, inW, tr, hp => by
    cases hfs : firstSet inW with
    | none => rw [refineLoop_none hfs]; exact Refines.refl _
    | some s =>
      by_cases hg : s < n ∧ p.cst[s]! = s
      · obtain ⟨hsn, hcs⟩ := hg
        obtain ⟨p1, i1, t1, sc1, hstep⟩ : ∃ p1 i1 t1 sc1, refineStep (Graph.ofOracle n f) p
          (inW.set! s false) s tr (Scratch.empty n) = (p1, i1, t1, sc1) := ⟨_, _, _, _, rfl⟩
        have hwf := refineStep_wf (f := f) hp hsn hcs (inW.set! s false) tr
        have href := refineStep_refines (f := f) hp hsn hcs (inW.set! s false) tr
        rw [hstep] at hwf href
        rw [refineLoop_step hfs (by simp [hcs, hsn]) hstep, show sc1 = Scratch.empty n from hwf.2]
        exact Refines.trans href (refineLoop_refines fuel p1 i1 t1 hwf.1)
      · by_cases hsn : s < n
        · have hcs : ¬(p.cst[s]! = s) := fun h => hg ⟨hsn, h⟩
          rw [refineLoop_skip hfs (by simp [hcs])]
          exact refineLoop_refines fuel p (inW.set! s false) tr hp
        · rw [refineLoop_skip hfs (by simp [hsn])]
          exact refineLoop_refines fuel p (inW.set! s false) tr hp

theorem refine_refines {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p)
    (inW : Array Bool) (tr : UInt64) :
    Refines n (refine (Graph.ofOracle n f) p inW tr).1 p := by
  rw [refine]; exact refineLoop_refines _ p inW tr hp

/-! ### Individualisation creates a cell, refinement keeps it -/

theorem cenTargetFrom_big {n : Nat} {c : Array Nat} :
    ∀ (fuel i j : Nat), cenTargetFrom c n fuel i = some j → c[j]! - j > 1
  | 0, _, _, h => by simp [cenTargetFrom] at h
  | fuel + 1, i, j, h => by
    rw [cenTargetFrom] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · rename_i hbig; cases h; exact hbig
      · exact cenTargetFrom_big fuel c[i]! j h

/-- The target cell has at least two vertices. -/
theorem targetCell_big {n : Nat} {p : Part} {c : Nat} (h : p.targetCell n = some c) :
    p.cen[c]! - c > 1 :=
  cenTargetFrom_big n 0 c h

theorem individualize_refines {n : Nat} {p : Part} {v : Nat} (hp : Part.WF n p) (hv : v < n) :
    Refines n (individualize p v).1 p := by
  have hd : IndivData n p v p.pos[v]! p.cst[p.pos[v]!]! p.cen[p.pos[v]!]! p.lab[p.cst[p.pos[v]!]!]!
    := ⟨hv, rfl, rfl, rfl, rfl⟩
  intro i hi hstart
  rw [individualize_cst_getElemD hp hd]
  split
  · rename_i hmem
    have := hd.cst_eq hp (by omega) hmem.2
    omega
  · exact hstart

/-- Individualising `v` makes `c + 1` a cell start, where `c` is the start of `v`'s cell. -/
theorem individualize_new_start {n : Nat} {p : Part} {v : Nat} (hp : Part.WF n p) (hv : v < n)
    (hbig : p.cst[p.pos[v]!]! + 1 < p.cen[p.pos[v]!]!) :
    (individualize p v).1.cst[p.cst[p.pos[v]!]! + 1]! = p.cst[p.pos[v]!]! + 1 := by
  have hd : IndivData n p v p.pos[v]! p.cst[p.pos[v]!]! p.cen[p.pos[v]!]! p.lab[p.cst[p.pos[v]!]!]!
    := ⟨hv, rfl, rfl, rfl, rfl⟩
  rw [individualize_cst_getElemD hp hd, ite_eq_left ⟨Nat.le_refl _, hbig⟩]

theorem child_refines {n : Nat} {f : Nat → Nat → Bool} {p : Part} {v : Nat} (hp : Part.WF n p)
    (hv : v < n) : Refines n (child (Graph.ofOracle n f) p v).1 p := by
  rw [child]
  exact Refines.trans (individualize_refines hp hv)
    (refine_refines (individualize_wf' hp hv) _ _)

/-! ### The number of cells, and why the search terminates in `n` levels -/

/-- The number of cells of `p` inside `{0, …, n-1}`. -/
def numCells (n : Nat) (p : Part) : Nat :=
  ((Finset.range n).filter (fun i => p.cst[i]! = i)).card

theorem numCells_le {n : Nat} (p : Part) : numCells n p ≤ n := by
  rw [numCells]
  exact (Finset.card_filter_le (Finset.range n) (fun i => p.cst[i]! = i)).trans_eq
    (Finset.card_range n)

theorem numCells_mono {n : Nat} {p q : Part} (h : Refines n q p) : numCells n p ≤ numCells n q := by
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, h i hi.1 hi.2⟩

theorem numCells_lt {n : Nat} {p q : Part} (h : Refines n q p) {i0 : Nat} (hi0 : i0 < n)
    (h1 : q.cst[i0]! = i0) (h2 : p.cst[i0]! ≠ i0) : numCells n p < numCells n q := by
  refine Finset.card_lt_card ⟨fun i hi => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨hi.1, h i hi.1 hi.2⟩
  · have := hsub (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hi0, h1⟩)
    simp only [Finset.mem_filter, Finset.mem_range] at this
    exact h2 this.2

/-- **Each level of the search splits a cell.**  This is what bounds the depth of the tree by `n`
and makes the fuel `n + 1` enough to reach a leaf. -/
theorem numCells_child {n : Nat} {f : Nat → Nat → Bool} {p : Part} {c v : Nat} (hp : Part.WF n p)
    (htc : p.targetCell n = some c) (hv : v < n) (hcell : p.cst[p.pos[v]!]! = c) :
    numCells n p < numCells n (child (Graph.ofOracle n f) p v).1 := by
  have hc : c < n := targetCell_lt n p c htc
  have hcst : p.cst[c]! = c := targetCell_cst hp htc
  have hbig : p.cen[c]! - c > 1 := targetCell_big htc
  have hi : p.pos[v]! < n := hp.posLt v hv
  have hcn : p.cen[c]! ≤ n := hp.cenLe c hc
  have hcen : p.cen[p.pos[v]!]! = p.cen[c]! := by
    refine hp.cellCen c hc p.pos[v]! ?_ ?_
    · rw [hcst]
      exact hcell ▸ hp.cstLe p.pos[v]! hi
    · exact ((hp.cst_eq_iff hc hi).1 (by rw [hcell, hcst])).2
  have hbig' : p.cst[p.pos[v]!]! + 1 < p.cen[p.pos[v]!]! := by rw [hcell, hcen]; omega
  refine numCells_lt (child_refines (f := f) hp hv) (i0 := c + 1) (by omega) ?_ ?_
  · rw [child]
    refine refine_refines (individualize_wf' hp hv) _ _ (c + 1) (by omega) ?_
    have := individualize_new_start hp hv hbig'
    rwa [hcell] at this
  · have hd : IndivData n p v p.pos[v]! c p.cen[p.pos[v]!]! p.lab[c]! := ⟨hv, rfl, hcell, rfl, rfl⟩
    rw [hd.cst_eq hp (by omega) (by omega)]
    omega

/-! ### The search always finishes with a leaf in hand -/

theorem pruneNode_abortTo {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') : st'.abortTo = st.abortTo := by
  rw [pruneNode] at h
  split at h
  · cases h; rfl
  · split at h
    · exact absurd h (by simp)
    · cases h; rfl
    · cases h; rfl

theorem pruneNode_none_best {invPath : Array UInt64} {st : St}
    (h : pruneNode invPath st = none) : st.best.isSome = true := by
  rw [pruneNode] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb; rw [hb]; rfl

theorem leafUpdate_best_isSome (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) : (leafUpdate G path invPath lab st).best.isSome = true := by
  rcases hb : st.best with _ | b
  · rw [leafUpdate]
    simp only [Id.run]
    repeat' split
    all_goals first | rfl | simp_all [addAuto_best]
  · rcases leafUpdate_best G path invPath lab st with h | h <;> rw [h] <;> simp [hb]

theorem orbRefresh_eq {G : Graph} {path processed : Array Nat} {orb : Orbits} {st : St}
    (h : orb.nGens = st.autos.size) : orbRefresh G path processed orb st = orb := by
  have hor : orbRefresh G path processed orb st
      = if orb.nGens == st.autos.size then orb
        else { nGens := st.autos.size, gens := usableAutos st.autos path,
               mark := orbitClosure G.n (usableAutos st.autos path) processed } := rfl
  rw [hor, ite_eq_left (by simp [h])]

/-- **The search always ends holding a leaf.**  The fuel `n + 1` is enough because every level of
the tree splits a cell, so a node at depth `d` has at least `d + 1` cells and the tree has depth at
most `n - 1`; and the first child of a node is never orbit-pruned, so the descent always reaches a
leaf, which `leafUpdate` stores. -/
theorem dfsNode_best (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      Part.WF n p → n + 1 ≤ numCells n p + fuel →
      (st.abortTo.isSome = true → st.best.isSome = true) →
        (dfsNode (Graph.ofOracle n f) fuel path invPath p st).best.isSome = true := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      Part.WF n p → n + 1 ≤ numCells n p + fuel →
      (st.abortTo.isSome = true → st.best.isSome = true) →
        (dfsNode (Graph.ofOracle n f) fuel path invPath p st).best.isSome = true)
    (motive2 := fun fuel path invPath p verts processed orb st =>
      Part.WF n p → (∀ v ∈ verts, v < n) →
      (∀ v ∈ verts, numCells n p < numCells n (child (Graph.ofOracle n f) p v).1) →
      n ≤ numCells n p + fuel →
      (st.abortTo.isSome = true → st.best.isSome = true) →
      (st.best.isSome = true ∨
        (verts ≠ [] ∧ orb.nGens = st.autos.size ∧ ∀ w : Nat, orb.mark[w]! = false)) →
        (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st).best.isSome
          = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    intro path invPath p st _ hfuel _
    have := numCells_le (n := n) p
    omega
  case refine_2 =>
    intro path invPath p st fuel habort _ _ hgood
    rw [dfsNode_abort habort]; exact hgood habort
  case refine_3 =>
    intro path invPath p st fuel habort hprune _ _ _
    rw [dfsNode_pruned (by simpa using habort) hprune]
    exact pruneNode_none_best hprune
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc _ _ _
    rw [dfsNode_leaf (by simpa using habort) hprune htc]
    exact leafUpdate_best_isSome _ _ _ _ _
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 c htc verts orb ih hp hfuel hgood
    have hc : c < n := targetCell_lt n p c htc
    have hbig : p.cen[c]! - c > 1 := targetCell_big htc
    have hcn : p.cen[c]! ≤ n := hp.cenLe c hc
    rw [dfsNode_branch (by simpa using habort) hprune htc]
    have hgood2 : st2.abortTo.isSome = true → st2.best.isSome = true := by
      intro h
      rw [show st2.abortTo = st1.abortTo from rfl, pruneNode_abortTo hprune] at h
      exact absurd h (by simp [habort])
    refine ih hp (fun v hv => mem_extract_lt hp hv)
      (fun v hv => numCells_child hp htc (mem_extract_lt hp hv)
        (mem_extract_cell hp hc (targetCell_cst hp htc) hv)) (by omega) hgood2
      (Or.inr ⟨?_, rfl, ?_⟩)
    · intro hnil
      have hsz : 0 < (p.lab.extract c p.cen[c]!).toList.length := by
        rw [Array.length_toList, Array.size_extract, hp.labSize]; omega
      rw [show (p.lab.extract c p.cen[c]!).toList = verts from rfl, hnil] at hsz
      simp at hsz
    · intro w; exact replicate_getElemD_false
  case refine_6 =>
    intro fuel path invPath p processed orb st _ _ _ _ _ hb
    rw [dfsChildren_nil]
    rcases hb with h | h
    · exact h
    · exact absurd rfl h.1
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort _ _ _ _ hgood _
    rw [dfsChildren_abort habort]; exact hgood habort
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hp hverts hnc hfuel
      hgood hb
    rw [dfsChildren_marked (by simpa using habort) hmark]
    have hb' : st.best.isSome = true := by
      rcases hb with h | ⟨_, hng, hzero⟩
      · exact h
      · have hmark' : (orbRefresh (Graph.ofOracle n f) path processed orb st).mark[v]! = true :=
          hmark
        rw [orbRefresh_eq hng, hzero v] at hmark'
        exact absurd hmark' (by simp)
    exact ih hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hnc w (List.mem_cons_of_mem _ hw)) hfuel hgood (Or.inl hb')
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 hp hverts hnc hfuel hgood _
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hnc' : numCells n p < numCells n p'' := by
      have := hnc v (by simp)
      rwa [hchild] at this
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    rw [unwind_best]
    exact ih1 hwf'' (by omega) hgood
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 hp hverts hnc hfuel hgood _
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hnc' : numCells n p < numCells n p'' := by
      have := hnc v (by simp)
      rwa [hchild] at this
    have hbest : st2.best.isSome = true := by
      rw [show st2 = unwind path st1 from rfl, unwind_best]
      exact ih1 hwf'' (by omega) hgood
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    exact ih2 hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hnc w (List.mem_cons_of_mem _ hw)) hfuel
      (fun _ => hbest) (Or.inl hbest)

/-- **The search always returns a genuine leaf**: `canonical` never falls back on the identity
labelling. -/
theorem canonSt_best_isSome (n : Nat) (f : Nat → Nat → Bool) :
    (canonSt n f).best.isSome = true :=
  dfsNode_best n f (n + 1) #[] (rootInv n f) (rootPart n f) _ (initialRefine_wf f) (by omega)
    (by simp)

theorem canonical_cert_leaf (n : Nat) (f : Nat → Nat → Bool) :
    ∃ b : Leaf, (canonSt n f).best = some b ∧ (canonical (Graph.ofOracle n f)).cert = b.cert
      ∧ Leafkey n f (leafKey b.invPath b.cert) := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (canonSt_best_isSome n f)
  exact ⟨b, hb, (canonical_cert_leafkey n f b hb).1, (canonical_cert_leafkey n f b hb).2⟩

end Canon
end IsoGraph
