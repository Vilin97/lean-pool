/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Branch
import LeanPool.IsoGraph.Canon.Orbits

/-!
# The search misses nothing

`dfsNode_dom`: every leaf of the *whole* tree that the search skipped was skipped for a reason,
so the leaf it finally holds is the best one.

The obstacle is that `pruneNode` may *clear* the incumbent (`st.best := none`) when the node's
invariant path already beats it.  So "dominated by the incumbent" is not preserved into a recursive
call, and cannot be the invariant.  The fix is to carry an extra predicate `D` — "already accounted
for by whoever called us" — and prove everything relative to

* `DomD D st k` — `k` is dominated by `st`'s incumbent, *or* `D k`.

`D` is quantified *inside* the induction motive, so each recursive call may be made at a shifted
predicate `DomD D st`; `Guar`'s `BestMono st0 st` component is exactly what lets the shift be
collapsed again on the way out (`DomD.shift`).

The other pieces:

* `Dchild` — every leaf below a given child of the current node is accounted for.  `dchild_gen`
  says this set is closed under automorphisms fixing the path, which is what makes orbit pruning
  sound.
* `Guar` — what a returning call promises: it never asks to jump above the node it was called at,
  every leaf below the depth it vouches for is accounted for, and it kept the incumbent it was
  given.  `guar_stop` / `guar_go` are the two ways a child can come back.
* `stopDepth` measures how far down the returning state actually vouches for: the whole subtree if
  it returned normally, only the part above the backjump target if it asked to jump.
-/

namespace IsoGraph
namespace Canon

/-- Dominated by the incumbent, or already accounted for by whoever called us. -/
def DomD (D : List (List UInt64) → Prop) (st : St) (k : List (List UInt64)) : Prop :=
  Dom st k ∨ D k

theorem DomD.up {D : List (List UInt64) → Prop} {st st' : St} {k : List (List UInt64)}
    (h : DomD D st k) (hm : BestMono st st') : DomD D st' k :=
  h.elim (fun hd => Or.inl (hd.mono hm)) Or.inr

theorem DomD.shift {D : List (List UInt64) → Prop} {st st' : St} {k : List (List UInt64)}
    (h : DomD (DomD D st) st' k) (hm : BestMono st st') : DomD D st' k := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inl (h.mono hm)
  · exact Or.inr h

theorem DomD.of {D : List (List UInt64) → Prop} {st st' : St} {k : List (List UInt64)}
    (h : DomD D st k) : DomD (DomD D st) st' k := Or.inr h

/-- Every leaf below the child `w` is accounted for. -/
def Dchild (n : Nat) (f : Nat → Nat → Bool) (D : List (List UInt64) → Prop)
    (invPath : Array UInt64) (p : Part) (st : St) (w : Nat) : Prop :=
  w < n ∧ ∀ k, SubR n f invPath p w k → DomD D st k

theorem Dchild.up {n : Nat} {f : Nat → Nat → Bool} {D : List (List UInt64) → Prop}
    {invPath : Array UInt64} {p : Part} {st st' : St} {w : Nat}
    (h : Dchild n f D invPath p st w) (hm : BestMono st st') : Dchild n f D invPath p st' w :=
  ⟨h.1, fun k hk => (h.2 k hk).up hm⟩

/-- **Orbit pruning is sound.**  A generator fixing the path maps accounted-for children to
accounted-for children, because it carries the subtree below `g w` onto the subtree below `w`. -/
theorem dchild_gen {n : Nat} {f : Nat → Nat → Bool} {D : List (List UInt64) → Prop}
    {path : Array Nat} {invPath : Array UInt64} {p : Part} {st : St}
    (hnode : Node n f path invPath p) {g : Array Nat} (hg : IsAutoArr n f g)
    (hfix : ∀ i, i < path.size → g[path[i]!]! = path[i]!) (w : Nat)
    (h : Dchild n f D invPath p st w) : Dchild n f D invPath p st g[w]! :=
  ⟨hg.perm.lt w h.1, fun k hk =>
    h.2 k (subR_inv hg hnode.wf (hnode.auto_partEquiv hg hfix) h.1 hk)⟩

/-! ## Small facts about `unwind` -/

theorem unwind_abort {path : Array Nat} {st : St} (h : (unwind path st).abortTo.isSome = true) :
    unwind path st = st ∧ ∃ j, st.abortTo = some j ∧ j < path.size := by
  rcases hst : st.abortTo with _ | j
  · rw [show unwind path st = st from by simp only [unwind, hst], hst] at h; simp at h
  · by_cases hj : path.size ≤ j
    · rw [show unwind path st = { st with abortTo := none } from by
        simp only [unwind, hst, ite_eq_left hj]] at h
      simp at h
    · exact ⟨by simp only [unwind, hst, ite_eq_right hj], j, rfl, by omega⟩

theorem unwind_none {path : Array Nat} {st : St} (h : (unwind path st).abortTo.isSome = false) :
    (unwind path st).abortTo = none := by
  cases hh : (unwind path st).abortTo with
  | none => rfl
  | some j => rw [hh] at h; simp at h

theorem unwind_stop {path : Array Nat} {st : St}
    (h : (unwind path st).abortTo.isSome = false)
    (hb : ∀ j, st.abortTo = some j → j < path.size + 1) :
    stopDepth (path.size + 1) st.abortTo = path.size + 1 := by
  rcases hst : st.abortTo with _ | j
  · rfl
  · have hj : path.size ≤ j := by
      by_contra hlt
      rw [show unwind path st = st from by simp only [unwind, hst, ite_eq_right hlt], hst] at h
      simp at h
    have := hb j hst
    simp only [stopDepth]
    omega

/-! ## Small facts about the state -/

theorem pruneNode_rec {invPath : Array UInt64} {st st' : St} {l : Leaf}
    (h : pruneNode invPath st = some st') (hl : Rec st' l) : Rec st l := by
  rcases pruneNode_mono' h with rfl | ⟨rfl, _⟩
  · exact hl
  · rcases hl with hl | hl
    · simp at hl
    · exact Or.inr hl

theorem unwind_rec {path : Array Nat} {st : St} {l : Leaf} (hl : Rec (unwind path st) l) :
    Rec st l := by
  rcases hl with hl | hl
  · exact Or.inl ((unwind_best path st) ▸ hl)
  · exact Or.inr ((unwind_first path st) ▸ hl)

theorem rec_iff_stq {st : St} {P : Array Nat → Prop} :
    StQ P st ↔ ∀ l, Rec st l → P l.path :=
  ⟨fun h l hl => hl.elim (h.1 l) (h.2 l), fun h => ⟨fun l hl => h l (Or.inl hl),
    fun l hl => h l (Or.inr hl)⟩⟩

theorem reach_leaf_key {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    (htc : p.targetCell n = none) {k : List (List UInt64)} (h : Reach n f invPath p k) :
    k = leafKey invPath (certOf (Graph.ofOracle n f) p.lab) := by
  cases h with
  | leaf htc' => rfl
  | step hc _ _ _ => rw [htc] at hc; exact absurd hc (by simp)

/-! ## The orbit cache -/

theorem orbRefresh_markP {n : Nat} {f : Nat → Nat → Bool} {P : Nat → Prop}
    {path processed : Array Nat} {orb : Orbits} {st : St}
    (hgen : ∀ g ∈ usableAutos st.autos path, ∀ w, P w → P g[w]!)
    (hseed : ∀ w ∈ processed, P w) (hm : MarkP P orb.mark) :
    MarkP P (orbRefresh (Graph.ofOracle n f) path processed orb st).mark := by
  simp only [orbRefresh]
  split
  · exact hm
  · exact orbitClosure_P hgen hseed

theorem orbRefresh_gens {n : Nat} {f : Nat → Nat → Bool} {path processed : Array Nat}
    {orb : Orbits} {st : St}
    (horb : ∀ g ∈ orb.gens, IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]!)
    (hst : StGood n f st) :
    ∀ g ∈ (orbRefresh (Graph.ofOracle n f) path processed orb st).gens,
      IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]! := by
  simp only [orbRefresh]
  split
  · exact horb
  · intro g hg
    obtain ⟨h1, h2⟩ := mem_usableAutos hg
    exact ⟨hst.2.2 g h1, h2⟩

theorem Dchild.self_of {n : Nat} {f : Nat → Nat → Bool} {D : List (List UInt64) → Prop}
    {invPath : Array UInt64} {p : Part} {st : St} {w : Nat}
    (h : Dchild n f D invPath p st w) : Dchild n f (DomD D st) invPath p st w :=
  ⟨h.1, fun k hk => (h.2 k hk).of⟩

/-- What a returning call guarantees: it never asks to jump above the node it was called at, and
every leaf below the depth it vouches for is accounted for.  `st0` is the state it started from,
whose incumbent it never loses. -/
def Guar (n : Nat) (f : Nat → Nat → Bool) (D : List (List UInt64) → Prop) (path : Array Nat)
    (st0 st : St) : Prop :=
  (∀ j, st.abortTo = some j → j < path.size) ∧
    (∀ k, ancReach n f path (stopDepth path.size st.abortTo) k → DomD D st k) ∧
    BestMono st0 st

/-- A child that came back asking to jump above us: the request passes through unchanged. -/
theorem guar_stop {n : Nat} {f : Nat → Nat → Bool} {D : List (List UInt64) → Prop}
    {path : Array Nat} {v : Nat} {st0 st : St} (hg : Guar n f D (path.push v) st0 st)
    (h : (unwind path st).abortTo.isSome = true) : Guar n f D path st0 (unwind path st) := by
  obtain ⟨hb, hd, hm⟩ := hg
  obtain ⟨heq, j, hj, hjlt⟩ := unwind_abort h
  refine ⟨fun j' hj' => ?_, fun k hk => ?_, ?_⟩
  · rw [heq, hj] at hj'; cases hj'; exact hjlt
  · rw [heq, hj] at hk
    simp only [stopDepth, Nat.min_eq_left (show j + 1 ≤ path.size by omega)] at hk
    refine (hd k ?_).up (BestMono.of_best_eq (unwind_best path st))
    rw [hj]
    simp only [stopDepth, Array.size_push,
      Nat.min_eq_left (show j + 1 ≤ path.size + 1 by omega)]
    exact (ancReach_push path v (j + 1) (by omega) k).2 hk
  · rw [heq]; exact hm

/-- A child that came back normally: everything below it is accounted for. -/
theorem guar_go {n : Nat} {f : Nat → Nat → Bool} {D : List (List UInt64) → Prop}
    {path : Array Nat} {invPath : Array UInt64} {p : Part} {v : Nat} {st0 st : St}
    (hnode : Node n f path invPath p) (hv : v < n) (hg : Guar n f D (path.push v) st0 st)
    (h : (unwind path st).abortTo.isSome = false) :
    Dchild n f D invPath p (unwind path st) v ∧ (unwind path st).abortTo = none
      ∧ BestMono st0 (unwind path st) := by
  obtain ⟨hb, hd, hm⟩ := hg
  refine ⟨⟨hv, fun k hk => ?_⟩, unwind_none h, hm.trans (BestMono.of_best_eq (unwind_best path st))⟩
  refine (hd k ?_).up (BestMono.of_best_eq (unwind_best path st))
  have hst : stopDepth (path.push v).size st.abortTo = path.size + 1 := by
    rw [Array.size_push]
    exact unwind_stop h (fun j hj => by have := hb j hj; simpa using this)
  rw [hst]
  exact (ancReach_child hnode v k).2 hk

/-- **The search misses nothing.** -/
theorem dfsNode_dom (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St)
      (D : List (List UInt64) → Prop),
      Node n f path invPath p → n + 1 ≤ numCells n p + fuel → st.abortTo = none →
      StGood n f st → Pth st path → Jmp n f (DomD D st) path st →
        Guar n f D path st (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st => ∀ D : List (List UInt64) → Prop,
      Node n f path invPath p → n + 1 ≤ numCells n p + fuel → st.abortTo = none →
      StGood n f st → Pth st path → Jmp n f (DomD D st) path st →
        Guar n f D path st (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      ∀ D : List (List UInt64) → Prop,
      Node n f path invPath p → (∃ c, p.targetCell n = some c) → (∀ v ∈ verts, Chld n p v) →
      verts.Nodup → n ≤ numCells n p + fuel → st.abortTo = none → StGood n f st →
      (∀ l, Rec st l → ∀ w ∈ verts, ¬ PathPre (path.push w) l.path) →
      JmpC n f (DomD D st) path st →
      (∀ w, Chld n p w → w ∉ verts → Dchild n f D invPath p st w) →
      (∀ w ∈ processed, Dchild n f D invPath p st w) →
      MarkP (Dchild n f D invPath p st) orb.mark →
      (∀ g ∈ orb.gens, IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]!) →
        Guar n f D path st
          (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    intro path invPath p st D hnode hfuel _ _ _ _
    exact absurd hfuel (by have := numCells_le (n := n) p; omega)
  case refine_2 =>
    intro path invPath p st fuel habort D _ _ hnone _ _ _
    rw [hnone] at habort; simp at habort
  case refine_3 =>
    intro path invPath p st fuel habort hprune D hnode _ hnone _ _ _
    rw [dfsNode_pruned (by simpa using habort) hprune]
    refine ⟨fun j hj => absurd (hnone.symm.trans hj) (by simp), fun k hk => ?_, BestMono.rfl st⟩
    rw [hnone] at hk; simp only [stopDepth] at hk
    exact Or.inl (pruneNode_none hprune ((ancReach_full hnode k).1 hk)).dom
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc D hnode hfuel hnone hgood hpth hjmp
    have hmono : BestMono st (dfsNode (Graph.ofOracle n f) (fuel + 1) path invPath p st) :=
      dfsNode_mono n f (fuel + 1) path invPath p st hnode.wf hfuel
    rw [dfsNode_leaf (by simpa using habort) hprune htc] at hmono ⊢
    set st2 : St := { st1 with nodes := st1.nodes + 1 } with hst2
    have hrec2 : ∀ l, Rec st2 l → Rec st l := fun l hl => pruneNode_rec hprune hl
    have hgood1 : StGood n f st1 := pruneNode_good hprune hgood
    have hgood2 : StGood n f st2 := hgood1
    have hpth2 : Pth st2 path := fun l hl => hpth l (hrec2 l hl)
    have hjmp2 : Jmp n f (DomD D st) path st2 := fun l hl => hjmp l (hrec2 l hl)
    refine ⟨fun j hj => (leaf_abort_dom hnode hgood2 hpth2 hjmp2 hj).1, fun k hk => ?_, hmono⟩
    rcases hab : (leafUpdate (Graph.ofOracle n f) path invPath p.lab st2).abortTo with _ | j
    · rw [hab] at hk; simp only [stopDepth] at hk
      have hkk := reach_leaf_key htc ((ancReach_full hnode k).1 hk)
      exact Or.inl (hkk ▸ leafUpdate_dom_new (Graph.ofOracle n f) path invPath p.lab st2)
    · obtain ⟨hjlt, hdk⟩ := leaf_abort_dom hnode hgood2 hpth2 hjmp2 hab
      simp only [hab, stopDepth, Nat.min_eq_left (show j + 1 ≤ path.size by omega)] at hk
      exact (hdk k hk).up hmono
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 s htc verts orb ih D hnode hfuel hnone
      hgood hpth hjmp
    have hp : Part.WF n p := hnode.wf
    have hmono : BestMono st (dfsNode (Graph.ofOracle n f) (fuel + 1) path invPath p st) :=
      dfsNode_mono n f (fuel + 1) path invPath p st hp hfuel
    rw [dfsNode_branch (by simpa using habort) hprune htc] at hmono ⊢
    have hrec2 : ∀ l, Rec st2 l → Rec st l := fun l hl => pruneNode_rec hprune hl
    have hgood1 : StGood n f st1 := pruneNode_good hprune hgood
    have hgood2 : StGood n f st2 := hgood1
    have hpth2 : Pth st2 path := fun l hl => hpth l (hrec2 l hl)
    have hjmp2 : Jmp n f (DomD (DomD D st) st2) path st2 := by
      intro l hl j hj1 hj2 ht hne k hk
      exact (hjmp l (hrec2 l hl) j hj1 hj2 ht hne k hk).of
    have hC : ∀ w, Chld n p w → w ∉ verts → Dchild n f (DomD D st) invPath p st2 w := by
      intro w hw hnw; obtain ⟨c, hc, hwn, hcell⟩ := hw
      rw [(Option.some.inj (htc.symm.trans hc)).symm] at hcell
      exact absurd (mem_extract_cell' hp (targetCell_lt n p s htc) (targetCell_cst hp htc)
        hwn hcell) hnw
    have hF : ∀ g ∈ orb.gens,
        IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]! := by
      intro g hg; obtain ⟨hg1, hg2⟩ := mem_usableAutos hg
      exact ⟨hgood2.2.2 g hg1, hg2⟩
    obtain ⟨h1, h2, h3⟩ := ih (DomD D st) hnode ⟨s, htc⟩
      (fun w hw => ⟨s, htc, mem_extract_lt hp hw,
        mem_extract_cell hp (targetCell_lt n p s htc) (targetCell_cst hp htc) hw⟩)
      (extract_nodup hp s p.cen[s]!) (by omega)
      (by rw [pruneNode_abortTo hprune]; exact hnone) hgood2
      (fun l hl w _ hw => hpth2 l hl hw.of_push) (JmpC.of_jmp hjmp2 hpth2) hC (by simp)
      markP_replicate hF
    exact ⟨h1, fun k hk => (h2 k hk).shift hmono, hmono⟩
  case refine_6 =>
    intro fuel path invPath p processed orb st D hnode htcex _ _ _ hnone _ _ _ hloop _ _ _
    obtain ⟨c, htc⟩ := htcex; rw [dfsChildren_nil]
    refine ⟨fun j hj => absurd (hnone.symm.trans hj) (by simp), fun k hk => ?_, BestMono.rfl st⟩
    rw [hnone] at hk; simp only [stopDepth] at hk
    obtain ⟨w, hw, hsub⟩ := (reach_iff_subR htc k).1 ((ancReach_full hnode k).1 hk)
    exact (hloop w hw (by simp)).2 k hsub
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort D _ _ _ _ _ hnone _ _ _ _ _ _ _
    rw [hnone] at habort; simp at habort
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih D hnode htcex hverts
      hnodup hfuel hnone hgood hpthc hjmpc hloop hproc hmarkP hgens
    rw [dfsChildren_marked (by simpa using habort) hmark]
    have hgens1 : ∀ g ∈ orb1.gens,
        IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]! :=
      orbRefresh_gens hgens hgood
    have hmarkP1 : MarkP (Dchild n f D invPath p st) orb1.mark :=
      orbRefresh_markP (fun g hg w hw =>
        dchild_gen hnode (hgood.2.2 g (mem_usableAutos hg).1) (mem_usableAutos hg).2 w hw)
        hproc hmarkP
    refine ih D hnode htcex (fun w hw => hverts w (List.mem_cons_of_mem _ hw)) hnodup.of_cons
      hfuel hnone hgood (fun l hl w hw => hpthc l hl w (List.mem_cons_of_mem _ hw)) hjmpc
      ?_ hproc hmarkP1 hgens1
    intro w hw hnw; by_cases hwv : w = v
    · subst hwv; exact hmarkP1 w hmark
    · exact hloop w hw (by simp [hwv, hnw])
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 D hnode htcex hverts hnodup hfuel hnone hgood hpthc hjmpc
      hloop hproc hmarkP hgens
    obtain ⟨c, htc, hv, hcell⟩ := hverts v (by simp)
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by rw [childInv, hchild]
    have hnode' : Node n f (path.push v) childInv' p'' := by
      have h := Node.step hnode htc hv hcell
      rw [hcinv] at h; simpa only [hchild] using h
    have hnc : numCells n p < numCells n p'' := by
      have := numCells_child (n := n) (f := f) hnode.wf htc hv hcell
      rwa [hchild] at this
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    exact guar_stop (ih1 D hnode' (by omega) hnone hgood
      (fun l hl => hpthc l hl v (by simp)) (hjmpc.child v)) habort2
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 D hnode htcex hverts hnodup hfuel hnone
      hgood hpthc hjmpc hloop hproc hmarkP hgens
    obtain ⟨c, htc, hv, hcell⟩ := hverts v (by simp)
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by rw [childInv, hchild]
    have hnode' : Node n f (path.push v) childInv' p'' := by
      have h := Node.step hnode htc hv hcell
      rw [hcinv] at h; simpa only [hchild] using h
    have hnc : numCells n p < numCells n p'' := by
      have := numCells_child (n := n) (f := f) hnode.wf htc hv hcell
      rwa [hchild] at this
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    have hg1 := ih1 D hnode' (by omega) hnone hgood
      (fun l hl => hpthc l hl v (by simp)) (hjmpc.child v)
    obtain ⟨hdv, hab2, hm2⟩ := guar_go hnode hv hg1
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)
    set ST2 : St :=
      unwind path (dfsNode (Graph.ofOracle n f) fuel (path.push v) childInv' p'' st) with hST2
    have hvne : ∀ w ∈ vs, ¬ w = v := fun w hw he => (List.nodup_cons.1 hnodup).1 (he ▸ hw)
    have hgood2 : StGood n f ST2 :=
      (dfsNode_good n f fuel (path.push v) childInv' p'' st hnode' hgood).unwind path
    have hrec2 := rec_iff_stq.1 ((dfsNode_paths n f
        (fun Q => PathPre (path.push v) Q ∨ ∃ z, Rec st z ∧ z.path = Q)
        fuel (path.push v) childInv' p'' st (fun Q hQ => Or.inl hQ)
        (rec_iff_stq.2 (fun z hz => Or.inr ⟨z, hz, rfl⟩))).unwind path)
    have hgens1 : ∀ g ∈ orb1.gens,
        IsAutoArr n f g ∧ ∀ i, i < path.size → g[path[i]!]! = path[i]! :=
      orbRefresh_gens hgens hgood
    have hmarkP1 : MarkP (Dchild n f D invPath p st) orb1.mark :=
      orbRefresh_markP (fun g hg w hw =>
        dchild_gen hnode (hgood.2.2 g (mem_usableAutos hg).1) (mem_usableAutos hg).2 w hw)
        hproc hmarkP
    -- no recorded leaf lies below a child we have not tried yet
    have hA : ∀ l, Rec ST2 l → ∀ w ∈ vs, ¬ PathPre (path.push w) l.path := by
      intro l hl w hw hpre; rcases hrec2 l hl with hp1 | ⟨z, hz, hzp⟩
      · have e1 : l.path[path.size]! = v := (PathPre.push_iff.1 hp1).2.2
        have e2 : l.path[path.size]! = w := (PathPre.push_iff.1 hpre).2.2
        exact hvne w hw (e2.symm.trans e1)
      · exact hpthc z hz w (List.mem_cons_of_mem _ hw) (by rw [hzp]; exact hpre)
    -- the backjump invariant, now also covering the child we just finished
    have hB : JmpC n f (DomD (DomD D ST2) ST2) path ST2 := by
      intro l hl j hjle hjl htake hne k hk; rcases hrec2 l hl with hp1 | ⟨z, hz, hzp⟩
      · rcases Nat.lt_or_ge j path.size with hlt | hge
        · exact absurd ((PathPre.push_iff.1 hp1).1.2 j hlt) (hne hlt)
        · obtain rfl : j = path.size := by omega
          have hcong : (path.push v).toList.take (path.size + 1)
              = l.path.toList.take (path.size + 1) := by
            have := take_of_pathPre hp1
            simpa using this
          exact Or.inr (hdv.2 k ((ancReach_child hnode v k).1 ((ancReach_congr hcong k).2 hk)))
      · refine Or.inr ((hjmpc z hz j hjle (by rw [hzp]; exact hjl) (by rw [hzp]; exact htake)
          (by rw [hzp]; exact hne) k (by rw [hzp]; exact hk)).up hm2)
    -- children not yet tried
    have hC : ∀ w, Chld n p w → w ∉ vs → Dchild n f (DomD D ST2) invPath p ST2 w := by
      intro w hw hnw; by_cases hwv : w = v
      · subst hwv; exact hdv.self_of
      · exact ((hloop w hw (by simp [hwv, hnw])).up hm2).self_of
    -- children already tried
    have hE : ∀ w ∈ processed.push v, Dchild n f (DomD D ST2) invPath p ST2 w := by
      intro w hw; rcases Array.mem_push.1 hw with hw1 | rfl
      · exact ((hproc w hw1).up hm2).self_of
      · exact hdv.self_of
    -- the orbit cache
    have hF : MarkP (Dchild n f (DomD D ST2) invPath p ST2) orb2.mark := by
      refine closureLoop_P (fun g hg w hw =>
          dchild_gen hnode (hgens1 g hg).1 (hgens1 g hg).2 w hw) _ _ _
        (markP_set (fun w hw => ((hmarkP1 w hw).up hm2).self_of) hdv.self_of) (fun i hi => ?_)
      obtain rfl : i = 0 := by
        have h1 : (#[v] : Array Nat).size = 1 := rfl; omega
      simpa using hdv.self_of
    obtain ⟨h1, h2, h3⟩ := ih2 (DomD D ST2) hnode htcex
      (fun w hw => hverts w (List.mem_cons_of_mem _ hw)) hnodup.of_cons hfuel hab2 hgood2
      hA hB hC hE hF hgens1
    exact ⟨h1, fun k hk => (h2 k hk).shift h3, hm2.trans h3⟩

end Canon
end IsoGraph
