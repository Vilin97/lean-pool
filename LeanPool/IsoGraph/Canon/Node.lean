/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Autos
import LeanPool.IsoGraph.ForMathlib.Array

/-!
# Nodes of the search tree

`dfsNode` carries three arguments that are only meaningful together: the array `path` of the
vertices individualised so far, the invariant path `invPath`, and the current partition `p`.
`Node n f path invPath p` is the ghost relation saying that these three really do come from
individualising `path` from the root, in order.

It packages the facts that the recursion needs about a node it is sitting at:

* `Node.wf` — the partition is well-formed;
* `Node.path_lt` — the individualised vertices are vertices;
* `Node.reach` — a leaf below this node is a leaf of the whole tree (so a key found here is a
  legitimate candidate for the maximum);
* `Node.auto_partEquiv` — the partition is invariant under any automorphism fixing `path`
  pointwise, which is exactly the hypothesis `reach_child_auto` needs and exactly what
  `usableAutos` filters for.
-/

namespace IsoGraph
namespace Canon

/-! ### Nodes of the search tree -/

/-- `Node n f path invPath p` says that the search reaches the node `(invPath, p)` by
individualising the vertices of `path`, in order.  It is the ghost information that ties together
the three arguments `path`, `invPath` and `p` of `dfsNode`. -/
inductive Node (n : Nat) (f : Nat → Nat → Bool) : Array Nat → Array UInt64 → Part → Prop
  | root : Node n f #[] (rootInv n f) (rootPart n f)
  | step {path : Array Nat} {invPath : Array UInt64} {p : Part} {c v : Nat}
      (h : Node n f path invPath p) (hc : p.targetCell n = some c) (hv : v < n)
      (hcell : p.cst[p.pos[v]!]! = c) :
      Node n f (path.push v) (childInv (Graph.ofOracle n f) invPath p v)
        (child (Graph.ofOracle n f) p v).1

theorem Node.wf {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} (h : Node n f path invPath p) : Part.WF n p := by
  induction h with
  | root => exact initialRefine_wf f
  | @step path invPath p c v _ _ hv _ ih => exact child_wf ih hv

theorem Node.path_lt {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} (h : Node n f path invPath p) : ∀ i, i < path.size → path[i]! < n := by
  induction h with
  | root => intro i hi; simp at hi
  | @step path invPath p c v _ _ hv _ ih =>
    intro i hi
    rw [Array.size_push] at hi
    rcases Nat.lt_or_ge i path.size with h1 | h1
    · rw [push_getElemD_lt path v h1]; exact ih i h1
    · have hip : i = path.size := by omega
      subst hip
      rw [push_getElemD_eq]; exact hv

/-- Every leaf below a node of the tree is a leaf of the whole tree. -/
theorem Node.reach {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} (h : Node n f path invPath p) {k : List (List UInt64)}
    (hk : Reach n f invPath p k) : Leafkey n f k := by
  induction h with
  | root => exact hk
  | @step path invPath p c v _ hc hv hcell ih => exact ih (Reach.step hc hv hcell hk)

/-- **The partition at a node is invariant under any automorphism fixing its path.**  This is what
makes orbit pruning legitimate: `usableAutos` keeps exactly the automorphisms fixing `path`. -/
theorem Node.auto_partEquiv {n : Nat} {f : Nat → Nat → Bool} {path : Array Nat}
    {invPath : Array UInt64} {p : Part} (h : Node n f path invPath p) {g : Array Nat}
    (hg : IsAutoArr n f g) (hfix : ∀ i, i < path.size → g[path[i]!]! = path[i]!) :
    PartEquiv n (fun x => g[x]!) p p := by
  induction h with
  | root =>
    have hu : PartEquiv n (fun x => g[x]!) (Part.unit n) (Part.unit n) := by
      refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun v hv => ?_⟩
      have hgv : g[v]! < n := hg.perm.lt v hv
      have hpos : ∀ w, w < n → (Part.unit n).cst[(Part.unit n).pos[w]!]! = 0 := by
        intro w hw
        have h1 : (Part.unit n).pos = Array.range n := rfl
        have h2 : (Part.unit n).cst = Array.replicate n 0 := rfl
        have hr : (Array.range n)[w]! = w := by
          rw [getElem!_pos (Array.range n) w (by simpa using hw)]; simp
        rw [h1, hr, h2, getElem!_pos (Array.replicate n 0) w (by simpa using hw)]
        simp
      rw [hpos _ hgv, hpos v hv]
    have := (refine_equiv (f := f) hg.perm.isPerm (unit_wf n) (unit_wf n) hu
      (if n == 0 then #[] else (Array.replicate n false).set! 0 true) hashSeed).1
    rw [hg.graph] at this
    rw [rootPart, initialRefine]
    simpa using this
  | @step path invPath p c v hnode hc hv hcell ih =>
    have hfix' : ∀ i, i < path.size → g[path[i]!]! = path[i]! := by
      intro i hi
      have h1 := hfix i (by rw [Array.size_push]; omega)
      rwa [push_getElemD_lt path v hi] at h1
    have hgv : g[v]! = v := by
      have h1 := hfix path.size (by rw [Array.size_push]; omega)
      rwa [push_getElemD_eq] at h1
    have hce := child_equiv (f := f) hg.perm.isPerm hnode.wf hnode.wf (ih hfix') hv
    rw [hg.graph, hgv] at hce
    exact hce.1

end Canon
end IsoGraph
