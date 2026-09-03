/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Algorithm
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Push
import LeanPool.IsoGraph.ForMathlib.Array
import LeanPool.IsoGraph.ForMathlib.Bits

/-!
# Equivariance of the pieces of the canonical labelling

This file works at the level of `IsoGraph.Canon.Algorithm`: raw `Array Nat`s, and permutations of
`{0, …, n-1}` represented as `Nat → Nat`.  The translation to `Equiv.Perm (Fin n)` happens in
`IsoGraph/Canon/Spec.lean`.

Fix a renaming `σ` of the vertices and write `q ≈ p` for "the ordered partitions `q` and `p` have
the same cell boundaries, and the `i`-th cell of `q` is the `σ`-image of the `i`-th cell of `p`
*as a set*" (`PartEquiv`).  Only as a set: refinement's counting sort is stable, so the order
*within* a cell is inherited from the parent cell and therefore does depend on the vertex names.
What is invariant is the sequence of cells.

Each piece of the search respects `≈`:

* `Graph.ofOracle` transforms along a renaming, and the labelling really is a permutation of the
  vertices (`canonicalLabellingOfOracle` checks that at run time);
* `Part.WF` and `PartEquiv` are the vocabulary — "well-formed ordered partition" and "the same
  partition up to renaming" — that everything else is phrased in;
* `cellCount_equiv`: corresponding cells agree on every count; `countFrom_cellCount`: the
  counting phase of `refineStep` computes exactly such a count (`countFrom_equiv` combines the
  two); `countFrom_mem_touched`: the set of vertices that phase records is invariant too;
  `collect_equiv`: the two runs go on to split the very same list of cells, in the very same
  order;
* the two readers of a partition, `shapeHash` and `targetCell`, see only cell boundaries, so they
  agree on partitions related by any renaming;
* individualising corresponding vertices of related partitions gives related partitions, at the
  same position (`individualize_partEquiv`), and preserves well-formedness;
* two runs that reach related *discrete* partitions read off the same certificate
  (`certOf_of_partEquiv`, via `certOf_relabel`), with `discrete_of_targetCell_none` supplying
  the discreteness at the leaves.
-/

namespace IsoGraph
namespace Canon

/-! ## Permutations of an initial segment -/

/-- `σ` permutes `{0, …, n-1}`: it maps the segment into itself and is injective there.  Since
the segment is finite this is the same as being a bijection of it, but the two clauses are what
the proofs actually use. -/
structure IsPerm (n : Nat) (σ : Nat → Nat) : Prop where
  /-- `σ` maps the segment into itself. -/
  maps : ∀ v, v < n → σ v < n
  /-- `σ` is injective on the segment. -/
  inj : ∀ v, v < n → ∀ w, w < n → σ v = σ w → v = w

theorem IsPerm.id (n : Nat) : IsPerm n _root_.id := ⟨fun _ h => h, fun _ _ _ _ h => h⟩

theorem IsPerm.comp {n : Nat} {σ τ : Nat → Nat} (hσ : IsPerm n σ) (hτ : IsPerm n τ) :
    IsPerm n (fun v => σ (τ v)) :=
  ⟨fun v hv => hσ.maps _ (hτ.maps v hv),
   fun v hv w hw h => hτ.inj v hv w hw (hσ.inj _ (hτ.maps v hv) _ (hτ.maps w hw) h)⟩

/-- The identity labelling is a permutation — the fallback branch of
`canonicalLabellingOfOracle`. -/
theorem range_isPerm (n : Nat) :
    (Array.range n).size = n ∧ IsPerm n (fun v => (Array.range n)[v]!) := by
  refine ⟨by simp, ⟨fun v hv => ?_, fun v hv w hw h => ?_⟩⟩
  · rw [getElem!_pos _ _ (by simpa using hv)]; simpa using hv
  · rw [getElem!_pos _ _ (by simpa using hv), getElem!_pos _ _ (by simpa using hw)] at h
    simpa using h

/-- `isPermArray` is sound: what it accepts really is a permutation of `{0, …, n-1}`.  (It is
also complete, but nothing below needs that — an unsound accept would be the problem.) -/
theorem isPermArray_spec {n : Nat} {a : Array Nat} (h : isPermArray n a = true) :
    a.size = n ∧ IsPerm n (fun v => a[v]!) := by
  simp only [isPermArray, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hsz, hall⟩ := h
  refine ⟨hsz, ⟨fun v hv => (hall v hv).1, fun v hv w hw hvw => ?_⟩⟩
  have hv2 := (hall v hv).2
  rw [hvw, (hall w hw).2] at hv2
  exact hv2.symm

/-- **The labelling really is a labelling.**  Not because the search is known to produce one —
that is still open — but because `canonicalLabellingOfOracle` checks, and falls back to the
identity if the check fails. -/
theorem canonicalLabellingOfOracle_isPerm (n : Nat) (f : Nat → Nat → Bool) :
    (canonicalLabellingOfOracle n f).size = n ∧
      IsPerm n (fun v => (canonicalLabellingOfOracle n f)[v]!) := by
  -- stated for an arbitrary `a` so that `split` sees the `if`, then applied to the search output
  have h : ∀ a : Array Nat,
      (if isPermArray n a then a else Array.range n).size = n ∧
        IsPerm n (fun v => (if isPermArray n a then a else Array.range n)[v]!) := by
    intro a
    split
    · exact isPermArray_spec (by assumption)
    · exact range_isPerm n
  exact h _

/-! ## `Graph.ofOracle`

The algorithm never reads an oracle directly: it reads the `adj` matrix and the `nbr` lists that
`Graph.ofOracle` builds from it.  So every statement about renaming vertices has to pass through
these three lemmas. -/

@[simp] theorem ofOracle_n (n : Nat) (f : Nat → Nat → Bool) : (Graph.ofOracle n f).n = n := by
  rfl

/-- The dense matrix of `Graph.ofOracle` is the oracle, on the intended range. -/
@[simp] theorem ofOracle_adj (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n)
    (hw : w < n) : ((Graph.ofOracle n f).adj[v]!)[w]! = f v w := by
  simp [Graph.ofOracle, getElem!_pos, hv, hw]

/-- A neighbour list of `Graph.ofOracle` is the row of the oracle, as a filtered range. -/
theorem ofOracle_nbr (n : Nat) (f : Nat → Nat → Bool) (v : Nat) (hv : v < n) :
    (Graph.ofOracle n f).nbr[v]! = (Array.range n).filter (f v) := by
  simp [Graph.ofOracle, getElem!_pos, hv]

/-- The neighbour lists of `Graph.ofOracle` are the rows of the oracle. -/
theorem ofOracle_mem_nbr (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n) (hw : w < n) :
    w ∈ (Graph.ofOracle n f).nbr[v]! ↔ f v w = true := by
  rw [ofOracle_nbr n f v hv, Array.mem_filter, Array.mem_range]
  simp [hw]

/-- Neighbour lists stay inside the vertex set. -/
theorem ofOracle_nbr_lt (n : Nat) (f : Nat → Nat → Bool) (v w : Nat) (hv : v < n)
    (hw : w ∈ (Graph.ofOracle n f).nbr[v]!) : w < n := by
  rw [ofOracle_nbr n f v hv, Array.mem_filter, Array.mem_range] at hw
  exact hw.1

/-- The number of neighbour lists is the number of vertices. -/
@[simp] theorem ofOracle_nbr_size (n : Nat) (f : Nat → Nat → Bool) :
    (Graph.ofOracle n f).nbr.size = n := by simp [Graph.ofOracle]

/-- Neighbour lists stay inside the vertex set, with no hypothesis on the vertex: out of range
`nbr[u]!` is the empty array, which has no members either. -/
theorem ofOracle_nbr_lt' (n : Nat) (f : Nat → Nat → Bool) (u x : Nat)
    (hx : x ∈ (Graph.ofOracle n f).nbr[u]!) : x < n := by
  by_cases hu : u < n
  · exact ofOracle_nbr_lt n f u x hu hx
  · rw [getElem!_neg _ _ (by simp; omega),
      show (default : Array Nat) = #[] from rfl] at hx
    simp at hx

/-! ## Readers of a partition that see only the cell boundaries

Step 2 of the decomposition: `shapeHash` and `targetCell` walk the partition cell by cell using
`cen` alone, never touching `lab`.  So they agree on any two partitions with the same boundaries
— in particular on partitions related by a renaming of the vertices, whatever that renaming does
inside the cells. -/

/-- The cell walk only ever reads `cen` at indices `< n`, so two `cen`s that agree there send it
along the same path.  Both congruence lemmas below are this observation at `fuel = n`, `i = 0`. -/
theorem cenHashFrom_congr {n : Nat} {c d : Array Nat} (h : ∀ i, i < n → c[i]! = d[i]!) :
    ∀ (fuel i : Nat) (x : UInt64), cenHashFrom c n fuel i x = cenHashFrom d n fuel i x
  | 0, _, _ => rfl
  | fuel + 1, i, x => by
    rw [cenHashFrom, cenHashFrom]
    by_cases hi : i ≥ n
    · simp [hi]
    · rw [h i (Nat.lt_of_not_le hi)]
      simpa [hi] using cenHashFrom_congr h fuel d[i]! (mixN x (d[i]! - i))

theorem cenTargetFrom_congr {n : Nat} {c d : Array Nat} (h : ∀ i, i < n → c[i]! = d[i]!) :
    ∀ (fuel i : Nat), cenTargetFrom c n fuel i = cenTargetFrom d n fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    rw [cenTargetFrom, cenTargetFrom]
    by_cases hi : i ≥ n
    · simp [hi]
    · rw [h i (Nat.lt_of_not_le hi)]
      simp only [ite_eq_right hi]
      by_cases hd : d[i]! - i > 1
      · simp [hd]
      · simp [hd, cenTargetFrom_congr h fuel d[i]!]

theorem shapeHash_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.shapeHash n = q.shapeHash n :=
  cenHashFrom_congr h n 0 hashSeed

theorem targetCell_congr (n : Nat) (p q : Part) (h : ∀ i, i < n → p.cen[i]! = q.cen[i]!) :
    p.targetCell n = q.targetCell n :=
  cenTargetFrom_congr h n 0

/-- The walk only reports a cell start it has already checked is `< n`. -/
theorem cenTargetFrom_lt {n : Nat} {c : Array Nat} :
    ∀ (fuel i j : Nat), cenTargetFrom c n fuel i = some j → j < n
  | 0, _, _, h => by simp [cenTargetFrom] at h
  | fuel + 1, i, j, h => by
    rw [cenTargetFrom] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hi
      split at h
      · cases h; exact Nat.lt_of_not_le hi
      · exact cenTargetFrom_lt fuel c[i]! j h

/-- The target cell, when there is one, is a cell start inside the vertex set that is not a
singleton.  (Used to know that individualising is legitimate.) -/
theorem targetCell_lt (n : Nat) (p : Part) (i : Nat) (h : p.targetCell n = some i) : i < n :=
  cenTargetFrom_lt n 0 i h

/-! ## Certificates

Step 4 of the decomposition, certificate half.  A certificate is the adjacency matrix read in the
order given by `lab`; so renaming the vertices along `σ` and reading in the order `lab` gives the
same bits as leaving the graph alone and reading in the order `σ ∘ lab`.  This is the point at
which "the search found corresponding leaves" turns into "the two runs return the same array". -/

/-- One packed row only reads columns `j < n`.  The fuel invariant `j + fuel = n` is what makes
that available: it says the loop is at position `j` with `fuel` columns left, so `fuel ≥ 1`
forces `j < n`. -/
theorem certRow_congr {n : Nat} {b b' : Nat → Bool} (h : ∀ j, j < n → b j = b' j) :
    ∀ (fuel j : Nat) (acc : UInt64) (k : Nat) (out : Array UInt64), j + fuel = n →
      certRow n b fuel j acc k out = certRow n b' fuel j acc k out
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, j, acc, k, out, hj => by
    simp only [certRow, h j (by omega)]
    split <;> exact certRow_congr h fuel (j + 1) _ _ _ (by omega)

/-- The same for the rows: row `i` is packed only for `i < n`. -/
theorem certRowsFrom_congr {n : Nat} {b b' : Nat → Nat → Bool} (w : Nat)
    (h : ∀ i, i < n → ∀ j, j < n → b i j = b' i j) :
    ∀ (fuel i : Nat) (out : Array UInt64), i + fuel = n →
      certRowsFrom n b w fuel i out = certRowsFrom n b' w fuel i out
  | 0, _, _, _ => rfl
  | fuel + 1, i, out, hi => by
    rw [certRowsFrom, certRowsFrom,
      certRow_congr (h i (by omega)) n 0 0 (i * w) out (Nat.zero_add n)]
    exact certRowsFrom_congr w h fuel (i + 1) _ (by omega)

/-- `certBits` reads the matrix only inside `{0, …, n-1}²`. -/
theorem certBits_congr (n : Nat) (b b' : Nat → Nat → Bool)
    (h : ∀ i, i < n → ∀ j, j < n → b i j = b' i j) : certBits n b = certBits n b' :=
  certRowsFrom_congr _ h n 0 _ (Nat.zero_add n)

theorem certOf_eq (G : Graph) (lab : Array Nat) :
    certOf G lab = certBits G.n fun i j => (G.adj[lab[i]!]!)[lab[j]!]! := rfl

/-- `certOf` reads the adjacency matrix only at the pairs named by `lab`. -/
theorem certOf_congr (G H : Graph) (lab lab' : Array Nat) (hn : G.n = H.n)
    (hlab : ∀ i, i < G.n → ∀ j, j < G.n →
      (G.adj[lab[i]!]!)[lab[j]!]! = (H.adj[lab'[i]!]!)[lab'[j]!]!) :
    certOf G lab = certOf H lab' := by
  rw [certOf_eq, certOf_eq, ← hn]
  exact certBits_congr _ _ _ hlab

/-- **Certificates are equivariant.**  Reading the renamed graph along `lab` is reading the
original along `σ ∘ lab`. -/
theorem certOf_relabel (n : Nat) (f : Nat → Nat → Bool) (σ : Nat → Nat) (hσ : IsPerm n σ)
    (lab : Array Nat) (hsz : lab.size = n) (hlab : ∀ i, i < n → lab[i]! < n) :
    certOf (Graph.ofOracle n (fun v w => f (σ v) (σ w))) lab
      = certOf (Graph.ofOracle n f) (lab.map σ) := by
  have hmap : ∀ i, i < n → (lab.map σ)[i]! = σ lab[i]! := by
    intro i hi
    rw [getElem!_pos _ _ (by simpa [hsz] using hi), getElem!_pos _ _ (by omega)]
    simp
  refine certOf_congr _ _ _ _ rfl fun i hi j hj => ?_
  rw [ofOracle_n] at hi hj
  rw [ofOracle_adj n _ _ _ (hlab i hi) (hlab j hj), hmap i hi, hmap j hj,
    ofOracle_adj n f _ _ (hσ.maps _ (hlab i hi)) (hσ.maps _ (hlab j hj))]

/-! ## Partitions related by a renaming

The vocabulary the rest of the decomposition is phrased in.  Fix a renaming `σ` and think of two
runs of the algorithm: one on `f`, one on the graph `fun v w => f (σ v) (σ w)` whose vertex `v`
"is" vertex `σ v` of the first.  The two runs do *not* produce partitions that agree positionwise
under `σ` — they both start from `Part.unit n`, whose `lab` is `Array.range n` in either run, and
refinement's counting sort is stable, so the order *within* a cell is inherited from the parent
and depends on vertex names.  What they do produce is partitions whose cells sit at the same
positions and correspond as *sets*, which is what `PartEquiv` says. -/

/-- `p` is a well-formed ordered partition of `{0, …, n-1}`: `lab` and `pos` are mutually inverse
bijections of the segment, and `cst`/`cen` mark off a decomposition of it into intervals.

The last two clauses are what make `cst`/`cen` describe *cells* rather than arbitrary bounds: the
interval `[cst[i], cen[i])` is the same for every `i` inside it, so `cst[i]` is a well-defined name
for the cell containing position `i`. -/
structure Part.WF (n : Nat) (p : Part) : Prop where
  /-- `lab` covers the segment. -/
  labSize : p.lab.size = n
  /-- `pos` covers the segment. -/
  posSize : p.pos.size = n
  /-- `cst` covers the segment. -/
  cstSize : p.cst.size = n
  /-- `cen` covers the segment. -/
  cenSize : p.cen.size = n
  /-- Positions hold vertices of the segment. -/
  labLt : ∀ i, i < n → p.lab[i]! < n
  /-- Vertices sit at positions in the segment. -/
  posLt : ∀ v, v < n → p.pos[v]! < n
  /-- `pos` is a left inverse of `lab`. -/
  posLab : ∀ i, i < n → p.pos[p.lab[i]!]! = i
  /-- `lab` is a left inverse of `pos`. -/
  labPos : ∀ v, v < n → p.lab[p.pos[v]!]! = v
  /-- A cell starts at or before each of its positions. -/
  cstLe : ∀ i, i < n → p.cst[i]! ≤ i
  /-- A cell ends after each of its positions. -/
  ltCen : ∀ i, i < n → i < p.cen[i]!
  /-- Cells stay inside the segment. -/
  cenLe : ∀ i, i < n → p.cen[i]! ≤ n
  /-- Every position of a cell reports the same start. -/
  cellCst : ∀ i, i < n → ∀ j, p.cst[i]! ≤ j → j < p.cen[i]! → p.cst[j]! = p.cst[i]!
  /-- Every position of a cell reports the same end. -/
  cellCen : ∀ i, i < n → ∀ j, p.cst[i]! ≤ j → j < p.cen[i]! → p.cen[j]! = p.cen[i]!

/-- **Cells are determined by their starts.**  Two positions report the same cell start exactly
when they lie in the same interval — so `cst` really is a set-theoretic partition of positions,
not just a monotone pair of arrays.  This is the workhorse behind `individualize_cell`. -/
theorem Part.WF.cst_eq_iff {n : Nat} {p : Part} (hp : Part.WF n p) {i : Nat} (hi : i < n)
    {k : Nat} (hk : k < n) : p.cst[k]! = p.cst[i]! ↔ (p.cst[i]! ≤ k ∧ k < p.cen[i]!) := by
  refine ⟨fun h => ⟨h ▸ hp.cstLe k hk, ?_⟩, fun h => hp.cellCst i hi k h.1 h.2⟩
  by_contra hke
  -- if `k` sat past the end of `i`'s cell, the position `cen[i] - 1` would be in both cells, and
  -- reading `cen` there would give both `cen[i]` and `cen[k] > k ≥ cen[i]`
  have h1 : p.cst[i]! ≤ i := hp.cstLe i hi
  have h2 : i < p.cen[i]! := hp.ltCen i hi
  have h3 : k < p.cen[k]! := hp.ltCen k hk
  have h4 := hp.cellCen k hk (p.cen[i]! - 1) (by omega) (by omega)
  have h5 := hp.cellCen i hi (p.cen[i]! - 1) (by omega) (by omega)
  omega

/-- `p` is discrete: every cell is a singleton, so each position is its own cell start. -/
def Part.Discrete (n : Nat) (p : Part) : Prop := ∀ i, i < n → p.cst[i]! = i

/-- The position after a singleton cell starts the next one. -/
theorem cst_succ {n : Nat} {p : Part} (hp : Part.WF n p) {i : Nat}
    (hcen : p.cen[i]! = i + 1) (h : i + 1 < n) : p.cst[i + 1]! = i + 1 := by
  have h1 : p.cst[i + 1]! ≤ i + 1 := hp.cstLe _ h
  by_contra hne
  have h3 : i + 1 < p.cen[i + 1]! := hp.ltCen _ h
  -- if `i + 1` were inside an earlier cell, that cell would contain `i` too, and so would end
  -- where `i`'s cell ends — at `i + 1`
  have h5 : p.cen[i]! = p.cen[i + 1]! := hp.cellCen (i + 1) h i (by omega) (by omega)
  omega

/-- The cell walk reaches `n` only by stepping through singletons. -/
theorem cenTargetFrom_none {n : Nat} {p : Part} (hp : Part.WF n p) :
    ∀ (fuel i : Nat), n ≤ i + fuel → (i < n → p.cst[i]! = i) →
      cenTargetFrom p.cen n fuel i = none → ∀ k, i ≤ k → k < n → p.cst[k]! = k
  | 0, _, _, _, _, _, _, _ => by omega
  | fuel + 1, i, hf, hst, h, k, hk1, hk2 => by
    rw [cenTargetFrom] at h
    by_cases hi : i ≥ n
    · omega
    rw [ite_eq_right hi] at h
    have hcst := hst (by omega)
    have hlt := hp.ltCen i (by omega)
    by_cases hd : p.cen[i]! - i > 1
    · rw [ite_eq_left hd] at h; simp at h
    rw [ite_eq_right hd] at h
    have hcen : p.cen[i]! = i + 1 := by omega
    rw [hcen] at h
    by_cases hki : k = i
    · rw [hki]; exact hcst
    · exact cenTargetFrom_none hp fuel (i + 1) (by omega)
        (fun hn => cst_succ hp hcen hn) h k (by omega) hk2

/-- **A partition the walk finds no target in is discrete.**  This is what discharges the
`Discrete` hypotheses of step 4 at the leaves of the search: the algorithm stops individualising
exactly when `targetCell` returns `none`, and that is the same condition. -/
theorem discrete_of_targetCell_none {n : Nat} {p : Part} (hp : Part.WF n p)
    (h : p.targetCell n = none) : p.Discrete n := by
  intro k hk
  refine cenTargetFrom_none hp n 0 (by omega) (fun h0 => ?_) h k (Nat.zero_le k) hk
  have := hp.cstLe 0 h0
  omega

/-- `p` and `q` are the same ordered partition up to the renaming `σ`: the cells occupy the same
ranges of positions, and vertex `v` of `q`'s graph lies in the cell where `σ v` lies in `p`.

The third clause is how "the cells correspond as sets" is said pointwise: a cell is named by its
start position, so it asserts that `σ` maps the cell of `v` in `q` onto the cell at the same
place in `p`. -/
structure PartEquiv (n : Nat) (σ : Nat → Nat) (p q : Part) : Prop where
  /-- Cells start at the same positions. -/
  cst : ∀ i, i < n → p.cst[i]! = q.cst[i]!
  /-- Cells end at the same positions. -/
  cen : ∀ i, i < n → p.cen[i]! = q.cen[i]!
  /-- `σ` carries the cell of `v` in `q` to the cell at the same position in `p`. -/
  cell : ∀ v, v < n → p.cst[p.pos[σ v]!]! = q.cst[q.pos[v]!]!

/-- Related partitions have the same cell-size hash. -/
theorem PartEquiv.shapeHash {n σ p q} (h : PartEquiv n σ p q) : p.shapeHash n = q.shapeHash n :=
  shapeHash_congr n p q h.cen

/-- Related partitions individualise at the same position. -/
theorem PartEquiv.targetCell {n σ p q} (h : PartEquiv n σ p q) :
    p.targetCell n = q.targetCell n :=
  targetCell_congr n p q h.cen

/-- The search starts from a well-formed partition: one cell, `[0, n)`, in vertex order. -/
theorem unit_wf (n : Nat) : Part.WF n (Part.unit n) := by
  have hlab : (Part.unit n).lab = Array.range n := rfl
  have hpos : (Part.unit n).pos = Array.range n := rfl
  have hcst : (Part.unit n).cst = Array.replicate n 0 := rfl
  have hcen : (Part.unit n).cen = Array.replicate n n := rfl
  have hr : ∀ i, i < n → (Array.range n)[i]! = i := by
    intro i hi; rw [getElem!_pos _ _ (by simpa using hi)]; simp
  have hrep : ∀ (x i : Nat), i < n → (Array.replicate n x)[i]! = x := by
    intro x i hi; rw [getElem!_pos _ _ (by simpa using hi)]; simp
  refine ⟨by rw [hlab]; simp, by rw [hpos]; simp, by rw [hcst]; simp, by rw [hcen]; simp,
    fun i hi => by rw [hlab, hr i hi]; exact hi,
    fun v hv => by rw [hpos, hr v hv]; exact hv,
    fun i hi => by rw [hlab, hr i hi, hpos]; exact hr i hi,
    fun v hv => by rw [hpos, hr v hv, hlab]; exact hr v hv,
    fun i hi => by rw [hcst, hrep 0 i hi]; exact Nat.zero_le i,
    fun i hi => by rw [hcen, hrep n i hi]; exact hi,
    fun i hi => by rw [hcen, hrep n i hi], fun i hi j h1 h2 => ?_, fun i hi j h1 h2 => ?_⟩
  · rw [hcen, hrep n i hi] at h2
    rw [hcst, hrep 0 j h2, hrep 0 i hi]
  · rw [hcen, hrep n i hi] at h2
    rw [hcen, hrep n j h2, hrep n i hi]

/-- The unit partition is related to itself under every renaming: one cell carries no order
information. -/
theorem partEquiv_unit (n : Nat) (σ : Nat → Nat) :
    PartEquiv n σ (Part.unit n) (Part.unit n) := by
  have hcst : ∀ i : Nat, (Part.unit n).cst[i]! = 0 := by
    intro i
    change (Array.replicate n 0)[i]! = 0
    by_cases h : i < n
    · rw [getElem!_pos (Array.replicate n 0) i (by simpa using h)]; simp
    · rw [getElem!_neg (Array.replicate n 0) i (by simpa using h)]; rfl
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => (hcst _).trans (hcst _).symm⟩

/-- **Once the partitions are discrete, `σ` relates the labellings positionwise.**  This is where
"cells correspond as sets" turns into an equation between arrays: a singleton cell has only one
member, so there is nothing left for the stable sort to have permuted. -/
theorem lab_eq_of_discrete {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (hpd : p.Discrete n) (hqd : q.Discrete n)
    (h : PartEquiv n σ p q) (i : Nat) (hi : i < n) : p.lab[i]! = σ q.lab[i]! := by
  have hv : q.lab[i]! < n := hq.labLt i hi
  have hσv : σ q.lab[i]! < n := hσ.maps _ hv
  have hc := h.cell q.lab[i]! hv
  rw [hq.posLab i hi, hqd i hi, hpd _ (hp.posLt _ hσv)] at hc
  calc p.lab[i]! = p.lab[p.pos[σ q.lab[i]!]!]! := by rw [hc]
    _ = σ q.lab[i]! := hp.labPos _ hσv

/-- **Step 4 of the decomposition.**  Two runs that reach related discrete partitions read off
the same certificate — the renamed graph along `q.lab` is the original along `p.lab`.  This is
the point at which "the search found corresponding leaves" becomes "the two runs return the same
array". -/
theorem certOf_of_partEquiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (hpd : p.Discrete n) (hqd : q.Discrete n)
    (h : PartEquiv n σ p q) (f : Nat → Nat → Bool) :
    certOf (Graph.ofOracle n fun v w => f (σ v) (σ w)) q.lab
      = certOf (Graph.ofOracle n f) p.lab := by
  have hqsz := hq.labSize
  rw [certOf_relabel n f σ hσ q.lab hqsz fun i hi => hq.labLt i hi]
  refine certOf_congr _ _ _ _ rfl fun i hi j hj => ?_
  rw [ofOracle_n] at hi hj
  have hmap : ∀ k, k < n → (q.lab.map σ)[k]! = p.lab[k]! := by
    intro k hk
    have h1 : (q.lab.map σ)[k]! = σ q.lab[k]! := by
      rw [getElem!_pos (q.lab.map σ) k (by simpa [hqsz] using hk),
        getElem!_pos q.lab k (by omega)]
      simp
    rw [h1, ← lab_eq_of_discrete hσ hp hq hpd hqd h k hk]
  rw [hmap i hi, hmap j hj]

/-! ## Step 3 of the decomposition: individualisation

`individualize p v` splits `v` off to the front of its cell.  The two runs pick *different*
vertices to displace — `p.lab[c]` need not be `σ (q.lab[c])`, since the order inside a cell is
name-dependent — so the arrays are genuinely different.  What survives is exactly what `PartEquiv`
records: the cell boundaries move the same way, and a vertex other than the individualised one
lands in the second fragment of the old cell precisely when it was in that cell to begin with. -/

theorem setCstFrom_size (c ec : Nat) :
    ∀ (fuel j : Nat) (cst : Array Nat), (setCstFrom c ec fuel j cst).size = cst.size
  | 0, _, _ => rfl
  | fuel + 1, j, cst => by
    rw [setCstFrom]
    split
    · rfl
    · rw [setCstFrom_size c ec fuel (j + 1) _]; simp

theorem setCstFrom_getElemD {c ec : Nat} {cst : Array Nat} (hec : ec ≤ cst.size) :
    ∀ (fuel j : Nat), ec ≤ j + fuel → ∀ k,
      (setCstFrom c ec fuel j cst)[k]! = if j ≤ k ∧ k < ec then c + 1 else cst[k]!
  | 0, j, hf, k => by rw [setCstFrom, ite_eq_right (by omega)]
  | fuel + 1, j, hf, k => by
    rw [setCstFrom]
    split
    · rw [ite_eq_right (by omega)]
    · rename_i hj
      rw [setCstFrom_getElemD (by simpa using hec) fuel (j + 1) (by omega) k,
        getElemD_setD (by omega) k]
      by_cases h1 : j + 1 ≤ k ∧ k < ec
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : k = j
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]

section Individualize

variable {n : Nat} {p : Part} {v i c ec u : Nat}

/-- The position returned by `individualize` is the start of the cell that was split. -/
theorem individualize_snd (p : Part) (v : Nat) : (individualize p v).2 = p.cst[p.pos[v]!]! := rfl

theorem individualize_lab_eq (p : Part) (v : Nat) : (individualize p v).1.lab
    = (p.lab.set! (p.cst[p.pos[v]!]!) v).set! (p.pos[v]!) (p.lab[p.cst[p.pos[v]!]!]!) := rfl

theorem individualize_pos_eq (p : Part) (v : Nat) : (individualize p v).1.pos
    = (p.pos.set! v (p.cst[p.pos[v]!]!)).set! (p.lab[p.cst[p.pos[v]!]!]!) (p.pos[v]!) := rfl

theorem individualize_cst_eq (p : Part) (v : Nat) : (individualize p v).1.cst
    = setCstFrom (p.cst[p.pos[v]!]!) (p.cen[p.pos[v]!]!)
        (p.cen[p.pos[v]!]! - (p.cst[p.pos[v]!]! + 1)) (p.cst[p.pos[v]!]! + 1) p.cst := rfl

theorem individualize_cen_eq (p : Part) (v : Nat) : (individualize p v).1.cen
    = p.cen.set! (p.cst[p.pos[v]!]!) (p.cst[p.pos[v]!]! + 1) := rfl

/-- The facts about `p` that every statement below is phrased in: `v` sits at position `i`, whose
cell is `[c, ec)`, and `u` is the vertex displaced from the front of that cell. -/
structure IndivData (n : Nat) (p : Part) (v i c ec u : Nat) : Prop where
  /-- `v` is a vertex of the segment. -/
  vLt : v < n
  /-- `i` is where `v` sits. -/
  posv : p.pos[v]! = i
  /-- `c` is the start of `i`'s cell. -/
  csti : p.cst[i]! = c
  /-- `ec` is its end. -/
  ceni : p.cen[i]! = ec
  /-- `u` is the vertex at the front of it. -/
  labc : p.lab[c]! = u

namespace IndivData

variable (hp : Part.WF n p) (hd : IndivData n p v i c ec u)
include hp hd

theorem iLt : i < n := hd.posv ▸ hp.posLt v hd.vLt
theorem cLe : c ≤ i := hd.csti ▸ hp.cstLe i (iLt hp hd)
theorem iLtEc : i < ec := hd.ceni ▸ hp.ltCen i (iLt hp hd)
theorem ecLe : ec ≤ n := hd.ceni ▸ hp.cenLe i (iLt hp hd)
theorem cLt : c < n := by have := cLe hp hd; have := iLt hp hd; omega

/-- The cell start is its own cell start. -/
theorem cstc : p.cst[c]! = c := by
  have h1 := cLe hp hd
  have h2 := iLtEc hp hd
  have h := hp.cellCst i (iLt hp hd) c (by rw [hd.csti]) (by rw [hd.ceni]; omega)
  rw [h, hd.csti]

theorem uLt : u < n := hd.labc ▸ hp.labLt c (cLt hp hd)

/-- The displaced vertex sits at the front of the cell. -/
theorem posu : p.pos[u]! = c := by rw [← hd.labc]; exact hp.posLab c (cLt hp hd)

/-- Membership in the split cell is visible from `cst` alone. -/
theorem mem_iff {k : Nat} (hk : k < n) : p.cst[k]! = c ↔ (c ≤ k ∧ k < ec) := by
  rw [← hd.csti, ← hd.ceni]; exact hp.cst_eq_iff (iLt hp hd) hk

theorem cst_eq {k : Nat} (h1 : c ≤ k) (h2 : k < ec) : p.cst[k]! = c := by
  have h := hp.cellCst i (iLt hp hd) k (by rw [hd.csti]; exact h1) (by rw [hd.ceni]; exact h2)
  rw [h, hd.csti]

theorem cen_eq {k : Nat} (h1 : c ≤ k) (h2 : k < ec) : p.cen[k]! = ec := by
  have h := hp.cellCen i (iLt hp hd) k (by rw [hd.csti]; exact h1) (by rw [hd.ceni]; exact h2)
  rw [h, hd.ceni]

end IndivData

/-- After individualisation the old cell `[c, ec)` has been cut into `{c}` and `[c+1, ec)`. -/
theorem individualize_cst_getElemD (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.cst[k]! = if c + 1 ≤ k ∧ k < ec then c + 1 else p.cst[k]! := by
  rw [individualize_cst_eq, hd.posv, hd.csti, hd.ceni]
  exact setCstFrom_getElemD (by rw [hp.cstSize]; exact hd.ecLe hp) _ _ (by omega) k

theorem individualize_cen_getElemD (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.cen[k]! = if k = c then c + 1 else p.cen[k]! := by
  rw [individualize_cen_eq, hd.posv, hd.csti]
  exact getElemD_setD (by rw [hp.cenSize]; exact hd.cLt hp) k

theorem individualize_pos_getElemD (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (w : Nat) :
    (individualize p v).1.pos[w]! = if w = u then i else if w = v then c else p.pos[w]! := by
  have h1 : u < (p.pos.set! v c).size := by
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hp.posSize]
    exact hd.uLt hp
  have h2 : v < p.pos.size := by rw [hp.posSize]; exact hd.vLt
  rw [individualize_pos_eq, hd.posv, hd.csti, hd.labc, getElemD_setD h1 w, getElemD_setD h2 w]

theorem individualize_lab_getElemD (hp : Part.WF n p) (hd : IndivData n p v i c ec u) (k : Nat) :
    (individualize p v).1.lab[k]! = if k = i then u else if k = c then v else p.lab[k]! := by
  have h1 : i < (p.lab.set! c v).size := by
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hp.labSize]
    exact hd.iLt hp
  have h2 : c < p.lab.size := by rw [hp.labSize]; exact hd.cLt hp
  rw [individualize_lab_eq, hd.posv, hd.csti, hd.labc, getElemD_setD h1 k, getElemD_setD h2 k]

/-- The individualised vertex now occupies the singleton cell at `c`. -/
theorem individualize_pos_self (hp : Part.WF n p) (hd : IndivData n p v i c ec u) :
    (individualize p v).1.pos[v]! = c := by
  rw [individualize_pos_getElemD hp hd v]
  by_cases hvu : v = u
  · rw [ite_eq_left hvu]
    have h := hd.posu hp
    rw [← hvu, hd.posv] at h
    omega
  · rw [ite_eq_right hvu, ite_eq_left rfl]

/-- **The cell of each vertex after individualisation.**  `v` gets the singleton cell `c`;
everything else that was in `v`'s cell moves to `c + 1`; everything else is untouched.  Note that
this says nothing about *where inside its cell* a vertex sits — which is exactly why it is stable
under a renaming that reorders cells internally. -/
theorem individualize_cell (hp : Part.WF n p) (hd : IndivData n p v i c ec u)
    (w : Nat) (hw : w < n) :
    (individualize p v).1.cst[(individualize p v).1.pos[w]!]!
      = if w = v then c else if p.cst[p.pos[w]!]! = c then c + 1 else p.cst[p.pos[w]!]! := by
  have hcLe := hd.cLe hp
  have hiEc := hd.iLtEc hp
  by_cases hwv : w = v
  · subst hwv
    rw [ite_eq_left rfl, individualize_pos_self hp hd, individualize_cst_getElemD hp hd,
      ite_eq_right (by omega), hd.cstc hp]
  rw [ite_eq_right hwv, individualize_pos_getElemD hp hd w]
  by_cases hwu : w = u
  · -- `w` is the displaced vertex: it was at the front of the cell and is now at position `i`
    have hic : i ≠ c := by
      intro h
      refine hwv ?_
      rw [hwu, ← hd.labc, ← h, ← hd.posv]
      exact hp.labPos v hd.vLt
    have hA : p.cst[p.pos[w]!]! = c := by
      rw [hwu, hd.posu hp, hd.cstc hp]
    rw [ite_eq_left hwu, hA, ite_eq_left rfl, individualize_cst_getElemD hp hd,
      ite_eq_left ⟨by omega, hiEc⟩]
  rw [ite_eq_right hwu, ite_eq_right hwv, individualize_cst_getElemD hp hd]
  have hjN : p.pos[w]! < n := hp.posLt w hw
  have hjc : p.pos[w]! ≠ c := by
    intro h
    exact hwu (by rw [← hd.labc, ← h, hp.labPos w hw])
  by_cases hA : p.cst[p.pos[w]!]! = c
  · have := (hd.mem_iff hp hjN).1 hA
    rw [ite_eq_left hA, ite_eq_left ⟨by omega, this.2⟩]
  · rw [ite_eq_right hA, ite_eq_right (fun hh => hA ((hd.mem_iff hp hjN).2 ⟨by omega, hh.2⟩))]

/-- **Individualisation preserves well-formedness.**  `lab`/`pos` stay inverse because the update
is a transposition, and `cst`/`cen` still describe intervals because `[c, ec)` was cut in two. -/
theorem individualize_wf (hp : Part.WF n p) (hd : IndivData n p v i c ec u) :
    Part.WF n (individualize p v).1 := by
  have hiLt := hd.iLt hp
  have hcLe := hd.cLe hp
  have hiEc := hd.iLtEc hp
  have hecN := hd.ecLe hp
  have hcN := hd.cLt hp
  have huN := hd.uLt hp
  have hvN := hd.vLt
  have hcstc := hd.cstc hp
  have hposu := hd.posu hp
  have hlabi : p.lab[i]! = v := by rw [← hd.posv]; exact hp.labPos v hvN
  have hlab := individualize_lab_getElemD hp hd
  have hpos := individualize_pos_getElemD hp hd
  have hcst := individualize_cst_getElemD hp hd
  have hcen := individualize_cen_getElemD hp hd
  -- the transposition is injective, in the four forms the proofs below need
  have hlabu : ∀ k, k < n → p.lab[k]! = u → k = c := by
    intro k hk h; have h2 := hp.posLab k hk; rw [h, hposu] at h2; omega
  have hlabv : ∀ k, k < n → p.lab[k]! = v → k = i := by
    intro k hk h; have h2 := hp.posLab k hk; rw [h, hd.posv] at h2; omega
  have hposi : ∀ w, w < n → p.pos[w]! = i → w = v := by
    intro w hw h; have h2 := hp.labPos w hw; rw [h, hlabi] at h2; omega
  have hposc : ∀ w, w < n → p.pos[w]! = c → w = u := by
    intro w hw h; have h2 := hp.labPos w hw; rw [h, hd.labc] at h2; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [individualize_lab_eq]; simp [hp.labSize]
  · rw [individualize_pos_eq]; simp [hp.posSize]
  · rw [individualize_cst_eq, setCstFrom_size]; exact hp.cstSize
  · rw [individualize_cen_eq]; simp [hp.cenSize]
  · intro k hk
    rw [hlab k]
    split_ifs
    · exact huN
    · exact hvN
    · exact hp.labLt k hk
  · intro w hw
    rw [hpos w]
    split_ifs
    · exact hiLt
    · exact hcN
    · exact hp.posLt w hw
  · -- `pos` is still a left inverse of `lab`
    intro k hk
    rw [hlab k]
    by_cases h1 : k = i
    · rw [ite_eq_left h1, hpos u, ite_eq_left rfl, h1]
    rw [ite_eq_right h1]
    by_cases h2 : k = c
    · have hci : c ≠ i := fun hh => h1 (h2.trans hh)
      have hvu : v ≠ u := fun h => hci (by rw [← hposu, ← h, hd.posv])
      rw [ite_eq_left h2, hpos v, ite_eq_right hvu, ite_eq_left rfl, h2]
    · rw [ite_eq_right h2, hpos p.lab[k]!, ite_eq_right (fun h => h2 (hlabu k hk h)),
        ite_eq_right (fun h => h1 (hlabv k hk h)), hp.posLab k hk]
  · -- and `lab` of `pos`
    intro w hw
    rw [hpos w]
    by_cases h1 : w = u
    · rw [ite_eq_left h1, hlab i, ite_eq_left rfl, h1]
    rw [ite_eq_right h1]
    by_cases h2 : w = v
    · have hci : c ≠ i := fun hh => h1 (by rw [h2, ← hlabi, ← hh, hd.labc])
      rw [ite_eq_left h2, hlab c, ite_eq_right hci, ite_eq_left rfl, h2]
    · rw [ite_eq_right h2, hlab p.pos[w]!, ite_eq_right (fun h => h2 (hposi w hw h)),
        ite_eq_right (fun h => h1 (hposc w hw h)), hp.labPos w hw]
  · intro k hk
    rw [hcst k]
    split_ifs with h
    · omega
    · exact hp.cstLe k hk
  · intro k hk
    rw [hcen k]
    split_ifs with h
    · omega
    · exact hp.ltCen k hk
  · intro k hk
    rw [hcen k]
    split_ifs
    · omega
    · exact hp.cenLe k hk
  · -- cells still report a common start …
    intro k hk j hj1 hj2
    have hcenk : (individualize p v).1.cen[k]! ≤ n := by
      rw [hcen k]
      split_ifs
      · omega
      · exact hp.cenLe k hk
    have hjn : j < n := by omega
    rw [hcst k] at hj1
    rw [hcen k] at hj2
    rw [hcst j, hcst k]
    by_cases h1 : c + 1 ≤ k ∧ k < ec
    · obtain ⟨h1a, h1b⟩ := h1
      rw [ite_eq_left (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)] at hj1
      rw [ite_eq_right (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b] at hj2
      rw [ite_eq_left (⟨by omega, by omega⟩ : c + 1 ≤ j ∧ j < ec),
        ite_eq_left (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)]
    rw [ite_eq_right h1] at hj1 ⊢
    by_cases h2 : k = c
    · rw [ite_eq_left h2] at hj2
      rw [h2, hcstc] at hj1 ⊢
      rw [ite_eq_right (by omega : ¬(c + 1 ≤ j ∧ j < ec))]
      rw [show j = c by omega, hcstc]
    · rw [ite_eq_right h2] at hj2
      have hkc : ¬(c ≤ k ∧ k < ec) := fun hh => h1 ⟨by omega, hh.2⟩
      have hck : p.cst[k]! ≠ c := fun hh => hkc ((hd.mem_iff hp hk).1 hh)
      have hjk : p.cst[j]! = p.cst[k]! := hp.cellCst k hk j hj1 hj2
      rw [ite_eq_right (fun hh =>
        hck (hjk.symm.trans (hd.cst_eq hp (Nat.le_of_succ_le hh.1) hh.2))), hjk]
  · -- … and a common end
    intro k hk j hj1 hj2
    have hcenk : (individualize p v).1.cen[k]! ≤ n := by
      rw [hcen k]
      split_ifs
      · omega
      · exact hp.cenLe k hk
    have hjn : j < n := by omega
    rw [hcst k] at hj1
    rw [hcen k] at hj2
    rw [hcen j, hcen k]
    by_cases h1 : c + 1 ≤ k ∧ k < ec
    · obtain ⟨h1a, h1b⟩ := h1
      rw [ite_eq_left (⟨h1a, h1b⟩ : c + 1 ≤ k ∧ k < ec)] at hj1
      rw [ite_eq_right (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b] at hj2
      rw [ite_eq_right (by omega : ¬ k = c), hd.cen_eq hp (by omega) h1b]
      rw [ite_eq_right (by omega : ¬ j = c), hd.cen_eq hp (by omega) hj2]
    rw [ite_eq_right h1] at hj1
    by_cases h2 : k = c
    · rw [ite_eq_left h2] at hj2 ⊢
      rw [h2, hcstc] at hj1
      rw [ite_eq_left (by omega : j = c)]
    · rw [ite_eq_right h2] at hj2 ⊢
      have hkc : ¬(c ≤ k ∧ k < ec) := fun hh => h1 ⟨by omega, hh.2⟩
      have hck : p.cst[k]! ≠ c := fun hh => hkc ((hd.mem_iff hp hk).1 hh)
      have hjc : j ≠ c := by
        intro hh
        exact hck ((hp.cellCst k hk c (by omega) (by omega)).symm.trans hcstc)
      rw [ite_eq_right hjc]
      exact hp.cellCen k hk j hj1 hj2

end Individualize

/-- **Step 3 of the decomposition.**  Individualising corresponding vertices of related partitions
gives related partitions, and at the same position — so the two runs stay in step through the
branch, and the recursive call sees the same splitter. -/
theorem individualize_partEquiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q) {v : Nat} (hv : v < n) :
    PartEquiv n σ (individualize p (σ v)).1 (individualize q v).1
      ∧ (individualize p (σ v)).2 = (individualize q v).2 := by
  have hσv : σ v < n := hσ.maps v hv
  -- the two runs split the cell at the same position `c`, and it has the same extent `ec`
  set c := q.cst[q.pos[v]!]! with hc
  have hcp : p.cst[p.pos[σ v]!]! = c := h.cell v hv
  have hdp : IndivData n p (σ v) p.pos[σ v]! c p.cen[p.pos[σ v]!]! p.lab[c]! :=
    ⟨hσv, rfl, hcp, rfl, rfl⟩
  have hdq : IndivData n q v q.pos[v]! c q.cen[q.pos[v]!]! q.lab[c]! := ⟨hv, rfl, hc.symm, rfl, rfl⟩
  have hcn : c < n := hdq.cLt hq
  have hecp : p.cen[c]! = p.cen[p.pos[σ v]!]! :=
    hp.cellCen _ (hdp.iLt hp) c (by rw [hcp]) (by have := hdp.cLe hp; have := hdp.iLtEc hp; omega)
  have hecq : q.cen[c]! = q.cen[q.pos[v]!]! :=
    hq.cellCen _ (hdq.iLt hq) c (by rw [← hc]) (by have := hdq.cLe hq; have := hdq.iLtEc hq; omega)
  have hec : p.cen[p.pos[σ v]!]! = q.cen[q.pos[v]!]! := by rw [← hecp, ← hecq, h.cen c hcn]
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_, fun w hw => ?_⟩, hcp⟩
  · rw [individualize_cst_getElemD hp hdp k, individualize_cst_getElemD hq hdq k, hec]
    split
    · rfl
    · exact h.cst k hk
  · rw [individualize_cen_getElemD hp hdp k, individualize_cen_getElemD hq hdq k]
    split
    · rfl
    · exact h.cen k hk
  · rw [individualize_cell hp hdp (σ w) (hσ.maps w hw), individualize_cell hq hdq w hw,
      h.cell w hw]
    by_cases hwv : w = v
    · rw [ite_eq_left hwv, ite_eq_left (by rw [hwv])]
    · rw [ite_eq_right hwv, ite_eq_right (fun hh => hwv (hσ.inj w hw v hv hh))]

/-! ## What `refineStep` counts

`refineStep` is the one piece of the algorithm whose equivariance is *not* positionwise.  Every
other loop walks positions, and corresponding positions hold corresponding data; but the counting
phase walks a cell in `lab` order, and corresponding cells are related only as sets.  So the
quantity it computes has to be described set-theoretically before it can be shown invariant, and
that description is `cellCount`: the number of vertices of a given cell satisfying a predicate.

The arithmetic comes first (`cellCount_equiv`: the quantity is invariant), then the first of
`refineStep`'s loops (`countFrom_cellCount`: the loop computes the quantity). -/

/-- A permutation of a finite initial segment is onto it.  Not part of `IsPerm` because nothing
before this section needed it — injectivity was always enough. -/
theorem IsPerm.surj {n : Nat} {σ : Nat → Nat} (hσ : IsPerm n σ) {w : Nat} (hw : w < n) :
    ∃ v, v < n ∧ σ v = w := by
  have hsub : (Finset.range n).image σ ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact hσ.maps a ha
  have hcard : ((Finset.range n).image σ).card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hσ.inj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) hab
  have heq : (Finset.range n).image σ = Finset.range n :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have hmem : w ∈ (Finset.range n).image σ := by rw [heq]; exact Finset.mem_range.2 hw
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨a, ha, hax⟩ := hmem
  exact ⟨a, ha, hax⟩

/-- How many vertices of the cell starting at position `s` satisfy `P`.  Every number
`refineStep` computes is of this form: the neighbour count of `v` is `P w := adj w v`, a bucket
size in the counting sort is `P w := cnt w == t`, and a cell size is `P w := true`. -/
def cellCount (n : Nat) (p : Part) (s : Nat) (P : Nat → Bool) : Nat :=
  ((Finset.range n).filter fun w => p.cst[p.pos[w]!]! = s ∧ P w = true).card

/-- **The arithmetic behind step 1.**  Corresponding cells have the same size, and more generally
agree on any count, because `σ` restricts to a bijection between them.  Note this is a genuine
cardinality argument — there is no order-preserving correspondence to appeal to. -/
theorem cellCount_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (s : Nat) (P : Nat → Bool) :
    cellCount n p s P = cellCount n q s (fun w => P (σ w)) := by
  refine (Finset.card_bij (fun w _ => σ w) ?_ ?_ ?_).symm
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
    exact ⟨hσ.maps w hw.1, (h.cell w hw.1).trans hw.2.1, hw.2.2⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact hσ.inj a ha.1 b hb.1 hab
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_range] at hw'
    obtain ⟨w, hw, rfl⟩ := hσ.surj hw'.1
    refine ⟨w, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hw, (h.cell w hw).symm.trans hw'.2.1, hw'.2.2⟩

/-- Corresponding cells have the same size. -/
theorem cellSize_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (s : Nat) :
    cellCount n p s (fun _ => true) = cellCount n q s (fun _ => true) :=
  cellCount_equiv hσ h s _

/-- The neighbour counts that drive refinement are equivariant: `σ v` sees as many neighbours in
`p`'s cell at `s` as `v` does in `q`'s. -/
theorem cellNbrCount_equiv {n : Nat} {σ : Nat → Nat} {p q : Part} (hσ : IsPerm n σ)
    (h : PartEquiv n σ p q) (f : Nat → Nat → Bool) (s v : Nat) :
    cellCount n p s (fun w => f w (σ v))
      = cellCount n q s (fun w => (fun a b => f (σ a) (σ b)) w v) :=
  cellCount_equiv hσ h s _

/-! ### The counting loop

`countFrom` is phase (1) of `refineStep`: it walks the splitter cell `lab[s:e]` and, for every
vertex `w`, accumulates in `cnt[w]` the number of cell members adjacent to `w`.  Written as a
`for` loop this would be out of reach — see the note on `cenHashFrom` — so `Algorithm.lean` gives
it as a structural recursion on fuel, and the three lemmas below read the result off.

The bridge to `cellCount` is `List.count`: the inner loop bumps `cnt[w]` once per occurrence of
`w` in a neighbour list, and `Graph.ofOracle`'s neighbour lists are filtered ranges, hence
duplicate-free, so each cell member contributes at most one. -/

/-- The inner loop only writes, never resizes. -/
theorem bumpFrom_size (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    (bumpFrom nbrs fuel j cnt touched).1.size = cnt.size
  | 0, _, _, _ => rfl
  | fuel + 1, j, cnt, touched => by
    rw [bumpFrom]
    split
    · rfl
    · rw [bumpFrom_size nbrs fuel (j + 1) _ _]
      simp

/-- The inner loop adds to `cnt[w]` the multiplicity of `w` in the part of the neighbour list it
scans.  Entries of `nbrs` outside `cnt` write nothing, but they are not `w` either, so the
statement needs no hypothesis on them. -/
theorem bumpFrom_getElemD (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    nbrs.size ≤ j + fuel → ∀ w, w < cnt.size →
      (bumpFrom nbrs fuel j cnt touched).1[w]! = cnt[w]! + (nbrs.toList.drop j).count w
  | 0, j, cnt, touched, hf, w, hw => by
    rw [bumpFrom, List.drop_eq_nil_of_le (by simp; omega), List.count_nil]
    simp
  | fuel + 1, j, cnt, touched, hf, w, hw => by
    rw [bumpFrom]
    split
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.count_nil]
      simp
    · rename_i hj
      have hjs : j < nbrs.size := by omega
      have hdrop : nbrs.toList.drop j = nbrs[j]! :: nbrs.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs), getElem!_pos nbrs j hjs,
          Array.getElem_toList]
      rw [bumpFrom_getElemD nbrs fuel (j + 1) _ _ (by omega) w
        (by simpa using hw), hdrop, List.count_cons]
      by_cases hwj : w = nbrs[j]!
      · rw [getElemD_setD (by omega : nbrs[j]! < cnt.size) w, ite_eq_left hwj,
          ite_eq_left (by simp [hwj]), hwj]
        omega
      · rw [getElemD_setD_ne hwj, ite_eq_right (by simpa using fun h => hwj h.symm)]
        omega

/-- Unfolding lemma for the outer loop.  The definition destructures the inner loop's result
rather than projecting it (that is what keeps `cnt` unshared, see `Algorithm.lean`), and
definitional eta for structures makes the two forms interchangeable. -/
theorem countFrom_succ (G : Graph) (lab : Array Nat) (e fuel k : Nat) (cnt touched : Array Nat) :
    countFrom G lab e (fuel + 1) k cnt touched =
      if k ≥ e then (cnt, touched)
      else
        countFrom G lab e fuel (k + 1)
          (bumpFrom (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched).1
          (bumpFrom (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched).2 := by
  rw [countFrom]

/-- The counting phase only writes, never resizes. -/
theorem countFrom_size (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat),
      (countFrom G lab e fuel k cnt touched).1.size = cnt.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, cnt, touched => by
    rw [countFrom_succ]
    split
    · rfl
    · rw [countFrom_size G lab e fuel (k + 1) _ _, bumpFrom_size]

/-- The counting phase adds to `cnt[w]` one for every occurrence of `w` in a neighbour list of a
vertex sitting at a position in `[k, e)`. -/
theorem countFrom_getElemD (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat), e ≤ k + fuel → ∀ w, w < cnt.size →
      (countFrom G lab e fuel k cnt touched).1[w]!
        = cnt[w]! + ∑ i ∈ Finset.Ico k e, (G.nbr[lab[i]!]!).toList.count w
  | 0, k, cnt, touched, hf, w, hw => by
    rw [countFrom, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    simp
  | fuel + 1, k, cnt, touched, hf, w, hw => by
    rw [countFrom_succ]
    split
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      simp
    · rename_i hk
      have hsplit : ∑ i ∈ Finset.Ico k e, (G.nbr[lab[i]!]!).toList.count w
          = (G.nbr[lab[k]!]!).toList.count w
            + ∑ i ∈ Finset.Ico (k + 1) e, (G.nbr[lab[i]!]!).toList.count w :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [countFrom_getElemD G lab e fuel (k + 1) _ _ (by omega) w
          (by rw [bumpFrom_size]; exact hw),
        bumpFrom_getElemD (G.nbr[lab[k]!]!) (G.nbr[lab[k]!]!).size 0 cnt touched (by omega) w hw,
        List.drop_zero, hsplit]
      omega

/-- Neighbour lists of `Graph.ofOracle` are duplicate-free, so a vertex occurs in one at most
once.  This is what turns the multiplicities counted above into a `0`/`1` adjacency test. -/
theorem ofOracle_nbr_count (n : Nat) (f : Nat → Nat → Bool) (u v : Nat) (hu : u < n) (hv : v < n) :
    (Graph.ofOracle n f).nbr[u]!.toList.count v = if f u v then 1 else 0 := by
  rw [ofOracle_nbr n f u hu,
    show ((Array.range n).filter (f u)).toList = (List.range n).filter (f u) by simp]
  by_cases h : f u v
  · rw [ite_eq_left h, List.count_filter h, List.count_range, ite_eq_left hv]
  · rw [ite_eq_right h, List.count_eq_zero_of_not_mem]
    simp [h]

/-- **What the counting phase computes.**  Run from cleared scratch over the cell starting at
position `s`, `countFrom` leaves `cnt[w]` holding the number of vertices of that cell adjacent to
`w` — that is, exactly `cellCount n p s (· is adjacent to w)`.

With `cellCount_equiv`, which says that quantity is invariant, this says the loop computes an
invariant. -/
theorem countFrom_cellCount {n : Nat} (f : Nat → Nat → Bool) {p : Part} (hp : Part.WF n p)
    {s : Nat} (hs : s < n) (hcst : p.cst[s]! = s) {w : Nat} (hw : w < n) :
    (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[w]!
      = cellCount n p s (fun u => f u w) := by
  set e := p.cen[s]! with he
  have hsE : s < e := he ▸ hp.ltCen s hs
  have hEn : e ≤ n := he ▸ hp.cenLe s hs
  have hsz : (Array.replicate n 0 : Array Nat).size = n := by simp
  rw [countFrom_getElemD _ _ _ _ _ _ _ (by omega) w (by rw [hsz]; exact hw),
    show (Array.replicate n 0 : Array Nat)[w]! = 0 by
      rw [getElem!_pos _ _ (by simpa using hw)]; simp,
    Nat.zero_add]
  have hterm : ∀ i ∈ Finset.Ico s e,
      ((Graph.ofOracle n f).nbr[p.lab[i]!]!).toList.count w = if f p.lab[i]! w then 1 else 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ofOracle_nbr_count n f _ w (hp.labLt i (by omega)) hw
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  -- What is left is a bijection: positions of the cell ↔ vertices of the cell.
  refine Finset.card_bij (fun i _ => p.lab[i]!) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i (by omega), ?_, hi.2⟩
    rw [hp.posLab i (by omega)]
    have := hp.cellCst s hs i (by rw [hcst]; omega) (by omega)
    rw [this, hcst]
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    have hab' : p.lab[a]! = p.lab[b]! := hab
    have h1 := hp.posLab a (by omega)
    have h2 := hp.posLab b (by omega)
    rw [hab', h2] at h1
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    refine ⟨p.pos[u]!, ?_, hp.labPos u hu.1⟩
    have hpu : p.pos[u]! < n := hp.posLt u hu.1
    have hmem := (hp.cst_eq_iff hs hpu).1 (by rw [hu.2.1, hcst])
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rw [hcst] at hmem
    exact ⟨⟨hmem.1, hmem.2⟩, by rw [hp.labPos u hu.1]; exact hu.2.2⟩

/-- **The counting phase of `refineStep` is equivariant.**  Putting the two halves together: in
two runs whose partitions correspond under `σ`, the count the `f`-run records at `σ w` is the one
the `f ∘ σ`-run records at `w`.  Note the cells need only correspond as sets — the two runs walk
them in different orders, and the proof goes through `cellCount` precisely to avoid caring. -/
theorem countFrom_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {s : Nat} (hs : s < n) (hcst : q.cst[s]! = s) {w : Nat} (hw : w < n) :
    (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[σ w]!
      = (countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]! (q.cen[s]! - s) s
        (Array.replicate n 0) #[]).1[w]! := by
  rw [countFrom_cellCount f hp hs (by rw [h.cst s hs, hcst]) (hσ.maps w hw),
    countFrom_cellCount _ hq hs hcst hw]
  exact cellNbrCount_equiv hσ h f s w

/-- The invariant the counting phase maintains on its scratch space: `touched` lists exactly the
vertices whose count is nonzero, each once.

`refineStep` needs both halves.  Completeness is what makes the collected cells the right ones —
a cell met by the splitter has a member with a nonzero count, so it is represented.  Soundness
and no-repetition are what make the restore loop at the end of the step put the scratch back
*exactly*, in time proportional to what was dirtied rather than to `n`. -/
structure Touched (cnt touched : Array Nat) : Prop where
  /-- No vertex is recorded twice. -/
  nodup : touched.toList.Nodup
  /-- Only vertices are recorded. -/
  lt : ∀ w ∈ touched, w < cnt.size
  /-- Recorded is the same as counted. -/
  mem : ∀ w, w < cnt.size → (w ∈ touched ↔ cnt[w]! ≠ 0)

/-- Cleared scratch satisfies the invariant. -/
theorem touched_empty (cnt : Array Nat) (h : ∀ w, w < cnt.size → cnt[w]! = 0) :
    Touched cnt #[] :=
  ⟨by simp, by simp, fun w hw => by simp [h w hw]⟩

/-- The inner loop maintains the scratch invariant: it pushes a vertex exactly when it is raising
that vertex's count off zero.  The hypothesis on `nbrs` is needed — a neighbour outside `cnt`
would leave the count at the `getElem!` default of `0` and so be pushed on every visit. -/
theorem bumpFrom_touched (nbrs : Array Nat) : ∀ (fuel j : Nat) (cnt touched : Array Nat),
    (∀ x ∈ nbrs, x < cnt.size) → Touched cnt touched →
      Touched (bumpFrom nbrs fuel j cnt touched).1 (bumpFrom nbrs fuel j cnt touched).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, j, cnt, touched, hnb, ht => by
    rw [bumpFrom]
    split
    · exact ht
    · rename_i hj
      have hjs : j < nbrs.size := by omega
      have hv : nbrs[j]! < cnt.size := hnb _ (getElemD_mem hjs)
      have hsz : (cnt.set! nbrs[j]! (cnt[nbrs[j]!]! + 1)).size = cnt.size := by simp
      refine bumpFrom_touched nbrs fuel (j + 1) _ _ (by simpa [hsz] using hnb) ⟨?_, ?_, ?_⟩
      · split
        · rename_i hc
          have hnot : nbrs[j]! ∉ touched := fun hmem =>
            ((ht.mem _ hv).1 hmem) (by simpa using hc)
          rw [Array.toList_push]
          refine List.nodup_append.2 ⟨ht.nodup, by simp, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton] at hb
          subst hab
          subst hb
          exact hnot (by simpa using ha)
        · exact ht.nodup
      · intro w hw
        rw [hsz]
        split at hw
        · rcases Array.mem_push.1 hw with h | h
          · exact ht.lt w h
          · exact h ▸ hv
        · exact ht.lt w hw
      · intro w hw
        rw [hsz] at hw
        by_cases hwv : w = nbrs[j]!
        · subst hwv
          rw [getElemD_setD hv _, ite_eq_left rfl]
          simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, iff_true]
          split
          · exact Array.mem_push.2 (Or.inr rfl)
          · rename_i hc
            exact (ht.mem _ hw).2 (by simpa using hc)
        · rw [getElemD_setD_ne hwv]
          split
          · rw [Array.mem_push]
            simp only [hwv, or_false]
            exact ht.mem w hw
          · exact ht.mem w hw

/-- The outer loop maintains the scratch invariant. -/
theorem countFrom_touched (G : Graph) (lab : Array Nat) (e : Nat) :
    ∀ (fuel k : Nat) (cnt touched : Array Nat),
      (∀ (u x : Nat), x ∈ G.nbr[u]! → x < cnt.size) → Touched cnt touched →
        Touched (countFrom G lab e fuel k cnt touched).1
          (countFrom G lab e fuel k cnt touched).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, k, cnt, touched, hG, ht => by
    rw [countFrom_succ]
    split
    · exact ht
    · refine countFrom_touched G lab e fuel (k + 1) _ _ ?_
        (bumpFrom_touched _ _ _ _ _ (fun x hx => hG lab[k]! x hx) ht)
      intro u x hx
      rw [bumpFrom_size]
      exact hG u x hx

/-- The counting phase as `refineStep` actually calls it, from cleared scratch. -/
theorem countFrom_touched_spec {n : Nat} (f : Nat → Nat → Bool) (lab : Array Nat) (e s : Nat) :
    Touched (countFrom (Graph.ofOracle n f) lab e (e - s) s (Array.replicate n 0) #[]).1
      (countFrom (Graph.ofOracle n f) lab e (e - s) s (Array.replicate n 0) #[]).2 :=
  countFrom_touched _ _ _ _ _ _ _
    (fun u x hx => by simpa using ofOracle_nbr_lt' n f u x hx)
    (touched_empty _ fun w hw => by rw [getElem!_pos (Array.replicate n 0) w hw]; simp)

/-- **The vertices the counting phase records form an invariant set.**  `touched` is exactly the
set of vertices that the splitter cell reaches, and membership is stated in terms of `cellCount`,
which `cellCount_equiv` shows corresponding runs agree on.

The *order* of `touched` is not invariant — it is first-touch order, which depends on vertex
names.  That is why `refineStep` maps it to cell starts and sorts before using it. -/
theorem countFrom_mem_touched {n : Nat} (f : Nat → Nat → Bool) {p : Part} (hp : Part.WF n p)
    {s : Nat} (hs : s < n) (hcst : p.cst[s]! = s) {w : Nat} (hw : w < n) :
    w ∈ (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]).2 ↔ cellCount n p s (fun u => f u w) ≠ 0 := by
  rw [(countFrom_touched_spec f p.lab p.cen[s]! s).mem w
      (by rw [countFrom_size]; simpa using hw),
    countFrom_cellCount f hp hs hcst hw]

/-! ### Collecting the cells met by the splitter

Phase (2) of `refineStep` turns the touched vertices into the list of cells that have to be split.
Its output has to be canonical in a stronger sense than phase (1)'s: not just the same *set* of
cells in both runs, but the same *array*, since the step then processes them in order.  That is
what the sort is for, and why `sortNats` goes through `List.mergeSort` rather than `Array.qsort` —
`qsort` has no specification in this toolchain, and an unspecified order is exactly what cannot be
tolerated here.  `sortNats_ext` is the punchline of the sorting half ("duplicate-free arrays with
the same elements sort alike"), `collect_equiv` of the whole phase.
-/

/-- Sorting a `List` and sorting the `Array` of the same elements agree. -/
@[simp] theorem sortNats_toList (a : Array Nat) :
    (sortNats a).toList = a.toList.mergeSort (fun x y => x ≤ y) := by
  simp [sortNats]

theorem sortNats_perm (a : Array Nat) : (sortNats a).toList.Perm a.toList := by
  rw [sortNats_toList]
  exact List.mergeSort_perm _ _

theorem sortNats_pairwise (a : Array Nat) : (sortNats a).toList.Pairwise (· ≤ ·) := by
  rw [sortNats_toList]
  have := List.pairwise_mergeSort (le := fun x y : Nat => x ≤ y)
    (fun a b c hab hbc => by simpa using le_trans (by simpa using hab) (by simpa using hbc))
    (fun a b => by simpa using le_total a b) a.toList
  simpa using this

theorem sortNats_mem {a : Array Nat} {c : Nat} : c ∈ sortNats a ↔ c ∈ a := by
  rw [← Array.mem_toList_iff, ← Array.mem_toList_iff]
  exact (sortNats_perm a).mem_iff

/-- **Sorting normalises.**  Two duplicate-free arrays with the same elements sort to the same
array; this is what makes the list of cells met by a splitter canonical. -/
theorem sortNats_ext {a b : Array Nat} (ha : a.toList.Nodup) (hb : b.toList.Nodup)
    (h : ∀ c, c ∈ a ↔ c ∈ b) : sortNats a = sortNats b := by
  have hperm : (sortNats a).toList.Perm (sortNats b).toList :=
    ((sortNats_perm a).trans
      (List.perm_of_nodup_nodup_toFinset_eq ha hb (by
        ext c
        simpa using h c))).trans (sortNats_perm b).symm
  refine Array.ext' (List.Perm.eq_of_pairwise ?_ (sortNats_pairwise a) (sortNats_pairwise b) hperm)
  intro x y _ _ hxy hyx
  exact le_antisymm hxy hyx


/-- The scratch invariant of the collection phase: `cells` lists exactly the cell starts marked
in `hit`, each once.  The analogue of `Touched` for phase (2). -/
structure Collected (hit : Array Bool) (cells : Array Nat) : Prop where
  /-- No cell is collected twice — this is what `hit` is for. -/
  nodup : cells.toList.Nodup
  /-- Collected cells are in range. -/
  lt : ∀ c ∈ cells, c < hit.size
  /-- `hit` marks exactly the collected cells. -/
  mem : ∀ c, c < hit.size → (c ∈ cells ↔ hit[c]! = true)

theorem collected_empty (hit : Array Bool) (h : ∀ c, c < hit.size → hit[c]! = false) :
    Collected hit #[] :=
  ⟨by simp, by simp, fun c hc => by simp [h c hc]⟩

/-- Marking and pushing an unmarked cell preserves the invariant. -/
theorem Collected.push {hit : Array Bool} {cells : Array Nat} (h : Collected hit cells) {c : Nat}
    (hc : c < hit.size) (hf : hit[c]! = false) : Collected (hit.set! c true) (cells.push c) := by
  have hsz : (hit.set! c true).size = hit.size := by simp
  have hnot : c ∉ cells := fun hmem => by rw [(h.mem c hc).1 hmem] at hf; exact Bool.noConfusion hf
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.toList_push]
    refine List.nodup_append.2 ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hab
    subst hb
    exact hnot (by simpa using ha)
  · intro w hw
    rw [hsz]
    rcases Array.mem_push.1 hw with hw | hw
    · exact h.lt w hw
    · exact hw ▸ hc
  · intro w hw
    rw [hsz] at hw
    by_cases hwc : w = c
    · subst hwc
      rw [getElemD_setD hc _, ite_eq_left rfl, Array.mem_push]
      simp
    · rw [getElemD_setD_ne hwc, Array.mem_push]
      simp only [hwc, or_false]
      exact h.mem w hw

theorem collectFrom_collected (pos cst touched : Array Nat) :
    ∀ (fuel j : Nat) (hit : Array Bool) (cells : Array Nat),
      (∀ v ∈ touched, cst[pos[v]!]! < hit.size) → Collected hit cells →
        Collected (collectFrom pos cst touched fuel j hit cells).1
          (collectFrom pos cst touched fuel j hit cells).2
  | 0, _, _, _, _, hc => hc
  | fuel + 1, j, hit, cells, hb, hc => by
    rw [collectFrom]
    split
    · exact hc
    · rename_i hj
      have hjs : j < touched.size := by omega
      have hlt : cst[pos[touched[j]!]!]! < hit.size := hb _ (getElemD_mem hjs)
      dsimp only
      split
      · exact collectFrom_collected pos cst touched fuel (j + 1) hit cells hb hc
      · rename_i hf
        refine collectFrom_collected pos cst touched fuel (j + 1) _ _ (by simpa using hb)
          (hc.push hlt (by simpa using hf))

/-- **What the collection phase collects**: exactly the cell starts of the vertices it is given,
each once (the `Nodup` half is `collectFrom_collected`). -/
theorem collectFrom_mem (pos cst touched : Array Nat) :
    ∀ (fuel j : Nat) (hit : Array Bool) (cells : Array Nat), touched.size ≤ j + fuel →
      (∀ v ∈ touched, cst[pos[v]!]! < hit.size) → Collected hit cells → ∀ c,
        (c ∈ (collectFrom pos cst touched fuel j hit cells).2 ↔
          c ∈ cells ∨ ∃ v ∈ touched.toList.drop j, cst[pos[v]!]! = c)
  | 0, j, hit, cells, hf, _, _, c => by
    rw [collectFrom, List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | fuel + 1, j, hit, cells, hf, hb, hc, c => by
    rw [collectFrom]
    split
    · rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp
    · rename_i hj
      have hjs : j < touched.size := by omega
      have hlt : cst[pos[touched[j]!]!]! < hit.size := hb _ (getElemD_mem hjs)
      have hdrop : touched.toList.drop j = touched[j]! :: touched.toList.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hjs), getElem!_pos touched j hjs,
          Array.getElem_toList]
      dsimp only
      split
      · rename_i hhit
        rw [collectFrom_mem pos cst touched fuel (j + 1) hit cells (by omega) hb hc c, hdrop]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by simpa using Or.inr h)
        · rintro (h | h)
          · exact Or.inl h
          · rcases (by simpa using h) with h | h
            · exact Or.inl (h ▸ (hc.mem _ hlt).2 hhit)
            · exact Or.inr h
      · rename_i hhit
        rw [collectFrom_mem pos cst touched fuel (j + 1) _ _ (by omega) (by simpa using hb)
          (hc.push hlt (by simpa using hhit)) c, hdrop, Array.mem_push]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (by simp [h])
          · exact Or.inr (by simpa using Or.inr h)
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · rcases (by simpa using h) with h | h
            · exact Or.inl (Or.inr h.symm)
            · exact Or.inr h

/-- The collection phase as `refineStep` runs it: from an all-clear `hit`, it collects exactly the
cells that the touched vertices lie in. -/
theorem collect_mem {n : Nat} {p : Part} (hp : Part.WF n p) {touched : Array Nat}
    (htn : ∀ v ∈ touched, v < n) {hit : Array Bool} (hsz : hit.size = n)
    (hf0 : ∀ c, c < n → hit[c]! = false) (c : Nat) :
    c ∈ (collectFrom p.pos p.cst touched touched.size 0 hit #[]).2 ↔
      ∃ v ∈ touched, p.cst[p.pos[v]!]! = c := by
  have hbd : ∀ v ∈ touched, p.cst[p.pos[v]!]! < hit.size := by
    intro v hv
    have h1 : p.pos[v]! < n := hp.posLt v (htn v hv)
    have h2 : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1
    omega
  rw [collectFrom_mem p.pos p.cst touched touched.size 0 hit #[] (by omega) hbd
    (collected_empty hit fun c hc => hf0 c (by omega)) c]
  simp

theorem collect_nodup {n : Nat} {p : Part} (hp : Part.WF n p) {touched : Array Nat}
    (htn : ∀ v ∈ touched, v < n) {hit : Array Bool} (hsz : hit.size = n)
    (hf0 : ∀ c, c < n → hit[c]! = false) :
    (collectFrom p.pos p.cst touched touched.size 0 hit #[]).2.toList.Nodup := by
  refine (collectFrom_collected p.pos p.cst touched touched.size 0 hit #[] ?_
    (collected_empty hit fun c hc => hf0 c (by omega))).nodup
  intro v hv
  have h1 : p.pos[v]! < n := hp.posLt v (htn v hv)
  have h2 : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1
  omega

/-- Every vertex the counting phase touches is a vertex. -/
theorem countFrom_touched_lt {n : Nat} (f : Nat → Nat → Bool) (lab : Array Nat) (e s : Nat)
    {v : Nat} (hv : v ∈ (countFrom (Graph.ofOracle n f) lab e (e - s) s
      (Array.replicate n 0) #[]).2) : v < n := by
  have := (countFrom_touched_spec f lab e s).lt v hv
  rwa [countFrom_size, Array.size_replicate] at this

/-- **Phase (2) of `refineStep` is equivariant.**  The two runs meet the same cells, in the same
order: the cells are the same *positions* because `PartEquiv` matches cell boundaries, and the
sort makes the order depend on nothing but the set. -/
theorem collect_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {s : Nat} (hs : s < n) (hcst : q.cst[s]! = s)
    {hit : Array Bool} (hsz : hit.size = n) (hf0 : ∀ c, c < n → hit[c]! = false)
    {tp tq : Array Nat}
    (htp : tp = (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[]).2)
    (htq : tq = (countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]!
      (q.cen[s]! - s) s (Array.replicate n 0) #[]).2) :
    sortNats (collectFrom p.pos p.cst tp tp.size 0 hit #[]).2
      = sortNats (collectFrom q.pos q.cst tq tq.size 0 hit #[]).2 := by
  have hcstp : p.cst[s]! = s := by rw [h.cst s hs, hcst]
  have htpn : ∀ v ∈ tp, v < n := fun v hv => countFrom_touched_lt f p.lab _ s (htp ▸ hv)
  have htqn : ∀ v ∈ tq, v < n := fun v hv => countFrom_touched_lt _ q.lab _ s (htq ▸ hv)
  -- Membership of the two touched sets corresponds along `σ`.
  have hmemp : ∀ v, v < n → (v ∈ tp ↔ cellCount n p s (fun u => f u v) ≠ 0) := by
    intro v hv
    rw [htp]
    exact countFrom_mem_touched f hp hs hcstp hv
  have hmemq : ∀ w, w < n → (w ∈ tq ↔ cellCount n q s (fun u => f (σ u) (σ w)) ≠ 0) := by
    intro w hw
    rw [htq]
    exact countFrom_mem_touched _ hq hs hcst hw
  refine sortNats_ext (collect_nodup hp htpn hsz hf0) (collect_nodup hq htqn hsz hf0) ?_
  intro c
  rw [collect_mem hp htpn hsz hf0, collect_mem hq htqn hsz hf0]
  constructor
  · rintro ⟨v, hv, hc⟩
    obtain ⟨w, hw, rfl⟩ := hσ.surj (htpn v hv)
    refine ⟨w, (hmemq w hw).2 ?_, ?_⟩
    · rw [← cellNbrCount_equiv hσ h f s w]
      exact (hmemp _ (hσ.maps w hw)).1 hv
    · rw [← h.cell w hw, hc]
  · rintro ⟨w, hw, hc⟩
    have hwn : w < n := htqn w hw
    refine ⟨σ w, (hmemp _ (hσ.maps w hwn)).2 ?_, ?_⟩
    · rw [cellNbrCount_equiv hσ h f s w]
      exact (hmemq w hwn).1 hw
    · rw [h.cell w hwn, hc]

/-! ### The counting sort

The heart of `refineStep`: each cell that the splitter met is sorted by neighbour count.  The
sort is a counting sort in five passes — count the buckets (`bucketFrom`), turn the counts into
offsets (`offsetFrom`), scatter the vertices into a block (`scatterFrom`), write the block back
(`writeFrom`), install the new fragment boundaries (`boundsFrom`) — and each pass gets its own
`getElem!` characterisation here.  The one substantial argument is `scatterFrom_block`: the
scatter writes each vertex to a distinct slot, which needs the buckets' offset ranges to be
disjoint (`Sep`) and is what makes the whole thing a permutation of the cell.
-/

/-- How many of the positions `[k, ec)` hold a vertex of neighbour count `t`. -/
def bucketSize (lab cnt : Array Nat) (k ec t : Nat) : Nat :=
  ∑ i ∈ Finset.Ico k ec, if cnt[lab[i]!]! = t then 1 else 0

theorem bucketSize_zero (lab cnt : Array Nat) {k ec t : Nat} (h : ec ≤ k) :
    bucketSize lab cnt k ec t = 0 := by
  rw [bucketSize, Finset.Ico_eq_empty (by omega), Finset.sum_empty]

theorem bucketSize_succ (lab cnt : Array Nat) {k ec t : Nat} (h : k < ec) :
    bucketSize lab cnt k ec t
      = (if cnt[lab[k]!]! = t then 1 else 0) + bucketSize lab cnt (k + 1) ec t :=
  Finset.sum_eq_sum_Ico_succ_bot h _

theorem bucketFrom_size (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), (bucketFrom lab cnt ec fuel k bc ks).1.size = bc.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, bc, ks => by
    rw [bucketFrom]
    split
    · rfl
    · rw [bucketFrom_size lab cnt ec fuel (k + 1) _ _]
      simp

theorem bucketFrom_getElemD (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), ec ≤ k + fuel → ∀ t, t < bc.size →
      (bucketFrom lab cnt ec fuel k bc ks).1[t]! = bc[t]! + bucketSize lab cnt k ec t
  | 0, k, bc, ks, hf, t, ht => by
    rw [bucketFrom, bucketSize_zero lab cnt (by omega)]
    simp
  | fuel + 1, k, bc, ks, hf, t, ht => by
    rw [bucketFrom]
    split
    · rw [bucketSize_zero lab cnt (by omega)]
      simp
    · rename_i hk
      have hlt : k < ec := by omega
      rw [bucketSize_succ lab cnt hlt]
      dsimp only
      rw [bucketFrom_getElemD lab cnt ec fuel (k + 1) _ _ (by omega) t (by simpa using ht)]
      by_cases hteq : t = cnt[lab[k]!]!
      · rw [getElemD_setD (by omega : cnt[lab[k]!]! < bc.size) t, ite_eq_left hteq,
          ite_eq_left (by simp [hteq]), hteq]
        omega
      · rw [getElemD_setD_ne hteq, ite_eq_right (by simpa using fun h => hteq h.symm)]
        omega

/-- The bucket table and the list of occurring counts satisfy the same invariant as the count
array and its touched list: `ks` lists exactly the counts with a nonzero bucket, each once. -/
theorem bucketFrom_touched (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (bc ks : Array Nat), (∀ (v : Nat), cnt[v]! < bc.size) → Touched bc ks →
      Touched (bucketFrom lab cnt ec fuel k bc ks).1 (bucketFrom lab cnt ec fuel k bc ks).2
  | 0, _, _, _, _, ht => ht
  | fuel + 1, k, bc, ks, hcb, ht => by
    rw [bucketFrom]
    split
    · exact ht
    · have hv : cnt[lab[k]!]! < bc.size := hcb _
      have hsz : (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)).size = bc.size := by simp
      dsimp only
      refine bucketFrom_touched lab cnt ec fuel (k + 1) _ _ (by simpa [hsz] using hcb) ⟨?_, ?_, ?_⟩
      · split
        · rename_i hc
          have hnot : cnt[lab[k]!]! ∉ ks := fun hmem => ((ht.mem _ hv).1 hmem) (by simpa using hc)
          rw [Array.toList_push]
          refine List.nodup_append.2 ⟨ht.nodup, by simp, ?_⟩
          intro a ha b hb hab
          rw [List.mem_singleton] at hb
          subst hab
          subst hb
          exact hnot (by simpa using ha)
        · exact ht.nodup
      · intro w hw
        rw [hsz]
        split at hw
        · rcases Array.mem_push.1 hw with h | h
          · exact ht.lt w h
          · exact h ▸ hv
        · exact ht.lt w hw
      · intro w hw
        rw [hsz] at hw
        by_cases hwv : w = cnt[lab[k]!]!
        · subst hwv
          rw [getElemD_setD hv _, ite_eq_left rfl]
          simp only [ne_eq, Nat.succ_ne_zero, not_false_eq_true, iff_true]
          split
          · exact Array.mem_push.2 (Or.inr rfl)
          · rename_i hc
            exact (ht.mem _ hw).2 (by simpa using hc)
        · rw [getElemD_setD_ne hwv]
          split
          · rw [Array.mem_push]
            simp only [hwv, or_false]
            exact ht.mem w hw
          · exact ht.mem w hw

/-- **What the bucketing phase collects**: exactly the counts that occur in the cell. -/
theorem bucket_mem {lab cnt bc : Array Nat} {c ec : Nat} (hcb : ∀ (v : Nat), cnt[v]! < bc.size)
    (hbc0 : ∀ t, t < bc.size → bc[t]! = 0) (t : Nat) :
    t ∈ (bucketFrom lab cnt ec (ec - c) c bc #[]).2 ↔
      t < bc.size ∧ bucketSize lab cnt c ec t ≠ 0 := by
  have hT : Touched (bucketFrom lab cnt ec (ec - c) c bc #[]).1
      (bucketFrom lab cnt ec (ec - c) c bc #[]).2 :=
    bucketFrom_touched lab cnt ec (ec - c) c bc #[] hcb
      (touched_empty bc fun w hw => hbc0 w hw)
  constructor
  · intro hmem
    have hlt : t < bc.size := by
      have := hT.lt t hmem
      rwa [bucketFrom_size] at this
    refine ⟨hlt, ?_⟩
    have := (hT.mem t (by rw [bucketFrom_size]; exact hlt)).1 hmem
    rwa [bucketFrom_getElemD lab cnt ec (ec - c) c bc #[] (by omega) t hlt, hbc0 t hlt,
      Nat.zero_add] at this
  · rintro ⟨hlt, hne⟩
    refine (hT.mem t (by rw [bucketFrom_size]; exact hlt)).2 ?_
    rw [bucketFrom_getElemD lab cnt ec (ec - c) c bc #[] (by omega) t hlt, hbc0 t hlt, Nat.zero_add]
    exact hne

/-- The bucket sizes are cell counts, so the vocabulary of step 1 applies to them: the same
position-to-vertex bijection as in `countFrom_cellCount`. -/
theorem bucketSize_cellCount {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (cnt : Array Nat) (t : Nat) :
    bucketSize p.lab cnt c p.cen[c]! t = cellCount n p c (fun u => cnt[u]! == t) := by
  have hcE : c < p.cen[c]! := hp.ltCen c hc
  have hEn : p.cen[c]! ≤ n := hp.cenLe c hc
  rw [bucketSize, ← Finset.sum_filter, ← Finset.card_eq_sum_ones, cellCount]
  refine Finset.card_bij (fun i _ => p.lab[i]!) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i (by omega), ?_, by simpa using hi.2⟩
    rw [hp.posLab i (by omega)]
    have := hp.cellCst c hc i (by rw [hcst]; omega) (by omega)
    rw [this, hcst]
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    have hab' : p.lab[a]! = p.lab[b]! := hab
    have h1 := hp.posLab a (by omega)
    have h2 := hp.posLab b (by omega)
    rw [hab', h2] at h1
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    refine ⟨p.pos[u]!, ?_, hp.labPos u hu.1⟩
    have hpu : p.pos[u]! < n := hp.posLt u hu.1
    have hmem := (hp.cst_eq_iff hc hpu).1 (by rw [hu.2.1, hcst])
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rw [hcst] at hmem
    exact ⟨⟨hmem.1, hmem.2⟩, by rw [hp.labPos u hu.1]; simpa using hu.2.2⟩

theorem offsetFrom_size1 (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat),
      (offsetFrom ks fuel j sizes bc acc).1.size = sizes.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc => by
    rw [offsetFrom]
    split
    · rfl
    · rw [offsetFrom_size1 ks fuel (j + 1) _ _ _]
      simp

theorem offsetFrom_size2 (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat),
      (offsetFrom ks fuel j sizes bc acc).2.size = bc.size
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc => by
    rw [offsetFrom]
    split
    · rfl
    · rw [offsetFrom_size2 ks fuel (j + 1) _ _ _]
      simp

/-- The pass writes only at the indices named in `ks[j:]`. -/
theorem offsetFrom_ne (ks : Array Nat) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc x : Nat),
      (∀ i, j ≤ i → i < ks.size → x ≠ ks[i]!) → (offsetFrom ks fuel j sizes bc acc).2[x]! = bc[x]!
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, sizes, bc, acc, x, hx => by
    rw [offsetFrom]
    split
    · rfl
    · rename_i hj
      rw [offsetFrom_ne ks fuel (j + 1) _ _ _ x (fun i h1 h2 => hx i (by omega) h2),
        getElemD_setD_ne (hx j (by omega) (by omega))]

/-- **The fragment sizes**: `sizes[j]` is the size of the bucket of the `j`-th count. -/
theorem offsetFrom_sizes (ks : Array Nat) (hnd : ks.toList.Nodup) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat), ks.size ≤ j + fuel →
      sizes.size = ks.size → ∀ i, i < ks.size →
        (offsetFrom ks fuel j sizes bc acc).1[i]! = if i < j then sizes[i]! else bc[ks[i]!]!
  | 0, j, sizes, bc, acc, hf, hsz, i, hi => by
    rw [offsetFrom, ite_eq_left (by omega)]
  | fuel + 1, j, sizes, bc, acc, hf, hsz, i, hi => by
    rw [offsetFrom]
    split
    · rw [ite_eq_left (by omega)]
    · rename_i hj
      rw [offsetFrom_sizes ks hnd fuel (j + 1) _ _ _ (by omega) (by simpa using hsz) i hi]
      rcases Nat.lt_trichotomy i j with h | h | h
      · rw [ite_eq_left (by omega), ite_eq_left h, getElemD_setD_ne (by omega : i ≠ j)]
      · subst h
        rw [ite_eq_left (by omega), ite_eq_right (by omega),
          getElemD_setD (by omega : i < sizes.size) i, ite_eq_left rfl]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          getElemD_setD_ne (nodup_getElemD_ne hnd hi (by omega) (by omega))]

/-- **The fragment offsets**: after the pass, the bucket of the `i`-th count starts at the sum of
the sizes of the buckets before it. -/
theorem offsetFrom_bc (ks : Array Nat) (hnd : ks.toList.Nodup) :
    ∀ (fuel j : Nat) (sizes bc : Array Nat) (acc : Nat), ks.size ≤ j + fuel →
      (∀ i, i < ks.size → ks[i]! < bc.size) → ∀ i, j ≤ i → i < ks.size →
        (offsetFrom ks fuel j sizes bc acc).2[ks[i]!]!
          = acc + ∑ i' ∈ Finset.Ico j i, bc[ks[i']!]!
  | 0, j, sizes, bc, acc, hf, hks, i, hji, hi => by omega
  | fuel + 1, j, sizes, bc, acc, hf, hks, i, hji, hi => by
    rw [offsetFrom]
    split
    · omega
    · rename_i hj
      rcases Nat.eq_or_lt_of_le hji with h | h
      · subst h
        rw [Finset.Ico_self, Finset.sum_empty, Nat.add_zero,
          offsetFrom_ne ks fuel (j + 1) _ _ _ _
            (fun i' h1 h2 => nodup_getElemD_ne hnd hi h2 (by omega)),
          getElemD_setD (hks j hi) _, ite_eq_left rfl]
        omega
      · have hsplit : ∑ i' ∈ Finset.Ico j i, bc[ks[i']!]!
            = bc[ks[j]!]! + ∑ i' ∈ Finset.Ico (j + 1) i, bc[ks[i']!]! :=
          Finset.sum_eq_sum_Ico_succ_bot h _
        have hterm : ∀ i' ∈ Finset.Ico (j + 1) i,
            (bc.set! ks[j]! acc)[ks[i']!]! = bc[ks[i']!]! := by
          intro i' hi'
          rw [Finset.mem_Ico] at hi'
          exact getElemD_setD_ne (nodup_getElemD_ne hnd (by omega) (by omega) (by omega))
        rw [offsetFrom_bc ks hnd fuel (j + 1) _ _ _ (by omega) (by simpa using hks) i (by omega) hi,
          Finset.sum_congr rfl hterm, hsplit]
        omega

theorem bucketSize_split (lab cnt : Array Nat) {k i ec t : Nat} (h1 : k ≤ i) (h2 : i ≤ ec) :
    bucketSize lab cnt k ec t = bucketSize lab cnt k i t + bucketSize lab cnt i ec t := by
  rw [bucketSize, bucketSize, bucketSize, Finset.sum_Ico_consecutive _ h1 h2]

theorem bucketSize_mono (lab cnt : Array Nat) {k i ec t : Nat} (h1 : k ≤ i) (h2 : i ≤ ec) :
    bucketSize lab cnt i ec t ≤ bucketSize lab cnt k ec t := by
  rw [bucketSize_split lab cnt h1 h2]
  omega

theorem bucketSize_pos (lab cnt : Array Nat) {k ec t : Nat} (h : k < ec)
    (ht : cnt[lab[k]!]! = t) : 0 < bucketSize lab cnt k ec t := by
  rw [bucketSize_succ lab cnt h, ite_eq_left ht]
  omega

theorem scatterFrom_size1 (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat),
      (scatterFrom lab cnt ec fuel k block bc).1.size = block.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, block, bc => by
    rw [scatterFrom]
    split
    · rfl
    · rw [scatterFrom_size1 lab cnt ec fuel (k + 1) _ _]
      simp

theorem scatterFrom_size2 (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat),
      (scatterFrom lab cnt ec fuel k block bc).2.size = bc.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, block, bc => by
    rw [scatterFrom]
    split
    · rfl
    · rw [scatterFrom_size2 lab cnt ec fuel (k + 1) _ _]
      simp

/-- The offset the scatter writes the vertex at position `i` to, as seen from position `k`: the
bucket's current offset plus the number of items of the same count already scattered. -/
def scatterAt (lab cnt bc : Array Nat) (k i : Nat) : Nat :=
  bc[cnt[lab[i]!]!]! + bucketSize lab cnt k i (cnt[lab[i]!]!)

/-- Taking one step leaves every later item's target offset where it was: the bucket that just
grew also advanced by one. -/
theorem scatterAt_step (lab cnt bc : Array Nat) {k i : Nat} (hk : k < i)
    (hb : cnt[lab[k]!]! < bc.size) :
    scatterAt lab cnt (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)) (k + 1) i
      = scatterAt lab cnt bc k i := by
  rw [scatterAt, scatterAt, bucketSize_succ lab cnt hk]
  by_cases h : cnt[lab[i]!]! = cnt[lab[k]!]!
  · rw [h, getElemD_setD hb _, ite_eq_left rfl, ite_eq_left rfl]
    omega
  · rw [getElemD_setD_ne h, ite_eq_right (by simpa using fun h' => h h'.symm)]
    omega

/-- The scatter writes only at the offsets its remaining items name. -/
theorem scatterFrom_ne (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat) (o : Nat), (∀ (v : Nat), cnt[v]! < bc.size) →
      (∀ i, k ≤ i → i < ec → scatterAt lab cnt bc k i ≠ o) →
        (scatterFrom lab cnt ec fuel k block bc).1[o]! = block[o]!
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, k, block, bc, o, hcb, ho => by
    rw [scatterFrom]
    split
    · rfl
    · rename_i hk
      have hne : bc[cnt[lab[k]!]!]! ≠ o := by
        have := ho k (by omega) (by omega)
        rwa [scatterAt, bucketSize_zero lab cnt (by omega), Nat.add_zero] at this
      rw [scatterFrom_ne lab cnt ec fuel (k + 1) _ _ o (by simpa using hcb) ?_,
        getElemD_setD_ne (by simpa using fun h => hne h.symm)]
      intro i h1 h2
      rw [scatterAt_step lab cnt bc (by omega) (hcb _)]
      exact ho i (by omega) h2

/-- The buckets do not overlap: distinct counts have disjoint offset ranges, each as wide as the
number of items still to be scattered into it. -/
def Sep (lab cnt : Array Nat) (k ec : Nat) (bc : Array Nat) : Prop :=
  ∀ t t' : Nat, t ≠ t' → ∀ a b : Nat, a < bucketSize lab cnt k ec t →
    b < bucketSize lab cnt k ec t' → bc[t]! + a ≠ bc[t']! + b

theorem Sep.step {lab cnt bc : Array Nat} {k ec : Nat} (h : Sep lab cnt k ec bc) (hk : k < ec)
    (hb : cnt[lab[k]!]! < bc.size) :
    Sep lab cnt (k + 1) ec (bc.set! cnt[lab[k]!]! (bc[cnt[lab[k]!]!]! + 1)) := by
  intro t t' htt a b ha hb'
  have hmono : ∀ u : Nat, bucketSize lab cnt (k + 1) ec u ≤ bucketSize lab cnt k ec u :=
    fun u => bucketSize_mono lab cnt (by omega) (by omega)
  have hstep : ∀ u : Nat, bucketSize lab cnt k ec u
      = (if cnt[lab[k]!]! = u then 1 else 0) + bucketSize lab cnt (k + 1) ec u :=
    fun u => bucketSize_succ lab cnt hk
  by_cases ht0 : t = cnt[lab[k]!]!
  · have ht0' : t' ≠ cnt[lab[k]!]! := fun h' => htt (ht0.trans h'.symm)
    rw [getElemD_setD hb t, ite_eq_left ht0, getElemD_setD_ne ht0', ← ht0]
    have h1 : a + 1 < bucketSize lab cnt k ec t := by
      have := hstep t
      rw [ite_eq_left ht0.symm] at this
      omega
    have := h t t' htt (a + 1) b h1 (by have := hmono t'; omega)
    omega
  · by_cases ht0' : t' = cnt[lab[k]!]!
    · rw [getElemD_setD_ne ht0, getElemD_setD hb t', ite_eq_left ht0', ← ht0']
      have h1 : b + 1 < bucketSize lab cnt k ec t' := by
        have := hstep t'
        rw [ite_eq_left ht0'.symm] at this
        omega
      have := h t t' htt a (b + 1) (by have := hmono t; omega) h1
      omega
    · rw [getElemD_setD_ne ht0, getElemD_setD_ne ht0']
      exact h t t' htt a b (by have := hmono t; omega) (by have := hmono t'; omega)

/-- **Where the scatter puts each vertex.**  The vertex at position `i` of the cell lands at its
bucket's offset plus the number of same-count vertices before it — a stable counting sort. -/
theorem scatterFrom_block (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat), ec ≤ k + fuel → (∀ (v : Nat), cnt[v]! < bc.size) →
      Sep lab cnt k ec bc → (∀ i, k ≤ i → i < ec → scatterAt lab cnt bc k i < block.size) →
        ∀ i, k ≤ i → i < ec →
          (scatterFrom lab cnt ec fuel k block bc).1[scatterAt lab cnt bc k i]! = lab[i]!
  | 0, k, block, bc, hf, _, _, _, i, h1, h2 => by omega
  | fuel + 1, k, block, bc, hf, hcb, hsep, hrange, i, h1, h2 => by
    rw [scatterFrom]
    split
    · omega
    · rename_i hk
      have hbk : cnt[lab[k]!]! < bc.size := hcb _
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · -- the vertex written now: no later write lands on the offset it just took
        subst h
        have hbsz : bc[cnt[lab[k]!]!]! < block.size := by
          have := hrange k (le_refl k) (by omega)
          rwa [scatterAt, bucketSize_zero lab cnt (le_refl k), Nat.add_zero] at this
        rw [scatterAt, bucketSize_zero lab cnt (le_refl k), Nat.add_zero,
          scatterFrom_ne lab cnt ec fuel (k + 1) _ _ _ (by simpa using hcb) ?_,
          getElemD_setD hbsz _, ite_eq_left (Nat.add_zero _)]
        intro i' h1' h2'
        rw [scatterAt_step lab cnt bc (by omega) hbk, scatterAt]
        by_cases ht : cnt[lab[i']!]! = cnt[lab[k]!]!
        · rw [ht]
          have : 0 < bucketSize lab cnt k i' cnt[lab[k]!]! :=
            bucketSize_pos lab cnt (by omega) rfl
          omega
        · have hb1 : bucketSize lab cnt k i' cnt[lab[i']!]!
              < bucketSize lab cnt k ec cnt[lab[i']!]! := by
            rw [bucketSize_split lab cnt (show k ≤ i' by omega) (show i' ≤ ec by omega)]
            have := bucketSize_pos lab cnt (k := i') (ec := ec) (t := cnt[lab[i']!]!)
              (by omega) rfl
            omega
          have hb2 : 0 < bucketSize lab cnt k ec cnt[lab[k]!]! :=
            bucketSize_pos lab cnt (by omega) rfl
          exact hsep _ _ ht _ 0 hb1 hb2
      · rw [← scatterAt_step lab cnt bc h hbk]
        refine scatterFrom_block lab cnt ec fuel (k + 1) _ _ (by omega) (by simpa using hcb)
          (hsep.step (by omega) hbk) ?_ i (by omega) h2
        intro i' h1' h2'
        rw [scatterAt_step lab cnt bc (by omega) hbk]
        simpa using hrange i' (by omega) h2'

/-! ### Writing the sorted block back -/

theorem writeFrom_size1 (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), (writeFrom block c fuel k lab pos).1.size = lab.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, lab, pos => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_size1 block c fuel (k + 1) _ _]
      simp

theorem writeFrom_size2 (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), (writeFrom block c fuel k lab pos).2.size = pos.size
  | 0, _, _, _ => rfl
  | fuel + 1, k, lab, pos => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_size2 block c fuel (k + 1) _ _]
      simp

/-- Positions outside the cell keep their label. -/
theorem writeFrom_lab_ne (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat) (x : Nat), (x < c + k ∨ c + block.size ≤ x) →
      (writeFrom block c fuel k lab pos).1[x]! = lab[x]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, lab, pos, x, hx => by
    rw [writeFrom]
    split
    · rfl
    · rw [writeFrom_lab_ne block c fuel (k + 1) _ _ x (by omega),
        getElemD_setD_ne (by omega : x ≠ c + k)]

/-- The block is laid down at positions `c, c+1, …`. -/
theorem writeFrom_lab (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), block.size ≤ k + fuel → c + block.size ≤ lab.size →
      ∀ m, k ≤ m → m < block.size → (writeFrom block c fuel k lab pos).1[c + m]! = block[m]!
  | 0, k, lab, pos, hf, _, m, h1, h2 => by omega
  | fuel + 1, k, lab, pos, hf, hlab, m, h1, h2 => by
    rw [writeFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        rw [writeFrom_lab_ne block c fuel (k + 1) _ _ _ (by omega),
          getElemD_setD (by omega) _, ite_eq_left rfl]
      · exact writeFrom_lab block c fuel (k + 1) _ _ (by omega) (by simpa using hlab) m
          (by omega) h2

/-- Vertices the block does not mention keep their position. -/
theorem writeFrom_pos_ne (block : Array Nat) (c : Nat) :
    ∀ (fuel k : Nat) (lab pos : Array Nat) (v : Nat),
      (∀ m, k ≤ m → m < block.size → block[m]! ≠ v) →
        (writeFrom block c fuel k lab pos).2[v]! = pos[v]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, lab, pos, v, hv => by
    rw [writeFrom]
    split
    · rfl
    · rename_i hk
      rw [writeFrom_pos_ne block c fuel (k + 1) _ _ v (fun m h1 h2 => hv m (by omega) h2),
        getElemD_setD_ne (Ne.symm (hv k (by omega) (by omega)))]

/-- **Where each vertex of the block ends up.**  The block has no repeats, so the write that
places a vertex is the only one that touches its position. -/
theorem writeFrom_pos (block : Array Nat) (c : Nat) (hnd : block.toList.Nodup) :
    ∀ (fuel k : Nat) (lab pos : Array Nat), block.size ≤ k + fuel →
      (∀ m, m < block.size → block[m]! < pos.size) →
        ∀ m, k ≤ m → m < block.size → (writeFrom block c fuel k lab pos).2[block[m]!]! = c + m
  | 0, k, lab, pos, hf, _, m, h1, h2 => by omega
  | fuel + 1, k, lab, pos, hf, hp, m, h1, h2 => by
    rw [writeFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        rw [writeFrom_pos_ne block c fuel (k + 1) _ _ _
            (fun m' h1' h2' => nodup_getElemD_ne hnd h2' h2 (by omega)),
          getElemD_setD (hp k h2) _, ite_eq_left rfl]
      · exact writeFrom_pos block c hnd fuel (k + 1) _ _ (by omega) (by simpa using hp) m
          (by omega) h2

/-! ### The fragment boundaries -/

theorem fillBoundsFrom_size1 (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    (fillBoundsFrom st en fuel i cst cen).1.size = cst.size
  | 0, _, _, _ => rfl
  | fuel + 1, i, cst, cen => by
    rw [fillBoundsFrom]
    split
    · rfl
    · rw [fillBoundsFrom_size1 st en fuel (i + 1) _ _]
      simp

theorem fillBoundsFrom_size2 (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    (fillBoundsFrom st en fuel i cst cen).2.size = cen.size
  | 0, _, _, _ => rfl
  | fuel + 1, i, cst, cen => by
    rw [fillBoundsFrom]
    split
    · rfl
    · rw [fillBoundsFrom_size2 st en fuel (i + 1) _ _]
      simp

theorem fillBoundsFrom_ne (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat) (x : Nat),
    (x < i ∨ en ≤ x) → (fillBoundsFrom st en fuel i cst cen).1[x]! = cst[x]!
      ∧ (fillBoundsFrom st en fuel i cst cen).2[x]! = cen[x]!
  | 0, _, _, _, _, _ => ⟨rfl, rfl⟩
  | fuel + 1, i, cst, cen, x, hx => by
    rw [fillBoundsFrom]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hi
      obtain ⟨h1, h2⟩ := fillBoundsFrom_ne st en fuel (i + 1) (cst.set! i st) (cen.set! i en) x
        (by omega)
      exact ⟨by rw [h1, getElemD_setD_ne (by omega : x ≠ i)],
        by rw [h2, getElemD_setD_ne (by omega : x ≠ i)]⟩

theorem fillBoundsFrom_getElemD (st en : Nat) : ∀ (fuel i : Nat) (cst cen : Array Nat),
    en ≤ i + fuel → en ≤ cst.size → en ≤ cen.size → ∀ x, i ≤ x → x < en →
      (fillBoundsFrom st en fuel i cst cen).1[x]! = st
        ∧ (fillBoundsFrom st en fuel i cst cen).2[x]! = en
  | 0, i, cst, cen, hf, _, _, x, h1, h2 => by omega
  | fuel + 1, i, cst, cen, hf, hc1, hc2, x, h1, h2 => by
    rw [fillBoundsFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        obtain ⟨e1, e2⟩ := fillBoundsFrom_ne st en fuel (i + 1) (cst.set! i st) (cen.set! i en) i
          (by omega)
        exact ⟨by rw [e1, getElemD_setD (by omega) _, ite_eq_left rfl],
          by rw [e2, getElemD_setD (by omega) _, ite_eq_left rfl]⟩
      · exact fillBoundsFrom_getElemD st en fuel (i + 1) _ _ (by omega) (by simpa using hc1)
          (by simpa using hc2) x (by omega) h2

/-- The total size of the fragments `[a, b)`. -/
def sizesSum (sizes : Array Nat) (a b : Nat) : Nat := ∑ j ∈ Finset.Ico a b, sizes[j]!

theorem sizesSum_self (sizes : Array Nat) (a : Nat) : sizesSum sizes a a = 0 := by
  simp [sizesSum]

theorem sizesSum_succ (sizes : Array Nat) {a b : Nat} (h : a < b) :
    sizesSum sizes a b = sizes[a]! + sizesSum sizes (a + 1) b := by
  rw [sizesSum, sizesSum, Finset.sum_eq_sum_Ico_succ_bot h]

theorem sizesSum_le (sizes : Array Nat) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    sizesSum sizes a b ≤ sizesSum sizes a c := by
  rw [sizesSum, sizesSum, ← Finset.sum_Ico_consecutive _ h1 h2]
  omega

theorem sizesSum_split (sizes : Array Nat) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    sizesSum sizes a c = sizesSum sizes a b + sizesSum sizes b c := by
  rw [sizesSum, sizesSum, sizesSum, Finset.sum_Ico_consecutive _ h1 h2]

/-- Positions outside the split cell keep their boundaries. -/
theorem boundsFrom_ne (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64) (x : Nat),
      (x < st ∨ st + sizesSum sizes j ks.size ≤ x) →
        (boundsFrom ks sizes fuel j cst cen starts st tr).1[x]! = cst[x]!
          ∧ (boundsFrom ks sizes fuel j cst cen starts st tr).2.1[x]! = cen[x]!
  | 0, _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | fuel + 1, j, cst, cen, starts, st, tr, x, hx => by
    rw [boundsFrom]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hj
      have hsz : sizes[j]! ≤ sizesSum sizes j ks.size := by
        rw [sizesSum_succ sizes (show j < ks.size by omega)]
        omega
      have hsub : sizesSum sizes (j + 1) ks.size + sizes[j]! = sizesSum sizes j ks.size := by
        rw [sizesSum_succ sizes (show j < ks.size by omega)]
        omega
      obtain ⟨h1, h2⟩ := boundsFrom_ne ks sizes fuel (j + 1)
        (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
        (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
        (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) x (by omega)
      obtain ⟨e1, e2⟩ := fillBoundsFrom_ne st (st + sizes[j]!) sizes[j]! st cst cen x (by omega)
      exact ⟨by rw [h1, e1], by rw [h2, e2]⟩

/-- **The boundaries the split installs.**  Every position of fragment `j'` reports that
fragment's range. -/
theorem boundsFrom_getElemD (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64), ks.size ≤ j + fuel →
      st + sizesSum sizes j ks.size ≤ cst.size → st + sizesSum sizes j ks.size ≤ cen.size →
        ∀ j', j ≤ j' → j' < ks.size → ∀ x, st + sizesSum sizes j j' ≤ x →
          x < st + sizesSum sizes j (j' + 1) →
            (boundsFrom ks sizes fuel j cst cen starts st tr).1[x]!
                = st + sizesSum sizes j j'
              ∧ (boundsFrom ks sizes fuel j cst cen starts st tr).2.1[x]!
                = st + sizesSum sizes j (j' + 1)
  | 0, j, cst, cen, starts, st, tr, hf, _, _, j', h1, h2, x, _, _ => by omega
  | fuel + 1, j, cst, cen, starts, st, tr, hf, hc1, hc2, j', h1, h2, x, hx1, hx2 => by
    rw [boundsFrom]
    split
    · omega
    · rename_i hj
      have hsub : ∀ m, j + 1 ≤ m → sizesSum sizes j m = sizes[j]! + sizesSum sizes (j + 1) m :=
        fun m hm => sizesSum_succ sizes (by omega)
      have hcell : st + sizes[j]! + sizesSum sizes (j + 1) ks.size
          = st + sizesSum sizes j ks.size := by rw [hsub ks.size (by omega)]; omega
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · -- the fragment being written now
        subst h
        rw [sizesSum_self, Nat.add_zero] at hx1 ⊢
        rw [hsub (j + 1) (by omega), sizesSum_self, Nat.add_zero] at hx2 ⊢
        obtain ⟨e1, e2⟩ := boundsFrom_ne ks sizes fuel (j + 1)
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
          (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) x (by omega)
        obtain ⟨f1, f2⟩ := fillBoundsFrom_getElemD st (st + sizes[j]!) sizes[j]! st cst cen
          (by omega) (by omega) (by omega) x (by omega) (by omega)
        exact ⟨by rw [e1, f1]; omega, by rw [e2, f2]; omega⟩
      · have := boundsFrom_getElemD ks sizes fuel (j + 1)
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).1
          (fillBoundsFrom st (st + sizes[j]!) sizes[j]! st cst cen).2
          (starts.push st) (st + sizes[j]!) (mixN (mixN tr sizes[j]!) ks[j]!) (by omega)
          (by rw [fillBoundsFrom_size1]; omega) (by rw [fillBoundsFrom_size2]; omega)
          j' (by omega) h2 x (by rw [hsub j' (by omega)] at hx1; omega)
          (by rw [hsub (j' + 1) (by omega)] at hx2; omega)
        rw [hsub j' (by omega), hsub (j' + 1) (by omega)]
        constructor
        · rw [this.1]; omega
        · rw [this.2]; omega

/-! ### Odds and ends: array extensionality, the leftover bucket counters, clearing scratch -/

/-- Counters the scatter never advances keep their value. -/
theorem scatterFrom_bc_ne (lab cnt : Array Nat) (ec : Nat) :
    ∀ (fuel k : Nat) (block bc : Array Nat) (t : Nat),
      (∀ i, k ≤ i → i < ec → cnt[lab[i]!]! ≠ t) →
        (scatterFrom lab cnt ec fuel k block bc).2[t]! = bc[t]!
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, k, block, bc, t, ht => by
    rw [scatterFrom]
    split
    · rfl
    · rename_i hk
      rw [scatterFrom_bc_ne lab cnt ec fuel (k + 1) _ _ t (fun i h1 h2 => ht i (by omega) h2),
        getElemD_setD_ne (Ne.symm (ht k (by omega) (by omega)))]

/-- The fragment starts and the trace do not depend on the boundary arrays being written. -/
theorem boundsFrom_congr (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen cst' cen' starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).2.2
        = (boundsFrom ks sizes fuel j cst' cen' starts st tr).2.2
  | 0, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, cst', cen', starts, st, tr => by
    rw [boundsFrom, boundsFrom]
    split
    · rfl
    · exact boundsFrom_congr ks sizes fuel (j + 1) _ _ _ _ _ _ _

theorem clearCntFrom_size (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat),
    (clearCntFrom touched fuel j cnt).size = cnt.size
  | 0, _, _ => rfl
  | fuel + 1, j, cnt => by
    rw [clearCntFrom]
    split
    · rfl
    · rw [clearCntFrom_size touched fuel (j + 1) _]
      simp

theorem clearCntFrom_ne (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat) (v : Nat),
    (∀ j', j ≤ j' → j' < touched.size → touched[j']! ≠ v) →
      (clearCntFrom touched fuel j cnt)[v]! = cnt[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, cnt, v, hv => by
    rw [clearCntFrom]
    split
    · rfl
    · rename_i hj
      rw [clearCntFrom_ne touched fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElemD_setD_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearCntFrom_mem (touched : Array Nat) : ∀ (fuel j : Nat) (cnt : Array Nat),
    touched.size ≤ j + fuel → ∀ j', j ≤ j' → j' < touched.size → touched[j']! < cnt.size →
      (clearCntFrom touched fuel j cnt)[touched[j']!]! = 0
  | 0, j, cnt, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, cnt, hf, j', h1, h2, hlt => by
    rw [clearCntFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < touched.size → touched[j'']! ≠ touched[j]!
        · rw [clearCntFrom_ne touched fuel (j + 1) _ _ hmem, getElemD_setD hlt _, ite_eq_left rfl]
        · push Not at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearCntFrom_mem touched fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearCntFrom_mem touched fuel (j + 1) _ (by omega) j' (by omega) h2
          (by simpa using hlt)

/-- **Clearing the counts.**  Every vertex the counting loop touched is reset, so the scratch is
back to all zeros. -/
theorem clearCntFrom_zero {cnt touched : Array Nat} (h : Touched cnt touched) (v : Nat)
    (hv : v < cnt.size) : (clearCntFrom touched touched.size 0 cnt)[v]! = 0 := by
  by_cases hmem : v ∈ touched
  · obtain ⟨j, hj1, hj2⟩ := mem_iff_getElemD.1 hmem
    have := clearCntFrom_mem touched touched.size 0 cnt (by omega) j (by omega) hj1
      (by rw [hj2]; exact hv)
    rwa [hj2] at this
  · rw [clearCntFrom_ne touched touched.size 0 cnt v
      (fun j' _ h2 => fun he => hmem (he ▸ getElemD_mem h2))]
    by_contra hne
    exact hmem ((h.mem v hv).2 hne)

theorem clearHitFrom_ne (cells : Array Nat) : ∀ (fuel j : Nat) (hit : Array Bool) (v : Nat),
    (∀ j', j ≤ j' → j' < cells.size → cells[j']! ≠ v) →
      (clearHitFrom cells fuel j hit)[v]! = hit[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, hit, v, hv => by
    rw [clearHitFrom]
    split
    · rfl
    · rename_i hj
      rw [clearHitFrom_ne cells fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElemD_setD_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearHitFrom_mem (cells : Array Nat) : ∀ (fuel j : Nat) (hit : Array Bool),
    cells.size ≤ j + fuel → ∀ j', j ≤ j' → j' < cells.size → cells[j']! < hit.size →
      (clearHitFrom cells fuel j hit)[cells[j']!]! = false
  | 0, j, hit, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, hit, hf, j', h1, h2, hlt => by
    rw [clearHitFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < cells.size → cells[j'']! ≠ cells[j]!
        · rw [clearHitFrom_ne cells fuel (j + 1) _ _ hmem, getElemD_setD hlt _, ite_eq_left rfl]
        · push Not at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearHitFrom_mem cells fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearHitFrom_mem cells fuel (j + 1) _ (by omega) j' (by omega) h2
          (by simpa using hlt)

/-- **Clearing the cell marks.**  Every collected cell is unmarked, so the scratch is back to all
`false`. -/
theorem clearHitFrom_zero {hit : Array Bool} {cells : Array Nat} (h : Collected hit cells)
    (v : Nat) (hv : v < hit.size) : (clearHitFrom cells cells.size 0 hit)[v]! = false := by
  by_cases hmem : v ∈ cells
  · obtain ⟨j, hj1, hj2⟩ := mem_iff_getElemD.1 hmem
    have := clearHitFrom_mem cells cells.size 0 hit (by omega) j (by omega) hj1
      (by rw [hj2]; exact hv)
    rwa [hj2] at this
  · rw [clearHitFrom_ne cells cells.size 0 hit v
      (fun j' _ h2 => fun he => hmem (he ▸ getElemD_mem h2))]
    by_contra hne
    exact hmem ((h.mem v hv).2 (by simpa using hne))

theorem clearBcFrom_size (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat),
    (clearBcFrom ks fuel j bc).size = bc.size
  | 0, _, _ => rfl
  | fuel + 1, j, bc => by
    rw [clearBcFrom]
    split
    · rfl
    · rw [clearBcFrom_size ks fuel (j + 1) _]
      simp

theorem clearBcFrom_ne (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat) (v : Nat),
    (∀ j', j ≤ j' → j' < ks.size → ks[j']! ≠ v) → (clearBcFrom ks fuel j bc)[v]! = bc[v]!
  | 0, _, _, _, _ => rfl
  | fuel + 1, j, bc, v, hv => by
    rw [clearBcFrom]
    split
    · rfl
    · rename_i hj
      rw [clearBcFrom_ne ks fuel (j + 1) _ v (fun j' h1 h2 => hv j' (by omega) h2),
        getElemD_setD_ne (Ne.symm (hv j (by omega) (by omega)))]

theorem clearBcFrom_mem (ks : Array Nat) : ∀ (fuel j : Nat) (bc : Array Nat),
    ks.size ≤ j + fuel → ∀ j', j ≤ j' → j' < ks.size → ks[j']! < bc.size →
      (clearBcFrom ks fuel j bc)[ks[j']!]! = 0
  | 0, j, bc, hf, j', h1, h2, _ => by omega
  | fuel + 1, j, bc, hf, j', h1, h2, hlt => by
    rw [clearBcFrom]
    split
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with h | h
      · subst h
        by_cases hmem : ∀ j'', j + 1 ≤ j'' → j'' < ks.size → ks[j'']! ≠ ks[j]!
        · rw [clearBcFrom_ne ks fuel (j + 1) _ _ hmem, getElemD_setD hlt _, ite_eq_left rfl]
        · push Not at hmem
          obtain ⟨j'', hj1, hj2, hj3⟩ := hmem
          rw [← hj3]
          exact clearBcFrom_mem ks fuel (j + 1) _ (by omega) j'' hj1 hj2
            (by rw [hj3]; simpa using hlt)
      · exact clearBcFrom_mem ks fuel (j + 1) _ (by omega) j' (by omega) h2 (by simpa using hlt)

theorem bucketSize_card (lab cnt : Array Nat) (c ec t : Nat) :
    bucketSize lab cnt c ec t = ((Finset.Ico c ec).filter (fun i => cnt[lab[i]!]! = t)).card := by
  rw [bucketSize, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The fragments of a split cell exhaust it: the bucket sizes sum to the size of the cell. -/
theorem sum_bucketSize (lab cnt ks : Array Nat) {c ec : Nat} (hnd : ks.toList.Nodup)
    (hmem : ∀ i, c ≤ i → i < ec → ∃ j, j < ks.size ∧ ks[j]! = cnt[lab[i]!]!) :
    ∑ j ∈ Finset.range ks.size, bucketSize lab cnt c ec ks[j]! = ec - c := by
  have hinj : ∀ j ∈ Finset.range ks.size, ∀ j' ∈ Finset.range ks.size,
      ks[j]! = ks[j']! → j = j' := by
    intro j hj j' hj' h
    simp only [Finset.mem_range] at hj hj'
    by_contra hne
    exact nodup_getElemD_ne hnd hj hj' hne h
  have himg : ∀ i ∈ Finset.Ico c ec,
      cnt[lab[i]!]! ∈ (Finset.range ks.size).image (fun j => ks[j]!) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    obtain ⟨j, hj, hjv⟩ := hmem i hi.1 hi.2
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, hjv⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun i => cnt[lab[i]!]!) (s := Finset.Ico c ec)
    (t := (Finset.range ks.size).image (fun j => ks[j]!))
    (by intro i hi; simpa using himg i (by simpa using hi))
  rw [Finset.sum_image (by
    intro j hj j' hj' h
    exact hinj j (by simpa using hj) j' (by simpa using hj') h)] at hcard
  simp only [bucketSize_card]
  rw [← hcard, Nat.card_Ico]

/-- Where the fragment of neighbour count `t` starts: after every vertex of the cell with a
smaller count.  The point of this description is that it never mentions the bucket list, so two
runs of `refineStep` on isomorphic inputs manifestly agree on it. -/
def fragStart (n : Nat) (p : Part) (cnt : Array Nat) (c t : Nat) : Nat :=
  c + ∑ t' ∈ Finset.range t, cellCount n p c (fun u => cnt[u]! == t')

/-- The prefix sums the algorithm computes are the fragment starts.  The bucket list is sorted
and holds exactly the counts that occur, so summing along it is summing over all smaller counts. -/
theorem fragStart_eq {n : Nat} {p : Part} {c : Nat} {cnt ks sizes : Array Nat}
    (hnd : ks.toList.Nodup) (hsorted : ks.toList.Pairwise (· ≤ ·))
    (hmem : ∀ t, t ∈ ks ↔ cellCount n p c (fun u => cnt[u]! == t) ≠ 0)
    (hsizes : ∀ j, j < ks.size → sizes[j]! = cellCount n p c (fun u => cnt[u]! == ks[j]!))
    (j : Nat) (hj : j < ks.size) :
    c + sizesSum sizes 0 j = fragStart n p cnt c ks[j]! := by
  have hs : sizesSum sizes 0 j
      = ∑ j' ∈ Finset.Ico 0 j, cellCount n p c (fun u => cnt[u]! == ks[j']!) := by
    rw [sizesSum]
    exact Finset.sum_congr rfl fun j' hj' => hsizes j' (by
      simp only [Finset.mem_Ico] at hj'; omega)
  have key : ∑ j' ∈ Finset.Ico 0 j, cellCount n p c (fun u => cnt[u]! == ks[j']!)
      = ∑ t' ∈ Finset.range ks[j]!, cellCount n p c (fun u => cnt[u]! == t') := by
    rw [← Finset.sum_filter_ne_zero (Finset.range ks[j]!)]
    refine Finset.sum_bij (fun j' _ => ks[j']!) ?_ ?_ ?_ ?_
    · intro j' hj'
      simp only [Finset.mem_Ico] at hj'
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨pairwise_getElemD_lt hsorted hnd hj (by omega),
        (hmem ks[j']!).1 (getElemD_mem (by omega))⟩
    · intro a ha b hb hab
      simp only [Finset.mem_Ico] at ha hb
      by_contra hne
      exact nodup_getElemD_ne hnd (show a < ks.size by omega) (show b < ks.size by omega) hne hab
    · intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_range] at ht'
      obtain ⟨j'', hj''1, hj''2⟩ := mem_iff_getElemD.1 ((hmem t').2 ht'.2)
      refine ⟨j'', ?_, hj''2⟩
      simp only [Finset.mem_Ico]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hle
      have : ks[j]! ≤ ks[j'']! := pairwise_getElemD_le hsorted hj''1 (by omega)
      omega
    · intro a _
      rfl
  rw [fragStart, hs, key]

/-- The partition carried by the cell loop's state. -/
def SplitState.part (st : SplitState) : Part :=
  { lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen }

/-- **What splitting one cell does.**  Outside the cell `[c, cen[c])` nothing moves; inside, each
vertex lands in the fragment of its neighbour count, and the fragments sit in increasing order of
count.  Everything is phrased through `fragStart`/`cellCount`, which mention only the cell as a
set — that is what makes the description equivariant. -/
structure SplitOk (n : Nat) (p : Part) (cnt : Array Nat) (c : Nat) (p' : Part) : Prop where
  /-- The result is still a partition. -/
  wf : Part.WF n p'
  /-- Positions outside the cell keep their vertex. -/
  lab_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.lab[i]! = p.lab[i]!
  /-- Positions outside the cell keep their cell start. -/
  cst_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.cst[i]! = p.cst[i]!
  /-- Positions outside the cell keep their cell end. -/
  cen_ne : ∀ i, i < n → (i < c ∨ p.cen[c]! ≤ i) → p'.cen[i]! = p.cen[i]!
  /-- Vertices outside the cell keep their position. -/
  pos_ne : ∀ v, v < n → (p.pos[v]! < c ∨ p.cen[c]! ≤ p.pos[v]!) → p'.pos[v]! = p.pos[v]!
  /-- Vertices of the cell stay in it. -/
  pos_mem : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    c ≤ p'.pos[v]! ∧ p'.pos[v]! < p.cen[c]!
  /-- A vertex of the cell lands in the fragment of its count. -/
  cell : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    p'.cst[p'.pos[v]!]! = fragStart n p cnt c cnt[v]!
  /-- That fragment is as long as the number of cell vertices of that count. -/
  cen_cell : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! →
    p'.cen[p'.pos[v]!]! = fragStart n p cnt c cnt[v]!
      + cellCount n p c (fun u => cnt[u]! == cnt[v]!)

theorem cellCount_congr {n : Nat} {p : Part} {c : Nat} {P Q : Nat → Bool}
    (h : ∀ w, w < n → p.cst[p.pos[w]!]! = c → P w = Q w) :
    cellCount n p c P = cellCount n p c Q := by
  rw [cellCount, cellCount]
  congr 1
  refine Finset.filter_congr fun w hw => ?_
  simp only [Finset.mem_range] at hw
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h w hw h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h w hw h1]; exact h2⟩

/-- A cell has as many vertices as it has positions. -/
theorem cellCount_true {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) : cellCount n p c (fun _ => true) = p.cen[c]! - c := by
  rw [cellCount, ← Nat.card_Ico c p.cen[c]!]
  refine Finset.card_bij (fun w _ => p.pos[w]!) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw
    have hpw : p.pos[w]! < n := hp.posLt w hw.1
    have := (hp.cst_eq_iff hc hpw).1 (by rw [hw.2.1, hcst])
    rw [hcst] at this
    simpa using this
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have h1 := hp.labPos a ha.1
    have h2 := hp.labPos b hb.1
    rw [show p.pos[a]! = p.pos[b]! from hab, h2] at h1
    omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    have hin : i < n := lt_of_lt_of_le hi.2 (hp.cenLe c hc)
    refine ⟨p.lab[i]!, ?_, hp.posLab i hin⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hp.labLt i hin, ?_, trivial⟩
    rw [hp.posLab i hin, hp.cellCst c hc i (by rw [hcst]; omega) hi.2, hcst]

/-- **A cell whose vertices all have the same count does not split.**  Both easy branches of
`splitCell` are this: the cell is a singleton, or the counting pass found a single bucket. -/
theorem splitOk_of_uniform {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (cnt : Array Nat)
    (huni : ∀ v w, v < n → w < n → p.cst[p.pos[v]!]! = c → p.cst[p.pos[w]!]! = c →
      cnt[v]! = cnt[w]!) :
    SplitOk n p cnt c p := by
  have hmem : ∀ v, v < n → c ≤ p.pos[v]! → p.pos[v]! < p.cen[c]! → p.cst[p.pos[v]!]! = c := by
    intro v hv h1 h2
    rw [hp.cellCst c hc _ (by rw [hcst]; omega) h2, hcst]
  have hfrag : ∀ v, v < n → p.cst[p.pos[v]!]! = c → fragStart n p cnt c cnt[v]! = c := by
    intro v hv hvc
    rw [fragStart, Nat.add_eq_left]
    refine Finset.sum_eq_zero fun t' ht' => ?_
    simp only [Finset.mem_range] at ht'
    rw [cellCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw
    simp only [Finset.mem_range] at hw
    rintro ⟨hwc, hwt⟩
    have : cnt[w]! = t' := by simpa using hwt
    rw [← huni v w hv hw hvc hwc] at this
    omega
  refine ⟨hp, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ h1 h2 => ⟨h1, h2⟩, fun v hv h1 h2 => ?_, fun v hv h1 h2 => ?_⟩
  · rw [hmem v hv h1 h2, hfrag v hv (hmem v hv h1 h2)]
  · have hc' : c < p.cen[c]! := hp.ltCen c hc
    rw [hp.cellCen c hc _ (by rw [hcst]; omega) h2, hfrag v hv (hmem v hv h1 h2),
      cellCount_congr (P := fun u => cnt[u]! == cnt[v]!) (Q := fun _ => true)
        (fun w hw hwc => by rw [huni v w hv hw (hmem v hv h1 h2) hwc]; simp),
      cellCount_true hp hc hcst]
    omega

theorem boundsFrom_size1 (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).1.size = cst.size
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, starts, st, tr => by
    rw [boundsFrom]
    split
    · rfl
    · rw [boundsFrom_size1 ks sizes fuel (j + 1) _ _ _ _ _, fillBoundsFrom_size1]

theorem boundsFrom_size2 (ks sizes : Array Nat) :
    ∀ (fuel j : Nat) (cst cen starts : Array Nat) (st : Nat) (tr : UInt64),
      (boundsFrom ks sizes fuel j cst cen starts st tr).2.1.size = cen.size
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, j, cst, cen, starts, st, tr => by
    rw [boundsFrom]
    split
    · rfl
    · rw [boundsFrom_size2 ks sizes fuel (j + 1) _ _ _ _ _, fillBoundsFrom_size2]

theorem sizesSum_one (sizes : Array Nat) (j : Nat) : sizesSum sizes j (j + 1) = sizes[j]! := by
  rw [sizesSum_succ sizes (Nat.lt_succ_self j), sizesSum_self]
  omega

/-- A nonempty bucket has a member. -/
theorem exists_of_bucketSize {lab cnt : Array Nat} {c ec t : Nat}
    (h : bucketSize lab cnt c ec t ≠ 0) : ∃ i, c ≤ i ∧ i < ec ∧ cnt[lab[i]!]! = t := by
  by_contra hno
  push Not at hno
  refine h ?_
  rw [bucketSize]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  rw [ite_eq_right (hno i hi.1 hi.2)]

/-! ### The counting sort is a permutation of the cell

Everything the scatter needs is packaged in `Offsets`: the counts occurring in the cell, in some
order and without duplicates (`ks`), their bucket sizes (`sizes`) and the offset each bucket was
given (`bc1`, the prefix sums).  From that alone the scatter is a bijection from the cell onto
`[0, ec - c)`. -/

/-- What the count-and-offset passes leave behind. -/
structure Offsets (lab cnt ks sizes bc1 : Array Nat) (c ec : Nat) : Prop where
  /-- The counts are listed once each. -/
  nodup : ks.toList.Nodup
  /-- `sizes[j]` is the size of bucket `ks[j]`. -/
  sizes_eq : ∀ j, j < ks.size → sizes[j]! = bucketSize lab cnt c ec ks[j]!
  /-- Bucket `ks[j]` was given the offset just past all earlier buckets. -/
  bc_eq : ∀ j, j < ks.size → bc1[ks[j]!]! = sizesSum sizes 0 j
  /-- Every count occurring in the cell is listed. -/
  mem : ∀ i, c ≤ i → i < ec → ∃ j, j < ks.size ∧ ks[j]! = cnt[lab[i]!]!

namespace Offsets

variable {lab cnt ks sizes bc1 : Array Nat} {c ec : Nat}

/-- The buckets exhaust the cell. -/
theorem total (h : Offsets lab cnt ks sizes bc1 c ec) : sizesSum sizes 0 ks.size = ec - c := by
  rw [sizesSum, ← Finset.range_eq_Ico, ← sum_bucketSize lab cnt ks h.nodup h.mem]
  exact Finset.sum_congr rfl fun j hj => h.sizes_eq j (Finset.mem_range.1 hj)

theorem index (h : Offsets lab cnt ks sizes bc1 c ec) {t : Nat}
    (ht : bucketSize lab cnt c ec t ≠ 0) : ∃ j, j < ks.size ∧ ks[j]! = t := by
  obtain ⟨i, h1, h2, h3⟩ := exists_of_bucketSize ht
  obtain ⟨j, hj, hjv⟩ := h.mem i h1 h2
  exact ⟨j, hj, by rw [hjv, h3]⟩

/-- Distinct buckets get disjoint ranges of slots. -/
theorem sep (h : Offsets lab cnt ks sizes bc1 c ec) : Sep lab cnt c ec bc1 := by
  intro t t' htt a b ha hb
  obtain ⟨j, hj, hjt⟩ := h.index (t := t) (by omega)
  obtain ⟨j', hj', hjt'⟩ := h.index (t := t') (by omega)
  have hne : j ≠ j' := by
    rintro rfl
    exact htt (by rw [← hjt, hjt'])
  have hja : a < sizes[j]! := by rw [h.sizes_eq j hj, hjt]; omega
  have hjb : b < sizes[j']! := by rw [h.sizes_eq j' hj', hjt']; omega
  rw [← hjt, ← hjt', h.bc_eq j hj, h.bc_eq j' hj']
  rcases Nat.lt_or_ge j j' with hlt | hge
  · have h1 : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 j' :=
      sizesSum_le sizes (by omega) (by omega)
    rw [sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one] at h1
    omega
  · have hne' : j' < j := by omega
    have h1 : sizesSum sizes 0 (j' + 1) ≤ sizesSum sizes 0 j :=
      sizesSum_le sizes (by omega) (by omega)
    rw [sizesSum_split sizes (Nat.zero_le j') (Nat.le_succ j'), sizesSum_one] at h1
    omega

/-- The slot a cell position is scattered to lies in its bucket's range. -/
theorem scatterAt_mem (h : Offsets lab cnt ks sizes bc1 c ec) {i : Nat} (h1 : c ≤ i) (h2 : i < ec)
    {j : Nat} (hj : j < ks.size) (hjt : ks[j]! = cnt[lab[i]!]!) :
    sizesSum sizes 0 j ≤ scatterAt lab cnt bc1 c i
      ∧ scatterAt lab cnt bc1 c i < sizesSum sizes 0 (j + 1) := by
  have hsplit : bucketSize lab cnt c ec cnt[lab[i]!]!
      = bucketSize lab cnt c i cnt[lab[i]!]! + bucketSize lab cnt i ec cnt[lab[i]!]! :=
    bucketSize_split lab cnt (by omega) (by omega)
  have hpos : 0 < bucketSize lab cnt i ec cnt[lab[i]!]! := bucketSize_pos lab cnt h2 rfl
  have hsz : sizes[j]! = bucketSize lab cnt c ec cnt[lab[i]!]! := by rw [h.sizes_eq j hj, hjt]
  have hbc : bc1[cnt[lab[i]!]!]! = sizesSum sizes 0 j := by rw [← hjt, h.bc_eq j hj]
  rw [scatterAt, hbc, sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one]
  omega

theorem scatterAt_lt (h : Offsets lab cnt ks sizes bc1 c ec) {i : Nat} (h1 : c ≤ i) (h2 : i < ec) :
    scatterAt lab cnt bc1 c i < ec - c := by
  obtain ⟨j, hj, hjt⟩ := h.mem i h1 h2
  have := (h.scatterAt_mem h1 h2 hj hjt).2
  have hle : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 ks.size :=
    sizesSum_le sizes (by omega) (by omega)
  rw [h.total] at hle
  omega

/-- Distinct cell positions are scattered to distinct slots. -/
theorem scatterAt_ne (h : Offsets lab cnt ks sizes bc1 c ec) {i i' : Nat} (h1 : c ≤ i)
    (hii : i < i') (h2 : i' < ec) :
    scatterAt lab cnt bc1 c i ≠ scatterAt lab cnt bc1 c i' := by
  by_cases ht : cnt[lab[i]!]! = cnt[lab[i']!]!
  · -- same bucket: `i` was scattered before `i'`, so it sits at a smaller offset
    have hstep : bucketSize lab cnt c (i + 1) cnt[lab[i]!]!
        = bucketSize lab cnt c i cnt[lab[i]!]! + 1 := by
      rw [bucketSize_split lab cnt (show c ≤ i by omega) (Nat.le_succ i),
        bucketSize_succ lab cnt (Nat.lt_succ_self i), ite_eq_left rfl,
        bucketSize_zero lab cnt (le_refl _)]
    have hmono : bucketSize lab cnt c (i + 1) cnt[lab[i]!]!
        ≤ bucketSize lab cnt c i' cnt[lab[i]!]! := by
      rw [bucketSize_split lab cnt (show c ≤ i + 1 by omega) (show i + 1 ≤ i' by omega)]
      omega
    rw [scatterAt, scatterAt, ← ht]
    omega
  · have hi : bucketSize lab cnt c i cnt[lab[i]!]! < bucketSize lab cnt c ec cnt[lab[i]!]! := by
      have := bucketSize_pos lab cnt (show i < ec by omega) (rfl (a := cnt[lab[i]!]!))
      rw [bucketSize_split lab cnt (show c ≤ i by omega) (show i ≤ ec by omega)]
      omega
    have hi' : bucketSize lab cnt c i' cnt[lab[i']!]! < bucketSize lab cnt c ec cnt[lab[i']!]! := by
      have := bucketSize_pos lab cnt h2 (rfl (a := cnt[lab[i']!]!))
      rw [bucketSize_split lab cnt (show c ≤ i' by omega) (show i' ≤ ec by omega)]
      omega
    exact h.sep _ _ ht _ _ hi hi'

theorem scatterAt_inj (h : Offsets lab cnt ks sizes bc1 c ec) {i i' : Nat} (h1 : c ≤ i)
    (h2 : i < ec) (h1' : c ≤ i') (h2' : i' < ec)
    (he : scatterAt lab cnt bc1 c i = scatterAt lab cnt bc1 c i') : i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd he (h.scatterAt_ne h1 hlt h2')
  · exact heq
  · exact absurd he.symm (h.scatterAt_ne h1' hgt h2)

/-- **The scatter is onto**: every slot of the block is written. -/
theorem scatterAt_surj (h : Offsets lab cnt ks sizes bc1 c ec) {m : Nat} (hm : m < ec - c) :
    ∃ i, c ≤ i ∧ i < ec ∧ scatterAt lab cnt bc1 c i = m := by
  have himg : (Finset.Ico c ec).image (fun i => scatterAt lab cnt bc1 c i)
      = Finset.range (ec - c) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [Finset.mem_image, Finset.mem_Ico] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact Finset.mem_range.2 (h.scatterAt_lt hi.1 hi.2)
    · rw [Finset.card_range, Finset.card_image_of_injOn, Nat.card_Ico]
      intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      exact h.scatterAt_inj ha.1 ha.2 hb.1 hb.2 hab
  have : m ∈ (Finset.Ico c ec).image (fun i => scatterAt lab cnt bc1 c i) := by
    rw [himg]
    exact Finset.mem_range.2 hm
  simp only [Finset.mem_image, Finset.mem_Ico] at this
  obtain ⟨i, hi, hie⟩ := this
  exact ⟨i, hi.1, hi.2, hie⟩

end Offsets

/-! ### Reading off one step of `splitCell`

`splitCell` has three branches; these equations name the state each one produces, so that the
rest of the file never has to unfold `splitCell` again: unfolding it in place would leave the
trace hash of the branch in the goal, and deciding whether two such hashes agree is something the
kernel should never be asked to do. -/

theorem part_mk (lab pos cst cen : Array Nat) (inW : Array Bool) (tr : UInt64) (bc : Array Nat) :
    (SplitState.mk lab pos cst cen inW tr bc).part
      = { lab := lab, pos := pos, cst := cst, cen := cen } := rfl

theorem part_update (st : SplitState) (inW : Array Bool) (tr : UInt64) (bc : Array Nat) :
    ({ lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen, inW, tr, bc } :
      SplitState).part = st.part := rfl

/-- A singleton cell: only the trace hash moves. -/
theorem splitCell_eq_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) :
    splitCell cnt c st = { st with tr := mixN (mixN st.tr c) cnt[st.lab[c]!]! } := by
  rw [splitCell]
  dsimp only
  exact ite_eq_left h

/-- A cell with a single bucket: again only the trace hash moves (and the bucket counter is
put back). -/
theorem splitCell_eq_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    splitCell cnt c st =
      { st with tr := mixN (mixN st.tr c) ks0[0]!, bc := bc0.set! ks0[0]! 0 } := by
  rw [splitCell]
  dsimp only
  rw [ite_eq_right h1, hb]
  dsimp only
  exact ite_eq_left h2

/-- The general branch, with each pass of the counting sort named. -/
theorem splitCell_eq_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat}
    (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat}
    (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64}
    (hbd : boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) = (cst, cen, starts, tr)) :
    splitCell cnt c st =
      { lab := lab, pos := pos, cst := cst, cen := cen,
        inW := if st.inW[c]! then markAllFrom starts starts.size 0 st.inW
          else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 st.inW,
        tr := tr, bc := clearBcFrom (sortNats ks0) (sortNats ks0).size 0 bc2 } := by
  rw [splitCell]
  dsimp only
  rw [ite_eq_right h1, hb]
  dsimp only
  rw [ite_eq_right h2, ho]
  dsimp only
  rw [hsc]
  dsimp only
  rw [hw]
  dsimp only
  rw [hbd]

/-- The partition after a singleton cell "splits": unchanged. -/
theorem splitCell_part_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) : (splitCell cnt c st).part = st.part := by
  rw [splitCell_eq_singleton h]
  exact part_update st st.inW _ st.bc

/-- The partition after a one-bucket cell "splits": unchanged. -/
theorem splitCell_part_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    (splitCell cnt c st).part = st.part := by
  rw [splitCell_eq_one hb h1 h2]
  exact part_update st st.inW _ _

/-- The partition after a genuine split. -/
theorem splitCell_part_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat}
    (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat}
    (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64}
    (hbd : boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).part = { lab := lab, pos := pos, cst := cst, cen := cen } := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]
  exact part_mk _ _ _ _ _ _ _

/-- Every offset below the total is inside exactly one fragment. -/
theorem sizesSum_exists (sizes : Array Nat) : ∀ (K x : Nat), x < sizesSum sizes 0 K →
    ∃ j, j < K ∧ sizesSum sizes 0 j ≤ x ∧ x < sizesSum sizes 0 (j + 1)
  | 0, x, hx => by rw [sizesSum_self] at hx; omega
  | K + 1, x, hx => by
    by_cases h : x < sizesSum sizes 0 K
    · obtain ⟨j, hj, h1, h2⟩ := sizesSum_exists sizes K x h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨K, by omega, by omega, hx⟩

private theorem splitOk_general_passes {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size)
    {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0)) :
    ∃ sizes bc1 block bc2 lab' pos' cst' cen' starts tr',
      offsetFrom (sortNats ks0) (sortNats ks0).size 0
          (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1) ∧
      scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
          (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2) ∧
      writeFrom block c block.size 0 st.lab st.pos = (lab', pos') ∧
      boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
          (mixN st.tr c) = (cst', cen', starts, tr') ∧
      (sortNats ks0).toList.Nodup ∧
      (∀ t, t ∈ sortNats ks0 ↔
        t < st.bc.size ∧ bucketSize st.lab cnt c st.cen[c]! t ≠ 0) ∧
      (∀ j, j < (sortNats ks0).size →
        sizes[j]! = bucketSize st.lab cnt c st.cen[c]! (sortNats ks0)[j]!) ∧
      Offsets st.lab cnt (sortNats ks0) sizes bc1 c st.cen[c]! ∧
      sizesSum sizes 0 (sortNats ks0).size = st.cen[c]! - c ∧
      (∀ v : Nat, cnt[v]! < bc1.size) := by
  obtain ⟨lab, pos, cst, cen, inW, tr, bc⟩ := st
  dsimp only [SplitState.part] at hp hcst hbc hcb hb
  -- the partition data, with the projections spelled out
  have hlabn : lab.size = n := hp.labSize
  have hposn : pos.size = n := hp.posSize
  have hcstn : cst.size = n := hp.cstSize
  have hcenn : cen.size = n := hp.cenSize
  have hlabLt : ∀ i, i < n → lab[i]! < n := hp.labLt
  have hposLt : ∀ v, v < n → pos[v]! < n := hp.posLt
  have hposLab : ∀ i, i < n → pos[lab[i]!]! = i := hp.posLab
  have hlabPos : ∀ v, v < n → lab[pos[v]!]! = v := hp.labPos
  have hcstLe : ∀ i, i < n → cst[i]! ≤ i := hp.cstLe
  have hltCen : ∀ i, i < n → i < cen[i]! := hp.ltCen
  have hcenLe : ∀ i, i < n → cen[i]! ≤ n := hp.cenLe
  have hcellCst : ∀ i, i < n → ∀ j, cst[i]! ≤ j → j < cen[i]! → cst[j]! = cst[i]! := hp.cellCst
  have hcellCen : ∀ i, i < n → ∀ j, cst[i]! ≤ j → j < cen[i]! → cen[j]! = cen[i]! := hp.cellCen
  have hcE : c < cen[c]! := hltCen c hc
  have hEn : cen[c]! ≤ n := hcenLe c hc
  -- the counting pass
  have e1 : (bucketFrom lab cnt cen[c]! (cen[c]! - c) c bc #[]).1 = bc0 := by rw [hb]
  have e2 : (bucketFrom lab cnt cen[c]! (cen[c]! - c) c bc #[]).2 = ks0 := by rw [hb]
  have hbc0size : bc0.size = bc.size := by rw [← e1, bucketFrom_size]
  have hbc0 : ∀ t, t < bc.size → bc0[t]! = bucketSize lab cnt c cen[c]! t := by
    intro t ht
    rw [← e1, bucketFrom_getElemD lab cnt cen[c]! (cen[c]! - c) c bc #[] (by omega) t ht, hbc t ht]
    omega
  have hks0mem : ∀ t, t ∈ ks0 ↔ t < bc.size ∧ bucketSize lab cnt c cen[c]! t ≠ 0 := by
    intro t
    rw [← e2]
    exact bucket_mem hcb hbc t
  have hks0nd : ks0.toList.Nodup := by
    have h := bucketFrom_touched lab cnt cen[c]! (cen[c]! - c) c bc #[] hcb
      (touched_empty bc fun w hw => hbc w hw)
    rw [e2] at h
    exact h.nodup
  -- sorting the counts
  have hndks : (sortNats ks0).toList.Nodup := (sortNats_perm ks0).nodup_iff.2 hks0nd
  have hksmem : ∀ t, t ∈ sortNats ks0 ↔ t < bc.size ∧ bucketSize lab cnt c cen[c]! t ≠ 0 :=
    fun t => sortNats_mem.trans (hks0mem t)
  have hkslt : ∀ j, j < (sortNats ks0).size → (sortNats ks0)[j]! < bc.size :=
    fun j hj => ((hksmem _).1 (getElemD_mem hj)).1
  -- the remaining passes
  obtain ⟨sizes, bc1, ho⟩ : ∃ sizes bc1, offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1) := ⟨_, _, rfl⟩
  obtain ⟨block, bc2, hsc⟩ : ∃ block bc2, scatterFrom lab cnt cen[c]! (cen[c]! - c) c
      (Array.replicate (cen[c]! - c) 0) bc1 = (block, bc2) := ⟨_, _, rfl⟩
  obtain ⟨lab', pos', hw⟩ : ∃ lab' pos', writeFrom block c block.size 0 lab pos = (lab', pos') :=
    ⟨_, _, rfl⟩
  obtain ⟨cst', cen', starts, tr', hbd⟩ : ∃ cst' cen' starts tr',
      boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 cst cen #[] c (mixN tr c)
        = (cst', cen', starts, tr') := ⟨_, _, _, _, rfl⟩
  -- what the offset pass computed
  have hsizes_eq : ∀ j, j < (sortNats ks0).size →
      sizes[j]! = bucketSize lab cnt c cen[c]! (sortNats ks0)[j]! := by
    intro j hj
    have h := offsetFrom_sizes (sortNats ks0) hndks (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 (by omega) (by simp) j hj
    rw [ho] at h
    rw [h, ite_eq_right (by omega), hbc0 _ (hkslt j hj)]
  have hbc_eq : ∀ j, j < (sortNats ks0).size → bc1[(sortNats ks0)[j]!]! = sizesSum sizes 0 j := by
    intro j hj
    have h := offsetFrom_bc (sortNats ks0) hndks (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 (by omega)
      (fun i hi => by rw [hbc0size]; exact hkslt i hi) j (by omega) hj
    rw [ho] at h
    rw [h, sizesSum, Nat.zero_add]
    exact Finset.sum_congr rfl fun i hi => by
      simp only [Finset.mem_Ico] at hi
      rw [hsizes_eq i (by omega), hbc0 _ (hkslt i (by omega))]
  have hmemj : ∀ i, c ≤ i → i < cen[c]! →
      ∃ j, j < (sortNats ks0).size ∧ (sortNats ks0)[j]! = cnt[lab[i]!]! := by
    intro i ha hb'
    have hpos0 : 0 < bucketSize lab cnt i cen[c]! cnt[lab[i]!]! := bucketSize_pos lab cnt hb' rfl
    have hmono : bucketSize lab cnt i cen[c]! cnt[lab[i]!]!
        ≤ bucketSize lab cnt c cen[c]! cnt[lab[i]!]! :=
      bucketSize_mono lab cnt (by omega) (by omega)
    exact mem_iff_getElemD.1 ((hksmem _).2 ⟨hcb _, by omega⟩)
  have hoff : Offsets lab cnt (sortNats ks0) sizes bc1 c cen[c]! :=
    ⟨hndks, hsizes_eq, hbc_eq, hmemj⟩
  have hK : sizesSum sizes 0 (sortNats ks0).size = cen[c]! - c := hoff.total
  have hbc1size : bc1.size = bc.size := by
    have h := offsetFrom_size2 (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0
    rw [ho] at h
    rw [h, hbc0size]
  have hcb1 : ∀ v : Nat, cnt[v]! < bc1.size := fun v => by rw [hbc1size]; exact hcb v
  exact ⟨sizes, bc1, block, bc2, lab', pos', cst', cen', starts, tr', ho, hsc, hw, hbd,
    hndks, hksmem, hsizes_eq, hoff, hK, hcb1⟩

private theorem splitOk_general_layout {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hcb : ∀ v : Nat, cnt[v]! < st.bc.size) {ks0 sizes bc1 block bc2 lab' pos' cst' cen'
      starts : Array Nat} {tr' : UInt64}
    (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    (hw : writeFrom block c block.size 0 st.lab st.pos = (lab', pos'))
    (hbd : boundsFrom (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) = (cst', cen', starts, tr'))
    (hndks : (sortNats ks0).toList.Nodup)
    (hksmem : ∀ t, t ∈ sortNats ks0 ↔
      t < st.bc.size ∧ bucketSize st.lab cnt c st.cen[c]! t ≠ 0)
    (hsizes_eq : ∀ j, j < (sortNats ks0).size →
      sizes[j]! = bucketSize st.lab cnt c st.cen[c]! (sortNats ks0)[j]!)
    (hoff : Offsets st.lab cnt (sortNats ks0) sizes bc1 c st.cen[c]!)
    (hK : sizesSum sizes 0 (sortNats ks0).size = st.cen[c]! - c)
    (hcb1 : ∀ v : Nat, cnt[v]! < bc1.size) :
    block.size = st.cen[c]! - c ∧
      (∀ i, c ≤ i → i < st.cen[c]! →
        block[scatterAt st.lab cnt bc1 c i]! = st.lab[i]!) ∧
      (∀ x, (x < c ∨ st.cen[c]! ≤ x) → lab'[x]! = st.lab[x]!) ∧
      (∀ m, m < st.cen[c]! - c → lab'[c + m]! = block[m]!) ∧
      (∀ v, v < n → (st.pos[v]! < c ∨ st.cen[c]! ≤ st.pos[v]!) →
        pos'[v]! = st.pos[v]!) ∧
      (∀ m, m < block.size → pos'[block[m]!]! = c + m) ∧
      (∀ v, v < n → c ≤ st.pos[v]! → st.pos[v]! < st.cen[c]! →
        pos'[v]! = c + scatterAt st.lab cnt bc1 c st.pos[v]!) ∧
      (∀ i, c ≤ i → i < st.cen[c]! →
        ∃ i', c ≤ i' ∧ i' < st.cen[c]! ∧ lab'[i]! = st.lab[i']!) ∧
      (∀ x, (x < c ∨ st.cen[c]! ≤ x) →
        cst'[x]! = st.cst[x]! ∧ cen'[x]! = st.cen[x]!) ∧
      (∀ j, j < (sortNats ks0).size → ∀ x, c + sizesSum sizes 0 j ≤ x →
        x < c + sizesSum sizes 0 (j + 1) →
          cst'[x]! = c + sizesSum sizes 0 j ∧
            cen'[x]! = c + sizesSum sizes 0 (j + 1)) ∧
      (∀ x, c ≤ x → x < st.cen[c]! → ∃ j, j < (sortNats ks0).size ∧
        c + sizesSum sizes 0 j ≤ x ∧ x < c + sizesSum sizes 0 (j + 1)) ∧
      (∀ i, c ≤ i → i < st.cen[c]! → ∃ j, j < (sortNats ks0).size ∧
        (sortNats ks0)[j]! = cnt[st.lab[i]!]! ∧
        c + sizesSum sizes 0 j ≤ c + scatterAt st.lab cnt bc1 c i ∧
        c + scatterAt st.lab cnt bc1 c i < c + sizesSum sizes 0 (j + 1)) ∧
      (∀ t, bucketSize st.lab cnt c st.cen[c]! t =
        cellCount n st.part c (fun u => cnt[u]! == t)) ∧
      (∀ j, j < (sortNats ks0).size → c + sizesSum sizes 0 j =
        fragStart n st.part cnt c (sortNats ks0)[j]!) := by
  have hlabn : st.lab.size = n := hp.labSize
  have hposn : st.pos.size = n := hp.posSize
  have hcstn : st.cst.size = n := hp.cstSize
  have hcenn : st.cen.size = n := hp.cenSize
  have hlabLt : ∀ i, i < n → st.lab[i]! < n := hp.labLt
  have hposLab : ∀ i, i < n → st.pos[st.lab[i]!]! = i := hp.posLab
  have hlabPos : ∀ v, v < n → st.lab[st.pos[v]!]! = v := hp.labPos
  have hcE : c < st.cen[c]! := hp.ltCen c hc
  have hEn : st.cen[c]! ≤ n := hp.cenLe c hc
  -- what the scatter produced
  have hblocksize : block.size = st.cen[c]! - c := by
    have h := scatterFrom_size1 st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1
    rw [hsc] at h
    rw [h]; simp
  have hblockval : ∀ i, c ≤ i → i < st.cen[c]! →
      block[scatterAt st.lab cnt bc1 c i]! = st.lab[i]! := by
    intro i ha hb'
    have h := scatterFrom_block st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 (by omega) hcb1 hoff.sep
      (fun i' h1' h2' => by simpa using hoff.scatterAt_lt h1' h2') i ha hb'
    rw [hsc] at h
    exact h
  have hblocknd : block.toList.Nodup := by
    refine nodup_of_getElemD_ne fun m m' hm hm' hmm => ?_
    rw [hblocksize] at hm hm'
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    obtain ⟨i', hi1', hi2', hi3'⟩ := hoff.scatterAt_surj hm'
    rw [← hi3, ← hi3', hblockval i hi1 hi2, hblockval i' hi1' hi2']
    intro he
    have hii : i = i' := by
      have h := congrArg (fun x => st.pos[x]!) he
      rw [hposLab i (by omega), hposLab i' (by omega)] at h
      exact h
    rw [hii, hi3'] at hi3
    omega
  have hblocklt : ∀ m, m < block.size → block[m]! < st.pos.size := by
    intro m hm
    rw [hblocksize] at hm
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    rw [← hi3, hblockval i hi1 hi2, hposn]
    exact hlabLt i (by omega)
  -- what the write-back produced
  have hlab'_ne : ∀ x, (x < c ∨ st.cen[c]! ≤ x) → lab'[x]! = st.lab[x]! := by
    intro x hx
    have h := writeFrom_lab_ne block c block.size 0 st.lab st.pos x (by rw [hblocksize]; omega)
    rw [hw] at h; exact h
  have hlab'_in : ∀ m, m < st.cen[c]! - c → lab'[c + m]! = block[m]! := by
    intro m hm
    have h := writeFrom_lab block c block.size 0 st.lab st.pos (by omega)
      (by rw [hlabn, hblocksize]; omega) m (by omega) (by rw [hblocksize]; omega)
    rw [hw] at h; exact h
  have hnotblock : ∀ v, v < n → (st.pos[v]! < c ∨ st.cen[c]! ≤ st.pos[v]!) →
      ∀ m, m < block.size → block[m]! ≠ v := by
    intro v hv hvp m hm hmv
    rw [hblocksize] at hm
    obtain ⟨i, hi1, hi2, hi3⟩ := hoff.scatterAt_surj hm
    rw [← hi3, hblockval i hi1 hi2] at hmv
    have h := hposLab i (by omega)
    rw [hmv] at h
    omega
  have hpos'_ne : ∀ v, v < n → (st.pos[v]! < c ∨ st.cen[c]! ≤ st.pos[v]!) →
      pos'[v]! = st.pos[v]! := by
    intro v hv hvp
    have h := writeFrom_pos_ne block c block.size 0 st.lab st.pos v
      (fun m _ hm => hnotblock v hv hvp m hm)
    rw [hw] at h; exact h
  have hpos'_block : ∀ m, m < block.size → pos'[block[m]!]! = c + m := by
    intro m hm
    have h := writeFrom_pos block c hblocknd block.size 0 st.lab st.pos (by omega) hblocklt m
      (by omega) hm
    rw [hw] at h; exact h
  have hpos'_in : ∀ v, v < n → c ≤ st.pos[v]! → st.pos[v]! < st.cen[c]! →
      pos'[v]! = c + scatterAt st.lab cnt bc1 c st.pos[v]! := by
    intro v hv ha hb'
    have hm : scatterAt st.lab cnt bc1 c st.pos[v]! < block.size := by
      rw [hblocksize]; exact hoff.scatterAt_lt ha hb'
    have hbv : block[scatterAt st.lab cnt bc1 c st.pos[v]!]! = v := by
      rw [hblockval _ ha hb', hlabPos v hv]
    have h := hpos'_block _ hm
    rwa [hbv] at h
  have hlab'_cell : ∀ i, c ≤ i → i < st.cen[c]! →
      ∃ i', c ≤ i' ∧ i' < st.cen[c]! ∧ lab'[i]! = st.lab[i']! := by
    intro i ha hb'
    obtain ⟨i', hi1, hi2, hi3⟩ :=
      hoff.scatterAt_surj (show i - c < st.cen[c]! - c by omega)
    refine ⟨i', hi1, hi2, ?_⟩
    have hcm : c + (i - c) = i := by omega
    rw [← hcm, hlab'_in (i - c) (by omega), ← hi3, hblockval i' hi1 hi2]
  -- what the boundary pass produced
  have hbounds_ne : ∀ x, (x < c ∨ st.cen[c]! ≤ x) →
      cst'[x]! = st.cst[x]! ∧ cen'[x]! = st.cen[x]! := by
    intro x hx
    have h := boundsFrom_ne (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen #[] c
      (mixN st.tr c) x (by rw [hK]; omega)
    rw [hbd] at h; exact h
  have hbounds : ∀ j, j < (sortNats ks0).size → ∀ x, c + sizesSum sizes 0 j ≤ x →
      x < c + sizesSum sizes 0 (j + 1) →
        cst'[x]! = c + sizesSum sizes 0 j ∧ cen'[x]! = c + sizesSum sizes 0 (j + 1) := by
    intro j hj x ha hb'
    have h := boundsFrom_getElemD (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen
      #[] c (mixN st.tr c) (by omega) (by rw [hcstn, hK]; omega)
      (by rw [hcenn, hK]; omega) j (by omega) hj x ha hb'
    rw [hbd] at h; exact h
  have hin : ∀ x, c ≤ x → x < st.cen[c]! → ∃ j, j < (sortNats ks0).size ∧
      c + sizesSum sizes 0 j ≤ x ∧ x < c + sizesSum sizes 0 (j + 1) := by
    intro x ha hb'
    obtain ⟨j, hj, hj1, hj2⟩ :=
      sizesSum_exists sizes (sortNats ks0).size (x - c) (by rw [hK]; omega)
    exact ⟨j, hj, by omega, by omega⟩
  -- the fragment a cell vertex lands in
  have hfrag : ∀ i, c ≤ i → i < st.cen[c]! → ∃ j, j < (sortNats ks0).size ∧
      (sortNats ks0)[j]! = cnt[st.lab[i]!]! ∧
      c + sizesSum sizes 0 j ≤ c + scatterAt st.lab cnt bc1 c i ∧
      c + scatterAt st.lab cnt bc1 c i < c + sizesSum sizes 0 (j + 1) := by
    intro i ha hb'
    obtain ⟨j, hj, hjt⟩ := hoff.mem i ha hb'
    obtain ⟨u1, u2⟩ := hoff.scatterAt_mem ha hb' hj hjt
    exact ⟨j, hj, hjt, by omega, by omega⟩
  -- the fragment starts, in the invariant vocabulary
  have hcellCount : ∀ t, bucketSize st.lab cnt c st.cen[c]! t =
      cellCount n st.part c (fun u => cnt[u]! == t) :=
    fun t => bucketSize_cellCount hp hc hcst cnt t
  have hfragStart : ∀ j, j < (sortNats ks0).size → c + sizesSum sizes 0 j
      = fragStart n st.part cnt c (sortNats ks0)[j]! := by
    refine fragStart_eq hndks (sortNats_pairwise ks0) ?_ ?_
    · intro t
      rw [← hcellCount t, hksmem t]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨i, _, _, h3⟩ := exists_of_bucketSize h
      rw [← h3]
      exact hcb _
    · intro j hj
      rw [hsizes_eq j hj, hcellCount]
  exact ⟨hblocksize, hblockval, hlab'_ne, hlab'_in, hpos'_ne, hpos'_block, hpos'_in,
    hlab'_cell, hbounds_ne, hbounds, hin, hfrag, hcellCount, hfragStart⟩

/-- **The general branch of `splitCell`**: the counting sort really does sort the cell into
fragments by count, and installs the fragment boundaries. -/
theorem splitOk_general {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size)
    {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true) :
    SplitOk n st.part cnt c (splitCell cnt c st).part := by
  obtain ⟨sizes, bc1, block, bc2, lab', pos', cst', cen', starts, tr', ho, hsc, hw, hbd,
      hndks, hksmem, hsizes_eq, hoff, hK, hcb1⟩ :=
    splitOk_general_passes hp hc hcst hbc hcb hb
  obtain ⟨hblocksize, hblockval, hlab'_ne, hlab'_in, hpos'_ne, hpos'_block, hpos'_in,
      hlab'_cell, hbounds_ne, hbounds, hin, hfrag, hcellCount, hfragStart⟩ :=
    splitOk_general_layout hp hc hcst hcb hsc hw hbd hndks hksmem hsizes_eq hoff hK hcb1
  have hlabn : st.lab.size = n := hp.labSize
  have hposn : st.pos.size = n := hp.posSize
  have hcstn : st.cst.size = n := hp.cstSize
  have hcenn : st.cen.size = n := hp.cenSize
  have hlabLt : ∀ i, i < n → st.lab[i]! < n := hp.labLt
  have hposLt : ∀ v, v < n → st.pos[v]! < n := hp.posLt
  have hposLab : ∀ i, i < n → st.pos[st.lab[i]!]! = i := hp.posLab
  have hlabPos : ∀ v, v < n → st.lab[st.pos[v]!]! = v := hp.labPos
  have hcstLe : ∀ i, i < n → st.cst[i]! ≤ i := hp.cstLe
  have hltCen : ∀ i, i < n → i < st.cen[i]! := hp.ltCen
  have hcenLe : ∀ i, i < n → st.cen[i]! ≤ n := hp.cenLe
  have hcellCst : ∀ i, i < n → ∀ j, st.cst[i]! ≤ j → j < st.cen[i]! →
      st.cst[j]! = st.cst[i]! := hp.cellCst
  have hcellCen : ∀ i, i < n → ∀ j, st.cst[i]! ≤ j → j < st.cen[i]! →
      st.cen[j]! = st.cen[i]! := hp.cellCen
  have hcE : c < st.cen[c]! := hp.ltCen c hc
  have hEn : st.cen[c]! ≤ n := hp.cenLe c hc
  -- the sizes of the new arrays
  have hlab'n : lab'.size = n := by
    have h := writeFrom_size1 block c block.size 0 st.lab st.pos
    rw [hw] at h; rw [h, hlabn]
  have hpos'n : pos'.size = n := by
    have h := writeFrom_size2 block c block.size 0 st.lab st.pos
    rw [hw] at h; rw [h, hposn]
  have hcst'n : cst'.size = n := by
    have h := boundsFrom_size1 (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen
      #[] c (mixN st.tr c)
    rw [hbd] at h; rw [h, hcstn]
  have hcen'n : cen'.size = n := by
    have h := boundsFrom_size2 (sortNats ks0) sizes (sortNats ks0).size 0 st.cst st.cen
      #[] c (mixN st.tr c)
    rw [hbd] at h; rw [h, hcenn]
  -- the new arrays are still a permutation
  have hlab'Lt : ∀ i, i < n → lab'[i]! < n := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨i', hi1, hi2, hi3⟩ := hlab'_cell i hcell.1 hcell.2
      rw [hi3]
      exact hlabLt i' (by omega)
    · rw [hlab'_ne i (by omega)]
      exact hlabLt i hi
  have hpos'Lt : ∀ v, v < n → pos'[v]! < n := by
    intro v hv
    by_cases hcell : c ≤ st.pos[v]! ∧ st.pos[v]! < st.cen[c]!
    · rw [hpos'_in v hv hcell.1 hcell.2]
      have := hoff.scatterAt_lt hcell.1 hcell.2
      omega
    · rw [hpos'_ne v hv (by omega)]
      exact hposLt v hv
  have hpos'Lab : ∀ i, i < n → pos'[lab'[i]!]! = i := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · have hm : i - c < block.size := by rw [hblocksize]; omega
      have hcm : c + (i - c) = i := by omega
      have h := hpos'_block (i - c) hm
      rw [← hlab'_in (i - c) (by rw [← hblocksize]; exact hm), hcm] at h
      exact h
    · rw [hlab'_ne i (by omega)]
      have hvp : st.pos[st.lab[i]!]! < c ∨ st.cen[c]! ≤ st.pos[st.lab[i]!]! := by
        rw [hposLab i hi]; omega
      rw [hpos'_ne _ (hlabLt i hi) hvp, hposLab i hi]
  have hlab'Pos : ∀ v, v < n → lab'[pos'[v]!]! = v := by
    intro v hv
    by_cases hcell : c ≤ st.pos[v]! ∧ st.pos[v]! < st.cen[c]!
    · rw [hpos'_in v hv hcell.1 hcell.2, hlab'_in _ (hoff.scatterAt_lt hcell.1 hcell.2),
        hblockval _ hcell.1 hcell.2, hlabPos v hv]
    · rw [hpos'_ne v hv (by omega), hlab'_ne _ (by omega), hlabPos v hv]
  -- the new boundaries are still boundaries
  have hcst'Le : ∀ i, i < n → cst'[i]! ≤ i := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1]
      omega
    · rw [(hbounds_ne i (by omega)).1]
      exact hcstLe i hi
  have hltCen' : ∀ i, i < n → i < cen'[i]! := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').2]
      omega
    · rw [(hbounds_ne i (by omega)).2]
      exact hltCen i hi
  have hcen'Le : ∀ i, i < n → cen'[i]! ≤ n := by
    intro i hi
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').2]
      have hle : sizesSum sizes 0 (j + 1) ≤ sizesSum sizes 0 (sortNats ks0).size :=
        sizesSum_le sizes (by omega) (by omega)
      omega
    · rw [(hbounds_ne i (by omega)).2]
      exact hcenLe i hi
  -- an old cell that is not the split cell is untouched
  have hout : ∀ i, i < n → (i < c ∨ st.cen[c]! ≤ i) → ∀ y, st.cst[i]! ≤ y → y < st.cen[i]! →
      (y < c ∨ st.cen[c]! ≤ y) := by
    intro i hi hio y hy1 hy2
    by_contra hcon
    push Not at hcon
    have hcy : st.cst[y]! = c := by
      rw [hcellCst c hc y (by omega) (by omega), hcst]
    have hcy2 : st.cen[y]! = st.cen[c]! := hcellCen c hc y (by omega) (by omega)
    have h1' : st.cst[y]! = st.cst[i]! := hcellCst i hi y hy1 hy2
    have h2' : st.cen[y]! = st.cen[i]! := hcellCen i hi y hy1 hy2
    have := hcstLe i hi
    have := hltCen i hi
    omega
  have hcellCst' : ∀ i, i < n → ∀ x, cst'[i]! ≤ x → x < cen'[i]! → cst'[x]! = cst'[i]! := by
    intro i hi x hx1 hx2
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1] at hx1
      rw [(hbounds j hj i ha hb').2] at hx2
      rw [(hbounds j hj x hx1 hx2).1, (hbounds j hj i ha hb').1]
    · rw [(hbounds_ne i (by omega)).1] at hx1
      rw [(hbounds_ne i (by omega)).2] at hx2
      rw [(hbounds_ne x (hout i hi (by omega) x hx1 hx2)).1, (hbounds_ne i (by omega)).1]
      exact hcellCst i hi x hx1 hx2
  have hcellCen' : ∀ i, i < n → ∀ x, cst'[i]! ≤ x → x < cen'[i]! → cen'[x]! = cen'[i]! := by
    intro i hi x hx1 hx2
    by_cases hcell : c ≤ i ∧ i < st.cen[c]!
    · obtain ⟨j, hj, ha, hb'⟩ := hin i hcell.1 hcell.2
      rw [(hbounds j hj i ha hb').1] at hx1
      rw [(hbounds j hj i ha hb').2] at hx2
      rw [(hbounds j hj x hx1 hx2).2, (hbounds j hj i ha hb').2]
    · rw [(hbounds_ne i (by omega)).1] at hx1
      rw [(hbounds_ne i (by omega)).2] at hx2
      rw [(hbounds_ne x (hout i hi (by omega) x hx1 hx2)).2, (hbounds_ne i (by omega)).2]
      exact hcellCen i hi x hx1 hx2
  have hwf : Part.WF n { lab := lab', pos := pos', cst := cst', cen := cen' } :=
    ⟨hlab'n, hpos'n, hcst'n, hcen'n, hlab'Lt, hpos'Lt, hpos'Lab, hlab'Pos, hcst'Le, hltCen',
      hcen'Le, hcellCst', hcellCen'⟩
  -- the cell fields
  have hposMem : ∀ v, v < n → c ≤ st.pos[v]! → st.pos[v]! < st.cen[c]! →
      c ≤ pos'[v]! ∧ pos'[v]! < st.cen[c]! := by
    intro v hv ha hb'
    rw [hpos'_in v hv ha hb']
    have := hoff.scatterAt_lt ha hb'
    omega
  have hcellFrag : ∀ v, v < n → c ≤ st.pos[v]! → st.pos[v]! < st.cen[c]! →
      cst'[pos'[v]!]! = fragStart n st.part cnt c cnt[v]! := by
    intro v hv ha hb'
    obtain ⟨j, hj, hjt, hs1, hs2⟩ := hfrag st.pos[v]! ha hb'
    rw [hpos'_in v hv ha hb', (hbounds j hj _ hs1 hs2).1, hfragStart j hj, hjt, hlabPos v hv]
  have hcenFrag : ∀ v, v < n → c ≤ st.pos[v]! → st.pos[v]! < st.cen[c]! →
      cen'[pos'[v]!]! = fragStart n st.part cnt c cnt[v]! +
        cellCount n st.part c (fun u => cnt[u]! == cnt[v]!) := by
    intro v hv ha hb'
    obtain ⟨j, hj, hjt, hs1, hs2⟩ := hfrag st.pos[v]! ha hb'
    have hfs : c + sizesSum sizes 0 j = fragStart n st.part cnt c cnt[v]! := by
      rw [hfragStart j hj, hjt, hlabPos v hv]
    have hsz : sizes[j]! = cellCount n st.part c (fun u => cnt[u]! == cnt[v]!) := by
      rw [hsizes_eq j hj, hcellCount, hjt, hlabPos v hv]
    rw [hpos'_in v hv ha hb', (hbounds j hj _ hs1 hs2).2,
      sizesSum_split sizes (Nat.zero_le j) (Nat.le_succ j), sizesSum_one]
    omega
  rw [splitCell_part_general hb h1 h2 ho hsc hw hbd]
  exact ⟨hwf, fun i _ h => hlab'_ne i h, fun i _ h => (hbounds_ne i h).1,
    fun i _ h => (hbounds_ne i h).2, fun v hv h => hpos'_ne v hv h, hposMem, hcellFrag, hcenFrag⟩

theorem splitCell_spec {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hp : Part.WF n st.part) (hc : c < n) (hcst : st.cst[c]! = c)
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size) :
    SplitOk n st.part cnt c (splitCell cnt c st).part := by
  have hce : st.part.cen[c]! = st.cen[c]! := rfl
  have hcstp : st.part.cst[c]! = c := hcst
  obtain ⟨bc0, ks0, hb⟩ : ∃ bc0 ks0,
      bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0) := ⟨_, _, rfl⟩
  by_cases h1 : (st.cen[c]! - c == 1) = true
  · -- a singleton cell: no two vertices to compare
    rw [splitCell_part_singleton h1]
    have hsing : st.cen[c]! - c = 1 := by simpa using h1
    refine splitOk_of_uniform hp hc hcstp cnt ?_
    intro v w hv hw hvc hwc
    have h2 := (hp.cst_eq_iff hc (hp.posLt v hv)).1 (by rw [hvc, hcstp])
    have h3 := (hp.cst_eq_iff hc (hp.posLt w hw)).1 (by rw [hwc, hcstp])
    rw [hcstp] at h2 h3
    rw [← hp.labPos v hv, ← hp.labPos w hw, show st.part.pos[v]! = st.part.pos[w]! by omega]
  · by_cases h2 : (ks0.size == 1) = true
    · -- one bucket: every vertex of the cell has the same neighbour count
      rw [splitCell_part_one hb h1 h2]
      have hks1 : ks0.size = 1 := by simpa using h2
      refine splitOk_of_uniform hp hc hcstp cnt ?_
      have key : ∀ v, v < n → st.part.cst[st.part.pos[v]!]! = c → cnt[v]! = ks0[0]! := by
        intro v hv hvc
        have h3 := (hp.cst_eq_iff hc (hp.posLt v hv)).1 (by rw [hvc, hcstp])
        rw [hcstp] at h3
        have hpos : 0 < bucketSize st.lab cnt st.part.pos[v]! st.cen[c]! cnt[v]! :=
          bucketSize_pos st.lab cnt (by omega)
            (show cnt[st.part.lab[st.part.pos[v]!]!]! = cnt[v]! by rw [hp.labPos v hv])
        have hbs : bucketSize st.lab cnt st.part.pos[v]! st.cen[c]! cnt[v]!
            ≤ bucketSize st.lab cnt c st.cen[c]! cnt[v]! :=
          bucketSize_mono st.lab cnt (by omega) (by omega)
        have hmem : cnt[v]! ∈ ks0 := by
          rw [← show (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).2 = ks0 by
            rw [hb]]
          exact (bucket_mem (lab := st.lab) (c := c) (ec := st.cen[c]!) hcb hbc cnt[v]!).2
            ⟨hcb v, by omega⟩
        obtain ⟨i, hi, hiv⟩ := mem_iff_getElemD.1 hmem
        rw [hks1] at hi
        rw [← hiv, show i = 0 by omega]
      intro v w hv hw hvc hwc
      rw [key v hv hvc, key w hw hwc]
    · exact splitOk_general hp hc hcst hbc hcb hb h1 h2

theorem sortNats_size (a : Array Nat) : (sortNats a).size = a.size :=
  (sortNats_perm a).length_eq

/-- The fragments of a split cell occupy disjoint ranges of positions: the fragment of `t` ends
before the fragment of any larger count starts. -/
theorem fragStart_disjoint {n : Nat} {p : Part} {cnt : Array Nat} {c t t' : Nat} (h : t < t') :
    fragStart n p cnt c t + cellCount n p c (fun u => cnt[u]! == t)
      ≤ fragStart n p cnt c t' := by
  rw [fragStart, fragStart]
  have hsub : ∑ u ∈ Finset.range t', cellCount n p c (fun w => cnt[w]! == u)
      = ∑ u ∈ Finset.Ico 0 (t + 1), cellCount n p c (fun w => cnt[w]! == u)
        + ∑ u ∈ Finset.Ico (t + 1) t', cellCount n p c (fun w => cnt[w]! == u) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  rw [← Finset.range_eq_Ico, Finset.sum_range_succ] at hsub
  omega

/-- **The split is equivariant.**  Two corresponding cells are split into corresponding
fragments: the fragment of a vertex is determined by its count, and corresponding vertices have
corresponding counts, so the two runs lay their cells out identically. -/
theorem splitOk_partEquiv {n : Nat} {σ : Nat → Nat} {p q p' q' : Part} {cnt cnt' : Array Nat}
    {c : Nat} (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (he : PartEquiv n σ p q)
    (hc : c < n) (hcst : q.cst[c]! = c) (hcnt : ∀ v, v < n → cnt[σ v]! = cnt'[v]!)
    (h1 : SplitOk n p cnt c p') (h2 : SplitOk n q cnt' c q') :
    PartEquiv n σ p' q' := by
  have hcstp : p.cst[c]! = c := by rw [he.cst c hc, hcst]
  have hcen : p.cen[c]! = q.cen[c]! := he.cen c hc
  have hcE : c < p.cen[c]! := hp.ltCen c hc
  have hEn : p.cen[c]! ≤ n := hp.cenLe c hc
  -- the two runs count the same number of cell vertices of each count
  have hcc : ∀ t, cellCount n p c (fun u => cnt[u]! == t)
      = cellCount n q c (fun u => cnt'[u]! == t) := by
    intro t
    rw [cellCount_equiv hσ he c (fun u => cnt[u]! == t)]
    refine cellCount_congr fun w hw _ => ?_
    rw [hcnt w hw]
  have hfs : ∀ t, fragStart n p cnt c t = fragStart n q cnt' c t := by
    intro t
    rw [fragStart, fragStart]
    exact congrArg _ (Finset.sum_congr rfl fun t' _ => hcc t')
  -- a vertex that ends up in the cell was in it to begin with
  have hback : ∀ {r r' : Part} {d : Array Nat}, SplitOk n r d c r' → r.cen[c]! = p.cen[c]! →
      ∀ v, v < n → c ≤ r'.pos[v]! → r'.pos[v]! < p.cen[c]! →
        c ≤ r.pos[v]! ∧ r.pos[v]! < p.cen[c]! := by
    intro r r' d h hcr v hv ha hb
    by_contra hcon
    have hout : r.pos[v]! < c ∨ r.cen[c]! ≤ r.pos[v]! := by omega
    have := h.pos_ne v hv hout
    omega
  -- the fragment boundaries agree at every position of the cell
  have hkey : ∀ i, c ≤ i → i < p.cen[c]! → p'.cst[i]! = q'.cst[i]! ∧ p'.cen[i]! = q'.cen[i]! := by
    intro i ha hb
    have hi : i < n := by omega
    set v := p'.lab[i]! with hv
    set w := q'.lab[i]! with hw
    have hvn : v < n := h1.wf.labLt i hi
    have hwn : w < n := h2.wf.labLt i hi
    have hpv : p'.pos[v]! = i := h1.wf.posLab i hi
    have hqw : q'.pos[w]! = i := h2.wf.posLab i hi
    obtain ⟨hv1, hv2⟩ := hback h1 rfl v hvn (by rw [hpv]; omega) (by rw [hpv]; omega)
    obtain ⟨hw1, hw2⟩ := hback h2 hcen.symm w hwn (by rw [hqw]; omega) (by rw [hqw]; omega)
    have hpcst : p'.cst[i]! = fragStart n p cnt c cnt[v]! := by
      rw [← hpv]; exact h1.cell v hvn hv1 hv2
    have hpcen : p'.cen[i]! = fragStart n p cnt c cnt[v]!
        + cellCount n p c (fun u => cnt[u]! == cnt[v]!) := by
      rw [← hpv]; exact h1.cen_cell v hvn hv1 hv2
    have hqcst : q'.cst[i]! = fragStart n q cnt' c cnt'[w]! := by
      rw [← hqw]; exact h2.cell w hwn hw1 (by omega)
    have hqcen : q'.cen[i]! = fragStart n q cnt' c cnt'[w]!
        + cellCount n q c (fun u => cnt'[u]! == cnt'[w]!) := by
      rw [← hqw]; exact h2.cen_cell w hwn hw1 (by omega)
    -- both counts name a fragment containing `i`, and fragments are disjoint
    have hlo1 : p'.cst[i]! ≤ i := h1.wf.cstLe i hi
    have hhi1 : i < p'.cen[i]! := h1.wf.ltCen i hi
    have hlo2 : q'.cst[i]! ≤ i := h2.wf.cstLe i hi
    have hhi2 : i < q'.cen[i]! := h2.wf.ltCen i hi
    rw [← hfs] at hqcst
    rw [← hfs, ← hcc] at hqcen
    have hteq : cnt[v]! = cnt'[w]! := by
      rcases Nat.lt_trichotomy cnt[v]! cnt'[w]! with hlt | heq | hgt
      · have := fragStart_disjoint (n := n) (p := p) (cnt := cnt) (c := c) hlt
        omega
      · exact heq
      · have := fragStart_disjoint (n := n) (p := p) (cnt := cnt) (c := c) hgt
        omega
    rw [hpcst, hpcen, hqcst, hqcen, hteq]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    by_cases hcell : c ≤ i ∧ i < p.cen[c]!
    · exact (hkey i hcell.1 hcell.2).1
    · rw [h1.cst_ne i hi (by omega), h2.cst_ne i hi (by omega), he.cst i hi]
  · intro i hi
    by_cases hcell : c ≤ i ∧ i < p.cen[c]!
    · exact (hkey i hcell.1 hcell.2).2
    · rw [h1.cen_ne i hi (by omega), h2.cen_ne i hi (by omega), he.cen i hi]
  · intro v hv
    have hσv : σ v < n := hσ.maps v hv
    have hpv : p.pos[σ v]! < n := hp.posLt _ hσv
    have hqv : q.pos[v]! < n := hq.posLt v hv
    by_cases hcell : q.cst[q.pos[v]!]! = c
    · have hpc : p.cst[p.pos[σ v]!]! = c := by rw [he.cell v hv, hcell]
      have hp1 : c ≤ p.pos[σ v]! ∧ p.pos[σ v]! < p.cen[c]! := by
        have := (hp.cst_eq_iff hc hpv).1 (by rw [hpc, hcstp])
        rw [hcstp] at this
        exact this
      have hq1 : c ≤ q.pos[v]! ∧ q.pos[v]! < q.cen[c]! := by
        have := (hq.cst_eq_iff hc hqv).1 (by rw [hcell, hcst])
        rw [hcst] at this
        exact this
      rw [h1.cell (σ v) hσv hp1.1 hp1.2, h2.cell v hv hq1.1 hq1.2, hfs, hcnt v hv]
    · have hpc : p.cst[p.pos[σ v]!]! ≠ c := by rw [he.cell v hv]; exact hcell
      have hq1 : q.pos[v]! < c ∨ q.cen[c]! ≤ q.pos[v]! := by
        by_contra hcon
        exact hcell ((hq.cellCst c hc _ (by omega) (by omega)).trans hcst)
      have hp1 : p.pos[σ v]! < c ∨ p.cen[c]! ≤ p.pos[σ v]! := by
        by_contra hcon
        exact hpc ((hp.cellCst c hc _ (by omega) (by omega)).trans hcstp)
      rw [h1.pos_ne (σ v) hσv hp1, h2.pos_ne v hv hq1,
        h1.cst_ne _ hpv hp1, h2.cst_ne _ hqv hq1, he.cell v hv]

/-! ### Reading off the scratch fields of one `splitCell` step

The same branch equations again, now for the fields the partition proofs ignore: the trace, the
worklist, and the bucket scratch. -/

theorem splitCell_tr_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) :
    (splitCell cnt c st).tr = mixN (mixN st.tr c) cnt[st.lab[c]!]! := by
  rw [splitCell_eq_singleton h]

theorem splitCell_inW_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) : (splitCell cnt c st).inW = st.inW := by
  rw [splitCell_eq_singleton h]

theorem splitCell_bc_singleton {cnt : Array Nat} {c : Nat} {st : SplitState}
    (h : (st.cen[c]! - c == 1) = true) : (splitCell cnt c st).bc = st.bc := by
  rw [splitCell_eq_singleton h]

theorem splitCell_tr_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    (splitCell cnt c st).tr = mixN (mixN st.tr c) ks0[0]! := by
  rw [splitCell_eq_one hb h1 h2]

theorem splitCell_inW_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    (splitCell cnt c st).inW = st.inW := by
  rw [splitCell_eq_one hb h1 h2]

theorem splitCell_bc_one {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : (ks0.size == 1) = true) :
    (splitCell cnt c st).bc = bc0.set! ks0[0]! 0 := by
  rw [splitCell_eq_one hb h1 h2]

theorem splitCell_tr_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat} (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat} (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64} (hbd : boundsFrom (sortNats ks0) sizes
      (sortNats ks0).size 0 st.cst st.cen #[] c (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).tr = tr := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]

theorem splitCell_inW_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat} (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat} (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64} (hbd : boundsFrom (sortNats ks0) sizes
      (sortNats ks0).size 0 st.cst st.cen #[] c (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).inW =
      if st.inW[c]! then markAllFrom starts starts.size 0 st.inW
      else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 st.inW := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]

theorem splitCell_bc_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat} (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat} (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64} (hbd : boundsFrom (sortNats ks0) sizes
      (sortNats ks0).size 0 st.cst st.cen #[] c (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).bc = clearBcFrom (sortNats ks0) (sortNats ks0).size 0 bc2 := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]

/-- **The bucket scratch array is restored.**  Whatever branch it takes, `splitCell` hands back a
`bc` of the same size and again all zero, so the next split can run on it. -/
theorem splitCell_bc {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size) :
    (splitCell cnt c st).bc.size = st.bc.size ∧
      ∀ t, t < st.bc.size → (splitCell cnt c st).bc[t]! = 0 := by
  obtain ⟨bc0, ks0, hb⟩ : ∃ bc0 ks0,
      bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0) := ⟨_, _, rfl⟩
  by_cases h1 : (st.cen[c]! - c == 1) = true
  · rw [splitCell_bc_singleton h1]
    exact ⟨rfl, hbc⟩
  · have e1 : bc0 = (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).1 := by rw [hb]
    have e2 : ks0 = (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).2 := by rw [hb]
    have hbc0size : bc0.size = st.bc.size := by rw [e1, bucketFrom_size]
    have hbc0 : ∀ t, t < st.bc.size → bc0[t]! = bucketSize st.lab cnt c st.cen[c]! t := by
      intro t ht
      rw [e1,
        bucketFrom_getElemD st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] (by omega) t ht,
        hbc t ht, Nat.zero_add]
    have hks0mem : ∀ t, t ∈ ks0 ↔ t < st.bc.size ∧ bucketSize st.lab cnt c st.cen[c]! t ≠ 0 := by
      intro t
      rw [e2]
      exact bucket_mem hcb hbc t
    by_cases h2 : (ks0.size == 1) = true
    · rw [splitCell_bc_one hb h1 h2]
      have hks1 : ks0.size = 1 := by simpa using h2
      have h0lt : ks0[0]! < bc0.size := by
        rw [hbc0size]; exact ((hks0mem _).1 (getElemD_mem (by omega))).1
      refine ⟨by simp [hbc0size], fun t ht => ?_⟩
      by_cases hteq : t = ks0[0]!
      · rw [getElemD_setD h0lt t, ite_eq_left hteq]
      · rw [getElemD_setD_ne hteq, hbc0 t ht]
        by_contra hz
        obtain ⟨i, hi, hiv⟩ := mem_iff_getElemD.1 ((hks0mem t).2 ⟨ht, hz⟩)
        exact hteq (by rw [← hiv, show i = 0 by omega])
    · obtain ⟨sizes, bc1, ho⟩ : ∃ sizes bc1, offsetFrom (sortNats ks0) (sortNats ks0).size 0
          (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1) := ⟨_, _, rfl⟩
      obtain ⟨block, bc2, hsc⟩ : ∃ block bc2, scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
          (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2) := ⟨_, _, rfl⟩
      obtain ⟨lab, pos, hw⟩ : ∃ lab pos,
          writeFrom block c block.size 0 st.lab st.pos = (lab, pos) := ⟨_, _, rfl⟩
      obtain ⟨cst, cen, starts, tr, hbd⟩ : ∃ cst cen starts tr, boundsFrom (sortNats ks0) sizes
          (sortNats ks0).size 0 st.cst st.cen #[] c (mixN st.tr c) = (cst, cen, starts, tr) :=
        ⟨_, _, _, _, rfl⟩
      rw [splitCell_bc_general hb h1 h2 ho hsc hw hbd]
      have e3 : bc1 = (offsetFrom (sortNats ks0) (sortNats ks0).size 0
        (Array.replicate (sortNats ks0).size 0) bc0 0).2 := by rw [ho]
      have e4 : bc2 = (scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
        (Array.replicate (st.cen[c]! - c) 0) bc1).2 := by rw [hsc]
      have hbc2size : bc2.size = st.bc.size := by
        rw [e4, scatterFrom_size2, e3, offsetFrom_size2, hbc0size]
      refine ⟨by rw [clearBcFrom_size, hbc2size], fun t ht => ?_⟩
      by_cases hmem : ∃ j, j < (sortNats ks0).size ∧ (sortNats ks0)[j]! = t
      · obtain ⟨j, hj, hjt⟩ := hmem
        rw [← hjt]
        exact clearBcFrom_mem (sortNats ks0) (sortNats ks0).size 0 bc2 (by omega) j (by omega) hj
          (by rw [hjt, hbc2size]; exact ht)
      · push Not at hmem
        have hnot0 : t ∉ ks0 := by
          intro h
          obtain ⟨j, hj, hjt⟩ := mem_iff_getElemD.1 (sortNats_mem.2 h)
          exact hmem j hj hjt
        have hzero : bucketSize st.lab cnt c st.cen[c]! t = 0 := by
          by_contra hz
          exact hnot0 ((hks0mem t).2 ⟨ht, hz⟩)
        have hne : ∀ i, c ≤ i → i < st.cen[c]! → cnt[st.lab[i]!]! ≠ t := by
          intro i hi1 hi2 he
          have hp1 : 0 < bucketSize st.lab cnt i st.cen[c]! t := bucketSize_pos st.lab cnt hi2 he
          have hp2 := bucketSize_mono st.lab cnt hi1 (Nat.le_of_lt hi2) (t := t)
          omega
        have c1 : (clearBcFrom (sortNats ks0) (sortNats ks0).size 0 bc2)[t]! = bc2[t]! :=
          clearBcFrom_ne (sortNats ks0) (sortNats ks0).size 0 bc2 t
            (fun j' _ hj2 he => hmem j' hj2 he)
        have c2 : bc2[t]! = bc1[t]! := by
          rw [e4]
          exact scatterFrom_bc_ne st.lab cnt st.cen[c]! (st.cen[c]! - c) c _ bc1 t hne
        have c3 : bc1[t]! = bc0[t]! := by
          rw [e3]
          exact offsetFrom_ne (sortNats ks0) (sortNats ks0).size 0 _ bc0 0 t
            (fun i _ hi2 he => hmem i hi2 he.symm)
        rw [c1, c2, c3, hbc0 t ht, hzero]

/-- What the bucketing and offset passes leave behind, in a form that mentions neither the size of
the scratch array nor the order the counts were met in: the counts are listed once each, they are
exactly the counts occurring in the cell, and the fragment sizes are their bucket sizes. -/
theorem bucketFrom_facts {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hbc : ∀ t, t < st.bc.size → st.bc[t]! = 0) (hcb : ∀ (v : Nat), cnt[v]! < st.bc.size)
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0)) :
    ks0.toList.Nodup ∧ (∀ t, t ∈ ks0 ↔ bucketSize st.lab cnt c st.cen[c]! t ≠ 0) ∧
      ∀ (sizes bc1 : Array Nat), offsetFrom (sortNats ks0) (sortNats ks0).size 0
          (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1) →
        sizes.size = (sortNats ks0).size ∧ ∀ j, j < (sortNats ks0).size →
          sizes[j]! = bucketSize st.lab cnt c st.cen[c]! (sortNats ks0)[j]! := by
  have e1 : bc0 = (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).1 := by rw [hb]
  have e2 : ks0 = (bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[]).2 := by rw [hb]
  have hbc0size : bc0.size = st.bc.size := by rw [e1, bucketFrom_size]
  have hbc0 : ∀ t, t < st.bc.size → bc0[t]! = bucketSize st.lab cnt c st.cen[c]! t := by
    intro t ht
    rw [e1, bucketFrom_getElemD st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] (by omega) t ht,
      hbc t ht, Nat.zero_add]
  have hks0nd : ks0.toList.Nodup := by
    have h := bucketFrom_touched st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] hcb
      (touched_empty st.bc fun w hw => hbc w hw)
    rw [← e2] at h
    exact h.nodup
  have hndks : (sortNats ks0).toList.Nodup := (sortNats_perm ks0).nodup_iff.2 hks0nd
  have hksmem : ∀ t, t ∈ ks0 ↔ bucketSize st.lab cnt c st.cen[c]! t ≠ 0 := by
    intro t
    rw [e2]
    refine (bucket_mem hcb hbc t).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, _, _, hi3⟩ := exists_of_bucketSize h
    exact hi3 ▸ hcb st.lab[i]!
  have hkslt : ∀ j, j < (sortNats ks0).size → (sortNats ks0)[j]! < st.bc.size := by
    intro j hj
    obtain ⟨i, _, _, hi3⟩ := exists_of_bucketSize ((hksmem _).1 (sortNats_mem.1 (getElemD_mem hj)))
    exact hi3 ▸ hcb st.lab[i]!
  refine ⟨hks0nd, hksmem, fun sizes bc1 ho => ⟨?_, fun j hj => ?_⟩⟩
  · have h := offsetFrom_size1 (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0
    rw [ho] at h
    rw [h]
    simp
  · have h := offsetFrom_sizes (sortNats ks0) hndks (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 (by omega) (by simp) j hj
    rw [ho] at h
    rw [h, ite_eq_right (by omega), hbc0 _ (hkslt j hj)]

/-- **The scratch fields move in lockstep too.**  Corresponding cells hash to the same trace and
queue the same fragments: the branch taken, the fragment sizes and the fragment starts are all
determined by data the two runs share. -/
theorem splitCell_scratch_equiv {n : Nat} {σ : Nat → Nat} {cnt cnt' : Array Nat} {c : Nat}
    {stp stq : SplitState} (hσ : IsPerm n σ) (hp : Part.WF n stp.part) (hq : Part.WF n stq.part)
    (he : PartEquiv n σ stp.part stq.part) (hc : c < n) (hcst : stq.cst[c]! = c)
    (hcnt : ∀ v, v < n → cnt[σ v]! = cnt'[v]!)
    (hbcp : ∀ t, t < stp.bc.size → stp.bc[t]! = 0) (hcbp : ∀ (v : Nat), cnt[v]! < stp.bc.size)
    (hbcq : ∀ t, t < stq.bc.size → stq.bc[t]! = 0) (hcbq : ∀ (v : Nat), cnt'[v]! < stq.bc.size)
    (htr : stp.tr = stq.tr) (hinW : stp.inW = stq.inW) :
    (splitCell cnt c stp).tr = (splitCell cnt' c stq).tr ∧
      (splitCell cnt c stp).inW = (splitCell cnt' c stq).inW := by
  -- the two partitions have literally the same cell boundaries
  have hcpn : stp.cst.size = n := hp.cstSize
  have hcqn : stq.cst.size = n := hq.cstSize
  have hepn : stp.cen.size = n := hp.cenSize
  have heqn : stq.cen.size = n := hq.cenSize
  have hcstEq : stp.cst = stq.cst :=
    array_extD (by rw [hcpn, hcqn]) (fun i hi => he.cst i (by rw [← hcpn]; exact hi))
  have hcenEq : stp.cen = stq.cen :=
    array_extD (by rw [hepn, heqn]) (fun i hi => he.cen i (by rw [← hepn]; exact hi))
  have hcenc : stp.cen[c]! = stq.cen[c]! := by rw [hcenEq]
  have hcstp : stp.cst[c]! = c := by rw [hcstEq]; exact hcst
  have hcE : c < stp.cen[c]! := hp.ltCen c hc
  -- and count the same number of cell vertices of each count
  have hbs : ∀ t, bucketSize stp.lab cnt c stp.cen[c]! t
      = bucketSize stq.lab cnt' c stq.cen[c]! t := by
    intro t
    have e1 : bucketSize stp.lab cnt c stp.cen[c]! t
        = cellCount n stp.part c (fun u => cnt[u]! == t) := bucketSize_cellCount hp hc hcstp cnt t
    have e2 : bucketSize stq.lab cnt' c stq.cen[c]! t
        = cellCount n stq.part c (fun u => cnt'[u]! == t) := bucketSize_cellCount hq hc hcst cnt' t
    rw [e1, e2, cellCount_equiv hσ he c (fun u => cnt[u]! == t)]
    exact cellCount_congr fun w hw _ => by rw [hcnt w hw]
  obtain ⟨bc0p, ks0p, hbp⟩ : ∃ a b,
      bucketFrom stp.lab cnt stp.cen[c]! (stp.cen[c]! - c) c stp.bc #[] = (a, b) := ⟨_, _, rfl⟩
  obtain ⟨bc0q, ks0q, hbq⟩ : ∃ a b,
      bucketFrom stq.lab cnt' stq.cen[c]! (stq.cen[c]! - c) c stq.bc #[] = (a, b) := ⟨_, _, rfl⟩
  obtain ⟨hndp, hmemp, hszp⟩ := bucketFrom_facts hbcp hcbp hbp
  obtain ⟨hndq, hmemq, hszq⟩ := bucketFrom_facts hbcq hcbq hbq
  -- so they meet the same set of counts, in the same order once sorted
  have hksEq : sortNats ks0p = sortNats ks0q :=
    sortNats_ext hndp hndq fun t => by rw [hmemp t, hmemq t, hbs t]
  have hsizeEq : ks0p.size = ks0q.size := by
    rw [← sortNats_size ks0p, ← sortNats_size ks0q, hksEq]
  by_cases h1 : (stp.cen[c]! - c == 1) = true
  · -- a singleton cell: the only vertex has the same count on both sides
    have h1' : (stq.cen[c]! - c == 1) = true := by rw [← hcenc]; exact h1
    rw [splitCell_tr_singleton h1, splitCell_inW_singleton h1,
      splitCell_tr_singleton h1', splitCell_inW_singleton h1']
    refine ⟨?_, hinW⟩
    have hsing : stp.cen[c]! - c = 1 := by simpa using h1
    have hpos : bucketSize stq.lab cnt' c stq.cen[c]! cnt[stp.lab[c]!]! ≠ 0 := by
      have := bucketSize_pos stp.lab cnt hcE (rfl : cnt[stp.lab[c]!]! = cnt[stp.lab[c]!]!)
      rw [← hbs]
      omega
    obtain ⟨i, hi1, hi2, hi3⟩ := exists_of_bucketSize hpos
    have hic : i = c := by rw [← hcenc] at hi2; omega
    rw [htr, ← hi3, hic]
  · have h1' : ¬(stq.cen[c]! - c == 1) = true := by rw [← hcenc]; exact h1
    by_cases h2 : (ks0p.size == 1) = true
    · -- one bucket: the single count is the same on both sides
      have h2' : (ks0q.size == 1) = true := by rw [← hsizeEq]; exact h2
      rw [splitCell_tr_one hbp h1 h2, splitCell_inW_one hbp h1 h2,
        splitCell_tr_one hbq h1' h2', splitCell_inW_one hbq h1' h2']
      refine ⟨?_, hinW⟩
      have hp1 : ks0p.size = 1 := by simpa using h2
      have hq1 : ks0q.size = 1 := by simpa using h2'
      have hmem : ks0p[0]! ∈ ks0q :=
        (hmemq _).2 (by rw [← hbs]; exact (hmemp _).1 (getElemD_mem (by omega)))
      obtain ⟨j, hj, hjv⟩ := mem_iff_getElemD.1 hmem
      rw [htr, ← hjv, show j = 0 by omega]
    · have h2' : ¬(ks0q.size == 1) = true := by rw [← hsizeEq]; exact h2
      obtain ⟨sizesp, bc1p, hop⟩ : ∃ a b, offsetFrom (sortNats ks0p) (sortNats ks0p).size 0
          (Array.replicate (sortNats ks0p).size 0) bc0p 0 = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨sizesq, bc1q, hoq⟩ : ∃ a b, offsetFrom (sortNats ks0q) (sortNats ks0q).size 0
          (Array.replicate (sortNats ks0q).size 0) bc0q 0 = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨blockp, bc2p, hscp⟩ : ∃ a b, scatterFrom stp.lab cnt stp.cen[c]! (stp.cen[c]! - c) c
          (Array.replicate (stp.cen[c]! - c) 0) bc1p = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨blockq, bc2q, hscq⟩ : ∃ a b, scatterFrom stq.lab cnt' stq.cen[c]! (stq.cen[c]! - c) c
          (Array.replicate (stq.cen[c]! - c) 0) bc1q = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨labp, posp, hwp⟩ : ∃ a b,
          writeFrom blockp c blockp.size 0 stp.lab stp.pos = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨labq, posq, hwq⟩ : ∃ a b,
          writeFrom blockq c blockq.size 0 stq.lab stq.pos = (a, b) := ⟨_, _, rfl⟩
      obtain ⟨cstp, cenp, startsp, trp, hbdp⟩ : ∃ a b d e, boundsFrom (sortNats ks0p) sizesp
          (sortNats ks0p).size 0 stp.cst stp.cen #[] c (mixN stp.tr c) = (a, b, d, e) :=
        ⟨_, _, _, _, rfl⟩
      obtain ⟨cstq, cenq, startsq, trq, hbdq⟩ : ∃ a b d e, boundsFrom (sortNats ks0q) sizesq
          (sortNats ks0q).size 0 stq.cst stq.cen #[] c (mixN stq.tr c) = (a, b, d, e) :=
        ⟨_, _, _, _, rfl⟩
      obtain ⟨hsp1, hsp2⟩ := hszp sizesp bc1p hop
      obtain ⟨hsq1, hsq2⟩ := hszq sizesq bc1q hoq
      -- the fragment sizes agree, hence so do the fragment starts and the trace
      have hsizesEq : sizesp = sizesq := by
        refine array_extD (by rw [hsp1, hsq1, hksEq]) fun j hj => ?_
        rw [hsp1] at hj
        rw [hsp2 j hj, hsq2 j (by rw [← hksEq]; exact hj), hbs, hksEq]
      have hbdEq : (cstp, cenp, startsp, trp) = (cstq, cenq, startsq, trq) := by
        rw [← hbdp, ← hbdq, hksEq, hsizesEq, hcstEq, hcenEq, htr]
      rw [splitCell_tr_general hbp h1 h2 hop hscp hwp hbdp,
        splitCell_inW_general hbp h1 h2 hop hscp hwp hbdp,
        splitCell_tr_general hbq h1' h2' hoq hscq hwq hbdq,
        splitCell_inW_general hbq h1' h2' hoq hscq hwq hbdq]
      simp only [Prod.mk.injEq] at hbdEq
      exact ⟨hbdEq.2.2.2, by rw [hinW, hbdEq.2.2.1, hsizesEq]⟩

/-! ### One refinement step

Everything above is about a single cell.  `splitCellsFrom` walks a list of cells, so the facts have
to be packaged into an invariant that survives the walk. -/

/-- What a split step needs of its state: a well-formed partition, a cleared bucket array, and
counts that index into it. -/
structure SplitInv (n : Nat) (cnt : Array Nat) (st : SplitState) : Prop where
  /-- The partition is well-formed. -/
  wf : Part.WF n st.part
  /-- The bucket scratch has one slot per possible count. -/
  bcSize : st.bc.size = n + 1
  /-- The bucket scratch is cleared. -/
  bcZero : ∀ t, t < st.bc.size → st.bc[t]! = 0
  /-- Every count indexes the bucket scratch. -/
  cntLt : ∀ (v : Nat), cnt[v]! < st.bc.size

/-- What two split states run in parallel share: corresponding partitions, and *identical* trace
and worklist. -/
structure SplitRel (n : Nat) (σ : Nat → Nat) (stp stq : SplitState) : Prop where
  /-- The partitions correspond under `σ`. -/
  part : PartEquiv n σ stp.part stq.part
  /-- The traces agree. -/
  tr : stp.tr = stq.tr
  /-- The worklists agree. -/
  inW : stp.inW = stq.inW

/-- A split step preserves the invariant. -/
theorem splitCell_inv {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hinv : SplitInv n cnt st) (hc : c < n) (hcst : st.cst[c]! = c) :
    SplitInv n cnt (splitCell cnt c st) := by
  obtain ⟨hsize, hzero⟩ :=
    splitCell_bc (cnt := cnt) (c := c) (st := st) hinv.bcZero hinv.cntLt
  exact ⟨(splitCell_spec hinv.wf hc hcst hinv.bcZero hinv.cntLt).wf,
    by rw [hsize]; exact hinv.bcSize, fun t ht => hzero t (by omega),
    fun v => by rw [hsize]; exact hinv.cntLt v⟩

/-- Splitting one cell leaves the other cell starts alone. -/
theorem splitCell_start {n : Nat} {cnt : Array Nat} {c : Nat} {st : SplitState}
    (hinv : SplitInv n cnt st) (hc : c < n) (hcst : st.cst[c]! = c) {c' : Nat} (hc' : c' < n)
    (hne : c' ≠ c) (hcst' : st.cst[c']! = c') : (splitCell cnt c st).cst[c']! = c' := by
  have hout : c' < c ∨ st.cen[c]! ≤ c' := by
    by_contra hcon
    push Not at hcon
    have hcon2 : c' < st.part.cen[c]! := hcon.2
    have h := hinv.wf.cellCst c hc c' (by rw [show st.part.cst[c]! = c from hcst]; omega)
      (by omega)
    rw [show st.part.cst[c]! = c from hcst, show st.part.cst[c']! = c' from hcst'] at h
    exact hne h
  have h := (splitCell_spec hinv.wf hc hcst hinv.bcZero hinv.cntLt).cst_ne c' hc' hout
  rw [show (splitCell cnt c st).part.cst[c']! = (splitCell cnt c st).cst[c']! from rfl,
    show st.part.cst[c']! = st.cst[c']! from rfl] at h
  rw [h, hcst']

/-- A split step preserves the relation: this is step 1 for a single cell. -/
theorem splitCell_rel {n : Nat} {σ : Nat → Nat} {cnt cnt' : Array Nat} {c : Nat}
    {stp stq : SplitState} (hσ : IsPerm n σ) (hip : SplitInv n cnt stp) (hiq : SplitInv n cnt' stq)
    (hr : SplitRel n σ stp stq) (hc : c < n) (hcst : stq.cst[c]! = c)
    (hcnt : ∀ v, v < n → cnt[σ v]! = cnt'[v]!) :
    SplitRel n σ (splitCell cnt c stp) (splitCell cnt' c stq) := by
  have hcstp : stp.cst[c]! = c := (hr.part.cst c hc).trans hcst
  obtain ⟨htr, hinW⟩ := splitCell_scratch_equiv hσ hip.wf hiq.wf hr.part hc hcst hcnt
    hip.bcZero hip.cntLt hiq.bcZero hiq.cntLt hr.tr hr.inW
  exact ⟨splitOk_partEquiv hσ hip.wf hiq.wf hr.part hc hcst hcnt
    (splitCell_spec hip.wf hc hcstp hip.bcZero hip.cntLt)
    (splitCell_spec hiq.wf hc hcst hiq.bcZero hiq.cntLt), htr, hinW⟩

/-- Splitting a list of distinct cells preserves the invariant. -/
theorem splitCellsFrom_inv {n : Nat} {cnt cells : Array Nat} (hnd : cells.toList.Nodup) :
    ∀ (fuel j : Nat) (st : SplitState), SplitInv n cnt st →
      (∀ j', j ≤ j' → j' < cells.size → cells[j']! < n ∧ st.cst[cells[j']!]! = cells[j']!) →
      SplitInv n cnt (splitCellsFrom cnt cells fuel j st)
  | 0, _, st, hinv, _ => hinv
  | fuel + 1, j, st, hinv, hst => by
    rw [splitCellsFrom]
    split
    · exact hinv
    · rename_i hj
      have hjs : j < cells.size := by omega
      refine splitCellsFrom_inv hnd fuel (j + 1) _
        (splitCell_inv hinv (hst j (by omega) hjs).1 (hst j (by omega) hjs).2) fun j' h1 h2 => ?_
      exact ⟨(hst j' (by omega) h2).1, splitCell_start hinv (hst j (by omega) hjs).1
        (hst j (by omega) hjs).2 (hst j' (by omega) h2).1
        (nodup_getElemD_ne hnd h2 hjs (by omega)) (hst j' (by omega) h2).2⟩

/-- **Step 1 for a refinement pass.**  Two runs that split the same list of cells with
corresponding counts stay in correspondence. -/
theorem splitCellsFrom_rel {n : Nat} {σ : Nat → Nat} {cnt cnt' cells : Array Nat}
    (hσ : IsPerm n σ) (hnd : cells.toList.Nodup) (hcnt : ∀ v, v < n → cnt[σ v]! = cnt'[v]!) :
    ∀ (fuel j : Nat) (stp stq : SplitState), SplitInv n cnt stp → SplitInv n cnt' stq →
      SplitRel n σ stp stq →
      (∀ j', j ≤ j' → j' < cells.size → cells[j']! < n ∧ stq.cst[cells[j']!]! = cells[j']!) →
      SplitRel n σ (splitCellsFrom cnt cells fuel j stp) (splitCellsFrom cnt' cells fuel j stq)
  | 0, _, _, _, _, _, hr, _ => hr
  | fuel + 1, j, stp, stq, hip, hiq, hr, hst => by
    rw [splitCellsFrom, splitCellsFrom]
    split
    · exact hr
    · rename_i hj
      have hjs : j < cells.size := by omega
      have hcj : cells[j]! < n := (hst j (by omega) hjs).1
      have hqj : stq.cst[cells[j]!]! = cells[j]! := (hst j (by omega) hjs).2
      have hpj : stp.cst[cells[j]!]! = cells[j]! := (hr.part.cst _ hcj).trans hqj
      refine splitCellsFrom_rel hσ hnd hcnt fuel (j + 1) _ _ (splitCell_inv hip hcj hpj)
        (splitCell_inv hiq hcj hqj) (splitCell_rel hσ hip hiq hr hcj hqj hcnt) fun j' h1 h2 => ?_
      exact ⟨(hst j' (by omega) h2).1, splitCell_start hiq hcj hqj (hst j' (by omega) h2).1
        (nodup_getElemD_ne hnd h2 hjs (by omega)) (hst j' (by omega) h2).2⟩

/-! ### Reading off one refinement step -/

theorem refineStep_eq_empty {G : Graph} {p : Part} {inW : Array Bool} {s : Nat} {tr : UInt64}
    {sc : Scratch} {cnt touched : Array Nat}
    (hc : countFrom G p.lab p.cen[s]! (p.cen[s]! - s) s sc.cnt #[] = (cnt, touched))
    (h : touched.isEmpty = true) :
    refineStep G p inW s tr sc = (p, inW, mixN tr s, sc) := by
  rw [refineStep]
  dsimp only
  rw [hc]
  dsimp only
  exact ite_eq_left h

theorem refineStep_eq {G : Graph} {p : Part} {inW : Array Bool} {s : Nat} {tr : UInt64}
    {sc : Scratch} {cnt touched : Array Nat}
    (hc : countFrom G p.lab p.cen[s]! (p.cen[s]! - s) s sc.cnt #[] = (cnt, touched))
    (h : ¬touched.isEmpty = true) {hit : Array Bool} {collected : Array Nat}
    (hcl : collectFrom p.pos p.cst touched touched.size 0 sc.hit #[] = (hit, collected))
    {st : SplitState}
    (hst : splitCellsFrom cnt (sortNats collected) (sortNats collected).size 0
      { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW := inW,
        tr := mixN tr s, bc := sc.bc } = st) :
    refineStep G p inW s tr sc =
      (st.part, st.inW, st.tr,
        { cnt := clearCntFrom touched touched.size 0 cnt,
          hit := clearHitFrom (sortNats collected) (sortNats collected).size 0 hit,
          bc := st.bc }) := by
  rw [refineStep]
  dsimp only
  rw [hc]
  dsimp only
  rw [ite_eq_right h, hcl]
  dsimp only
  rw [hst]
  rfl

/-! ### The scratch space is restored, and the partition stays well-formed -/

theorem collectFrom_size (pos cst touched : Array Nat) :
    ∀ (fuel j : Nat) (hit : Array Bool) (cells : Array Nat),
      (collectFrom pos cst touched fuel j hit cells).1.size = hit.size
  | 0, _, _, _ => rfl
  | fuel + 1, j, hit, cells => by
    rw [collectFrom]
    split
    · rfl
    · dsimp only
      split
      · exact collectFrom_size pos cst touched fuel (j + 1) hit cells
      · rw [collectFrom_size pos cst touched fuel (j + 1) _ _]
        simp

theorem clearHitFrom_size (cells : Array Nat) : ∀ (fuel j : Nat) (hit : Array Bool),
    (clearHitFrom cells fuel j hit).size = hit.size
  | 0, _, _ => rfl
  | fuel + 1, j, hit => by
    rw [clearHitFrom]
    split
    · rfl
    · rw [clearHitFrom_size cells fuel (j + 1) _]
      simp

/-- Sorting the collected cells changes neither the invariant nor the marks. -/
theorem Collected.sortNats {hit : Array Bool} {cells : Array Nat} (h : Collected hit cells) :
    Collected hit (sortNats cells) :=
  ⟨(sortNats_perm cells).nodup_iff.2 h.nodup, fun c hc => h.lt c (sortNats_mem.1 hc),
    fun c hc => sortNats_mem.trans (h.mem c hc)⟩

/-- A cell has at most `n` members, so counts fit in the bucket array. -/
theorem cellCount_le (n : Nat) (p : Part) (s : Nat) (P : Nat → Bool) : cellCount n p s P ≤ n := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun w => p.cst[p.pos[w]!]! = s ∧ P w = true) (Finset.range n))
  rw [Finset.card_range] at h
  exact h

theorem countFrom_lt {n : Nat} (f : Nat → Nat → Bool) {p : Part} (hp : Part.WF n p) {s : Nat}
    (hs : s < n) (hcst : p.cst[s]! = s) (v : Nat) :
    (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[]).1[v]! < n + 1 := by
  by_cases hv : v < n
  · rw [countFrom_cellCount f hp hs hcst hv]
    have := cellCount_le n p s (fun u => f u v)
    omega
  · rw [getElem!_neg _ v (by rw [countFrom_size]; simpa using hv)]
    exact Nat.succ_pos n

/-- Every vertex the counting phase touches is a vertex — packaged for a named result. -/
theorem countFrom_touched_lt' {n : Nat} (f : Nat → Nat → Bool) (p : Part) (s : Nat)
    {cnt touched : Array Nat}
    (hc : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cnt, touched)) : ∀ v ∈ touched, v < n := by
  intro v hv
  have ht2 : (countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[]).2 = touched := by rw [hc]
  rw [← ht2] at hv
  exact countFrom_touched_lt f p.lab _ s hv

/-- The cells the collection phase gathers are distinct cell starts. -/
theorem collect_start {n : Nat} {p : Part} (hp : Part.WF n p) {touched : Array Nat}
    (htn : ∀ v ∈ touched, v < n) {hit : Array Bool} {collected : Array Nat}
    (hcl : collectFrom p.pos p.cst touched touched.size 0 (Array.replicate n false) #[]
      = (hit, collected)) :
    collected.toList.Nodup ∧ ∀ c ∈ collected, c < n ∧ p.cst[c]! = c := by
  have hhitsz : (Array.replicate n false : Array Bool).size = n := by simp
  have hhit0 : ∀ c, c < n → (Array.replicate n false : Array Bool)[c]! = false := by
    intro c hc0
    rw [getElem!_pos _ c (by simpa using hc0)]
    simp
  have hcl2 : (collectFrom p.pos p.cst touched touched.size 0
      (Array.replicate n false) #[]).2 = collected := by rw [hcl]
  refine ⟨?_, ?_⟩
  · have h := collect_nodup hp htn hhitsz hhit0
    rw [hcl2] at h
    exact h
  · intro c hcmem
    have h := collect_mem hp htn hhitsz hhit0 c
    rw [hcl2] at h
    obtain ⟨v, hv, rfl⟩ := h.1 hcmem
    have h1 : p.pos[v]! < n := hp.posLt v (htn v hv)
    have h2 : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1
    refine ⟨by omega, hp.cellCst p.pos[v]! h1 p.cst[p.pos[v]!]! (le_refl _) ?_⟩
    have := hp.ltCen p.pos[v]! h1
    omega

/-- The state the cell loop starts from satisfies its invariant. -/
theorem splitInv_init {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p) {s : Nat}
    (hs : s < n) (hcst : p.cst[s]! = s) {cnt touched : Array Nat}
    (hc : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cnt, touched)) (inW : Array Bool) (tr' : UInt64) :
    SplitInv n cnt
      { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen,
        inW := inW, tr := tr', bc := (Scratch.empty n).bc } := by
  refine ⟨hp, by simp [Scratch.empty], fun t ht => ?_, fun v => ?_⟩
  · have ht' : t < (Array.replicate (n + 1) 0 : Array Nat).size := ht
    rw [show ((Scratch.empty n).bc)[t]! = (Array.replicate (n + 1) 0 : Array Nat)[t]! from rfl,
      getElem!_pos _ t ht']
    simp
  · change cnt[v]! < ((Scratch.empty n).bc).size
    have h := countFrom_lt f hp hs hcst v
    rw [hc] at h
    have h' : cnt[v]! < n + 1 := h
    have hsz : ((Scratch.empty n).bc).size = n + 1 := by simp [Scratch.empty]
    omega

/-- **What one refinement step leaves behind.**  The partition is still well-formed, the cells it
split are cells of the old partition, and the scratch space is back to its cleared state — the
last point is what lets the worklist loop keep reusing it. -/
theorem refineStep_wf {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p) {s : Nat}
    (hs : s < n) (hcst : p.cst[s]! = s) (inW : Array Bool) (tr : UInt64) :
    Part.WF n (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).1 ∧
      (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).2.2.2 = Scratch.empty n := by
  obtain ⟨cnt, touched, hc⟩ : ∃ cnt touched, countFrom (Graph.ofOracle n f) p.lab p.cen[s]!
      (p.cen[s]! - s) s (Scratch.empty n).cnt #[] = (cnt, touched) := ⟨_, _, rfl⟩
  have hc' : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cnt, touched) := hc
  by_cases hemp : touched.isEmpty = true
  · rw [refineStep_eq_empty hc hemp]
    exact ⟨hp, rfl⟩
  · obtain ⟨hit, collected, hcl⟩ : ∃ hit collected,
        collectFrom p.pos p.cst touched touched.size 0 (Scratch.empty n).hit #[]
          = (hit, collected) := ⟨_, _, rfl⟩
    have hcl' : collectFrom p.pos p.cst touched touched.size 0 (Array.replicate n false) #[]
        = (hit, collected) := hcl
    obtain ⟨st, hst⟩ : ∃ st, splitCellsFrom cnt (sortNats collected) (sortNats collected).size 0
        { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW := inW,
          tr := mixN tr s, bc := (Scratch.empty n).bc } = st := ⟨_, rfl⟩
    -- the touched vertices and the collected cells
    have hhitsz : (Array.replicate n false : Array Bool).size = n := by simp
    have hhit0 : ∀ c, c < n → (Array.replicate n false : Array Bool)[c]! = false := by
      intro c hc0
      rw [getElem!_pos _ c (by simpa using hc0)]
      simp
    have htn : ∀ v ∈ touched, v < n := countFrom_touched_lt' f p s hc'
    obtain ⟨hcolnd, hcolstart⟩ := collect_start hp htn hcl'
    -- the cell loop
    have hinv0 : SplitInv n cnt
        { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen,
          inW := inW, tr := mixN tr s, bc := (Scratch.empty n).bc } :=
      splitInv_init hp hs hcst hc' inW (mixN tr s)
    have hnd : (sortNats collected).toList.Nodup := (sortNats_perm collected).nodup_iff.2 hcolnd
    have hinv : SplitInv n cnt st := by
      rw [← hst]
      refine splitCellsFrom_inv hnd (sortNats collected).size 0 _ hinv0 fun j' _ h2 => ?_
      exact hcolstart _ (sortNats_mem.1 (getElemD_mem h2))
    rw [refineStep_eq hc hemp hcl hst]
    refine ⟨hinv.wf, ?_⟩
    -- the scratch space is back to cleared
    have hcntsz : cnt.size = n := by
      have := countFrom_size (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
        (Array.replicate n 0) #[]
      rw [hc'] at this
      rw [this]
      simp
    have htsp : Touched cnt touched := by
      have h := countFrom_touched_spec (n := n) f p.lab p.cen[s]! s
      rw [hc'] at h
      exact h
    have h1 : clearCntFrom touched touched.size 0 cnt = Array.replicate n 0 := by
      refine array_extD (by rw [clearCntFrom_size, hcntsz]; simp) fun v hv => ?_
      rw [clearCntFrom_size, hcntsz] at hv
      rw [clearCntFrom_zero htsp v (by omega), getElem!_pos _ v (by simpa using hv)]
      simp
    have hcol : Collected hit collected := by
      have hbd : ∀ v ∈ touched,
          p.cst[p.pos[v]!]! < (Array.replicate n false : Array Bool).size := by
        intro v hv
        have h1' : p.pos[v]! < n := hp.posLt v (htn v hv)
        have h2' : p.cst[p.pos[v]!]! ≤ p.pos[v]! := hp.cstLe _ h1'
        rw [hhitsz]
        omega
      have h := collectFrom_collected p.pos p.cst touched touched.size 0
        (Array.replicate n false) #[] hbd
        (collected_empty _ fun c hc0 => hhit0 c (by simpa using hc0))
      rw [hcl'] at h
      exact h
    have hhitsz' : hit.size = n := by
      have := collectFrom_size p.pos p.cst touched touched.size 0 (Array.replicate n false) #[]
      rw [hcl'] at this
      rw [this]
      simp
    have h2 : clearHitFrom (sortNats collected) (sortNats collected).size 0 hit
        = Array.replicate n false := by
      refine array_extD (by rw [clearHitFrom_size, hhitsz']; simp) fun v hv => ?_
      rw [clearHitFrom_size, hhitsz'] at hv
      rw [clearHitFrom_zero hcol.sortNats v (by omega), getElem!_pos _ v (by simpa using hv)]
      simp
    have hbcsz : st.bc.size = n + 1 := hinv.bcSize
    have h3 : st.bc = Array.replicate (n + 1) 0 := by
      refine array_extD (by rw [hbcsz]; simp) fun t ht => ?_
      rw [hinv.bcZero t ht, getElem!_pos _ t (by simp; omega)]
      simp
    simp only [Scratch.empty, Scratch.mk.injEq]
    exact ⟨h1, h2, h3⟩


/-! ### One refinement step is equivariant -/

/-- **Step 1.**  One refinement pass commutes with relabelling: run on corresponding partitions
with corresponding adjacency oracles it produces corresponding partitions, the same worklist and
the same trace. -/
theorem refineStep_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (he : PartEquiv n σ p q)
    {s : Nat} (hs : s < n) (hcst : q.cst[s]! = s) (inW : Array Bool) (tr : UInt64) :
    PartEquiv n σ (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).1
        (refineStep (Graph.ofOracle n fun a b => f (σ a) (σ b)) q inW s tr (Scratch.empty n)).1 ∧
      (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).2.1
        = (refineStep (Graph.ofOracle n fun a b => f (σ a) (σ b)) q inW s tr
            (Scratch.empty n)).2.1 ∧
      (refineStep (Graph.ofOracle n f) p inW s tr (Scratch.empty n)).2.2.1
        = (refineStep (Graph.ofOracle n fun a b => f (σ a) (σ b)) q inW s tr
            (Scratch.empty n)).2.2.1 := by
  have hcstp : p.cst[s]! = s := (he.cst s hs).trans hcst
  obtain ⟨cntp, tp, hcp⟩ : ∃ cnt touched, countFrom (Graph.ofOracle n f) p.lab p.cen[s]!
      (p.cen[s]! - s) s (Scratch.empty n).cnt #[] = (cnt, touched) := ⟨_, _, rfl⟩
  obtain ⟨cntq, tq, hcq⟩ : ∃ cnt touched, countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b))
      q.lab q.cen[s]! (q.cen[s]! - s) s (Scratch.empty n).cnt #[] = (cnt, touched) := ⟨_, _, rfl⟩
  have hcp' : countFrom (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[] = (cntp, tp) := hcp
  have hcq' : countFrom (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]!
      (q.cen[s]! - s) s (Array.replicate n 0) #[] = (cntq, tq) := hcq
  -- corresponding counts
  have hcnt : ∀ v, v < n → cntp[σ v]! = cntq[v]! := by
    intro v hv
    have h := countFrom_equiv (f := f) hσ hp hq he hs hcst hv
    rw [hcp', hcq'] at h
    exact h
  have htnp : ∀ v ∈ tp, v < n := countFrom_touched_lt' f p s hcp'
  have htnq : ∀ v ∈ tq, v < n := countFrom_touched_lt' (fun a b => f (σ a) (σ b)) q s hcq'
  have htsp : Touched cntp tp := by
    have h := countFrom_touched_spec (n := n) f p.lab p.cen[s]! s
    rw [hcp'] at h
    exact h
  have htsq : Touched cntq tq := by
    have h := countFrom_touched_spec (n := n) (fun a b => f (σ a) (σ b)) q.lab q.cen[s]! s
    rw [hcq'] at h
    exact h
  have hszp : cntp.size = n := by
    have h := countFrom_size (Graph.ofOracle n f) p.lab p.cen[s]! (p.cen[s]! - s) s
      (Array.replicate n 0) #[]
    rw [hcp'] at h
    simpa using h
  have hszq : cntq.size = n := by
    have h := countFrom_size (Graph.ofOracle n fun a b => f (σ a) (σ b)) q.lab q.cen[s]!
      (q.cen[s]! - s) s (Array.replicate n 0) #[]
    rw [hcq'] at h
    simpa using h
  -- one side touches something exactly when the other does
  have hiff : tp.isEmpty = true ↔ tq.isEmpty = true := by
    rw [arr_isEmpty_iff, arr_isEmpty_iff]
    constructor
    · intro h v hv
      have hvn : v < n := htnq v hv
      have hmaps : σ v < n := hσ.maps v hvn
      have hne : cntq[v]! ≠ 0 := (htsq.mem v (by omega)).1 hv
      exact h (σ v) ((htsp.mem (σ v) (by omega)).2 (by rw [hcnt v hvn]; exact hne))
    · intro h v hv
      have hvn : v < n := htnp v hv
      obtain ⟨w, hw, hwv⟩ := hσ.surj hvn
      have hne : cntp[v]! ≠ 0 := (htsp.mem v (by omega)).1 hv
      refine h w ((htsq.mem w (by omega)).2 ?_)
      rw [← hcnt w hw, hwv]
      exact hne
  by_cases hep : tp.isEmpty = true
  · rw [refineStep_eq_empty hcp hep, refineStep_eq_empty hcq (hiff.1 hep)]
    exact ⟨he, rfl, rfl⟩
  · have heq : ¬tq.isEmpty = true := fun h => hep (hiff.2 h)
    obtain ⟨hitp, colp, hclp⟩ : ∃ hit col, collectFrom p.pos p.cst tp tp.size 0
        (Scratch.empty n).hit #[] = (hit, col) := ⟨_, _, rfl⟩
    obtain ⟨hitq, colq, hclq⟩ : ∃ hit col, collectFrom q.pos q.cst tq tq.size 0
        (Scratch.empty n).hit #[] = (hit, col) := ⟨_, _, rfl⟩
    have hclp' : collectFrom p.pos p.cst tp tp.size 0 (Array.replicate n false) #[]
        = (hitp, colp) := hclp
    have hclq' : collectFrom q.pos q.cst tq tq.size 0 (Array.replicate n false) #[]
        = (hitq, colq) := hclq
    have hcolEq : sortNats colp = sortNats colq := by
      have h := collect_equiv (f := f) hσ hp hq he hs hcst (hit := Array.replicate n false)
        (by simp) (fun c hc0 => by rw [getElem!_pos _ c (by simpa using hc0)]; simp)
        (tp := tp) (tq := tq) (by rw [hcp']) (by rw [hcq'])
      rw [hclp', hclq'] at h
      exact h
    obtain ⟨_, hstartq⟩ := collect_start hq htnq hclq'
    obtain ⟨hndq, _⟩ := collect_start hq htnq hclq'
    obtain ⟨stp, hstp⟩ : ∃ st, splitCellsFrom cntp (sortNats colp) (sortNats colp).size 0
        { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW := inW,
          tr := mixN tr s, bc := (Scratch.empty n).bc } = st := ⟨_, rfl⟩
    obtain ⟨stq, hstq⟩ : ∃ st, splitCellsFrom cntq (sortNats colq) (sortNats colq).size 0
        { lab := q.lab, pos := q.pos, cst := q.cst, cen := q.cen, inW := inW,
          tr := mixN tr s, bc := (Scratch.empty n).bc } = st := ⟨_, rfl⟩
    have hrel : SplitRel n σ stp stq := by
      rw [← hstp, ← hstq, hcolEq]
      refine splitCellsFrom_rel hσ ((sortNats_perm colq).nodup_iff.2 hndq) hcnt _ 0 _ _
        (splitInv_init hp hs hcstp hcp' inW (mixN tr s))
        (splitInv_init hq hs hcst hcq' inW (mixN tr s)) ⟨he, rfl, rfl⟩ fun j' _ h2 => ?_
      exact hstartq _ (sortNats_mem.1 (getElemD_mem h2))
    rw [refineStep_eq hcp hep hclp hstp, refineStep_eq hcq heq hclq hstq]
    exact ⟨hrel.part, hrel.inW, hrel.tr⟩

/-! ### Reading off the worklist loop -/

theorem refineLoop_none {G : Graph} {fuel : Nat} {p : Part} {inW : Array Bool} {tr : UInt64}
    {sc : Scratch} (hfs : firstSet inW = none) :
    refineLoop G (fuel + 1) p inW tr sc = (p, tr) := by
  rw [refineLoop, hfs]

theorem refineLoop_step {G : Graph} {fuel : Nat} {p : Part} {inW : Array Bool} {tr : UInt64}
    {sc : Scratch} {s : Nat} (hfs : firstSet inW = some s)
    (hg : (s < G.n && p.cst[s]! == s) = true)
    {p' : Part} {inW' : Array Bool} {tr' : UInt64} {sc' : Scratch}
    (hstep : refineStep G p (inW.set! s false) s tr sc = (p', inW', tr', sc')) :
    refineLoop G (fuel + 1) p inW tr sc = refineLoop G fuel p' inW' tr' sc' := by
  rw [refineLoop, hfs]
  dsimp only
  rw [ite_eq_left hg, hstep]

theorem refineLoop_skip {G : Graph} {fuel : Nat} {p : Part} {inW : Array Bool} {tr : UInt64}
    {sc : Scratch} {s : Nat} (hfs : firstSet inW = some s)
    (hg : (s < G.n && p.cst[s]! == s) = false) :
    refineLoop G (fuel + 1) p inW tr sc = refineLoop G fuel p (inW.set! s false) tr sc := by
  rw [refineLoop, hfs]
  dsimp only
  rw [ite_eq_right (by rw [hg]; exact Bool.false_ne_true)]

/-! ### The worklist loop is equivariant -/

/-- **Step 1 for a whole refinement.**  Two runs of the worklist loop on corresponding partitions
stay in correspondence and produce the same trace.  The two runs pop the same positions in the
same order, because the worklist is literally the same array in both. -/
theorem refineLoop_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ) :
    ∀ (fuel : Nat) (p q : Part) (inW : Array Bool) (tr : UInt64),
      Part.WF n p → Part.WF n q → PartEquiv n σ p q →
        PartEquiv n σ (refineLoop (Graph.ofOracle n f) fuel p inW tr (Scratch.empty n)).1
            (refineLoop (Graph.ofOracle n fun a b => f (σ a) (σ b)) fuel q inW tr
              (Scratch.empty n)).1
          ∧ (refineLoop (Graph.ofOracle n f) fuel p inW tr (Scratch.empty n)).2
            = (refineLoop (Graph.ofOracle n fun a b => f (σ a) (σ b)) fuel q inW tr
              (Scratch.empty n)).2
  | 0, _, _, _, _, _, _, he => ⟨he, rfl⟩
  | fuel + 1, p, q, inW, tr, hp, hq, he => by
    cases hfs : firstSet inW with
    | none =>
      rw [refineLoop_none hfs, refineLoop_none hfs]
      exact ⟨he, rfl⟩
    | some s =>
      by_cases hg : s < n ∧ q.cst[s]! = s
      · obtain ⟨hsn, hcs⟩ := hg
        have hpcs : p.cst[s]! = s := (he.cst s hsn).trans hcs
        obtain ⟨p1, i1, t1, sc1, hstep1⟩ : ∃ p1 i1 t1 sc1, refineStep (Graph.ofOracle n f) p
          (inW.set! s false) s tr (Scratch.empty n) = (p1, i1, t1, sc1) := ⟨_, _, _, _, rfl⟩
        obtain ⟨q1, j1, u1, sd1, hstep2⟩ : ∃ q1 j1 u1 sd1,
          refineStep (Graph.ofOracle n fun a b => f (σ a) (σ b)) q (inW.set! s false) s tr
            (Scratch.empty n) = (q1, j1, u1, sd1) := ⟨_, _, _, _, rfl⟩
        have hwf1 := refineStep_wf (f := f) hp hsn hpcs (inW.set! s false) tr
        have hwf2 := refineStep_wf (f := fun a b => f (σ a) (σ b)) hq hsn hcs (inW.set! s false) tr
        have heq := refineStep_equiv (f := f) hσ hp hq he hsn hcs (inW.set! s false) tr
        rw [hstep1] at hwf1
        rw [hstep2] at hwf2
        rw [hstep1, hstep2] at heq
        have hwfp1 : Part.WF n p1 := hwf1.1
        have hwfq1 : Part.WF n q1 := hwf2.1
        have hsc1 : sc1 = Scratch.empty n := hwf1.2
        have hsd1 : sd1 = Scratch.empty n := hwf2.2
        have hpq1 : PartEquiv n σ p1 q1 := heq.1
        have hij : i1 = j1 := heq.2.1
        have htu : t1 = u1 := heq.2.2
        rw [refineLoop_step hfs (by simp [hpcs, hsn]) hstep1,
          refineLoop_step hfs (by simp [hcs, hsn]) hstep2, hsc1, hsd1, hij, htu]
        exact refineLoop_equiv hσ fuel p1 q1 j1 u1 hwfp1 hwfq1 hpq1
      · by_cases hsn : s < n
        · have hcs : ¬(q.cst[s]! = s) := fun h => hg ⟨hsn, h⟩
          have hpcs : ¬(p.cst[s]! = s) := by rw [he.cst s hsn]; exact hcs
          rw [refineLoop_skip hfs (by simp [hpcs]), refineLoop_skip hfs (by simp [hcs])]
          exact refineLoop_equiv hσ fuel p q (inW.set! s false) tr hp hq he
        · rw [refineLoop_skip hfs (by simp [hsn]), refineLoop_skip hfs (by simp [hsn])]
          exact refineLoop_equiv hσ fuel p q (inW.set! s false) tr hp hq he

/-- The worklist loop keeps the partition well-formed. -/
theorem refineLoop_wf {n : Nat} {f : Nat → Nat → Bool} :
    ∀ (fuel : Nat) (p : Part) (inW : Array Bool) (tr : UInt64), Part.WF n p →
      Part.WF n (refineLoop (Graph.ofOracle n f) fuel p inW tr (Scratch.empty n)).1
  | 0, _, _, _, hp => hp
  | fuel + 1, p, inW, tr, hp => by
    cases hfs : firstSet inW with
    | none =>
      rw [refineLoop_none hfs]
      exact hp
    | some s =>
      by_cases hg : s < n ∧ p.cst[s]! = s
      · obtain ⟨hsn, hcs⟩ := hg
        obtain ⟨p1, i1, t1, sc1, hstep⟩ : ∃ p1 i1 t1 sc1, refineStep (Graph.ofOracle n f) p
          (inW.set! s false) s tr (Scratch.empty n) = (p1, i1, t1, sc1) := ⟨_, _, _, _, rfl⟩
        have hwf := refineStep_wf (f := f) hp hsn hcs (inW.set! s false) tr
        rw [hstep] at hwf
        rw [refineLoop_step hfs (by simp [hcs, hsn]) hstep, show sc1 = Scratch.empty n from hwf.2]
        exact refineLoop_wf fuel p1 i1 t1 hwf.1
      · by_cases hsn : s < n
        · have hcs : ¬(p.cst[s]! = s) := fun h => hg ⟨hsn, h⟩
          rw [refineLoop_skip hfs (by simp [hcs])]
          exact refineLoop_wf fuel p (inW.set! s false) tr hp
        · rw [refineLoop_skip hfs (by simp [hsn])]
          exact refineLoop_wf fuel p (inW.set! s false) tr hp

/-! ### Refinement from a partition, and from the unit partition -/

theorem refine_wf {n : Nat} {f : Nat → Nat → Bool} {p : Part} (hp : Part.WF n p)
    (inW : Array Bool) (tr : UInt64) : Part.WF n (refine (Graph.ofOracle n f) p inW tr).1 := by
  rw [refine]
  exact refineLoop_wf _ p inW tr hp

theorem refine_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (he : PartEquiv n σ p q)
    (inW : Array Bool) (tr : UInt64) :
    PartEquiv n σ (refine (Graph.ofOracle n f) p inW tr).1
        (refine (Graph.ofOracle n fun a b => f (σ a) (σ b)) q inW tr).1
      ∧ (refine (Graph.ofOracle n f) p inW tr).2
        = (refine (Graph.ofOracle n fun a b => f (σ a) (σ b)) q inW tr).2 := by
  rw [refine, refine]
  exact refineLoop_equiv hσ _ p q inW tr hp hq he

theorem initialRefine_wf {n : Nat} (f : Nat → Nat → Bool) :
    Part.WF n (initialRefine (Graph.ofOracle n f)).1 := by
  rw [initialRefine]
  exact refine_wf (unit_wf n) _ _

/-- **Step 1.**  The initial equitable refinement is equivariant. -/
theorem initialRefine_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ) :
    PartEquiv n σ (initialRefine (Graph.ofOracle n f)).1
        (initialRefine (Graph.ofOracle n fun a b => f (σ a) (σ b))).1
      ∧ (initialRefine (Graph.ofOracle n f)).2
        = (initialRefine (Graph.ofOracle n fun a b => f (σ a) (σ b))).2 := by
  rw [initialRefine, initialRefine]
  exact refine_equiv hσ (unit_wf n) (unit_wf n) (partEquiv_unit n σ) _ _

/-! ## Certificate readback

The search compares packed certificates; `certOf_get` below turns an equality of certificates
back into an equality of adjacency entries, which is what `Spec.LabellingInvariant` asks for. -/

/-- Bit `j` of row `i` of a certificate packed by `certBits`. -/
def certGet (n : Nat) (c : Array UInt64) (i j : Nat) : Bool :=
  (c[i * rowWords n + j / 64]!).toBitVec.getLsbD (63 - j % 64)

/-- The accumulator invariant of `certRow`: `acc` holds the bits of columns
`64 * (j / 64) … j - 1`, right-aligned, with column `j - 1` at bit 0. -/
def AccOk (b : Nat → Bool) (j : Nat) (acc : UInt64) : Prop :=
  ∀ t, t < 64 → acc.toBitVec.getLsbD t = (decide (t + 64 * (j / 64) < j) && b (j - 1 - t))

theorem certRow_spec (n : Nat) (b : Nat → Bool) (base : Nat) :
    ∀ (fuel j : Nat) (acc : UInt64) (out res : Array UInt64), j + fuel = n →
      base + rowWords n ≤ out.size → AccOk b j acc →
      certRow n b fuel j acc (base + j / 64) out = res →
      res.size = out.size
      ∧ (∀ x, (x < base + j / 64 ∨ base + rowWords n ≤ x) → res[x]! = out[x]!)
      ∧ (∀ j', j' < n → 64 * (j / 64) ≤ j' →
          (res[base + j' / 64]!).toBitVec.getLsbD (63 - j' % 64) = b j') := by
  intro fuel
  induction fuel with
  | zero =>
    intro j acc out res hj hsz hacc hres
    have hj' : n = j := by omega
    subst hj'
    have hrwn : rowWords n = (n + 63) / 64 := rfl
    rw [certRow] at hres
    by_cases hm : n % 64 = 0
    · rw [ite_eq_right (by simp [hm])] at hres
      subst hres
      refine ⟨rfl, fun x _ => rfl, ?_⟩
      intro j' hj' hge
      omega
    · rw [ite_eq_left (by simp [hm])] at hres
      have hk : base + n / 64 < out.size := by omega
      subst hres
      refine ⟨by simp, ?_, ?_⟩
      · intro x hx
        exact getElemD_setD_ne (by omega)
      · intro j' hj' hge
        have hq : j' / 64 = n / 64 := by omega
        rw [hq, getElemD_setD hk _, ite_eq_left rfl,
          shl_natshift _ _ (by omega), BitVec.getLsbD_shiftLeft]
        have hr : j' % 64 < n % 64 := by omega
        rw [decide_eq_true (show 63 - j' % 64 < 64 by omega),
          decide_eq_false (show ¬ (63 - j' % 64 < 64 - n % 64) by omega)]
        simp only [Bool.true_and, Bool.not_false]
        rw [hacc (63 - j' % 64 - (64 - n % 64)) (by omega),
          decide_eq_true (show 63 - j' % 64 - (64 - n % 64) + 64 * (n / 64) < n by omega)]
        simp only [Bool.true_and]
        congr 1
        omega
  | succ fuel ih =>
    intro j acc out res hj hsz hacc hres
    have hjn : j < n := by omega
    have hrwn : rowWords n = (n + 63) / 64 := rfl
    rw [certRow] at hres
    set acc' := acc <<< 1 ||| (if b j then 1 else 0) with hacc'def
    have hacc'ok : ∀ t, t < 64 → acc'.toBitVec.getLsbD t
        = (decide (t + 64 * (j / 64) < j + 1) && b (j - t)) := by
      intro t ht
      rw [hacc'def, shl_bit _ _ _ ht]
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · rw [ite_eq_left rfl, decide_eq_true (show 0 + 64 * (j / 64) < j + 1 by omega)]
        simp
      · rw [ite_eq_right (by omega), hacc (t - 1) (by omega)]
        have h1 : decide (t - 1 + 64 * (j / 64) < j) = decide (t + 64 * (j / 64) < j + 1) := by
          simp only [decide_eq_decide]; omega
        have h2 : j - 1 - (t - 1) = j - t := by omega
        rw [h1, h2]
    have hrw : j / 64 < rowWords n := by
      rw [rowWords]; omega
    by_cases h64 : (j + 1) % 64 = 0
    · rw [ite_eq_left (by simp [h64])] at hres
      have hq : base + j / 64 + 1 = base + (j + 1) / 64 := by omega
      rw [hq] at hres
      have hk : base + j / 64 < out.size := by omega
      have hsz' : base + rowWords n ≤ (out.set! (base + j / 64) acc').size := by simp; omega
      have hzero : AccOk b (j + 1) 0 := by
        intro t ht
        rw [decide_eq_false (show ¬ (t + 64 * ((j + 1) / 64) < j + 1) by omega)]
        simp
      obtain ⟨hsize, hunch, hbits⟩ := ih (j + 1) 0 _ res (by omega) hsz' hzero hres
      refine ⟨by rw [hsize]; simp, ?_, ?_⟩
      · intro x hx
        rw [hunch x (by omega), getElemD_setD_ne (by omega)]
      · intro j' hj' hge
        by_cases hlt : 64 * ((j + 1) / 64) ≤ j'
        · exact hbits j' hj' hlt
        · have hq' : j' / 64 = j / 64 := by omega
          rw [hq', hunch _ (by omega), getElemD_setD hk _, ite_eq_left rfl,
            hacc'ok (63 - j' % 64) (by omega),
            decide_eq_true (show 63 - j' % 64 + 64 * (j / 64) < j + 1 by omega)]
          simp only [Bool.true_and]
          congr 1
          omega
    · rw [ite_eq_right (by simp [h64])] at hres
      have hq : (j + 1) / 64 = j / 64 := by omega
      have hacc'ok' : AccOk b (j + 1) acc' := by
        intro t ht
        rw [hacc'ok t ht, hq]
        congr 2
      obtain ⟨hsize, hunch, hbits⟩ :=
        ih (j + 1) acc' out res (by omega) hsz hacc'ok' (by rw [hq]; exact hres)
      exact ⟨hsize, fun x hx => hunch x (by omega), fun j' hj' hge => hbits j' hj' (by omega)⟩

theorem certRowsFrom_spec (n : Nat) (bit : Nat → Nat → Bool) :
    ∀ (fuel i : Nat) (out res : Array UInt64), i + fuel = n → n * rowWords n ≤ out.size →
      certRowsFrom n bit (rowWords n) fuel i out = res →
      res.size = out.size
      ∧ (∀ x, x < i * rowWords n → res[x]! = out[x]!)
      ∧ (∀ i' j', i ≤ i' → i' < n → j' < n → certGet n res i' j' = bit i' j') := by
  intro fuel
  induction fuel with
  | zero =>
    intro i out res hi hsz hres
    rw [certRowsFrom] at hres
    subst hres
    exact ⟨rfl, fun _ _ => rfl, fun i' j' h1 h2 _ => absurd h2 (by omega)⟩
  | succ fuel ih =>
    intro i out res hi hsz hres
    rw [certRowsFrom] at hres
    have hrwn : rowWords n = (n + 63) / 64 := rfl
    have hmul2 : i * rowWords n + rowWords n = (i + 1) * rowWords n := (Nat.succ_mul _ _).symm
    have hmul : i * rowWords n + rowWords n ≤ n * rowWords n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have hcr := certRow_spec n (bit i) (i * rowWords n) n 0 0 out _ (by omega)
      (by omega) (fun t ht => by simp) rfl
    simp only [Nat.zero_div, Nat.add_zero] at hcr
    obtain ⟨hsz1, hunch1, hbits1⟩ := hcr
    obtain ⟨hsize, hunch, hbits⟩ := ih (i + 1) _ res (by omega) (by omega) hres
    refine ⟨by omega, ?_, ?_⟩
    · intro x hx
      rw [hunch x (by omega), hunch1 x (Or.inl hx)]
    · intro i' j' h1 h2 h3
      rcases Nat.lt_or_ge i i' with h | h
      · exact hbits i' j' (by omega) h2 h3
      · have hii : i' = i := by omega
        subst hii
        have hjw : j' / 64 < rowWords n := by omega
        rw [certGet, hunch _ (by rw [Nat.succ_mul]; omega)]
        exact hbits1 j' h3 (by omega)

theorem certBits_get (n : Nat) (bit : Nat → Nat → Bool) {i j : Nat} (hi : i < n) (hj : j < n) :
    certGet n (certBits n bit) i j = bit i j := by
  have h := certRowsFrom_spec n bit n 0 (Array.replicate (n * rowWords n) 0) _ (by omega)
    (by simp) rfl
  exact h.2.2 i j (Nat.zero_le _) hi hj

/-- Reading the packed certificate back: bit `(i, j)` of `certOf G lab` is the adjacency of the
`i`-th and `j`-th vertices in the order `lab`. -/
theorem certOf_get {G : Graph} {lab : Array Nat} {i j : Nat} (hi : i < G.n) (hj : j < G.n) :
    certGet G.n (certOf G lab) i j = (G.adj[lab[i]!]!)[lab[j]!]! :=
  certBits_get _ _ hi hj

theorem addAuto_best (st : St) (g : Array Nat) : (st.addAuto g).best = st.best := by
  rw [St.addAuto]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem addAuto_first (st : St) (g : Array Nat) : (st.addAuto g).first = st.first := by
  rw [St.addAuto]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- `leafUpdate` either keeps the incumbent or replaces it with the new leaf. -/
theorem leafUpdate_best (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) :
    (leafUpdate G path invPath lab st).best = st.best
      ∨ (leafUpdate G path invPath lab st).best
          = some { path, invPath, cert := certOf G lab, lab } := by
  rw [leafUpdate]
  simp only [Id.run]
  repeat' split
  all_goals (try exact Or.inr rfl)
  all_goals (try exact Or.inl rfl)
  all_goals (try exact Or.inl (addAuto_best _ _))
  all_goals (try exact Or.inl ((addAuto_best _ _).trans (addAuto_best _ _)))

/-- Same for the first leaf, which is only ever set once. -/
theorem leafUpdate_first (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) :
    (leafUpdate G path invPath lab st).first = st.first
      ∨ (leafUpdate G path invPath lab st).first
          = some { path, invPath, cert := certOf G lab, lab } := by
  rw [leafUpdate]
  simp only [Id.run]
  repeat' split
  all_goals (try exact Or.inr rfl)
  all_goals (try exact Or.inl rfl)
  all_goals (try exact Or.inl (addAuto_first _ _))
  all_goals (try exact Or.inl ((addAuto_first _ _).trans (addAuto_first _ _)))
  all_goals (try exact Or.inr (addAuto_first _ _))

/-! ## The search only ever stores honest leaves

Two facts about every leaf the search records: its labelling is a permutation of the vertices,
and its certificate is the certificate *of that labelling*.  Together they say that the winner
returned by `canonical` passes the `isPermArray` check of `canonicalLabellingOfOracle` and that
`Result.cert` and `Result.lab` belong together, which is what turns an equality of certificates
into `Spec.LabellingInvariant`. -/
/-- A stored leaf whose labelling is a vertex permutation and whose certificate matches it. -/
structure LeafOk (G : Graph) (l : Leaf) : Prop where
  /-- The labelling has one entry per vertex. -/
  size : l.lab.size = G.n
  /-- Its entries are vertices. -/
  lt : ∀ i, i < G.n → l.lab[i]! < G.n
  /-- Distinct positions hold distinct vertices. -/
  inj : ∀ i, i < G.n → ∀ j, j < G.n → l.lab[i]! = l.lab[j]! → i = j
  /-- The stored certificate is the one the labelling determines. -/
  cert : l.cert = certOf G l.lab

/-- Every leaf a state remembers is honest. -/
def StOk (G : Graph) (st : St) : Prop :=
  (∀ l, st.best = some l → LeafOk G l) ∧ (∀ l, st.first = some l → LeafOk G l)

theorem leafOk_of_wf {n : Nat} {G : Graph} (hn : G.n = n) {p : Part} (hp : Part.WF n p)
    (path : Array Nat) (invPath : Array UInt64) :
    LeafOk G { path, invPath, cert := certOf G p.lab, lab := p.lab } := by
  subst hn
  exact ⟨hp.labSize, fun i hi => hp.labLt i hi, fun i hi j hj h => by
    have h1 := hp.posLab i hi
    have h2 := hp.posLab j hj
    have h' : p.lab[i]! = p.lab[j]! := h
    rw [h'] at h1
    omega, rfl⟩

theorem leafUpdate_ok {G : Graph} {path : Array Nat} {invPath : Array UInt64} {lab : Array Nat}
    {st : St} (hl : LeafOk G { path, invPath, cert := certOf G lab, lab }) (hst : StOk G st) :
    StOk G (leafUpdate G path invPath lab st) := by
  refine ⟨fun l hb => ?_, fun l hf => ?_⟩
  · rcases leafUpdate_best G path invPath lab st with h | h
    · exact hst.1 l (h ▸ hb)
    · rw [h] at hb; cases hb; exact hl
  · rcases leafUpdate_first G path invPath lab st with h | h
    · exact hst.2 l (h ▸ hf)
    · rw [h] at hf; cases hf; exact hl

theorem StOk.addAuto {G : Graph} {st : St} (h : StOk G st) (g : Array Nat) :
    StOk G (st.addAuto g) :=
  ⟨fun l hb => h.1 l ((addAuto_best st g) ▸ hb), fun l hf => h.2 l ((addAuto_first st g) ▸ hf)⟩

theorem individualize_wf' {n : Nat} {p : Part} (hp : Part.WF n p) {v : Nat} (hv : v < n) :
    Part.WF n (individualize p v).1 :=
  individualize_wf hp ⟨hv, rfl, rfl, rfl, rfl⟩

theorem pruneNode_ok {G : Graph} {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') (hst : StOk G st) : StOk G st' := by
  rw [pruneNode] at h
  split at h
  · cases h; exact hst
  · split at h
    · exact absurd h (by simp)
    · cases h; exact ⟨by simp, hst.2⟩
    · cases h; exact hst

theorem mem_extract_lt {n : Nat} {p : Part} (hp : Part.WF n p) {a b v : Nat}
    (h : v ∈ (p.lab.extract a b).toList) : v < n := by
  rw [← Array.mem_def, Array.mem_iff_getElem] at h
  obtain ⟨i, hi, hv⟩ := h
  rw [Array.getElem_extract] at hv
  have hlt : a + i < p.lab.size := by
    simp only [Array.size_extract] at hi
    omega
  rw [← hv, ← getElem!_pos p.lab (a + i) hlt]
  exact hp.labLt _ (by rw [hp.labSize] at hlt; exact hlt)

/-! ### Branch equations for the search

`dfsNode` and `dfsChildren` are written as one `match`/`if` cascade each, with `let`s naming the
intermediate states.  Rewriting inside those `let`s is painful, so each branch gets an equation
here, stated with the intermediates named by `orbRefresh` and `unwind`.  Proofs elsewhere only
ever use these, never the definitions. -/

/-- The orbit cache of `dfsChildren`, refreshed if new generators have turned up. -/
def orbRefresh (G : Graph) (path : Array Nat) (processed : Array Nat) (orb : Orbits) (st : St) :
    Orbits :=
  if orb.nGens == st.autos.size then orb
  else
    let gens := usableAutos st.autos path
    { nGens := st.autos.size, gens, mark := orbitClosure G.n gens processed }

/-- Absorb a backjump request aimed at this depth. -/
def unwind (path : Array Nat) (st : St) : St :=
  match st.abortTo with
  | some k => if k ≥ path.size then { st with abortTo := none } else st
  | none => st

theorem dfsNode_zero (G : Graph) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St) :
    dfsNode G 0 path invPath p st = st := by rw [dfsNode]

theorem dfsNode_abort {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {st : St} (h : st.abortTo.isSome = true) :
    dfsNode G (fuel + 1) path invPath p st = st := by
  rw [dfsNode, ite_eq_left h]

theorem dfsNode_pruned {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {st : St} (h : st.abortTo.isSome = false) (hp : pruneNode invPath st = none) :
    dfsNode G (fuel + 1) path invPath p st = st := by
  rw [dfsNode, ite_eq_right (by simp [h]), hp]

theorem dfsNode_leaf {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {st st' : St} (h : st.abortTo.isSome = false)
    (hp : pruneNode invPath st = some st') (hc : p.targetCell G.n = none) :
    dfsNode G (fuel + 1) path invPath p st
      = leafUpdate G path invPath p.lab { st' with nodes := st'.nodes + 1 } := by
  rw [dfsNode, ite_eq_right (by simp [h]), hp]
  simp only []
  rw [hc]

theorem dfsNode_branch {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {st st' : St} {c : Nat} (h : st.abortTo.isSome = false)
    (hp : pruneNode invPath st = some st') (hc : p.targetCell G.n = some c) :
    dfsNode G (fuel + 1) path invPath p st
      = dfsChildren G fuel path invPath p ((p.lab.extract c p.cen[c]!).toList) #[]
          { nGens := st'.autos.size, gens := usableAutos st'.autos path,
            mark := Array.replicate G.n false }
          { st' with nodes := st'.nodes + 1 } := by
  rw [dfsNode, ite_eq_right (by simp [h]), hp]
  simp only []
  rw [hc]

theorem dfsChildren_nil (G : Graph) (fuel : Nat) (path : Array Nat) (invPath : Array UInt64)
    (p : Part) (processed : Array Nat) (orb : Orbits) (st : St) :
    dfsChildren G fuel path invPath p [] processed orb st = st := by rw [dfsChildren]

theorem dfsChildren_abort {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {v : Nat} {vs : List Nat} {processed : Array Nat} {orb : Orbits} {st : St}
    (h : st.abortTo.isSome = true) :
    dfsChildren G fuel path invPath p (v :: vs) processed orb st = st := by
  rw [dfsChildren]
  simp only []
  rw [ite_eq_left h]

theorem dfsChildren_marked {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {v : Nat} {vs : List Nat} {processed : Array Nat} {orb : Orbits} {st : St}
    (h : st.abortTo.isSome = false) (hm : (orbRefresh G path processed orb st).mark[v]! = true) :
    dfsChildren G fuel path invPath p (v :: vs) processed orb st
      = dfsChildren G fuel path invPath p vs processed (orbRefresh G path processed orb st) st := by
  have hor : orbRefresh G path processed orb st
      = if orb.nGens == st.autos.size then orb
        else { nGens := st.autos.size, gens := usableAutos st.autos path,
               mark := orbitClosure G.n (usableAutos st.autos path) processed } := rfl
  rw [dfsChildren]
  simp only []
  rw [ite_eq_right (by simp [h]), ← hor, ite_eq_left hm]

theorem dfsChildren_step {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {v : Nat} {vs : List Nat} {processed : Array Nat} {orb : Orbits} {st : St}
    {p' p'' : Part} {s : Nat} {tr : UInt64}
    (h : st.abortTo.isSome = false) (hm : (orbRefresh G path processed orb st).mark[v]! = false)
    (hi : individualize p v = (p', s))
    (hr : refine G p' ((Array.replicate G.n false).set! s true) hashSeed = (p'', tr)) :
    dfsChildren G fuel path invPath p (v :: vs) processed orb st
      = (let st1 := unwind path
            (dfsNode G fuel (path.push v) (invPath.push (mix tr (p''.shapeHash G.n))) p'' st)
         if st1.abortTo.isSome then st1
         else
           dfsChildren G fuel path invPath p vs (processed.push v)
             { orbRefresh G path processed orb st with
               mark := closureLoop (orbRefresh G path processed orb st).gens (G.n + 1)
                 ((orbRefresh G path processed orb st).mark.set! v true) #[v] } st1) := by
  have hor : orbRefresh G path processed orb st
      = if orb.nGens == st.autos.size then orb
        else { nGens := st.autos.size, gens := usableAutos st.autos path,
               mark := orbitClosure G.n (usableAutos st.autos path) processed } := rfl
  rw [dfsChildren]
  simp only []
  rw [ite_eq_right (by simp [h]), ← hor, ite_eq_right (by simp [hm]), hi]
  simp only []
  rw [hr]
  rfl

theorem dfsChildren_step_stop {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {v : Nat} {vs : List Nat} {processed : Array Nat} {orb : Orbits} {st : St}
    {p' p'' : Part} {s : Nat} {tr : UInt64}
    (h : st.abortTo.isSome = false) (hm : (orbRefresh G path processed orb st).mark[v]! = false)
    (hi : individualize p v = (p', s))
    (hr : refine G p' ((Array.replicate G.n false).set! s true) hashSeed = (p'', tr))
    (hs : (unwind path (dfsNode G fuel (path.push v)
        (invPath.push (mix tr (p''.shapeHash G.n))) p'' st)).abortTo.isSome = true) :
    dfsChildren G fuel path invPath p (v :: vs) processed orb st
      = unwind path
          (dfsNode G fuel (path.push v) (invPath.push (mix tr (p''.shapeHash G.n))) p'' st) := by
  rw [dfsChildren_step h hm hi hr]
  simp only []
  rw [ite_eq_left hs]

theorem dfsChildren_step_go {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {v : Nat} {vs : List Nat} {processed : Array Nat} {orb : Orbits} {st : St}
    {p' p'' : Part} {s : Nat} {tr : UInt64}
    (h : st.abortTo.isSome = false) (hm : (orbRefresh G path processed orb st).mark[v]! = false)
    (hi : individualize p v = (p', s))
    (hr : refine G p' ((Array.replicate G.n false).set! s true) hashSeed = (p'', tr))
    (hs : (unwind path (dfsNode G fuel (path.push v)
        (invPath.push (mix tr (p''.shapeHash G.n))) p'' st)).abortTo.isSome = false) :
    dfsChildren G fuel path invPath p (v :: vs) processed orb st
      = dfsChildren G fuel path invPath p vs (processed.push v)
          { orbRefresh G path processed orb st with
            mark := closureLoop (orbRefresh G path processed orb st).gens (G.n + 1)
              ((orbRefresh G path processed orb st).mark.set! v true) #[v] }
          (unwind path
            (dfsNode G fuel (path.push v) (invPath.push (mix tr (p''.shapeHash G.n))) p'' st)) := by
  rw [dfsChildren_step h hm hi hr]
  simp only []
  rw [ite_eq_right (by simp [hs])]

/-- `unwind` only clears a backjump request; it never touches the recorded leaves. -/
theorem unwind_best (path : Array Nat) (st : St) : (unwind path st).best = st.best := by
  rw [unwind]
  split
  · split <;> rfl
  · rfl

theorem unwind_first (path : Array Nat) (st : St) : (unwind path st).first = st.first := by
  rw [unwind]
  split
  · split <;> rfl
  · rfl

theorem StOk.unwind {G : Graph} {st : St} (h : StOk G st) (path : Array Nat) :
    StOk G (Canon.unwind path st) :=
  ⟨fun l hb => h.1 l ((unwind_best path st) ▸ hb), fun l hf => h.2 l ((unwind_first path st) ▸ hf)⟩

/-- **Every leaf the search stores is honest.**  By functional induction over the two mutually
recursive halves of the search: the only place a leaf is created is `leafUpdate`, and there it is
built from the `lab` of the current partition, which the refinement keeps well-formed. -/
theorem dfsNode_ok (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      Part.WF n p → StOk (Graph.ofOracle n f) st →
        StOk (Graph.ofOracle n f) (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      Part.WF n p → StOk (Graph.ofOracle n f) st →
        StOk (Graph.ofOracle n f) (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      Part.WF n p → (∀ v ∈ verts, v < n) → StOk (Graph.ofOracle n f) st →
        StOk (Graph.ofOracle n f)
          (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => intro path invPath p st hp hst; rw [dfsNode]; exact hst
  case refine_2 =>
    intro path invPath p st fuel habort hp hst
    rw [dfsNode, ite_eq_left habort]; exact hst
  case refine_3 =>
    intro path invPath p st fuel habort hprune hp hst
    rw [dfsNode, ite_eq_right habort, hprune]; exact hst
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc hp hst
    have hst1 : StOk (Graph.ofOracle n f) st1 := pruneNode_ok hprune hst
    rw [dfsNode_leaf (by simpa using habort) hprune htc]
    exact leafUpdate_ok (leafOk_of_wf (ofOracle_n n f) hp path invPath) hst1
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 s htc verts orb ih hp hst
    have hst1 : StOk (Graph.ofOracle n f) st1 := pruneNode_ok hprune hst
    rw [dfsNode_branch (by simpa using habort) hprune htc]
    exact ih hp (fun v hv => mem_extract_lt hp hv) hst1
  case refine_6 =>
    intro fuel path invPath p processed orb st hp hverts hst
    rw [dfsChildren_nil]; exact hst
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort hp hverts hst
    rw [dfsChildren_abort habort]; exact hst
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hp hverts hst
    rw [dfsChildren_marked (by simpa using habort) hmark]
    exact ih hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw)) hst
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv st1 st2 habort2 ih1 hp hverts hst
    have hv : v < n := hverts v (by simp)
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (refine (Graph.ofOracle n f) p' inW hashSeed).1 := by rw [href]
      have h1 : p' = (individualize p v).1 := by rw [hind]
      rw [h2, h1]
      exact refine_wf (individualize_wf' hp hv) _ _
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href (by exact habort2)]
    exact (ih1 hwf'' hst).unwind path
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv st1 st2 habort2 orb2 ih1 _ih1' ih2 hp hverts hst
    have hv : v < n := hverts v (by simp)
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (refine (Graph.ofOracle n f) p' inW hashSeed).1 := by rw [href]
      have h1 : p' = (individualize p v).1 := by rw [hind]
      rw [h2, h1]
      exact refine_wf (individualize_wf' hp hv) _ _
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    exact ih2 hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw)) ((ih1 hwf'' hst).unwind path)

/-! ### `isPermArray` is complete

`isPermArray_spec` says an accept is honest.  Here is the converse: an honest array is accepted.
That is what turns `canonicalLabellingOfOracle`'s `if` into a no-op, so that the labelling really
is the search's output and not the identity fallback. -/

/-- Positions not written by any step of the `invLab` fold keep their old value. -/
theorem invLab_foldl_unchanged (n : Nat) (a : Array Nat) (l : List Nat) (b : Array Nat) (x : Nat)
    (h : ∀ i ∈ l, a[i]! ≠ x) :
    (l.foldl (fun b i => if a[i]! < n then b.set! a[i]! i else b) b)[x]! = b[x]! := by
  induction l generalizing b with
  | nil => rfl
  | cons c t ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    split
    · exact getElemD_setD_ne (Ne.symm (h c (by simp)))
    · rfl

theorem invLab_foldl_size (n : Nat) (a : Array Nat) (l : List Nat) (b : Array Nat) :
    (l.foldl (fun b i => if a[i]! < n then b.set! a[i]! i else b) b).size = b.size := by
  induction l generalizing b with
  | nil => rfl
  | cons c t ih => simp only [List.foldl_cons]; rw [ih]; split <;> simp

theorem invLab_foldl_get (n : Nat) (a : Array Nat) (l : List Nat) (hnd : l.Nodup)
    (hinj : ∀ i ∈ l, ∀ j ∈ l, a[i]! = a[j]! → i = j) (b : Array Nat) (hb : b.size = n)
    (i : Nat) (hi : i ∈ l) (hai : a[i]! < n) :
    (l.foldl (fun b i => if a[i]! < n then b.set! a[i]! i else b) b)[a[i]!]! = i := by
  induction l generalizing b with
  | nil => cases hi
  | cons c t ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hit
    · have hne : ∀ j ∈ t, a[j]! ≠ a[i]! := by
        intro j hj heq
        exact absurd (hinj j (List.mem_cons_of_mem _ hj) i (by simp) heq ▸ hj)
          (List.nodup_cons.1 hnd).1
      rw [invLab_foldl_unchanged n a t _ _ hne, ite_eq_left hai,
        getElemD_setD (show a[i]! < b.size by rw [hb]; exact hai) a[i]!, ite_eq_left rfl]
    · refine ih (List.nodup_cons.1 hnd).2
        (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) _
        ?_ hit
      split <;> simp [hb]

theorem invLab_get {n : Nat} {a : Array Nat}
    (hinj : ∀ i, i < n → ∀ j, j < n → a[i]! = a[j]! → i = j) {i : Nat} (hi : i < n)
    (hai : a[i]! < n) : (invLab n a)[a[i]!]! = i := by
  rw [invLab]
  exact invLab_foldl_get n a (List.range n) List.nodup_range
    (fun x hx y hy => hinj x (by simpa using hx) y (by simpa using hy)) _ (by simp) i
    (by simpa using hi) hai

/-- **`isPermArray` is complete.**  Anything of the right size whose entries are in range and
pairwise distinct is accepted. -/
theorem isPermArray_of {n : Nat} {a : Array Nat} (hsize : a.size = n)
    (hlt : ∀ i, i < n → a[i]! < n)
    (hinj : ∀ i, i < n → ∀ j, j < n → a[i]! = a[j]! → i = j) : isPermArray n a = true := by
  simp only [isPermArray, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨hsize, fun i hi => ?_⟩
  have hi' : i < n := by simpa using hi
  simp [hlt i hi', invLab_get hinj hi' (hlt i hi')]

/-! ### The search's output is an honest leaf -/

/-- The `Leaf` view of a `Result`, so that `LeafOk` can be reused for it. -/
def resultLeaf (r : Result) : Leaf :=
  { path := #[], invPath := #[], cert := r.cert, lab := r.lab }

/-- **The canonical labelling is a permutation and its certificate is the graph read at it.** -/
theorem canonical_ok (n : Nat) (f : Nat → Nat → Bool) :
    LeafOk (Graph.ofOracle n f) (resultLeaf (canonical (Graph.ofOracle n f))) := by
  have key : ∀ st : St, StOk (Graph.ofOracle n f) st →
      LeafOk (Graph.ofOracle n f) (resultLeaf (match st.best with
        | none => { lab := Array.range n,
                    cert := certOf (Graph.ofOracle n f) (Array.range n),
                    autos := #[], nodes := st.nodes }
        | some b => { lab := b.lab, cert := b.cert, autos := st.autos, nodes := st.nodes })) := by
    intro st hst
    cases hb : st.best with
    | none =>
      simp only [resultLeaf]
      refine ⟨by simp, fun i hi => ?_, fun i hi j hj h => ?_, rfl⟩
      · rw [getElem!_pos _ _ (by simpa using hi)]; simpa using hi
      · have h' : (Array.range n)[i]! = (Array.range n)[j]! := h
        rw [getElem!_pos _ _ (by simpa using hi), getElem!_pos _ _ (by simpa using hj)] at h'
        simpa using h'
    | some b =>
      have hbo := hst.1 b hb
      exact ⟨hbo.size, hbo.lt, hbo.inj, hbo.cert⟩
  exact key _ (dfsNode_ok n f _ _ _ _ _ (initialRefine_wf f) ⟨by simp, by simp⟩)

theorem canonical_cert (n : Nat) (f : Nat → Nat → Bool) :
    (canonical (Graph.ofOracle n f)).cert
      = certOf (Graph.ofOracle n f) (canonical (Graph.ofOracle n f)).lab :=
  (canonical_ok n f).cert

theorem canonical_isPerm (n : Nat) (f : Nat → Nat → Bool) :
    isPermArray n (canonical (Graph.ofOracle n f)).lab = true :=
  isPermArray_of (canonical_ok n f).size (canonical_ok n f).lt (canonical_ok n f).inj

/-- With the check now known to pass, the labelling *is* the search's output. -/
theorem canonicalLabellingOfOracle_eq (n : Nat) (f : Nat → Nat → Bool) :
    canonicalLabellingOfOracle n f = (canonical (Graph.ofOracle n f)).lab := by
  rw [canonicalLabellingOfOracle]
  simp only [canonical_isPerm n f, ite_eq_left]


end Canon
end IsoGraph
