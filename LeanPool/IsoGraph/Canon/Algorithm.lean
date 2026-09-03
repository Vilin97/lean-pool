/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-!
# Canonical labelling of finite graphs (a compact "mini-nauty")

This file is deliberately *programming* Lean rather than *proving* Lean: it implements an
individualisation–refinement (IR) canonical labelling algorithm in the style of McKay's `nauty`,
with no `Prop`-level content at all.  Correctness proofs live elsewhere; the only thing this file
promises syntactically is termination.

## The algorithm

Fix a graph `G` on the vertex set `{0, …, n-1}`.

* An **ordered partition** of the vertices is stored `nauty`-style: an array `lab` listing the
  vertices in partition order, its inverse `pos`, and for every *position* `i` the start `cst[i]`
  and end `cen[i]` of the cell containing position `i`.  Cells are contiguous blocks of `lab`.

* **Refinement** (`refine`) computes the coarsest equitable ordered partition refining a given
  one, by the usual Hopcroft-style worklist: pop a cell `S` (the *splitter*), and split every
  other cell `C` according to `|N(v) ∩ S|`, ordering the fragments by increasing count.  This is
  1-dimensional Weisfeiler–Leman; on a random graph it already produces a discrete partition.

* A discrete ordered partition *is* a labelling, so it yields a **certificate**: the adjacency
  matrix read off in that order, stored one `Nat` bitmask per row.  Certificates are totally
  ordered lexicographically.

* When refinement does not discretise, we **individualise**: pick the first non-singleton cell
  (an isomorphism-invariant choice), split off one of its vertices, re-refine, and recurse.  This
  produces a search tree whose leaves are labellings.

* The canonical labelling is the leaf that is largest for the order
  `(invariant path, certificate)`, lexicographically.  The **invariant path** records, for each
  node on the root-to-leaf path, a hash of the *trace* of the refinement that produced it (which
  cells split, into what sizes, at which counts) together with the shape of the resulting
  partition.  Everything hashed is a function of positions and multiplicities only — never of
  vertex names — so the invariant path is an isomorphism invariant.

Two prunings make this fast:

* **Invariant pruning.**  At a node of depth `d`, compare its length-`d` invariant path with that
  of the best leaf so far.  Smaller ⇒ every leaf below is smaller ⇒ prune.  Larger ⇒ every leaf
  below beats the incumbent ⇒ discard the incumbent.

* **Automorphism pruning.**  Two leaves with equal certificates differ by an automorphism `γ`,
  which we record.  At a node with individualisation path `p`, any recorded `γ` fixing `p`
  pointwise maps the subtree below `p ++ [v]` isomorphically onto the one below `p ++ [γ v]`, so
  only one vertex per orbit needs to be explored.

Note that hash collisions can only *weaken* pruning: an invariant path is used solely as the first
component of a total order on leaves, and any isomorphism-invariant function works there.
-/

namespace IsoGraph
namespace Canon

/-! ## Graphs -/

/-- A finite graph on the vertex set `{0, …, n-1}`, stored both as a dense adjacency matrix (for
`O(1)` adjacency queries) and as neighbour lists (for the refinement inner loop).

The algorithm below never inspects `adj`/`nbr` beyond index `n`, and assumes they agree and are
symmetric; `Graph.ofOracle` builds a well-formed value. -/
structure Graph where
  /-- Number of vertices. -/
  n : Nat
  /-- `adj[v]![w]!` is `true` iff `v` and `w` are adjacent. -/
  adj : Array (Array Bool)
  /-- `nbr[v]!` lists the neighbours of `v` in increasing order. -/
  nbr : Array (Array Nat)
  deriving Inhabited

/-- Build a `Graph` from an adjacency oracle on `{0, …, n-1}`.

Written with `Array.ofFn`/`Array.filter` rather than as an imperative fill: the arrays are the
same, but every entry is then definitionally the oracle, which is what makes the lemmas in
`IsoGraph/Canon/Equivariance.lean` about this function short.  `vs` is shared across the rows so the
`nbr` pass allocates only the neighbour lists themselves. -/
def Graph.ofOracle (n : Nat) (f : Nat → Nat → Bool) : Graph :=
  let vs := Array.range n
  { n := n
    adj := Array.ofFn (n := n) fun v => Array.ofFn (n := n) fun w => f v.1 w.1
    nbr := Array.ofFn (n := n) fun v => vs.filter (f v.1) }

/-- Number of edges (counting each unordered pair once); handy for sanity checks. -/
def Graph.edgeCount (G : Graph) : Nat := Id.run do
  let mut m := 0
  for v in [0:G.n] do
    m := m + G.nbr[v]!.size
  return m / 2

/-! ## Hashing

A 64-bit FNV-style mixer.  Only used to compress isomorphism-invariant integer sequences into a
comparable summary; collisions cost pruning power, never correctness. -/

/-- The FNV-1a offset basis, used as the seed of every invariant hash. -/
def hashSeed : UInt64 := 1469598103934665603

/-- Fold one number into a running hash. -/
@[inline] def mix (h : UInt64) (x : UInt64) : UInt64 :=
  (h ^^^ x) * 1099511628211

/-- Fold one `Nat` into a running hash. -/
@[inline] def mixN (h : UInt64) (x : Nat) : UInt64 :=
  mix h (UInt64.ofNat x)

/-! ## Ordered partitions -/

/-- An ordered partition of `{0, …, n-1}` into contiguous cells of `lab`.

* `lab[i]!` — the vertex at position `i`;
* `pos[v]!` — the position of vertex `v` (inverse of `lab`);
* `cst[i]!` — first position of the cell containing position `i`;
* `cen[i]!` — one past the last position of that cell.

A cell is therefore identified by its start position, and cell starts are exactly the `i` with
`cst[i]! = i`. -/
structure Part where
  /-- Position `↦` vertex. -/
  lab : Array Nat
  /-- Vertex `↦` position. -/
  pos : Array Nat
  /-- Position `↦` start of its cell. -/
  cst : Array Nat
  /-- Position `↦` end (exclusive) of its cell. -/
  cen : Array Nat
  deriving Inhabited

/-- The one-cell (unit) partition of `{0, …, n-1}`. -/
def Part.unit (n : Nat) : Part :=
  { lab := Array.range n
    pos := Array.range n
    cst := Array.replicate n 0
    cen := Array.replicate n n }

/-! Both readers of a partition below walk it cell by cell: from a cell start `i`, `cen[i]!` is
the start of the next cell, so the walk `i ↦ cen[i]!` visits every cell once and reaches `n`.
They are written as structural recursions on an explicit fuel rather than as `for` loops with a
`break`, because that is the form induction works on — see `IsoGraph/Canon/Equivariance.lean`, where
everything about them is proved.  `n` is always enough fuel: there are at most `n` cells. -/

/-- Fold the cell sizes from cell start `i` into the hash `h`. -/
def cenHashFrom (cen : Array Nat) (n : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, h => h
  | fuel + 1, i, h =>
    if i ≥ n then h else cenHashFrom cen n fuel cen[i]! (mixN h (cen[i]! - i))

/-- Start of the first non-singleton cell at or after cell start `i`, if any. -/
def cenTargetFrom (cen : Array Nat) (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i ≥ n then none
    else if cen[i]! - i > 1 then some i
    else cenTargetFrom cen n fuel cen[i]!

/-- Hash of the sequence of cell sizes.  Isomorphism-invariant. -/
def Part.shapeHash (p : Part) (n : Nat) : UInt64 := cenHashFrom p.cen n n 0 hashSeed

/-- Start position of the first non-singleton cell, if any.  This is the target cell for
individualisation; picking the *first* one is an isomorphism-invariant rule. -/
def Part.targetCell (p : Part) (n : Nat) : Option Nat := cenTargetFrom p.cen n n 0

/-! ## Refinement -/

/-- Scratch space reused across refinement steps.

Allocating these three arrays afresh in every step would make a step cost `Ω(n)` even when the
splitter is tiny, which on sparse graphs dominates everything else.  Instead they are threaded
through the worklist loop and each step *restores* them, so the invariant

* `cnt` is all `0`,
* `hit` is all `false`,
* `bc` is all `0`

holds on entry to and on exit from every step, and clearing costs only what was dirtied. -/
structure Scratch where
  /-- Vertex `↦` number of neighbours in the current splitter cell. -/
  cnt : Array Nat
  /-- Cell start `↦` has this cell already been collected? -/
  hit : Array Bool
  /-- Neighbour count `↦` bucket size, then bucket offset, during the counting sort. -/
  bc : Array Nat
  deriving Inhabited

/-- Cleared scratch space for a graph on `n` vertices.  Counts never exceed `n`, so `bc` needs
`n + 1` entries. -/
def Scratch.empty (n : Nat) : Scratch :=
  { cnt := Array.replicate n 0, hit := Array.replicate n false, bc := Array.replicate (n + 1) 0 }

/-- Bump `cnt[v]` for every `v` in `nbrs[j:]`, pushing each newly-touched vertex onto `touched`.

Like `cenHashFrom` above this is a structural recursion on an explicit fuel (only ever
`nbrs.size - j`) rather than a `for` loop, so that the equivariance proof can read off the
resulting count at each index; the `j < nbrs.size` that a `for` loop hides is exactly what the
proof needs. -/
def bumpFrom (nbrs : Array Nat) : Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cnt, touched => (cnt, touched)
  | fuel + 1, j, cnt, touched =>
    if j ≥ nbrs.size then (cnt, touched)
    else
      let v := nbrs[j]!
      let c := cnt[v]!
      bumpFrom nbrs fuel (j + 1) (cnt.set! v (c + 1)) (if c == 0 then touched.push v else touched)

/-- Accumulate into `cnt` the number of neighbours each vertex has among `lab[k:e]`, recording in
`touched` the vertices whose count became nonzero.  This is phase (1) of `refineStep`, and is the
hot loop of the whole algorithm: it costs the splitter cell's degree sum. -/
def countFrom (G : Graph) (lab : Array Nat) (e : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cnt, touched => (cnt, touched)
  | fuel + 1, k, cnt, touched =>
    if k ≥ e then (cnt, touched)
    else
      let nbrs := G.nbr[lab[k]!]!
      match bumpFrom nbrs nbrs.size 0 cnt touched with
      | (cnt, touched) => countFrom G lab e fuel (k + 1) cnt touched

/-- Sort an array of naturals increasingly.

`Array.qsort` would do the same job, but it has no verified specification in this toolchain, and
the sorted order of the cells and of the counts *is* part of what makes the trace canonical.  So
this goes through `List.mergeSort`, which does.  The round trip through `List` costs nothing
measurable on the benchmarks: both call sites sort at most one entry per cell of the partition,
against a refinement step that already costs the splitter's degree sum. -/
def sortNats (a : Array Nat) : Array Nat := (a.toList.mergeSort (fun x y => x ≤ y)).toArray

/-- Collect the distinct cell starts of the vertices in `touched[j:]`, using `hit` to deduplicate.
Phase (2) of `refineStep`, as a structural recursion on fuel; `fuel` is only ever
`touched.size - j`. -/
def collectFrom (pos cst touched : Array Nat) :
    Nat → Nat → Array Bool → Array Nat → Array Bool × Array Nat
  | 0, _, hit, cells => (hit, cells)
  | fuel + 1, j, hit, cells =>
    if j ≥ touched.size then (hit, cells)
    else
      let c := cst[pos[touched[j]!]!]!
      if hit[c]! then collectFrom pos cst touched fuel (j + 1) hit cells
      else collectFrom pos cst touched fuel (j + 1) (hit.set! c true) (cells.push c)

/-- Bucket the cell `lab[k:ec]` by neighbour count: `bc[t]` counts the members whose count is `t`,
and `ks` lists the counts that occur, in first-occurrence order.  Phase (3a) of `refineStep`, and
another fuel recursion in place of a `for` loop; `fuel` is only ever `ec - k`. -/
def bucketFrom (lab cnt : Array Nat) (ec : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, bc, ks => (bc, ks)
  | fuel + 1, k, bc, ks =>
    if k ≥ ec then (bc, ks)
    else
      let t := cnt[lab[k]!]!
      let b := bc[t]!
      bucketFrom lab cnt ec fuel (k + 1) (bc.set! t (b + 1)) (if b == 0 then ks.push t else ks)

/-- Turn the bucket sizes into the fragment sizes `sizes[j]` and the bucket *offsets* `bc[ks[j]]`
(relative to the start of the cell).  `acc` is the running offset.  Phase (3b). -/
def offsetFrom (ks : Array Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Array Nat × Array Nat
  | 0, _, sizes, bc, _ => (sizes, bc)
  | fuel + 1, j, sizes, bc, acc =>
    if j ≥ ks.size then (sizes, bc)
    else
      let t := ks[j]!
      let b := bc[t]!
      offsetFrom ks fuel (j + 1) (sizes.set! j b) (bc.set! t acc) (acc + b)

/-- Scatter the cell's vertices into `block` in count order, each bucket keeping the order it had
in the cell.  Phase (3c). -/
def scatterFrom (lab cnt : Array Nat) (ec : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, block, bc => (block, bc)
  | fuel + 1, k, block, bc =>
    if k ≥ ec then (block, bc)
    else
      let v := lab[k]!
      let t := cnt[v]!
      let o := bc[t]!
      scatterFrom lab cnt ec fuel (k + 1) (block.set! o v) (bc.set! t (o + 1))

/-- Zero the buckets the cell used, leaving `bc` clear for the next cell.  Phase (3d). -/
def clearBcFrom (ks : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, bc => bc
  | fuel + 1, j, bc =>
    if j ≥ ks.size then bc else clearBcFrom ks fuel (j + 1) (bc.set! ks[j]! 0)

/-- Copy the sorted block back into `lab[c:]`, keeping `pos` its inverse.  Phase (3e). -/
def writeFrom (block : Array Nat) (c : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, lab, pos => (lab, pos)
  | fuel + 1, k, lab, pos =>
    if k ≥ block.size then (lab, pos)
    else
      let v := block[k]!
      writeFrom block c fuel (k + 1) (lab.set! (c + k) v) (pos.set! v (c + k))

/-- Write the boundaries of the fragment `[st, en)` into `cst`/`cen`.  Phase (4a). -/
def fillBoundsFrom (st en : Nat) : Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, cst, cen => (cst, cen)
  | fuel + 1, i, cst, cen =>
    if i ≥ en then (cst, cen)
    else fillBoundsFrom st en fuel (i + 1) (cst.set! i st) (cen.set! i en)

/-- Install the boundaries of every fragment of a split cell, collecting the fragment starts and
hashing each fragment's size and count into the trace.  Phase (4). -/
def boundsFrom (ks sizes : Array Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat → Nat → UInt64 →
      Array Nat × Array Nat × Array Nat × UInt64
  | 0, _, cst, cen, starts, _, tr => (cst, cen, starts, tr)
  | fuel + 1, j, cst, cen, starts, st, tr =>
    if j ≥ ks.size then (cst, cen, starts, tr)
    else
      let sz := sizes[j]!
      let en := st + sz
      match fillBoundsFrom st en sz st cst cen with
      | (cst, cen) =>
        boundsFrom ks sizes fuel (j + 1) cst cen (starts.push st) en (mixN (mixN tr sz) ks[j]!)

/-- Queue every fragment of a split cell.  Phase (5), the case where the parent was queued. -/
def markAllFrom (starts : Array Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, inW => inW
  | fuel + 1, j, inW =>
    if j ≥ starts.size then inW else markAllFrom starts fuel (j + 1) (inW.set! starts[j]! true)

/-- Index of a largest fragment, scanning left to right. -/
def maxIdxFrom (sizes : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, bi => bi
  | fuel + 1, k, bi =>
    if k ≥ sizes.size then bi
    else maxIdxFrom sizes fuel (k + 1) (if sizes[k]! > sizes[bi]! then k else bi)

/-- Queue every fragment but `starts[bi]`.  Phase (5), Hopcroft's case: skipping one largest
fragment is what keeps refinement near-linear. -/
def markExceptFrom (starts : Array Nat) (bi : Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, inW => inW
  | fuel + 1, k, inW =>
    if k ≥ starts.size then inW
    else markExceptFrom starts bi fuel (k + 1) (if k != bi then inW.set! starts[k]! true else inW)

/-- Zero the counts of the touched vertices.  Phase (6). -/
def clearCntFrom (touched : Array Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, cnt => cnt
  | fuel + 1, j, cnt =>
    if j ≥ touched.size then cnt else clearCntFrom touched fuel (j + 1) (cnt.set! touched[j]! 0)

/-- Unmark the cells that were collected.  Phase (6). -/
def clearHitFrom (cells : Array Nat) : Nat → Nat → Array Bool → Array Bool
  | 0, _, hit => hit
  | fuel + 1, j, hit =>
    if j ≥ cells.size then hit else clearHitFrom cells fuel (j + 1) (hit.set! cells[j]! false)

/-- The state `refineStep`'s cell loop carries: the partition being rewritten, the worklist, the
trace, and the bucket scratch.  (`cnt` is read-only during the loop, so it stays outside.) -/
structure SplitState where
  /-- Position to vertex. -/
  lab : Array Nat
  /-- Vertex to position. -/
  pos : Array Nat
  /-- Position to the start of its cell. -/
  cst : Array Nat
  /-- Position to the end of its cell. -/
  cen : Array Nat
  /-- Which cells are queued as splitters. -/
  inW : Array Bool
  /-- The trace hash so far. -/
  tr : UInt64
  /-- The bucket scratch, all-zero between cells. -/
  bc : Array Nat

/-- Split the cell starting at position `c` by neighbour count, phases (3) to (5).  Written as a
chain of `match`es rather than a `do` block for the same reason as the loops above. -/
def splitCell (cnt : Array Nat) (c : Nat) (st : SplitState) : SplitState :=
  -- Read the cell's extent *before* splitting it; splits stay inside `[c, ec)`, so the cells
  -- collected by phase (2) keep their starts.
  let ec := st.cen[c]!
  if ec - c == 1 then
    -- A singleton cell cannot split, but its count is still invariant information.
    { st with tr := mixN (mixN st.tr c) cnt[st.lab[c]!]! }
  else
    -- (3) counting sort of the cell by neighbour count.  Only the counts that actually occur in
    -- the cell are visited, so the cost is `O(|cell|)` rather than `O(|splitter|)`; `bc` doubles
    -- as the bucket-size table and then as the offset table, and is left all-zero again.
    match bucketFrom st.lab cnt ec (ec - c) c st.bc #[] with
    | (bc, ks) =>
      if ks.size == 1 then
        -- No split; record the common count and reset the scratch counter.
        { st with tr := mixN (mixN st.tr c) ks[0]!, bc := bc.set! ks[0]! 0 }
      else
        let ks := sortNats ks
        match offsetFrom ks ks.size 0 (Array.replicate ks.size 0) bc 0 with
        | (sizes, bc) =>
          match scatterFrom st.lab cnt ec (ec - c) c (Array.replicate (ec - c) 0) bc with
          | (block, bc) =>
            match writeFrom block c block.size 0 st.lab st.pos with
            | (lab, pos) =>
              -- (4) install the fragment boundaries and collect them.
              match boundsFrom ks sizes ks.size 0 st.cst st.cen #[] c (mixN st.tr c) with
              | (cst, cen, starts, tr) =>
                -- (5) worklist maintenance (Hopcroft).
                let inW :=
                  if st.inW[c]! then markAllFrom starts starts.size 0 st.inW
                  else markExceptFrom starts (maxIdxFrom sizes sizes.size 0 0) starts.size 0 st.inW
                { lab, pos, cst, cen, inW, tr, bc := clearBcFrom ks ks.size 0 bc }

/-- Split every cell in `cells[j:]`, left to right. -/
def splitCellsFrom (cnt cells : Array Nat) : Nat → Nat → SplitState → SplitState
  | 0, _, st => st
  | fuel + 1, j, st =>
    if j ≥ cells.size then st
    else splitCellsFrom cnt cells fuel (j + 1) (splitCell cnt cells[j]! st)

/-- Perform one refinement step: use the cell starting at position `s` as a splitter, splitting
every cell that meets its neighbourhood.

Returns the new partition, the updated worklist (`inW`, indexed by cell start position), the
updated trace hash, and the scratch space, restored to its cleared state.  Cells created by a
split are pushed onto the worklist following Hopcroft's rule: all fragments if the parent was
queued, otherwise all but a largest fragment. -/
def refineStep (G : Graph) (p : Part) (inW : Array Bool) (s : Nat) (tr : UInt64) (sc : Scratch) :
    Part × Array Bool × UInt64 × Scratch :=
  let e := p.cen[s]!
  let tr := mixN tr s
  -- (1) count neighbours inside the splitter cell `lab[s:e]`.
  match countFrom G p.lab e (e - s) s sc.cnt #[] with
  | (cnt, touched) =>
    if touched.isEmpty then (p, inW, tr, sc)
    else
      -- (2) collect the cells met by the splitter and process them left to right, so that the
      -- order in which they are processed depends only on positions.  Only *met* cells are
      -- visited, which is what keeps a refinement step proportional to the splitter's degree sum
      -- rather than to the number of cells.
      match collectFrom p.pos p.cst touched touched.size 0 sc.hit #[] with
      | (hit, collected) =>
        let cells := sortNats collected
        match splitCellsFrom cnt cells cells.size 0
            { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW, tr, bc := sc.bc } with
        | st =>
          -- (6) restore the scratch space, touching only the entries that were dirtied.  `bc` is
          -- already back to all-zero: every bucket counter is reset as soon as its cell is done.
          ({ lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen }, st.inW, st.tr,
            { cnt := clearCntFrom touched touched.size 0 cnt,
              hit := clearHitFrom cells cells.size 0 hit,
              bc := st.bc })

/-- Index of the first `true` entry of `a`. -/
def firstSet (a : Array Bool) : Option Nat := Id.run do
  for j in [0:a.size] do
    if a[j]! then return some j
  return none

/-- The refinement worklist loop.  `fuel` bounds the number of splitter pops.

The guard `s < G.n && p.cst[s]! == s` is never false in a real run — only cell starts are ever
queued, and a cell start stays one when its cell is split — but checking it costs one array read
per pop and saves `Equivariance.refineLoop_equiv` from having to carry the worklist invariant.
Popping a position that is not a cell start simply drops it. -/
def refineLoop (G : Graph) : Nat → Part → Array Bool → UInt64 → Scratch → Part × UInt64
  | 0, p, _, tr, _ => (p, tr)
  | fuel + 1, p, inW, tr, sc =>
    match firstSet inW with
    | none => (p, tr)
    | some s =>
      if s < G.n && p.cst[s]! == s then
        let (p, inW, tr, sc) := refineStep G p (inW.set! s false) s tr sc
        refineLoop G fuel p inW tr sc
      else refineLoop G fuel p (inW.set! s false) tr sc

/-- Refine `p` to the coarsest equitable partition refining it, using the cells whose start
positions are flagged in `inW` as initial splitters.  Returns the refined partition together with
the trace hash of the refinement.

The fuel `n² + n + 1` is a genuine bound: a cell start enters the worklist once initially and once
per fragment of each split, there are at most `n - 1` splits, and each split creates at most `n`
fragments. -/
def refine (G : Graph) (p : Part) (inW : Array Bool) (tr : UInt64) : Part × UInt64 :=
  refineLoop G (G.n * G.n + G.n + 1) p inW tr (Scratch.empty G.n)

/-- Refine from the unit partition: equivalently, the coarsest equitable partition of `G`. -/
def initialRefine (G : Graph) : Part × UInt64 :=
  let p := Part.unit G.n
  let inW := if G.n == 0 then #[] else (Array.replicate G.n false).set! 0 true
  refine G p inW hashSeed

/-- Write `c + 1` into `cst[j]` for every `j ∈ [j₀, ec)`, where `j₀` is the second argument.  A
structural recursion rather than a `for` loop so that `Equivariance.setCstFrom_getElemD` can read
off each entry; `fuel` is only ever `ec - j₀`, so the work is the same. -/
def setCstFrom (c ec : Nat) : Nat → Nat → Array Nat → Array Nat
  | 0, _, cst => cst
  | fuel + 1, j, cst =>
    if j ≥ ec then cst else setCstFrom c ec fuel (j + 1) (cst.set! j (c + 1))

/-- Split the vertex `v` off from its cell, placing it first.  Returns the new partition and the
position of the new singleton cell `{v}` (which is the only splitter needed to re-refine, since
the input partition is assumed equitable). -/
def individualize (p : Part) (v : Nat) : Part × Nat :=
  let i := p.pos[v]!
  let c := p.cst[i]!
  let ec := p.cen[i]!
  let u := p.lab[c]!
  let lab := (p.lab.set! c v).set! i u
  let pos := (p.pos.set! v c).set! u i
  let cst := setCstFrom c ec (ec - (c + 1)) (c + 1) p.cst
  let cen := p.cen.set! c (c + 1)
  ({ lab, pos, cst, cen }, c)

/-! ## Certificates -/

/-- Number of 64-bit words used for one row of a certificate. -/
def rowWords (n : Nat) : Nat := (n + 63) / 64

/-- An `n × n` bit matrix packed into 64-bit words: row `i` occupies words
`[i * rowWords n, (i+1) * rowWords n)`, and column `j` of a row is bit `63 - j % 64` of word
`j / 64`.  Unused trailing bits are zero.

The matrix is given as a curried function so that a caller can do its per-row work — for
`certOf` below, one array index — in the outer lambda, where this loop applies it once per row
rather than once per bit.

Like the partition walks above, the two loops are structural recursions on fuel rather than
`for` loops, so that induction applies to them: `fuel` counts the entries still to do and `j`
(resp. `i`) the position reached, and `j + fuel = n` is the invariant that gives `j < n` inside
the body — which is exactly what a proof about the loop needs and what a `for` loop hides. -/
def certRow (n : Nat) (b : Nat → Bool) :
    Nat → Nat → UInt64 → Nat → Array UInt64 → Array UInt64
  | 0, _, acc, k, out =>
    if n % 64 != 0 then out.set! k (acc <<< UInt64.ofNat (64 - n % 64)) else out
  | fuel + 1, j, acc, k, out =>
    let acc := acc <<< 1 ||| (if b j then 1 else 0)
    if (j + 1) % 64 == 0 then certRow n b fuel (j + 1) 0 (k + 1) (out.set! k acc)
    else certRow n b fuel (j + 1) acc k out

/-- Pack rows `i, i+1, …` of the matrix, `fuel` of them, into `out`. -/
def certRowsFrom (n : Nat) (bit : Nat → Nat → Bool) (w : Nat) :
    Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, out => out
  | fuel + 1, i, out => certRowsFrom n bit w fuel (i + 1) (certRow n (bit i) n 0 0 (i * w) out)

@[inherit_doc certRow]
def certBits (n : Nat) (bit : Nat → Nat → Bool) : Array UInt64 :=
  certRowsFrom n bit (rowWords n) n 0 (Array.replicate (n * rowWords n) 0)

/-- The adjacency matrix of `G` read off in the order `lab`, packed by `certBits`.

Packing bits most-significant-first means that comparing the word arrays lexicographically, as
unsigned integers, compares the bit strings lexicographically.  Two labellings give the same
certificate exactly when they differ by an automorphism. -/
def certOf (G : Graph) (lab : Array Nat) : Array UInt64 :=
  certBits G.n fun i => let row := G.adj[lab[i]!]!; fun j => row[lab[j]!]!

/-- Lexicographic comparison of `a` and `b` from index `i` on, with `fuel` bounding the number of
positions still to look at.  Written as a structural recursion rather than a `for` loop so that
the order lemmas in `IsoGraph.Canon.Search` can be proved by induction on `fuel`. -/
def lexCmpFrom (a b : Array UInt64) : Nat → Nat → Ordering
  | 0, _ => compare a.size b.size
  | fuel + 1, i =>
    if i < min a.size b.size then
      match compare a[i]! b[i]! with
      | .eq => lexCmpFrom a b fuel (i + 1)
      | c => c
    else compare a.size b.size

/-- Lexicographic comparison of `UInt64` arrays (shorter is smaller on a common prefix). -/
def lexCmpU64 (a b : Array UInt64) : Ordering := lexCmpFrom a b (min a.size b.size) 0

/-! ## Automorphisms -/

/-- Given two labellings `σ τ : position → vertex` with equal certificates, the permutation
`γ = τ ∘ σ⁻¹`, which is an automorphism of the graph.

Written as a `foldl` over `List.range n` rather than as a `for` loop so that
`IsoGraph.Canon.Autos.autoOf_get` can read off each entry; the work is the same. -/
def autoOf (n : Nat) (σ τ : Array Nat) : Array Nat :=
  (List.range n).foldl (init := Array.replicate n 0) fun g i => g.set! σ[i]! τ[i]!

/-- Whether a permutation moves some point. -/
def moves (g : Array Nat) : Bool := Id.run do
  for i in [0:g.size] do
    if g[i]! != i then return true
  return false

/-- One step of orbit closure: mark the images of `v` under all generators.  A `foldl` rather
than a `for` loop so that `IsoGraph.Canon.Orbits` can induct on the generator list. -/
def closureStep (gens : Array (Array Nat)) (mark : Array Bool) (stack : Array Nat)
    (v : Nat) : Array Bool × Array Nat :=
  gens.foldl (init := (mark, stack)) fun ms g =>
    let w := g[v]!
    if !ms.1[w]! then (ms.1.set! w true, ms.2.push w) else ms

/-- Close `mark` under the generators, using `stack` as the frontier.  `fuel` bounds the number of
pops, which is at most the number of marked points. -/
def closureLoop (gens : Array (Array Nat)) : Nat → Array Bool → Array Nat → Array Bool
  | 0, mark, _ => mark
  | fuel + 1, mark, stack =>
    if stack.isEmpty then mark
    else
      let v := stack[stack.size - 1]!
      let (mark, stack) := closureStep gens mark stack.pop v
      closureLoop gens fuel mark stack

/-- The union of the `gens`-orbits of the vertices in `seed`, as a membership array of size `n`. -/
def orbitClosure (n : Nat) (gens : Array (Array Nat)) (seed : Array Nat) : Array Bool :=
  closureLoop gens (n + 1) (seed.foldl (init := Array.replicate n false)
    fun mark v => mark.set! v true) seed
/-! ## The search -/

/-- Scan for the first disagreement at or after `i`, stopping at `m`.  A structural recursion on
fuel rather than a `for` loop with a `break`, for the same reason as the partition walks above:
`IsoGraph.Canon.Jump` needs to induct on it. -/
def commonPrefixFrom (a b : Array Nat) (m : Nat) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if i ≥ m then m
    else if a[i]! == b[i]! then commonPrefixFrom a b m fuel (i + 1)
    else i

/-- Length of the longest common prefix of two paths. -/
def commonPrefix (a b : Array Nat) : Nat :=
  let m := min a.size b.size
  commonPrefixFrom a b m m 0

/-- A leaf of the search tree: a discrete ordered partition together with the data used to compare
it against other leaves. -/
structure Leaf where
  /-- The vertices individualised to reach this leaf. -/
  path : Array Nat
  /-- Node invariants along the root-to-leaf path. -/
  invPath : Array UInt64
  /-- The certificate of `lab`. -/
  cert : Array UInt64
  /-- The labelling itself: position `↦` vertex. -/
  lab : Array Nat
  deriving Inhabited

/-- Mutable state threaded through the depth-first search. -/
structure St where
  /-- The best leaf seen so far, for the order `(invPath, cert)`. -/
  best : Option Leaf
  /-- The very first leaf reached, kept only to detect automorphisms. -/
  first : Option Leaf
  /-- Automorphisms discovered so far, as image arrays `γ[v]!`. -/
  autos : Array (Array Nat)
  /-- Number of search-tree nodes visited. -/
  nodes : Nat
  /-- When `some k`: abandon the search below depth `k`.  See `leafUpdate`. -/
  abortTo : Option Nat
  deriving Inhabited

/-- Cap on the number of stored automorphism generators.  Dropping generators only weakens orbit
pruning, so this is a pure performance guard. -/
def maxGens : Nat := 256

/-- Record a newly found automorphism, ignoring the identity and duplicates. -/
def St.addAuto (st : St) (g : Array Nat) : St :=
  if !moves g then st
  else if st.autos.size ≥ maxGens then st
  else if st.autos.any (fun h => h == g) then st
  else { st with autos := st.autos.push g }

/-- Invariant pruning at a node.  Returns `none` if the whole subtree is dominated by the current
best leaf, and otherwise the state to continue with (with the incumbent discarded if the subtree
is guaranteed to beat it). -/
def pruneNode (invPath : Array UInt64) (st : St) : Option St :=
  match st.best with
  | none => some st
  | some b =>
    match lexCmpU64 invPath (b.invPath.extract 0 invPath.size) with
    | .lt => none
    | .gt => some { st with best := none }
    | .eq => some st

/-- Process a leaf: update the incumbent, harvest any automorphism, and decide how far to
backjump.

If the new leaf `ν` has the same certificate as a previously completed leaf `ζ`, then
`γ = ζ ∘ ν⁻¹` is an automorphism.  Writing `k` for the depth of the greatest common ancestor of
the two leaves, `γ` fixes the first `k` individualised vertices and maps `ν`'s branch at depth `k`
onto `ζ`'s.  Since depth-first search had already *finished* `ζ`'s branch before entering `ν`'s,
every leaf still unexplored below `ν`'s branch is a `γ`-image of one already seen, and carries the
same certificate.  So the whole remainder of that branch can be abandoned: we request a backjump
to depth `k`. -/
def leafUpdate (G : Graph) (path : Array Nat) (invPath : Array UInt64) (lab : Array Nat)
    (st : St) : St := Id.run do
  let cert := certOf G lab
  let leaf : Leaf := { path, invPath, cert, lab }
  let mut st := st
  let mut jump : Option Nat := none
  match st.first with
  | none => st := { st with first := some leaf }
  | some f =>
    if lexCmpU64 cert f.cert == .eq then
      st := st.addAuto (autoOf G.n lab f.lab)
      jump := some (commonPrefix path f.path)
  match st.best with
  | none => st := { st with best := some leaf }
  | some b =>
    match lexCmpU64 invPath b.invPath with
    | .gt => st := { st with best := some leaf }
    | .lt => pure ()
    | .eq =>
      match lexCmpU64 cert b.cert with
      | .gt => st := { st with best := some leaf }
      | .lt => pure ()
      | .eq =>
        st := st.addAuto (autoOf G.n lab b.lab)
        let k := commonPrefix path b.path
        jump := some (match jump with | none => k | some j => min j k)
  return { st with abortTo := jump }

/-- The automorphisms found so far that fix every vertex of `path`.  Only these may be used to
prune the children of the node reached by `path`. -/
def usableAutos (autos : Array (Array Nat)) (path : Array Nat) : Array (Array Nat) :=
  if autos.isEmpty then autos else autos.filter fun g => path.all fun x => g[x]! == x

/-- Cached orbit information for the children of one search-tree node: the orbit of the already
processed children, under those automorphisms that fix the node's individualisation path. -/
structure Orbits where
  /-- Size of `St.autos` when this was computed; used to detect staleness. -/
  nGens : Nat
  /-- The automorphisms fixing the node's path pointwise. -/
  gens : Array (Array Nat)
  /-- Membership array for the orbit of the processed children. -/
  mark : Array Bool
  deriving Inhabited

section SearchRecursion

mutual

/-- Visit one node of the search tree.  `p` is the (already refined) ordered partition, `path`
the vertices individualised to reach it, and `invPath` the node invariants along that path. -/
def dfsNode (G : Graph) (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part)
    (st : St) : St :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
    if st.abortTo.isSome then st else
    match pruneNode invPath st with
    | none => st
    | some st =>
      let st := { st with nodes := st.nodes + 1 }
      match p.targetCell G.n with
      | none => leafUpdate G path invPath p.lab st
      | some c =>
        let verts := (p.lab.extract c (p.cen[c]!)).toList
        let orb : Orbits :=
          { nGens := st.autos.size, gens := usableAutos st.autos path,
            mark := Array.replicate G.n false }
        dfsChildren G fuel path invPath p verts #[] orb st
  termination_by (fuel, 0)

/-- Visit the remaining children `verts` of a node, skipping those in the orbit of an already
visited child, and honouring any backjump request coming back from below. -/
def dfsChildren (G : Graph) (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part)
    (verts : List Nat) (processed : Array Nat) (orb : Orbits) (st : St) : St :=
  match verts with
  | [] => st
  | v :: vs =>
    if st.abortTo.isSome then st else
    -- Refresh the orbit cache if new automorphisms have turned up since it was built.
    let orb : Orbits :=
      if orb.nGens == st.autos.size then orb
      else
        let gens := usableAutos st.autos path
        { nGens := st.autos.size, gens, mark := orbitClosure G.n gens processed }
    if orb.mark[v]! then
      dfsChildren G fuel path invPath p vs processed orb st
    else
      let (p', s) := individualize p v
      let inW := (Array.replicate G.n false).set! s true
      let (p'', tr) := refine G p' inW hashSeed
      let childInv := invPath.push (mix tr (p''.shapeHash G.n))
      let st := dfsNode G fuel (path.push v) childInv p'' st
      -- A backjump to depth `path.size` stops here; a shallower one keeps unwinding.
      let st : St :=
        match st.abortTo with
        | some k => if k ≥ path.size then { st with abortTo := none } else st
        | none => st
      if st.abortTo.isSome then st
      else
        let orb : Orbits :=
          { orb with mark := closureLoop orb.gens (G.n + 1) (orb.mark.set! v true) #[v] }
        dfsChildren G fuel path invPath p vs (processed.push v) orb st
  termination_by (fuel, verts.length + 1)

end

/-! ## Entry points -/

/-- The result of canonicalisation. -/
structure Result where
  /-- The canonical labelling: `lab[i]!` is the vertex placed at canonical position `i`. -/
  lab : Array Nat
  /-- The canonical form: `certOf G lab`, one row bitmask per canonical position. -/
  cert : Array UInt64
  /-- Generators of (a subgroup of) the automorphism group found along the way. -/
  autos : Array (Array Nat)
  /-- Number of search-tree nodes visited, for diagnostics. -/
  nodes : Nat
  deriving Inhabited

/-- Compute a canonical labelling of `G`.

`Result.lab` is a permutation of `{0, …, n-1}` such that `Result.cert` depends only on the
isomorphism class of `G`. -/
def canonical (G : Graph) : Result :=
  let (p, tr) := initialRefine G
  let inv0 : Array UInt64 := #[mix tr (p.shapeHash G.n)]
  let st := dfsNode G (G.n + 1) #[] inv0 p
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }
  match st.best with
  | none =>
    { lab := Array.range G.n, cert := certOf G (Array.range G.n), autos := #[], nodes := st.nodes }
  | some b => { lab := b.lab, cert := b.cert, autos := st.autos, nodes := st.nodes }

/-- The canonical form of `G`: an isomorphism invariant that is complete (equal iff isomorphic,
for graphs on the same number of vertices). -/
def canonicalForm (G : Graph) : Array UInt64 :=
  (canonical G).cert

/-- Positional inverse of `a`: if `a` is a permutation of `{0, …, n-1}` then this is the array
with `invLab n a` at position `a[i]!` equal to `i`.  Used only to *check* that, so nothing is
claimed about it when `a` is not a permutation. -/
def invLab (n : Nat) (a : Array Nat) : Array Nat :=
  (List.range n).foldl (init := Array.replicate n 0) fun b i =>
    if a[i]! < n then b.set! a[i]! i else b

/-- Is `a` a permutation of `{0, …, n-1}`?  `O(n)`: build the positional inverse and check that
it really inverts, which gives injectivity for free (if `a[v]! = a[w]!` then
`v = b[a[v]!]! = b[a[w]!]! = w`). -/
def isPermArray (n : Nat) (a : Array Nat) : Bool :=
  a.size == n &&
    (let b := invLab n a
     (List.range n).all fun i => a[i]! < n && b[a[i]!]! == i)

/-- Canonical labelling from an adjacency oracle.

The search's output is checked to be a permutation of `{0, …, n-1}` before being returned, and
the identity is substituted if it is not.  The check costs `O(n)` against an `Ω(n²)` search, and
makes the returned array a permutation whatever the search does (`Spec.labellingIsPerm`). -/
def canonicalLabellingOfOracle (n : Nat) (f : Nat → Nat → Bool) : Array Nat :=
  let a := (canonical (Graph.ofOracle n f)).lab
  if isPermArray n a then a else Array.range n

end SearchRecursion
end Canon
end IsoGraph
