/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankOne
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionGraph
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator

/-!
# Rank-determining sets

A set `A` of vertices is *rank-determining* when the rank of every divisor can
be read off using only effective divisors supported on `A`:

```
rank G D ≥ r  ↔  ∀ E effective, deg E = r, supp E ⊆ A → winnable G (D - E)
```

The left-to-right implication is trivial and holds for every `A`
(`winnable_sub_of_rank_ge`); the content is the converse, which says that the
`|A|`-many tests already see everything the full quantifier over all effective
divisors of degree `r` would see.

## Main result and proof structure

On a subdivision of a **loopless** core, the core vertices are
rank-determining.  The finite-graph proof given here does not invoke Luo's
metric-graph theorem: it factors into a strong-separator argument at `r = 1`
and a purely arithmetic promotion from `r = 1` to all `r`.

Contents:

* `RankDeterminingSet` and its cheap general theory — the trivial direction,
  monotonicity in `A`, the fact that `Finset.univ` is rank-determining, and
  the specialization to `r = 1`, which reproduces
  `rank_ge_one_iff_winnable_sub_one_chip` from `Foundations/RankOne.lean`
  (`rank_ge_one_iff_winnable_sub_one_chip_of_univ`).
* `rankDeterminingSet_of_rank_ge_one` — **the `r = 1` case is the whole
  content**.  A set that decides rank one for every divisor is rank-determining
  at every `r`, by an induction that needs nothing about the graph.
* `Certificate.SubdivisionGraph.Spec.rank_ge_one_of_forall_mem_coreVertices` —
  the single geometric input, at `r = 1`, assembled from the strong-separator
  machinery.
* `Certificate.SubdivisionGraph.Spec.rankDeterminingSet_coreVertices` — the
  theorem itself, at general `r`, and its consumers
  `Spec.rank_ge_one_of_reaches_coreVertices` and
  `Spec.rank_ge_iff_core_criterion`.
* A two-sided rank criterion and its Riemann--Roch reduction
  (`winnable_iff_forall_add_supported_effective`,
  `rank_ge_iff_forall_sub_add_supported`): they take a rank-determining set as a
  hypothesis and derive a two-sided criterion, so that
  the `F`-quantifier costs no second appeal to the geometry.

Everything in this file is proved and depends only on
`[propext, Classical.choice, Quot.sound]`.

## How the theorem is proved

The proof has two halves.

**Half one, `r = 1`.**  The needed statement is that
a divisor reaching every core vertex has rank at least one, and that is the
strong-separator lemma of van Dobben de Bruyn--Gijswijt (Lemma 2.6), formalized
here as `Certificate.StrongSeparator.rank_ge_one_of_strongSeparatorCertificate`
(`Subdivision/StrongSeparator.lean`).  Its hypothesis for the embedded core is
discharged by `Spec.coreVertices_strongSeparatorCertificate`
(`Subdivision/SubdivisionSeparator.lean`), which is exactly the "components of
the complement are slot interiors" step: after removing any enlargement of the
core, each remaining cell is a contiguous interval of positions inside a single
subdivided slot (`Spec.ComplementInterval`, `Spec.exists_complementInterval`),
and `Spec.expansionCell` checks the one-edge and path-cut conditions for it.
These two separator results supply the complete geometric input.

**Half two, `r = 1` implies every `r`: `rankDeterminingSet_of_rank_ge_one`.**
An induction on `r` in which each step applies the `r = 1` hypothesis at a
shifted divisor `D - E`.  No geometry, no induction on the degree of the test
divisor, and no second appeal to half one.  See the section header there.

Consequently **no metric graph appears anywhere**, and the discrete/metric
comparison of Hladký--Král--Norine (Theorem 1.3), which a genuine port of Luo
would have needed in order to descend to `spec.graph`, is not required either.

## The looplessness hypothesis is forced, not defensive

Luo's theorem (Thm. 1.6) is stated for a **loopless model** `(G, ℓ)` of a
metric graph `Γ`; the general criterion behind it (see the form quoted as
"Luo's Theorem" in Cools--Draisma--Payne--Robeva) asks that the closure in `Γ`
of every connected component of `Γ ∖ A` be contractible.

For a subdivision of a core with `A` = the core vertices, a component of
`Γ ∖ A` is the interior of a single edge slot, and its closure is that slot
together with its two endpoints:

* a slot joining **distinct** core vertices closes up to a segment — contractible,
  so the criterion is met;
* a **loop** slot at a core vertex `v` closes up to a circle — *not*
  contractible, and the criterion fails.

The same dichotomy is visible in the proof actually used here, without any
topology: a core vertex `v` carrying a **loop** slot of length `≥ 2` has *two*
edges into that slot's interior, so the interior violates the `oneEdge` field of
`StrongSeparator.ExpansionCell` and is not a strong-separator cell.  A slot
between distinct core vertices contributes one edge at each end, and is.

The failure is not an artifact of the proof: on a core carrying a loop slot, a
divisor can reach every core vertex and still fail to have rank one because the
obstruction lies in the interior of the loop chain.  Statements below therefore
carry looplessness explicitly.

Note that `Certificate.SubdivisionGraph.Spec` already demands
`core_loopless`, so the dangerous object cannot even be built through it.  That
is structural protection, but it is protection only as long as nobody
generalizes to a core type without the field: `ExplicitPotential.Core` itself
permits `tail e = head e`, and a loop slot of length `≥ 2` subdivides to a
perfectly legal loopless `CFGraph`.  This is why the looplessness hypothesis is
repeated as an explicit binder below rather than left implicit in the structure.

## References

Ye Luo, *Rank-determining sets of metric graphs*, J. Combin. Theory Ser. A
**118** (2011), 1775--1793.  Theorem 1.6 there is the general statement whose
special case is proved here; the general criterion is **not** formalized, and
nothing below depends on it.  Likewise Hladký--Král--Norine, *Rank of divisors
on tropical curves* (arXiv:0709.4485), Theorem 1.3, is the
discrete/metric comparison a port of Luo would have needed, and is not used.

The proof that *is* used is the discrete strong-separator lemma of
J. van Dobben de Bruyn and D. Gijswijt, *Treewidth is a lower bound on graph
gonality*, Lemma 2.6, formalized in `Subdivision/StrongSeparator.lean`.
-/

namespace Utilities

/-! ## The definition -/

/-- A divisor is *supported on* `A` when it vanishes at every vertex outside
`A`. -/
def SupportedOn {G : CFGraph} (A : Finset G.V) (E : CFDiv G) : Prop :=
  ∀ v : G.V, v ∉ A → E v = 0

/-- `A` is a **rank-determining set** for `G`: the rank of every divisor is
computed by the effective test divisors supported on `A` alone.

The forward implication is trivial for every `A` (`winnable_sub_of_rank_ge`);
the content is the backward one, and `rankDeterminingSet_iff` repackages the
definition as that half.

Note the quantifier is over all `r : ℤ`, matching `rank_geq`.  For `r < 0` both
sides hold vacuously, so nothing is claimed there. -/
def RankDeterminingSet (G : CFGraph) (A : Finset G.V) : Prop :=
  ∀ (D : CFDiv G) (r : ℤ),
    rank G D ≥ r ↔
      ∀ E : CFDiv G, effective E → deg E = r → SupportedOn A E → winnable G (D - E)

/-! ## The trivial direction, and cheap general theory -/

/-- The trivial half of a rank-determining-set statement: if `rank D ≥ r` then
`D - E` is winnable for *every* effective `E` of degree `r`, supported anywhere.
This holds for all graphs and needs no hypothesis on any vertex set. -/
theorem winnable_sub_of_rank_ge {G : CFGraph} {D : CFDiv G} {r : ℤ}
    (hRank : rank G D ≥ r) {E : CFDiv G} (hEffective : effective E)
    (hDegree : deg E = r) :
    winnable G (D - E) :=
  ((rank_geq_iff G D r).mpr hRank) E ⟨hEffective, hDegree⟩

/-- `RankDeterminingSet` is exactly its nontrivial half.  Consumers proving a
set rank-determining only ever have to supply this implication. -/
theorem rankDeterminingSet_iff {G : CFGraph} (A : Finset G.V) :
    RankDeterminingSet G A ↔
      ∀ (D : CFDiv G) (r : ℤ),
        (∀ E : CFDiv G, effective E → deg E = r → SupportedOn A E →
          winnable G (D - E)) →
        rank G D ≥ r := by
  constructor
  · intro hSet D r hTests
    exact (hSet D r).mpr hTests
  · intro hHard D r
    exact ⟨fun hRank E hEffective hDegree _ =>
      winnable_sub_of_rank_ge hRank hEffective hDegree, hHard D r⟩

/-- Every vertex set containing a rank-determining set is rank-determining.
Enlarging `A` only weakens the hypothesis the hard direction has to consume. -/
theorem RankDeterminingSet.mono {G : CFGraph} {A B : Finset G.V}
    (hSet : RankDeterminingSet G A) (hSubset : A ⊆ B) :
    RankDeterminingSet G B := by
  rw [rankDeterminingSet_iff]
  intro D r hTests
  refine (hSet D r).mpr ?_
  intro E hEffective hDegree hSupport
  exact hTests E hEffective hDegree
    (fun v hv => hSupport v (fun hvA => hv (hSubset hvA)))

/-- The full vertex set is rank-determining; this is the definition of `rank`
unwound, and is the base case that every other rank-determining set improves
on. -/
theorem rankDeterminingSet_univ (G : CFGraph) :
    RankDeterminingSet G (Finset.univ : Finset G.V) := by
  rw [rankDeterminingSet_iff]
  intro D r hTests
  rw [← rank_geq_iff]
  intro E hE
  exact hTests E hE.1 hE.2 (fun v hv => absurd (Finset.mem_univ v) hv)

/-! ## The `r = 1` specialization -/

/-- A one-chip divisor is supported on any set containing its vertex. -/
theorem supportedOn_one_chip {G : CFGraph} {A : Finset G.V} {v : G.V}
    (hv : v ∈ A) : SupportedOn A (one_chip v) := by
  intro w hw
  have hne : w ≠ v := fun h => hw (h ▸ hv)
  simp [one_chip, hne]

/-- At `r = 1` a rank-determining set gives a vertexwise reachability test:
rank at least one is decided by subtracting one chip at each vertex **of
`A`**. -/
theorem rank_ge_one_iff_forall_mem_winnable_sub_one_chip
    {G : CFGraph} {A : Finset G.V} (hSet : RankDeterminingSet G A)
    (D : CFDiv G) :
    rank G D ≥ 1 ↔ ∀ v ∈ A, winnable G (D - one_chip v) := by
  rw [hSet D 1]
  constructor
  · intro hTests v hv
    exact hTests (one_chip v) (eff_one_chip v) (deg_one_chip v)
      (supportedOn_one_chip hv)
  · intro hVertex E hEffective hDegree hSupport
    obtain ⟨v, rfl⟩ := effective_degree_one_eq_one_chip E hEffective hDegree
    refine hVertex v ?_
    by_contra hv
    have hZero : one_chip v v = 0 := hSupport v hv
    simp [one_chip] at hZero

/-- Sanity check that the definition specializes correctly: at `A = univ` the
`r = 1` criterion is exactly `rank_ge_one_iff_winnable_sub_one_chip` from
`Foundations/RankOne.lean`. -/
theorem rank_ge_one_iff_winnable_sub_one_chip_of_univ
    (G : CFGraph) (D : CFDiv G) :
    rank G D ≥ 1 ↔ ∀ v : G.V, winnable G (D - one_chip v) := by
  rw [rank_ge_one_iff_forall_mem_winnable_sub_one_chip
    (rankDeterminingSet_univ G) D]
  simp

/-! ## From `r = 1` to every `r`

`RankDeterminingSet` quantifies over all `r`, but **the `r = 1` case is the
whole content**: `rankDeterminingSet_of_rank_ge_one` below promotes it to every
`r` with no further geometric input.  Only the `r = 1` case ever needs a fact
about the graph, so a consumer proving a set rank-determining has exactly one
obligation.

The promotion is an induction on `r`, and each step uses the `r = 1` hypothesis
at a *shifted divisor*:

* to see `rank D ≥ k + 1` it suffices to see `rank (D - w) ≥ k` for every vertex
  `w` (`rank_ge_add_one_of_forall_rank_sub_one_chip_ge`);
* to see `rank (D - w) ≥ k` the inductive hypothesis asks for
  `winnable (D - w - E)` for `E` effective of degree `k` supported on `A`;
* and that is `winnable (D - E - w)`, which follows from `rank (D - E) ≥ 1` —
  the `r = 1` hypothesis at the divisor `D - E`, whose own tests
  `winnable (D - E - v)` for `v ∈ A` are the degree-`(k+1)` tests of `D` at the
  supported divisors `E + v`.

No induction on the *degree* of the test divisor and no second appeal to the
geometry is involved. -/

/-- An effective divisor of positive degree carries a chip somewhere. -/
theorem exists_chip_of_effective_of_deg_pos {G : CFGraph} {E : CFDiv G}
    (hEffective : effective E) (hDegree : 0 < deg E) :
    ∃ v : G.V, 1 ≤ E v := by
  by_contra hNone
  push Not at hNone
  have hZero : E = 0 := by
    funext v
    have hle := hNone v
    have hge := hEffective v
    simp only [Pi.zero_apply]
    omega
  rw [hZero] at hDegree
  simp at hDegree

/-- Removing one chip from an effective divisor at a vertex where a chip
actually sits leaves an effective divisor. -/
theorem effective_sub_one_chip {G : CFGraph} {E : CFDiv G} {v : G.V}
    (hEffective : effective E) (hChip : 1 ≤ E v) :
    effective (E - one_chip v) := by
  intro w
  by_cases hw : w = v
  · subst w
    simp [one_chip, hChip]
  · simpa [one_chip, hw] using hEffective w

/-- **The one-chip step up.**  If every one-chip subtraction has rank at least
`k ≥ 0`, then the divisor itself has rank at least `k + 1`.  This is the
converse of `rank_sub_one_chip_ge_of_rank_ge_succ` from
`Foundations/RankChipStep.lean`, and it is what turns the `r = 1` case of a
rank-determining-set statement into the general one. -/
theorem rank_ge_add_one_of_forall_rank_sub_one_chip_ge {G : CFGraph}
    {D : CFDiv G} {k : ℤ} (hk : 0 ≤ k)
    (hChips : ∀ v : G.V, rank G (D - one_chip v) ≥ k) :
    rank G D ≥ k + 1 := by
  rw [← rank_geq_iff]
  intro E hE
  obtain ⟨hEffective, hDegree⟩ := hE
  obtain ⟨v, hv⟩ :=
    exists_chip_of_effective_of_deg_pos hEffective (by rw [hDegree]; omega)
  have hSubDegree : deg (E - one_chip v) = k := by
    rw [deg.map_sub, deg_one_chip, hDegree]
    ring
  have hWin := (rank_geq_iff G (D - one_chip v) k).mpr (hChips v)
    (E - one_chip v) ⟨effective_sub_one_chip hEffective hv, hSubDegree⟩
  have hRewrite : D - one_chip v - (E - one_chip v) = D - E := by abel
  rwa [hRewrite] at hWin

/-- **The `r = 1` case is the whole content of `RankDeterminingSet`.**

A vertex set which decides *rank one* for every divisor — i.e. for which
`winnable (D - v)` at all `v ∈ A` already forces `rank D ≥ 1` — is
rank-determining at every `r`.

This is the reduction that lets a geometric input be supplied only once, at
`r = 1`; see `Spec.rankDeterminingSet_coreVertices`. -/
theorem rankDeterminingSet_of_rank_ge_one {G : CFGraph} {A : Finset G.V}
    (hOne : ∀ D : CFDiv G, (∀ v ∈ A, winnable G (D - one_chip v)) →
      rank G D ≥ 1) :
    RankDeterminingSet G A := by
  have key : ∀ k : ℕ, ∀ D : CFDiv G,
      (∀ E : CFDiv G, effective E → deg E = (k : ℤ) → SupportedOn A E →
        winnable G (D - E)) →
      rank G D ≥ (k : ℤ) := by
    intro k
    induction k with
    | zero =>
        intro D hTests
        have hWin : winnable G D := by
          have hZero := hTests 0 (fun _ => le_refl 0) (by simp) (fun _ _ => rfl)
          simpa using hZero
        simp only [Nat.cast_zero]
        exact (rank_geq_iff G D 0).mp ((rank_nonneg_iff_winnable G D).mpr hWin)
    | succ k ih =>
        intro D hTests
        have hTests' : ∀ E : CFDiv G, effective E → deg E = (k : ℤ) + 1 →
            SupportedOn A E → winnable G (D - E) := by
          intro E hEffective hDegree hSupport
          refine hTests E hEffective ?_ hSupport
          push_cast
          exact hDegree
        have hChips : ∀ w : G.V, rank G (D - one_chip w) ≥ (k : ℤ) := by
          intro w
          refine ih (D - one_chip w) ?_
          intro E hEffective hDegree hSupport
          have hRankOne : rank G (D - E) ≥ 1 := by
            refine hOne (D - E) ?_
            intro v hv
            have hAddEffective : effective (E + one_chip v) := fun x =>
              add_nonneg (hEffective x) (eff_one_chip v x)
            have hAddDegree : deg (E + one_chip v) = (k : ℤ) + 1 := by
              rw [map_add, hDegree, deg_one_chip]
            have hAddSupport : SupportedOn A (E + one_chip v) := by
              intro x hx
              have hEx := hSupport x hx
              have hOneChipx := supportedOn_one_chip hv x hx
              simp [Pi.add_apply, hEx, hOneChipx]
            have hWin := hTests' (E + one_chip v) hAddEffective hAddDegree
              hAddSupport
            have hRewrite : D - (E + one_chip v) = D - E - one_chip v := by
              abel
            rwa [hRewrite] at hWin
          have hWin :=
            (rank_ge_one_iff_winnable_sub_one_chip G (D - E)).mp hRankOne w
          have hRewrite : D - E - one_chip w = D - one_chip w - E := by abel
          rwa [hRewrite] at hWin
        have hStep := rank_ge_add_one_of_forall_rank_sub_one_chip_ge
          (Int.natCast_nonneg k) hChips
        push_cast
        exact hStep
  rw [rankDeterminingSet_iff]
  intro D r hTests
  rcases lt_or_ge r 0 with hr | hr
  · have hNegOne := rank_geq_neg_one G D
    omega
  · lift r to ℕ using hr with k
    exact key k D hTests

/-! ## A two-sided criterion and its Riemann--Roch reduction

The relevant criterion is

```
rank D ≥ r  ↔  D - E + F winnable  for all effective E of degree r and
                all effective F of degree g - deg D + r - 1, both supported on A.
```

Although a rank-determining-set hypothesis appears relevant to both
quantifiers, the `F`-side is a Riemann--Roch consequence of the `E`-side.  The reduction is
`winnable_iff_forall_add_supported_effective` below, and it is short:

* `D` is winnable iff `rank (K - D) ≥ g - 1 - deg D`
  (`canonical_sub_rank_ge_iff_winnable_of_degree`);
* that rank inequality is tested on `A` by the *one* rank-determining-set
  hypothesis;
* each test `winnable (K - D - F)` is `winnable (K - (D + F))`, and
  `deg (D + F) = g - 1`, so it is `winnable (D + F)`
  (`degree_genus_sub_one_winnable_iff_complement_winnable`).

No induction on `deg F` is needed; the degree bookkeeping does it in one step.
-/

/-- **The Riemann--Roch reduction of the `F`-quantifier.**  Winnability of `D`
is decided by winnability of `D + F` for the effective divisors `F` of the
complementary degree `g - 1 - deg D` supported on a rank-determining set.

Thus only one rank-determining-set hypothesis is required. -/
theorem winnable_iff_forall_add_supported_effective
    {G : CFGraph} {A : Finset G.V} (hConnected : graph_connected G)
    (hSet : RankDeterminingSet G A) (D : CFDiv G) :
    winnable G D ↔
      ∀ F : CFDiv G, effective F → deg F = genus G - 1 - deg D →
        SupportedOn A F → winnable G (D + F) := by
  have hDual :
      winnable G D ↔
        rank G (canonical_divisor G - D) ≥ genus G - 1 - deg D :=
    (canonical_sub_rank_ge_iff_winnable_of_degree hConnected D
      (genus G - 1 - deg D) (by ring)).symm
  rw [hDual, hSet (canonical_divisor G - D) (genus G - 1 - deg D)]
  refine forall_congr' fun F => ?_
  refine imp_congr_right fun _hEffective => ?_
  refine imp_congr_right fun hDegree => ?_
  refine imp_congr_right fun _hSupport => ?_
  have hSum : canonical_divisor G - D - F = canonical_divisor G - (D + F) := by
    abel
  have hDegSum : deg (D + F) = genus G - 1 := by
    rw [map_add, hDegree]
    ring
  rw [hSum]
  exact (degree_genus_sub_one_winnable_iff_complement_winnable hConnected
    (D + F) hDegSum).symm

/-- **Two-sided rank criterion.**  For a rank-determining set `A` on a connected
graph, `rank D ≥ r` is decided by the two-sided test
`D - E + F` over effective `E` of degree `r` and effective `F` of degree
`g - deg D + r - 1`, both supported on `A`.

It follows from a single rank-determining-set hypothesis: the `E`-side is
that hypothesis, and the `F`-side is
`winnable_iff_forall_add_supported_effective`. -/
theorem rank_ge_iff_forall_sub_add_supported
    {G : CFGraph} {A : Finset G.V} (hConnected : graph_connected G)
    (hSet : RankDeterminingSet G A) (D : CFDiv G) (r : ℤ) :
    rank G D ≥ r ↔
      ∀ E : CFDiv G, effective E → deg E = r → SupportedOn A E →
        ∀ F : CFDiv G, effective F → deg F = genus G - deg D + r - 1 →
          SupportedOn A F → winnable G (D - E + F) := by
  rw [hSet D r]
  refine forall_congr' fun E => ?_
  refine imp_congr_right fun _hEffective => ?_
  refine imp_congr_right fun hDegree => ?_
  refine imp_congr_right fun _hSupport => ?_
  rw [winnable_iff_forall_add_supported_effective hConnected hSet (D - E)]
  have hDegSub : deg (D - E) = deg D - r := by
    rw [deg.map_sub, hDegree]
  rw [hDegSub,
    show genus G - 1 - (deg D - r) = genus G - deg D + r - 1 from by ring]

end Utilities

/-! ## Luo's theorem for a subdivided loopless core -/

namespace Utilities.Certificate.SubdivisionGraph

variable {n p : ℕ}

/-- The core vertices of a subdivision, as a finite set of subdivision
vertices. -/
def Spec.coreVertices (spec : Spec n p) : Finset spec.graph.V :=
  (Finset.univ : Finset (Fin n)).image spec.coreVertex

@[simp] theorem Spec.mem_coreVertices (spec : Spec n p) (x : spec.graph.V) :
    x ∈ spec.coreVertices ↔ ∃ v : Fin n, spec.coreVertex v = x := by
  simp [Spec.coreVertices]

/-- `Spec.coreVertices` and the `ExplicitPotential.Certificate` spelling of the
same set agree on the nose.  Both are `Finset.univ.image spec.coreVertex`; the
duplicate exists only because the two namespaces grew independently, and this
`rfl` lets the separator machinery be quoted verbatim. -/
theorem Spec.coreVertices_eq (spec : Spec n p) :
    spec.coreVertices = ExplicitPotential.Certificate.coreVertices spec := rfl

/-- **The geometric input, at `r = 1`: a divisor reaching every core vertex of
a subdivided loopless core has rank at least one.**

This is the entire graph-theoretic content of the rank-determining-set theorem
below; `rankDeterminingSet_of_rank_ge_one` supplies every other `r` for free.

It is *not* proved here by porting Luo's general metric-graph criterion.  The
proof assembles the following two finite-graph ingredients:

* `SubdivisionSeparator.lean` — **"components of the complement are slot
  interiors"**.  `Spec.ComplementInterval` and `Spec.exists_complementInterval`
  show that after removing any enlargement `R ⊇ core vertices`, every remaining
  cell is a contiguous interval `(left, right)` of positions inside a *single*
  subdivided slot, with `left` and `right` in `R`; `Spec.expansionCell` packages
  such an interval as a `StrongSeparator.ExpansionCell`, verifying the two
  properties that fail for a loop slot — one edge per boundary vertex into the
  cell, and the path-cut condition.  Culminates in
  `Spec.coreVertices_strongSeparatorCertificate`.
* `StrongSeparator.lean` — **"the one-path lemma implies the theorem"**.
  `StrongSeparator.rank_ge_one_of_strongSeparatorCertificate` is the discrete
  form of van Dobben de Bruyn--Gijswijt, Lemma 2.6: enlarge the core to the set
  `R` of *all* vertices reached by `D`, and if `R ≠ univ` a complementary cell
  plus one `q`-reduction produces a vertex outside `R` that `D` reaches after
  all — a contradiction.

**Where looplessness enters.**  `Spec` carries `core_loopless` as a field, and
it is used twice in the chain above: `stepLeft_ne_stepRight` needs it to build
`spec.graph` at all when a slot has length one, and — the substantive use — the
`oneEdge` field of the expansion cell needs it, because a core vertex `v`
carrying a loop slot of length `≥ 2` has **two** edges into that slot's
interior, so the interior is not a strong-separator cell. -/
theorem Spec.rank_ge_one_of_forall_mem_coreVertices (spec : Spec n p)
    (hConnected : graph_connected spec.graph) (D : CFDiv spec.graph)
    (hReaches : ∀ x ∈ spec.coreVertices,
      winnable spec.graph (D - one_chip x)) :
    rank spec.graph D ≥ 1 := by
  refine StrongSeparator.rank_ge_one_of_strongSeparatorCertificate hConnected
    (ExplicitPotential.Certificate.coreVertices_nonempty spec)
    spec.coreVertices_strongSeparatorCertificate ?_
  intro s hs
  exact hReaches s (by rwa [spec.coreVertices_eq])

/-- **A finite-graph special case of Luo's rank-determining set theorem.**
On the subdivision of a finite loopless core, the core vertices are
rank-determining: for every divisor `D` and every `r`, `rank D ≥ r` already
follows from winnability of `D - E` for the effective divisors `E` of degree `r`
supported at core vertices.

The general statement is Ye Luo, *Rank-determining sets of metric graphs*,
J. Combin. Theory Ser. A **118** (2011), 1775--1793, Theorem 1.6 ("for a
loopless model `(G, ℓ)` of a metric graph `Γ`, the set `V(G) ⊆ Γ` is
rank-determining").  **Luo is not used, and no metric graph appears.**  In the
special case at hand — a subdivision of a loopless core, tested at its own core
vertices — the theorem factors into two elementary halves:

* the `r = 1` case, `Spec.rank_ge_one_of_forall_mem_coreVertices`, which is the
  strong-separator argument on the slot-interval decomposition of the
  complement (see that docstring for the full attribution);
* the promotion from `r = 1` to all `r`,
  `rankDeterminingSet_of_rank_ge_one`, which is pure divisor bookkeeping and
  uses nothing about the graph.

Consequently no discrete/metric comparison (Hladký--Král--Norine, Theorem 1.3)
is needed either: the whole argument stays on the finite graph `spec.graph`.

**Looplessness is a hypothesis of the theorem, not a convenience.**
`hLoopless` restates the field `spec.core_loopless`; it is an explicit binder
so that no consumer can invoke this result without meeting it, and so that a
future restatement over a core type that does not build looplessness in
(`ExplicitPotential.Core` does not) keeps it.  With a loop slot at a core vertex
`v`, that vertex has two edges into the slot's interior, the interior is not a
strong-separator cell, the closure of the corresponding component of
`Γ ∖ (core vertices)` is a circle rather than a segment, and the conclusion is
false: a divisor may reach every core vertex of a loop-carrying core and still
have rank zero, with the obstruction living in the loop chain's interior.

`hConnected` is needed by the `q`-reduced-representative step inside the
strong-separator lemma and by the Riemann--Roch argument. -/
theorem Spec.rankDeterminingSet_coreVertices (spec : Spec n p)
    (hLoopless : ∀ edge : Fin p, spec.core.tail edge ≠ spec.core.head edge)
    (hConnected : graph_connected spec.graph) :
    RankDeterminingSet spec.graph spec.coreVertices := by
  -- `hLoopless` is *literally* the structure field `spec.core_loopless`, which
  -- is what the separator construction below consumes (through the `oneEdge`
  -- field of the expansion cell).  Recording that equation both discharges the
  -- binder and documents why the binder is kept: a future restatement over a
  -- core type that does not build looplessness in must still supply it.
  have _hLooplessIsField : hLoopless = spec.core_loopless := rfl
  exact rankDeterminingSet_of_rank_ge_one fun D hD =>
    spec.rank_ge_one_of_forall_mem_coreVertices hConnected D hD

/-- The `r = 1` core criterion: a divisor on the subdivision that reaches every
core vertex has rank at least one.

Proved, via `Spec.rankDeterminingSet_coreVertices`. -/
theorem Spec.rank_ge_one_of_reaches_coreVertices (spec : Spec n p)
    (hLoopless : ∀ edge : Fin p, spec.core.tail edge ≠ spec.core.head edge)
    (hConnected : graph_connected spec.graph) (D : CFDiv spec.graph)
    (hReaches : ∀ v : Fin n,
      winnable spec.graph (D - one_chip (spec.coreVertex v))) :
    rank spec.graph D ≥ 1 := by
  rw [rank_ge_one_iff_forall_mem_winnable_sub_one_chip
    (spec.rankDeterminingSet_coreVertices hLoopless hConnected) D]
  intro x hx
  obtain ⟨v, rfl⟩ := (spec.mem_coreVertices x).mp hx
  exact hReaches v

/-- The two-sided criterion on a subdivided loopless core, at general `r`: the
combination of `Spec.rankDeterminingSet_coreVertices` (for the `E`-quantifier)
with the Riemann--Roch reduction (for the `F`-quantifier).  Both inputs are
proved above. -/
theorem Spec.rank_ge_iff_core_criterion (spec : Spec n p)
    (hLoopless : ∀ edge : Fin p, spec.core.tail edge ≠ spec.core.head edge)
    (hConnected : graph_connected spec.graph) (D : CFDiv spec.graph) (r : ℤ) :
    rank spec.graph D ≥ r ↔
      ∀ E : CFDiv spec.graph, effective E → deg E = r →
          SupportedOn spec.coreVertices E →
        ∀ F : CFDiv spec.graph, effective F →
            deg F = genus spec.graph - deg D + r - 1 →
          SupportedOn spec.coreVertices F →
            winnable spec.graph (D - E + F) :=
  rank_ge_iff_forall_sub_add_supported hConnected
    (spec.rankDeterminingSet_coreVertices hLoopless hConnected) D r

end Utilities.Certificate.SubdivisionGraph
