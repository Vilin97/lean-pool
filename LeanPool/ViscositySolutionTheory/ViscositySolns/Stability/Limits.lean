/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Abstract stability through tail-closed semijet graphs

This file isolates the closed-graph argument used in stability theorems. The
analytic content of locally uniform convergence is separated into an
approximation hypothesis saying that semijets of the limit lie in the tail
closure of semijet graphs of the approximating functions.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat} {ι : Type*}

/--
Tail closure of the superjet graphs of a family `uᵢ` along a filter `l`.

A point `z` belongs to this set if, for every set of indices `A` with
`A ∈ l`, the point `z` belongs to the closure of
`⋃ i ∈ A, SuperjetGraph C (uᵢ i)`.
-/
def TailClosureSuperjetGraph (C : Set (Point n)) (uᵢ : ι -> Point n -> Real)
    (l : Filter ι) : Set ((Point n × Real) × Jet n) :=
  {z | ∀ A : Set ι, A ∈ l -> z ∈ closure (⋃ i ∈ A, SuperjetGraph C (uᵢ i))}

/--
Tail closure of the subjet graphs of a family `uᵢ` along a filter `l`.
-/
def TailClosureSubjetGraph (C : Set (Point n)) (uᵢ : ι -> Point n -> Real)
    (l : Filter ι) : Set ((Point n × Real) × Jet n) :=
  {z | ∀ A : Set ι, A ∈ l -> z ∈ closure (⋃ i ∈ A, SubjetGraph C (uᵢ i))}

/--
Neighborhood criterion for tail closure of superjet graphs.

If, for every set of indices `A` with `A ∈ l`, every neighborhood of `z`
contains a point of `⋃ i ∈ A, SuperjetGraph C (uᵢ i)`, then `z` belongs to
`TailClosureSuperjetGraph C uᵢ l`.
-/
theorem tailClosureSuperjetGraph_of_forall_nhds_exists
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {z : (Point n × Real) × Jet n}
    (h : ∀ A : Set ι, A ∈ l -> ∀ W : Set ((Point n × Real) × Jet n),
      W ∈ nhds z -> ∃ w ∈ W, w ∈ ⋃ i ∈ A, SuperjetGraph C (uᵢ i)) :
    z ∈ TailClosureSuperjetGraph C uᵢ l := by
  intro A hA
  rw [mem_closure_iff_nhds]
  intro W hW
  rcases h A hA W hW with ⟨w, hwW, hwgraph⟩
  exact ⟨w, hwW, hwgraph⟩

/--
Neighborhood criterion for tail closure of subjet graphs.

If, for every set of indices `A` with `A ∈ l`, every neighborhood of `z`
contains a point of `⋃ i ∈ A, SubjetGraph C (uᵢ i)`, then `z` belongs to
`TailClosureSubjetGraph C uᵢ l`.
-/
theorem tailClosureSubjetGraph_of_forall_nhds_exists
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {z : (Point n × Real) × Jet n}
    (h : ∀ A : Set ι, A ∈ l -> ∀ W : Set ((Point n × Real) × Jet n),
      W ∈ nhds z -> ∃ w ∈ W, w ∈ ⋃ i ∈ A, SubjetGraph C (uᵢ i)) :
    z ∈ TailClosureSubjetGraph C uᵢ l := by
  intro A hA
  rw [mem_closure_iff_nhds]
  intro W hW
  rcases h A hA W hW with ⟨w, hwW, hwgraph⟩
  exact ⟨w, hwW, hwgraph⟩

/--
Componentwise neighborhood criterion for tail closure of superjet graphs.

If every neighborhood of `((x, r), J)` contains a graph point
`((y, s), J') ∈ SuperjetGraph C (uᵢ i)` with `i ∈ A`, for every set of indices
`A` satisfying `A ∈ l`, then `((x, r), J)` belongs to the tail closure.
-/
theorem tailClosureSuperjetGraph_of_forall_nhds_exists_components
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x : Point n} {r : Real} {J : Jet n}
    (h : ∀ A : Set ι, A ∈ l -> ∀ W : Set ((Point n × Real) × Jet n),
      W ∈ nhds ((x, r), J) ->
        ∃ i ∈ A, ∃ y s J',
          ((y, s), J') ∈ SuperjetGraph C (uᵢ i) ∧ ((y, s), J') ∈ W) :
    ((x, r), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  refine tailClosureSuperjetGraph_of_forall_nhds_exists ?_
  intro A hA W hW
  rcases h A hA W hW with ⟨i, hiA, y, s, J', hgraph, hWmem⟩
  exact ⟨((y, s), J'), hWmem,
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hgraph⟩⟩⟩

/--
Componentwise neighborhood criterion for tail closure of subjet graphs.

If every neighborhood of `((x, r), J)` contains a graph point
`((y, s), J') ∈ SubjetGraph C (uᵢ i)` with `i ∈ A`, for every set of indices
`A` satisfying `A ∈ l`, then `((x, r), J)` belongs to the tail closure.
-/
theorem tailClosureSubjetGraph_of_forall_nhds_exists_components
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x : Point n} {r : Real} {J : Jet n}
    (h : ∀ A : Set ι, A ∈ l -> ∀ W : Set ((Point n × Real) × Jet n),
      W ∈ nhds ((x, r), J) ->
        ∃ i ∈ A, ∃ y s J',
          ((y, s), J') ∈ SubjetGraph C (uᵢ i) ∧ ((y, s), J') ∈ W) :
    ((x, r), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  refine tailClosureSubjetGraph_of_forall_nhds_exists ?_
  intro A hA W hW
  rcases h A hA W hW with ⟨i, hiA, y, s, J', hgraph, hWmem⟩
  exact ⟨((y, s), J'), hWmem,
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hgraph⟩⟩⟩

/-- Tail closures of superjet graphs are closed sets. -/
theorem isClosed_tailClosureSuperjetGraph
    (C : Set (Point n)) (uᵢ : ι -> Point n -> Real) (l : Filter ι) :
    IsClosed (TailClosureSuperjetGraph C uᵢ l) := by
  have hclosed : ∀ A : Set ι,
      IsClosed {z : (Point n × Real) × Jet n |
        A ∈ l -> z ∈ closure (⋃ i ∈ A, SuperjetGraph C (uᵢ i))} := by
    intro A
    by_cases hA : A ∈ l
    · simpa only [hA, true_implies, Set.ofPred_mem_eq] using
        (isClosed_closure (s := ⋃ i ∈ A, SuperjetGraph C (uᵢ i)))
    · have hset : {z : (Point n × Real) × Jet n |
          A ∈ l -> z ∈ closure (⋃ i ∈ A, SuperjetGraph C (uᵢ i))} = Set.univ := by
        ext z
        simp only [hA, false_implies, Set.ofPred_true]
      rw [hset]
      exact isClosed_univ
  rw [TailClosureSuperjetGraph, Set.ofPred_forall]
  exact isClosed_iInter hclosed

/-- Tail closures of subjet graphs are closed sets. -/
theorem isClosed_tailClosureSubjetGraph
    (C : Set (Point n)) (uᵢ : ι -> Point n -> Real) (l : Filter ι) :
    IsClosed (TailClosureSubjetGraph C uᵢ l) := by
  have hclosed : ∀ A : Set ι,
      IsClosed {z : (Point n × Real) × Jet n |
        A ∈ l -> z ∈ closure (⋃ i ∈ A, SubjetGraph C (uᵢ i))} := by
    intro A
    by_cases hA : A ∈ l
    · simpa only [hA, true_implies, Set.ofPred_mem_eq] using
        (isClosed_closure (s := ⋃ i ∈ A, SubjetGraph C (uᵢ i)))
    · have hset : {z : (Point n × Real) × Jet n |
          A ∈ l -> z ∈ closure (⋃ i ∈ A, SubjetGraph C (uᵢ i))} = Set.univ := by
        ext z
        simp only [hA, false_implies, Set.ofPred_true]
      rw [hset]
      exact isClosed_univ
  rw [TailClosureSubjetGraph, Set.ofPred_forall]
  exact isClosed_iInter hclosed

/--
A limit of tail-closed superjet graph points is tail-closed.
-/
theorem tailClosureSuperjetGraph_of_tendsto_tailClosureSuperjetGraph
    {α : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} {m : Filter α} [m.NeBot]
    {z : (Point n × Real) × Jet n} {zα : α -> (Point n × Real) × Jet n}
    (hz : Tendsto zα m (nhds z))
    (hmem : ∀ᶠ a in m, zα a ∈ TailClosureSuperjetGraph C uᵢ l) :
    z ∈ TailClosureSuperjetGraph C uᵢ l :=
  (isClosed_tailClosureSuperjetGraph C uᵢ l).mem_of_tendsto hz hmem

/--
A limit of tail-closed subjet graph points is tail-closed.
-/
theorem tailClosureSubjetGraph_of_tendsto_tailClosureSubjetGraph
    {α : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} {m : Filter α} [m.NeBot]
    {z : (Point n × Real) × Jet n} {zα : α -> (Point n × Real) × Jet n}
    (hz : Tendsto zα m (nhds z))
    (hmem : ∀ᶠ a in m, zα a ∈ TailClosureSubjetGraph C uᵢ l) :
    z ∈ TailClosureSubjetGraph C uᵢ l :=
  (isClosed_tailClosureSubjetGraph C uᵢ l).mem_of_tendsto hz hmem

/--
If every positive identity-matrix perturbation along the sequence
`1 / (k + 1)` lies in the tail closure of the superjet graphs, then the
unperturbed jet lies in the same tail closure.
-/
theorem tailClosureSuperjetGraph_of_nat_hessian_add_identity
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x p : Point n} {r : Real} {X : Hessian n}
    (hmem : ∀ k : Nat,
      ((x, r),
        { gradient := p
          hessian := X + (1 / ((k : Real) + 1)) • (1 : Hessian n) }) ∈
          TailClosureSuperjetGraph C uᵢ l) :
    ((x, r), { gradient := p, hessian := X }) ∈
      TailClosureSuperjetGraph C uᵢ l := by
  let δ : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  let Jδ : Nat -> Jet n := fun k =>
    { gradient := p
      hessian := X + δ k • (1 : Hessian n) }
  let J : Jet n := { gradient := p, hessian := X }
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hH : Tendsto (fun k : Nat => X + δ k • (1 : Hessian n)) atTop (nhds X) := by
    simpa using (tendsto_const_nhds.add (hδ.smul_const (1 : Hessian n)))
  have hJdata : Tendsto (fun k : Nat => (p, X + δ k • (1 : Hessian n)))
      atTop (nhds (p, X)) :=
    tendsto_const_nhds.prodMk_nhds hH
  have hJ : Tendsto Jδ atTop (nhds J) := by
    rw [show nhds J =
        comap (fun K : Jet n => (K.gradient, K.hessian)) (nhds (p, X)) by
          simpa [J] using
            (nhds_induced (fun K : Jet n => (K.gradient, K.hessian)) J)]
    rw [tendsto_comap_iff]
    exact hJdata
  have hz : Tendsto (fun k : Nat => ((x, r), Jδ k)) atTop
      (nhds ((x, r), J)) :=
    tendsto_const_nhds.prodMk_nhds hJ
  refine tailClosureSuperjetGraph_of_tendsto_tailClosureSuperjetGraph hz ?_
  filter_upwards with k
  simpa [δ, Jδ] using hmem k

/--
If every negative identity-matrix perturbation along the sequence
`1 / (k + 1)` lies in the tail closure of the subjet graphs, then the
unperturbed jet lies in the same tail closure.
-/
theorem tailClosureSubjetGraph_of_nat_hessian_sub_identity
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x p : Point n} {r : Real} {X : Hessian n}
    (hmem : ∀ k : Nat,
      ((x, r),
        { gradient := p
          hessian := X - (1 / ((k : Real) + 1)) • (1 : Hessian n) }) ∈
          TailClosureSubjetGraph C uᵢ l) :
    ((x, r), { gradient := p, hessian := X }) ∈
      TailClosureSubjetGraph C uᵢ l := by
  let δ : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  let Jδ : Nat -> Jet n := fun k =>
    { gradient := p
      hessian := X - δ k • (1 : Hessian n) }
  let J : Jet n := { gradient := p, hessian := X }
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hH : Tendsto (fun k : Nat => X - δ k • (1 : Hessian n)) atTop (nhds X) := by
    simpa using (tendsto_const_nhds.sub (hδ.smul_const (1 : Hessian n)))
  have hJdata : Tendsto (fun k : Nat => (p, X - δ k • (1 : Hessian n)))
      atTop (nhds (p, X)) :=
    tendsto_const_nhds.prodMk_nhds hH
  have hJ : Tendsto Jδ atTop (nhds J) := by
    rw [show nhds J =
        comap (fun K : Jet n => (K.gradient, K.hessian)) (nhds (p, X)) by
          simpa [J] using
            (nhds_induced (fun K : Jet n => (K.gradient, K.hessian)) J)]
    rw [tendsto_comap_iff]
    exact hJdata
  have hz : Tendsto (fun k : Nat => ((x, r), Jδ k)) atTop
      (nhds ((x, r), J)) :=
    tendsto_const_nhds.prodMk_nhds hJ
  refine tailClosureSubjetGraph_of_tendsto_tailClosureSubjetGraph hz ?_
  filter_upwards with k
  simpa [δ, Jδ] using hmem k

/--
A convergent net of approximating superjet graph points gives a point in the
tail closure of the approximating superjet graphs.
-/
theorem tailClosureSuperjetGraph_of_tendsto_superjetGraph
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {z : (Point n × Real) × Jet n} {zᵢ : ι -> (Point n × Real) × Jet n}
    (hz : Tendsto zᵢ l (nhds z))
    (hgraph : ∀ᶠ i in l, zᵢ i ∈ SuperjetGraph C (uᵢ i)) :
    z ∈ TailClosureSuperjetGraph C uᵢ l := by
  intro A hA
  have htail : ∀ᶠ i in l, zᵢ i ∈ ⋃ i ∈ A, SuperjetGraph C (uᵢ i) := by
    filter_upwards [hA, hgraph] with i hiA hiz
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hiz⟩⟩
  exact mem_closure_of_tendsto hz htail

/--
A convergent net of approximating subjet graph points gives a point in the
tail closure of the approximating subjet graphs.
-/
theorem tailClosureSubjetGraph_of_tendsto_subjetGraph
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {z : (Point n × Real) × Jet n} {zᵢ : ι -> (Point n × Real) × Jet n}
    (hz : Tendsto zᵢ l (nhds z))
    (hgraph : ∀ᶠ i in l, zᵢ i ∈ SubjetGraph C (uᵢ i)) :
    z ∈ TailClosureSubjetGraph C uᵢ l := by
  intro A hA
  have htail : ∀ᶠ i in l, zᵢ i ∈ ⋃ i ∈ A, SubjetGraph C (uᵢ i) := by
    filter_upwards [hA, hgraph] with i hiA hiz
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hiz⟩⟩
  exact mem_closure_of_tendsto hz htail

/--
Componentwise convergence of selected approximating superjet graph triples
gives tail-closure membership.
-/
theorem tailClosureSuperjetGraph_of_tendsto_superjetGraph_components
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l,
      ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph C (uᵢ i)) :
    ((x, r), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  exact tailClosureSuperjetGraph_of_tendsto_superjetGraph
    ((hx.prodMk_nhds hr).prodMk_nhds hJ) hgraph

/--
Componentwise convergence of selected approximating subjet graph triples gives
tail-closure membership.
-/
theorem tailClosureSubjetGraph_of_tendsto_subjetGraph_components
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l,
      ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph C (uᵢ i)) :
    ((x, r), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  exact tailClosureSubjetGraph_of_tendsto_subjetGraph
    ((hx.prodMk_nhds hr).prodMk_nhds hJ) hgraph

/--
Let `K ⊆ C`. If the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i)` belongs to `l`, and the set of
indices `i` for which `nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C` belongs to
`l`, then the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph C (uᵢ i)` belongs to `l`.
-/
theorem eventually_superjetGraph_of_eventually_superjetGraph_of_nhdsWithin_eq
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i))
    (hnhds : ∀ᶠ i in l, nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C) :
    ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph C (uᵢ i) := by
  filter_upwards [hgraph, hnhds] with i hzi hi
  exact mem_superjetGraph_of_mem_of_nhdsWithin_eq hKC hi hzi

/--
Let `K ⊆ C`. If the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i)` belongs to `l`, and the set of
indices `i` for which `nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C` belongs to
`l`, then the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph C (uᵢ i)` belongs to `l`.
-/
theorem eventually_subjetGraph_of_eventually_subjetGraph_of_nhdsWithin_eq
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i))
    (hnhds : ∀ᶠ i in l, nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C) :
    ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph C (uᵢ i) := by
  filter_upwards [hgraph, hnhds] with i hzi hi
  exact mem_subjetGraph_of_mem_of_nhdsWithin_eq hKC hi hzi

/--
Let `K ⊆ C`. If the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i)` belongs to `l`, and the set of
indices `i` for which `K ∈ nhdsWithin (xᵢ i) C` belongs to `l`, then the set of
indices `i` for which `((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph C (uᵢ i)` belongs
to `l`.
-/
theorem eventually_superjetGraph_of_eventually_superjetGraph_of_mem_nhdsWithin
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph C (uᵢ i) :=
  eventually_superjetGraph_of_eventually_superjetGraph_of_nhdsWithin_eq hKC hgraph <|
    hKnhds.mono fun _ hi => nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hi

/--
Let `K ⊆ C`. If the set of indices `i` for which
`((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i)` belongs to `l`, and the set of
indices `i` for which `K ∈ nhdsWithin (xᵢ i) C` belongs to `l`, then the set of
indices `i` for which `((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph C (uᵢ i)` belongs
to `l`.
-/
theorem eventually_subjetGraph_of_eventually_subjetGraph_of_mem_nhdsWithin
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph C (uᵢ i) :=
  eventually_subjetGraph_of_eventually_subjetGraph_of_nhdsWithin_eq hKC hgraph <|
    hKnhds.mono fun _ hi => nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hi

/--
Selected convergent superjet graph triples on a local domain `K` give a
tail-closure point for the ambient domain `C`, assuming that the set of indices
`i` for which `nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C` belongs to `l`.
-/
theorem tailClosureSuperjetGraph_of_tendsto_superjetGraph_nhdsWithin_eq
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i))
    (hnhds : ∀ᶠ i in l, nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C) :
    ((x, r), J) ∈ TailClosureSuperjetGraph C uᵢ l :=
  tailClosureSuperjetGraph_of_tendsto_superjetGraph_components hx hr hJ
    (eventually_superjetGraph_of_eventually_superjetGraph_of_nhdsWithin_eq
      hKC hgraph hnhds)

/--
Selected convergent subjet graph triples on a local domain `K` give a
tail-closure point for the ambient domain `C`, assuming that the set of indices
`i` for which `nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C` belongs to `l`.
-/
theorem tailClosureSubjetGraph_of_tendsto_subjetGraph_nhdsWithin_eq
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i))
    (hnhds : ∀ᶠ i in l, nhdsWithin (xᵢ i) K = nhdsWithin (xᵢ i) C) :
    ((x, r), J) ∈ TailClosureSubjetGraph C uᵢ l :=
  tailClosureSubjetGraph_of_tendsto_subjetGraph_components hx hr hJ
    (eventually_subjetGraph_of_eventually_subjetGraph_of_nhdsWithin_eq
      hKC hgraph hnhds)

/--
Selected convergent superjet graph triples on a local domain `K` give a
tail-closure point for the ambient domain `C` when the set of indices `i`
for which `K ∈ nhdsWithin (xᵢ i) C` belongs to `l`.
-/
theorem tailClosureSuperjetGraph_of_tendsto_superjetGraph_mem_nhdsWithin
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SuperjetGraph K (uᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, r), J) ∈ TailClosureSuperjetGraph C uᵢ l :=
  tailClosureSuperjetGraph_of_tendsto_superjetGraph_components hx hr hJ
    (eventually_superjetGraph_of_eventually_superjetGraph_of_mem_nhdsWithin
      hKC hgraph hKnhds)

/--
Selected convergent subjet graph triples on a local domain `K` give a
tail-closure point for the ambient domain `C` when the set of indices `i`
for which `K ∈ nhdsWithin (xᵢ i) C` belongs to `l`.
-/
theorem tailClosureSubjetGraph_of_tendsto_subjetGraph_mem_nhdsWithin
    {K C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    {x : Point n} {r : Real} {J : Jet n}
    {xᵢ : ι -> Point n} {rᵢ : ι -> Real} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hr : Tendsto rᵢ l (nhds r))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hgraph : ∀ᶠ i in l, ((xᵢ i, rᵢ i), Jᵢ i) ∈ SubjetGraph K (uᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, r), J) ∈ TailClosureSubjetGraph C uᵢ l :=
  tailClosureSubjetGraph_of_tendsto_subjetGraph_components hx hr hJ
    (eventually_subjetGraph_of_eventually_subjetGraph_of_mem_nhdsWithin
      hKC hgraph hKnhds)

/--
If the set of indices `i` for which `uᵢ i` agrees with `u` on `C` belongs to
`l`, then every superjet graph point of `u` belongs to the tail closure of the
approximating superjet graphs.
-/
theorem superjetGraph_subset_tailClosureSuperjetGraph_of_eventually_eqOn
    {C : Set (Point n)} {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot]
    (heq : ∀ᶠ i in l, Set.EqOn (uᵢ i) u C) :
    SuperjetGraph C u ⊆ TailClosureSuperjetGraph C uᵢ l := by
  intro z hz A hA
  have hlarge : A ∩ {i | Set.EqOn (uᵢ i) u C} ∈ l := inter_mem hA heq
  rcases Filter.nonempty_of_mem hlarge with ⟨i, hiA, hEq⟩
  rcases z with ⟨⟨x, r⟩, J⟩
  rcases hz with ⟨hxC, hr, hJ⟩
  change r = u x at hr
  subst r
  have hJi : J ∈ Superjet C (uᵢ i) x := by
    simpa [superjet_congr_eqOn hEq hxC] using hJ
  have hz_i : ((x, u x), J) ∈ SuperjetGraph C (uᵢ i) := by
    refine ⟨hxC, ?_, hJi⟩
    exact (hEq hxC).symm
  exact subset_closure (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hz_i⟩⟩)

/--
If the set of indices `i` for which `uᵢ i` agrees with `u` on `C` belongs to
`l`, then every subjet graph point of `u` belongs to the tail closure of the
approximating subjet graphs.
-/
theorem subjetGraph_subset_tailClosureSubjetGraph_of_eventually_eqOn
    {C : Set (Point n)} {u : Point n -> Real} {uᵢ : ι -> Point n -> Real}
    {l : Filter ι} [l.NeBot]
    (heq : ∀ᶠ i in l, Set.EqOn (uᵢ i) u C) :
    SubjetGraph C u ⊆ TailClosureSubjetGraph C uᵢ l := by
  intro z hz A hA
  have hlarge : A ∩ {i | Set.EqOn (uᵢ i) u C} ∈ l := inter_mem hA heq
  rcases Filter.nonempty_of_mem hlarge with ⟨i, hiA, hEq⟩
  rcases z with ⟨⟨x, r⟩, J⟩
  rcases hz with ⟨hxC, hr, hJ⟩
  change r = u x at hr
  subst r
  have hJi : J ∈ Subjet C (uᵢ i) x := by
    simpa [subjet_congr_eqOn hEq hxC] using hJ
  have hz_i : ((x, u x), J) ∈ SubjetGraph C (uᵢ i) := by
    refine ⟨hxC, ?_, hJi⟩
    exact (hEq hxC).symm
  exact subset_closure (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hz_i⟩⟩)

theorem tailClosureSuperjetGraph_induction
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {z : (Point n × Real) × Jet n} {S : Set ((Point n × Real) × Jet n)}
    (hclosed : IsClosed S)
    (hgraph : ∀ᶠ i in l, ∀ y : Point n, y ∈ C -> ∀ K : Jet n,
      K ∈ Superjet C (uᵢ i) y -> ((y, uᵢ i y), K) ∈ S)
    (hz : z ∈ TailClosureSuperjetGraph C uᵢ l) :
    z ∈ S := by
  let A : Set ι :=
    {i | ∀ y : Point n, y ∈ C -> ∀ K : Jet n,
      K ∈ Superjet C (uᵢ i) y -> ((y, uᵢ i y), K) ∈ S}
  have hA : A ∈ l := hgraph
  have hzclosure : z ∈ closure (⋃ i ∈ A, SuperjetGraph C (uᵢ i)) := hz A hA
  refine closure_minimal ?_ hclosed hzclosure
  intro w hw
  rcases Set.mem_iUnion.mp hw with ⟨i, hwi⟩
  rcases Set.mem_iUnion.mp hwi with ⟨hiA, hwgraph⟩
  rcases w with ⟨⟨y, r⟩, K⟩
  rcases hwgraph with ⟨hyC, hr, hK⟩
  change r = uᵢ i y at hr
  subst r
  exact hiA y hyC K hK

theorem tailClosureSubjetGraph_induction
    {C : Set (Point n)} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {z : (Point n × Real) × Jet n} {S : Set ((Point n × Real) × Jet n)}
    (hclosed : IsClosed S)
    (hgraph : ∀ᶠ i in l, ∀ y : Point n, y ∈ C -> ∀ K : Jet n,
      K ∈ Subjet C (uᵢ i) y -> ((y, uᵢ i y), K) ∈ S)
    (hz : z ∈ TailClosureSubjetGraph C uᵢ l) :
    z ∈ S := by
  let A : Set ι :=
    {i | ∀ y : Point n, y ∈ C -> ∀ K : Jet n,
      K ∈ Subjet C (uᵢ i) y -> ((y, uᵢ i y), K) ∈ S}
  have hA : A ∈ l := hgraph
  have hzclosure : z ∈ closure (⋃ i ∈ A, SubjetGraph C (uᵢ i)) := hz A hA
  refine closure_minimal ?_ hclosed hzclosure
  intro w hw
  rcases Set.mem_iUnion.mp hw with ⟨i, hwi⟩
  rcases Set.mem_iUnion.mp hwi with ⟨hiA, hwgraph⟩
  rcases w with ⟨⟨y, r⟩, K⟩
  rcases hwgraph with ⟨hyC, hr, hK⟩
  change r = uᵢ i y at hr
  subst r
  exact hiA y hyC K hK

/--
Abstract stability criterion for subsolutions. If every superjet of the limit
is in the tail closure of the approximating superjet graphs, then eventual
subsolutions pass to the limit for continuous operators.
-/
theorem ViscositySubsolution.of_eventually_tailClosureSuperjetGraph
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (husc : UpperSemicontinuousOn u C)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (happrox : ∀ x : Point n, x ∈ C -> ∀ J : Jet n, J ∈ Superjet C u x ->
      ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l) :
    ViscositySubsolution C F u := by
  refine ⟨husc, ?_⟩
  intro x hx J hJ
  have hz : ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l :=
    happrox x hx J hJ
  have hmem :
      ((x, u x), J) ∈
        {z : (Point n × Real) × Jet n | operatorGraphEval F z <= 0} := by
    refine tailClosureSuperjetGraph_induction hF.isClosed_le_zero ?_ hz
    filter_upwards [hsub] with i hi y hy K hK
    exact hi.2 y hy K hK
  simpa [operatorGraphEval] using hmem

/--
Abstract stability criterion for supersolutions. If every subjet of the limit
is in the tail closure of the approximating subjet graphs, then eventual
supersolutions pass to the limit for continuous operators.
-/
theorem ViscositySupersolution.of_eventually_tailClosureSubjetGraph
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hlsc : LowerSemicontinuousOn u C)
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (happrox : ∀ x : Point n, x ∈ C -> ∀ J : Jet n, J ∈ Subjet C u x ->
      ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l) :
    ViscositySupersolution C F u := by
  refine ⟨hlsc, ?_⟩
  intro x hx J hJ
  have hz : ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l :=
    happrox x hx J hJ
  have hmem :
      ((x, u x), J) ∈
        {z : (Point n × Real) × Jet n | 0 <= operatorGraphEval F z} := by
    refine tailClosureSubjetGraph_induction hF.isClosed_zero_le ?_ hz
    filter_upwards [hsuper] with i hi y hy K hK
    exact hi.2 y hy K hK
  simpa [operatorGraphEval] using hmem

/--
Pointwise closed-graph consequence for subsolutions. If the set of indices
`i` for which `uᵢ i` is a viscosity subsolution belongs to `l`, then any
tail-closure point of the approximating superjet graphs satisfies the
limiting operator inequality.
-/
theorem le_of_eventually_viscositySubsolution_tailClosureSuperjetGraph
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x : Point n} {J : Jet n}
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hz : ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l) :
    F x (u x) J.gradient J.hessian <= 0 := by
  have hmem :
      ((x, u x), J) ∈
        {z : (Point n × Real) × Jet n | operatorGraphEval F z <= 0} := by
    refine tailClosureSuperjetGraph_induction hF.isClosed_le_zero ?_ hz
    filter_upwards [hsub] with i hi y hy K hK
    exact hi.2 y hy K hK
  simpa [operatorGraphEval] using hmem

/--
Pointwise closed-graph consequence for supersolutions. If the set of indices
`i` for which `uᵢ i` is a viscosity supersolution belongs to `l`, then any
tail-closure point of the approximating subjet graphs satisfies the limiting
operator inequality.
-/
theorem nonneg_of_eventually_viscositySupersolution_tailClosureSubjetGraph
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    {x : Point n} {J : Jet n}
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (hz : ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l) :
    0 <= F x (u x) J.gradient J.hessian := by
  have hmem :
      ((x, u x), J) ∈
        {z : (Point n × Real) × Jet n | 0 <= operatorGraphEval F z} := by
    refine tailClosureSubjetGraph_induction hF.isClosed_zero_le ?_ hz
    filter_upwards [hsuper] with i hi y hy K hK
    exact hi.2 y hy K hK
  simpa [operatorGraphEval] using hmem

/--
If the set of indices `i` for which `uᵢ i` agrees with `u` on `C` belongs to
`l`, then the tail-closure approximation hypothesis holds. Consequently, if
the set of indices `i` for which `uᵢ i` is a subsolution belongs to `l`, then
`u` is a subsolution.
-/
theorem ViscositySubsolution.of_eventually_eqOn
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    (husc : UpperSemicontinuousOn u C)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (heq : ∀ᶠ i in l, Set.EqOn (uᵢ i) u C) :
    ViscositySubsolution C F u := by
  refine ViscositySubsolution.of_eventually_tailClosureSuperjetGraph husc hF hsub ?_
  intro x hx J hJ
  exact superjetGraph_subset_tailClosureSuperjetGraph_of_eventually_eqOn
    (C := C) (u := u) (uᵢ := uᵢ) (l := l) heq ⟨hx, rfl, hJ⟩

/--
If the set of indices `i` for which `uᵢ i` agrees with `u` on `C` belongs to
`l`, then the tail-closure approximation hypothesis holds. Consequently, if
the set of indices `i` for which `uᵢ i` is a supersolution belongs to `l`,
then `u` is a supersolution.
-/
theorem ViscositySupersolution.of_eventually_eqOn
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {l : Filter ι} [l.NeBot]
    (hlsc : LowerSemicontinuousOn u C)
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (heq : ∀ᶠ i in l, Set.EqOn (uᵢ i) u C) :
    ViscositySupersolution C F u := by
  refine ViscositySupersolution.of_eventually_tailClosureSubjetGraph hlsc hF hsuper ?_
  intro x hx J hJ
  exact subjetGraph_subset_tailClosureSubjetGraph_of_eventually_eqOn
    (C := C) (u := u) (uᵢ := uᵢ) (l := l) heq ⟨hx, rfl, hJ⟩

end ViscositySolns
