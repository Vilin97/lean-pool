/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.GonalityTransport
public import Mathlib.Tactic

/-!
# The occurrence presentation of a unit-length subdivision spec

`regularSubdivision G k` (`Utilities/Gonality/GonalityTransport.lean`) builds
`σ_k(G)` on the *occurrence presentation* of `G`, which labels vertices and edge
occurrences by arbitrary `Fintype.equivFin` bijections.  A graph that is already
given as `spec.graph` for a **unit-length** `spec : Spec n p` therefore has two
descriptions of `σ_k`, and this module shows they agree:

```
Nonempty (LaplacianEquiv (spec.scale k hk).graph (regularSubdivision spec.graph k hk))
```

The content is a slot correspondence.  `spec.graph.edges` is
`Multiset.map spec.unitEdge univ`, so its multiset-as-type
`(x : V × V) × Fin (count x)` is equivalent to `spec.Step` — compatibly with
`unitEdge`, which is the only property the endpoint conditions of a
`Spec.Relabeling` need.  With unit lengths `spec.Step ≃ Fin p` and
`spec.Vertex ≃ Fin n`, and the relabeling assembles.

The payoff is that the tricycle gap can be stated for
`regularSubdivisionGonality : CFGraph → ℕ`, with no `Spec` in the statement.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset

open Utilities.Gonality

variable {n p : ℕ}

/-! ## The multiset of edges, as a type -/

/-- **The slot correspondence.**  The edge multiset of a subdivision, viewed as
a type, enumerates the unit steps — compatibly with `unitEdge`. -/
noncomputable def stepEquivEdges (spec : Spec n p) :
    spec.Step ≃ (spec.graph.edges : Type) := by
  classical
  refine (Equiv.sigmaFiberEquiv spec.unitEdge).symm.trans
    (Equiv.sigmaCongrRight fun y => (Fintype.equivFin _).trans (finCongr ?_))
  show Fintype.card {step : spec.Step // spec.unitEdge step = y}
      = Multiset.count y spec.graph.edges
  rw [Fintype.card_subtype, graph_edges, Multiset.count_map, ← Finset.filter_val]
  show Finset.card _ = Finset.card _
  exact congrArg Finset.card (Finset.filter_congr fun step _ => by simp [eq_comm])

@[simp] theorem stepEquivEdges_coe (spec : Spec n p) (step : spec.Step) :
    ((stepEquivEdges spec step : (spec.graph.edges : Type)) : spec.Vertex × spec.Vertex)
      = spec.unitEdge step := rfl

/-! ## Unit-length specs -/

variable (spec : Spec n p) (hlen : ∀ e : Fin p, spec.length e = 1)

/-- With all lengths one there are no interior vertices. -/
def unitVertexEquiv : Fin n ≃ spec.Vertex where
  toFun := spec.coreVertex
  invFun := Sum.elim id fun y => absurd y.2.isLt (by have := hlen y.1; omega)
  left_inv := fun _ => rfl
  right_inv := by
    rintro (v | ⟨e, j⟩)
    · rfl
    · exact absurd j.isLt (by have := hlen e; omega)

@[simp] theorem unitVertexEquiv_apply (v : Fin n) :
    unitVertexEquiv spec hlen v = spec.coreVertex v := rfl

/-- With all lengths one, every slot has exactly one unit step. -/
def unitStepEquiv : Fin p ≃ spec.Step where
  toFun := fun e => ⟨e, ⟨0, by rw [hlen e]; omega⟩⟩
  invFun := fun step => step.1
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨e, ⟨j, hj⟩⟩
    have hj0 : j = 0 := by have := hlen e; omega
    subst hj0
    rfl

theorem unitEdge_unitStepEquiv (e : Fin p) :
    spec.unitEdge (unitStepEquiv spec hlen e) =
      (spec.coreVertex (spec.core.tail e), spec.coreVertex (spec.core.head e)) := by
  refine Prod.ext ?_ ?_
  · show spec.stepLeft e ⟨0, spec.length_pos e⟩ = _
    exact spec.stepLeft_zero e
  · show spec.stepRight e ⟨0, spec.length_pos e⟩ = _
    rw [show (⟨0, spec.length_pos e⟩ : Fin (spec.length e))
        = ⟨spec.length e - 1, by have := spec.length_pos e; omega⟩ from
      Fin.ext (by have := hlen e; omega)]
    exact spec.stepRight_last e

/-! ## The relabeling -/

/-- The vertex labelling used by the occurrence presentation, restricted to the
core vertices. -/
noncomputable def unitCoreEquiv : Fin n ≃ Fin (Fintype.card spec.graph.V) :=
  (unitVertexEquiv spec hlen).trans (UnitSubdivisionPresentation.vertexEquiv spec.graph)

/-- The slot labelling used by the occurrence presentation. -/
noncomputable def unitSlotEquiv : Fin p ≃ Fin spec.graph.edges.card :=
  ((unitStepEquiv spec hlen).trans (stepEquivEdges spec)).trans
    (UnitSubdivisionPresentation.edgeEquiv spec.graph)

theorem edgeAt_unitSlotEquiv (e : Fin p) :
    UnitSubdivisionPresentation.edgeAt spec.graph (unitSlotEquiv spec hlen e) =
      (spec.coreVertex (spec.core.tail e), spec.coreVertex (spec.core.head e)) := by
  unfold UnitSubdivisionPresentation.edgeAt UnitSubdivisionPresentation.edgeOccurrence
    unitSlotEquiv
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [stepEquivEdges_coe]
  exact unitEdge_unitStepEquiv spec hlen e

/-- **The two presentations of `σ_k` agree.** -/
noncomputable def scaleRelabeling (k : ℕ) (hk : 0 < k) :
    (spec.scale k hk).Relabeling
      ((UnitSubdivisionPresentation.spec spec.graph).scale k hk) where
  coreEquiv := unitCoreEquiv spec hlen
  slotEquiv := unitSlotEquiv spec hlen
  reversed := fun _ => false
  length_eq := by
    intro e
    show k * spec.length e = k * 1
    rw [hlen e]
  tail_eq := by
    intro e
    show UnitSubdivisionPresentation.vertexEquiv spec.graph
        (UnitSubdivisionPresentation.edgeAt spec.graph (unitSlotEquiv spec hlen e)).1
      = _
    rw [edgeAt_unitSlotEquiv spec hlen e]
    simp [unitCoreEquiv]
  head_eq := by
    intro e
    show UnitSubdivisionPresentation.vertexEquiv spec.graph
        (UnitSubdivisionPresentation.edgeAt spec.graph (unitSlotEquiv spec hlen e)).2
      = _
    rw [edgeAt_unitSlotEquiv spec hlen e]
    simp [unitCoreEquiv]

/-- **The bridge.**  For a unit-length subdivision specification, scaling the
specification by `k` and building `σ_k` on the occurrence presentation of its
graph give the same graph up to Laplacian equivalence. -/
noncomputable def scaleLaplacianEquiv (k : ℕ) (hk : 0 < k) :
    LaplacianEquiv (spec.scale k hk).graph (regularSubdivision spec.graph k hk) :=
  Spec.laplacianEquiv _ _ (scaleRelabeling spec hlen k hk)

theorem divisorialGonality_regularSubdivision (spec : Spec n p)
    (hlen : ∀ e : Fin p, spec.length e = 1) (k : ℕ) (hk : 0 < k) :
    divisorialGonality (regularSubdivision spec.graph k hk)
      = divisorialGonality (spec.scale k hk).graph :=
  (divisorialGonality_of_laplacianEquiv (scaleLaplacianEquiv spec hlen k hk)).symm

/-- The `CFGraph`-level invariant agrees with the `Spec`-level one on a
unit-length specification. -/
theorem regularSubdivisionGonality_graph (spec : Spec n p)
    (hlen : ∀ e : Fin p, spec.length e = 1) :
    Utilities.Gonality.regularSubdivisionGonality spec.graph
      = spec.regularSubdivisionGonality := by
  unfold Utilities.Gonality.regularSubdivisionGonality
    Spec.regularSubdivisionGonality
  congr 1
  ext d
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (divisorialGonality_regularSubdivision spec hlen k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, divisorialGonality_regularSubdivision spec hlen k hk⟩

end Utilities.Certificate.SubdivisionGraph.Spec
