/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge

/-!
# The loop graph, evaluated

The accompanying paper's worked example of Definition 2.1 (§2.4),
carried out in the flag model.  With `k = 2` and `ℓ = 1`, the
functional
`h(θ)` of `charPolyFunctional` has `p_{h(θ)}` equal to the
characteristic polynomial `G ↦ det(θ I − A_G)` on graphs without
free circles (Regts–Sevenster, arXiv:1807.04494, Proposition 10),
and the graph `L` with one vertex and one loop has `A_L = (2)`.
So `p_{h(θ)}(L)` must be `θ − 2`, and
`mixedPartition_loopGraph` is that evaluation.

The example is a convention check.  Reaching `θ − 2` exercises, in
one number, the two incidences of a loop at its vertex, the
Eulerian condition, the circuit sign, the distinction between a
loop and a free circle, and the `η`-convention that makes the two
odd colourings contribute through a common basis vector.  A sign
error in any one of them changes the answer.
-/

@[expose] public section

namespace RS

/-! ### The graph -/

/-- **The loop graph** `L`: one vertex, one edge, both of whose
flags are attached to that vertex.  No boundary labels, and no free
circles — the loop is an edge, not a circle. -/
def loopGraph : ClosedFragment where
  Flag := Bool
  Vertex := Unit
  attach := fun _ => Sum.inl ()
  pairing := not
  pairing_invol := Bool.not_not
  pairing_ne := by decide
  boundaryFlag := fun i => i.elim0
  attach_boundaryFlag := fun i => i.elim0
  eq_boundaryFlag := fun i => i.elim0
  circles := 0

/-! ### The functional -/

/-- **The paper's example functional** `h(θ)`, with `k = 2` and
`ℓ = 1`.  On the paper's basis it is
`h(e₁^⊙i) = θ`, `h(e₁^⊙i ⊙ e₂) = √-1`,
`h(e₁^⊙i ⊗ ξ₁ ∧ η₁) = 1`, and zero elsewhere.

The odd value carried here is the coefficient on the *sorted* wedge
`ξ₁ ∧ ξ₂`, which is `−1`: the symplectic partner of `ξ₁` is
`η₁ = −ξ₂`, so `ξ₁ ∧ η₁ = −ξ₁ ∧ ξ₂`. These are the partner
conventions of the paper's §2.4, and the two odd colourings each
contribute `−1` below. -/
def charPolyFunctional (θ : ℂ) : MixedFunctional 2 1 := fun μ w =>
  if μ.count 1 = 0 then
    (if w = ∅ then θ else if w = Finset.univ then -1 else 0)
  else if μ.count 1 = 1 ∧ w = ∅ then Complex.I
  else 0

/-! ### The two Eulerian subsets

The loop has two half-edges at its vertex, so both the empty subset
and the whole loop are Eulerian, and no other flag set is closed
under the edge pairing. -/

/-- The empty flag set is closed under the edge pairing. -/
private theorem loopEmpty_closed :
    ∀ f ∈ (∅ : Finset loopGraph.Flag),
      loopGraph.pairing f ∈ (∅ : Finset loopGraph.Flag) :=
  fun f hf => absurd hf (Finset.notMem_empty f)

/-- So is the whole flag set. -/
private theorem loopFull_closed :
    ∀ f ∈ (Finset.univ : Finset loopGraph.Flag),
      loopGraph.pairing f ∈ (Finset.univ : Finset loopGraph.Flag) :=
  fun _ _ => Finset.mem_univ _

/-- The empty edge subset. -/
private def loopEmpty : EdgeSubset loopGraph := ⟨∅, loopEmpty_closed⟩

/-- The edge subset in which the loop participates. -/
private def loopFull : EdgeSubset loopGraph :=
  ⟨Finset.univ, loopFull_closed⟩

/-- The vacuous transition system on the empty subset. -/
private def loopEmptyTransition : loopEmpty.TransitionSystem where
  match_ := id
  match_invol := fun f hf => absurd hf (Finset.notMem_empty f)
  match_ne := fun f hf => absurd hf (Finset.notMem_empty f)
  match_mem := fun f hf => absurd hf (Finset.notMem_empty f)
  match_vertex := fun f hf => absurd hf (Finset.notMem_empty f)
  attach_internal := fun f hf => absurd hf (Finset.notMem_empty f)

/-- The vacuous orientation on the empty subset. -/
private def loopEmptyOrientation : loopEmptyTransition.Orientation where
  isOut := fun _ => false
  match_flip := fun f hf => absurd hf (Finset.notMem_empty f)
  pairing_flip := fun f hf => absurd hf (Finset.notMem_empty f)

/-- The transition system `κ_v` on the participating loop: the two
half-edges at the vertex are matched to each other. -/
private def loopFullTransition : loopFull.TransitionSystem where
  match_ := not
  match_invol := fun f _ => Bool.not_not f
  match_ne := fun f _ => by cases f <;> intro h <;> cases h
  match_mem := fun f _ => Finset.mem_univ _
  match_vertex := fun _ _ _ hv => hv
  attach_internal := fun _ _ => ⟨(), rfl⟩

/-- The orientation with `false` the incoming end of the loop. -/
private def loopFullOrientation : loopFullTransition.Orientation where
  isOut := id
  match_flip := fun _ _ => rfl
  pairing_flip := fun _ _ => rfl

/-! ### Circuit counts -/

/-- Nothing participates, so there are no circuits. -/
private theorem circuitCount_loopEmpty :
    loopEmptyTransition.circuitCount = 0 := by
  have : IsEmpty {f : loopGraph.Flag // f ∈ loopEmpty.flags} :=
    ⟨fun f => absurd f.prop (Finset.notMem_empty f.val)⟩
  unfold EdgeSubset.TransitionSystem.circuitCount
  rw [Subsingleton.elim loopEmptyTransition.walkPerm 1,
    Equiv.Perm.cycleType_one]
  simp

/-- The participating loop is a single circuit.  Its walk map
`f ↦ κ(σ(f))` is the identity, because the edge pairing and the
vertex matching are the same involution here; a one-edge circuit
therefore appears as two walk fixed points, which is what the
halving in `circuitCount` is for. -/
private theorem circuitCount_loopFull :
    loopFullTransition.circuitCount = 1 := by
  have hwalk : loopFullTransition.walkPerm = 1 :=
    Equiv.ext fun f => Subtype.ext (Bool.not_not f.val)
  have hcard :
      Fintype.card {f : loopGraph.Flag // f ∈ loopFull.flags} = 2 :=
    (Fintype.card_congr
      (Equiv.subtypeUnivEquiv fun f => Finset.mem_univ f)).trans
      (Fintype.card_bool)
  have hfix : Fintype.card
      ↥(Function.fixedPoints
        (⇑(1 : Equiv.Perm
          {f : loopGraph.Flag // f ∈ loopFull.flags}))) = 2 :=
    (Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)).trans hcard
  unfold EdgeSubset.TransitionSystem.circuitCount
  rw [hwalk, Equiv.Perm.cycleType_one, hfix]
  simp

/-! ### The colourings -/

/-- Even colourings of the loop, when nothing participates: a
single colour, constant along the edge. -/
private def loopEmptyEvenEquiv : loopEmpty.EvenColouring 2 ≃ Fin 2 where
  toFun ψ := ψ.val ⟨false, Finset.notMem_empty _⟩
  invFun c := ⟨fun _ => c, fun _ => rfl⟩
  left_inv ψ := Subtype.ext (funext fun f => by
    obtain ⟨f, hf⟩ := f
    cases f with
    | false => rfl
    | true => exact (ψ.prop ⟨false, Finset.notMem_empty _⟩).symm)
  right_inv _ := rfl

/-- Odd colourings of the participating loop: a single odd colour,
constant along the edge. -/
private def loopFullOddEquiv : loopFull.OddColouring 1 ≃ Fin 2 where
  toFun φ := φ.val ⟨false, Finset.mem_univ _⟩
  invFun c := ⟨fun _ => c, fun _ => rfl⟩
  left_inv φ := Subtype.ext (funext fun f => by
    obtain ⟨f, hf⟩ := f
    cases f with
    | false => rfl
    | true => exact (φ.prop ⟨false, Finset.mem_univ _⟩).symm)
  right_inv _ := rfl

/-- No flag participates, so the odd colouring is unique. -/
private instance : Subsingleton (loopEmpty.OddColouring 1) :=
  ⟨fun _ _ => Subtype.ext (funext fun f =>
    absurd f.prop (Finset.notMem_empty f.val))⟩

/-- Every flag participates, so the even colouring is unique. -/
private instance : Subsingleton (loopFull.EvenColouring 2) :=
  ⟨fun _ _ => Subtype.ext (funext fun f =>
    absurd (Finset.mem_univ f.val) f.prop)⟩

/-- An even colouring of the unparticipating loop takes one value. -/
private theorem loopEmptyEven_const (ψ : loopEmpty.EvenColouring 2)
    (f : {f : loopGraph.Flag // f ∉ loopEmpty.flags}) :
    ψ.val f = loopEmptyEvenEquiv ψ :=
  (congrFun (congrArg Subtype.val
    (loopEmptyEvenEquiv.symm_apply_apply ψ)) f).symm

/-- An odd colouring of the participating loop takes one value. -/
private theorem loopFullOdd_const (φ : loopFull.OddColouring 1)
    (f : {f : loopGraph.Flag // f ∈ loopFull.flags}) :
    φ.val f = loopFullOddEquiv φ :=
  (congrFun (congrArg Subtype.val
    (loopFullOddEquiv.symm_apply_apply φ)) f).symm

/-! ### Small facts about the graph -/

/-- The loop has a single vertex. -/
private instance : Unique loopGraph.Vertex :=
  inferInstanceAs (Unique Unit)

/-- Every flag of the loop is attached to its vertex. -/
private theorem loopGraph_attach (f : loopGraph.Flag)
    (v : loopGraph.Vertex) : loopGraph.attach f = Sum.inl v :=
  congrArg Sum.inl (Subsingleton.elim _ _)

/-- The unique odd colouring when nothing participates. -/
private def loopEmptyOdd : loopEmpty.OddColouring 1 :=
  ⟨fun f => absurd f.prop (Finset.notMem_empty f.val),
   fun f => absurd f.prop (Finset.notMem_empty f.val)⟩

/-- The unique even colouring when the whole loop participates. -/
private def loopFullEven : loopFull.EvenColouring 2 :=
  ⟨fun f => absurd (Finset.mem_univ f.val) f.prop,
   fun f => absurd (Finset.mem_univ f.val) f.prop⟩

/-- The half-edge of the loop that the orientation makes
incoming. -/
private def loopIn : loopGraph.Flag := false

/-! ### The Eulerian condition -/

/-- The empty subset is Eulerian: every vertex has degree zero. -/
private theorem eulerian_loopEmpty : loopEmpty.Eulerian := by
  intro v
  have hdeg : loopEmpty.deg v = 0 := by
    unfold EdgeSubset.deg
    rw [show loopEmpty.flags = ∅ from rfl, Finset.filter_empty,
      Finset.card_empty]
  rw [hdeg]
  exact ⟨0, rfl⟩

/-- The whole loop is Eulerian: its two half-edges meet the single
vertex, which therefore has degree two. -/
private theorem eulerian_loopFull : loopFull.Eulerian := by
  intro v
  let := Classical.decEq (loopGraph.Vertex ⊕ Fin 0)
  have hdeg : loopFull.deg v = 2 := by
    unfold EdgeSubset.deg
    rw [Finset.filter_true_of_mem (fun f _ => loopGraph_attach f v),
      show loopFull.flags = Finset.univ from rfl, Finset.card_univ]
    exact Fintype.card_bool
  rw [hdeg]
  exact ⟨1, rfl⟩

/-! ### The value of the empty subset

Nothing participates, so there is no odd sector and no circuit
sign.  The loop's two colourings contribute `h(e₁ ⊙ e₁) = θ` and
`h(e₂ ⊙ e₂) = 0`. -/

open Classical in
/-- The even colours at the vertex are the colour of the loop,
counted once for each of its two incidences. -/
private theorem evenColoursAt_loopEmpty (ψ : loopEmpty.EvenColouring 2)
    (v : loopGraph.Vertex) :
    loopEmpty.evenColoursAt ψ v =
      Multiset.replicate 2 (loopEmptyEvenEquiv ψ) := by
  have hcard :
      Fintype.card {f : loopGraph.Flag // f ∉ loopEmpty.flags} = 2 :=
    (Fintype.card_congr (Equiv.subtypeUnivEquiv
      fun f => Finset.notMem_empty f)).trans Fintype.card_bool
  unfold EdgeSubset.evenColoursAt
  rw [Finset.filter_true_of_mem (fun f _ => loopGraph_attach f.val v),
    Multiset.map_congr rfl (fun f _ => loopEmptyEven_const ψ f),
    Multiset.map_const',
    show Multiset.card (Finset.univ :
        Finset {f : loopGraph.Flag // f ∉ loopEmpty.flags}).val =
      Fintype.card {f : loopGraph.Flag // f ∉ loopEmpty.flags} from rfl,
    hcard]

/-- No flag participates, so no flag is incoming. -/
private theorem inFlagsAt_loopEmpty (v : loopGraph.Vertex) :
    loopEmpty.inFlagsAt loopEmptyOrientation v = [] := by
  let := loopGraph.flagOrder
  let := Classical.dec
  unfold EdgeSubset.inFlagsAt
  rw [show loopEmpty.flags = ∅ from rfl, Finset.filter_empty,
    Finset.sort_empty]

/-- With nothing incoming there is no odd list. -/
private theorem oddListAt_loopEmpty (φ : loopEmpty.OddColouring 1)
    (v : loopGraph.Vertex) :
    loopEmpty.oddListAt loopEmptyOrientation φ v = [] := by
  unfold EdgeSubset.oddListAt
  simp [inFlagsAt_loopEmpty]

/-- With nothing incoming there is no odd sign. -/
private theorem oddSignAt_loopEmpty (φ : loopEmpty.OddColouring 1)
    (v : loopGraph.Vertex) :
    loopEmpty.oddSignAt loopEmptyOrientation φ v = 1 := by
  unfold EdgeSubset.oddSignAt
  simp [inFlagsAt_loopEmpty]

/-- The vertex value at a colouring of the unparticipating loop. -/
private noncomputable def loopEmptyTerm (θ : ℂ) (c : Fin 2) : ℂ :=
  charPolyFunctional θ (Multiset.replicate 2 c) ∅

/-- Colouring the loop `e₁` gives `h(e₁ ⊙ e₁) = θ`. -/
private theorem loopEmptyTerm_zero (θ : ℂ) : loopEmptyTerm θ 0 = θ := by
  unfold loopEmptyTerm charPolyFunctional
  norm_num [Multiset.count_replicate]

/-- Colouring the loop `e₂` gives `h(e₂ ⊙ e₂) = 0`. -/
private theorem loopEmptyTerm_one (θ : ℂ) : loopEmptyTerm θ 1 = 0 := by
  unfold loopEmptyTerm charPolyFunctional
  norm_num [Multiset.count_replicate]

/-- **The empty subset contributes `θ`.** -/
private theorem mixedValue_loopEmpty (θ : ℂ) :
    loopEmpty.mixedValue (charPolyFunctional θ) = θ := by
  rw [EdgeSubset.mixedValue_eq_summand_open loopEmpty _
    loopEmptyOrientation]
  unfold EdgeSubset.mixedSummand
  rw [circuitCount_loopEmpty, pow_zero, one_mul,
    Fintype.sum_equiv loopEmptyEvenEquiv _ (loopEmptyTerm θ)
      (fun ψ => ?_)]
  · rw [Fin.sum_univ_two, loopEmptyTerm_zero, loopEmptyTerm_one, add_zero]
  · rw [Fintype.sum_subsingleton _ loopEmptyOdd, Fintype.prod_unique,
      oddSignAt_loopEmpty, oddListAt_loopEmpty, evenColoursAt_loopEmpty]
    simp [MixedFunctional.evalOdd, loopEmptyTerm, sortSign, inversions]

/-! ### The value of the participating loop

The loop's two half-edges are matched to each other, so they form a
single κ-circuit and the summand carries the sign `(−1)¹`.  There
are no even colours left, and the two odd colourings contribute
through the same basis vector of `Λ²V₁`. -/

/-- Exactly one half-edge of the loop is the incoming end. -/
private theorem inFlagsAt_loopFull (v : loopGraph.Vertex) :
    loopFull.inFlagsAt loopFullOrientation v = [loopIn] := by
  let := loopGraph.flagOrder
  let := Classical.dec
  have hfilter : Finset.filter
      (fun f => loopGraph.attach f = Sum.inl v ∧
        loopFullOrientation.isOut f = false) loopFull.flags =
      {loopIn} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton,
      show loopFull.flags = Finset.univ from rfl, Finset.mem_univ,
      true_and]
    change (loopGraph.attach f = Sum.inl v ∧ f = loopIn) ↔ f = loopIn
    exact ⟨fun h => h.2, fun h => ⟨loopGraph_attach f v, h⟩⟩
  unfold EdgeSubset.inFlagsAt
  rw [hfilter, Finset.sort_singleton]

/-- The odd list at the vertex: the incoming colour followed by the
partner index of the outgoing colour. -/
private theorem oddListAt_loopFull (φ : loopFull.OddColouring 1)
    (v : loopGraph.Vertex) :
    loopFull.oddListAt loopFullOrientation φ v =
      [loopFullOddEquiv φ, oddPartner 1 (loopFullOddEquiv φ)] := by
  unfold EdgeSubset.oddListAt
  simp [inFlagsAt_loopFull, EdgeSubset.oddPairFn, loopFullOdd_const,
    List.flatMap_cons, List.flatMap_nil]

/-- The odd sign at the vertex is the partner sign of the outgoing
colour. -/
private theorem oddSignAt_loopFull (φ : loopFull.OddColouring 1)
    (v : loopGraph.Vertex) :
    loopFull.oddSignAt loopFullOrientation φ v =
      oddPartnerSign 1 (loopFullOddEquiv φ) := by
  unfold EdgeSubset.oddSignAt
  simp [inFlagsAt_loopFull, EdgeSubset.oddSignFn, loopFullOdd_const]

open Classical in
/-- Both half-edges participate, so no even colour survives. -/
private theorem evenColoursAt_loopFull (ψ : loopFull.EvenColouring 2)
    (v : loopGraph.Vertex) : loopFull.evenColoursAt ψ v = 0 := by
  have : IsEmpty {f : loopGraph.Flag // f ∉ loopFull.flags} :=
    ⟨fun f => absurd (Finset.mem_univ f.val) f.prop⟩
  unfold EdgeSubset.evenColoursAt
  rw [Finset.univ_eq_empty, Finset.filter_empty]
  rfl

/-- The vertex value at an odd colouring of the participating
loop. -/
private noncomputable def loopFullTerm (θ : ℂ) (c : Fin 2) : ℂ :=
  (oddPartnerSign 1 c : ℂ) *
    (charPolyFunctional θ).evalOdd 0 [c, oddPartner 1 c]

/-- The colouring `ξ₁` contributes `1`: the partner sign is `−1`
and the wedge is already sorted, so the functional's `−1` is
recovered. -/
private theorem loopFullTerm_zero (θ : ℂ) : loopFullTerm θ 0 = 1 := by
  have huniv : (Finset.univ : Finset (Fin 2)) ≠ ∅ := by decide
  unfold loopFullTerm charPolyFunctional MixedFunctional.evalOdd
  norm_num [oddPartner, oddPartnerSign, sortSign, inversions, huniv,
    show ([0, 1] : List (Fin 2)).toFinset = Finset.univ from by decide]

/-- The colouring `ξ₂` contributes `1` as well: the partner sign is
`+1` and the wedge is reversed, so the two odd colourings agree. -/
private theorem loopFullTerm_one (θ : ℂ) : loopFullTerm θ 1 = 1 := by
  have huniv : (Finset.univ : Finset (Fin 2)) ≠ ∅ := by decide
  unfold loopFullTerm charPolyFunctional MixedFunctional.evalOdd
  norm_num [oddPartner, oddPartnerSign, sortSign, inversions, huniv,
    show ([1, 0] : List (Fin 2)).toFinset = Finset.univ from by decide]

/-- **The participating loop contributes `−2`**: two odd colourings,
each worth `1`, against the sign of the single κ-circuit. -/
private theorem mixedValue_loopFull (θ : ℂ) :
    loopFull.mixedValue (charPolyFunctional θ) = -2 := by
  rw [EdgeSubset.mixedValue_eq_summand_open loopFull _ loopFullOrientation]
  unfold EdgeSubset.mixedSummand
  rw [circuitCount_loopFull, pow_one,
    Fintype.sum_subsingleton _ loopFullEven,
    Fintype.sum_equiv loopFullOddEquiv _ (loopFullTerm θ) (fun φ => ?_)]
  · rw [Fin.sum_univ_two, loopFullTerm_zero, loopFullTerm_one]
    norm_num
  · rw [Fintype.prod_unique, oddSignAt_loopFull, oddListAt_loopFull,
      evenColoursAt_loopFull]
    rfl

/-! ### The evaluation -/

/-- No other flag set is closed under the edge pairing: the loop's
two half-edges are each other's partners, so a subset containing one
contains the other. -/
private theorem loop_pairing_not_closed :
    ∀ s : Finset loopGraph.Flag, s ≠ ∅ → s ≠ Finset.univ →
      ¬ ∀ f ∈ s, loopGraph.pairing f ∈ s := by
  decide

/-- The two Eulerian subsets are distinct. -/
private theorem loop_empty_ne_univ :
    (∅ : Finset loopGraph.Flag) ≠ Finset.univ := by
  decide

open Classical in
/-- **The paper's worked example**: the mixed partition function of
the functional `h(θ)` evaluates on the loop graph `L` to `θ − 2`,
the characteristic polynomial `det(θ I − A_L)` of its adjacency
matrix `A_L = (2)`.

The two Eulerian subsets contribute `θ` and `−2` respectively.  The
free-circle factor `(k − 2ℓ)^circles` is `0 ^ 0 = 1`: the loop is an
edge, not a free circle, and had it been one the value would have
been `0`. -/
theorem mixedPartition_loopGraph (θ : ℂ) :
    mixedPartition (charPolyFunctional θ) loopGraph = θ - 2 := by
  unfold mixedPartition
  rw [show loopGraph.circles = 0 from rfl, pow_zero, one_mul,
    ← Finset.sum_subset (Finset.subset_univ
        ({∅, Finset.univ} : Finset (Finset loopGraph.Flag)))
      (fun x _ hx => dite_eq_right (loop_pairing_not_closed x
        (fun h => hx (by rw [h]; exact Finset.mem_insert_self _ _))
        (fun h => hx (by
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))),
    Finset.sum_pair loop_empty_ne_univ,
    dite_eq_left loopEmpty_closed, dite_eq_left loopFull_closed]
  change (if loopEmpty.Eulerian then
        loopEmpty.mixedValue (charPolyFunctional θ) else 0) +
      (if loopFull.Eulerian then
        loopFull.mixedValue (charPolyFunctional θ) else 0) = θ - 2
  rw [ite_eq_left eulerian_loopEmpty, ite_eq_left eulerian_loopFull,
    mixedValue_loopEmpty, mixedValue_loopFull]
  ring

/-- The loop graph with a free circle adjoined. -/
def loopGraphCircle : ClosedFragment := { loopGraph with circles := 1 }

/-- **A free circle annihilates.**  Here `k − 2ℓ = 0`, so the paper's
`(k − 2ℓ)^circles` convention makes `p_{h(θ)}` vanish on every graph
carrying a free circle.  Set beside `mixedPartition_loopGraph`, this
is the loop/free-circle distinction as a pair of numbers: the same
one-vertex graph is worth `θ − 2` when its edge is a loop and `0`
when a circle rides alongside. -/
theorem mixedPartition_loopGraphCircle (θ : ℂ) :
    mixedPartition (charPolyFunctional θ) loopGraphCircle = 0 := by
  unfold mixedPartition
  rw [show loopGraphCircle.circles = 1 from rfl]
  norm_num

end RS
