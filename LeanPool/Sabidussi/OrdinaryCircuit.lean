/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import LeanPool.Sabidussi.LoopGraphBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Ordinary circuits in endpoint multigraphs

This file relates the binary ``minimal even edge set`` notion used by the colouring proof to
the usual graph-theoretic notion of a circuit.  Connectivity below is phrased directly in terms
of chains of incident labelled edges; in particular it does not mention parity or minimality.
Loops and parallel edges need no exceptional representation.
-/

namespace Sabidussi
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

omit [DecidableEq E] in
@[simp]
theorem mem_edgeSupport_iff {F : Finset E} {v : V} :
    v ∈ G.edgeSupport F ↔ ∃ e ∈ F, ∃ i : Fin 2, G.endAt e i = v := by
  simp [edgeSupport]

omit [DecidableEq E] in
private theorem degreeIn_eq_sum_indicator (F : Finset E) (v : V) :
    G.degreeIn F v = ∑ e ∈ F, ∑ i : Fin 2, if G.endAt e i = v then 1 else 0 := by
  simp only [degreeIn, Finset.card_filter, Finset.sum_product]

omit [DecidableEq E] in
theorem degreeIn_cast (F : Finset E) (v : V) :
    (G.degreeIn F v : F₂) = ∑ e ∈ F, G.edgeIncidence v e := by
  rw [G.degreeIn_eq_sum_indicator]
  simp only [edgeIncidence, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr with e
  rw [Fin.sum_univ_two]

omit [DecidableEq E] in
theorem isEvenEdgeSet_iff_even_degree (F : Finset E) :
    G.IsEvenEdgeSet F ↔ ∀ v : V, Even (G.degreeIn F v) := by
  constructor
  · intro h v
    rw [← ZMod.natCast_eq_zero_iff_even, G.degreeIn_cast]
    exact h v
  · intro h v
    rw [← G.degreeIn_cast, ZMod.natCast_eq_zero_iff_even]
    exact h v

omit [DecidableEq E] in
theorem degreeIn_pos_iff_mem_edgeSupport (F : Finset E) (v : V) :
    0 < G.degreeIn F v ↔ v ∈ G.edgeSupport F := by
  rw [degreeIn, Finset.card_pos, G.mem_edgeSupport_iff]
  constructor
  · rintro ⟨⟨e, i⟩, hh⟩
    have hh' := Finset.mem_filter.mp hh
    have heF : e ∈ F := (Finset.mem_product.mp hh'.1).1
    have hend : G.endAt e i = v := hh'.2
    exact ⟨e, heF, i, hend⟩
  · rintro ⟨e, heF, i, hend⟩
    refine ⟨⟨e, i⟩, Finset.mem_filter.mpr ⟨?_, hend⟩⟩
    exact Finset.mem_product.mpr ⟨heF, Finset.mem_univ i⟩

omit [DecidableEq E] in
/-- The degree-sum formula, valid without excluding loops: each labelled edge has exactly two
numbered ends. -/
theorem sum_degreeIn (F : Finset E) :
    ∑ v : V, G.degreeIn F v = 2 * F.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun h : E × Fin 2 ↦ G.endAt h.1 h.2)
    (s := F ×ˢ (Finset.univ : Finset (Fin 2))) (t := Finset.univ) (by simp)
  simpa only [degreeIn, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Nat.mul_comm] using h.symm

omit [DecidableEq E] in
private theorem incident_of_edgeIncidence_ne_zero {v : V} {e : E}
    (h : G.edgeIncidence v e ≠ 0) : ∃ i : Fin 2, G.endAt e i = v := by
  by_contra hn
  push Not at hn
  simp [edgeIncidence, hn] at h

omit [DecidableEq E] [DecidableEq V] in
private theorem adjacent_of_incident {d e : E} {v : V} {i j : Fin 2}
    (hd : G.endAt d i = v) (he : G.endAt e j = v) : G.EdgeAdjacent d e := by
  exact ⟨i, j, hd.trans he.symm⟩

omit [DecidableEq E] in
/-- Inclusion-minimal even edge sets are connected in the ordinary edge-chain sense. -/
theorem Cycle.edgeConnected (C : G.Cycle) : G.EdgeConnected C.edges := by
  classical
  obtain ⟨root, hroot⟩ := C.nonempty
  let R : E → E → Prop := fun x y ↦
    x ∈ C.edges ∧ y ∈ C.edges ∧ G.EdgeAdjacent x y
  let D : Finset E := C.edges.filter fun e ↦ Relation.ReflTransGen R root e
  have hrootD : root ∈ D := by
    exact Finset.mem_filter.mpr ⟨hroot, Relation.ReflTransGen.refl⟩
  have hDne : D.Nonempty := ⟨root, hrootD⟩
  have hDsub : D ⊆ C.edges := Finset.filter_subset _ _
  have hDeven : G.IsEvenEdgeSet D := by
    intro v
    by_cases hincident : ∃ d ∈ D, ∃ i : Fin 2, G.endAt d i = v
    · rw [← C.even v]
      apply Finset.sum_subset hDsub
      intro e heF heD
      by_contra hinc
      obtain ⟨j, hej⟩ := G.incident_of_edgeIncidence_ne_zero hinc
      obtain ⟨d, hdD, i, hdi⟩ := hincident
      have hdmem := (Finset.mem_filter.mp hdD).1
      have hdreach := (Finset.mem_filter.mp hdD).2
      have hstep : R d e :=
        ⟨hdmem, heF, G.adjacent_of_incident hdi hej⟩
      have hereach : Relation.ReflTransGen R root e := hdreach.tail hstep
      exact heD (Finset.mem_filter.mpr ⟨heF, hereach⟩)
    · apply Finset.sum_eq_zero
      intro e heD
      have hnend : ∀ i : Fin 2, G.endAt e i ≠ v := by
        intro i hi
        exact hincident ⟨e, heD, i, hi⟩
      simp [edgeIncidence, hnend]
  have hDF : D = C.edges := C.minimal D hDne hDsub hDeven
  refine ⟨root, hroot, ?_⟩
  intro e heF
  have heD : e ∈ D := hDF.symm ▸ heF
  exact (Finset.mem_filter.mp heD).2

private theorem F₂_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The vertex-edge incidence matrix of an edge set, with rows restricted to its support. -/
noncomputable def incidenceMatrix (F : Finset E) :
    Matrix (↑(G.edgeSupport F)) (↑F) F₂ :=
  fun v e ↦ G.edgeIncidence v.1 e.1

/-- The incidence matrix as a linear map over `F₂`. -/
noncomputable def incidenceMap (F : Finset E) :
    (↑F → F₂) →ₗ[F₂] (↑(G.edgeSupport F) → F₂) :=
  (G.incidenceMatrix F).mulVecLin

omit [DecidableEq E] in
@[simp]
theorem incidenceMap_apply (F : Finset E) (x : ↑F → F₂)
    (v : ↑(G.edgeSupport F)) :
    G.incidenceMap F x v = ∑ e : ↑F, G.edgeIncidence v.1 e.1 * x e := by
  rfl

/-- Extend a coefficient vector on a subtype by zero to all labelled edges. -/
private noncomputable def vectorCoeff (F : Finset E) (x : ↑F → F₂) (e : E) : F₂ :=
  if h : e ∈ F then x ⟨e, h⟩ else 0

/-- Edges on which a binary coefficient vector is one. -/
private noncomputable def selectedEdges (F : Finset E) (x : ↑F → F₂) : Finset E :=
  F.filter fun e ↦ vectorCoeff F x e = 1

omit [Fintype E] in
private theorem selectedEdges_subset (F : Finset E) (x : ↑F → F₂) :
    selectedEdges F x ⊆ F := Finset.filter_subset _ _

private theorem sum_selectedEdges (F : Finset E) (x : ↑F → F₂) (v : V) :
    ∑ e ∈ selectedEdges F x, G.edgeIncidence v e =
      ∑ e : ↑F, G.edgeIncidence v e.1 * x e := by
  classical
  rw [selectedEdges, Finset.sum_filter, ← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro e _
  simp only [vectorCoeff, dif_pos e.2]
  rcases F₂_eq_zero_or_one (x e) with hx | hx
  · simp [hx]
  · simp [hx]

private def oneVector (F : Finset E) : ↑F → F₂ := fun _ ↦ 1

omit [DecidableEq E] [Fintype E] in
private theorem oneVector_ne_zero {F : Finset E} (hF : F.Nonempty) :
    oneVector F ≠ 0 := by
  obtain ⟨e, he⟩ := hF
  intro h
  have := congr_fun h (⟨e, he⟩ : ↑F)
  simp [oneVector] at this

omit [DecidableEq E] in
private theorem Cycle.oneVector_mem_incidenceKer (C : G.Cycle) :
    oneVector C.edges ∈ LinearMap.ker (G.incidenceMap C.edges) := by
  rw [LinearMap.mem_ker]
  funext v
  rw [G.incidenceMap_apply]
  calc
    (∑ e : ↑C.edges, G.edgeIncidence v.1 e.1 * oneVector C.edges e) =
        ∑ e : ↑C.edges, G.edgeIncidence v.1 e.1 := by simp [oneVector]
    _ = ∑ e ∈ C.edges, G.edgeIncidence v.1 e := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach C.edges (fun e ↦ G.edgeIncidence v.1 e)
    _ = 0 := C.even v.1

private theorem selectedEdges_even_of_mem_ker {F : Finset E} (x : ↑F → F₂)
    (hx : x ∈ LinearMap.ker (G.incidenceMap F)) :
    G.IsEvenEdgeSet (selectedEdges F x) := by
  classical
  intro v
  by_cases hv : v ∈ G.edgeSupport F
  · have hx0 : G.incidenceMap F x ⟨v, hv⟩ = 0 := by
      have hmap : G.incidenceMap F x = 0 := LinearMap.mem_ker.mp hx
      exact congr_fun hmap ⟨v, hv⟩
    rw [G.sum_selectedEdges]
    simpa [G.incidenceMap_apply, mul_comm] using hx0
  · apply Finset.sum_eq_zero
    intro e heD
    have heF : e ∈ F := selectedEdges_subset F x heD
    have hnend : ∀ i : Fin 2, G.endAt e i ≠ v := by
      intro i hi
      exact hv (G.mem_edgeSupport_iff.mpr ⟨e, heF, i, hi⟩)
    simp [edgeIncidence, hnend]

omit [DecidableEq E] in
private theorem Cycle.incidenceKer_eq_span_oneVector (C : G.Cycle) :
    LinearMap.ker (G.incidenceMap C.edges) =
      Submodule.span F₂ ({oneVector C.edges} : Set (↑C.edges → F₂)) := by
  classical
  apply le_antisymm
  · intro x hx
    let D := selectedEdges C.edges x
    have hDsub : D ⊆ C.edges := selectedEdges_subset C.edges x
    have hDeven : G.IsEvenEdgeSet D := G.selectedEdges_even_of_mem_ker x hx
    by_cases hDne : D.Nonempty
    · have hDF : D = C.edges := C.minimal D hDne hDsub hDeven
      have hxone : x = oneVector C.edges := by
        funext e
        have heD : e.1 ∈ D := hDF.symm ▸ e.2
        have hcoeff := (Finset.mem_filter.mp heD).2
        simpa [D, selectedEdges, vectorCoeff, e.2, oneVector] using hcoeff
      rw [hxone]
      exact Submodule.mem_span_singleton_self (R := F₂) (oneVector C.edges)
    · have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDne
      have hxzero : x = 0 := by
        funext e
        have heNotD : e.1 ∉ D := by simp [hDempty]
        have hcoeff : vectorCoeff C.edges x e.1 ≠ 1 := by
          simpa [D, selectedEdges, e.2] using heNotD
        rcases F₂_eq_zero_or_one (x e) with he | he
        · exact he
        · exfalso
          apply hcoeff
          simpa [vectorCoeff, e.2] using he
      rw [hxzero]
      exact (Submodule.span F₂ ({oneVector C.edges} : Set (↑C.edges → F₂))).zero_mem
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact C.oneVector_mem_incidenceKer

omit [DecidableEq E] in
private theorem Cycle.finrank_incidenceKer (C : G.Cycle) :
    Module.finrank F₂ (LinearMap.ker (G.incidenceMap C.edges)) = 1 := by
  rw [C.incidenceKer_eq_span_oneVector]
  exact finrank_span_singleton (oneVector_ne_zero C.nonempty)

private def coordinateSum {J : Type*} [Fintype J] : (J → F₂) →ₗ[F₂] F₂ where
  toFun x := ∑ j, x j
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, RingHom.id_apply]
    change (∑ j, c * x j) = c * ∑ j, x j
    exact (Finset.mul_sum Finset.univ x c).symm

private theorem coordinateSum_surjective {J : Type*} [Fintype J] [Nonempty J] :
    Function.Surjective (coordinateSum (J := J)) := by
  classical
  intro c
  let j₀ : J := Classical.choice inferInstance
  refine ⟨Pi.single j₀ c, ?_⟩
  simp [coordinateSum, j₀]

private theorem coordinateSum_ker_finrank {J : Type*} [Fintype J] [Nonempty J] :
    Module.finrank F₂ (LinearMap.ker (coordinateSum (J := J))) + 1 = Fintype.card J := by
  have hrange : LinearMap.range (coordinateSum (J := J)) = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ coordinateSum_surjective
  have h := LinearMap.finrank_range_add_finrank_ker (coordinateSum (J := J))
  rw [hrange] at h
  simpa [Module.finrank_pi, Module.finrank_self, add_comm] using h

omit [DecidableEq E] in
private theorem sum_endpoint_indicator (F : Finset E) {e : E} (he : e ∈ F) (i : Fin 2) :
    (∑ v : ↑(G.edgeSupport F),
      if G.endAt e i = v.1 then (1 : F₂) else 0) = 1 := by
  classical
  let w : ↑(G.edgeSupport F) :=
    ⟨G.endAt e i, G.mem_edgeSupport_iff.mpr ⟨e, he, i, rfl⟩⟩
  simpa only [w, Subtype.ext_iff] using
    (Fintype.sum_ite_eq w (fun _ : ↑(G.edgeSupport F) ↦ (1 : F₂)))

omit [DecidableEq E] in
private theorem sum_edgeIncidence_support (F : Finset E) {e : E} (he : e ∈ F) :
    ∑ v : ↑(G.edgeSupport F), G.edgeIncidence v.1 e = 0 := by
  simp only [edgeIncidence, Finset.sum_add_distrib]
  rw [G.sum_endpoint_indicator F he 0, G.sum_endpoint_indicator F he 1]
  exact CharTwo.add_self_eq_zero 1

omit [DecidableEq E] in
private theorem Cycle.support_nonempty (C : G.Cycle) : Nonempty ↑(G.edgeSupport C.edges) := by
  obtain ⟨e, he⟩ := C.nonempty
  exact ⟨⟨G.endAt e 0, G.mem_edgeSupport_iff.mpr ⟨e, he, 0, rfl⟩⟩⟩

omit [DecidableEq E] in
/-- A minimal nonzero binary-even family has at most as many edges as supported vertices.
This is the rank-nullity step in the standard proof that a binary cycle is 2-regular. -/
private theorem Cycle.card_edges_le_card_support (C : G.Cycle) :
    C.edges.card ≤ (G.edgeSupport C.edges).card := by
  let S := ↑(G.edgeSupport C.edges)
  let A := G.incidenceMap C.edges
  let σ : (S → F₂) →ₗ[F₂] F₂ := coordinateSum
  letI : Nonempty S := C.support_nonempty
  have hrange : LinearMap.range A ≤ LinearMap.ker σ := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change ∑ v : S, G.incidenceMap C.edges x v = 0
    simp_rw [G.incidenceMap_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    rw [← Finset.sum_mul, G.sum_edgeIncidence_support C.edges e.2]
    simp
  have hle : Module.finrank F₂ (LinearMap.range A) ≤
      Module.finrank F₂ (LinearMap.ker σ) := Submodule.finrank_mono hrange
  have hrank := LinearMap.finrank_range_add_finrank_ker A
  have hker := C.finrank_incidenceKer
  have hσ := coordinateSum_ker_finrank (J := S)
  change Module.finrank F₂ (LinearMap.ker A) = 1 at hker
  change Module.finrank F₂ (LinearMap.ker σ) + 1 = Fintype.card S at hσ
  rw [hker, Module.finrank_pi] at hrank
  have hrank' : Module.finrank F₂ (LinearMap.range A) + 1 = C.edges.card := by
    simpa using hrank
  have hσ' : Module.finrank F₂ (LinearMap.ker σ) + 1 =
      (G.edgeSupport C.edges).card := by
    simpa using hσ
  omega

omit [DecidableEq E] in
/-- Every supported vertex of a binary cycle has ordinary degree exactly two. -/
theorem Cycle.degree_eq_two (C : G.Cycle) {v : V}
    (hv : v ∈ G.edgeSupport C.edges) : G.degreeIn C.edges v = 2 := by
  have heven : ∀ w : V, Even (G.degreeIn C.edges w) :=
    (G.isEvenEdgeSet_iff_even_degree C.edges).mp C.even
  have hge : ∀ w ∈ G.edgeSupport C.edges, 2 ≤ G.degreeIn C.edges w := by
    intro w hw
    have hpos : 0 < G.degreeIn C.edges w :=
      (G.degreeIn_pos_iff_mem_edgeSupport C.edges w).mpr hw
    obtain ⟨k, hk⟩ := heven w
    omega
  have hsum : ∑ w ∈ G.edgeSupport C.edges, G.degreeIn C.edges w =
      2 * C.edges.card := by
    rw [← G.sum_degreeIn]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    have hnpos : ¬ 0 < G.degreeIn C.edges w := by
      intro hp
      exact hw ((G.degreeIn_pos_iff_mem_edgeSupport C.edges w).mp hp)
    omega
  have hlower : 2 * (G.edgeSupport C.edges).card ≤
      ∑ w ∈ G.edgeSupport C.edges, G.degreeIn C.edges w := by
    have h := Finset.sum_le_sum (fun w hw ↦ hge w hw)
    simpa [Nat.mul_comm] using h
  have hcard : C.edges.card = (G.edgeSupport C.edges).card := by
    have hle := C.card_edges_le_card_support
    omega
  have hsumeq : (∑ _w ∈ G.edgeSupport C.edges, 2) =
      ∑ w ∈ G.edgeSupport C.edges, G.degreeIn C.edges w := by
    calc
      (∑ _w ∈ G.edgeSupport C.edges, 2) =
          (G.edgeSupport C.edges).card * 2 := by simp
      _ = 2 * C.edges.card := by omega
      _ = ∑ w ∈ G.edgeSupport C.edges, G.degreeIn C.edges w := hsum.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun w hw ↦ hge w hw)).mp hsumeq v hv).symm

/-- Regard a minimal nonempty binary-even edge set as an ordinary connected 2-regular circuit. -/
def Cycle.toOrdinaryCircuit (C : G.Cycle) : G.OrdinaryCircuit where
  edges := C.edges
  nonempty := C.nonempty
  connected := C.edgeConnected
  twoRegular := fun _ hv ↦ Cycle.degree_eq_two G C hv

omit [DecidableEq E] in
@[simp]
theorem Cycle.toOrdinaryCircuit_edges (C : G.Cycle) :
    C.toOrdinaryCircuit.edges = C.edges := rfl

omit [DecidableEq E] in
/-- An ordinary circuit is an even edge set (including the singleton-loop case). -/
theorem OrdinaryCircuit.even (C : G.OrdinaryCircuit) : G.IsEvenEdgeSet C.edges := by
  rw [G.isEvenEdgeSet_iff_even_degree]
  intro v
  by_cases hv : v ∈ G.edgeSupport C.edges
  · rw [C.twoRegular v hv]
    exact ⟨1, by omega⟩
  · have hnpos : ¬ 0 < G.degreeIn C.edges v := by
      intro hp
      exact hv ((G.degreeIn_pos_iff_mem_edgeSupport C.edges v).mp hp)
    have hz : G.degreeIn C.edges v = 0 := Nat.eq_zero_of_not_pos hnpos
    rw [hz]
    exact Even.zero

/-- Mapping cycles to ordinary circuits does not change edge multiplicities. -/
private theorem filter_map_toOrdinaryCircuit_length (L : List G.Cycle) (e : E) :
    ((L.map (Cycle.toOrdinaryCircuit G)).filter fun C ↦ e ∈ C.edges).length =
      (L.filter fun C ↦ e ∈ C.edges).length := by
  induction L with
  | nil => simp
  | cons C L ih =>
      by_cases he : e ∈ C.edges <;> simp [he, Cycle.toOrdinaryCircuit, ih]

/-- The existing minimal-even-set decomposition can therefore be read as a decomposition into
ordinary connected 2-regular circuits. -/
theorem decompose_even_edge_set_ordinary (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.OrdinaryCircuit,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by
  obtain ⟨L, hL⟩ := G.decompose_even_edge_set F hF
  refine ⟨L.map (Cycle.toOrdinaryCircuit G), ?_⟩
  intro e
  rw [filter_map_toOrdinaryCircuit_length, hL e]

/-- Transport a decomposition from the minimal-even representation to ordinary circuits. -/
def CircuitDecomposition.toOrdinary (S : G.CircuitDecomposition) :
    G.OrdinaryCircuitDecomposition where
  circuits := S.circuits.map (Cycle.toOrdinaryCircuit G)
  coveredOnce := by
    intro e
    rw [filter_map_toOrdinaryCircuit_length, S.coveredOnce e]

theorem CircuitDecomposition.compatible_toOrdinary {T : G.EulerTour}
    {S : G.CircuitDecomposition} (h : S.Compatible T) : S.toOrdinary.Compatible T := by
  intro i C hC
  change C ∈ S.circuits.map (Cycle.toOrdinaryCircuit G) at hC
  rw [List.mem_map] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  exact h i D hD

/-- Sabidussi compatibility with the conclusion expressed using ordinary connected 2-regular
circuits rather than minimal binary-even edge sets. -/
theorem loop_sabidussi_compatibility_ordinary {G : LoopMultigraph V E} (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.OrdinaryCircuitDecomposition, S.Compatible T := by
  obtain ⟨S, hS⟩ := loop_sabidussi_compatibility T hmin
  exact ⟨S.toOrdinary, CircuitDecomposition.compatible_toOrdinary G hS⟩

end LoopMultigraph
end Sabidussi
