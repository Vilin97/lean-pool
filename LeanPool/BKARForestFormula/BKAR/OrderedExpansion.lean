/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanPool.BKARForestFormula.BKAR.ForestGraph
import LeanPool.BKARForestFormula.BKAR.Differential

/-! # The one-edge expansion step

The fundamental-theorem-of-calculus step of the forest induction: for a
one-edge extension of a forest, differentiating the interpolation family in
the new edge parameter and integrating over `[0, 1]` splits a contribution
into a boundary term and a contribution of the extended forest.  Packages
extensions along active edges as `ActiveExtension` and proves the
derivative and integrability lemmas consumed by the recursion behind the
BKAR forest interpolation formula (see `BKAR.Formula`).
-/

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace EdgeExtension

variable {F F' : Forest V} {e₀ : Edge V}

/-- The edge added by an extension is active for the old forest. -/
theorem mem_activeEdges (h : EdgeExtension F F' e₀) :
    e₀ ∈ F.activeEdges := by
  apply F.mem_activeEdges_of_not_inSameComponent
  have hacyclic : IsAcyclicEdgeSet (insert e₀ F.edges) := by
    rw [← h.edges_eq]
    exact F'.isAcyclicEdgeSet
  exact (F.acyclic_insert_iff_edge h.new_not_mem).mp hacyclic

/--
After a one-edge extension, every still-active edge was already active before,
and the newly inserted edge is no longer active.
-/
theorem activeEdges_subset_erase (h : EdgeExtension F F' e₀) :
    F'.activeEdges ⊆ F.activeEdges.erase e₀ := by
  intro e he
  rw [Finset.mem_erase]
  constructor
  · intro heq
    subst e
    exact (F'.not_inSameComponent_of_mem_activeEdges he)
      (F'.edge_inSameComponent h.new_mem)
  · apply F.mem_activeEdges_of_not_inSameComponent
    intro hcomp
    exact (F'.not_inSameComponent_of_mem_activeEdges he)
      (h.old_component hcomp)

/--
A one-edge extension strictly decreases the number of active edges.
-/
theorem activeEdges_card_lt (h : EdgeExtension F F' e₀) :
    F'.activeEdges.card < F.activeEdges.card := by
  have hsubset : F'.activeEdges ⊆ F.activeEdges.erase e₀ :=
    h.activeEdges_subset_erase
  exact (Finset.card_le_card hsubset).trans_lt
    (Finset.card_erase_lt_of_mem h.mem_activeEdges)

/--
Pointwise re-interpretation of an active-edge integrand on a one-edge
extension, under the ordered-simplex bound on the old parameters.
-/
theorem partialDeriv_interpWithFill_eq_extension (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ ρ (F.interpWithFill u s) =
      partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u s) s) := by
  rw [h.interpWithFill_extend_eq u hu]

/--
Interval integrability transfers across the one-edge extension
re-interpretation.
-/
theorem intervalIntegrable_partialDeriv_interpWithFill_extension
    (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (hint : IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ (F.interpWithFill u t))
      MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t))
      MeasureTheory.volume a b := by
  refine hint.congr ?_
  intro t ht
  exact h.partialDeriv_interpWithFill_eq_extension u ρ
    (hbound t (Set.uIoc_subset_uIcc ht))

/--
The one-edge summand in the differential identity may be integrated after
reinterpreting its configuration on the extended forest.
-/
theorem integral_partialDeriv_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b, partialDeriv e₀ ρ (F.interpWithFill u t)) =
      ∫ t in a..b, partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact h.partialDeriv_interpWithFill_eq_extension u ρ (hbound t ht)

/--
Ordered-derivative form of the one-edge extension re-interpretation. The new
edge is consed onto the explicit derivative list.
-/
theorem mixedPartialList_cons_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u s) =
      mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u s) s) := by
  rw [mixedPartialList_cons_apply]
  exact h.partialDeriv_interpWithFill_eq_extension u
    (mixedPartialList es ρ) hu

/--
Interval integrability transfers for the ordered-derivative form of the
one-edge extension re-interpretation.
-/
theorem intervalIntegrable_mixedPartialList_cons_interpWithFill_extension
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (hint : IntervalIntegrable
      (fun t : ℝ =>
        partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u t))
      MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun t : ℝ => mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u t) t))
      MeasureTheory.volume a b := by
  simpa only [mixedPartialList_cons_apply] using
    h.intervalIntegrable_partialDeriv_interpWithFill_extension u
      (mixedPartialList es ρ) a b hbound hint

/--
Integral congruence for the ordered-derivative form of the one-edge extension
re-interpretation.
-/
theorem integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b,
        partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u t)) =
      ∫ t in a..b, mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u t) t) := by
  simpa only [mixedPartialList_cons_apply] using
    h.integral_partialDeriv_interpWithFill_eq_extension u
      (mixedPartialList es ρ) a b hbound

end EdgeExtension

/-- A chosen one-edge forest extension for an edge. -/
structure ActiveExtension (F : Forest V) (e : Edge V) where
  /-- The forest obtained by adjoining the selected active edge. -/
  forest : Forest V
  extension : EdgeExtension F forest e

namespace ActiveExtension

variable {F : Forest V} {e : Edge V}

/-- The edge of a chosen one-edge extension is active for the old forest. -/
theorem mem_activeEdges (h : ActiveExtension F e) :
    e ∈ F.activeEdges :=
  h.extension.mem_activeEdges

/-- A chosen active extension strictly decreases the number of active edges. -/
theorem activeEdges_card_lt (h : ActiveExtension F e) :
    h.forest.activeEdges.card < F.activeEdges.card :=
  h.extension.activeEdges_card_lt

end ActiveExtension

/--
Any `Forest` representative whose edge set is obtained by inserting an active edge gives the
corresponding one-edge extension certificate.  Thus the hard existence problem
for active extensions is exactly the construction of the inserted `Forest` representative.
-/
theorem edgeExtension_of_edges_eq_insert
    {F F' : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hedges : F'.edges = insert e₀ F.edges) :
    EdgeExtension F F' e₀ := by
  let oldComponent :
      ∀ {i j : V}, F.inSameComponent i j → F'.inSameComponent i j := by
    intro i j h
    have hpathF : IsSimplePath F (F.pathInF i j h) i j :=
      F.pathInF_isSimple h
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F.pathInF i j h) i j :=
      F.acyclic.isSimplePath_iff.mp hpathF
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F.pathInF i j h) i j := by
      rw [hedges]
      exact hgraphF.mono (Finset.subset_insert e₀ F.edges)
    exact F'.inSameComponent_of_isSimplePath
      (F'.acyclic.isSimplePath_iff.mpr hgraphF')
  refine {
    new_not_mem := F.not_mem_edges_of_mem_activeEdges he₀
    edges_eq := hedges
    old_component := oldComponent
    old_path := ?_
    new_path_uses := ?_ }
  · intro i j h
    have hpathF : IsSimplePath F (F.pathInF i j h) i j :=
      F.pathInF_isSimple h
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F.pathInF i j h) i j :=
      F.acyclic.isSimplePath_iff.mp hpathF
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F.pathInF i j h) i j := by
      rw [hedges]
      exact hgraphF.mono (Finset.subset_insert e₀ F.edges)
    symm
    exact F'.pathInF_unique (oldComponent h) (F.pathInF i j h)
      (F'.acyclic.isSimplePath_iff.mpr hgraphF')
  · intro i j hnot hF'
    by_contra hmissing
    have hpathF' : IsSimplePath F' (F'.pathInF i j hF') i j :=
      F'.pathInF_isSimple hF'
    have hgraphF' :
        EdgePath.IsSimplePath F'.edges (F'.pathInF i j hF') i j :=
      F'.acyclic.isSimplePath_iff.mp hpathF'
    have hmemF : ∀ e ∈ F'.pathInF i j hF', e ∈ F.edges := by
      intro e he
      have heF' : e ∈ F'.edges :=
        hgraphF'.edge_mem e he
      have heInsert : e ∈ insert e₀ F.edges := by
        rw [← hedges]
        exact heF'
      rw [Finset.mem_insert] at heInsert
      exact heInsert.elim
        (fun heq => False.elim (hmissing (heq ▸ he)))
        id
    have hgraphF :
        EdgePath.IsSimplePath F.edges (F'.pathInF i j hF') i j :=
      hgraphF'.mono_of_forall_mem hmemF
    exact hnot (F.inSameComponent_of_isSimplePath
      (F.acyclic.isSimplePath_iff.mpr hgraphF))

/--
Packaging form of `edgeExtension_of_edges_eq_insert`: to produce an active
extension, it is enough to produce a `Forest` representative with the inserted edge set.
-/
def activeExtensionOfEdgesEqInsert
    {F F' : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hedges : F'.edges = insert e₀ F.edges) :
    ActiveExtension F e₀ where
  forest := F'
  extension := edgeExtension_of_edges_eq_insert he₀ hedges

/--
Existential packaging form for the final choice-removal step.  The remaining
hard graph obligation is now isolated as existence of a `Forest` representative whose
support is the inserted active edge set.
-/
theorem nonempty_activeExtension_of_exists_forest_edges_eq_insert
    {F : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hforest : ∃ F' : Forest V, F'.edges = insert e₀ F.edges) :
    Nonempty (ActiveExtension F e₀) := by
  rcases hforest with ⟨F', hedges⟩
  exact ⟨activeExtensionOfEdgesEqInsert he₀ hedges⟩

theorem exists_forest_edges_eq_insert_of_mem_activeEdges
    (F : Forest V) {e₀ : Edge V} (he₀ : e₀ ∈ F.activeEdges) :
    ∃ F' : Forest V, F'.edges = insert e₀ F.edges := by
  rcases F.isAcyclicEdgeSet_insert_of_mem_activeEdges he₀ with ⟨data⟩
  exact ⟨data.toForest, rfl⟩

theorem nonempty_activeExtension_of_mem_activeEdges
    (F : Forest V) {e₀ : Edge V} (he₀ : e₀ ∈ F.activeEdges) :
    Nonempty (ActiveExtension F e₀) :=
  nonempty_activeExtension_of_exists_forest_edges_eq_insert he₀
    (F.exists_forest_edges_eq_insert_of_mem_activeEdges he₀)

/--
If no edge connects two different components, the fill-parameter interpolation
has already reached the standard BKAR interpolation.
-/
theorem interpWithFill_eq_standardInterp_of_activeEdges_eq_empty (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) (hF : F.activeEdges = ∅) :
    F.interpWithFill u t = F.standardInterp u := by
  funext e
  by_cases he : F.inSameComponent e.left e.right
  · rw [interpWithFill, standardInterp, dite_eq_left he, dite_eq_left he]
  · have hactive : e ∈ F.activeEdges :=
      F.mem_activeEdges_of_not_inSameComponent he
    have hempty : e ∈ (∅ : Finset (Edge V)) := by
      rw [← hF]
      exact hactive
    exact False.elim (Finset.notMem_empty e hempty)

/--
Terminal ordered-derivative form: with no active edges left, the interpolation
parameter can be replaced by the standard configuration.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u t) =
      mixedPartialList es ρ (F.standardInterp u) := by
  rw [F.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty u t hF]

/--
The differential right-hand side is interval integrable once each active-edge
partial derivative is interval integrable.
-/
theorem intervalIntegrable_activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b := by
  refine (IntervalIntegrable.sum F.activeEdges
      (f := fun e t => partialDeriv e ρ (F.interpWithFill u t))
      hint).congr ?_
  intro t _
  change (∑ e ∈ F.activeEdges,
      (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))) t =
    F.activeEdgePartialSum u ρ t
  rw [F.activeEdgePartialSum_def u ρ t, Finset.sum_apply]

/--
Split the integral of the differential right-hand side into the finite
sum of one-edge integrals over the active edges of the forest.
-/
theorem integral_activeEdgePartialSum_eq_sum_integrals (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      Finset.sum F.activeEdges
        (fun e => ∫ t in a..b,
          partialDeriv e ρ (F.interpWithFill u t)) := by
  simpa only [activeEdgePartialSum] using
    (intervalIntegral.integral_finsetSum
      (a := a) (b := b) (μ := MeasureTheory.volume)
      (s := F.activeEdges)
      (f := fun e t => partialDeriv e ρ (F.interpWithFill u t))
      hint)

/--
Integrated form of the differential identity over one interpolation parameter.
This is the analytic one-step expansion behind the ordered forest recursion.
-/
theorem integral_activeEdgePartialSum_eq_sub (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht =>
      F.hasDerivAt_rho_interpWithFill_of_differentiableAt u (hρ t ht))
    hint

/--
Integrated differential identity after expanding the differential right-hand side as
the active-edge sum.
-/
theorem sum_integrals_activeEdges_eq_sub (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        partialDeriv e ρ (F.interpWithFill u t)) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) := by
  rw [← F.integral_activeEdgePartialSum_eq_sum_integrals u ρ a b hint]
  exact F.integral_activeEdgePartialSum_eq_sub u ρ a b hρ
    (F.intervalIntegrable_activeEdgePartialSum u ρ a b hint)

/--
Boundary-expansion form of the integrated differential identity, with the lower
endpoint specialized to the standard interpolation configuration.
-/
theorem rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    ρ (F.interpWithFill u b) =
      ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            partialDeriv e ρ (F.interpWithFill u t)) := by
  have hsum :
      Finset.sum F.activeEdges
        (fun e => ∫ t in 0..b,
          partialDeriv e ρ (F.interpWithFill u t)) =
        ρ (F.interpWithFill u b) - ρ (F.standardInterp u) := by
    simpa only [F.interpWithFill_zero u] using
      F.sum_integrals_activeEdges_eq_sub u ρ 0 b hρ hint
  calc
    ρ (F.interpWithFill u b) =
        (ρ (F.interpWithFill u b) - ρ (F.standardInterp u)) +
          ρ (F.standardInterp u) := by
          rw [sub_add_cancel]
    _ =
        ρ (F.standardInterp u) +
          (ρ (F.interpWithFill u b) - ρ (F.standardInterp u)) := by
          rw [add_comm]
    _ = ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            partialDeriv e ρ (F.interpWithFill u t)) := by
          rw [← hsum]

/--
The true empty-start expansion: the first FTC step runs from the zero
configuration to the all-one configuration and differentiates along every
edge of the complete graph.
-/
theorem rho_oneConfig_eq_zeroConfig_add_sum_integrals_empty
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 (1 : ℝ),
      DifferentiableAt ℝ ρ (constantConfig t))
    (hint : ∀ e : Edge V,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (constantConfig t))
        MeasureTheory.volume 0 1) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ (constantConfig t)) := by
  have hbase :
      ρ ((Forest.empty V).interpWithFill emptyParam 1) =
        ρ ((Forest.empty V).standardInterp emptyParam) +
          Finset.sum (Forest.empty V).activeEdges
            (fun e => ∫ t in 0..(1 : ℝ),
              partialDeriv e ρ
                ((Forest.empty V).interpWithFill emptyParam t)) :=
    (Forest.empty V).rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
      emptyParam ρ 1
      (by
        intro t ht
        rw [emptyParam_interpWithFill t]
        exact hρ t ht)
      (by
        intro e _
        have hfun :
            (fun t : ℝ =>
                partialDeriv e ρ
                  ((Forest.empty V).interpWithFill emptyParam t)) =
              fun t : ℝ => partialDeriv e ρ (constantConfig t) := by
          funext t
          rw [emptyParam_interpWithFill t]
        rw [hfun]
        exact hint e)
  rw [emptyParam_interpWithFill_one, emptyParam_standardInterp,
    empty_activeEdges] at hbase
  have hsum :
      Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ
              ((Forest.empty V).interpWithFill emptyParam t)) =
        Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ (constantConfig t)) := by
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr
    intro t _
    change partialDeriv e ρ
        ((Forest.empty V).interpWithFill emptyParam t) =
      partialDeriv e ρ (constantConfig t)
    rw [emptyParam_interpWithFill t]
  rw [hsum] at hbase
  exact hbase

/--
Ordered-mixed-partial version of the integrated differential identity. This is the
form used when the ordered recursion has already accumulated the derivative
list `es` and expands by one active edge.
-/
theorem sum_integrals_activeEdges_mixedPartialList_eq_sub (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) =
      mixedPartialList es ρ (F.interpWithFill u b) -
        mixedPartialList es ρ (F.interpWithFill u a) := by
  simpa only [mixedPartialList_cons_apply] using
    F.sum_integrals_activeEdges_eq_sub u (mixedPartialList es ρ) a b hρ
      (by
        simpa only [mixedPartialList_cons_apply] using hint)

/-- The ordered active-edge integral remainder is zero when no active edges remain. -/
theorem sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ) (hF : F.activeEdges = ∅) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) = 0 := by
  rw [hF]
  exact Finset.sum_empty

/--
Boundary-expansion form of the ordered-mixed-partial differential identity. This is
the local recursion formula before the active-edge summands are reinterpreted
as one-edge forest extensions.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            mixedPartialList (e :: es) ρ (F.interpWithFill u t)) := by
  simpa only [mixedPartialList_cons_apply] using
    F.rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
      u (mixedPartialList es ρ) b hρ
      (by
        simpa only [mixedPartialList_cons_apply] using hint)

/--
Terminal form of the ordered-recursion step: with no active edges, the boundary
term is the whole contribution and the next remainder is zero.
-/
theorem mixedPartial_eq_standard_add_integralSum_activeEdges_of_emptyActiveEdges
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            mixedPartialList (e :: es) ρ (F.interpWithFill u t)) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    es u ρ b hF]
  rw [F.sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
    es u ρ 0 b hF]
  rw [add_zero]

/--
Rewrite the active-edge remainder as a sum over explicitly chosen one-edge
forest extensions.
-/
theorem sum_integrals_activeEdges_eq_sum_activeExtensions
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in a..b,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [← Finset.sum_attach F.activeEdges
    (fun e => ∫ t in a..b,
      mixedPartialList (e :: es) ρ (F.interpWithFill u t))]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [mixedPartialList_cons_apply] using
    ((extensions e).extension.integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
        es u ρ a b hbound)

/--
Boundary-expansion form whose active-edge remainder has already been
reinterpreted as a sum over explicitly chosen one-edge forest extensions.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..b,
            mixedPartialList (e.val :: es) ρ
              ((extensions e).forest.interpWithFill
                ((extensions e).extension.extendParam u t) t)) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    es u ρ b hρ hint]
  rw [F.sum_integrals_activeEdges_eq_sum_activeExtensions
    es u ρ 0 b hbound extensions]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
