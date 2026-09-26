/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Sequences
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Exhaustion
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Thullen

/-!
# The Cartan–Thullen characterizations

The core equivalences relate holomorphic convexity, obstruction to common local continuation, a
single function's domain of existence, and hull boundary distance. The function-theoretic
equivalences apply to open subsets of arbitrary finite-dimensional complex normed spaces; the
numerical hull-radius forms use coordinate sup norms. Connectedness is not required. They
include the empty set, the whole space, and dimension zero.

Thullen's Taylor continuation lemma gives the forward implication. For the converse, a countable
basis of balls and overlap components supplies escaping sequences that detect every local
continuation patch. Baire's theorem gives one holomorphic function unbounded on all these
sequences. This proves the full equivalences, including for disconnected open sets.

References: [Range][Range1986] II §3.6; [Fritzsche–Grauert][FritzscheGrauert2002] II §§5–6;
[Scheidemann][Scheidemann2005] §7.3; [Jakóbczak–Jarnicki][JakobczakJarnicki2021] §2.7;
[Hörmander][Hormander1973] §2.5.

## Main results

`isDomainOfHolomorphy_iff_isHolomorphicallyConvex` is the Cartan–Thullen equivalence.
`isDomainOfHolomorphy_iff_exists_domainOfExistence` produces a single completely nonextendable
function. `isDomainOfHolomorphy_iff_hasHolomorphicHullDistanceProperty` and
`isDomainOfHolomorphy_iff_hasHolomorphicHullRadiusProperty` are the hull-radius forms.
`isHolomorphicallyConvex_of_convex` is the convex example.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E}

/-- Finite-dimensional source spaces are proper. -/
local instance : ProperSpace E := FiniteDimensional.proper ℂ E

/-- Finite-dimensional source spaces have countable bases. -/
local instance : SecondCountableTopology E :=
  (Module.finBasis ℂ E).equivFunL.toHomeomorph.secondCountableTopology

omit [FiniteDimensional ℂ E] in
/-- A component of the overlap with a connected larger open set approaches the boundary of the
original set inside the larger set. -/
private theorem exists_boundary_point_of_component (ho : IsOpen U)
    {V : Set E} (hV : IsOpen V) (hc : IsPreconnected V)
    {x : E} (hx : x ∈ U ∩ V) (hn : ¬ V ⊆ U) :
    ∃ a ∈ V, a ∉ U ∧ a ∈ closure (connectedComponentIn (U ∩ V) x) := by
  let C := connectedComponentIn (U ∩ V) x
  have hC : IsOpen C := (ho.inter hV).connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCF : C ⊆ U ∩ V := connectedComponentIn_subset _ _
  have hrel {a : E} (ha : a ∈ closure C) (haF : a ∈ U ∩ V) : a ∈ C := by
    have hconn : IsPreconnected (insert a C) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset ha subset_closure)
    exact (hconn.subset_connectedComponentIn (mem_insert_of_mem _ hxC)
      (insert_subset haF hCF)) (mem_insert _ _)
  by_contra! h
  apply hn
  apply subset_trans (hc.subset_of_closure_inter_subset hC ⟨x, hx.2, hxC⟩ ?_)
    (hCF.trans inter_subset_left)
  rintro a ⟨haC, haV⟩
  exact hrel haC ⟨by by_contra haU; exact h a haV haU haC, haV⟩

/-- There is a countable basis of nonempty open balls in a finite coordinate space. -/
private theorem exists_countable_ball_basis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] :
    ∃ b : Set (Set E), b.Countable ∧ TopologicalSpace.IsTopologicalBasis b ∧
      ∀ B ∈ b, ∃ c r, 0 < r ∧ B = ball c r := by
  let T : Set (Set E) := {B | ∃ c r, 0 < r ∧ B = ball c r}
  have hT : TopologicalSpace.IsTopologicalBasis T := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨c, r, hr, rfl⟩; exact isOpen_ball
    · intro x N hx hN
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hN.mem_nhds hx)
      exact ⟨ball x r, ⟨x, r, hr, rfl⟩, mem_ball_self hr, hsub⟩
  obtain ⟨b, hbT, hbc, hb⟩ := hT.exists_countable
  exact ⟨b, hbc, hb, hbT⟩

/-- One holomorphic function is unbounded on every member of a countable family of escaping
sequences. Baire's theorem combines the individual obstructions. -/
private theorem exists_unbounded_on_sequences {I : Type*} [Countable I]
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U)
    (p : I → ℕ → E) (hp : ∀ i j, p i j ∈ U)
    (he : ∀ i, EscapesCompactSubsets U (p i)) :
    ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧
      ∀ i, ¬ BddAbove (range (fun j => ‖f (p i j)‖)) := by
  classical
  let V : TopologicalSpace.Opens E := ⟨U, ho⟩
  let : LocallyCompactSpace V := ho.locallyCompactSpace
  have : (uniformity C(V, ℂ)).IsCountablyGenerated := inferInstance
  have : (uniformity (HolomorphicMap V ℂ)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (HolomorphicMap V ℂ) :=
    .of_completeSpace_pseudometrizable
  let : BaireSpace (HolomorphicMap V ℂ) := BaireSpace.of_completelyPseudoMetrizable
  let A (q : I × ℕ) : Set (HolomorphicMap V ℂ) :=
    {f | ∀ j, ‖f.val ⟨p q.1 j, hp q.1 j⟩‖ ≤ q.2}
  have hclosed (q : I × ℕ) : IsClosed (A q) := by
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le
      (continuous_holomorphicMap_eval V ⟨p q.1 j, hp q.1 j⟩).norm continuous_const
  have hempty (q : I × ℕ) : interior (A q) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hgA := interior_subset hg
    obtain ⟨h, hh, hno⟩ :=
      (isHolomorphicallyConvex_iff_unbounded_on_escaping_sequences ho).mp hU
        (p q.1) (hp q.1) (he q.1)
    let H : HolomorphicMap V ℂ := ⟨⟨fun z => h z, hh.continuousOn.domRestrict⟩,
      hh.congr ho (fun z hz => by rw [openExtension_apply V _ hz]; rfl)⟩
    let c (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1)
    have hlim : Tendsto (fun k => g + c k • H) atTop (𝓝 g) := by
      simpa [c] using (tendsto_const_nhds (x := g)).add
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).smul_const H)
    obtain ⟨k, hk⟩ := (hlim.eventually (mem_interior_iff_mem_nhds.mp hg)).exists
    have hc : 0 < ‖c k‖ := by
      apply norm_pos_iff.mpr
      apply one_div_ne_zero
      exact_mod_cast Nat.succ_ne_zero k
    apply hno
    refine ⟨2 * (q.2 : ℝ) / ‖c k‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    apply (le_div_iff₀ hc).mpr
    have hnorm := norm_sub_le ((g + c k • H).val ⟨p q.1 j, hp q.1 j⟩)
      (g.val ⟨p q.1 j, hp q.1 j⟩)
    change ‖g.val ⟨p q.1 j, hp q.1 j⟩ + c k * h (p q.1 j) -
      g.val ⟨p q.1 j, hp q.1 j⟩‖ ≤ _ at hnorm
    rw [add_sub_cancel_left, norm_mul] at hnorm
    nlinarith [hk j, hgA j]
  have hdense := dense_iInter_of_isOpen (fun q => (hclosed q).isOpen_compl)
    (fun q => interior_eq_empty_iff_dense_compl.mp (hempty q))
  obtain ⟨f, hf⟩ := hdense.nonempty
  refine ⟨openExtension V f.val, f.property, ?_⟩
  intro i hbound
  obtain ⟨M, hM⟩ := hbound
  obtain ⟨N, hN⟩ := exists_nat_ge M
  apply (mem_iInter.mp hf (i, N))
  intro j
  have h := (hM (mem_range_self j)).trans hN
  simpa only [openExtension_apply V _ (hp i j)] using h

/-- **Existence of a completely nonextendable function.** Baire's theorem gives one
function unbounded on a countable family of escaping sequences that detects every
local continuation patch. Disconnected open sets are allowed. -/
theorem IsHolomorphicallyConvex.exists_domainOfExistence
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) :
    ∃ f : E → ℂ, IsDomainOfExistence U f := by
  classical
  obtain ⟨b, hbc, hb, hballs⟩ := exists_countable_ball_basis E
  have : Countable b := hbc.to_subtype
  have hne (B : b) : B.val.Nonempty := by
    obtain ⟨c, r, hr, hB⟩ := hballs B.val B.property
    exact ⟨c, hB ▸ mem_ball_self hr⟩
  let I := {q : b × b // q.2.val ⊆ U ∩ q.1.val ∧ ¬ q.1.val ⊆ U}
  let x (q : I) := (hne q.val.2).some
  let C (q : I) := connectedComponentIn (U ∩ q.val.1.val) (x q)
  have hx (q : I) : x q ∈ U ∩ q.val.1.val := q.property.1 (hne q.val.2).some_mem
  have hseq (q : I) : ∃ p : ℕ → E,
      (∀ j, p j ∈ C q) ∧ EscapesCompactSubsets U p := by
    obtain ⟨c, r, hr, hB⟩ := hballs q.val.1.val q.val.1.property
    have hc : IsPreconnected q.val.1.val := hB ▸ (convex_ball c r).isPreconnected
    obtain ⟨a, _, haU, haC⟩ := exists_boundary_point_of_component ho
      (hb.isOpen q.val.1.property) hc (hx q) q.property.2
    obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp haC
    refine ⟨p, hp, ?_⟩
    intro K hK hKU
    exact ht.eventually (hK.isClosed.isOpen_compl.mem_nhds (fun haK => haU (hKU haK)))
  choose p hp he using hseq
  have hpU (q : I) (j : ℕ) : p q j ∈ U :=
    (connectedComponentIn_subset _ _ (hp q j)).1
  obtain ⟨f, hf, hno⟩ := exists_unbounded_on_sequences hU ho p hpU he
  refine ⟨f, hf, ?_⟩
  intro V W hV hc hW hWne hWU hWV hext
  by_contra hnot
  obtain ⟨g, hg, hgf⟩ := hext
  obtain ⟨w, hw⟩ := hWne
  let D := connectedComponentIn (U ∩ V) w
  have hDo : IsOpen D := (ho.inter hV).connectedComponentIn
  have hwD : w ∈ D := mem_connectedComponentIn ⟨hWU hw, hWV hw⟩
  have hDsub : D ⊆ U ∩ V := connectedComponentIn_subset _ _
  have heqD : EqOn g f D :=
    (hg.mono (hDsub.trans inter_subset_right)).eqOn_of_preconnected_of_eventuallyEq
      (hf.mono (hDsub.trans inter_subset_left)) isPreconnected_connectedComponentIn hwD
      (Filter.mem_of_superset (hW.mem_nhds hw) hgf)
  obtain ⟨a, haV, haU, haD⟩ := exists_boundary_point_of_component ho hV hc.isPreconnected
    ⟨hWU hw, hWV hw⟩ hnot
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds haV)
  obtain ⟨B, hBb, haB, hBr⟩ := hb.exists_subset_of_mem_open (mem_ball_self hr) isOpen_ball
  have hBcl : closure B ⊆ closedBall a r :=
    (closure_mono hBr).trans closure_ball_subset_closedBall
  have hBV : closure B ⊆ V := hBcl.trans hrV
  have hBK : IsCompact (closure B) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure hBcl
  obtain ⟨z, hzB, hzD⟩ := _root_.mem_closure_iff.mp haD B (hb.isOpen hBb) haB
  obtain ⟨A, hAb, hzA, hAsub⟩ := hb.exists_subset_of_mem_open
    (show z ∈ B ∩ D from ⟨hzB, hzD⟩) ((hb.isOpen hBb).inter hDo)
  let q : I := ⟨(⟨B, hBb⟩, ⟨A, hAb⟩),
    fun z hz => ⟨(hDsub (hAsub hz).2).1, (hAsub hz).1⟩,
    fun h => haU (h haB)⟩
  have hxD : x q ∈ D := (hAsub (hne q.val.2).some_mem).2
  have hCsub : C q ⊆ U ∩ B := connectedComponentIn_subset _ _
  have hCV : C q ⊆ V := hCsub.trans (inter_subset_right.trans (subset_closure.trans hBV))
  have heqC : EqOn g f (C q) :=
    (hg.mono hCV).eqOn_of_preconnected_of_eventuallyEq
      (hf.mono (hCsub.trans inter_subset_left)) isPreconnected_connectedComponentIn
      (mem_connectedComponentIn (hx q))
      (Filter.mem_of_superset (hDo.mem_nhds hxD) heqD)
  obtain ⟨M, hM⟩ := hBK.bddAbove_image (hg.continuousOn.mono hBV).norm
  apply hno q
  refine ⟨M, ?_⟩
  rintro _ ⟨j, rfl⟩
  change ‖f (p q j)‖ ≤ M
  rw [← heqC (hp q j)]
  exact hM ⟨p q j, subset_closure (hCsub (hp q j)).2, rfl⟩

/-- **Cartan–Thullen, reverse implication.** A single completely nonextendable
function obstructs common local continuation beyond the open set. -/
theorem IsHolomorphicallyConvex.isDomainOfHolomorphy
    (hU : IsHolomorphicallyConvex U) (ho : IsOpen U) : IsDomainOfHolomorphy U := by
  obtain ⟨f, hf⟩ := hU.exists_domainOfExistence ho
  exact hf.isDomainOfHolomorphy

/-- **Cartan–Thullen.** Holomorphic convexity is equivalent to the domain-of-holomorphy
property. The reverse implication uses a completely nonextendable function. -/
theorem isDomainOfHolomorphy_iff_isHolomorphicallyConvex (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ IsHolomorphicallyConvex U :=
  ⟨fun h => h.isHolomorphicallyConvex ho, fun h => h.isDomainOfHolomorphy ho⟩

/-- A domain of holomorphy is the domain of existence of a single scalar function. The converse
follows from the obstruction to common local continuation. -/
theorem isDomainOfHolomorphy_iff_exists_domainOfExistence (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ ∃ f : E → ℂ, IsDomainOfExistence U f :=
  ⟨fun h => (h.isHolomorphicallyConvex ho).exists_domainOfExistence ho,
    fun ⟨_, hf⟩ => hf.isDomainOfHolomorphy⟩

/-- Convex open subsets of finite-dimensional complex normed spaces are holomorphically convex.
This deduction uses the separating-hyperplane example and Thullen's lemma. -/
theorem isHolomorphicallyConvex_of_convex (hU : Convex ℝ U) (ho : IsOpen U) :
    IsHolomorphicallyConvex U := (isDomainOfHolomorphy_of_convex hU ho).isHolomorphicallyConvex ho

end General

variable {n : ℕ} {U : Set (Fin n → ℂ)}

/-- Exact preservation of compact hull boundary distance characterizes domains of holomorphy, by the
equivalence with holomorphic convexity. -/
theorem isDomainOfHolomorphy_iff_hasHolomorphicHullDistanceProperty (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ HasHolomorphicHullDistanceProperty U :=
  ⟨fun h => h.hasHolomorphicHullDistanceProperty ho,
    fun h => (h.isHolomorphicallyConvex ho).isDomainOfHolomorphy ho⟩

/-- The uniform polydisc-radius formulation is another Cartan–Thullen characterization. -/
theorem isDomainOfHolomorphy_iff_hasHolomorphicHullRadiusProperty (ho : IsOpen U) :
    IsDomainOfHolomorphy U ↔ HasHolomorphicHullRadiusProperty U :=
  ⟨fun h => h.hasHolomorphicHullRadiusProperty ho,
    fun h => (h.isHolomorphicallyConvex ho).isDomainOfHolomorphy ho⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
