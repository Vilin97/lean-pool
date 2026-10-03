/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Calculus

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Closed second-order semijets

This file contains closed superjets, closed subjets, and closure-induction
principles for the closed semijet graph.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- The graph whose closure defines the closed superjet. -/
def SuperjetGraph (C : Set (Point n)) (u : Point n -> Real) :
    Set ((Point n × Real) × Jet n) :=
  {z | z.1.1 ∈ C ∧ z.1.2 = u z.1.1 ∧ z.2 ∈ Superjet C u z.1.1}

/-- The graph whose closure defines the closed subjet. -/
def SubjetGraph (C : Set (Point n)) (u : Point n -> Real) :
    Set ((Point n × Real) × Jet n) :=
  {z | z.1.1 ∈ C ∧ z.1.2 = u z.1.1 ∧ z.2 ∈ Subjet C u z.1.1}

/--
A superjet graph point over a smaller set is a superjet graph point over a
larger set when the two domains have the same germ at the base point.
-/
theorem mem_superjetGraph_of_mem_of_nhdsWithin_eq
    {K C : Set (Point n)} {u : Point n -> Real}
    {z : (Point n × Real) × Jet n}
    (hKC : K ⊆ C) (hnhds : nhdsWithin z.1.1 K = nhdsWithin z.1.1 C)
    (hz : z ∈ SuperjetGraph K u) :
    z ∈ SuperjetGraph C u := by
  rcases z with ⟨⟨x, r⟩, J⟩
  rcases hz with ⟨hxK, hr, hJ⟩
  exact ⟨hKC hxK, hr, by simpa [superjet_congr_nhdsWithin hnhds] using hJ⟩

/--
A subjet graph point over a smaller set is a subjet graph point over a larger
set when the two domains have the same germ at the base point.
-/
theorem mem_subjetGraph_of_mem_of_nhdsWithin_eq
    {K C : Set (Point n)} {u : Point n -> Real}
    {z : (Point n × Real) × Jet n}
    (hKC : K ⊆ C) (hnhds : nhdsWithin z.1.1 K = nhdsWithin z.1.1 C)
    (hz : z ∈ SubjetGraph K u) :
    z ∈ SubjetGraph C u := by
  rcases z with ⟨⟨x, r⟩, J⟩
  rcases hz with ⟨hxK, hr, hJ⟩
  exact ⟨hKC hxK, hr, by simpa [subjet_congr_nhdsWithin hnhds] using hJ⟩

private theorem exists_nhds_forall_mem_nhdsWithin_of_mem_nhdsWithin
    {C K : Set (Point n)} {x : Point n}
    (hK : K ∈ nhdsWithin x C) :
    ∃ U ∈ nhds x, ∀ z : Point n, z ∈ U -> z ∈ C -> K ∈ nhdsWithin z C := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hK with ⟨U, hU, hUC⟩
  refine ⟨interior U, interior_mem_nhds.2 hU, ?_⟩
  intro z hzU _hzC
  have hUnhds : interior U ∈ nhds z := isOpen_interior.mem_nhds hzU
  exact mem_of_superset (inter_mem_nhdsWithin C hUnhds) fun y hy =>
    hUC ⟨interior_subset hy.2, hy.1⟩

/--
The closed superjet `\bar J^{2,+}_C u(x)`.

Following CIL, the graph being closed records triples `(x, u x, J)`, so the
extra convergence condition on the values of `u` is part of the definition.
-/
def ClosedSuperjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) : Set (Jet n) :=
  {J | ((x, u x), J) ∈ closure (SuperjetGraph C u)}

/--
The closed subjet `\bar J^{2,-}_C u(x)`.

As for `ClosedSuperjet`, closing the graph of `(x, u x, J)` encodes the
convergence of both base points and function values.
-/
def ClosedSubjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) : Set (Jet n) :=
  {J | ((x, u x), J) ∈ closure (SubjetGraph C u)}

/--
Closed superjets on a relative neighborhood are closed superjets on the
ambient domain.

In quantified mathematical form, if `K ⊆ C`, `K ∈ nhdsWithin x C`, and
`J ∈ \overline J^{2,+}_K u(x)`, then
`J ∈ \overline J^{2,+}_C u(x)`.
-/
theorem closedSuperjet_of_closedSuperjet_of_mem_nhdsWithin
    {K C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hKC : K ⊆ C) (hKnhds : K ∈ nhdsWithin x C)
    (hJ : J ∈ ClosedSuperjet K u x) :
    J ∈ ClosedSuperjet C u x := by
  rcases exists_nhds_forall_mem_nhdsWithin_of_mem_nhdsWithin hKnhds with
    ⟨U, hU, hUprop⟩
  change ((x, u x), J) ∈ closure (SuperjetGraph C u)
  rw [mem_closure_iff_nhds]
  intro W hW
  let baseNear : Set ((Point n × Real) × Jet n) := {z | z.1.1 ∈ U}
  have hbaseNear : baseNear ∈ nhds ((x, u x), J) := by
    have hbase : Continuous fun z : (Point n × Real) × Jet n => z.1.1 :=
      continuous_fst.comp continuous_fst
    exact hbase.continuousAt hU
  have hJclosure : ((x, u x), J) ∈ closure (SuperjetGraph K u) := hJ
  rw [mem_closure_iff_nhds] at hJclosure
  rcases hJclosure (W ∩ baseNear) (inter_mem hW hbaseNear) with
    ⟨z, hzW, hzGraphK⟩
  have hzC : z.1.1 ∈ C := hKC hzGraphK.1
  have hzKnhds : K ∈ nhdsWithin z.1.1 C := hUprop z.1.1 hzW.2 hzC
  have hnhds : nhdsWithin z.1.1 K = nhdsWithin z.1.1 C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hzKnhds
  exact ⟨z, hzW.1, mem_superjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hzGraphK⟩

/--
Closed subjets on a relative neighborhood are closed subjets on the ambient
domain.

In quantified mathematical form, if `K ⊆ C`, `K ∈ nhdsWithin x C`, and
`J ∈ \overline J^{2,-}_K u(x)`, then
`J ∈ \overline J^{2,-}_C u(x)`.
-/
theorem closedSubjet_of_closedSubjet_of_mem_nhdsWithin
    {K C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hKC : K ⊆ C) (hKnhds : K ∈ nhdsWithin x C)
    (hJ : J ∈ ClosedSubjet K u x) :
    J ∈ ClosedSubjet C u x := by
  rcases exists_nhds_forall_mem_nhdsWithin_of_mem_nhdsWithin hKnhds with
    ⟨U, hU, hUprop⟩
  change ((x, u x), J) ∈ closure (SubjetGraph C u)
  rw [mem_closure_iff_nhds]
  intro W hW
  let baseNear : Set ((Point n × Real) × Jet n) := {z | z.1.1 ∈ U}
  have hbaseNear : baseNear ∈ nhds ((x, u x), J) := by
    have hbase : Continuous fun z : (Point n × Real) × Jet n => z.1.1 :=
      continuous_fst.comp continuous_fst
    exact hbase.continuousAt hU
  have hJclosure : ((x, u x), J) ∈ closure (SubjetGraph K u) := hJ
  rw [mem_closure_iff_nhds] at hJclosure
  rcases hJclosure (W ∩ baseNear) (inter_mem hW hbaseNear) with
    ⟨z, hzW, hzGraphK⟩
  have hzC : z.1.1 ∈ C := hKC hzGraphK.1
  have hzKnhds : K ∈ nhdsWithin z.1.1 C := hUprop z.1.1 hzW.2 hzC
  have hnhds : nhdsWithin z.1.1 K = nhdsWithin z.1.1 C :=
    nhdsWithin_eq_of_subset_of_mem_nhdsWithin hKC hzKnhds
  exact ⟨z, hzW.1, mem_subjetGraph_of_mem_of_nhdsWithin_eq hKC hnhds hzGraphK⟩

theorem superjet_subset_closedSuperjet {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} (hx : x ∈ C) :
    Superjet C u x ⊆ ClosedSuperjet C u x := by
  intro J hJ
  exact subset_closure ⟨hx, rfl, hJ⟩

theorem subjet_subset_closedSubjet {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} (hx : x ∈ C) :
    Subjet C u x ⊆ ClosedSubjet C u x := by
  intro J hJ
  exact subset_closure ⟨hx, rfl, hJ⟩

/--
Ordinary superjets are preserved by translating the domain.

In quantified mathematical form, if `(p, X) ∈ J^{2,+}_K (x ↦ u(x0+x))(x)`,
then `(p, X) ∈ J^{2,+}_{x0+K} u(x0+x)`, where
`x0+K = {x0 + z | z ∈ K}`.
-/
theorem superjet_translate_add_left
    {K : Set (Point n)} {u : Point n -> Real} {x0 x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet K (fun y : Point n => u (x0 + y)) x) :
    J ∈ Superjet ((fun y : Point n => x0 + y) '' K) u (x0 + x) := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  let T : Point n -> Point n := fun y => x0 + y
  let S : Point n -> Point n := fun y => y - x0
  have hS_tendsto :
      Tendsto S (nhdsWithin (x0 + x) ((fun y : Point n => x0 + y) '' K))
        (nhdsWithin x K) := by
    have hforward :
        Filter.map T (nhdsWithin x K) =
          nhdsWithin (x0 + x) ((fun y : Point n => x0 + y) '' K) := by
      simpa only [T, Homeomorph.coe_addLeft] using
        (Homeomorph.addLeft x0).isEmbedding.map_nhdsWithin_eq K x
    have hST : Tendsto (S ∘ T) (nhdsWithin x K) (nhdsWithin x K) := by
      have hcomp : S ∘ T = id := by
        funext y
        ext i
        simp [S, T, sub_eq_add_neg, add_assoc]
      simpa [hcomp] using (tendsto_id : Tendsto id (nhdsWithin x K) (nhdsWithin x K))
    have hSmap : Tendsto S (Filter.map T (nhdsWithin x K)) (nhdsWithin x K) :=
      Filter.tendsto_map' hST
    simpa [hforward] using hSmap
  refine ⟨fun y => rho (S y), ?_, ?_⟩
  · have hcomp := hrho.comp_tendsto hS_tendsto
    refine hcomp.congr' (Filter.Eventually.of_forall fun y => rfl)
      (Filter.Eventually.of_forall ?_)
    intro y
    have hdiff : S y - x = y - (x0 + x) := by
      ext i
      simp [S, sub_eq_add_neg, add_assoc, add_comm]
    simp [hdiff]
  · have hineq' := hS_tendsto.eventually hineq
    filter_upwards [hineq'] with y hy
    have hbase : x0 + S y = y := by
      ext i
      simp [S, sub_eq_add_neg]
    have hquad :
        quadraticModel x (u (x0 + x)) J.gradient J.hessian (S y) =
          quadraticModel (x0 + x) (u (x0 + x)) J.gradient J.hessian y := by
      simp [quadraticModel, S, sub_eq_add_neg, add_assoc, add_comm]
    simpa [hbase, hquad] using hy

/--
Ordinary subjets are preserved by translating the domain.

In quantified mathematical form, if `(p, X) ∈ J^{2,-}_K (x ↦ u(x0+x))(x)`,
then `(p, X) ∈ J^{2,-}_{x0+K} u(x0+x)`, where
`x0+K = {x0 + z | z ∈ K}`.
-/
theorem subjet_translate_add_left
    {K : Set (Point n)} {u : Point n -> Real} {x0 x : Point n} {J : Jet n}
    (hJ : J ∈ Subjet K (fun y : Point n => u (x0 + y)) x) :
    J ∈ Subjet ((fun y : Point n => x0 + y) '' K) u (x0 + x) := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  let T : Point n -> Point n := fun y => x0 + y
  let S : Point n -> Point n := fun y => y - x0
  have hS_tendsto :
      Tendsto S (nhdsWithin (x0 + x) ((fun y : Point n => x0 + y) '' K))
        (nhdsWithin x K) := by
    have hforward :
        Filter.map T (nhdsWithin x K) =
          nhdsWithin (x0 + x) ((fun y : Point n => x0 + y) '' K) := by
      simpa only [T, Homeomorph.coe_addLeft] using
        (Homeomorph.addLeft x0).isEmbedding.map_nhdsWithin_eq K x
    have hST : Tendsto (S ∘ T) (nhdsWithin x K) (nhdsWithin x K) := by
      have hcomp : S ∘ T = id := by
        funext y
        ext i
        simp [S, T, sub_eq_add_neg, add_assoc]
      simpa [hcomp] using (tendsto_id : Tendsto id (nhdsWithin x K) (nhdsWithin x K))
    have hSmap : Tendsto S (Filter.map T (nhdsWithin x K)) (nhdsWithin x K) :=
      Filter.tendsto_map' hST
    simpa [hforward] using hSmap
  refine ⟨fun y => rho (S y), ?_, ?_⟩
  · have hcomp := hrho.comp_tendsto hS_tendsto
    refine hcomp.congr' (Filter.Eventually.of_forall fun y => rfl)
      (Filter.Eventually.of_forall ?_)
    intro y
    have hdiff : S y - x = y - (x0 + x) := by
      ext i
      simp [S, sub_eq_add_neg, add_assoc, add_comm]
    simp [hdiff]
  · have hineq' := hS_tendsto.eventually hineq
    filter_upwards [hineq'] with y hy
    have hbase : x0 + S y = y := by
      ext i
      simp [S, sub_eq_add_neg]
    have hquad :
        quadraticModel x (u (x0 + x)) J.gradient J.hessian (S y) =
          quadraticModel (x0 + x) (u (x0 + x)) J.gradient J.hessian y := by
      simp [quadraticModel, S, sub_eq_add_neg, add_assoc, add_comm]
    simpa [hbase, hquad] using hy

/--
Closed superjets are preserved by translating the domain.

In quantified mathematical form, if
`(p, X) ∈ \overline J^{2,+}_K (x ↦ u(x0+x))(x)`, then
`(p, X) ∈ \overline J^{2,+}_{x0+K} u(x0+x)`.
-/
theorem closedSuperjet_translate_add_left
    {K : Set (Point n)} {u : Point n -> Real} {x0 x : Point n} {J : Jet n}
    (hJ : J ∈ ClosedSuperjet K (fun y : Point n => u (x0 + y)) x) :
    J ∈ ClosedSuperjet ((fun y : Point n => x0 + y) '' K) u (x0 + x) := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => (((fun y : Point n => x0 + y) z.1.1, z.1.2), z.2)
  have hshift_cont : Continuous shift := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => x0 + z.1.1) :=
      continuous_const.add (continuous_fst.comp continuous_fst)
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2) :=
      continuous_snd.comp continuous_fst
    exact (hbase.prodMk hvalue).prodMk continuous_snd
  have hshift_mem :
      shift ((x, (fun y : Point n => u (x0 + y)) x), J) ∈
        closure (shift '' SuperjetGraph K (fun y : Point n => u (x0 + y))) :=
    image_closure_subset_closure_image hshift_cont
      ⟨((x, (fun y : Point n => u (x0 + y)) x), J), hJ, rfl⟩
  have hsubset :
      shift '' SuperjetGraph K (fun y : Point n => u (x0 + y)) ⊆
        SuperjetGraph ((fun y : Point n => x0 + y) '' K) u := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, KJ⟩
    rcases hw with ⟨hyK, hr, hKJ⟩
    exact ⟨⟨y, hyK, rfl⟩, by simpa using hr,
      superjet_translate_add_left hKJ⟩
  change ((x0 + x, u (x0 + x)), J) ∈ closure (SuperjetGraph ((fun y : Point n => x0 + y) '' K) u)
  simpa only [shift, add_sub_cancel_right] using closure_mono hsubset hshift_mem

/--
Closed subjets are preserved by translating the domain.

In quantified mathematical form, if
`(p, X) ∈ \overline J^{2,-}_K (x ↦ u(x0+x))(x)`, then
`(p, X) ∈ \overline J^{2,-}_{x0+K} u(x0+x)`.
-/
theorem closedSubjet_translate_add_left
    {K : Set (Point n)} {u : Point n -> Real} {x0 x : Point n} {J : Jet n}
    (hJ : J ∈ ClosedSubjet K (fun y : Point n => u (x0 + y)) x) :
    J ∈ ClosedSubjet ((fun y : Point n => x0 + y) '' K) u (x0 + x) := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => (((fun y : Point n => x0 + y) z.1.1, z.1.2), z.2)
  have hshift_cont : Continuous shift := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => x0 + z.1.1) :=
      continuous_const.add (continuous_fst.comp continuous_fst)
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2) :=
      continuous_snd.comp continuous_fst
    exact (hbase.prodMk hvalue).prodMk continuous_snd
  have hshift_mem :
      shift ((x, (fun y : Point n => u (x0 + y)) x), J) ∈
        closure (shift '' SubjetGraph K (fun y : Point n => u (x0 + y))) :=
    image_closure_subset_closure_image hshift_cont
      ⟨((x, (fun y : Point n => u (x0 + y)) x), J), hJ, rfl⟩
  have hsubset :
      shift '' SubjetGraph K (fun y : Point n => u (x0 + y)) ⊆
        SubjetGraph ((fun y : Point n => x0 + y) '' K) u := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, KJ⟩
    rcases hw with ⟨hyK, hr, hKJ⟩
    exact ⟨⟨y, hyK, rfl⟩, by simpa using hr,
      subjet_translate_add_left hKJ⟩
  change ((x0 + x, u (x0 + x)), J) ∈ closure (SubjetGraph ((fun y : Point n => x0 + y) '' K) u)
  simpa only [shift, add_sub_cancel_right] using closure_mono hsubset hshift_mem

/-- For fixed base point, the closed superjet fiber is topologically closed. -/
theorem isClosed_closedSuperjet {C : Set (Point n)} {u : Point n -> Real} {x : Point n} :
    IsClosed (ClosedSuperjet C u x) := by
  unfold ClosedSuperjet
  exact isClosed_closure.preimage (by continuity)

/-- For fixed base point, the closed subjet fiber is topologically closed. -/
theorem isClosed_closedSubjet {C : Set (Point n)} {u : Point n -> Real} {x : Point n} :
    IsClosed (ClosedSubjet C u x) := by
  unfold ClosedSubjet
  exact isClosed_closure.preimage (by continuity)

/--
A limit of closed-superjet graph points is again in the closed-superjet graph.

In quantified mathematical form, suppose `xᵢ -> x`, `u xᵢ -> u x`, and
`Jᵢ -> J` along a nontrivial filter. If for all indices in a set belonging to
that filter one has `Jᵢ ∈ \overline J^{2,+}_C u(xᵢ)`, then
`J ∈ \overline J^{2,+}_C u(x)`.
-/
theorem closedSuperjet_of_tendsto_closedSuperjet
    {α : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {l : Filter α} [l.NeBot]
    {x : Point n} {J : Jet n} {xᵢ : α -> Point n} {Jᵢ : α -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => u (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hmem : ∀ᶠ i in l, Jᵢ i ∈ ClosedSuperjet C u (xᵢ i)) :
    J ∈ ClosedSuperjet C u x := by
  have hz :
      Tendsto (fun i : α => ((xᵢ i, u (xᵢ i)), Jᵢ i))
        l (nhds ((x, u x), J)) :=
    (hx.prodMk_nhds hu).prodMk_nhds hJ
  exact isClosed_closure.mem_of_tendsto hz hmem

/--
A limit of closed-subjet graph points is again in the closed-subjet graph.

In quantified mathematical form, suppose `xᵢ -> x`, `u xᵢ -> u x`, and
`Jᵢ -> J` along a nontrivial filter. If for all indices in a set belonging to
that filter one has `Jᵢ ∈ \overline J^{2,-}_C u(xᵢ)`, then
`J ∈ \overline J^{2,-}_C u(x)`.
-/
theorem closedSubjet_of_tendsto_closedSubjet
    {α : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {l : Filter α} [l.NeBot]
    {x : Point n} {J : Jet n} {xᵢ : α -> Point n} {Jᵢ : α -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => u (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hmem : ∀ᶠ i in l, Jᵢ i ∈ ClosedSubjet C u (xᵢ i)) :
    J ∈ ClosedSubjet C u x := by
  have hz :
      Tendsto (fun i : α => ((xᵢ i, u (xᵢ i)), Jᵢ i))
        l (nhds ((x, u x), J)) :=
    (hx.prodMk_nhds hu).prodMk_nhds hJ
  exact isClosed_closure.mem_of_tendsto hz hmem

/--
Subtracting a constant from a function preserves closed superjet membership.

In quantified mathematical form, for every real number `δ`, if
`J ∈ \bar J^{2,+}_C u(x)`, then
`J ∈ \bar J^{2,+}_C (u - δ)(x)`.
-/
theorem closedSuperjet_sub_const_of_closedSuperjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} {δ : Real}
    (hJ : J ∈ ClosedSuperjet C u x) :
    J ∈ ClosedSuperjet C (fun y => u y - δ) x := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, z.1.2 - δ), z.2)
  have hshift_cont : Continuous shift := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
      continuous_fst.comp continuous_fst
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2 - δ) :=
      (continuous_snd.comp continuous_fst).sub continuous_const
    have hleft : Continuous (fun z : (Point n × Real) × Jet n => (z.1.1, z.1.2 - δ)) :=
      hbase.prodMk hvalue
    exact hleft.prodMk continuous_snd
  have hshift_mem :
      shift ((x, u x), J) ∈ closure (shift '' SuperjetGraph C u) :=
    image_closure_subset_closure_image hshift_cont ⟨((x, u x), J), hJ, rfl⟩
  have hsubset :
      shift '' SuperjetGraph C u ⊆ SuperjetGraph C (fun y => u y - δ) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y at hr
    change K ∈ Superjet C u y at hK
    subst r
    exact ⟨hyC, rfl, (superjet_sub_const_iff).2 hK⟩
  exact closure_mono hsubset hshift_mem

/--
Subtracting a constant from a function does not change its closed superjet
fibers.

In quantified mathematical form, for every real number `δ`,
`J ∈ \bar J^{2,+}_C (u - δ)(x)` if and only if
`J ∈ \bar J^{2,+}_C u(x)`.
-/
theorem closedSuperjet_sub_const_iff
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} {δ : Real} :
    J ∈ ClosedSuperjet C (fun y => u y - δ) x ↔ J ∈ ClosedSuperjet C u x := by
  constructor
  · intro hJ
    have h :=
      closedSuperjet_sub_const_of_closedSuperjet
        (u := fun y => u y - δ) (δ := -δ) (x := x) (J := J) hJ
    simpa using h
  · intro hJ
    exact closedSuperjet_sub_const_of_closedSuperjet hJ

/--
Subtracting a function with a second-order expansion at every point of `C`
pulls back closed superjets of `u + φ` to closed superjets of `u`.

In quantified mathematical form, suppose that for every `y ∈ C`, the function
`φ` has second-order expansion within `C` at `y` with jet `A y`, and suppose
that `φ` and `A` are continuous. If
`J ∈ \bar J^{2,+}_C (u + φ)(x)`, then
`J - A x ∈ \bar J^{2,+}_C u(x)`.
-/
theorem closedSuperjet_sub_of_add_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    {A : Point n -> Jet n}
    (hφ : ∀ y : Point n, y ∈ C -> HasSecondOrderExpansionWithin C φ y (A y))
    (hφ_cont : Continuous φ) (hA_cont : Continuous A)
    (hJ : J ∈ ClosedSuperjet C (fun y => u y + φ y) x) :
    J - A x ∈ ClosedSuperjet C u x := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, z.1.2 - φ z.1.1), z.2 - A z.1.1)
  have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hshift_cont : Continuous shift := by
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2 - φ z.1.1) :=
      (continuous_snd.comp continuous_fst).sub (hφ_cont.comp hbase)
    have hleft : Continuous
        (fun z : (Point n × Real) × Jet n => (z.1.1, z.1.2 - φ z.1.1)) :=
      hbase.prodMk hvalue
    have hright : Continuous
        (fun z : (Point n × Real) × Jet n => z.2 - A z.1.1) :=
      by
        apply continuous_induced_rng.mpr
        change Continuous fun z : (Point n × Real) × Jet n =>
          ((z.2 - A z.1.1).gradient, (z.2 - A z.1.1).hessian)
        have hgrad : Continuous fun z : (Point n × Real) × Jet n =>
            z.2.gradient - (A z.1.1).gradient :=
          (Jet.continuous_gradient.comp continuous_snd).sub
            (Jet.continuous_gradient.comp (hA_cont.comp hbase))
        have hhess : Continuous fun z : (Point n × Real) × Jet n =>
            z.2.hessian - (A z.1.1).hessian :=
          (Jet.continuous_hessian.comp continuous_snd).sub
            (Jet.continuous_hessian.comp (hA_cont.comp hbase))
        simpa using Continuous.prodMk hgrad hhess
    exact hleft.prodMk hright
  have hshift_mem :
      shift ((x, (fun y => u y + φ y) x), J) ∈
        closure (shift '' SuperjetGraph C (fun y => u y + φ y)) :=
    image_closure_subset_closure_image hshift_cont
      ⟨((x, (fun y => u y + φ y) x), J), hJ, rfl⟩
  have hsubset :
      shift '' SuperjetGraph C (fun y => u y + φ y) ⊆ SuperjetGraph C u := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y + φ y at hr
    change K ∈ Superjet C (fun y => u y + φ y) y at hK
    subst r
    exact ⟨hyC, by ring, superjet_sub_of_add_hasSecondOrderExpansionWithin hK (hφ y hyC)⟩
  change ((x, u x), J - A x) ∈ closure (SuperjetGraph C u)
  simpa only [shift, add_sub_cancel_right] using closure_mono hsubset hshift_mem

/--
Subtracting a constant from a function preserves closed subjet membership.

In quantified mathematical form, for every real number `δ`, if
`J ∈ \bar J^{2,-}_C u(x)`, then
`J ∈ \bar J^{2,-}_C (u - δ)(x)`.
-/
theorem closedSubjet_sub_const_of_closedSubjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} {δ : Real}
    (hJ : J ∈ ClosedSubjet C u x) :
    J ∈ ClosedSubjet C (fun y => u y - δ) x := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, z.1.2 - δ), z.2)
  have hshift_cont : Continuous shift := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
      continuous_fst.comp continuous_fst
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2 - δ) :=
      (continuous_snd.comp continuous_fst).sub continuous_const
    have hleft : Continuous (fun z : (Point n × Real) × Jet n => (z.1.1, z.1.2 - δ)) :=
      hbase.prodMk hvalue
    exact hleft.prodMk continuous_snd
  have hshift_mem :
      shift ((x, u x), J) ∈ closure (shift '' SubjetGraph C u) :=
    image_closure_subset_closure_image hshift_cont ⟨((x, u x), J), hJ, rfl⟩
  have hsubset :
      shift '' SubjetGraph C u ⊆ SubjetGraph C (fun y => u y - δ) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y at hr
    change K ∈ Subjet C u y at hK
    subst r
    exact ⟨hyC, rfl, (subjet_sub_const_iff).2 hK⟩
  exact closure_mono hsubset hshift_mem

/--
Subtracting a constant from a function does not change its closed subjet
fibers.

In quantified mathematical form, for every real number `δ`,
`J ∈ \bar J^{2,-}_C (u - δ)(x)` if and only if
`J ∈ \bar J^{2,-}_C u(x)`.
-/
theorem closedSubjet_sub_const_iff
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} {δ : Real} :
    J ∈ ClosedSubjet C (fun y => u y - δ) x ↔ J ∈ ClosedSubjet C u x := by
  constructor
  · intro hJ
    have h :=
      closedSubjet_sub_const_of_closedSubjet
        (u := fun y => u y - δ) (δ := -δ) (x := x) (J := J) hJ
    simpa using h
  · intro hJ
    exact closedSubjet_sub_const_of_closedSubjet hJ

/--
Subtracting a function with a second-order expansion at every point of `C`
pulls back closed subjets of `u + φ` to closed subjets of `u`.

In quantified mathematical form, suppose that for every `y ∈ C`, the function
`φ` has second-order expansion within `C` at `y` with jet `A y`, and suppose
that `φ` and `A` are continuous. If
`J ∈ \bar J^{2,-}_C (u + φ)(x)`, then
`J - A x ∈ \bar J^{2,-}_C u(x)`.
-/
theorem closedSubjet_sub_of_add_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    {A : Point n -> Jet n}
    (hφ : ∀ y : Point n, y ∈ C -> HasSecondOrderExpansionWithin C φ y (A y))
    (hφ_cont : Continuous φ) (hA_cont : Continuous A)
    (hJ : J ∈ ClosedSubjet C (fun y => u y + φ y) x) :
    J - A x ∈ ClosedSubjet C u x := by
  let shift : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, z.1.2 - φ z.1.1), z.2 - A z.1.1)
  have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hshift_cont : Continuous shift := by
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => z.1.2 - φ z.1.1) :=
      (continuous_snd.comp continuous_fst).sub (hφ_cont.comp hbase)
    have hleft : Continuous
        (fun z : (Point n × Real) × Jet n => (z.1.1, z.1.2 - φ z.1.1)) :=
      hbase.prodMk hvalue
    have hright : Continuous
        (fun z : (Point n × Real) × Jet n => z.2 - A z.1.1) :=
      by
        apply continuous_induced_rng.mpr
        change Continuous fun z : (Point n × Real) × Jet n =>
          ((z.2 - A z.1.1).gradient, (z.2 - A z.1.1).hessian)
        have hgrad : Continuous fun z : (Point n × Real) × Jet n =>
            z.2.gradient - (A z.1.1).gradient :=
          (Jet.continuous_gradient.comp continuous_snd).sub
            (Jet.continuous_gradient.comp (hA_cont.comp hbase))
        have hhess : Continuous fun z : (Point n × Real) × Jet n =>
            z.2.hessian - (A z.1.1).hessian :=
          (Jet.continuous_hessian.comp continuous_snd).sub
            (Jet.continuous_hessian.comp (hA_cont.comp hbase))
        simpa using Continuous.prodMk hgrad hhess
    exact hleft.prodMk hright
  have hshift_mem :
      shift ((x, (fun y => u y + φ y) x), J) ∈
        closure (shift '' SubjetGraph C (fun y => u y + φ y)) :=
    image_closure_subset_closure_image hshift_cont
      ⟨((x, (fun y => u y + φ y) x), J), hJ, rfl⟩
  have hsubset :
      shift '' SubjetGraph C (fun y => u y + φ y) ⊆ SubjetGraph C u := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y + φ y at hr
    change K ∈ Subjet C (fun y => u y + φ y) y at hK
    subst r
    exact ⟨hyC, by ring, subjet_sub_of_add_hasSecondOrderExpansionWithin hK (hφ y hyC)⟩
  change ((x, u x), J - A x) ∈ closure (SubjetGraph C u)
  simpa only [shift, add_sub_cancel_right] using closure_mono hsubset hshift_mem

/--
Closed subjets are dual to closed superjets under negation.

In standard mathematical terms, `(p, X) ∈ \bar J^{2,-}_C u(x)` implies
`(-p, -X) ∈ \bar J^{2,+}_C (-u)(x)`.
-/
theorem closedSubjet_neg_to_closedSuperjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ ClosedSubjet C u x) :
    J.neg ∈ ClosedSuperjet C (fun y => -u y) x := by
  let negGraph : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, -z.1.2), z.2.neg)
  have hneg_cont : Continuous negGraph := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
      continuous_fst.comp continuous_fst
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => -z.1.2) :=
      (continuous_snd.comp continuous_fst).neg
    have hleft : Continuous (fun z : (Point n × Real) × Jet n => (z.1.1, -z.1.2)) :=
      hbase.prodMk hvalue
    have hgrad : Continuous fun z : (Point n × Real) × Jet n => z.2.neg.gradient :=
      (Jet.continuous_gradient.comp continuous_snd).neg
    have hhess : Continuous fun z : (Point n × Real) × Jet n => z.2.neg.hessian :=
      (Jet.continuous_hessian.comp continuous_snd).neg
    have hjet : Continuous fun z : (Point n × Real) × Jet n => z.2.neg := by
      rw [continuous_iff_continuousAt]
      intro z
      rw [ContinuousAt, nhds_induced, Filter.tendsto_comap_iff]
      exact (hgrad.continuousAt.prodMk_nhds hhess.continuousAt)
    exact hleft.prodMk hjet
  have hneg_mem :
      negGraph ((x, u x), J) ∈ closure (negGraph '' SubjetGraph C u) :=
    image_closure_subset_closure_image hneg_cont ⟨((x, u x), J), hJ, rfl⟩
  have hsubset :
      negGraph '' SubjetGraph C u ⊆ SuperjetGraph C (fun y => -u y) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y at hr
    change K ∈ Subjet C u y at hK
    subst r
    exact ⟨hyC, rfl, (subjet_neg_iff_superjet (J := K)).mp hK⟩
  exact closure_mono hsubset hneg_mem

/--
Closed superjets are dual to closed subjets under negation.

In standard mathematical terms, `(p, X) ∈ \bar J^{2,+}_C u(x)` implies
`(-p, -X) ∈ \bar J^{2,-}_C (-u)(x)`.
-/
theorem closedSuperjet_neg_to_closedSubjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ ClosedSuperjet C u x) :
    J.neg ∈ ClosedSubjet C (fun y => -u y) x := by
  let negGraph : ((Point n × Real) × Jet n) -> ((Point n × Real) × Jet n) :=
    fun z => ((z.1.1, -z.1.2), z.2.neg)
  have hneg_cont : Continuous negGraph := by
    have hbase : Continuous (fun z : (Point n × Real) × Jet n => z.1.1) :=
      continuous_fst.comp continuous_fst
    have hvalue : Continuous (fun z : (Point n × Real) × Jet n => -z.1.2) :=
      (continuous_snd.comp continuous_fst).neg
    have hleft : Continuous (fun z : (Point n × Real) × Jet n => (z.1.1, -z.1.2)) :=
      hbase.prodMk hvalue
    have hgrad : Continuous fun z : (Point n × Real) × Jet n => z.2.neg.gradient :=
      (Jet.continuous_gradient.comp continuous_snd).neg
    have hhess : Continuous fun z : (Point n × Real) × Jet n => z.2.neg.hessian :=
      (Jet.continuous_hessian.comp continuous_snd).neg
    have hjet : Continuous fun z : (Point n × Real) × Jet n => z.2.neg := by
      rw [continuous_iff_continuousAt]
      intro z
      rw [ContinuousAt, nhds_induced, Filter.tendsto_comap_iff]
      exact (hgrad.continuousAt.prodMk_nhds hhess.continuousAt)
    exact hleft.prodMk hjet
  have hneg_mem :
      negGraph ((x, u x), J) ∈ closure (negGraph '' SuperjetGraph C u) :=
    image_closure_subset_closure_image hneg_cont ⟨((x, u x), J), hJ, rfl⟩
  have hsubset :
      negGraph '' SuperjetGraph C u ⊆ SubjetGraph C (fun y => -u y) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases w with ⟨⟨y, r⟩, K⟩
    rcases hw with ⟨hyC, hr, hK⟩
    change y ∈ C at hyC
    change r = u y at hr
    change K ∈ Superjet C u y at hK
    subst r
    exact ⟨hyC, rfl, (superjet_neg_iff_subjet (J := K)).mp hK⟩
  exact closure_mono hsubset hneg_mem

/--
Closed subjet membership is equivalent to closed superjet membership for the
negated function and negated jet.
-/
theorem closedSubjet_neg_iff_closedSuperjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} :
    J ∈ ClosedSubjet C u x ↔
      J.neg ∈ ClosedSuperjet C (fun y => -u y) x := by
  constructor
  · exact closedSubjet_neg_to_closedSuperjet
  · intro hJ
    have hdual :
        J.neg.neg ∈ ClosedSubjet C (fun y => -(-u y)) x :=
      closedSuperjet_neg_to_closedSubjet
        (C := C) (u := fun y => -u y) (x := x) (J := J.neg) hJ
    have hnegneg : J.neg.neg = J := by
      cases J
      simp [Jet.neg]
    simpa [hnegneg] using hdual

/--
Closed superjet membership is equivalent to closed subjet membership for the
negated function and negated jet.
-/
theorem closedSuperjet_neg_iff_closedSubjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n} :
    J ∈ ClosedSuperjet C u x ↔
      J.neg ∈ ClosedSubjet C (fun y => -u y) x := by
  constructor
  · exact closedSuperjet_neg_to_closedSubjet
  · intro hJ
    have hdual :
        J.neg.neg ∈ ClosedSuperjet C (fun y => -(-u y)) x :=
      closedSubjet_neg_to_closedSuperjet
        (C := C) (u := fun y => -u y) (x := x) (J := J.neg) hJ
    have hnegneg : J.neg.neg = J := by
      cases J
      simp [Jet.neg]
    simpa [hnegneg] using hdual

theorem closedSuperjet_induction {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {S : Set ((Point n × Real) × Jet n)}
    (hclosed : IsClosed S)
    (hgraph : forall y : Point n, y ∈ C -> forall K : Jet n, K ∈ Superjet C u y ->
      ((y, u y), K) ∈ S)
    (hJ : J ∈ ClosedSuperjet C u x) :
    ((x, u x), J) ∈ S := by
  exact closure_minimal
    (by
      intro z hz
      rcases z with ⟨⟨y, r⟩, K⟩
      rcases hz with ⟨hyC, hr, hK⟩
      change y ∈ C at hyC
      change r = u y at hr
      change K ∈ Superjet C u y at hK
      subst r
      exact hgraph y hyC K hK)
    hclosed hJ

theorem closedSubjet_induction {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {S : Set ((Point n × Real) × Jet n)}
    (hclosed : IsClosed S)
    (hgraph : forall y : Point n, y ∈ C -> forall K : Jet n, K ∈ Subjet C u y ->
      ((y, u y), K) ∈ S)
    (hJ : J ∈ ClosedSubjet C u x) :
    ((x, u x), J) ∈ S := by
  exact closure_minimal
    (by
      intro z hz
      rcases z with ⟨⟨y, r⟩, K⟩
      rcases hz with ⟨hyC, hr, hK⟩
      change y ∈ C at hyC
      change r = u y at hr
      change K ∈ Subjet C u y at hK
      subst r
      exact hgraph y hyC K hK)
    hclosed hJ

end ViscositySolns
