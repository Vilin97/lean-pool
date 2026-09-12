/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all Mathlib.Analysis.InnerProductSpace.Adjoint
import all Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Hopf problem: recognition · smale 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem Smale.FlowConstruction.forwardInvariant_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Icc 0 ε, F t x ∈ A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A := by
  intro x hx T hT
  let S : Set ℝ := {t | F t x ∈ A}
  have hS : IsClosed S := hA.preimage (F.continuous continuous_id continuous_const)
  have hzero : (0 : ℝ) ∈ S := by simpa only [S, Set.mem_ofPred_eq, F.map_zero_apply] using hx
  apply (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hzero hT
  intro s hs
  obtain ⟨ε, hε, hstay⟩ := hlocal (F s x) hs.1
  let δ := Min.min ε (T - s) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hs.2.2))
  have hδε : δ ≤ ε :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_left _ _)
  have hδT : δ ≤ T - s :=
    (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hs.2.2)))).trans (min_le_right _ _)
  refine ⟨s + δ, ?_, by linarith, by linarith⟩
  change F (s + δ) x ∈ A
  rw [add_comm s δ, F.map_add]
  exact hstay δ ⟨hδ.le, hδε⟩

private theorem Smale.FlowConstruction.forwardInvariant_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : x ∈ interior A) {t : ℝ} (ht : 0 ≤ t) : F t x ∈ interior A := by
  apply mem_interior.mpr
  refine ⟨F t '' interior A, ?_, (F.toHomeomorph t).isOpenMap _ isOpen_interior, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hforward y (interior_subset hy) t ht
  · exact ⟨x, hx, rfl⟩

private theorem Smale.FlowConstruction.interior_entry_of_local {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hlocal : ∀ x ∈ A, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior A) :
    ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A := by
  intro x hx t ht
  obtain ⟨ε, hε, hentry⟩ := hlocal x hx
  let δ := Min.min ε t / 2
  have hδ : 0 < δ := half_pos (lt_min hε ht)
  have hδε : δ ≤ ε := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_left _ _)
  have hδt : δ ≤ t := (half_le_self (le_of_lt (lt_min hε ht))).trans (min_le_right _ _)
  have hi := forwardInvariant_interior F hforward (hentry δ ⟨hδ, hδε⟩) (sub_nonneg.mpr hδt)
  rw [← F.map_add, sub_add_cancel] at hi
  exact hi

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_local_attachingUnion_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    {x : M} (hx : x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hAx : x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) :
    ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioc 0 ε,
        F t x ∈
          interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hmodel := (c.mem_attachingUnion_iff_model ρ hρ hblock hx).mp hAx
  have hαc : Continuous (fun t : ℝ => Smale.MorseHandle.descentFlow t (c.splitChart x)) :=
    Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const
  have hα₀ : Smale.MorseHandle.descentFlow 0 (c.splitChart x) = e x :=
    Smale.MorseHandle.descentFlow.map_zero_apply _
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), Smale.MorseHandle.descentFlow t (c.splitChart x) ∈ e.target :=
    hαc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hα₀ ▸ e.map_source hx))
  have hFc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
  have hsource : ∀ᶠ t in 𝓝 (0 : ℝ), F t x ∈ e.source :=
    hFc.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds
        (by
          rw [F.map_zero_apply]
          exact hx))
  have heqF := c.eventually_flow_eq_descentModel hV F hcurve hx heq
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.mp ((heqF.and htarget).and hsource)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  have hdist : Dist.dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  obtain ⟨⟨heqt, htar⟩, hsrc⟩ := hεall hdist
  apply c.mem_interior_attachingUnion_of_model ρ hρ hblock hsrc
  have hcoord : c.splitChart (F t x) = Smale.MorseHandle.descentFlow t (c.splitChart x) := by
    rw [heqt]
    exact e.right_inv htar
  rw [hcoord]
  exact Smale.MorseHandle.descentFlow_mem_interior_lower_union_handle hρ ht.1 hmodel

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.forwardInvariant_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 ≤ t → F t x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock) := by
  apply
    Smale.FlowConstruction.forwardInvariant_of_local F
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    left
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (Smale.MorseHandle.modelMap_mem_product hρ z))
    obtain ⟨ε, hε, hentry⟩ :=
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · rw [← hzero, F.map_zero_apply]
      exact Or.inr hx
    · exact interior_subset (hentry t ⟨hpos, ht.2⟩)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.interior_entry_attachingUnion {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x) :
    ∀ x ∈ {y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock),
      ∀ t : ℝ,
        0 < t →
          F t x ∈
            interior ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) := by
  apply
    Smale.FlowConstruction.interior_entry_of_local F
      (c.forwardInvariant_attachingUnion hf hV F hcurve hmono ρ hρ hblock hagreement)
  intro x hx
  rcases hx with hx | hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hlow : f (F t x) < f p - ρ ^ 2 := by
      change f x ≤ f p - ρ ^ 2 at hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1.le
        exact hle.trans_lt hlt
      · exact (hbottom x heq t ht.1).trans_le hx
    apply mem_interior.mpr
    exact
      ⟨{y | f y < f p - ρ ^ 2}, fun y hy => Or.inl (show f y ≤ f p - ρ ^ 2 from le_of_lt hy),
        isOpen_lt hf continuous_const, hlow⟩
  · have hxsource : x ∈ c.splitChart.source := by
      obtain ⟨z, rfl⟩ := hx
      exact
        c.splitChart.toOpenPartialHomeomorph.map_target
          (hblock (Smale.MorseHandle.modelMap_mem_product hρ z))
    exact
      c.exists_local_attachingUnion_entry hV F hcurve ρ hρ hblock hxsource (hagreement x hx)
        (Or.inr hx)

private def
    Smale.FlowConstruction.entryTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (A : Set X)
    (x : X) : ℝ :=
  InfSet.sInf {t : ℝ | 0 ≤ t ∧ F t x ∈ A}

private theorem
    Smale.FlowConstruction.entryTime_nonneg {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : 0 ≤ entryTime F A x :=
  le_csInf hx (fun _ ht => ht.1)

private theorem
    Smale.FlowConstruction.entryTime_le_of_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} {t : ℝ} (ht : 0 ≤ t) (hx : F t x ∈ A) : entryTime F A x ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, hx⟩

private theorem
    Smale.FlowConstruction.flow_entryTime_mem {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) :
    F (entryTime F A x) x ∈ A := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ F t x ∈ A} :=
    isClosed_Ici.inter (hA.preimage (F.continuous continuous_id continuous_const))
  exact (hclosed.csInf_mem hx ⟨0, fun _ hs => hs.1⟩).2

private theorem
    Smale.FlowConstruction.entryTime_eq_zero {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} {x : X} (hx : x ∈ A) : entryTime F A x = 0 := by
  have hhit : F 0 x ∈ A := by simpa only [F.map_zero_apply] using hx
  exact le_antisymm (entryTime_le_of_mem F le_rfl hhit) (entryTime_nonneg F ⟨0, le_rfl, hhit⟩)

private theorem
    Smale.FlowConstruction.entryTime_le_iff {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t) : entryTime F A x ≤ t ↔ F t x ∈ A := by
  constructor
  · intro h
    have hh := hforward _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_nonneg.mpr h)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  · exact entryTime_le_of_mem F ht

private theorem
    Smale.FlowConstruction.flow_mem_interior_of_entryTime_lt {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : entryTime F A x < t) : F t x ∈ interior A := by
  have hh := hentry _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_pos.mpr ht)
  rw [← F.map_add, sub_add_cancel] at hh
  exact hh

private theorem
    Smale.FlowConstruction.entryTime_eq_of_flow_mem_frontier {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {x : X} {t : ℝ} (ht : 0 ≤ t)
    (hfront : F t x ∈ frontier A) : entryTime F A x = t := by
  have hmem : F t x ∈ A := by simpa only [hA.closure_eq] using frontier_subset_closure hfront
  apply le_antisymm (entryTime_le_of_mem F ht hmem)
  apply le_of_not_gt
  intro hlt
  exact hfront.2 (flow_mem_interior_of_entryTime_lt F hA hentry ⟨t, ht, hmem⟩ hlt)

private theorem Smale.FlowConstruction.continuousOn_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) {B : Set X}
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : ContinuousOn (entryTime F A) B := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hneg : a < 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hneg.trans_le (entryTime_nonneg F (hhit y hy))
    · have ha₀ : 0 ≤ a := le_of_not_gt hneg
      have hnot : F a x ∉ A := fun h => not_le_of_gt ha (entryTime_le_of_mem F ha₀ h)
      have hevent : ∀ᶠ y in 𝓝 x, F a y ∉ A :=
        (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
          (hA.isOpen_compl.mem_nhds hnot)
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hevent] with y
        hy hya
      apply lt_of_not_ge
      intro hle
      exact hya ((entryTime_le_iff F hA hforward (hhit y hy) ha₀).mp hle)
  · intro b hb
    obtain ⟨t, hxt, htb⟩ := exists_between hb
    have ht₀ : 0 ≤ t := (entryTime_nonneg F (hhit x hx)).trans hxt.le
    have hi := flow_mem_interior_of_entryTime_lt F hA hentry (hhit x hx) hxt
    have hevent : ∀ᶠ y in 𝓝 x, F t y ∈ interior A :=
      (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hi)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hevent] with y hy
    exact (entryTime_le_of_mem F ht₀ (interior_subset hy)).trans_lt htb

private def Smale.FlowConstruction.entryRetraction {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : C(B, A)
    where
  toFun x := ⟨F (entryTime F A x.1) x.1, flow_entryTime_mem F hA (hhit x.1 x.2)⟩
  continuous_toFun :=
    (F.continuous
          (continuousOn_iff_continuous_domRestrict.mp
            (continuousOn_entryTime F hA hforward hentry hhit))
          continuous_subtype_val).subtype_mk
      _

private theorem Smale.FlowConstruction.entryRetraction_inclusion {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A B : Set X} (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B) (x : A) :
    entryRetraction F hA hforward hentry hhit (ContinuousMap.inclusion hsub x) = x := by
  apply Subtype.ext
  change F (entryTime F A x.1) x.1 = x.1
  rw [entryTime_eq_zero F x.2, F.map_zero_apply]

private def Smale.FlowConstruction.entryDeformation {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) :
    (ContinuousMap.id B).HomotopyRel
      ((ContinuousMap.inclusion hsub).comp (entryRetraction F hA hforward hentry hhit))
      {x : B | x.1 ∈ A}
    where
  toFun
    q :=
    ⟨F (q.1.1 * entryTime F A q.2.1) q.2.1,
      hregion q.2.1 q.2.2 _ (mul_nonneg q.1.2.1 (entryTime_nonneg F (hhit q.2.1 q.2.2)))⟩
  continuous_toFun :=
    (F.continuous
          ((continuous_subtype_val.comp continuous_fst).mul
            ((continuousOn_iff_continuous_domRestrict.mp
                  (continuousOn_entryTime F hA hforward hentry hhit)).comp
              continuous_snd))
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change F ((0 : ℝ) * entryTime F A x.1) x.1 = x.1
    rw [MulZeroClass.zero_mul, F.map_zero_apply]
  map_one_left
    x := by
    apply Subtype.ext
    change F ((1 : ℝ) * entryTime F A x.1) x.1 = F (entryTime F A x.1) x.1
    rw [one_mul]
  prop' u x
    hx := by
    apply Subtype.ext
    change F (u.1 * entryTime F A x.1) x.1 = x.1
    rw [entryTime_eq_zero F (A := A) (show x.1 ∈ A from hx), MulZeroClass.mul_zero,
      F.map_zero_apply]

private def
    Smale.FlowConstruction.entryHomotopyEquiv {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {A B : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) (hsub : A ⊆ B)
    (hregion : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B) : A ≃ₕ B
    where
  toFun := ContinuousMap.inclusion hsub
  invFun := entryRetraction F hA hforward hentry hhit
  left_inv := by
    have heq :
      (entryRetraction F hA hforward hentry hhit).comp (ContinuousMap.inclusion hsub) =
        ContinuousMap.id A := by
      apply ContinuousMap.ext
      intro x
      exact entryRetraction_inclusion F hA hforward hentry hhit hsub x
    rw [heq]
  right_inv := ⟨(entryDeformation F hA hforward hentry hhit hsub hregion).toHomotopy.symm⟩

private theorem
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (v (γ t))) t := by
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • v (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (v (γ t))
  exact map_smul _ _ _

private theorem Smale.FlowConstruction.exists_regularBandField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
                ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                    (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                  ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = φ (f x) := by
  let B := f '' Smale.ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((Smale.ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Set.Icc a b ⊆ Bᶜ := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hφB, W, hW, hAW, -, hφW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ ∘ f) := hφ.contMDiff.comp hf
  have hsupp : tsupport (φ ∘ f) ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hxφ := tsupport_comp_subset_preimage φ hf.continuous hx
    exact hφB hxφ ⟨x, hcrit, rfl⟩
  obtain ⟨V, hV, hVφ⟩ := exists_prescribedDerivativeField hf hχ hsupp
  exact ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩

private theorem Smale.FlowConstruction.exists_regularBandFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ) (F : Flow ℝ M),
      ContDiff ℝ ∞ φ ∧
        IsOpen W ∧
          Set.Icc a b ⊆ W ∧
            Set.EqOn φ (fun _ => 1) W ∧
              ∀ x t, HasDerivAt (fun s => f (F s x)) (φ (f (F t x))) t := by
  obtain ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩ := exists_regularBandField hf hband
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  refine ⟨φ, W, compactFlow hV₁, hφ, hW, hAW, hφW, ?_⟩
  intro x t
  have hd := hasDerivAt_comp_integralCurve hf (isMIntegralCurve_compactFlow hV₁ x) t
  rw [hVφ] at hd
  exact hd

private theorem Smale.FlowConstruction.flow_fixed_of_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hx : V x = 0)
    (t : ℝ) : F t x = x := by
  have heq :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve x) (isMIntegralCurve_const hx)
      (t₀ := 0) (F.map_zero_apply x)
  exact congrFun heq t

private theorem Smale.FlowConstruction.flow_preserves_regular {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) (t : ℝ) :
    F t x ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro hy
  have hfix := flow_fixed_of_zero hV F hcurve (hzero (F t x) hy) (-t)
  have hinv : F (-t) (F t x) = x := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have hxy : x = F t x := hinv.symm.trans hfix
  exact hx (hxy.symm ▸ hy)

private theorem Smale.FlowConstruction.antitone_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (x : M) : Antitone (fun t => f (F t x)) := by
  apply antitone_of_hasDerivAt_nonpos (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
  intro t
  change mvfderiv 𝓘(ℝ, E) f (F t x) (V (F t x)) ≤ 0
  by_cases ht : F t x ∈ Smale.ManifoldMorse.criticalPoints E f
  · rw [hzero (F t x) ht, map_zero]
  · exact (hdesc (F t x) ht).le

private theorem Smale.FlowConstruction.strictAnti_flow_height {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) : StrictAnti (fun t => f (F t x)) :=
  strictAnti_of_hasDerivAt_neg (fun t => hasDerivAt_comp_integralCurve hf (hcurve x) t)
    (fun t => hdesc (F t x) (flow_preserves_regular hV F hcurve hzero hx t))

private theorem
    Smale.FlowConstruction.exists_adaptedDescentFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (F : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f,
                  ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p,
                    ∀ᶠ x in 𝓝 p, V x = c.descentField x) ∧
                (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ t, F t x = x) ∧
                  (∀ x,
                      x ∉ Smale.ManifoldMorse.criticalPoints E f →
                        StrictAnti (fun t => f (F t x))) ∧
                    ∀ x, Antitone (fun t => f (F t x)) := by
  obtain ⟨V, hV, hzero, hdesc, hcharts⟩ := Smale.ManifoldMorse.exists_adaptedDescentField hf hm
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  let F := compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V := isMIntegralCurve_compactFlow hV₁ x
  exact
    ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, fun x hx t =>
      flow_fixed_of_zero hV₁ F hcurve (hzero x hx) t, fun x hx =>
      strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hx, fun x =>
      antitone_flow_height hf F hcurve hzero hdesc x⟩

private theorem
    Smale.FlowConstruction.continuous_mvfderiv_field {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.continuous_tangentMap (by simp)).comp hV.continuous
  have hp := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp ht
  convert hp.snd using 1
  rfl

private theorem
    Smale.FlowConstruction.exists_uniform_negative_speed {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ δ > (0 : ℝ), ∀ x ∈ K, mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_mvfderiv_field hf hV).continuousOn
    refine ⟨-mvfderiv 𝓘(ℝ, E) f p (V p), neg_pos.mpr (hdesc p (hreg hp)), ?_⟩
    intro x hx
    have hle : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f p (V p) := hmax hx
    simpa only [neg_neg] using hle
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

private theorem
    Smale.FlowConstruction.exists_uniform_residence_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ T > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ K := by
  by_cases hne : K.Nonempty
  · obtain ⟨δ, hδ, hspeed⟩ := exists_uniform_negative_speed hf hV hdesc hK hreg
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuous.continuousOn
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hf.continuous.continuousOn
    let T := (f q - f p + 1) / δ
    have hpq : f p ≤ f q := hmax hp
    have hgap : 0 < f q - f p + 1 := by linarith
    have hT : 0 < T := div_pos hgap hδ
    have hδT : δ * T = f q - f p + 1 := by
      dsimp [T]
      field_simp [hδ.ne']
    refine ⟨T, hT, ?_⟩
    intro γ hγ
    by_contra! hstay
    have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
      hasDerivAt_comp_integralCurve hf hγ t
    have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
    have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
    have hlast : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
    have hbound :=
      (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
        hdiff.differentiableOn
        (fun t ht => by
          rw [(hd t).deriv]
          exact hspeed (γ t) (hstay t (interior_subset ht)))
        0 hzero T hlast hT.le
    simp only [Function.comp_apply, sub_zero, neg_mul] at hbound
    rw [hδT] at hbound
    have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
    have hhi : f (γ 0) ≤ f q := hmax (hstay 0 hzero)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro γ _
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩

private theorem Smale.FlowConstruction.exists_uniform_criticalNeighborhood_entry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {U : Set M} (hU : IsOpen U)
    (hcover : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ U) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) < a ∨ F t x ∈ U := by
  let K := f ⁻¹' Set.Icc a b ∩ Uᶜ
  have hK : IsCompact K :=
    ((isClosed_Icc.preimage hf.continuous).inter hU.isClosed_compl).isCompact
  have hreg : K ⊆ (Smale.ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    exact hx.2 (hcover x hcrit hx.1)
  obtain ⟨T, hT, hexit⟩ := exists_uniform_residence_bound hf hV hdesc hK hreg
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hout⟩ := hexit (fun s => F s x) (hcurve x)
  have hupper : f (F t x) ≤ b := by
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  refine ⟨t, ht, ?_⟩
  by_cases hlow : f (F t x) < a
  · exact Or.inl hlow
  · right
    by_contra hnot
    exact hout ⟨⟨le_of_not_gt hlow, hupper⟩, hnot⟩

private theorem
    Smale.FlowConstruction.exists_uniform_absorbing_entry {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M}
    (hlower : {x | f x ≤ a} ⊆ A)
    (hcover : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b → ∃ t ∈ Set.Icc 0 T, F t x ∈ A := by
  obtain ⟨T, hT, hentry⟩ :=
    exists_uniform_criticalNeighborhood_entry hf hV hdesc F hcurve hmono isOpen_interior hcover
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hlow | hint⟩ := hentry x hx
  · exact ⟨t, ht, hlower (show f (F t x) ≤ a from le_of_lt hlow)⟩
  · exact ⟨t, ht, interior_subset hint⟩

private theorem Smale.FlowConstruction.exists_absorbingSublevelHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A) :
    ∃ e : A ≃ₕ { x : M // f x ≤ b }, ∀ x, (e x).1 = x.1 := by
  obtain ⟨T, _, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hfinite : ∀ x ∈ {x | f x ≤ b}, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A := by
    intro x hx
    obtain ⟨t, ht, hm⟩ := hhit x hx
    exact ⟨t, ht.1, hm⟩
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hle : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hle.trans hx
  exact ⟨entryHomotopyEquiv F hA hforward hentry hfinite hupper hregion, fun _ => rfl⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₕ
        { x : M // f x ≤ f p + ρ ^ 2 },
      ∀ x, (e x).1 = x.1 := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x := by
    intro x hx t ht
    have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp : x = p := hband x hcrit ⟨hx.ge, by rw [hx]; linarith [sq_nonneg ρ]⟩
      rw [hxp] at hx
      nlinarith [sq_pos_of_pos hρ]
    simpa only [F.map_zero_apply] using
      Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  apply
    Smale.FlowConstruction.exists_absorbingSublevelHomotopyEquiv hf hV hdesc F hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
  · intro x hcrit hx
    have hxp := hband x hcrit hx
    subst x
    exact
      interior_mono Set.subset_union_right (c.mem_interior_range_attachingHandleMap ρ hρ hblock)
  · exact
      c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
  · exact
      c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom

private theorem Smale.FlowConstruction.entryTime_flow_of_le {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ}
    (ht : 0 ≤ t) (hle : t ≤ entryTime F A x) : entryTime F A (F t x) = entryTime F A x - t := by
  have hhit : F (entryTime F A x - t) (F t x) ∈ A := by
    rw [← F.map_add, sub_add_cancel]
    exact flow_entryTime_mem F hA hx
  have hy : ∃ u : ℝ, 0 ≤ u ∧ F u (F t x) ∈ A := ⟨_, sub_nonneg.mpr hle, hhit⟩
  apply le_antisymm (entryTime_le_of_mem F (sub_nonneg.mpr hle) hhit)
  have hh := flow_entryTime_mem F hA hy
  rw [← F.map_add] at hh
  have hb := entryTime_le_of_mem F (add_nonneg (entryTime_nonneg F hy) ht) hh
  linarith

private theorem
    Smale.FlowConstruction.entryTime_lt_of_flow_mem_interior {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} {x : X} {t : ℝ} (ht : 0 < t) (hx : F t x ∈ interior A) :
    entryTime F A x < t := by
  have he : ∀ᶠ s in 𝓝 t, 0 < s ∧ F s x ∈ interior A :=
    (eventually_gt_nhds ht).and
      ((F.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hx))
  obtain ⟨s, hst, hs⟩ := he.exists_lt
  exact (entryTime_le_of_mem F hs.1.le (interior_subset hs.2)).trans_lt hst

private theorem Smale.FlowConstruction.entryTime_eq_add_of_flow_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {A : Set X} (hA : IsClosed A) (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hpos : 0 < entryTime F A (F t x)) : entryTime F A x = t + entryTime F A (F t x) := by
  have hle : t ≤ entryTime F A x := by
    by_contra h
    have hh := (entryTime_le_iff F hA hforward hx ht).mp (le_of_not_ge h)
    rw [entryTime_eq_zero F hh] at hpos
    exact lt_irrefl _ hpos
  rw [entryTime_flow_of_le F hA hx ht hle]
  ring

private structure
    Smale.FlowConstruction.FlowCollarData {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (A B : Set X) where
  time : ℝ
  time_pos : 0 < time
  closed_outer : IsClosed B
  closed_inner : IsClosed A
  inner_subset : A ⊆ B
  forward_outer : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B
  forward_inner : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A
  strict_outer : ∀ x ∈ B, ∀ t : ℝ, 0 < t → F t x ∈ interior B
  strict_inner : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A
  core_inside : ∀ x ∈ B, F time x ∈ interior A

private def
    Smale.FlowConstruction.FlowCollarData.core {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) : Set X :=
  (F (-d.time)) ⁻¹' B

private theorem Smale.FlowConstruction.FlowCollarData.closed_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    IsClosed d.core :=
  d.closed_outer.preimage (F.continuous continuous_const continuous_id)

private theorem Smale.FlowConstruction.FlowCollarData.forward_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 ≤ t → F t x ∈ d.core := by
  intro x hx t ht
  change F (-d.time) (F t x) ∈ B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.forward_outer _ hx t ht

private theorem Smale.FlowConstruction.FlowCollarData.strict_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    ∀ x ∈ d.core, ∀ t : ℝ, 0 < t → F t x ∈ interior d.core := by
  intro x hx t ht
  apply preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
  change F (-d.time) (F t x) ∈ interior B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.strict_outer _ hx t ht

private theorem
    Smale.FlowConstruction.FlowCollarData.flow_time_mem_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : F d.time x ∈ d.core := by
  change F (-d.time) (F d.time x) ∈ B
  simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hx

private theorem Smale.FlowConstruction.FlowCollarData.hits_core {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ d.core :=
  ⟨d.time, d.time_pos.le, d.flow_time_mem_core hx⟩

private theorem Smale.FlowConstruction.FlowCollarData.hits_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) {x : X}
    (hx : x ∈ B) : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A :=
  ⟨d.time, d.time_pos.le, interior_subset (d.core_inside x hx)⟩

private def
    Smale.FlowConstruction.FlowCollarData.duration {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  Smale.FlowConstruction.entryTime F d.core x.1

private theorem
    Smale.FlowConstruction.FlowCollarData.duration_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.duration x :=
  Smale.FlowConstruction.entryTime_nonneg F (d.hits_core x.2)

private theorem Smale.FlowConstruction.FlowCollarData.duration_le {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x ≤ d.time :=
  Smale.FlowConstruction.entryTime_le_of_mem F d.time_pos.le (d.flow_time_mem_core x.2)

private theorem
    Smale.FlowConstruction.FlowCollarData.continuous_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Continuous d.duration :=
  continuousOn_iff_continuous_domRestrict.mp
    (Smale.FlowConstruction.continuousOn_entryTime F d.closed_core d.forward_core d.strict_core
      (fun _ hx => d.hits_core hx))

private def
    Smale.FlowConstruction.FlowCollarData.origin {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) : B :=
  ⟨F (d.duration x - d.time) x.1,
    by
    have h := Smale.FlowConstruction.flow_entryTime_mem F d.closed_core (d.hits_core x.2)
    change F (-d.time) (F (d.duration x) x.1) ∈ B at h
    simpa only [← F.map_add, sub_eq_add_neg, add_comm] using h⟩

private theorem
    Smale.FlowConstruction.FlowCollarData.continuous_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Continuous d.origin :=
  (F.continuous (d.continuous_duration.sub continuous_const) continuous_subtype_val).subtype_mk _

private theorem
    Smale.FlowConstruction.FlowCollarData.origin_reconstruct {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    F (d.time - d.duration x) (d.origin x).1 = x.1 := by
  change F (d.time - d.duration x) (F (d.duration x - d.time) x.1) = x.1
  rw [← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]

private def
    Smale.FlowConstruction.FlowCollarData.delay {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  Smale.FlowConstruction.entryTime F A (d.origin x).1

private theorem Smale.FlowConstruction.FlowCollarData.delay_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.delay x :=
  Smale.FlowConstruction.entryTime_nonneg F (d.hits_inner (d.origin x).2)

private theorem Smale.FlowConstruction.FlowCollarData.delay_lt {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.delay x < d.time :=
  Smale.FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos
    (d.core_inside _ (d.origin x).2)

private theorem
    Smale.FlowConstruction.FlowCollarData.continuous_delay {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Continuous d.delay :=
  (continuousOn_iff_continuous_domRestrict.mp
        (Smale.FlowConstruction.continuousOn_entryTime F d.closed_inner d.forward_inner
          d.strict_inner (fun _ hx => d.hits_inner hx))).comp
    d.continuous_origin

private def
    Smale.FlowConstruction.FlowCollarData.factor {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  (d.time - d.delay x) / d.time

private theorem Smale.FlowConstruction.FlowCollarData.factor_pos {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    0 < d.factor x :=
  div_pos (sub_pos.mpr (d.delay_lt x)) d.time_pos

private theorem Smale.FlowConstruction.FlowCollarData.factor_le_one {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor x ≤ 1 := by
  apply (div_le_one d.time_pos).mpr
  linarith [d.delay_nonneg x]

private theorem
    Smale.FlowConstruction.FlowCollarData.time_mul_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.time * d.factor x = d.time - d.delay x := by
  dsimp [factor]
  field_simp [d.time_pos.ne']

private theorem
    Smale.FlowConstruction.FlowCollarData.continuous_factor {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Continuous d.factor :=
  (continuous_const.sub d.continuous_delay).div_const _

private theorem Smale.FlowConstruction.FlowCollarData.duration_le_retained {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) (hx : x.1 ∈ A) :
    d.duration x ≤ d.time * d.factor x := by
  have hhit : F (d.time - d.duration x) (d.origin x).1 ∈ A := by rwa [d.origin_reconstruct]
  have h := Smale.FlowConstruction.entryTime_le_of_mem F (sub_nonneg.mpr (d.duration_le x)) hhit
  change d.delay x ≤ d.time - d.duration x at h
  rw [d.time_mul_factor]
  linarith

private def
    Smale.FlowConstruction.FlowCollarData.shift {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) : ℝ :=
  d.duration x * (1 - d.factor x)

private theorem Smale.FlowConstruction.FlowCollarData.shift_nonneg {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    0 ≤ d.shift x :=
  mul_nonneg (d.duration_nonneg x) (sub_nonneg.mpr (d.factor_le_one x))

private theorem
    Smale.FlowConstruction.FlowCollarData.shift_le_duration {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.shift x ≤ d.duration x := by
  dsimp [shift]
  nlinarith [mul_nonneg (d.duration_nonneg x) (d.factor_pos x).le]

private theorem
    Smale.FlowConstruction.FlowCollarData.continuous_shift {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Continuous d.shift :=
  d.continuous_duration.mul (continuous_const.sub d.continuous_factor)

private def
    Smale.FlowConstruction.FlowCollarData.rescale {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) : C(B, B)
    where
  toFun x := ⟨F (d.shift x) x.1, d.forward_outer x.1 x.2 _ (d.shift_nonneg x)⟩
  continuous_toFun := (F.continuous d.continuous_shift continuous_subtype_val).subtype_mk _

private theorem
    Smale.FlowConstruction.FlowCollarData.rescale_from_origin {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 = F (d.time - d.duration x * d.factor x) (d.origin x).1 := by
  change F (d.shift x) x.1 = _
  conv_lhs => rw [← d.origin_reconstruct x]
  rw [← F.map_add]
  congr 1
  dsimp [shift]
  ring

private theorem
    Smale.FlowConstruction.FlowCollarData.rescale_mem_inner {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).1 ∈ A := by
  rw [d.rescale_from_origin]
  have hh : d.delay x ≤ d.time - d.duration x * d.factor x := by
    have h := mul_le_mul_of_nonneg_right (d.duration_le x) (d.factor_pos x).le
    rw [d.time_mul_factor] at h
    linarith
  exact
    (Smale.FlowConstruction.entryTime_le_iff F d.closed_inner d.forward_inner
          (d.hits_inner (d.origin x).2) ((d.delay_nonneg x).trans hh)).mp
      hh

private theorem
    Smale.FlowConstruction.FlowCollarData.duration_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration (d.rescale x) = d.duration x * d.factor x := by
  change Smale.FlowConstruction.entryTime F d.core (F (d.shift x) x.1) = _
  rw [Smale.FlowConstruction.entryTime_flow_of_le F d.closed_core (d.hits_core x.2)
      (d.shift_nonneg x) (d.shift_le_duration x)]
  change d.duration x - d.shift x = _
  dsimp [shift]
  ring

private theorem
    Smale.FlowConstruction.FlowCollarData.origin_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.origin (d.rescale x) = d.origin x := by
  apply Subtype.ext
  change F (d.duration (d.rescale x) - d.time) (F (d.shift x) x.1) = F (d.duration x - d.time) x.1
  rw [d.duration_rescale, ← F.map_add]
  congr 1
  dsimp [shift]
  ring

private theorem
    Smale.FlowConstruction.FlowCollarData.factor_rescale {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.factor (d.rescale x) = d.factor x := by
  unfold factor delay
  rw [d.origin_rescale]

private theorem
    Smale.FlowConstruction.FlowCollarData.rescale_injective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Function.Injective d.rescale := by
  intro x y h
  have hfactor : d.factor x = d.factor y := by rw [← d.factor_rescale x, ← d.factor_rescale y, h]
  have hdur : d.duration x = d.duration y := by
    have he := congrArg d.duration h
    rw [d.duration_rescale, d.duration_rescale, hfactor] at he
    exact mul_right_cancel₀ (d.factor_pos y).ne' he
  have horigin : d.origin x = d.origin y := by rw [← d.origin_rescale x, ← d.origin_rescale y, h]
  apply Subtype.ext
  rw [← d.origin_reconstruct x, ← d.origin_reconstruct y, hdur, horigin]

private theorem
    Smale.FlowConstruction.FlowCollarData.rescale_eq_self_of_duration_eq_zero {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) (hx : d.duration x = 0) :
    d.rescale x = x := by
  apply Subtype.ext
  change F (d.shift x) x.1 = x.1
  simp only [shift, hx, MulZeroClass.zero_mul, F.map_zero_apply]

private theorem
    Smale.FlowConstruction.FlowCollarData.exists_rescale_eq {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) (y : B)
    (hy : y.1 ∈ A) : ∃ x : B, d.rescale x = y := by
  by_cases hs : d.duration y = 0
  · exact ⟨y, d.rescale_eq_self_of_duration_eq_zero y hs⟩
  have hspos : 0 < d.duration y := lt_of_le_of_ne (d.duration_nonneg y) (Ne.symm hs)
  let r := d.duration y / d.factor y
  have hr₀ : 0 ≤ r := (div_pos hspos (d.factor_pos y)).le
  have hrT : r ≤ d.time := (div_le_iff₀ (d.factor_pos y)).mpr (d.duration_le_retained y hy)
  have hr : r * d.factor y = d.duration y := div_mul_cancel₀ _ (d.factor_pos y).ne'
  have hsr : d.duration y ≤ r := by
    have hh := mul_le_mul_of_nonneg_left (d.factor_le_one y) hr₀
    rwa [mul_one, hr] at hh
  let x : B :=
    ⟨F (d.time - r) (d.origin y).1, d.forward_outer _ (d.origin y).2 _ (sub_nonneg.mpr hrT)⟩
  have hxy : F (r - d.duration y) x.1 = y.1 := by
    change F (r - d.duration y) (F (d.time - r) (d.origin y).1) = y.1
    rw [← F.map_add]
    convert d.origin_reconstruct y using 2
    ring
  have hdx : d.duration x = r := by
    have hh :=
      Smale.FlowConstruction.entryTime_eq_add_of_flow_pos F d.closed_core d.forward_core
        (d.hits_core x.2) (sub_nonneg.mpr hsr)
        (show 0 < Smale.FlowConstruction.entryTime F d.core (F (r - d.duration y) x.1) by
          rw [hxy]; exact hspos)
    rw [hxy] at hh
    change d.duration x = r - d.duration y + d.duration y at hh
    linarith
  have hox : d.origin x = d.origin y := by
    apply Subtype.ext
    change F (d.duration x - d.time) (F (d.time - r) (d.origin y).1) = _
    rw [hdx, ← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]
  have hfx : d.factor x = d.factor y := by
    unfold factor delay
    rw [hox]
  refine ⟨x, Subtype.ext ?_⟩
  rw [d.rescale_from_origin, hdx, hfx, hox, hr, d.origin_reconstruct]

private def
    Smale.FlowConstruction.FlowCollarData.innerMap {X : Type*} [TopologicalSpace X] {F : Flow ℝ X}
    {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) : C(B, A)
    where
  toFun x := ⟨(d.rescale x).1, d.rescale_mem_inner x⟩
  continuous_toFun := (continuous_subtype_val.comp d.rescale.continuous).subtype_mk _

private theorem
    Smale.FlowConstruction.FlowCollarData.innerMap_bijective {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) :
    Function.Bijective d.innerMap := by
  constructor
  · intro x y h
    apply d.rescale_injective
    exact Subtype.ext (congrArg (fun z : A => (z : X)) h)
  · intro y
    obtain ⟨x, hx⟩ := d.exists_rescale_eq ⟨y.1, d.inner_subset y.2⟩ y.2
    exact ⟨x, Subtype.ext (congrArg (fun z : B => (z : X)) hx)⟩

private def Smale.FlowConstruction.FlowCollarData.homeomorph {X : Type*} [TopologicalSpace X]
    {F : Flow ℝ X} {A B : Set X} (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X]
    [CompactSpace B] : B ≃ₜ A :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d.innerMap d.innerMap_bijective)
    d.innerMap.continuous

private theorem Smale.FlowConstruction.FlowCollarData.duration_lt_time_iff_interior {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x < d.time ↔ (x : X) ∈ interior B := by
  constructor
  · intro hlt
    have hi :=
      d.strict_outer (d.origin x).val (d.origin x).property (d.time - d.duration x)
        (sub_pos.mpr hlt)
    rwa [d.origin_reconstruct] at hi
  · intro hi
    have hcore : F d.time x.val ∈ interior d.core := by
      apply
        preimage_interior_subset_interior_preimage (F.continuous continuous_const continuous_id)
      change F (-d.time) (F d.time x.val) ∈ interior B
      simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hi
    exact Smale.FlowConstruction.entryTime_lt_of_flow_mem_interior F d.time_pos hcore

private theorem Smale.FlowConstruction.FlowCollarData.duration_eq_time_iff_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    d.duration x = d.time ↔ (x : X) ∈ frontier B := by
  rw [frontier, d.closed_outer.closure_eq]
  constructor
  · intro heq
    refine ⟨x.property, ?_⟩
    intro hi
    have hlt := (d.duration_lt_time_iff_interior x).mpr hi
    exact (ne_of_lt hlt) heq
  · intro hx
    apply le_antisymm (d.duration_le x)
    exact le_of_not_gt (fun hlt => hx.2 ((d.duration_lt_time_iff_interior x).mp hlt))

private theorem Smale.FlowConstruction.FlowCollarData.rescale_mem_interior_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.rescale x).val ∈ interior A ↔ x.val ∈ interior B := by
  suffices h : (d.rescale x).val ∈ interior A ↔ d.duration x < d.time from
    h.trans (d.duration_lt_time_iff_interior x)
  constructor
  · intro hi
    by_contra hnot
    have heq : d.duration x = d.time := le_antisymm (d.duration_le x) (le_of_not_gt hnot)
    have horigin : (d.origin x).val = x.val := by
      change F (d.duration x - d.time) x.val = x.val
      rw [heq, sub_self, F.map_zero_apply]
    have hentry : F (d.delay x) (d.origin x).val ∈ interior A := by
      rw [d.rescale_from_origin, heq, d.time_mul_factor, sub_sub_cancel] at hi
      exact hi
    by_cases hpos : 0 < d.delay x
    · have hlt := Smale.FlowConstruction.entryTime_lt_of_flow_mem_interior F hpos hentry
      exact (lt_irrefl (d.delay x)) hlt
    · have hzero : d.delay x = 0 := le_antisymm (le_of_not_gt hpos) (d.delay_nonneg x)
      rw [hzero, F.map_zero_apply, horigin] at hentry
      have hB := interior_mono d.inner_subset hentry
      exact hnot ((d.duration_lt_time_iff_interior x).mpr hB)
  · intro hlt
    rw [d.rescale_from_origin]
    have hmul := mul_lt_mul_of_pos_right hlt (d.factor_pos x)
    rw [d.time_mul_factor] at hmul
    have hdelay : d.delay x < d.time - d.duration x * d.factor x := by linarith
    exact
      Smale.FlowConstruction.flow_mem_interior_of_entryTime_lt F d.closed_inner d.strict_inner
        (d.hits_inner (d.origin x).property) hdelay

private theorem Smale.FlowConstruction.FlowCollarData.innerMap_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) :
    (d.innerMap x).val ∈ frontier A ↔ x.val ∈ frontier B := by
  change (d.rescale x).val ∈ frontier A ↔ x.val ∈ frontier B
  rw [frontier, frontier, d.closed_inner.closure_eq, d.closed_outer.closure_eq]
  constructor
  · intro hx
    exact ⟨x.property, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mpr hi)⟩
  · intro hx
    exact ⟨d.rescale_mem_inner x, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mp hi)⟩

private theorem Smale.FlowConstruction.FlowCollarData.homeomorph_mem_frontier_iff {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B) :
    (d.homeomorph x).val ∈ frontier A ↔ x.val ∈ frontier B :=
  d.innerMap_mem_frontier_iff x

private theorem Smale.FlowConstruction.FlowCollarData.homeomorph_eq_flow_entryTime {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) :
    (d.homeomorph x).val = F (Smale.FlowConstruction.entryTime F A x.val) x.val := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hx
  have ho : (d.origin x).val = x.val := by
    change F (d.duration x - d.time) x.val = x.val
    rw [ht, sub_self, F.map_zero_apply]
  change (d.rescale x).val = _
  rw [d.rescale_from_origin, ht, d.time_mul_factor, sub_sub_cancel]
  change F (Smale.FlowConstruction.entryTime F A (d.origin x).val) (d.origin x).val = _
  rw [ho]

private theorem Smale.FlowConstruction.FlowCollarData.homeomorph_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hx : x.val ∈ frontier B) {t : ℝ} (ht : 0 ≤ t) (hfront : F t x.val ∈ frontier A) :
    (d.homeomorph x).val = F t x.val := by
  rw [d.homeomorph_eq_flow_entryTime x hx,
    Smale.FlowConstruction.entryTime_eq_of_flow_mem_frontier F d.closed_inner d.strict_inner ht
      hfront]

private theorem
    Smale.FlowConstruction.FlowCollarData.homeomorph_symm_eq_flow_of_mem_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (y : A)
    (hy : y.val ∈ frontier A) {t : ℝ} (ht : t ≤ 0) (hfront : F t y.val ∈ frontier B) :
    (d.homeomorph.symm y).val = F t y.val := by
  have hmem : F t y.val ∈ B := by
    simpa only [d.closed_outer.closure_eq] using frontier_subset_closure hfront
  let x : B := ⟨F t y.val, hmem⟩
  have hreturn : F (-t) x.val = y.val := by
    change F (-t) (F t y.val) = y.val
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have heq : d.homeomorph x = y := by
    apply Subtype.ext
    rw [d.homeomorph_eq_flow_of_mem_frontier x hfront (neg_nonneg.mpr ht) (hreturn ▸ hy), hreturn]
  have hinv := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hinv
  exact congrArg (fun z : B => z.val) hinv.symm

private theorem Smale.FlowConstruction.FlowCollarData.rescale_eq_self_of_mem_inner_frontier_outer
    {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) (x : B) (hxA : x.val ∈ A)
    (hxB : x.val ∈ frontier B) : d.rescale x = x := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hxB
  have hret := d.duration_le_retained x hxA
  rw [ht] at hret
  have hfac : d.factor x = 1 := by nlinarith [d.factor_le_one x, d.time_pos]
  apply Subtype.ext
  change F (d.shift x) x.val = x.val
  simp only [shift, hfac, sub_self, MulZeroClass.mul_zero, F.map_zero_apply]

private theorem
    Smale.FlowConstruction.FlowCollarData.homeomorph_fixed_on_common_frontier {X : Type*}
    [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
    (d : Smale.FlowConstruction.FlowCollarData F A B) [T2Space X] [CompactSpace B] (x : B)
    (hxA : x.val ∈ A) (hxB : x.val ∈ frontier B) : (d.homeomorph x).val = x.val :=
  congrArg (fun y : B => y.val) (d.rescale_eq_self_of_mem_inner_frontier_outer x hxA hxB)

private theorem Smale.FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {a b : ℝ} {A : Set M} (hA : IsClosed A)
    (hlower : {x | f x ≤ a} ⊆ A) (hupper : A ⊆ {x | f x ≤ b})
    (hcover : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc a b → x ∈ interior A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    ∃ e : { x : M // f x ≤ b } ≃ₜ A,
      (∀ x, (e x).val ∈ frontier A ↔ x.val ∈ frontier {y : M | f y ≤ b}) ∧
        (∀ x, x.val ∈ A → x.val ∈ frontier {y : M | f y ≤ b} → (e x).val = x.val) ∧
          (∀ y,
            y.val ∈ frontier A →
              ∀ t : ℝ,
                t ≤ 0 → F t y.val ∈ frontier {x : M | f x ≤ b} → (e.symm y).val = F t y.val) := by
  obtain ⟨T, hT, hhit⟩ := exists_uniform_absorbing_entry hf hV hdesc F hcurve hmono hlower hcover
  have hregion : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ b := by
    intro x hx t ht
    have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht
    exact hh.trans hx
  have hstrict : ∀ x ∈ {x | f x ≤ b}, ∀ t : ℝ, 0 < t → F t x ∈ interior {x | f x ≤ b} := by
    intro x hx t ht
    change f x ≤ b at hx
    apply
      interior_maximal
        (show {x | f x < b} ⊆ {x | f x ≤ b} from fun x (hy : f x < b) =>
          (show f x ≤ b from hy.le))
        (isOpen_lt hf.continuous continuous_const)
    rcases lt_or_eq_of_le hx with hlt | heq
    · have hh : f (F t x) ≤ f x := by simpa only [F.map_zero_apply] using hmono x ht.le
      exact hh.trans_lt hlt
    · exact htop x heq t ht
  let d : FlowCollarData F A {x | f x ≤ b} :=
    { time := T + 1
      time_pos := by linarith
      closed_outer := isClosed_le hf.continuous continuous_const
      closed_inner := hA
      inner_subset := hupper
      forward_outer := hregion
      forward_inner := hforward
      strict_outer := hstrict
      strict_inner := hentry
      core_inside := by
        intro x hx
        obtain ⟨t, ht, hmem⟩ := hhit x hx
        have hh := hentry _ hmem (T + 1 - t) (by linarith [ht.2])
        rwa [← F.map_add, sub_add_cancel] at hh }
  have : CompactSpace ↥({x : M | f x ≤ b}) :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  exact
    ⟨d.homeomorph, d.homeomorph_mem_frontier_iff, d.homeomorph_fixed_on_common_frontier,
      fun y hy _ ht hfront => d.homeomorph_symm_eq_flow_of_mem_frontier y hy ht hfront⟩

private theorem Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow {X : Type*}
    [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) (F : Flow ℝ X)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {b : ℝ}
    (htop : ∀ x, f x = b → ∀ t : ℝ, 0 < t → f (F t x) < b) :
    frontier {x | f x ≤ b} = {x | f x = b} := by
  have hclosed : IsClosed {x | f x ≤ b} := isClosed_le hf continuous_const
  ext x
  rw [frontier, hclosed.closure_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    apply le_antisymm hx
    by_contra hn
    have hlt : f x < b := lt_of_not_ge hn
    exact
      hnot (interior_maximal (fun y (hy : f y < b) => hy.le) (isOpen_lt hf continuous_const) hlt)
  · intro hx
    refine ⟨(show f x ≤ b from hx.le), ?_⟩
    intro hi
    have he : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ b} := by
      have hcont : ContinuousAt (fun t : ℝ => F t x) 0 :=
        (F.continuous continuous_id continuous_const).continuousAt
      apply hcont.preimage_mem_nhds
      simpa only [F.map_zero_apply] using isOpen_interior.mem_nhds hi
    obtain ⟨s, hs, hsB⟩ := he.exists_lt
    have hy : F s x ∈ {y | f y ≤ b} := interior_subset hsB
    have hxy : f x ≤ f (F s x) := by
      have hh := hmono (F s x) (show (0 : ℝ) ≤ -s by linarith)
      simpa only [F.map_zero_apply, ← F.map_add, neg_add_cancel] using hh
    have hyeq : f (F s x) = b := le_antisymm hy (hx ▸ hxy)
    have hstrict := htop (F s x) hyeq (-s) (by linarith)
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hx] at hstrict
    exact lt_irrefl b hstrict

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hagreement :
      ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (hband :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) :
    ∃ e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 },
      (∀ x,
          f (e x) = f p + ρ ^ 2 ↔
            x.val ∈
              frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
        (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
          (∀ x,
            x.val ∈
                frontier
                  ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
              ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) := by
  have hV₁ :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    hV.of_le (by simp)
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hboundary (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) (t : ℝ) (ht : 0 < t) : f (F t x) < f x := by
    have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxp := hband x hcrit (hx ▸ hb)
      exact hne (hx.symm.trans (congrArg f hxp))
    simpa only [F.map_zero_apply] using
      Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hcurve hzero hdesc hreg ht
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f x :=
    hboundary _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have htop : ∀ x, f x = f p + ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p + ρ ^ 2 := by
    intro x hx t ht
    rw [← hx]
    exact
      hboundary _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ]) x hx t ht
  have hhome :=
    Smale.FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits hf hV hdesc F
      hcurve hmono
      ((isClosed_le hf.continuous continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      Set.subset_union_left (c.attachingHandleUnion_subset_upper ρ hρ hblock) (a := f p - ρ ^ 2)
      (fun x hcrit hx => by
        have hxp := hband x hcrit hx
        subst x
        exact
          interior_mono Set.subset_union_right
            (c.mem_interior_range_attachingHandleMap ρ hρ hblock))
      (c.forwardInvariant_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement)
      (c.interior_entry_attachingUnion hf.continuous hV₁ F hcurve hmono ρ hρ hblock hagreement
        hbottom)
      htop
  obtain ⟨e, hfront, hfixed, horbit⟩ := hhome
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro x
    have hx := hfront (e.symm x)
    rw [e.apply_symm_apply,
      Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop] at hx
    exact hx.symm
  · intro x hx
    let y : { x : M // f x ≤ f p + ρ ^ 2 } := ⟨x.val, hx.le⟩
    have hy : y.val ∈ frontier {z : M | f z ≤ f p + ρ ^ 2} := by
      rw [Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
      exact hx
    have heq : e y = x := Subtype.ext (hfixed y x.property hy)
    have hh := congrArg e.symm heq
    rw [e.symm_apply_apply] at hh
    exact congrArg (fun z : { z : M // f z ≤ f p + ρ ^ 2 } => z.val) hh.symm
  · intro x hx t ht hlevel
    apply horbit x hx t ht
    rw [Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono htop]
    exact hlevel

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.FollowsModelBoundaryOrbits {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 }) :
    Prop :=
  ∀ x,
    x.val ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
      x.val ∈ c.splitChart.source →
        ∀ t : ℝ,
          t ≤ 0 →
            (∀ s ∈ Set.uIcc 0 t,
                Smale.MorseHandle.descentFlow s (c.splitChart x.val) ∈
                  Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                    Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ)) →
              f (c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x.val))) =
                  f p + ρ ^ 2 →
                (e x).val =
                  c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x.val))

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.followsModelBoundaryOrbits_of_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (horbit :
      ∀ x,
        x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) →
          ∀ t : ℝ, t ≤ 0 → f (F t x.val) = f p + ρ ^ 2 → (e x).val = F t x.val) :
    c.FollowsModelBoundaryOrbits ρ hρ hblock e := by
  intro x hx hsource t ht hpath hlevel
  have hmodel :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hcurve hsource (fun s hs => hblock (hpath s hs))
      (fun s hs => heq _ (hpath s hs))
  exact (horbit x hx t ht (hmodel ▸ hlevel)).trans hmodel

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_closed_productBlock_in {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {W : Set M} (hW : IsOpen W)
    (hpW : p ∈ W) :
    ∃ r > (0 : ℝ),
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hmem : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target ∩ e.symm ⁻¹' W :=
    ⟨hzero, by simpa only [Set.mem_preimage, hinv] using hpW⟩
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp ((e.isOpen_inter_preimage_symm hW).mem_nhds hmem)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_fieldCompatibleBlock {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) :
    ∃ ρ > (0 : ℝ),
      ∃ W : Set M,
        IsOpen W ∧
          p ∈ W ∧
            (∀ x ∈ W, V x = c.descentField x) ∧
              Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp heq
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hW hpW
  refine ⟨r / 2, half_pos hr, W, hW, hpW, hWeq, ?_⟩
  rw [show 2 * (r / 2) = r by ring]
  exact hblock

private theorem Smale.ManifoldMorse.exists_isolating_radius {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (p : X) (hunique : ∀ x ∈ K, f x = f p → x = p) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ρ < R ∧ ∀ x ∈ K, f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  have hfin : (f '' (K \ { p })).Finite := (hK.subset Set.sdiff_subset).image f
  have hnot : f p ∉ f '' (K \ { p }) := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (Set.mem_singleton_iff.mpr (hunique x hx.1 heq))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl (f p) hnot
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro x hx hval
  by_contra hxp
  have hd : Dist.dist (f x) (f p) < δ := by
    rw [Real.dist_eq]
    have ha : |f x - f p| ≤ ρ ^ 2 := abs_le.mpr ⟨by linarith [hval.1], by linarith [hval.2]⟩
    exact ha.trans_lt hρsq
  exact hball hd ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, rfl⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.exists_isolated_fieldCompatibleBlock_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hunique : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ),
      ρ < ε ∧
        ∃ W : Set M,
          IsOpen W ∧
            p ∈ W ∧
              (∀ x ∈ W, V x = c.descentField x) ∧
                (Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                      Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
                    c.splitChart.target ∩ c.splitChart.symm ⁻¹' W) ∧
                  ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                    f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨R, hR, W, hW, hpW, heqW, hblock⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρbound, hband⟩ :=
    Smale.ManifoldMorse.exists_isolating_radius hfinite p hunique (lt_min hR hε)
  have hρR : ρ < R := hρbound.trans_le (min_le_left _ _)
  have hρε : ρ < ε := hρbound.trans_le (min_le_right _ _)
  refine ⟨ρ, hρ, hρε, W, hW, hpW, heqW, ?_, hband⟩
  intro z hz
  apply hblock
  have hr : 2 * ρ ≤ 2 * R := mul_le_mul_of_nonneg_left hρR.le (by norm_num)
  exact ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩

private theorem Smale.ManifoldMorse.isOpen_regularInChart {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen {q : P × M | q.2 ∈ e.source ∧ fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0} := by
  have hU : IsOpen {q : P × E | q.2 ∈ e.target} := e.open_target.preimage continuous_snd
  have hd :=
    Smale.MorsePerturbation.contDiffOn_spatialDerivative (f := fun a y => f a (e.symm y)) hU
      (contDiffOn_inChart hf he)
  have hg :=
    hd.continuousOn.isOpen_inter_preimage hU
      (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff, S]
  constructor
  · rintro ⟨hq, hn⟩
    exact ⟨hq, e.map_source hq, hn⟩
  · rintro ⟨hq, -, hn⟩
    exact ⟨hq, hn⟩

private theorem Smale.ManifoldMorse.isOpen_regularPoint {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | q.2 ∉ criticalPoints E (f q.1)} := by
  have hslice (a : P) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let e := chartAt E q.2
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas q.2
  have hx : q.2 ∈ e.source := mem_chart_source E q.2
  have hmem : q ∈ {r : P × M | r.2 ∈ e.source ∧ fderiv ℝ (f r.1 ∘ e.symm) (e r.2) ≠ 0} :=
    ⟨hx, fun hz => hq ((mem_criticalPoints_iff (hslice q.1) he hx).mpr hz)⟩
  apply Filter.mem_of_superset ((isOpen_regularInChart hf he).mem_nhds hmem)
  intro r hr hcrit
  exact hr.2 ((mem_criticalPoints_iff (hslice r.1) he hr.1).mp hcrit)

private theorem Smale.ManifoldMorse.isOpen_regularOn {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) {K : Set M}
    (hK : IsCompact K) : IsOpen {a : P | ∀ x ∈ K, x ∉ criticalPoints E (f a)} :=
  Smale.MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_regularPoint hf)

private theorem
    Smale.ManifoldMorse.eventually_criticalPoints_eq {E P M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) (a₀ : P) {U : Set M}
    (hU : IsOpen U) (hcover : criticalPoints E (f a₀) ⊆ U)
    (hfixed : ∀ a x, x ∈ U → (x ∈ criticalPoints E (f a) ↔ x ∈ criticalPoints E (f a₀))) :
    ∀ᶠ a in 𝓝 a₀, criticalPoints E (f a) = criticalPoints E (f a₀) := by
  have hreg : ∀ x ∈ Uᶜ, x ∉ criticalPoints E (f a₀) := fun x hx hc => hx (hcover hc)
  have hn := (isOpen_regularOn hf hU.isClosed_compl.isCompact).mem_nhds hreg
  filter_upwards [hn] with a ha
  ext x
  by_cases hx : x ∈ U
  · exact hfixed a x hx
  · exact iff_of_false (ha x hx) (hreg x hx)

private def Smale.ManifoldMorse.constantPerturb {M : Type*} (f ψ : M → ℝ) (a : ℝ) (x : M) : ℝ :=
  f x + a * ψ x

private theorem Smale.ManifoldMorse.contMDiff_constantPerturb {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry (constantPerturb f ψ)) :=
  (hf.comp contMDiff_snd).add (contMDiff_fst.smul (hψ.comp contMDiff_snd))

private theorem Smale.ManifoldMorse.mfderiv_constantPerturb_of_locally_constant {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M} {b : ℝ} (hψ : ψ =ᶠ[𝓝 x] fun _ => b) (a : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : constantPerturb f ψ a =ᶠ[𝓝 x] (fun y => f y + a * b) := by
    filter_upwards [hψ] with y hy
    simp only [constantPerturb, hy]
  rw [heq.mfderiv_eq]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f + fun _ => a * b) x = _
  rw [mfderiv_add (hf.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const]
  exact add_zero _

private theorem Smale.ManifoldMorse.eventually_constantPerturb_morse_criticalPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ)
    (hconstant : ∀ p ∈ criticalPoints E f, ∃ b : ℝ, ψ =ᶠ[𝓝 p] fun _ => b) :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      IsMorse E (constantPerturb f ψ a) ∧
        criticalPoints E (constantPerturb f ψ a) = criticalPoints E f := by
  have hfamily := contMDiff_constantPerturb hf hψ
  have hzero : constantPerturb f ψ 0 = f := by funext x; simp [constantPerturb]
  have hm₀ : IsMorseOn E (constantPerturb f ψ 0) Set.univ := by
    rw [hzero]
    exact fun x _ => hm x
  have hmor := (isOpen_isMorseOn hfamily isCompact_univ).mem_nhds hm₀
  let U := ⋃ b : ℝ, interior {x : M | ψ x = b}
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_interior)
  have hcover : criticalPoints E (constantPerturb f ψ 0) ⊆ U := by
    rw [hzero]
    intro p hp
    obtain ⟨b, hb⟩ := hconstant p hp
    exact Set.mem_iUnion.mpr ⟨b, mem_interior_iff_mem_nhds.mpr hb⟩
  have hfixed :
    ∀ a x,
      x ∈ U →
        (x ∈ criticalPoints E (constantPerturb f ψ a) ↔
          x ∈ criticalPoints E (constantPerturb f ψ 0)) := by
    intro a x hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    have hlocal : ψ =ᶠ[𝓝 x] fun _ => b := mem_interior_iff_mem_nhds.mp hb
    rw [hzero]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_constantPerturb_of_locally_constant hf hlocal a]
    rfl
  have hcrit := eventually_criticalPoints_eq hfamily 0 hU hcover hfixed
  rw [hzero] at hcrit
  filter_upwards [hmor, hcrit] with a ha hc
  exact ⟨fun x => ha x (Set.mem_univ x), hc⟩

private theorem
    Smale.ManifoldMorse.exists_separating_critical_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) (p : M) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧
            (∀ x ∈ criticalPoints E f, x ≠ p → g x = f x) ∧
              ∀ x ∈ criticalPoints E f, g x = g p → x = p := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hclosed : IsClosed (K \ { p }) := (hK.subset Set.sdiff_subset).isClosed
  have hp : p ∈ (K \ { p })ᶜ := by simp
  obtain ⟨ψ, _, hψsub⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
      (hclosed.isOpen_compl.mem_nhds hp)
  have hψone : (ψ : M → ℝ) =ᶠ[𝓝 p] fun _ => 1 := ψ.eventuallyEq_one
  have hψzero (x : M) (hx : x ∈ K) (hxp : x ≠ p) : (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact hψsub h ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩
  have hconstant : ∀ x ∈ criticalPoints E f, ∃ b : ℝ, (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => b := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact ⟨1, hψone⟩
    · exact ⟨0, hψzero x hx hxp⟩
  have hstable := eventually_constantPerturb_morse_criticalPoints hf hm ψ.contMDiff hconstant
  let T : Set ℝ := (fun x => f x - f p) '' (K \ { p })
  have hT : T.Finite := (hK.subset Set.sdiff_subset).image _
  have hdense : Dense Tᶜ := by
    have heq : (Set.univ : Set ℝ) \ T = Tᶜ := by
      ext a
      exact and_iff_right (Set.mem_univ a)
    rw [← heq]
    exact dense_univ.sdiff_finite hT
  obtain ⟨U, hUstable, hU, hzeroU⟩ := _root_.mem_nhds_iff.mp hstable
  obtain ⟨a, haT, haU⟩ := hdense.exists_mem_open hU ⟨0, hzeroU⟩
  let g := constantPerturb f ψ a
  have hvalues (x : M) (hx : x ∈ K) (hxp : x ≠ p) : g x = f x := by
    have hxzero : ψ x = 0 := (hψzero x hx hxp).eq_of_nhds
    simp only [g, constantPerturb, hxzero, MulZeroClass.mul_zero, add_zero]
  have hpvalue : g p = f p + a := by
    have hpone : ψ p = 1 := hψone.eq_of_nhds
    simp only [g, constantPerturb, hpone, mul_one]
  refine
    ⟨g, (contMDiff_constantPerturb hf ψ.contMDiff).comp (contMDiff_const.prodMk contMDiff_id),
      (hUstable haU).1, (hUstable haU).2, hvalues, ?_⟩
  intro x hx heq
  by_contra hxp
  have hax : f x - f p = a := by rw [hvalues x hx hxp, hpvalue] at heq; linarith
  exact haT ⟨x, ⟨hx, by simpa only [Set.mem_singleton_iff] using hxp⟩, hax⟩

private theorem
    Smale.ManifoldMorse.exists_distinct_critical_values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        IsMorse E g ∧
          criticalPoints E g = criticalPoints E f ∧ Set.InjOn g (criticalPoints E g) := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hfinite :
    ∀ s : Finset M,
      (s : Set M) ⊆ K →
        ∃ g : M → ℝ,
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
            IsMorse E g ∧ criticalPoints E g = K ∧ Set.InjOn g (s : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨f, hf, hm, rfl, by simp⟩
    | @insert p s hps ih =>
      intro hsK
      have hsK' : (s : Set M) ⊆ K := fun x hx => hsK (Finset.mem_insert_of_mem hx)
      obtain ⟨g, hg, hmg, hcrit, hinj⟩ := ih hsK'
      obtain ⟨g', hg', hmg', hcrit', hfixed, hunique⟩ := exists_separating_critical_value hg hmg p
      have hK' : criticalPoints E g' = K := hcrit'.trans hcrit
      refine ⟨g', hg', hmg', hK', ?_⟩
      intro x hx y hy heq
      have hxcrit : x ∈ criticalPoints E g := hcrit ▸ hsK hx
      have hycrit : y ∈ criticalPoints E g := hcrit ▸ hsK hy
      by_cases hxp : x = p
      · subst x
        exact (hunique y hycrit heq.symm).symm
      by_cases hyp : y = p
      · subst y
        exact hunique x hxcrit heq
      have hxs : x ∈ (s : Set M) := (Finset.mem_insert.mp hx).resolve_left hxp
      have hys : y ∈ (s : Set M) := (Finset.mem_insert.mp hy).resolve_left hyp
      apply hinj hxs hys
      rw [← hfixed x hxcrit hxp, ← hfixed y hycrit hyp]
      exact heq
  obtain ⟨g, hg, hmg, hcrit, hinj⟩ := hfinite hK.toFinset (by simp)
  refine ⟨g, hg, hmg, hcrit, ?_⟩
  rw [hcrit]
  simpa only [hK.coe_toFinset] using hinj

private theorem Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values (E : Type*)
    (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        IsMorse E f ∧ (criticalPoints E f).Finite ∧ Set.InjOn f (criticalPoints E f) := by
  obtain ⟨f, hf, hm⟩ := exists_morse_function E M
  obtain ⟨g, hg, hmg, _, hinj⟩ := exists_distinct_critical_values hf hm
  exact ⟨g, hg, hmg, finite_criticalPoints hg hmg, hinj⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.exists_morse_boundary_attachment_with_model_orbits_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      ρ < ε ∧
        ∃ c : SignedMorseChart (E := E) f p,
          ∃ hblock :
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
              c.splitChart.target,
            ∃ e :
              ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
                { x : M // f x ≤ f p + ρ ^ 2 },
              (∀ x,
                  f (e x) = f p + ρ ^ 2 ↔
                    x.val ∈
                      frontier
                        ({y | f y ≤ f p - ρ ^ 2} ∪
                          Set.range (c.attachingHandleMap ρ hρ hblock))) ∧
                (∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) ∧
                  (frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) ∧
                    (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
                      (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
                        c.FollowsModelBoundaryOrbits ρ hρ hblock e ∧
                          ∀ x ∈ criticalPoints E f,
                            f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    Smale.FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨ρ, hρ, hρε, W, hW, _, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt (finite_criticalPoints hf hm) hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (Smale.MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hcurve ρ hρ hblock
      hagreement hband
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ criticalPoints E f := by
    intro hcrit
    have hxp := hband x hcrit (hx ▸ hb)
    exact hne (hx.symm.trans (congrArg f hxp))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hstrict :=
      Smale.FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hcurve hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hstrict
  refine
    ⟨ρ, hρ, hρε, c, hblock, e, hfront, hfixed,
      Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F hmono hbottom,
      hlower, hupper, ?_, hband⟩
  apply
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hcurve ρ hρ hblock (e := e)
      (horbit := horbit)
  intro z hz
  filter_upwards [hW.mem_nhds (hblockW hz).2] with y hy
  exact heqW y hy

private def Smale.SurgeryBoundaryPair.changeNewBoundary {N P R X Y Z : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (d : Smale.SurgeryBoundaryPair N P R X Y) (e : Y ≃ₜ Z) :
    Smale.SurgeryBoundaryPair N P R X Z
    where
  oldExterior := d.oldExterior
  newExterior := e ∘ d.newExterior
  oldPiece := d.oldPiece
  newPiece := e ∘ d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := e.isClosedEmbedding.comp d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := e.isClosedEmbedding.comp d.newPiece_closed
  old_cover := d.old_cover
  new_cover := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : e.symm z ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by
      rw [d.new_cover]
      trivial
    rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
    · exact Or.inl ⟨r, (congrArg e hr).trans (e.apply_symm_apply z)⟩
    · exact Or.inr ⟨p, (congrArg e hp).trans (e.apply_symm_apply z)⟩
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := fun r p => e.injective.eq_iff.trans (d.new_overlap r p)

private def
    Smale.ClosedCover.frontierLevelHomeomorph {M : Type*} [TopologicalSpace M] {f : M → ℝ} {b : ℝ}
    {A : Set M} (hA : IsClosed A) (e : A ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x) = b ↔ (x : M) ∈ frontier A) : frontier A ≃ₜ { x : M // f x = b } := by
  have hsub : frontier A ⊆ A := by
    intro x hx
    have hc := frontier_subset_closure hx
    rwa [hA.closure_eq] at hc
  let toA : frontier A → A := Set.inclusion hsub
  let toB : { x : M // f x = b } → { x : M // f x ≤ b } := fun x => ⟨x, x.property.le⟩
  refine
    { toFun := fun x => ⟨e (toA x), (he (toA x)).mpr x.property⟩
      invFun := fun y => ⟨e.symm (toB y), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (he (e.symm (toB y))).mp
    rw [e.apply_symm_apply]
    exact y.property
  · intro x
    apply Subtype.ext
    exact congrArg (fun z : A => (z : M)) (e.symm_apply_apply (toA x))
  · intro y
    apply Subtype.ext
    exact congrArg (fun z : { x : M // f x ≤ b } => (z : M)) (e.apply_symm_apply (toB y))
  · exact
      (continuous_subtype_val.comp
            (e.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _
  · exact
      (continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk
        _

private theorem Smale.SurgeryBoundaryPair.exchange_preserves_incidence {E F R X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair E F R X Y) (r : R)
    (p : Smale.PuncturedHandle.UnitSphere E × Smale.PuncturedHandle.PuncturedBall F) :
    d.oldExteriorMap r = d.oldPuncturedMap p ↔
      d.newExteriorMap r = d.newPuncturedMap (Smale.PuncturedHandle.exchange E F p) := by
  rw [d.oldPunctured_overlap, d.newPunctured_overlap]
  constructor
  · rintro ⟨q, hr, rfl⟩
    exact ⟨q, hr, Smale.PuncturedHandle.exchange_boundary q.1 q.2⟩
  · rintro ⟨q, hr, hq⟩
    refine ⟨q, hr, (Smale.PuncturedHandle.exchange E F).injective ?_⟩
    exact hq.trans (Smale.PuncturedHandle.exchange_boundary q.1 q.2).symm

private def
    Smale.SurgeryBoundaryPair.complementHomeomorph {E F R X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair E F R X Y) :
    d.OldComplement ≃ₜ d.NewComplement :=
  Smale.ClosedCover.homeomorphOfClosedPieces d.oldExteriorMap d.newExteriorMap d.oldPuncturedMap
    d.newPuncturedMap d.isClosedEmbedding_oldExteriorMap d.isClosedEmbedding_newExteriorMap
    d.isClosedEmbedding_oldPuncturedMap d.isClosedEmbedding_newPuncturedMap d.oldComplement_cover
    d.newComplement_cover (Smale.PuncturedHandle.exchange E F) d.exchange_preserves_incidence

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.boundaryLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    frontier ({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) ≃ₜ
      { x : M // f x = f p + ρ ^ 2 } :=
  (Homeomorph.setCongr (by rw [c.range_normHandleMap ρ hρ hblock])).trans
    (Smale.ClosedCover.frontierLevelHomeomorph
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range)
      e he)

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.levelSurgeryBoundaryPair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock))) :
    Smale.SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates
      { x : M //
        f x = f p - ρ ^ 2 ∧
          x ∈ frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.normHandleMap ρ hρ hblock)) }
      { x : M // f x = f p - ρ ^ 2 } { x : M // f x = f p + ρ ^ 2 } :=
  (c.attachmentBoundaryData hf ρ hρ hblock hlevel).surgeryBoundaryPair.changeNewBoundary
    (c.boundaryLevelHomeomorph hf ρ hρ hblock e he)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.normHandleMap_belt_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    f
        (c.normHandleMap ρ hρ hblock
          (Smale.PuncturedHandle.ballZero, Smale.PuncturedHandle.sphereToBall v)) =
      f p + ρ ^ 2 := by
  change
    f
        (c.attachingHandleMap ρ hρ hblock
          (⟨0, by simp⟩,
            ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩)) =
      _
  rw [c.attachingHandleMap_quadratic]
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [Smale.MorseHandle.modelMap, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv]

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.beltCoreMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates, { y : M // f y = f p + ρ ^ 2 })
    where
  toFun
    v :=
    ⟨c.normHandleMap ρ hρ hblock
        (Smale.PuncturedHandle.ballZero, Smale.PuncturedHandle.sphereToBall v),
      c.normHandleMap_belt_height ρ hρ hblock v⟩
  continuous_toFun :=
    ((c.normHandleMap ρ hρ hblock).continuous.comp
          (continuous_const.prodMk (continuous_subtype_val.subtype_mk _))).subtype_mk
      _

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.beltCoreMap_coe {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    (c.beltCoreMap ρ hρ hblock v : M) = c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) := by
  change
    c.splitChart.symm
        ((ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) • (0 : c.NegativeCoordinates),
          ρ • (v : c.PositiveCoordinates)) =
      _
  simp only [smul_zero]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.contMDiff_beltCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) := by
  have heq :
    Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates =>
      c.splitChart.symm (0, ρ • (v : c.PositiveCoordinates)) :=
    funext (c.beltCoreMap_coe ρ hρ hblock)
  rw [heq]
  have hcoe :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (Subtype.val :
        Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates → c.PositiveCoordinates) :=
    contMDiff_coe_sphere (E := c.PositiveCoordinates) (n := n)
  have hscalar :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun _ : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates => ρ) :=
    contMDiff_const
  have hpositive :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.PositiveCoordinates) ∞
      (fun v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ρ • (v : c.PositiveCoordinates)) :=
    hscalar.smul hcoe
  have hcoords :
    ContMDiff (𝓡 n) 𝓘(ℝ, c.NegativeCoordinates × c.PositiveCoordinates) ∞
      (fun v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates =>
        ((0 : c.NegativeCoordinates), ρ • (v : c.PositiveCoordinates))) :=
    contMDiff_const.prodMk_space hpositive
  apply c.splitChart.contMDiffOn_invFun.comp_contMDiff hcoords
  intro v
  have hh :=
    hblock
      (Smale.MorseHandle.modelMap_mem_product hρ
        ((⟨0, by simp⟩ : Smale.MorseHandle.UnitDisk c.NegativeCoordinates),
          ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩))
  simpa [Smale.MorseHandle.modelMap] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.beltSphere_eq_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M]
    (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e :
      ↥({x | f x ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
        { x : M // f x ≤ f p + ρ ^ 2 })
    (he :
      ∀ x,
        f (e x) = f p + ρ ^ 2 ↔
          x.val ∈
            frontier ({y | f y ≤ f p - ρ ^ 2} ∪ Set.range (c.attachingHandleMap ρ hρ hblock)))
    (hfixed : ∀ x, f x.val = f p + ρ ^ 2 → (e x).val = x.val) :
    (c.levelSurgeryBoundaryPair hf ρ hρ hblock hlevel e he).beltSphere =
      c.beltCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  exact hfixed _ (c.normHandleMap_belt_height ρ hρ hblock v)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.contMDiff_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (c.beltCoreMap ρ hρ hblock) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  exact
    (Smale.RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 n) (c.beltCoreMap ρ hρ hblock)).mpr
      (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock)

private def Smale.PartialChart.restrictSource {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {U : Set M} (hU : IsOpen U) : PartialDiffeomorph I J M N ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left

private def Smale.PartialChart.restrictTarget {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {V : Set N} (hV : IsOpen V) :
    PartialDiffeomorph I J M N ∞ :=
  (restrictSource Φ.symm hV).symm

public
theorem Smale.PartialChart.bijective_mfderiv {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  exact hdiff.mfderiv_bijective hx

private theorem Smale.PartialChart.injective_mfderiv_linear_sphere {N F E H M : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞) (L : N →L[ℝ] F) (hL : Function.Injective L)
    (u : Metric.sphere (0 : N) 1) (hu : L (u : N) ∈ Φ.source) :
    Function.Injective (mfderiv (𝓡 n) I (fun v : Metric.sphere (0 : N) 1 => Φ (L (v : N))) u) := by
  have hcoesm : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (Subtype.val : Metric.sphere (0 : N) 1 → N) :=
    contMDiff_coe_sphere (E := N) (n := n)
  have hcoe := hcoesm.mdifferentiableAt (x := u) (by simp)
  have hlinear : MDifferentiableAt 𝓘(ℝ, N) 𝓘(ℝ, F) L (u : N) :=
    L.differentiableAt.mdifferentiableAt
  have hinner := hlinear.comp u hcoe
  have hsphere :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, N) (Subtype.val : Metric.sphere (0 : N) 1 → N) u) := by
    convert! injective_mvfderiv_subtypeVal_sphere u
  change Function.Injective (mfderiv (𝓡 n) I (Φ ∘ (L ∘ Subtype.val)) u)
  rw [mfderiv_comp u (Φ.mdifferentiableAt (by simp) hu) hinner, mfderiv_comp u hlinear hcoe,
    mfderiv_eq_fderiv, L.fderiv]
  exact (bijective_mfderiv Φ hu).injective.comp (hL.comp hsphere)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.injective_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.attachingCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh :=
    c.attachingHandleMap_injective ρ hρ hblock
      (congrArg (fun y : { y : M // f y = f p - ρ ^ 2 } => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.1 : c.NegativeCoordinates)) hh)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.injective_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (c.beltCoreMap ρ hρ hblock) := by
  intro u v huv
  have hh :=
    c.attachingHandleMap_injective ρ hρ hblock
      (congrArg (fun y : { y : M // f y = f p + ρ ^ 2 } => (y : M)) huv)
  exact Subtype.ext (congrArg (fun z => (z.2 : c.PositiveCoordinates)) hh)

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.attachingCoreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.attachingCoreMap ρ hρ hblock) :=
  (c.attachingCoreMap ρ hρ hblock).continuous.isClosedEmbedding
    (c.injective_attachingCoreMap ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.beltCoreMap_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [T2Space M] (ρ : ℝ)
    (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Topology.IsClosedEmbedding (c.beltCoreMap ρ hρ hblock) :=
  (c.beltCoreMap ρ hρ hblock).continuous.isClosedEmbedding (c.injective_beltCoreMap ρ hρ hblock)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.injective_mfderiv_attachingCoreMap_ambient
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.attachingCoreMap ρ hρ hblock) u) :=
  by
  let L : c.NegativeCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inl ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Function.Injective L := by
    intro x y hxy
    apply smul_right_injective c.NegativeCoordinates hρ.ne'
    exact congrArg Prod.fst hxy
  have hu : L (u : c.NegativeCoordinates) ∈ c.splitChart.target := by
    have hh :=
      hblock
        (Smale.MorseHandle.modelMap_mem_product hρ
          (⟨(u : c.NegativeCoordinates), Metric.sphere_subset_closedBall u.property⟩,
            (⟨0, by simp⟩ : Smale.MorseHandle.UnitDisk c.PositiveCoordinates)))
    simpa [L, Smale.MorseHandle.modelMap] using hh
  have heq :
    Subtype.val ∘ c.attachingCoreMap ρ hρ hblock =
      fun v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates => c.splitChart.symm (L v) :=
    by
    funext v
    rw [Function.comp_apply, c.attachingCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact Smale.PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL u hu

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.injective_mfderiv_beltCoreMap_ambient {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)] (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val ∘ c.beltCoreMap ρ hρ hblock) v) := by
  let L : c.PositiveCoordinates →L[ℝ] c.NegativeCoordinates × c.PositiveCoordinates :=
    ρ • ContinuousLinearMap.inr ℝ c.NegativeCoordinates c.PositiveCoordinates
  have hL : Function.Injective L := by
    intro x y hxy
    apply smul_right_injective c.PositiveCoordinates hρ.ne'
    exact congrArg Prod.snd hxy
  have hv : L (v : c.PositiveCoordinates) ∈ c.splitChart.target := by
    have hh :=
      hblock
        (Smale.MorseHandle.modelMap_mem_product hρ
          ((⟨0, by simp⟩ : Smale.MorseHandle.UnitDisk c.NegativeCoordinates),
            ⟨(v : c.PositiveCoordinates), Metric.sphere_subset_closedBall v.property⟩))
    simpa [L, Smale.MorseHandle.modelMap] using hh
  have heq :
    Subtype.val ∘ c.beltCoreMap ρ hρ hblock =
      fun u : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates => c.splitChart.symm (L u) :=
    by
    funext u
    rw [Function.comp_apply, c.beltCoreMap_coe]
    congr 1
    simp [L]
  rw [heq]
  exact Smale.PartialChart.injective_mfderiv_linear_sphere c.splitChart.symm L hL v hv

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.injective_mfderiv_attachingCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) (c.attachingCoreMap ρ hρ hblock) u) := by
  exact
    Smale.RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n)
      (c.attachingCoreMap ρ hρ hblock) u (c.contMDiff_attachingCoreMap_ambient n ρ hρ hblock u)
      (c.injective_mfderiv_attachingCoreMap_ambient n ρ hρ hblock u)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.injective_mfderiv_beltCoreMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.PositiveCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p + ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) (c.beltCoreMap ρ hρ hblock) v) := by
  exact
    Smale.RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 n) (c.beltCoreMap ρ hρ hblock) v
      (c.contMDiff_beltCoreMap_ambient n ρ hρ hblock v)
      (c.injective_mfderiv_beltCoreMap_ambient n ρ hρ hblock v)

private def Smale.ManifoldSmoothing.flattenTime (t : unitInterval) : unitInterval :=
  ⟨Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem Smale.ManifoldSmoothing.continuous_flattenTime : Continuous flattenTime :=
  (continuous_const.max
      (continuous_const.min
        ((continuous_const.mul continuous_subtype_val).sub continuous_const))) |>.subtype_mk
    _

private theorem
    Smale.ManifoldSmoothing.flattenTime_eq_zero (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 3) :
    flattenTime t = 0 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 0
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

private theorem
    Smale.ManifoldSmoothing.flattenTime_eq_one (t : unitInterval) (ht : 2 / 3 ≤ (t : ℝ)) :
    flattenTime t = 1 := by
  apply Subtype.ext
  change Max.max 0 (Min.min 1 (3 * (t : ℝ) - 1)) = 1
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

private def Smale.ManifoldSmoothing.flattenedHomotopyMap {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) : C(unitInterval × X, N)
    where
  toFun q := H (flattenTime q.1, q.2)
  continuous_toFun :=
    H.continuous.comp ((continuous_flattenTime.comp continuous_fst).prodMk continuous_snd)

private theorem
    Smale.ManifoldSmoothing.flattenedHomotopyMap_lower {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : (t : ℝ) ≤ 1 / 3) : flattenedHomotopyMap H (t, x) = f x := by
  change H (flattenTime t, x) = f x
  rw [flattenTime_eq_zero t ht, H.apply_zero]

private theorem
    Smale.ManifoldSmoothing.flattenedHomotopyMap_upper {X N : Type*} [TopologicalSpace X]
    [TopologicalSpace N] {f g : C(X, N)} (H : f.Homotopy g) (t : unitInterval) (x : X)
    (ht : 2 / 3 ≤ (t : ℝ)) : flattenedHomotopyMap H (t, x) = g x := by
  change H (flattenTime t, x) = g x
  rw [flattenTime_eq_one t ht, H.apply_one]

private def Smale.ManifoldSmoothing.homotopyCollars (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (q.1 : ℝ)}

private def
    Smale.ManifoldSmoothing.homotopyCollarNeighborhood (X : Type*) : Set (unitInterval × X) :=
  {q | (q.1 : ℝ) < 1 / 3 ∨ 2 / 3 < (q.1 : ℝ)}

private theorem Smale.ManifoldSmoothing.isClosed_homotopyCollars {X : Type*} [TopologicalSpace X] :
    IsClosed (homotopyCollars X) :=
  (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst))

private theorem Smale.ManifoldSmoothing.isOpen_homotopyCollarNeighborhood {X : Type*}
    [TopologicalSpace X] : IsOpen (homotopyCollarNeighborhood X) :=
  (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).union
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst))

private theorem Smale.ManifoldSmoothing.homotopyCollars_subset {X : Type*} :
    homotopyCollars X ⊆ homotopyCollarNeighborhood X := by
  rintro q (hl | hu)
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private def Smale.ChartMapPerturbation.coordinateFamily {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : F × X) : F :=
  c (f q.2) + β q.2 • q.1

private def
    Smale.ChartMapPerturbation.Valid {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) : Prop :=
  ∀ x ∈ tsupport β, coordinateFamily c f β (a, x) ∈ c.target

private def Smale.ChartMapPerturbation.perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) (x : X) : N := by
  classical exact if f x ∈ c.source then c.symm (coordinateFamily c f β (a, x)) else f x

private theorem
    Smale.ChartMapPerturbation.perturb_eq_of_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) {x : X}
    (hx : β x = 0) : perturb c f β a x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, ite_eq_left, coordinateFamily, hx, zero_smul, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, ite_false]

private theorem Smale.ChartMapPerturbation.perturb_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (x : X) :
    perturb c f β 0 x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, ite_eq_left, coordinateFamily, smul_zero, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, ite_false]

private theorem Smale.ChartMapPerturbation.valid_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : Valid c f β (0 : F) := by
  intro x hx
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

private theorem Smale.ChartMapPerturbation.coordinate_mem_target {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {x : X} (hx : f x ∈ c.source) :
    coordinateFamily c f β (a, x) ∈ c.target := by
  by_cases hβx : β x = 0
  · simpa only [coordinateFamily, hβx, zero_smul, add_zero] using c.map_source' hx
  · exact ha x (subset_tsupport β hβx)

private theorem
    Smale.ChartMapPerturbation.perturb_mem_source {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : perturb c f β a x ∈ c.source := by
  classical
  simp only [perturb, hx, ite_eq_left]
  exact c.map_target' (coordinate_mem_target c f β ha hx)

private theorem Smale.ChartMapPerturbation.chart_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : c (perturb c f β a x) = coordinateFamily c f β (a, x) := by
  classical
  simp only [perturb, hx, ite_eq_left]
  exact c.right_inv' (coordinate_mem_target c f β ha hx)

private theorem Smale.ChartMapPerturbation.contMDiffAt_coordinateFamily {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq)).comp q
        (hf.comp contMDiff_snd).contMDiffAt).add
    (((hβ.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_fst)

private theorem
    Smale.ChartMapPerturbation.eventually_valid {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  have hh := (contMDiffAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).continuousAt
  apply hh.preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

private theorem Smale.ChartMapPerturbation.exists_radius_valid {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_valid c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

private theorem Smale.ChartMapPerturbation.contMDiffAt_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := contMDiffAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, ite_eq_left, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

private theorem Smale.ChartMapPerturbation.contMDiff_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f β a) : ContMDiff I J ∞ (perturb c f β a) := by
  intro x
  exact
    (contMDiffAt_perturb c hf hβ hsupport (a, x) ha).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)

private theorem Smale.ChartMapPerturbation.continuousAt_coordinateFamily {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContinuousAt (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hq)).comp (f :=
        fun r : F × X => f r.2) (hf.comp continuous_snd).continuousAt).add
    ((hβ.comp continuous_snd).continuousAt.smul continuousAt_fst)

private theorem Smale.ChartMapPerturbation.eventually_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  apply (continuousAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

private theorem Smale.ChartMapPerturbation.exists_radius_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (eventually_valid_of_continuous c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

private theorem
    Smale.ChartMapPerturbation.continuousAt_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : Continuous f)
    (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) : ContinuousAt (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := continuousAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh :=
      (c.contMDiffOn_invFun.continuousOn.continuousAt (c.open_target.mem_nhds htarget)).comp
        hcoord
    apply hh.congr
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.comp continuous_snd).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, ite_eq_left, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact (perturb_eq_of_zero c f β r.1 hr).symm

private theorem Smale.ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous
    {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {β : X → ℝ} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {L : Set X} (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  apply
    (continuousAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

private theorem
    Smale.ChartMapPerturbation.contMDiffAt_perturb_of_contMDiffAt {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X) (hf : ContMDiffAt I J ∞ f q.2)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β q.2) (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord : ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp q
            (hf.comp q contMDiffAt_snd)).add
        ((hβ.comp q contMDiffAt_snd).smul contMDiffAt_fst)
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuousAt.comp continuousAt_snd).preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, ite_eq_left, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp q contMDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

private theorem Smale.ChartMapPerturbation.eventually_maps_compact_into_open {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {L : Set X}
    (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have hc :=
    (contMDiffAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

private theorem Smale.ChartMapPerturbation.norm_interval_smul_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ε : ℝ} {a : F} (ha : ‖a‖ < ε) (t : unitInterval) : ‖(t : ℝ) • a‖ < ε := by
  calc
    ‖(t : ℝ) • a‖ = (t : ℝ) * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    _ ≤ ‖a‖ := by nlinarith [t.2.2, norm_nonneg a]
    _ < ε := ha

private def Smale.ChartMapPerturbation.homotopyRel {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ} (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a)
    {a : F} (ha : ‖a‖ < ε) :
    (⟨f, hf.continuous⟩ : C(X, N)).HomotopyRel
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0}
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt ha q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk continuous_snd
    exact
      ContinuousAt.comp (f := fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2))
        (contMDiffAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a), q.2) hv).continuousAt
        hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a) x = perturb c f β a x
    rw [one_smul]
  prop' _ x hx := perturb_eq_of_zero c f β _ hx

private def Smale.ChartMapPerturbation.variablePerturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : X → F) (x : X) : N :=
  perturb c f β (a x) x

private theorem Smale.ChartMapPerturbation.continuous_variablePerturb {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    {a : X → F} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) (hvalid : ∀ x, Valid c f β (a x)) :
    Continuous (variablePerturb c f β a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact
    (continuousAt_perturb c hf hβ hsupport (a x, x) (hvalid x)).comp (f := fun y : X => (a y, y))
      (ha.prodMk continuous_id).continuousAt

private theorem Smale.ChartMapPerturbation.contMDiffAt_variablePerturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x) (ha : ContMDiffAt I 𝓘(ℝ, F) ∞ a x)
    (hvalid : Valid c f β (a x)) : ContMDiffAt I J ∞ (variablePerturb c f β a) x :=
  (contMDiffAt_perturb_of_contMDiffAt c hsupport (a x, x) hf hβ hvalid).comp x (f := fun y : X =>
    (a y, y)) (ha.prodMk contMDiffAt_id)

private def
    Smale.ChartMapPerturbation.variableHomotopyRel {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C : Set X} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0) :
    (⟨f, hf⟩ : C(X, N)).HomotopyRel
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a q.2) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt (hbound q.2) q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul (ha.comp continuous_snd)).prodMk
        continuous_snd
    exact
      (continuousAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a q.2), q.2) hv).comp (f :=
        fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a x) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a x) x = perturb c f β (a x) x
    rw [one_smul]
  prop' t x
    hx := by
    rcases hfixed x hx with hb | ha₀
    · exact perturb_eq_of_zero c f β _ hb
    · change perturb c f β ((t : ℝ) • a x) x = f x
      rw [ha₀, smul_zero, perturb_zero]

private def Smale.ChartMapPerturbation.cutoffCoordinates {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) (x : X) : F :=
  χ x • c (f x)

private theorem Smale.ChartMapPerturbation.cutoffCoordinates_eq_of_one {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) {x : X} (hx : χ x = 1) :
    cutoffCoordinates c f χ x = c (f x) := by simp only [cutoffCoordinates, hx, one_smul]

private theorem Smale.ChartMapPerturbation.continuous_cutoffCoordinates {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) :
    Continuous (cutoffCoordinates c f χ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.continuousAt.smul
        ((c.contMDiffOn_toFun.continuousOn.continuousAt
              (c.open_source.mem_nhds (hsupport hx))).comp
          hf.continuousAt)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : F))).congr
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

private theorem Smale.ChartMapPerturbation.contMDiffAt_cutoffCoordinates {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) : ContMDiffAt I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) x := by
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.smul ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds (hsupport hx))).comp x hf)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

private theorem
    Smale.ChartMapPerturbation.exists_smooth_coordinate_approximation {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ} [FiniteDimensional ℝ E]
    [IsManifold I ∞ X] [SigmaCompactSpace X] [T2Space X] (hf : Continuous f)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {C U : Set X}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : X → F,
      ContMDiff I 𝓘(ℝ, F) ∞ g ∧
        (∀ x, Dist.dist (g x) (cutoffCoordinates c f χ x) < ε) ∧
          Set.EqOn g (cutoffCoordinates c f χ) C := by
  have hk := continuous_cutoffCoordinates c hf hχ.continuous hsupport
  have hkU : ContMDiffOn I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) U := by
    intro x hx
    exact
      (contMDiffAt_cutoffCoordinates c hsupport ((hfU x hx).contMDiffAt (hU.mem_nhds hx))
          hχ.contMDiffAt).contMDiffWithinAt
  have hUn : U ∈ 𝓝ˢ C := mem_nhdsSet_iff_forall.mpr (fun x hx => hU.mem_nhds (hCU hx))
  obtain ⟨g, hg, hgeq, _⟩ :=
    hk.exists_contMDiff_approx_and_eqOn I ⊤ (continuous_const (y := ε)) (fun _ => hε) hC hUn hkU
  exact ⟨g, g.contMDiff, hg, hgeq⟩

private def Smale.ChartMapPerturbation.smoothedMap {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) : X → N :=
  variablePerturb c f β (fun x => g x - cutoffCoordinates c f χ x)

private theorem Smale.ChartMapPerturbation.coordinateFamily_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) {x : X}
    (hβx : β x = 1) (hχx : χ x = 1) :
    coordinateFamily c f β (g x - cutoffCoordinates c f χ x, x) = g x := by
  simp only [coordinateFamily, cutoffCoordinates, hβx, hχx, one_smul]
  abel

private theorem Smale.ChartMapPerturbation.smoothedMap_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ)
    (g : X → F) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1)
    {x : X} (hβx : β x = 1) : smoothedMap c f β χ g x = c.symm (g x) := by
  classical
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  change perturb c f β (g x - cutoffCoordinates c f χ x) x = _
  have hsource : f x ∈ c.source := hsupport hs
  simp only [perturb, hsource, ite_eq_left]
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)]

private theorem
    Smale.ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1) {x : X}
    (hplateau : β =ᶠ[𝓝 x] (fun _ => 1)) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x := by
  have hβx : β x = 1 := hplateau.eq_of_nhds
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  have htarget := coordinate_mem_target c f β hvalid (hsupport hs)
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)] at htarget
  have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp x hg
  apply hh.congr_of_eventuallyEq
  filter_upwards [hplateau] with y hy
  exact smoothedMap_eq_on_plateau c f β χ g hsupport hnested hy

private theorem Smale.ChartMapPerturbation.contMDiffAt_smoothedMap_of_old {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hβsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X}
    (hf : ContMDiffAt I J ∞ f x) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x :=
  contMDiffAt_variablePerturb c hβsupport hf hβ
    (hg.sub (contMDiffAt_cutoffCoordinates c hχsupport hf hχ)) hvalid

private def Smale.HomotopicRelWithin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (C K : Set X) (O : Set Y) : Prop :=
  ∃ F : f.HomotopyRel g C, ∀ t : unitInterval, Set.MapsTo (fun x => F (t, x)) K O

private theorem
    Smale.HomotopicRelWithin.refl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {O : Set Y} (f : C(X, Y)) (C : Set X) (hmaps : Set.MapsTo f K O) :
    Smale.HomotopicRelWithin f f C K O :=
  ⟨ContinuousMap.HomotopyRel.refl f C, fun _ => hmaps⟩

private theorem Smale.HomotopicRelWithin.homotopicRel {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : Smale.HomotopicRelWithin f g C K O) : f.HomotopicRel g C := by
  obtain ⟨F, _⟩ := H
  exact ⟨F⟩

private theorem Smale.HomotopicRelWithin.mapsTo_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} {C K : Set X} {O : Set Y}
    (H : Smale.HomotopicRelWithin f g C K O) : Set.MapsTo g K O := by
  obtain ⟨F, hF⟩ := H
  intro x hx
  exact (congrArg (fun y => y ∈ O) (F.map_one_left x)).mp (hF 1 hx)

private theorem
    Smale.HomotopicRelWithin.trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} {C K : Set X} {O : Set Y} (H : Smale.HomotopicRelWithin f g C K O)
    (G : Smale.HomotopicRelWithin g h C K O) : Smale.HomotopicRelWithin f h C K O := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := G
  refine ⟨ContinuousMap.HomotopyRel.trans F G, ?_⟩
  intro t x hx
  change (F.toHomotopy.trans G.toHomotopy) (t, x) ∈ O
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _ hx
  · exact hG _ hx

private theorem
    Smale.HomotopicRelWithin.mono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {C K : Set X} {O : Set Y} (H : Smale.HomotopicRelWithin f g C K O)
    {D L : Set X} {P : Set Y} (hDC : D ⊆ C) (hLK : L ⊆ K) (hOP : O ⊆ P) :
    Smale.HomotopicRelWithin f g D L P := by
  obtain ⟨F, hF⟩ := H
  exact
    ⟨{ toHomotopy := F.toHomotopy, prop' := fun t x hx => F.eq_fst t (hDC hx) }, fun t x hx =>
      hOP (hF t (hLK hx))⟩

private theorem Smale.ChartMapPerturbation.perturb_mem_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {O : Set N} (hsource : c.source ⊆ O) {x : X} (hx : f x ∈ O) :
    perturb c f β a x ∈ O := by
  by_cases hxc : f x ∈ c.source
  · exact hsource (perturb_mem_source c f β ha hxc)
  · simpa only [perturb, ite_eq_right hxc] using hx

private theorem
    Smale.ChartMapPerturbation.homotopicRelWithin_of_source_subset {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ}
    (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a) {a : F} (ha : ‖a‖ < ε) {D : Set X} {O : Set N}
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    Smale.HomotopicRelWithin (⟨f, hf.continuous⟩ : C(X, N))
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0} D O := by
  refine ⟨homotopyRel c hf hβ hsupport hvalid ha, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt ha t)) hsource (hmaps hx)

private theorem
    Smale.ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : X → F}
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C D : Set X} {O : Set N} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0)
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    Smale.HomotopicRelWithin (⟨f, hf⟩ : C(X, N))
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C D O := by
  refine ⟨variableHomotopyRel c hf hβ hsupport ha hvalid hbound hfixed, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt (hbound x) t)) hsource
      (hmaps hx)

private structure
    Smale.ManifoldSmoothing.MapSmoothingPatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N] where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  outer : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  outer_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ outer
  compact : HasCompactSupport cutoff
  outer_compact : HasCompactSupport outer
  nested : ∀ x ∈ tsupport cutoff, outer x = 1

private def Smale.ManifoldSmoothing.MapSmoothingPatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : Smale.ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.outer) p.chart.source

private def
    Smale.ManifoldSmoothing.MapSmoothingPatch.plateau {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (p : Smale.ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) : Set X :=
  interior {x | p.cutoff x = 1}

private theorem
    Smale.ManifoldSmoothing.MapSmoothingPatch.inner_support_subset_outer {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : Smale.ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) :
    tsupport p.cutoff ⊆ tsupport p.outer := by
  intro x hx
  apply subset_tsupport p.outer
  change p.outer x ≠ 0
  rw [p.nested x hx]
  exact one_ne_zero

private theorem Smale.ManifoldSmoothing.MapSmoothingPatch.inner_compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : Smale.ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {f : X → N} (hf : p.Compatible f) : tsupport p.cutoff ⊆ f ⁻¹' p.chart.source := fun _ hx =>
  hf (p.inner_support_subset_outer hx)

private theorem
    Smale.ManifoldSmoothing.MapSmoothingPatch.plateau_eventually_one {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : Smale.ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {x : X} (hx : x ∈ p.plateau) : p.cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact interior_subset (s := {y : X | p.cutoff y = 1}) hy

private theorem
    Smale.ManifoldSmoothing.exists_smoothing_patch_step_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ E] [IsManifold I ∞ X] [SigmaCompactSpace X]
    [T2Space X] {ι : Type*} [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (i : ι)
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        Smale.HomotopicRelWithin f f' C D O ∧
          ∀ x, ContMDiffAt I J ∞ f x ∨ x ∈ (p i).plateau → ContMDiffAt I J ∞ f' x := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous (p i).chart
        f.continuous (p i).smooth.continuous hinner (p j).outer_compact.isCompact
        (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid_of_continuous (p i).chart f.continuous
      (p i).smooth.continuous (p i).compact hinner
  obtain ⟨g, hg, happrox, heq⟩ :=
    Smale.ChartMapPerturbation.exists_smooth_coordinate_approximation (p i).chart f.continuous
      (p i).outer_smooth (hcompatible i) hC hU hCU hfU (lt_min hδ hr)
  let a : X → G := fun x =>
    g x - Smale.ChartMapPerturbation.cutoffCoordinates (p i).chart f (p i).outer x
  have ha : Continuous a :=
    hg.continuous.sub
      (Smale.ChartMapPerturbation.continuous_cutoffCoordinates (p i).chart f.continuous
        (p i).outer_smooth.continuous (hcompatible i))
  have hbound (x : X) : ‖a x‖ < Min.min δ r := by simpa only [a, dist_eq_norm] using happrox x
  have haδ (x : X) : ‖a x‖ < δ := (lt_min_iff.mp (hbound x)).1
  have har (x : X) : ‖a x‖ < r := (lt_min_iff.mp (hbound x)).2
  let f' : C(X, N) :=
    ⟨Smale.ChartMapPerturbation.variablePerturb (p i).chart f (p i).cutoff a,
      Smale.ChartMapPerturbation.continuous_variablePerturb (p i).chart f.continuous
        (p i).smooth.continuous hinner ha (fun x => hvalid _ (har x))⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro j x hx
    have hh :=
      hδkeep
        (show a x ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ x)
    exact hh j hx
  · exact
      Smale.ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset (p i).chart
        f.continuous (p i).smooth.continuous hinner ha hvalid har
        (fun x hx => Or.inr (sub_eq_zero.mpr (heq hx))) hsource hmaps
  · intro x hx
    rcases hx with hold | hplateau
    · exact
        Smale.ChartMapPerturbation.contMDiffAt_smoothedMap_of_old (p i).chart hinner
          (hcompatible i) hold (p i).smooth.contMDiffAt (p i).outer_smooth.contMDiffAt
          hg.contMDiffAt (hvalid _ (har x))
    · exact
        Smale.ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau (p i).chart hinner
          (p i).nested ((p i).plateau_eventually_one hplateau) hg.contMDiffAt (hvalid _ (har x))

private theorem
    Smale.ManifoldSmoothing.exists_finite_patch_smoothing_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        Smale.HomotopicRelWithin f f' C D O ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hcompatible, Smale.HomotopicRelWithin.refl f C hmaps, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hc₁, hhom₁, hsm₁⟩ := ih
    have hf₁U : ContMDiffOn I J ∞ f₁ U := by
      intro x hx
      exact (hsm₁ x (Or.inl ((hfU x hx).contMDiffAt (hU.mem_nhds hx)))).contMDiffWithinAt
    obtain ⟨f₂, hc₂, hhom₂, hsm₂⟩ :=
      exists_smoothing_patch_step_within_target p i f₁ hc₁ hC hU hCU hf₁U (hsource i)
        hhom₁.mapsTo_right
    refine ⟨f₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hsm₂ x
    rcases hx with hold | ⟨j, hj, hplateau⟩
    · exact Or.inl (hsm₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hplateau
      · exact Or.inl (hsm₁ x (Or.inr ⟨j, hjs, hplateau⟩))

private theorem Smale.ManifoldSmoothing.exists_finite_patch_smoothing {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        f.HomotopicRel f' C ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  obtain ⟨f', hc, hrel, hsm⟩ :=
    exists_finite_patch_smoothing_within_target p f hcompatible hC hU hCU hfU
      (fun _ => Set.subset_univ _) (Set.mapsTo_univ f Set.univ) s
  exact ⟨f', hc, hrel.homotopicRel, hsm⟩

private theorem Smale.ManifoldSmoothing.exists_smoothing_of_finite_patches {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (hcover : ∀ x, ∃ i, x ∈ (p i).plateau) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing p f hcompatible hC hU hCU hfU Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hsm x (Or.inr ⟨i, Finset.mem_univ i, hi⟩)

private theorem Smale.ManifoldSmoothing.exists_smoothing_patch_at_in_open {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N),
      p.Compatible f ∧ x ∈ p.plateau ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  let c := Smale.PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∈ 𝓝 x := (c.open_source.preimage f.continuous).mem_nhds hsource
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  have hχone : {y : X | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hχone
  let p : MapSmoothingPatch I J (X := X) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  refine ⟨p, hχ, ?_, fun _ hx => hx.2⟩
  change x ∈ interior {y : X | β y = 1}
  exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one

private theorem Smale.ManifoldSmoothing.exists_smoothing_patch_at {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau := by
  obtain ⟨p, hc, hp, _⟩ :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f x isOpen_univ (Set.mem_univ _)
  exact ⟨p, hc, hp⟩

private theorem Smale.ManifoldSmoothing.exists_smooth_map_homotopicRel {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  have hp (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau :=
    exists_smoothing_patch_at f x
  choose p hpcompatible hpplateau using hp
  have hopen (x : X) : IsOpen (p x).plateau := isOpen_interior
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (p x).plateau := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hpplateau x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (p x).plateau) hopen hcover
  apply
    exists_smoothing_of_finite_patches (fun i : s => p i.1) f (fun i => hpcompatible i.1) hC hU
      hCU hfU
  intro x
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hix⟩

private theorem Smale.ManifoldSmoothing.exists_smooth_map_homotopic {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.Homotopic f' := by
  obtain ⟨f', hf', ⟨H⟩⟩ :=
    exists_smooth_map_homotopicRel (I := I) (J := J) f isClosed_empty isOpen_empty
      (Set.Subset.refl ∅) contMDiffOn_empty
  exact ⟨f', hf', ⟨H.toHomotopy⟩⟩

private theorem Smale.ManifoldSmoothing.contMDiffOn_flattenedHomotopyMap {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ContMDiffOn ((𝓡∂ 1).prod I) J ∞ (flattenedHomotopyMap H) (homotopyCollarNeighborhood X) := by
  rintro q (hl | hu)
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => f r.2) :=
      hf.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => f r.2) := by
      have hn : {r : unitInterval × X | (r.1 : ℝ) < 1 / 3} ∈ 𝓝 q :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds hl
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_lower H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => g r.2) :=
      hg.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => g r.2) := by
      have hn : {r : unitInterval × X | 2 / 3 < (r.1 : ℝ)} ∈ 𝓝 q :=
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds hu
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_upper H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

private theorem Smale.ManifoldSmoothing.exists_smooth_homotopy_with_collars {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ∃ H' : f.Homotopy g,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H' ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H' (t, x) = f x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H' (t, x) = g x) := by
  obtain ⟨F, hF, ⟨K⟩⟩ :=
    exists_smooth_map_homotopicRel (flattenedHomotopyMap H) isClosed_homotopyCollars
      isOpen_homotopyCollarNeighborhood homotopyCollars_subset
      (contMDiffOn_flattenedHomotopyMap hf hg H)
  have hlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : F (t, x) = f x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inl ht)
    rw [← heq]
    exact flattenedHomotopyMap_lower H t x (by linarith)
  have hhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : F (t, x) = g x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inr ht)
    rw [← heq]
    exact flattenedHomotopyMap_upper H t x (by linarith)
  let H' : f.Homotopy g :=
    { toContinuousMap := F
      map_zero_left := fun x => hlo 0 x (by norm_num)
      map_one_left := fun x => hhi 1 x (by norm_num) }
  exact ⟨H', hF, hlo, hhi⟩

private theorem Smale.GeneralPosition.dimH_image_chart_le {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] {f : X → F} {s : Set X} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (x : X) : dimH (f '' ((extChartAt I x).source ∩ s)) ≤ Module.finrank ℝ E := by
  let c := extChartAt I x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp ((contMDiffOn_extChartAt_symm x).mono Set.inter_subset_left)
        Set.inter_subset_right).contDiffOn
  have hVsub : V ⊆ Set.range I := fun y hy => extChartAt_target_subset_range x hy.1
  have hdim : dimH ((f ∘ c.symm) '' V) ≤ dimH V := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro y hy
    have ht : c.target ∈ 𝓝[Set.range I] y := extChartAt_target_mem_nhdsWithin_of_mem hy.1
    have hp : c.symm ⁻¹' s ∈ 𝓝[Set.range I] y := by
      rw [← nhdsWithin_extChartAt_target_eq_of_mem hy.1]
      exact
        (contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) x).continuousOn y
            hy.1 |>.preimage_mem_nhdsWithin
          (hs.mem_nhds hy.2)
    have hV : V ∈ 𝓝[Set.range I] y := Filter.inter_mem ht hp
    have hd : ContDiffWithinAt ℝ 1 (f ∘ c.symm) (Set.range I) y :=
      ((hfc y hy).of_le (by simp)).mono_of_mem_nhdsWithin hV
    obtain ⟨L, U, hU, hLip⟩ := hd.exists_lipschitzOnWith I.convex_range
    exact ⟨L, U, nhdsWithin_mono y hVsub hU, hLip⟩
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        rwa [c.left_inv hyc]
      · exact congrArg f (c.left_inv hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact hdim.trans ((dimH_mono (Set.subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

private theorem
    Smale.GeneralPosition.dimH_image_manifold_le {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [LindelofSpace X] {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) : dimH (f '' s) ≤ Module.finrank ℝ E := by
  let U : X → Set X := fun x => (extChartAt I x).source
  have hU : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_source x
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x => iSup_le (fun _ => dimH_image_chart_le hs hf x))

private theorem
    Smale.GeneralPosition.dense_compl_manifold_image {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [LindelofSpace X] [FiniteDimensional ℝ F] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

private theorem Smale.exists_small_localized_image_avoidance {E E' F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] [LindelofSpace (X × Y)] {f : X → F} {g : Y → F} {β : X → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hg : ContMDiff J 𝓘(ℝ, F) ∞ g) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ∀ x, β x ≠ 0 → ∀ y, f x + β x • a ≠ g y := by
  let s : Set (X × Y) := {p | β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (g p.2 - f p.1)
  have hs : IsOpen s := isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const
  have hb : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ bad s :=
    ((hβ.comp contMDiff_fst).contMDiffOn.inv₀ (fun _ hp => hp)).smul
      ((hg.comp contMDiff_snd).sub (hf.comp contMDiff_fst)).contMDiffOn
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨a, ha, haε⟩ := hdense.exists_dist_lt 0 hε
  refine ⟨a, ?_, ?_⟩
  · simpa only [dist_zero_left] using haε
  · intro x hx y hxy
    apply ha
    refine ⟨(x, y), hx, ?_⟩
    change (β x)⁻¹ • (g y - f x) = a
    rw [← hxy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

private theorem
    Smale.ChartMapPerturbation.exists_small_avoiding_parameter {E E' G F H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N] [LindelofSpace (X × Y)]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧ ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  let s : Set (X × Y) := {p | f p.1 ∈ c.source ∧ g p.2 ∈ c.source ∧ β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (c (g p.2) - c (f p.1))
  have hs : IsOpen s :=
    (c.open_source.preimage (hf.continuous.comp continuous_fst)).inter
      ((c.open_source.preimage (hg.continuous.comp continuous_snd)).inter
        (isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const))
  have hb : ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ bad s := by
    intro p hp
    have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (f q.1)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.1)).comp p
        (hf.comp contMDiff_fst).contMDiffAt
    have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (g q.2)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.2.1)).comp p
        (hg.comp contMDiff_snd).contMDiffAt
    exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hp.2.2).smul (hcg.sub hcf)).contMDiffWithinAt
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := Smale.GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, ha, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have haε : ‖a‖ < ε :=
    (lt_min_iff.mp (show ‖a‖ < Min.min ε δ by simpa only [dist_zero_left] using har)).1
  have haδ : ‖a‖ < δ :=
    (lt_min_iff.mp (show ‖a‖ < Min.min ε δ by simpa only [dist_zero_left] using har)).2
  have hva : Valid c f β a := hvalid a haδ
  refine ⟨a, haε, hva, contMDiff_perturb c hf hβ hsupport hva, ?_⟩
  intro x hx y hxy
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := hxy ▸ perturb_mem_source c f β hva hfx
  have heq : c (f x) + β x • a = c (g y) := by
    rw [← hxy, chart_perturb c f β hva hfx]
    rfl
  apply ha
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

private structure
    Smale.GeneralPosition.MapAvoidancePatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (C : Set X) where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  compact : HasCompactSupport cutoff
  fixed : ∀ x ∈ C, cutoff x = 0

private def Smale.GeneralPosition.MapAvoidancePatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {C : Set X} (p : Smale.GeneralPosition.MapAvoidancePatch I J (N := N) C)
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.cutoff) p.chart.source

private theorem Smale.GeneralPosition.exists_patch_step {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    {E' H' Y : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold I' ∞ Y] [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (i : ι) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          f.HomotopicRel f' C ∧
            ∀ x, (f x ∉ Set.range g ∨ (p i).cutoff x ≠ 0) → f' x ∉ Set.range g := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ :=
    Smale.ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, _, hsmooth, havoid⟩ :=
    Smale.ChartMapPerturbation.exists_small_avoiding_parameter (p i).chart hf hg (p i).smooth
      (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(X, N) := ⟨_, hsmooth.continuous⟩
  have H :=
    Smale.ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth (hcompatible i) hvalid har
  refine ⟨f', hsmooth, ?_, ?_, ?_⟩
  · exact hδkeep (by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  · exact
      ⟨{  toHomotopy := H.toHomotopy
          prop' := fun t x hx => H.prop t x ((p i).fixed x hx) }⟩
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ Set.range g := hx.resolve_right (Classical.not_not.mpr hzero)
      change Smale.ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ Set.range g
      rwa [Smale.ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, hy⟩
      exact havoid x hzero y hy.symm

private theorem Smale.GeneralPosition.exists_finite_patch_avoidance {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (s : Finset ι) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          f.HomotopicRel f' C ∧
            ∀ x, (f x ∉ Set.range g ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ Set.range g := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, havoid₂⟩ := exists_patch_step p i f₁ g hf₁ hg hc₁ hdim
    refine ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hnonzero⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hnonzero
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hnonzero⟩))

private theorem
    Smale.GeneralPosition.exists_avoidance_of_finite_patches {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hcover : ∀ x, f x ∈ Set.range g → ∃ i, (p i).cutoff x ≠ 0) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', hf', _, hhom, havoid⟩ :=
    exists_finite_patch_avoidance p f g hf hg hcompatible hdim Finset.univ
  refine ⟨f', hf', hhom, Set.disjoint_left.mpr ?_⟩
  rintro z ⟨x, rfl⟩ hz
  apply havoid x _ hz
  by_cases hx : f x ∈ Set.range g
  · obtain ⟨i, hi⟩ := hcover x hx
    exact Or.inr ⟨i, Finset.mem_univ i, hi⟩
  · exact Or.inl hx

private theorem Smale.GeneralPosition.exists_avoidance_patch_at {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) {C : Set X} (hC : IsClosed C) {x : X} (hx : x ∉ C) :
    ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x ≠ 0 := by
  classical
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hsource : f x ∈ c.source := mem_extChartAt_source (I := J) (f x)
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  let p : MapAvoidancePatch I J (N := N) C :=
    { chart := c
      cutoff := φ
      smooth := φ.contMDiff
      compact := φ.hasCompactSupport
      fixed := by
        intro y hy
        exact image_eq_zero_of_notMem_tsupport (fun ht => (hφ ht).2 hy) }
  refine ⟨p, ?_, ?_⟩
  · exact fun y hy => (hφ hy).1
  · change φ x ≠ 0
    rw [φ.eq_one]
    exact one_ne_zero

private theorem Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range
    {E G H K X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] {E' H' Y : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace X] [LindelofSpace (X × Y)] (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (Set.range g))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {C : Set X}
    (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ Set.range g) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) := by
  classical
  let bad : Set X := f ⁻¹' Set.range g
  have hbad : IsCompact bad := (hclosed.preimage f.continuous).isCompact
  have hp (x : bad) : ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    exists_avoidance_patch_at f hC (fun hx => hfixed x.1 hx x.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff) hopen hcover
  apply
    exists_avoidance_of_finite_patches (fun i : s => p i.1) f g hf hg (fun i => hpcompatible i.1)
      hdim
  intro x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, hix⟩

private theorem Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] {E' H' Y : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace X] [CompactSpace Y] [T2Space N] (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {C : Set X}
    (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ Set.range g) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) :=
  exists_disjoint_smooth_map_homotopicRel_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hdim hC hfixed

private def Smale.ImageComplement.domain {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : TopologicalSpace.Opens N :=
  ⟨(Set.range g)ᶜ, (isCompact_range g.continuous).isClosed.isOpen_compl⟩

private def Smale.ImageComplement.inclusion {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : C(domain g, N) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem Smale.ImageComplement.exists_smooth_homotopy_of_ambient_homotopic {Y N : Type*}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace N] [T2Space N]
    {E E' G H H' K X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [ChartedSpace K N] [IsManifold J ∞ N] (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g)) (hf₀ : ContMDiff I J ∞ f₀) (hf₁ : ContMDiff I J ∞ f₁)
    (hambient :
      ((Smale.ImageComplement.inclusion g).comp f₀).Homotopic
        ((Smale.ImageComplement.inclusion g).comp f₁)) :
    ∃ H : f₀.Homotopy f₁,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f₀ x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = f₁ x) := by
  obtain ⟨H⟩ := hambient
  have hval : ContMDiff J J ∞ (Smale.ImageComplement.inclusion g) := contMDiff_subtype_val
  have hf₀val : ContMDiff I J ∞ ((Smale.ImageComplement.inclusion g).comp f₀) := hval.comp hf₀
  have hf₁val : ContMDiff I J ∞ ((Smale.ImageComplement.inclusion g).comp f₁) := hval.comp hf₁
  obtain ⟨H, hH, hlo, hhi⟩ :=
    Smale.ManifoldSmoothing.exists_smooth_homotopy_with_collars hf₀val hf₁val H
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × E) + Module.finrank ℝ E' < Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ q ∈ Smale.ManifoldSmoothing.homotopyCollars X, H q ∉ Set.range g := by
    rintro ⟨t, x⟩ (ht | ht)
    · rw [hlo t x ht]
      exact (f₀ x).property
    · rw [hhi t x ht]
      exact (f₁ x).property
  obtain ⟨F, hF, hrel, hdisjoint⟩ :=
    Smale.GeneralPosition.exists_disjoint_smooth_map_homotopicRel H.toContinuousMap g hH hg hd
      Smale.ManifoldSmoothing.isClosed_homotopyCollars hfixed
  have heq : Set.EqOn F H (Smale.ManifoldSmoothing.homotopyCollars X) := fun _ hq =>
    (hrel.fst_eq_snd hq).symm
  have havoid : ∀ q, F q ∈ domain g := by
    intro q
    change F q ∉ Set.range g
    exact fun hq => Set.disjoint_left.mp hdisjoint ⟨q, rfl⟩ hq
  let A : C(unitInterval × X, domain g) := ⟨fun q => ⟨F q, havoid q⟩, F.continuous.subtype_mk _⟩
  have hA : ContMDiff ((𝓡∂ 1).prod I) J ∞ A := (ContMDiff.subtypeVal_comp_iff (domain g) A).mp hF
  have hAlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : A (t, x) = f₀ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ Smale.ManifoldSmoothing.homotopyCollars X from Or.inl ht)).trans
        (hlo t x ht)
  have hAhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : A (t, x) = f₁ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ Smale.ManifoldSmoothing.homotopyCollars X from Or.inr ht)).trans
        (hhi t x ht)
  exact
    ⟨{  toContinuousMap := A
        map_zero_left := fun x => hAlo 0 x (by norm_num)
        map_one_left := fun x => hAhi 1 x (by norm_num) }, hA, hAlo, hAhi⟩

private theorem
    Smale.ImageComplement.homotopic_of_ambient_homotopic {Y N : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace N] [T2Space N] {E E' G H H' K X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [ChartedSpace K N] [IsManifold J ∞ N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g))
    (hambient :
      ((Smale.ImageComplement.inclusion g).comp f₀).Homotopic
        ((Smale.ImageComplement.inclusion g).comp f₁)) :
    f₀.Homotopic f₁ := by
  obtain ⟨f₀', hf₀', h₀⟩ :=
    Smale.ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₀
  obtain ⟨f₁', hf₁', h₁⟩ :=
    Smale.ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₁
  have ha₀ := (ContinuousMap.Homotopic.refl (Smale.ImageComplement.inclusion g)).comp h₀
  have ha₁ := (ContinuousMap.Homotopic.refl (Smale.ImageComplement.inclusion g)).comp h₁
  obtain ⟨H, -⟩ :=
    exists_smooth_homotopy_of_ambient_homotopic g hg hdim f₀' f₁' hf₀' hf₁'
      (ha₀.symm.trans (hambient.trans ha₁))
  exact h₀.trans ((show f₀'.Homotopic f₁' from ⟨H⟩).trans h₁.symm)

private abbrev Smale.DiskDouble.Disk (E : Type*) [NormedAddCommGroup E] :=
  Metric.closedBall (0 : E) 1

private abbrev Smale.DiskDouble.Boundary (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

private def
    Smale.DiskDouble.boundary (E : Type*) [NormedAddCommGroup E] (x : Boundary E) : Disk E :=
  ⟨x, Metric.sphere_subset_closedBall x.property⟩

private def Smale.DiskDouble.Rel {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :
    Disk E ⊕ Disk E → Disk E ⊕ Disk E → Prop
  | .inl x, .inr y => ∃ z : Boundary E, x = boundary E z ∧ y = boundary E (e z)
  | _, _ => False

private abbrev
    Smale.DiskDouble.Space {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :=
  Quot (Smale.DiskDouble.Rel e)

private def Smale.DiskDouble.untwist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Disk E ⊕ Disk E ≃ₜ Disk E ⊕ Disk E :=
  (Homeomorph.refl (Disk E)).sumCongr (Smale.RadialExtension.closedBallHomeomorph e.symm)

private theorem
    Smale.DiskDouble.rel_untwist_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) (x y : Disk E ⊕ Disk E) :
    Smale.DiskDouble.Rel e x y ↔
      Smale.DiskDouble.Rel (Homeomorph.refl (Boundary E)) (untwist e x) (untwist e y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr
      y =>
      change
        (∃ z, x = boundary E z ∧ y = boundary E (e z)) ↔
          ∃ z,
            x = boundary E z ∧ Smale.RadialExtension.closedBallHomeomorph e.symm y = boundary E z
      constructor
      · rintro ⟨z, rfl, rfl⟩
        refine ⟨z, rfl, ?_⟩
        simp [boundary]
      · rintro ⟨z, hx, hy⟩
        refine ⟨z, hx, ?_⟩
        apply (Smale.RadialExtension.closedBallHomeomorph e.symm).injective
        rw [hy]
        simp [boundary]
  | inr x => cases y <;> rfl

private def
    Smale.DiskDouble.homeomorphUntwisted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Space e ≃ₜ Space (Homeomorph.refl (Boundary E)) :=
  Homeomorph.Quot.congr (untwist e) (rel_untwist_iff e)

private abbrev Smale.Hemisphere.Ambient (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

private abbrev Smale.Hemisphere.Ball (n : ℕ) :=
  Smale.DiskDouble.Disk (Ambient n)

private abbrev Smale.Hemisphere.Sphere (n : ℕ) :=
  Metric.sphere (0 : Ambient (n + 1)) 1

private def Smale.Hemisphere.radius {n : ℕ} (x : Ball n) : ℝ :=
  Real.sqrt (1 - ‖(x : Ambient n)‖ ^ 2)

private theorem Smale.Hemisphere.radius_sq {n : ℕ} (x : Ball n) :
    radius x ^ 2 = 1 - ‖(x : Ambient n)‖ ^ 2 := by
  apply Real.sq_sqrt
  have hx : ‖(x : Ambient n)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  nlinarith [norm_nonneg (x : Ambient n)]

private def Smale.Hemisphere.vector {n : ℕ} (b : Bool) (x : Ball n) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.cons (if b then radius x else -radius x) (x : Ambient n))

@[simp]
private theorem Smale.Hemisphere.vector_zero {n : ℕ} (b : Bool) (x : Ball n) :
    vector b x 0 = if b then radius x else -radius x :=
  rfl

@[simp]
private theorem Smale.Hemisphere.vector_succ {n : ℕ} (b : Bool) (x : Ball n) (i : Fin n) :
    vector b x i.succ = (x : Ambient n) i :=
  rfl

private theorem
    Smale.Hemisphere.vector_norm_sq {n : ℕ} (b : Bool) (x : Ball n) : ‖vector b x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ]
  rw [← EuclideanSpace.real_norm_sq_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;> rw [radius_sq] <;> ring

private def Smale.Hemisphere.point {n : ℕ} (b : Bool) (x : Ball n) : Sphere n :=
  ⟨vector b x, by
    rw [mem_sphere_zero_iff_norm]
    have h := vector_norm_sq b x
    nlinarith [norm_nonneg (vector b x)]⟩

@[simp]
private theorem Smale.Hemisphere.point_zero {n : ℕ} (b : Bool) (x : Ball n) :
    (point b x : Ambient (n + 1)) 0 = if b then radius x else -radius x :=
  rfl

private theorem Smale.Hemisphere.continuous_radius {n : ℕ} : Continuous (radius (n := n)) := by
  unfold radius
  fun_prop

private theorem
    Smale.Hemisphere.continuous_vector {n : ℕ} (b : Bool) : Continuous (vector (n := n) b) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases b
    · exact continuous_radius.neg
    · exact continuous_radius
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val

private theorem
    Smale.Hemisphere.continuous_point {n : ℕ} (b : Bool) : Continuous (point (n := n) b) :=
  (continuous_vector b).subtype_mk _

private theorem Smale.Hemisphere.point_injective {n : ℕ} (b : Bool) :
    Function.Injective (point (n := n) b) := by
  intro x y h
  apply Subtype.ext
  ext i
  exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h

@[simp]
private theorem
    Smale.Hemisphere.radius_boundary {n : ℕ} (x : Smale.DiskDouble.Boundary (Ambient n)) :
    radius (Smale.DiskDouble.boundary (Ambient n) x) = 0 := by
  have hx : ‖(x : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp [radius, Smale.DiskDouble.boundary, hx]

private theorem
    Smale.Hemisphere.point_boundary {n : ℕ} (x : Smale.DiskDouble.Boundary (Ambient n)) :
    point Bool.false (Smale.DiskDouble.boundary (Ambient n) x) =
      point Bool.true (Smale.DiskDouble.boundary (Ambient n) x) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

private theorem Smale.Hemisphere.point_false_eq_true_iff {n : ℕ} (x y : Ball n) :
    point Bool.false x = point Bool.true y ↔
      ∃ z : Smale.DiskDouble.Boundary (Ambient n),
        x = Smale.DiskDouble.boundary (Ambient n) z ∧
          y = Smale.DiskDouble.boundary (Ambient n) z := by
  constructor
  · intro h
    have hxy : x = y := by
      apply Subtype.ext
      ext i
      exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h
    subst y
    have hr : radius x = 0 := by
      have hh := congrArg (fun z : Sphere n => (z : Ambient (n + 1)) 0) h
      simp only [point_zero, Bool.false_eq_true, ↓reduceIte] at hh
      linarith
    have hn : ‖(x : Ambient n)‖ = 1 := by
      have hs := radius_sq x
      rw [hr] at hs
      nlinarith [norm_nonneg (x : Ambient n)]
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr hn⟩, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    exact point_boundary z

private theorem
    Smale.ImageComplement.nullhomotopic_of_ambient_nullhomotopic {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f : C(X, domain g))
    (hambient :
      ∃ c, ((Smale.ImageComplement.inclusion g).comp f).Homotopic (ContinuousMap.const X c)) :
    ∃ c, f.Homotopic (ContinuousMap.const X c) := by
  classical
  obtain ⟨c, hc⟩ := hambient
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hconst :
    (ContinuousMap.const X ((f x₀ : domain g) : N)).Homotopic (ContinuousMap.const X c) :=
    hc.comp (ContinuousMap.Homotopic.refl (ContinuousMap.const X x₀))
  refine
    ⟨f x₀, homotopic_of_ambient_homotopic (I := I) g hg hdim f (ContinuousMap.const X (f x₀)) ?_⟩
  exact hc.trans hconst.symm

private theorem Smale.ImageComplement.circle_nullhomotopies {E' G H' K Y N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H'] [TopologicalSpace K]
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (g : C(Y, N))
    (hg : ContMDiff I' J ∞ g) (hdim : 2 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, N), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Smale.Hemisphere.Sphere 1, domain g), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Nonempty (Smale.Hemisphere.Sphere 1) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro f
  apply nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 1) g hg _ f (hnull _)
  simpa only [finrank_euclideanSpace_fin] using hdim

private theorem Smale.SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_sphere_dimension
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)]
    (d : Smale.SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Smale.Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hold :
    ∀ f : C(Smale.Hemisphere.Sphere 1, d.OldComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
    apply Smale.ImageComplement.circle_nullhomotopies d.attachingSphere hattach _ hnull
    simpa only [finrank_euclideanSpace_fin] using hdim
  intro f
  let e := d.complementHomeomorph
  let forward : C(d.OldComplement, d.NewComplement) := ⟨e, e.continuous⟩
  let backward : C(d.NewComplement, d.OldComplement) := ⟨e.symm, e.symm.continuous⟩
  let f₀ : C(Smale.Hemisphere.Sphere 1, d.OldComplement) := backward.comp f
  obtain ⟨c, hc⟩ := hold f₀
  have heq : forward.comp f₀ = f := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (f x)
  have hout : (forward.comp f₀).Homotopic (ContinuousMap.const _ (e c)) :=
    (ContinuousMap.Homotopic.refl forward).comp hc
  exact ⟨e c, heq ▸ hout⟩

private theorem Smale.SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_finrank_two
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [Fact (Module.finrank ℝ N = 1 + 1)]
    (d : Smale.SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 1) J ∞ d.attachingSphere)
    (hdim : 3 < Module.finrank ℝ G)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Smale.Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  d.beltComplement_circle_nullhomotopies_of_sphere_dimension 1 hattach hdim hnull

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.attachingSphere_eq_attachingCoreMap {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (d :
      Smale.SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (Smale.PuncturedHandle.sphereToBall z.1, z.2)) :
    d.attachingSphere = c.attachingCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (d.oldPiece (u, Smale.PuncturedHandle.ballZero) : M) = _
  rw [hpiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SignedMorseChart.contMDiff_surgeryAttachingSphere {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (d :
      Smale.SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (Smale.PuncturedHandle.sphereToBall z.1, z.2)) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ d.attachingSphere := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  rw [c.attachingSphere_eq_attachingCoreMap ρ hρ hblock d hpiece]
  exact c.contMDiff_attachingCoreMap n hf ρ hρ hblock hreg

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.surgery_beltComplement_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (d :
      Smale.SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (Smale.PuncturedHandle.sphereToBall z.1, z.2))
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 2) (hdim : 4 < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, d.NewComplement),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  let _ : Fact (Module.finrank ℝ c.NegativeCoordinates = 1 + 1) := ⟨hindex⟩
  have hattach := c.contMDiff_surgeryAttachingSphere 1 hf ρ hρ hblock hreg d hpiece
  apply d.beltComplement_circle_nullhomotopies_of_finrank_two hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

private abbrev Smale.PuncturedHandle.OpenUnitBall (N : Type*) [NormedAddCommGroup N] :=
  { x : N // ‖x‖ < 1 }

private abbrev Smale.SurgeryBoundaryPair.NewInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) : Set Y :=
  (Set.range d.newExterior)ᶜ

private theorem
    Smale.SurgeryBoundaryPair.isOpen_newInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) : IsOpen d.NewInterior :=
  d.newExterior_closed.isClosed_range.isOpen_compl

private theorem Smale.SurgeryBoundaryPair.newPiece_mem_exterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair N P R X Y)
    (p : Smale.PuncturedHandle.UnitBall N × Smale.PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ Set.range d.newExterior ↔ ‖(p.1 : N)‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, -, rfl⟩ := (d.new_overlap r p).mp hr
    exact mem_sphere_zero_iff_norm.mp q.1.property
  · intro hp
    let q : Smale.PuncturedHandle.UnitSphere N × Smale.PuncturedHandle.UnitSphere P :=
      (⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2)
    exact ⟨d.boundary q, (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

private theorem Smale.SurgeryBoundaryPair.newPiece_mem_newInterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair N P R X Y)
    (p : Smale.PuncturedHandle.UnitBall N × Smale.PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ d.NewInterior ↔ ‖(p.1 : N)‖ < 1 := by
  change ¬d.newPiece p ∈ Set.range d.newExterior ↔ _
  rw [d.newPiece_mem_exterior_iff]
  constructor
  · intro hp
    rcases lt_or_eq_of_le p.1.property with h | h
    · exact h
    · exact (hp h).elim
  · exact fun h => h.ne

private theorem Smale.SurgeryBoundaryPair.newInterior_subset_range {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair N P R X Y) :
    d.NewInterior ⊆ Set.range d.newPiece := by
  intro y hy
  have hc : y ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by rw [d.new_cover]; trivial
  exact hc.resolve_left hy

private def
    Smale.SurgeryBoundaryPair.newInteriorParameter {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) :
    (Smale.PuncturedHandle.OpenUnitBall N × Smale.PuncturedHandle.UnitSphere P) ≃ₜ
      (d.newPiece ⁻¹' d.NewInterior)
    where
  toFun p := ⟨(⟨p.1, p.1.property.le⟩, p.2), (d.newPiece_mem_newInterior_iff _).mpr p.1.property⟩
  invFun p := (⟨p.val.1, (d.newPiece_mem_newInterior_iff _).mp p.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def
    Smale.SurgeryBoundaryPair.newInteriorHomeomorph {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) :
    (Smale.PuncturedHandle.OpenUnitBall N × Smale.PuncturedHandle.UnitSphere P) ≃ₜ
      d.NewInterior :=
  d.newInteriorParameter.trans
    (d.newPiece_closed.isEmbedding.homeomorphOfSubsetRange d.newInterior_subset_range)

private theorem Smale.SurgeryBoundaryPair.beltSphere_mem_newInterior {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair N P R X Y)
    (v : Smale.PuncturedHandle.UnitSphere P) : d.beltSphere v ∈ d.NewInterior := by
  apply (d.newPiece_mem_newInterior_iff (Smale.PuncturedHandle.ballZero, v)).mpr
  simp [Smale.PuncturedHandle.ballZero]

private theorem Smale.SurgeryBoundaryPair.newInteriorHomeomorph_mem_belt_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : Smale.SurgeryBoundaryPair N P R X Y)
    (p : Smale.PuncturedHandle.OpenUnitBall N × Smale.PuncturedHandle.UnitSphere P) :
    (d.newInteriorHomeomorph p : Y) ∈ Set.range d.beltSphere ↔ (p.1 : N) = 0 :=
  d.newPiece_mem_belt_iff (⟨p.1, p.1.property.le⟩, p.2)

attribute [local instance 100] Classical.propDecidable in
private def Smale.OpenHomotopyExtension.extendFunction {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) : X → Y := fun x =>
  if hx : x ∈ U then g ⟨x, hx⟩ else f x

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.OpenHomotopyExtension.extendFunction_of_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) (x : U) :
    extendFunction U f g x = g x := by simp only [extendFunction, dite_eq_left x.property]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.OpenHomotopyExtension.extendFunction_of_not_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) {x : X} (hx : x ∉ U) :
    extendFunction U f g x = f x := by simp only [extendFunction, dite_eq_right hx]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.OpenHomotopyExtension.continuous_extendFunction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y)
    (hf : Continuous f) (hg : Continuous g) {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U)
    (hfixed : ∀ x : U, (x : X) ∉ K → g x = f x) : Continuous (extendFunction U f g) := by
  have hU : ContinuousOn (extendFunction U f g) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (U : Set X).domRestrict (extendFunction U f g) = g :=
      funext (extendFunction_of_mem U f g)
    rw [heq]
    exact hg
  have haway : ContinuousOn (extendFunction U f g) Kᶜ := by
    apply hf.continuousOn.congr
    intro x hx
    by_cases hxU : x ∈ U
    · rw [extendFunction, dite_eq_left hxU]
      exact hfixed ⟨x, hxU⟩ hx
    · exact extendFunction_of_not_mem U f g hxU
  have hcover : (U : Set X) ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hU.union_of_isOpen haway U.isOpen hK.isOpen_compl

private theorem
    Smale.OpenHomotopyExtension.exists_extended_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : C(X, Y)) (H : C(unitInterval × U, Y))
    {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (hzero : ∀ x : U, H (0, x) = f x)
    (hfixed : ∀ t (x : U), (x : X) ∉ K → H (t, x) = f x) :
    ∃ g : C(X, Y),
      ∃ G : f.Homotopy g, (∀ t (x : U), G (t, x) = H (t, x)) ∧ (∀ t x, x ∉ K → G (t, x) = f x) := by
  let V : TopologicalSpace.Opens (unitInterval × X) :=
    ⟨Prod.snd ⁻¹' U, U.isOpen.preimage continuous_snd⟩
  let L : V → Y := fun z => H (z.val.1, ⟨z.val.2, z.property⟩)
  have hL : Continuous L :=
    H.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  let T : C(unitInterval × X, Y) :=
    ⟨extendFunction V (fun z => f z.2) L,
      continuous_extendFunction V _ L (f.continuous.comp continuous_snd) hL
        (hK.preimage continuous_snd) (fun _ hz => hKU hz)
        (fun z hz => hfixed z.val.1 ⟨z.val.2, z.property⟩ hz)⟩
  have hlocal (t) (x : U) : T (t, x) = H (t, x) :=
    extendFunction_of_mem V (fun z : unitInterval × X => f z.2) L ⟨(t, x), x.property⟩
  have houtside (t) (x : X) (hx : x ∉ K) : T (t, x) = f x := by
    by_cases hxU : x ∈ U
    · exact (hlocal t ⟨x, hxU⟩).trans (hfixed t ⟨x, hxU⟩ hx)
    · exact extendFunction_of_not_mem V (fun z : unitInterval × X => f z.2) L (x := (t, x)) hxU
  let g : C(X, Y) := T.comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
  refine
    ⟨g, { toContinuousMap := T, map_zero_left := ?_, map_one_left := fun _ => rfl }, hlocal,
      houtside⟩
  intro x
  by_cases hx : x ∈ U
  · exact (hlocal 0 ⟨x, hx⟩).trans (hzero ⟨x, hx⟩)
  · exact houtside 0 x (fun h => hx (hKU h))

private theorem NoExotic.dimH_image_le_of_contDiffOn_isOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) : dimH (f '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  obtain ⟨C, U, hU, hL⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩

private theorem NoExotic.dimH_image_chart_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → F} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (x : M) :
    dimH (f '' ((modelChartPartialDiffeomorph (I := I) x).source ∩ s)) ≤ Module.finrank ℝ E := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hs
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp (c.contMDiffOn_invFun.mono Set.inter_subset_left) Set.inter_subset_right).contDiffOn
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source' hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        have hc : c.symm (c y) = y := c.left_inv' hyc
        rwa [hc]
      · exact congrArg f (c.left_inv' hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target' hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact
    (dimH_image_le_of_contDiffOn_isOpen hV (hfc.of_le (by simp))).trans
      ((dimH_mono (Set.subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

private theorem
    NoExotic.dimH_image_manifold_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M] {f : M → F} {s : Set M}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) : dimH (f '' s) ≤ Module.finrank ℝ E := by
  let U : M → Set M := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).source
  have hU : ∀ x, IsOpen (U x) := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).open_source
  have hcover : (Set.univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x ↦ iSup_le (fun _ ↦ dimH_image_chart_le hs hf x))

private theorem
    NoExotic.dense_compl_manifold_image {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M] [FiniteDimensional ℝ F] {f : M → F}
    {s : Set M} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

private theorem NoExotic.not_surjective_contMDiff_of_dim_lt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M]
    [FiniteDimensional ℝ F] {G N : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [Nonempty N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (hd : Module.finrank ℝ E < Module.finrank ℝ F) :
    ¬Function.Surjective f := by
  intro hsurj
  let y : N := Classical.choice inferInstance
  let d := modelChartPartialDiffeomorph (I := J) y
  let s : Set M := f ⁻¹' d.source
  have hs : IsOpen s := d.open_source.preimage hf.continuous
  have hdf : ContMDiffOn I 𝓘(ℝ, F) ∞ (d ∘ f) s :=
    d.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ h ↦ h)
  have himage : (d ∘ f) '' s = d.target := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact d.map_source' hx
    · intro hz
      obtain ⟨x, hx⟩ := hsurj (d.symm z)
      refine ⟨x, ?_, ?_⟩
      · change f x ∈ d.source
        rw [hx]
        exact d.map_target' hz
      · change d (f x) = z
        rw [hx]
        exact d.right_inv' hz
  have hne : (interior d.target).Nonempty := by
    rw [d.open_target.interior_eq]
    exact ⟨d y, d.map_source' (mem_extChartAt_source y)⟩
  have hdim := dimH_image_manifold_le hs hdf
  rw [himage, Real.dimH_of_nonempty_interior hne] at hdim
  exact
    (not_le_of_gt (Nat.cast_lt.mpr hd : (Module.finrank ℝ E : ℝ≥0∞) < Module.finrank ℝ F)) hdim

private theorem NoExotic.exists_smooth_nonzero_approx {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F), ContMDiff I 𝓘(ℝ, F) ∞ g ∧ (∀ x, g x ≠ 0) ∧ ∀ x, Dist.dist (g x) (f x) < ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨h, hh, -⟩ :=
    f.continuous.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ ε / 2) continuous_const
      (fun _ ↦ hhalf)
  have hdense : Dense (Set.range h)ᶜ := by
    simpa only [Set.image_univ] using
      dense_compl_manifold_image isOpen_univ h.contMDiff.contMDiffOn hd
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp (hdense (0 : F)) (ε / 2) hhalf
  have haNorm : ‖a‖ < ε / 2 := by simpa only [dist_zero_left, dist_zero_right] using hdist
  let g : C(M, F) := ⟨fun x ↦ h x - a, h.contMDiff.continuous.sub continuous_const⟩
  refine ⟨g, h.contMDiff.sub contMDiff_const, ?_, ?_⟩
  · intro x hx
    have he : h x = a := sub_eq_zero.mp hx
    exact ha ⟨x, he⟩
  · intro x
    have hnorm : ‖h x - a - f x‖ ≤ ‖h x - f x‖ + ‖a‖ := by
      have he : h x - a - f x = (h x - f x) - a := by abel
      rw [he]
      exact norm_sub_le _ _
    change Dist.dist (h x - a) (f x) < ε
    rw [dist_eq_norm]
    have hhx : ‖h x - f x‖ < ε / 2 := by simpa only [dist_eq_norm] using hh x
    linarith

private noncomputable def NoExotic.RealIntervalProgress.progress (l u t : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((t - l) / (u - l))

private theorem
    NoExotic.RealIntervalProgress.continuous_progress (l u : ℝ) : Continuous (progress l u) :=
  continuous_subtype_val.comp
    (continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _))

private theorem
    NoExotic.RealIntervalProgress.progress_before {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) :
    progress l u t = 0 := by
  have h :=
    Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) zero_le_one
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu))
  exact congrArg Subtype.val h

private theorem
    NoExotic.RealIntervalProgress.progress_after {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) :
    progress l u t = 1 := by
  have hr : 1 ≤ (t - l) / (u - l) := by
    apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
    simpa only [one_mul] using sub_le_sub_right ht l
  exact congrArg Subtype.val (Set.projIcc_of_right_le zero_le_one hr)

private noncomputable def NoExotic.ZeroAvoidanceCutoff.weight {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) : C(X, ℝ) :=
  ⟨fun x ↦ 1 - NoExotic.RealIntervalProgress.progress ε (2 * ε) ‖f x‖,
    continuous_const.sub
      ((NoExotic.RealIntervalProgress.continuous_progress ε (2 * ε)).comp f.continuous.norm)⟩

private theorem NoExotic.ZeroAvoidanceCutoff.weight_bounds {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (x : X) : 0 ≤ weight f ε x ∧ weight f ε x ≤ 1 := by
  have hp : NoExotic.RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∈ Set.Icc (0 : ℝ) 1 :=
    (Set.projIcc (0 : ℝ) 1 zero_le_one ((‖f x‖ - ε) / (2 * ε - ε))).property
  change
    0 ≤ 1 - NoExotic.RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∧
      1 - NoExotic.RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ≤ 1
  constructor <;> linarith [hp.1, hp.2]

private theorem NoExotic.ZeroAvoidanceCutoff.weight_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : ‖f x‖ ≤ ε) :
    weight f ε x = 1 := by
  simp only [weight, ContinuousMap.coe_mk,
    NoExotic.RealIntervalProgress.progress_before (by linarith : ε ≤ 2 * ε) hx, sub_zero]

private theorem NoExotic.ZeroAvoidanceCutoff.weight_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : 2 * ε ≤ ‖f x‖) :
    weight f ε x = 0 := by
  simp only [weight, ContinuousMap.coe_mk,
    NoExotic.RealIntervalProgress.progress_after (by linarith : ε < 2 * ε) hx, sub_self]

private noncomputable def NoExotic.ZeroAvoidanceCutoff.blend {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) : C(X, F) :=
  ⟨fun x ↦ f x + weight f ε x • (g x - f x),
    f.continuous.add ((weight f ε).continuous.smul (g.continuous.sub f.continuous))⟩

private theorem NoExotic.ZeroAvoidanceCutoff.blend_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : ‖f x‖ ≤ ε) : blend f g ε x = g x := by
  change f x + weight f ε x • (g x - f x) = g x
  rw [weight_small f ε hε hx, one_smul]
  abel

private theorem NoExotic.ZeroAvoidanceCutoff.blend_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : 2 * ε ≤ ‖f x‖) : blend f g ε x = f x := by
  change f x + weight f ε x • (g x - f x) = f x
  rw [weight_large f ε hε hx, zero_smul, add_zero]

private theorem NoExotic.ZeroAvoidanceCutoff.dist_blend_le {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (x : X) :
    Dist.dist (blend f g ε x) (f x) ≤ Dist.dist (g x) (f x) := by
  simp only [dist_eq_norm]
  change ‖f x + weight f ε x • (g x - f x) - f x‖ ≤ ‖g x - f x‖
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_bounds f ε x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_bounds f ε x).2

private theorem NoExotic.ZeroAvoidanceCutoff.blend_ne_zero {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ x, g x ≠ 0) (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (x : X) : blend f g ε x ≠ 0 := by
  by_cases hx : ‖f x‖ ≤ ε
  · rw [blend_small f g ε hε hx]
    exact hg x
  · intro hz
    have hh := (dist_blend_le f g ε x).trans_lt (hclose x)
    rw [hz, dist_zero_left] at hh
    exact hx hh.le

private noncomputable def NoExotic.ZeroAvoidanceCutoff.homotopy {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyRel f (blend f g ε) {x | 2 * ε ≤ ‖f x‖}
    where
  toFun p := f p.2 + (p.1 : ℝ) • (blend f g ε p.2 - f p.2)
  continuous_toFun :=
    (f.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((blend f g ε).continuous.comp continuous_snd).sub (f.continuous.comp continuous_snd)))
  map_zero_left x := by simp
  map_one_left
    x := by
    change f x + (1 : ℝ) • (blend f g ε x - f x) = blend f g ε x
    rw [one_smul]
    abel
  prop' t x
    hx := by
    change f x + (t : ℝ) • (blend f g ε x - f x) = f x
    rw [blend_large f g ε hε hx, sub_self, smul_zero, add_zero]

private theorem NoExotic.ZeroAvoidanceCutoff.homotopy_dist_lt {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (t : (unitInterval)) (x : X) :
    Dist.dist (homotopy f g ε hε (t, x)) (f x) < ε := by
  rw [dist_eq_norm]
  change ‖f x + (t : ℝ) • (blend f g ε x - f x) - f x‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖blend f g ε x - f x‖ ≤ ‖blend f g ε x - f x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ ≤ Dist.dist (g x) (f x) := by simpa only [dist_eq_norm] using dist_blend_le f g ε x
    _ < ε := hclose x

private theorem NoExotic.exists_nonzero_homotopy_small {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F),
      (∀ x, g x ≠ 0) ∧
        ∃ G : ContinuousMap.HomotopyRel f g {x | 2 * ε ≤ ‖f x‖},
          ∀ t x, Dist.dist (G (t, x)) (f x) < ε := by
  obtain ⟨h, -, hnonzero, hclose⟩ := exists_smooth_nonzero_approx (I := I) f ε hε hd
  refine
    ⟨ZeroAvoidanceCutoff.blend f h ε, ZeroAvoidanceCutoff.blend_ne_zero f h ε hε hnonzero hclose,
      ZeroAvoidanceCutoff.homotopy f h ε hε, ?_⟩
  exact ZeroAvoidanceCutoff.homotopy_dist_lt f h ε hε hclose

private theorem Smale.SurgeryBoundaryPair.exists_belt_avoiding_circle {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (g : C(Smale.Hemisphere.Sphere 1, Y)) :
    ∃ g' : C(Smale.Hemisphere.Sphere 1, Y),
      (∀ x, g' x ∉ Set.range d.beltSphere) ∧ g.Homotopic g' := by
  let U : TopologicalSpace.Opens (Smale.Hemisphere.Sphere 1) :=
    ⟨g ⁻¹' d.NewInterior, d.isOpen_newInterior.preimage g.continuous⟩
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e := d.newInteriorHomeomorph
  let coord : C(U, Smale.PuncturedHandle.OpenUnitBall N × Smale.PuncturedHandle.UnitSphere P) :=
    ⟨fun x => e.symm ⟨g x, x.property⟩,
      e.symm.continuous.comp ((g.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  let normal : C(U, N) := ⟨fun x => (coord x).1, continuous_subtype_val.comp coord.continuous.fst⟩
  have hparam (x : U) : d.newPiece (⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2) = g x :=
    congrArg (fun y : d.NewInterior => (y : Y)) (e.apply_symm_apply ⟨g x, x.property⟩)
  obtain ⟨q, hq, G, hclose⟩ :=
    NoExotic.exists_nonzero_homotopy_small (I := 𝓡 1) normal (1 / 8) (by norm_num)
      (by simpa only [finrank_euclideanSpace_fin] using hdim)
  have hnorm (t) (x : U) : ‖G (t, x)‖ < 1 := by
    by_cases hx : 1 / 4 ≤ ‖normal x‖
    · rw [G.eq_fst t
          (show x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} from
            by
            change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
            linarith)]
      exact (coord x).1.property
    · have hdist : ‖G (t, x) - normal x‖ < 1 / 8 := by simpa only [dist_eq_norm] using hclose t x
      have hbound := norm_add_le (G (t, x) - normal x) (normal x)
      rw [sub_add_cancel] at hbound
      linarith
  let H : C(unitInterval × U, Y) :=
    ⟨fun z => (e (⟨G z, hnorm z.1 z.2⟩, (coord z.2).2) : Y),
      continuous_subtype_val.comp
        (e.continuous.comp
          ((G.continuous.subtype_mk _).prodMk (coord.continuous.snd.comp continuous_snd)))⟩
  have hreturn (t) (x : U) (hx : G (t, x) = normal x) : H (t, x) = g x := by
    have hu : (⟨G (t, x), hnorm t x⟩ : Smale.PuncturedHandle.OpenUnitBall N) = (coord x).1 :=
      Subtype.ext hx
    change (e (⟨G (t, x), _⟩, (coord x).2) : Y) = _
    rw [hu]
    exact hparam x
  have hzero (x : U) : H (0, x) = g x := hreturn 0 x (G.apply_zero x)
  let K₀ : Set Y :=
    d.newPiece ''
      {p : Smale.PuncturedHandle.UnitBall N × Smale.PuncturedHandle.UnitSphere P |
        ‖(p.1 : N)‖ ≤ 1 / 2}
  have hK₀ : IsClosed K₀ :=
    d.newPiece_closed.isClosedMap _
      (isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const)
  have hK₀U : K₀ ⊆ d.NewInterior := by
    rintro _ ⟨p, hp, rfl⟩
    apply (d.newPiece_mem_newInterior_iff p).mpr
    exact hp.trans_lt (by norm_num)
  let K : Set (Smale.Hemisphere.Sphere 1) := g ⁻¹' K₀
  have hK : IsClosed K := hK₀.preimage g.continuous
  have hKU : K ⊆ U := fun _ hx => hK₀U hx
  have hfixed (t) (x : U) (hx : (x : Smale.Hemisphere.Sphere 1) ∉ K) : H (t, x) = g x := by
    have hlarge : 1 / 2 < ‖normal x‖ := by
      by_contra! hh
      apply hx
      exact ⟨(⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2), hh, hparam x⟩
    have hsafe : x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} := by
      change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
      linarith
    exact hreturn t x (G.eq_fst t hsafe)
  obtain ⟨g', G', hlocal, houtside⟩ :=
    Smale.OpenHomotopyExtension.exists_extended_homotopy U g H hK hKU hzero hfixed
  refine ⟨g', ?_, ⟨G'⟩⟩
  intro x hxB
  by_cases hx : x ∈ U
  · have heq : g' x = H (1, ⟨x, hx⟩) := (G'.apply_one x).symm.trans (hlocal 1 ⟨x, hx⟩)
    rw [heq] at hxB
    have hzero' : G (1, ⟨x, hx⟩) = 0 := (d.newInteriorHomeomorph_mem_belt_iff _).mp hxB
    rw [G.apply_one] at hzero'
    exact hq ⟨x, hx⟩ hzero'
  · have heq : g' x = g x := (G'.apply_one x).symm.trans (houtside 1 x (fun h => hx (hKU h)))
    rw [heq] at hxB
    obtain ⟨v, hv⟩ := hxB
    apply hx
    change g x ∈ d.NewInterior
    rw [← hv]
    exact d.beltSphere_mem_newInterior v

private theorem
    Smale.SurgeryBoundaryPair.circle_nullhomotopies_of_beltComplement {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : Smale.SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, d.NewComplement),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  intro g
  obtain ⟨g', havoid, hgg'⟩ := d.exists_belt_avoiding_circle hdim g
  let g₀ : C(Smale.Hemisphere.Sphere 1, d.NewComplement) :=
    ⟨fun x => ⟨g' x, havoid x⟩, g'.continuous.subtype_mk _⟩
  let inc : C(d.NewComplement, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨q, hq⟩ := hnull g₀
  have hh : (inc.comp g₀).Homotopic (ContinuousMap.const _ (q : Y)) :=
    (ContinuousMap.Homotopic.refl inc).comp hq
  exact ⟨q, hgg'.trans hh⟩

private theorem Smale.SurgeryBoundaryPair.newBoundary_circle_nullhomotopies {N F R X Y G H : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]
    (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] (hn : 0 < n)
    (d : Smale.SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Smale.Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Smale.Hemisphere.Sphere 1, Y), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hnormal : 1 < Module.finrank ℝ N := by
    rw [show Module.finrank ℝ N = n + 1 from Fact.out]
    omega
  exact
    d.circle_nullhomotopies_of_beltComplement hnormal
      (d.beltComplement_circle_nullhomotopies_of_sphere_dimension n hattach hdim hnull)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.surgery_newBoundary_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (d :
      Smale.SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (Smale.PuncturedHandle.sphereToBall z.1, z.2))
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  have hattach := c.contMDiff_surgeryAttachingSphere n hf ρ hρ hblock hreg d hpiece
  apply d.newBoundary_circle_nullhomotopies n hn hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

attribute [local instance 100] Classical.propDecidable in
private structure Smale.ManifoldMorse.MorseSurgeryData (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ)
    (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : SignedMorseChart (E := E) f p
  block :
    Metric.closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
        Metric.closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆
      chart.splitChart.target
  attachmentHomeomorph :
    ↥({x : M | f x ≤ f p - radius ^ 2} ∪
          Set.range (chart.attachingHandleMap radius radius_pos block)) ≃ₜ
      { x : M // f x ≤ f p + radius ^ 2 }
  attachment_frontier :
    ∀ x,
      f (attachmentHomeomorph x) = f p + radius ^ 2 ↔
        x.val ∈
          frontier
            ({y : M | f y ≤ f p - radius ^ 2} ∪
              Set.range (chart.attachingHandleMap radius radius_pos block))
  attachment_fixed : ∀ x, f x.val = f p + radius ^ 2 → (attachmentHomeomorph x).val = x.val
  attachment_model_orbits :
    chart.FollowsModelBoundaryOrbits radius radius_pos block attachmentHomeomorph
  surgery :
    Smale.SurgeryBoundaryPair chart.NegativeCoordinates chart.PositiveCoordinates
      { x : M //
        f x = f p - radius ^ 2 ∧
          x ∈
            frontier
              ({y | f y ≤ f p - radius ^ 2} ∪
                Set.range (chart.normHandleMap radius radius_pos block)) }
      { x : M // f x = f p - radius ^ 2 } { x : M // f x = f p + radius ^ 2 }
  oldExterior_eq : ∀ r, (surgery.oldExterior r : M) = r.val
  newExterior_eq :
    ∀ r, (surgery.newExterior r : M) = (attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩).val
  oldPiece_eq :
    ∀ z,
      (surgery.oldPiece z : M) =
        chart.normHandleMap radius radius_pos block (Smale.PuncturedHandle.sphereToBall z.1, z.2)
  newPiece_eq :
    ∀ z,
      (surgery.newPiece z : M) =
        (attachmentHomeomorph
            ⟨chart.normHandleMap radius radius_pos block
                (z.1, Smale.PuncturedHandle.sphereToBall z.2),
              Or.inr
                ⟨chart.handleBallCoordinates (z.1, Smale.PuncturedHandle.sphereToBall z.2),
                  rfl⟩⟩).val
  belt_eq : surgery.beltSphere = chart.beltCoreMap radius radius_pos block
  lower_regular : ∀ x, f x = f p - radius ^ 2 → x ∉ criticalPoints E f
  upper_regular : ∀ x, f x = f p + radius ^ 2 → x ∉ criticalPoints E f

private abbrev Smale.ManifoldMorse.MorseSurgeryData.LowerLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p - d.radius ^ 2 }

private abbrev Smale.ManifoldMorse.MorseSurgeryData.UpperLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p + d.radius ^ 2 }

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.attaching_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    d.surgery.attachingSphere = d.chart.attachingCoreMap d.radius d.radius_pos d.block :=
  d.chart.attachingSphere_eq_attachingCoreMap d.radius d.radius_pos d.block d.surgery
    d.oldPiece_eq

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.attaching_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.attachingSphere := by
  rw [d.attaching_eq]
  exact d.chart.attachingCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.belt_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.beltSphere := by
  rw [d.belt_eq]
  exact d.chart.beltCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.attaching_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] :
    letI := Smale.RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ d.surgery.attachingSphere := by
  let _ := Smale.RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact d.chart.contMDiff_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.belt_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ d.surgery.beltSphere := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.contMDiff_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.attaching_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)]
    (u : Smale.PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.lower_regular
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.attachingSphere u) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact
    d.chart.injective_mfderiv_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular
      u

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.belt_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.injective_mfderiv_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular v

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.upper_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = f p - d.radius ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = f p + d.radius ^ 2 }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
  d.chart.surgery_newBoundary_circle_nullhomotopies n hn hf d.radius d.radius_pos d.block
    d.lower_regular d.surgery d.oldPiece_eq hdim hnull

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.exists_morseSurgeryData_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p,
      d.radius < ε ∧
        ∀ x ∈ criticalPoints E f,
          f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p := by
  obtain ⟨ρ, hρ, hρε, c, hblock, e, he, hfixed, hlevel, hlower, hupper, horbits, hband⟩ :=
    exists_morse_boundary_attachment_with_model_orbits_lt hf hm hp hunique hε
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := he
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e he hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, hband⟩

private theorem Smale.ManifoldMorse.exists_separated_value_radii {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (hinj : Set.InjOn f K) :
    ∃ r : K → ℝ, (∀ p, 0 < r p) ∧ ∀ p q : K, f p < f q → f p + (r p) ^ 2 < f q - (r q) ^ 2 := by
  have hex :
    ∀ p : K,
      ∃ ρ > (0 : ℝ), ρ < 1 ∧ ∀ x ∈ K, f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p.val := by
    intro p
    exact exists_isolating_radius hK p.val (fun x hx hfx => hinj hx p.property hfx) zero_lt_one
  choose ρ hρ hρ₁ hisolated using hex
  refine ⟨fun p => ρ p / 2, fun p => half_pos (hρ p), ?_⟩
  intro p q hpq
  have hupper : f p + (ρ p) ^ 2 < f q := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated p q.val q.property ⟨by nlinarith [sq_nonneg (ρ p)], h⟩
    exact (ne_of_lt hpq) (congrArg f heq).symm
  have hlower : f p < f q - (ρ q) ^ 2 := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated q p.val p.property ⟨h, by nlinarith [sq_nonneg (ρ q)]⟩
    exact (ne_of_lt hpq) (congrArg f heq)
  nlinarith

private theorem Smale.exists_partialDiffeomorph_into_manifold {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : D → M} {U : Set D}
    {x : D} (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set D := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContDiffOn ℝ ∞ (c ∘ f) V :=
    (c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  have hcinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (fderiv ℝ (c ∘ f) x).IsInvertible := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp x (c.mdifferentiableAt (by simp) hc)
        ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hcinv.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ := NoExotic.exists_partialDiffeomorph_of_contDiffOn hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    rw [hdf]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  change f y = c.symm (d y)
  rw [hdf]
  exact (c.left_inv' (hdV hy.1).2).symm

private theorem Smale.isLocalDiffeomorphAt_of_contMDiffOn {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : D → M} {U : Set D}
    {x : D} (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_into_manifold hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

private theorem
    Smale.exists_partialDiffeomorph_between_manifolds {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H X : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [I.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] {f : X → M} {U : Set X} {x : X} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := I) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source' hxc
  have hleft (y : X) (hy : y ∈ c.source) : c.symm (c y) = y := c.left_inv' hy
  let V : Set D := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcxV : c x ∈ V :=
    ⟨hcx, by
      change c.symm (c x) ∈ U
      rwa [hleft x hxc]⟩
  have hgf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (f ∘ c.symm) V :=
    hf.comp (c.contMDiffOn_invFun.mono Set.inter_subset_left) (fun _ hy => hy.2)
  have hcDiff : c.toOpenPartialHomeomorph.MDifferentiable I 𝓘(ℝ, D) :=
    ⟨c.mdifferentiableOn (by simp), c.symm.mdifferentiableOn (by simp)⟩
  have hci : (mfderiv 𝓘(ℝ, D) I c.symm (c x)).IsInvertible := ⟨hcDiff.symm.mfderiv hcx, rfl⟩
  have hderiv : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (f ∘ c.symm) (c x)).IsInvertible := by
    have hfx := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hfc : MDifferentiableAt I 𝓘(ℝ, E) f (c.symm (c x)) := by
      simpa only [hleft x hxc] using hfx
    rw [mfderiv_comp (c x) hfc (c.symm.mdifferentiableAt (by simp) hcx), hleft x hxc]
    exact hinv.comp hci
  obtain ⟨d, hd, hdV, heq⟩ := exists_partialDiffeomorph_into_manifold hV hcxV hgf hderiv
  refine ⟨c.trans d, ⟨hxc, hd⟩, ?_, ?_⟩
  · intro y hy
    have hh := (hdV hy.2).2
    change c.symm (c y) ∈ U at hh
    rwa [hleft y hy.1] at hh
  · intro y hy
    have hh := heq hy.2
    change f (c.symm (c y)) = d (c y) at hh
    change f y = d (c y)
    simpa only [hleft y hy.1] using hh

private theorem Smale.isLocalDiffeomorphAt_between_manifolds {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H X : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [I.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] {f : X → M} {U : Set X} {x : X} (hU : IsOpen U)
    (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, E) ∞ f U)
    (hinv : (mfderiv I 𝓘(ℝ, E) f x).IsInvertible) : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_between_manifolds hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

private theorem
    Smale.exists_partialDiffeomorph_boundaryless {D E H H' X Y : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ E H'} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] {f : X → Y} {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞, x ∈ Φ.source ∧ Φ.source ⊆ U ∧ Set.EqOn f Φ Φ.source := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hc : f x ∈ c.source := mem_extChartAt_source (f x)
  let V : Set X := U ∩ f ⁻¹' c.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have hxV : x ∈ V := ⟨hx, hc⟩
  have hcf : ContMDiffOn I 𝓘(ℝ, E) ∞ (c ∘ f) V :=
    c.contMDiffOn_toFun.comp (hf.mono Set.inter_subset_left) (fun _ hy => hy.2)
  have hci : (mfderiv J 𝓘(ℝ, E) c (f x)).IsInvertible :=
    isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x))
  have hderiv : (mfderiv I 𝓘(ℝ, E) (c ∘ f) x).IsInvertible := by
    rw [mfderiv_comp x (c.mdifferentiableAt (by simp) hc)
        ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact hci.comp hinv
  obtain ⟨d, hd, hdV, hdf⟩ := exists_partialDiffeomorph_between_manifolds hV hxV hcf hderiv
  have hdx : d x ∈ c.target := by
    have heq : d x = c (f x) := (hdf hd).symm
    rw [heq]
    exact c.map_source' hc
  refine ⟨d.trans c.symm, ⟨hd, hdx⟩, fun y hy => (hdV hy.1).1, ?_⟩
  intro y hy
  have heq : d y = c (f y) := (hdf hy.1).symm
  change f y = c.symm (d y)
  rw [heq]
  exact (c.left_inv' (hdV hy.1).2).symm

private theorem
    Smale.isLocalDiffeomorphAt_boundaryless {D E H H' X Y : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ D H}
    {J : ModelWithCorners ℝ E H'} [I.Boundaryless] [J.Boundaryless] [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] {f : X → Y} {U : Set X} {x : X} (hU : IsOpen U) (hx : x ∈ U)
    (hf : ContMDiffOn I J ∞ f U) (hinv : (mfderiv I J f x).IsInvertible) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨Φ, hxΦ, -, heq⟩ := exists_partialDiffeomorph_boundaryless hU hx hf hinv
  exact ⟨Φ, hxΦ, heq⟩

private def Smale.partialDiffeomorphOfInjectiveLocal {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] {f : X → Y}
    {U : Set X} (hU : IsOpen U) (hinj : Set.InjOn f U) (hloc : IsLocalDiffeomorphOn I J ∞ f U) :
    PartialDiffeomorph I J X Y ∞ := by
  let p := hinj.toPartialEquiv f U
  have htarget : IsOpen p.target := by
    change IsOpen (f '' U)
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hx]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  have hinverse : ContMDiffOn J I ∞ p.symm p.target := by
    intro y hy
    have hx : p.symm y ∈ U := p.map_target hy
    obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
    have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
    have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
    have hφyx : φ.symm y = p.symm y := by
      calc
        φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
        _ = p.symm y := φ.left_inv' hφx
    have hg : ContMDiffAt J I ∞ φ.symm y :=
      φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
    have hNU : U ∈ 𝓝 (φ.symm y) := by
      rw [hφyx]
      exact hU.mem_nhds hx
    have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
      filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
      have hfz : f (φ.symm z) = z := (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
      exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
    exact (hfg.contMDiffAt_iff.mpr hg).contMDiffWithinAt
  exact
    { p with
      open_source := hU
      open_target := htarget
      contMDiffOn_toFun := hloc.contMDiffOn
      contMDiffOn_invFun := hinverse }

private theorem
    Smale.exists_partialDiffeomorph_near_compact {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
    {f : X → Y} {K U : Set X} (hK : IsCompact K) (hinj : Set.InjOn f K)
    (hloc : ∀ x ∈ K, IsLocalDiffeomorphAt I J ∞ f x) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Φ : PartialDiffeomorph I J X Y ∞, K ⊆ Φ.source ∧ Φ.source ⊆ U ∧ (Φ : X → Y) = f := by
  let R : Set X := {x | IsLocalDiffeomorphAt I J ∞ f x}
  have hR : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨φ, hx, heq⟩
    exact Filter.mem_of_superset (φ.open_source.mem_nhds hx) (fun y hy => ⟨φ, hy, heq⟩)
  have hlocalinj : ∀ x ∈ K, ∃ V ∈ 𝓝 x, Set.InjOn f V := by
    intro x hx
    obtain ⟨φ, hφ, heq⟩ := hloc x hx
    exact ⟨φ.source, φ.open_source.mem_nhds hφ, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩
  obtain ⟨V, hV, hKV, hVi⟩ :=
    hinj.exists_isOpen_superset hK (fun x hx => (hloc x hx).contMDiffAt.continuousAt) hlocalinj
  let W := (V ∩ R) ∩ U
  have hW : IsOpen W := (hV.inter hR).inter hU
  have hKW : K ⊆ W := fun x hx => ⟨⟨hKV hx, hloc x hx⟩, hKU hx⟩
  have hWi : Set.InjOn f W := hVi.mono (Set.inter_subset_left.trans Set.inter_subset_left)
  have hWloc : IsLocalDiffeomorphOn I J ∞ f W := fun x => x.property.1.2
  exact ⟨partialDiffeomorphOfInjectiveLocal hW hWi hWloc, hKW, Set.inter_subset_right, rfl⟩

private def Smale.CollarHeight.heightChange {X : Type*} (h : X × ℝ → ℝ) (z : X × ℝ) : X × ℝ :=
  (z.1, h z)

private theorem Smale.CollarHeight.heightChange_zero {X : Type*} {h : X × ℝ → ℝ}
    (hzero : ∀ x, h (x, 0) = 0) (x : X) : heightChange h (x, 0) = (x, 0) :=
  Prod.ext rfl (hzero x)

private theorem Smale.CollarHeight.contMDiffOn_heightChange {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)}
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (heightChange h) U :=
  contMDiff_fst.contMDiffOn.prodMk hh

private theorem Smale.CollarHeight.mfderiv_height_zero {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0) (x : X)
    (hx : (x, 0) ∈ U) (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h (x, 0) = ContinuousLinearMap.snd ℝ D ℝ := by
  have hbase : (fun y : X => h (y, 0)) = fun _ => 0 := funext hzero
  have ht : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => h (x, t)) 0 = ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv, htime.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, mul_one]
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    hbase, mfderiv_const, ht]
  change (0 : ℝ) + v.2 = v.2
  exact zero_add _

private theorem Smale.CollarHeight.mfderiv_heightChange_zero {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0) (x : X)
    (hx : (x, 0) ∈ U) (htime : HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (heightChange h) (x, 0) =
      ContinuousLinearMap.id ℝ (D × ℝ) := by
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) (x, 0) = _
  rw [mfderiv_prodMk mdifferentiableAt_fst
      ((hh.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)),
    mfderiv_fst, mfderiv_height_zero hU hh hzero x hx htime]
  rfl

private theorem Smale.CollarHeight.exists_heightChangeChart {D H X : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [TopologicalSpace H] {I : ModelWithCorners ℝ D H} [TopologicalSpace X]
    [ChartedSpace H X] [CompleteSpace D] [I.Boundaryless] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [Nonempty X] {h : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U) (hzero : ∀ x, h (x, 0) = 0)
    (hsource : ∀ x, (x, 0) ∈ U) (htime : ∀ x, HasDerivAt (fun t : ℝ => h (x, t)) 1 0) :
    ∃ χ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (X × ℝ) (X × ℝ) ∞,
      (Set.univ : Set X) ×ˢ {(0 : ℝ)} ⊆ χ.source ∧
        χ.source ⊆ U ∧ (χ : X × ℝ → X × ℝ) = heightChange h := by
  let K : Set (X × ℝ) := Set.univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : Set.InjOn (heightChange h) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [heightChange_zero hzero x, heightChange_zero hzero y] at hxy
    exact hxy
  have hloc :
    ∀ z ∈ K, IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (heightChange h) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    apply Smale.isLocalDiffeomorphAt_boundaryless hU (hsource x) (contMDiffOn_heightChange hh)
    rw [mfderiv_heightChange_zero hU hh hzero x (hsource x) (htime x)]
    exact ⟨ContinuousLinearEquiv.refl ℝ (D × ℝ), rfl⟩
  exact
    Smale.exists_partialDiffeomorph_near_compact hK hinj hloc hU
      (fun ⟨x, t⟩ hx => by
        have ht : t = 0 := hx.2
        simpa only [ht] using hsource x)

private theorem Smale.RegularLevel.injective_mfderiv_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    Function.Injective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let Φ := heightChart hf hreg x
  have hΦ :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg x))
  have hprojection : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Model E) ∞ (fun y : M => (Φ y).2) (x : M) :=
    contDiff_snd.contMDiff.contMDiffAt.comp (x : M) hΦ
  have hi :=
    (mdifferentiable_chart (I := 𝓘(ℝ, Model E)) x).mfderiv_injective
      (mem_chart_source (Model E) x)
  change
    Function.Injective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ((fun y : M => (Φ y).2) ∘ Subtype.val) x) at hi
  rw [mfderiv_comp x (hprojection.mdifferentiableAt (by simp))
      ((Smale.RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))] at hi
  exact fun u v huv =>
    hi (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model E) (fun y : M => (Φ y).2) (x : M)) huv)

private theorem
    Smale.RegularLevel.height_derivative_comp_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    (mvfderiv 𝓘(ℝ, E) f (x : M)).comp
        (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x) =
      0 := by
  let _ := chartedSpace hf hreg
  have heq : f ∘ (Subtype.val : { x : M // f x = b } → M) = fun _ => b :=
    funext (fun y => y.property)
  have hc :=
    mfderiv_comp x (hf.mdifferentiableAt (by simp))
      ((Smale.RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
  rw [heq, mfderiv_const] at hc
  exact hc.symm

private theorem Smale.RegularLevel.range_mfderiv_inclusion {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x).range =
      (mvfderiv 𝓘(ℝ, E) f (x : M)).ker := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  change A.range = L.ker
  have hsub : A.range ≤ L.ker := by
    rintro _ ⟨v, rfl⟩
    change L (A v) = 0
    exact congrArg (fun T => T v) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Function.Injective A := injective_mfderiv_inclusion hf hreg x
  have hL : L ≠ 0 := hreg x x.property
  have hdim := finrank_kernel_add_one hL
  have hAr : Module.finrank ℝ A.range = Module.finrank ℝ E - 1 := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hAr]
  omega

private def
    Smale.RegularLevel.transverseTangentMap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (x : { x : M // f x = b })
    (v : E) : Model E × ℝ →L[ℝ] E :=
  letI := chartedSpace hf hreg
  (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x).coprod
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

private theorem
    Smale.RegularLevel.bijective_transverseTangentMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (x : { x : M // f x = b })
    (v : E) (hv : mvfderiv 𝓘(ℝ, E) f (x : M) v = 1) :
    Function.Bijective (transverseTangentMap hf hreg x v) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hLA (u : Model E) : L (A u) = 0 :=
    congrArg (fun T => T u) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Function.Injective A := injective_mfderiv_inclusion hf hreg x
  change L v = 1 at hv
  constructor
  · intro z w hzw
    change A z.1 + z.2 • v = A w.1 + w.2 • v at hzw
    have ht : z.2 = w.2 := by
      have h := congrArg L hzw
      simpa only [map_add, map_smul, hLA, hv, smul_eq_mul, mul_one, zero_add] using h
    rw [ht] at hzw
    exact Prod.ext (hAi (add_right_cancel hzw)) ht
  · intro w
    have hrem : w - L w • v ∈ L.ker := by
      change L (w - L w • v) = 0
      simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
    rw [← hrange] at hrem
    obtain ⟨u, hu⟩ := hrem
    change A u = w - L w • v at hu
    refine ⟨(u, L w), ?_⟩
    change A u + L w • v = w
    rw [hu, sub_add_cancel]

private theorem Smale.RegularLevel.surjective_normal_derivative_of_tangent_lift {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] {n : M → N} (x : { x : M // f x = b })
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M)) (R : N →L[ℝ] E)
    (hheight : (mvfderiv 𝓘(ℝ, E) f (x : M)).comp R = 0)
    (hnormal :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M) : E →L[ℝ] N).comp R = ContinuousLinearMap.id ℝ N) :
    letI := chartedSpace hf hreg
    Function.Surjective
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, N) (n ∘ (Subtype.val : { x : M // f x = b } → M)) x) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E) (Subtype.val : { x : M // f x = b } → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  let B : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M)
  change L.comp R = 0 at hheight
  change B.comp R = ContinuousLinearMap.id ℝ N at hnormal
  have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
  rw [mfderiv_comp x hn
      ((Smale.RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))]
  change Function.Surjective (B.comp A)
  intro z
  have hker : R z ∈ L.ker := by
    change L (R z) = 0
    exact congrArg (fun T : N →L[ℝ] ℝ => T z) hheight
  rw [← hrange] at hker
  obtain ⟨v, hv⟩ := hker
  change A v = R z at hv
  refine ⟨v, ?_⟩
  change B (A v) = z
  rw [hv]
  exact congrArg (fun T : N →L[ℝ] N => T z) hnormal

private structure
    Smale.NativeEuclideanEmbedding (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  ambientDimension : ℕ
  toFun : M → EuclideanSpace ℝ (Fin ambientDimension)
  smooth : ContMDiff 𝓘(ℝ, E) (𝓡 ambientDimension) ∞ toFun
  closedEmbedding : Topology.IsClosedEmbedding toFun
  injective_mfderiv : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) (𝓡 ambientDimension) toFun x)

private theorem
    Smale.nonempty_nativeEuclideanEmbedding {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    Nonempty (NativeEuclideanEmbedding E M) := by
  obtain ⟨n, f, hs, hc, hd⟩ := exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  exact ⟨⟨n, f, hs, hc, hd⟩⟩

private theorem Smale.NativeEuclideanEmbedding.injective_mvfderiv {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Function.Injective (mvfderiv 𝓘(ℝ, E) e.toFun x) :=
  (NormedSpace.fromTangentSpace (e.toFun x)).injective.comp (e.injective_mfderiv x)

private def
    Smale.NativeEuclideanEmbedding.tangentImage {E : Type*} {M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (mvfderiv 𝓘(ℝ, E) e.toFun x).range

private theorem Smale.NativeEuclideanEmbedding.finrank_tangentImage {E : Type*} {M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ (e.tangentImage x) = Module.finrank ℝ E := by
  exact LinearMap.finrank_range_of_inj (e.injective_mvfderiv x)

private noncomputable def NoExotic.realAdjoint {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E)
    where
  toFun A := A.adjoint
  map_add' A B := map_add ContinuousLinearMap.adjoint A B
  map_smul' r A := by simp
  cont := ContinuousLinearMap.adjoint.continuous

private noncomputable def NoExotic.gramOperator {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) : E →L[ℝ] E :=
  A.adjoint.comp A

private theorem NoExotic.gramOperator_isInvertible {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    (gramOperator A).IsInvertible := by
  have hG : Function.Injective (gramOperator A) := A.adjoint_comp_self_injective_iff.mpr hA
  let g := (LinearEquiv.ofInjectiveEndo (gramOperator A).toLinearMap hG).toContinuousLinearEquiv
  exact ⟨g, by ext v; rfl⟩

private noncomputable def NoExotic.gramProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) : F →L[ℝ] F :=
  A.comp ((gramOperator A).inverse.comp A.adjoint)

private theorem NoExotic.gramProjection_eq_starProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    gramProjection A = A.range.starProjection := by
  ext v
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(gramOperator A).inverse (A.adjoint v), rfl⟩
  · rw [A.orthogonal_range]
    change A.adjoint (v - A ((gramOperator A).inverse (A.adjoint v))) = 0
    rw [map_sub]
    change A.adjoint v - gramOperator A ((gramOperator A).inverse (A.adjoint v)) = 0
    rw [(gramOperator_isInvertible A hA).self_apply_inverse, sub_self]

private theorem NoExotic.contMDiffAt_gramProjection {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    {A : M → E →L[ℝ] F} {x : M} (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x)
    (hinj : Function.Injective (A x)) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ gramProjection (A y)) x := by
  have hadj : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun y ↦ (A y).adjoint) x :=
    (realAdjoint.contDiff.contMDiff.contMDiffAt).comp x hA
  have hgram : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ gramOperator (A y)) x := hadj.clm_comp hA
  have hinverse : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ (gramOperator (A y)).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ gramOperator (A y)) (x := x)
      (gramOperator_isInvertible (A x) hinj).contDiffAt_map_inverse hgram
  exact hA.clm_comp (hinverse.clm_comp hadj)

private def Smale.NativeEuclideanEmbedding.localDifferential {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : Smale.NativeEuclideanEmbedding E M) (x₀ : M) :
    M → E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  inTangentCoordinates 𝓘(ℝ, E) (𝓡 e.ambientDimension) id e.toFun
    (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun) x₀

private theorem Smale.NativeEuclideanEmbedding.contMDiffAt_localDifferential {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x₀ : M) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
      (e.localDifferential x₀) x₀ :=
  e.smooth.contMDiffAt.mfderiv_const (by simp)

private theorem
    Smale.NativeEuclideanEmbedding.localDifferential_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : Smale.NativeEuclideanEmbedding E M) (x₀ y : M) :
    e.localDifferential x₀ y =
      (mvfderiv 𝓘(ℝ, E) e.toFun y).comp
        ((FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  simp only [localDifferential, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

private theorem Smale.NativeEuclideanEmbedding.localFiberMap_bijective_mo1973_860 {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x₀ y : M) (hy : y ∈ (chartAt E x₀).source) :
    Function.Bijective ((FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ y) := by
  have hy' : y ∈ (FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hy
  rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq _ hy']
  exact ContinuousLinearEquiv.bijective _

private theorem Smale.NativeEuclideanEmbedding.localDifferential_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) : Function.Injective (e.localDifferential x₀ y) := by
  rw [e.localDifferential_eq]
  exact (e.injective_mvfderiv y).comp (localFiberMap_bijective_mo1973_860 x₀ y hy).1

private theorem Smale.NativeEuclideanEmbedding.localDifferential_range {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x₀ y : M)
    (hy : y ∈ (chartAt E x₀).source) : (e.localDifferential x₀ y).range = e.tangentImage y := by
  rw [e.localDifferential_eq]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (localFiberMap_bijective_mo1973_860 x₀ y hy).2

private def Smale.NativeEuclideanEmbedding.tangentProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.tangentImage x).starProjection

private theorem Smale.NativeEuclideanEmbedding.contMDiff_tangentProjection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ,
        EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
      ∞ e.tangentProjection := by
  let φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  intro x
  let A (y : M) := (e.localDifferential x y).comp φ.toContinuousLinearMap
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, _ →L[ℝ] _) ∞ A x :=
    (e.contMDiffAt_localDifferential x).clm_comp contMDiffAt_const
  have hi (y : M) (hy : y ∈ (chartAt E x).source) : Function.Injective (A y) :=
    (e.localDifferential_injective x y hy).comp φ.injective
  have hr (y : M) (hy : y ∈ (chartAt E x).source) : (A y).range = e.tangentImage y := by
    calc
      (A y).range = (e.localDifferential x y).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
      _ = e.tangentImage y := e.localDifferential_range x y hy
  have h := NoExotic.contMDiffAt_gramProjection hs (hi x (mem_chart_source _ _))
  have heq : e.tangentProjection =ᶠ[𝓝 x] (fun y => NoExotic.gramProjection (A y)) := by
    filter_upwards [chart_source_mem_nhds E x] with y hy
    simpa only [tangentProjection, hr y hy] using
      (NoExotic.gramProjection_eq_starProjection _ (hi y hy)).symm
  exact heq.contMDiffAt_iff.mpr h

private def Smale.NativeEuclideanEmbedding.normalFiber {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.tangentImage x)ᗮ

private def Smale.NativeEuclideanEmbedding.normalProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  (e.normalFiber x).starProjection

private theorem
    Smale.NativeEuclideanEmbedding.normalProjection_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    e.normalProjection x = 1 - e.tangentProjection x :=
  Submodule.starProjection_orthogonal' (e.tangentImage x)

private theorem
    Smale.NativeEuclideanEmbedding.range_normalProjection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    (e.normalProjection x).range = e.normalFiber x :=
  (e.normalFiber x).range_starProjection

private theorem Smale.NativeEuclideanEmbedding.normalProjection_idempotent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) : IsIdempotentElem (e.normalProjection x) :=
  (e.normalFiber x).isIdempotentElem_starProjection

end Mathoverflow1973

end
