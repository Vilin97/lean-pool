/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakKernelLocal
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing local almost-everywhere constants

Positive measure of nonempty open overlaps identifies the chosen local values.
These values form a locally constant function on the domain. Only after identifying
their common value do we glue AE statements, using a countable subcover.

Source APIs: Mathlib `Topology/Compactness/Lindelof.lean`
(`IsLindelof.elim_countable_subcover`), `Topology/LocallyConstant/Basic.lean`
(`IsLocallyConstant.exists_eq_const`), and `MeasureTheory/Measure/Restrict.lean`
(`ae_restrict_biUnion_iff`). No uncountable intersection of full-measure sets is used.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

namespace AlmostSchur

/-- Local AE constants glue on a preconnected Lindelöf set. The local neighborhoods
are ambient open sets; neither measurability nor regularity of `u` is needed. -/
theorem ae_eq_const_on_of_locally_ae_eq_const
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {β : Type*} [Nonempty β] {μ : Measure X} [μ.IsOpenPosMeasure]
    {S : Set X} (hS : IsPreconnected S) (hL : IsLindelof S) {u : X → β}
    (hloc : ∀ x ∈ S, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ c : β, u =ᵐ[μ.restrict V] (fun _ => c)) :
    ∃ c : β, u =ᵐ[μ.restrict S] (fun _ => c) := by
  classical
  choose V hV hx c hc using (fun x : S => hloc x x.property)
  have hcompat (x y : S) (hy : (y : X) ∈ V x) : c y = c x := by
    have hpos : μ (V x ∩ V y) ≠ 0 :=
      ne_of_gt ((hV x).inter (hV y) |>.measure_pos μ ⟨y, hy, hx y⟩)
    have hcx := ae_restrict_of_ae_restrict_of_subset
      (show V x ∩ V y ⊆ V x from inter_subset_left) (hc x)
    have hcy := ae_restrict_of_ae_restrict_of_subset
      (show V x ∩ V y ⊆ V y from inter_subset_right) (hc y)
    obtain ⟨z, _, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (hcx.and hcy)
    exact hz.2.symm.trans hz.1
  have hconstant : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq c).2
    intro x
    have hn : ∀ᶠ y : S in 𝓝 x, (y : X) ∈ V x :=
      ((hV x).preimage continuous_subtype_val).mem_nhds (hx x)
    exact hn.mono fun y hy => hcompat x y hy
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  obtain ⟨k, hk⟩ := hconstant.exists_eq_const
  have hcover : S ⊆ ⋃ x : S, V x := by
    intro x hxS
    exact mem_iUnion.mpr ⟨⟨x, hxS⟩, hx ⟨x, hxS⟩⟩
  obtain ⟨t, ht, htcov⟩ := hL.elim_countable_subcover V hV hcover
  refine ⟨k, ae_restrict_of_ae_restrict_of_subset htcov ?_⟩
  apply (ae_restrict_biUnion_iff V ht (fun x => u x = k)).2
  intro x _
  have hck : c x = k := congrFun hk x
  exact (hc x).mono fun y hy => hy.trans hck

/-- On a preconnected Lindelöf space, locally AE-constant functions are globally
AE constant. This applies in particular to Borel measures on manifolds. -/
theorem ae_eq_const_of_locally_ae_eq_const
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [PreconnectedSpace X] [LindelofSpace X]
    {β : Type*} [Nonempty β] {μ : Measure X} [μ.IsOpenPosMeasure] {u : X → β}
    (hloc : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ c : β, u =ᵐ[μ.restrict V] (fun _ => c)) :
    ∃ c : β, u =ᵐ[μ] (fun _ => c) := by
  simpa only [Measure.restrict_univ] using
    ae_eq_const_on_of_locally_ae_eq_const isPreconnected_univ isLindelof_univ
      (fun x _ => hloc x)

/-- Zero weak directional derivatives imply AE constancy on an open preconnected
Euclidean domain. The original function is only locally integrable. -/
theorem ae_eq_const_on_of_weakDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) {u : E → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hweak : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ v : E, ∫ y, u y * fderiv ℝ φ y v = 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict U] (fun _ => c) := by
  apply ae_eq_const_on_of_locally_ae_eq_const hconn IsLindelof.of_coe
  intro x hxU
  obtain ⟨d, hd, hdx⟩ := Metric.isOpen_iff.mp hU x hxU
  have hclosed : closedBall x (d / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith : d / 2 < d)).trans hdx
  refine ⟨ball x (d / 4), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  exact ae_eq_const_on_ball_of_weakDeriv_eq_zero hu hweak hclosed
    (by positivity) (by linarith)

end AlmostSchur
