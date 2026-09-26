/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

/-!
# Open mapping for complete metrizable real or complex vector spaces

This supplies the open-mapping argument needed for holomorphic function spaces with their
compact-open topology. Baire's theorem first gives neighborhoods in closures of images;
successive approximations and completeness remove the closure. The compatible metrics need not
arise from norms and scalar multiplication need not preserve them.

## Main results

`isOpenMap_of_surjective_complete` is the open mapping theorem for a surjective continuous
linear map from a complete metrizable space to a Hausdorff metrizable Baire space. Its proof goes
through a private neighborhood form: the image of every zero neighborhood is a zero neighborhood.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [PseudoMetricSpace E]
  [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [PseudoMetricSpace F]
  [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]

/-- Baire's theorem gives a neighborhood in the closure of the image of any zero neighborhood under
a surjective continuous linear map. -/
private theorem closure_image_mem_nhds_of_surjective [BaireSpace F]
    (T : E →L[𝕜] F) (hs : Function.Surjective T) {W : Set E} (hW : W ∈ 𝓝 0) :
    closure (T '' W) ∈ 𝓝 0 := by
  classical
  have hsub : {p : E × E | p.1 - p.2 ∈ W} ∈ 𝓝 (0, 0) :=
    (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨D, hD, D', hD', hDD⟩ := mem_nhds_prod_iff.mp hsub
  let B := D ∩ D'
  have hB : B ∈ 𝓝 (0 : E) := inter_mem hD hD'
  have hBW {x y : E} (hx : x ∈ B) (hy : y ∈ B) : x - y ∈ W :=
    hDD (show (x, y) ∈ D ×ˢ D' from ⟨hx.1, hy.2⟩)
  let c (n : ℕ) : 𝕜 := (n + 1 : ℕ)
  have hc (n : ℕ) : c n ≠ 0 := by dsimp [c]; exact_mod_cast Nat.succ_ne_zero n
  let e (n : ℕ) : F ≃L[𝕜] F :=
    ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := F) (Units.mk0 (c n) (hc n))
  let S := closure (T '' B)
  have hcover : ⋃ n, e n '' S = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := hs y
    have ht : Tendsto (fun n => (c n)⁻¹ • x) atTop (𝓝 (0 : E)) := by
      simpa [c, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜)).smul_const x
    obtain ⟨n, hn⟩ := (ht.eventually hB).exists
    refine ⟨n, T ((c n)⁻¹ • x), subset_closure ⟨_, hn, rfl⟩, ?_⟩
    simp [e, map_smul, smul_smul, hc]
  obtain ⟨n, z, hz⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n => (e n).toHomeomorph.isClosedMap S isClosed_closure) hcover
  let a := (e n).symm z
  have hS : S ∈ 𝓝 a := by
    have hh := (e n).continuous.continuousAt.preimage_mem_nhds
      (show e n '' S ∈ 𝓝 (e n a) by
        simpa [a] using mem_interior_iff_mem_nhds.mp hz)
    simpa only [preimage_image_eq _ (e n).injective] using hh
  have ha : a ∈ S := mem_of_mem_nhds hS
  have hN : (fun y : F => y + a) ⁻¹' S ∈ 𝓝 0 :=
    (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hS)
  apply mem_of_superset hN
  intro y hy
  have hh : (y + a) - a ∈ closure (T '' W) :=
    map_mem_closure₂ continuous_sub hy ha (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      exact ⟨x - x', hBW hx hx', T.map_sub x x'⟩)
  simpa only [add_sub_cancel_right] using hh

/-- Completeness removes the closure from the neighborhood conclusion in the Baire argument by
successively correcting the error with geometrically small increments. -/
private theorem image_mem_nhds_of_surjective [CompleteSpace E] [BaireSpace F] [T2Space F]
    (T : E →L[𝕜] F) (hs : Function.Surjective T) {W : Set E} (hW : W ∈ 𝓝 0) :
    T '' W ∈ 𝓝 0 := by
  classical
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  have hsmall (n : ℕ) : ∃ B ∈ 𝓝 (0 : E),
      ∀ x ∈ B, ∀ s : E, dist s (s + x) ≤ (r / 2) * (1 / 2 : ℝ) ^ n := by
    have h := dist_mem_uniformity (α := E) (show 0 < (r / 2) * (1 / 2 : ℝ) ^ n by positivity)
    rw [uniformity_eq_comap_nhds_zero E] at h
    obtain ⟨B, hB, hsub⟩ := Filter.mem_comap.mp h
    refine ⟨B, hB, fun x hx s => le_of_lt (hsub
      (show (s, s + x) ∈ (fun p : E × E => p.2 - p.1) ⁻¹' B from ?_))⟩
    change (s + x) - s ∈ B
    simpa only [add_sub_cancel_left] using hx
  choose B hB hdist using hsmall
  let V (n : ℕ) := interior (closure (T '' B n)) ∩ ball 0 (1 / ((n : ℝ) + 1))
  have hVo (n : ℕ) : IsOpen (V n) := isOpen_interior.inter isOpen_ball
  have hV0 (n : ℕ) : (0 : F) ∈ V n := by
    refine ⟨mem_interior_iff_mem_nhds.mpr
      (closure_image_mem_nhds_of_surjective T hs (hB n)), ?_⟩
    simp only [mem_ball, dist_self]
    positivity
  have happrox (n : ℕ) (y : F) (hy : y ∈ V n) :
      ∃ x ∈ B n, y - T x ∈ V (n + 1) := by
    have hopen : IsOpen ((fun z : F => y - z) ⁻¹' V (n + 1)) :=
      (hVo _).preimage (continuous_const.sub continuous_id)
    obtain ⟨z, hz, x, hx, rfl⟩ :=
      _root_.mem_closure_iff.mp (interior_subset hy.1) _ hopen (by simpa using hV0 (n + 1))
    exact ⟨x, hx, hz⟩
  apply mem_of_superset ((hVo 0).mem_nhds (hV0 0))
  intro y hy
  let step (n : ℕ) (s : {s : E // y - T s ∈ V n}) :
      {s : E // y - T s ∈ V (n + 1)} :=
    ⟨s.val + (happrox n (y - T s.val) s.property).choose, by
      have h := (happrox n (y - T s.val) s.property).choose_spec.2
      simpa only [map_add, sub_sub] using h⟩
  let seq : (n : ℕ) → {s : E // y - T s ∈ V n} :=
    fun n => Nat.rec (motive := fun n => {s : E // y - T s ∈ V n})
      ⟨0, by simpa using hy⟩ step n
  have hd (n : ℕ) : dist (seq n).val (seq (n + 1)).val ≤ (r / 2) * (1 / 2 : ℝ) ^ n :=
    hdist n _ (happrox n (y - T (seq n).val) (seq n).property).choose_spec.1 _
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2) (r / 2) (by norm_num) hd)
  have hxW : x ∈ W := by
    apply hrW
    have h := dist_le_of_le_geometric_of_tendsto₀ (1 / 2) (r / 2) (by norm_num) hd hx
    change dist x 0 ≤ r
    norm_num [seq, dist_comm, div_div] at h ⊢
    exact h
  have herr : Tendsto (fun n => y - T (seq n).val) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => le_of_lt (show dist (y - T (seq n).val) 0 < 1 / ((n : ℝ) + 1) from
        (seq n).property.2))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have heq : y - T x = 0 := tendsto_nhds_unique
    (tendsto_const_nhds.sub (T.continuous.tendsto x |>.comp hx)) herr
  exact ⟨x, hxW, (sub_eq_zero.mp heq).symm⟩

/-- A surjective continuous real- or complex-linear map from a complete metrizable topological
vector space to a Hausdorff metrizable Baire vector space is open. The metrics only need to
induce the additive uniformities; they need not arise from norms. -/
theorem isOpenMap_of_surjective_complete [CompleteSpace E] [BaireSpace F] [T2Space F]
    (T : E →L[𝕜] F) (hs : Function.Surjective T) : IsOpenMap T := by
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  intro S hS
  exact mem_of_superset (image_mem_nhds_of_surjective T hs hS) (image_preimage_subset _ _)

end ContinuousLinearMap

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
