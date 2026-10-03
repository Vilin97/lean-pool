/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Face

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Norm thickenings and cluster tools

This module contains the open norm-thickening API and general cluster-point lemmas used in the
Rockafellar directional outer-semicontinuity argument.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Open norm-thickening of a set.

This is the project-local version of the set `A + ε B` appearing in Rockafellar's directional
outer semicontinuity theorem: a point lies in `normThickening A ε` if it is within norm-distance
`< ε` of some point of `A`. -/
def normThickening (s : Set E) (ε : ℝ) : Set E :=
  {x | ∃ a ∈ s, ‖x - a‖ < ε}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The project-local open norm thickening is open. -/
theorem isOpen_normThickening (s : Set E) (ε : ℝ) :
    IsOpen (normThickening s ε) := by
  have hset : normThickening s ε = ⋃ a : s, Metric.ball (a : E) ε := by
    ext x
    simp [normThickening, Metric.mem_ball, dist_eq_norm]
  rw [hset]
  exact isOpen_iUnion fun a => Metric.isOpen_ball

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A set is contained in every positive norm thickening of itself. -/
theorem subset_normThickening_self {s : Set E} {ε : ℝ} (hε : 0 < ε) :
    s ⊆ normThickening s ε := by
  intro x hx
  exact ⟨x, hx, by simpa using hε⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every positive norm thickening is a neighborhood of the thickened set. -/
theorem normThickening_mem_nhdsSet (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    normThickening s ε ∈ 𝓝ˢ s :=
  (isOpen_normThickening s ε).mem_nhdsSet.2 (subset_normThickening_self hε)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Compact cluster-point criterion for eventual membership in norm thickenings.

If `f` is eventually contained in a compact set `K`, and every cluster value of `f` in `K`
belongs to `target`, then `f` is eventually contained in every positive norm-thickening of
`target`. This is the abstract compactness/contradiction step in Rockafellar's directional
outer-semicontinuity argument. -/
theorem IsCompact.eventually_mem_normThickening_of_forall_mapClusterPt
    {ι : Type*} {l : Filter ι} {K target : Set E} {f : ι → E}
    (hK : IsCompact K)
    (hmem : ∀ᶠ i in l, f i ∈ K)
    (hcluster : ∀ q ∈ K, MapClusterPt q l f → q ∈ target)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, f i ∈ normThickening target ε :=
  hK.tendsto_nhdsSet_of_mapClusterPt hmem hcluster
    (normThickening_mem_nhdsSet target hε)

/-- Pair a map-cluster point with an ordinary limit along the same filter. -/
theorem MapClusterPt.prod_of_tendsto
    {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {l : Filter ι} {u : ι → X} {v : ι → Y} {x : X} {y : Y}
    (hu : MapClusterPt x l u) (hv : Filter.Tendsto v l (𝓝 y)) :
    MapClusterPt (x, y) l (fun i => (u i, v i)) := by
  rw [mapClusterPt_iff_frequently]
  intro U hU
  rcases mem_nhds_prod_iff.mp hU with ⟨Ux, hUx, Uy, hUy, hsubset⟩
  exact ((mapClusterPt_iff_frequently.mp hu Ux hUx).and_eventually (hv hUy)).mono
    fun i hi => hsubset ⟨hi.1, hi.2⟩

/-- An eventual scalar inequality passes to a limit on the left and a cluster point on the
right. -/
theorem le_of_tendsto_of_mapClusterPt_of_eventually_le
    {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {a b : ℝ}
    (hf : Filter.Tendsto f l (𝓝 a))
    (hg : MapClusterPt b l g)
    (hle : f ≤ᶠ[l] g) :
    a ≤ b := by
  by_contra hnot
  have hlt : b < a := lt_of_not_ge hnot
  let δ : ℝ := (a - b) / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδ_gap : b + δ < a - δ := by
    dsimp [δ]
    linarith
  have hf_event : ∀ᶠ i in l, a - δ < f i := by
    have hmem : Set.Ioi (a - δ) ∈ 𝓝 a := by
      exact Ioi_mem_nhds (by linarith)
    exact hf hmem
  have hg_freq : ∃ᶠ i in l, g i ∈ Set.Iio (b + δ) :=
    mapClusterPt_iff_frequently.mp hg (Set.Iio (b + δ)) (Iio_mem_nhds (by linarith))
  have hfreq : ∃ᶠ i in l, g i < b + δ ∧ a - δ < f i ∧ f i ≤ g i :=
    (hg_freq.and_eventually (hf_event.and hle)).mono fun i hi => ⟨hi.1, hi.2.1, hi.2.2⟩
  rcases hfreq.exists with ⟨i, hgi, hfi, hlei⟩
  linarith

/-- An eventual scalar inequality passes to a cluster point on the left and a limit on the
right. -/
theorem le_of_mapClusterPt_of_tendsto_of_eventually_le
    {ι : Type*} {l : Filter ι} {f g : ι → ℝ} {a b : ℝ}
    (hf : MapClusterPt a l f)
    (hg : Filter.Tendsto g l (𝓝 b))
    (hle : f ≤ᶠ[l] g) :
    a ≤ b := by
  have hneg_cluster : MapClusterPt (-a) l (fun i => -f i) := by
    have hcont : ContinuousAt (fun x : ℝ => -x) a := by fun_prop
    simpa [Function.comp_def] using hf.continuousAt_comp hcont
  have hneg_tend : Filter.Tendsto (fun i => -g i) l (𝓝 (-b)) := by
    simpa using hg.neg
  have hneg_le : (fun i => -g i) ≤ᶠ[l] (fun i => -f i) := by
    filter_upwards [hle] with i hi
    linarith
  have hle_neg : -b ≤ -a :=
    le_of_tendsto_of_mapClusterPt_of_eventually_le hneg_tend hneg_cluster hneg_le
  linarith

omit [CompleteSpace E] in
/-- Closed-graph form of the subgradient inequality for cluster points.

This is the cluster-point analogue of `SubgradientOn.of_tendsto`: the slopes `ps i` need only
cluster at `p`, while the base points `xs i` converge to `x`. -/
theorem SubgradientOn.of_mapClusterPt_of_continuousAt
    {ι : Type*} {l : Filter ι} {s : Set E} {u : E → ℝ}
    {x p : E} {xs ps : ι → E}
    (hx : x ∈ s)
    (hxs : Filter.Tendsto xs l (𝓝 x))
    (hps : MapClusterPt p l ps)
    (hu : ContinuousAt u x)
    (hsub : ∀ᶠ i in l, SubgradientOn s u (xs i) (ps i)) :
    SubgradientOn s u x p := by
  refine ⟨hx, ?_⟩
  intro z hz
  have hpair : MapClusterPt (p, x) l (fun i => (ps i, xs i)) :=
    MapClusterPt.prod_of_tendsto hps hxs
  have hcont :
      ContinuousAt (fun w : E × E => u w.2 + inner ℝ w.1 (z - w.2)) (p, x) := by
    have hu_comp : ContinuousAt (fun w : E × E => u w.2) (p, x) :=
      hu.comp (by fun_prop)
    have hinner : ContinuousAt (fun w : E × E => inner ℝ w.1 (z - w.2)) (p, x) := by
      fun_prop
    exact hu_comp.add hinner
  have hleft :
      MapClusterPt (u x + inner ℝ p (z - x)) l
        (fun i => u (xs i) + inner ℝ (ps i) (z - xs i)) := by
    simpa [Function.comp_def] using hpair.continuousAt_comp hcont
  have hright : Filter.Tendsto (fun _ : ι => u z) l (𝓝 (u z)) :=
    tendsto_const_nhds
  have hle :
      (fun i => u (xs i) + inner ℝ (ps i) (z - xs i)) ≤ᶠ[l]
        (fun _ : ι => u z) := by
    filter_upwards [hsub] with i hi
    exact hi.supporting_inequality hz
  exact le_of_mapClusterPt_of_tendsto_of_eventually_le hleft hright hle

end AleksandrovDifferentiability
