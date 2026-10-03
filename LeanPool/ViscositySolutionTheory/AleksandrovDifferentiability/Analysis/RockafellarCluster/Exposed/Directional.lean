/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Thickening

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Directional exposed-face outer semicontinuity

This module packages the subgradient inequalities and compactness wrapper leading to eventual
membership in norm thickenings of an exposed face.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Directional monotonicity of subgradients from two supporting inequalities.

If `r` is a subgradient at `y` and `ps i` is a subgradient at `xs i`, then pairing both
subgradient inequalities with the displacement `xs i - y` gives
`r · (xs i - y) ≤ ps i · (xs i - y)`. This is the elementary inequality behind
Rockafellar's directional outer-semicontinuity theorem. -/
theorem eventually_inner_le_unitDirection_of_subgradientOn
    {ι : Type*} {l : Filter ι} {domain : Set E} {u : E → ℝ}
    {y r : E} {xs ps : ι → E}
    (hr : SubgradientOn domain u y r)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i)) :
    (fun i => inner ℝ r (‖xs i - y‖⁻¹ • (xs i - y))) ≤ᶠ[l]
      (fun i => inner ℝ (ps i) (‖xs i - y‖⁻¹ • (xs i - y))) := by
  filter_upwards [hsub] with i hpsi
  have hyx : u y + inner ℝ r (xs i - y) ≤ u (xs i) :=
    hr.supporting_inequality hpsi.mem
  have hxy : u (xs i) + inner ℝ (ps i) (y - xs i) ≤ u y :=
    hpsi.supporting_inequality hr.mem
  have hsub_eq : y - xs i = -(xs i - y) := by
    abel
  rw [hsub_eq, inner_neg_right] at hxy
  have hraw : inner ℝ r (xs i - y) ≤ inner ℝ (ps i) (xs i - y) := by
    linarith
  have hscale :
      ‖xs i - y‖⁻¹ * inner ℝ r (xs i - y) ≤
        ‖xs i - y‖⁻¹ * inner ℝ (ps i) (xs i - y) :=
    mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (norm_nonneg _))
  simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hscale

omit [CompleteSpace E] in
/-- Directional closed-graph inequality for subgradients.

Let `ps i ∈ ∂u(xs i)` and suppose the normalized displacements
`‖xs i - y‖⁻¹ • (xs i - y)` tend to `normal`, while `ps i` tends to `q`. Then every
base subgradient `r ∈ ∂u(y)` satisfies
`normal · r ≤ normal · q`.

This is the Lean-local half-space form of the exposed-face conclusion in Rockafellar's
directional outer-semicontinuity step. -/
theorem inner_le_of_subgradientOn_tendsto_direction
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] {domain : Set E} {u : E → ℝ}
    {y r q normal : E} {xs ps : ι → E}
    (hr : SubgradientOn domain u y r)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i))
    (hdir :
      Filter.Tendsto (fun i => ‖xs i - y‖⁻¹ • (xs i - y)) l (𝓝 normal))
    (hps : Filter.Tendsto ps l (𝓝 q)) :
    inner ℝ normal r ≤ inner ℝ normal q := by
  have hle_eventually :
      (fun i => inner ℝ r (‖xs i - y‖⁻¹ • (xs i - y))) ≤ᶠ[l]
        (fun i => inner ℝ (ps i) (‖xs i - y‖⁻¹ • (xs i - y))) :=
    eventually_inner_le_unitDirection_of_subgradientOn hr hsub
  have hleft :
      Filter.Tendsto (fun i => inner ℝ r (‖xs i - y‖⁻¹ • (xs i - y))) l
        (𝓝 (inner ℝ r normal)) :=
    tendsto_const_nhds.inner hdir
  have hright :
      Filter.Tendsto (fun i => inner ℝ (ps i) (‖xs i - y‖⁻¹ • (xs i - y))) l
        (𝓝 (inner ℝ q normal)) :=
    hps.inner hdir
  have hlimit : inner ℝ r normal ≤ inner ℝ q normal :=
    le_of_tendsto_of_tendsto hleft hright hle_eventually
  simpa [real_inner_comm] using hlimit

omit [CompleteSpace E] in
/-- A convergent directional family of subgradients lands in the exposed face of the base
subdifferential. -/
theorem tendsto_subgradientOn_mem_exposedFace
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] {domain : Set E} {u : E → ℝ}
    {y q normal : E} {xs ps : ι → E}
    (hq : SubgradientOn domain u y q)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i))
    (hdir :
      Filter.Tendsto (fun i => ‖xs i - y‖⁻¹ • (xs i - y)) l (𝓝 normal))
    (hps : Filter.Tendsto ps l (𝓝 q)) :
    q ∈ exposedFace {r : E | SubgradientOn domain u y r} normal := by
  refine ⟨hq, ?_⟩
  intro r hr
  exact inner_le_of_subgradientOn_tendsto_direction hr hsub hdir hps

omit [CompleteSpace E] in
/-- Cluster-point version of the directional exposed-face inequality for subgradients.

This is the form needed for the compactness upgrade in Rockafellar's directional
outer-semicontinuity proof: `ps` need only have `q` as a cluster point, not as an ordinary
limit. -/
theorem mapClusterPt_subgradientOn_mem_exposedFace
    {ι : Type*} {l : Filter ι} {domain : Set E} {u : E → ℝ}
    {y q normal : E} {xs ps : ι → E}
    (hq : SubgradientOn domain u y q)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i))
    (hdir :
      Filter.Tendsto (fun i => ‖xs i - y‖⁻¹ • (xs i - y)) l (𝓝 normal))
    (hps : MapClusterPt q l ps) :
    q ∈ exposedFace {r : E | SubgradientOn domain u y r} normal := by
  refine ⟨hq, ?_⟩
  intro r hr
  have hle_eventually :
      (fun i => inner ℝ r (‖xs i - y‖⁻¹ • (xs i - y))) ≤ᶠ[l]
        (fun i => inner ℝ (ps i) (‖xs i - y‖⁻¹ • (xs i - y))) :=
    eventually_inner_le_unitDirection_of_subgradientOn hr hsub
  have hleft :
      Filter.Tendsto (fun i => inner ℝ r (‖xs i - y‖⁻¹ • (xs i - y))) l
        (𝓝 (inner ℝ r normal)) :=
    tendsto_const_nhds.inner hdir
  have hright_cluster :
      MapClusterPt (inner ℝ q normal) l
        (fun i => inner ℝ (ps i) (‖xs i - y‖⁻¹ • (xs i - y))) := by
    have hpair :
        MapClusterPt (q, normal) l
          (fun i => (ps i, ‖xs i - y‖⁻¹ • (xs i - y))) :=
      MapClusterPt.prod_of_tendsto hps hdir
    have hcont : ContinuousAt (fun z : E × E => inner ℝ z.1 z.2) (q, normal) := by
      fun_prop
    simpa [Function.comp_def] using hpair.continuousAt_comp hcont
  have hlimit : inner ℝ r normal ≤ inner ℝ q normal :=
    le_of_tendsto_of_mapClusterPt_of_eventually_le hleft hright_cluster hle_eventually
  simpa [real_inner_comm] using hlimit

omit [CompleteSpace E] in
/-- Compact directional outer-semicontinuity wrapper for moving subgradients.

If moving subgradients `ps i ∈ ∂u(xs i)` are eventually contained in a compact set `K`, every
cluster point of `ps` inside `K` is a base subgradient at `y`, and the normalized directions from
`y` to `xs i` tend to `normal`, then the moving subgradients are eventually in every positive
norm-thickening of the exposed face of the base subdifferential. -/
theorem IsCompact.eventually_mem_normThickening_exposedFace_of_directional_subgradientOn
    {ι : Type*} {l : Filter ι} {domain : Set E} {u : E → ℝ}
    {y normal : E} {xs ps : ι → E} {K : Set E}
    (hK : IsCompact K)
    (hmemK : ∀ᶠ i in l, ps i ∈ K)
    (hbase : ∀ q ∈ K, MapClusterPt q l ps → SubgradientOn domain u y q)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i))
    (hdir :
      Filter.Tendsto (fun i => ‖xs i - y‖⁻¹ • (xs i - y)) l (𝓝 normal))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l,
      ps i ∈ normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε :=
  IsCompact.eventually_mem_normThickening_of_forall_mapClusterPt hK hmemK
    (fun q hqK hqcluster =>
      mapClusterPt_subgradientOn_mem_exposedFace
        (hbase q hqK hqcluster) hsub hdir hqcluster)
    hε

omit [CompleteSpace E] in
/-- Compact directional outer-semicontinuity wrapper with the base-subgradient condition supplied
by the local closed graph theorem.

This is the local finite-valued analogue of the compact part of Rockafellar's Theorem 24.6:
cluster points of the moving subgradients become subgradients at the limit base point, and the
directional inequality then puts them in the exposed face. -/
theorem IsCompact.eventually_mem_normThickening_exposedFace_of_directional_subgradientOn'
    {ι : Type*} {l : Filter ι} {domain : Set E} {u : E → ℝ}
    {y normal : E} {xs ps : ι → E} {K : Set E}
    (hK : IsCompact K)
    (hmemK : ∀ᶠ i in l, ps i ∈ K)
    (hy : y ∈ domain)
    (hxs : Filter.Tendsto xs l (𝓝 y))
    (hu : ContinuousAt u y)
    (hsub : ∀ᶠ i in l, SubgradientOn domain u (xs i) (ps i))
    (hdir :
      Filter.Tendsto (fun i => ‖xs i - y‖⁻¹ • (xs i - y)) l (𝓝 normal))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l,
      ps i ∈ normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε :=
  IsCompact.eventually_mem_normThickening_exposedFace_of_directional_subgradientOn hK hmemK
    (fun _q _hqK hqcluster =>
      SubgradientOn.of_mapClusterPt_of_continuousAt hy hxs hqcluster hu hsub)
    hsub hdir hε

/-- Gradient-sample form of the compact directional outer-semicontinuity wrapper.

At differentiability points of a convex function, `gradient u` is a subgradient. Therefore the
moving-subgradient wrapper applies directly to differentiability samples approaching the base
point in the exposing direction. -/
theorem ConvexOn.eventually_gradient_mem_normThickening_exposedFace_of_compact_directional
    {ι : Type*} {l : Filter ι} {domain : Set E} {u : E → ℝ}
    {y normal : E} {φ : ι → E} {K : Set E}
    (huconv : ConvexOn ℝ domain u)
    (hK : IsCompact K)
    (hmemK : ∀ᶠ i in l, gradient u (φ i) ∈ K)
    (hy : y ∈ domain)
    (hφ : Filter.Tendsto φ l (𝓝 y))
    (hucont : ContinuousAt u y)
    (hφ_mem : ∀ᶠ i in l, φ i ∈ interior domain)
    (hφ_diff : ∀ᶠ i in l, DifferentiableAt ℝ u (φ i))
    (hdir :
      Filter.Tendsto (fun i => ‖φ i - y‖⁻¹ • (φ i - y)) l (𝓝 normal))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l,
      gradient u (φ i) ∈
        normThickening (exposedFace {q : E | SubgradientOn domain u y q} normal) ε := by
  refine IsCompact.eventually_mem_normThickening_exposedFace_of_directional_subgradientOn'
    (xs := φ) (ps := fun i => gradient u (φ i)) hK hmemK hy hφ hucont ?_ hdir hε
  filter_upwards [hφ_mem, hφ_diff] with i hmem hdiff
  exact ConvexOn.subgradientOn_gradient_of_differentiableAt huconv hmem hdiff

end AleksandrovDifferentiability
