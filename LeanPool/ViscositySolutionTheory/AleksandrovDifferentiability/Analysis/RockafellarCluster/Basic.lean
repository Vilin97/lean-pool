/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LineRestriction
public import Mathlib.Analysis.Convex.Continuous

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic Rockafellar-style subgradient cluster-density interfaces

This module contains the local cluster-density predicate, elementary topological wrappers for the
Rockafellar ray construction, and the basic convex-gradient cluster facts used by later modules.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Differentiability points inside a prescribed sampling region. -/
def differentiabilitySetOn (s : Set E) (u : E → ℝ) : Set E :=
  s ∩ {x | DifferentiableAt ℝ u x}

/-- Local interior form of the Rockafellar subgradient cluster-density conclusion.

For every point `y` in the sampling region and every subgradient `p` of `u` at `y` relative to
the larger domain, `p` belongs to the closed convex hull of all ambient cluster values of
`gradient u` along differentiability points in the sampling region approaching `y`.

The assumptions that the sets are open, convex, and nested are kept in the theorem statement
below rather than inside this conclusion predicate. -/
def LocalSubgradientClusterDensityOn
    (domain sample : Set E) (u : E → ℝ) : Prop :=
  ∀ ⦃y p : E⦄,
    y ∈ sample →
      SubgradientOn domain u y p →
        p ∈ closure
          (convexHull ℝ
            (HasSubgradientLinearizationOnAt.GradientClusterSet
              (differentiabilitySetOn sample u) (gradient u) y))

/-- At a differentiability point, the local cluster-density conclusion is immediate.

Indeed, any subgradient relative to a neighborhood domain is the gradient, and that gradient is
itself a cluster value through the non-punctured differentiability filter. -/
theorem mem_closure_convexHull_gradientClusterSet_of_differentiableAt
    {domain sample : Set E} {u : E → ℝ} {y p : E}
    (hdomain : domain ∈ 𝓝 y) (hy : y ∈ sample) (hdu : DifferentiableAt ℝ u y)
    (hp : SubgradientOn domain u y p) :
    p ∈ closure
      (convexHull ℝ
        (HasSubgradientLinearizationOnAt.GradientClusterSet
          (differentiabilitySetOn sample u) (gradient u) y)) := by
  have hp_eq : p = gradient u y :=
    hp.eq_gradient_of_differentiableAt hdomain hdu
  subst p
  exact HasSubgradientLinearizationOnAt.GradientClusterSet.mem_closure_convexHull_of_mem
    (D := differentiabilitySetOn sample u) (G := gradient u) ⟨hy, hdu⟩

/-- If `u` is differentiable on the whole sampling set and the domain is a neighborhood of each
sample point, then the local cluster-density conclusion holds on that sampling set. -/
theorem localSubgradientClusterDensityOn_of_forall_differentiableAt
    {domain sample : Set E} {u : E → ℝ}
    (hdomain : ∀ ⦃y : E⦄, y ∈ sample → domain ∈ 𝓝 y)
    (hdu : ∀ ⦃y : E⦄, y ∈ sample → DifferentiableAt ℝ u y) :
    LocalSubgradientClusterDensityOn domain sample u := by
  intro y p hy hp
  exact mem_closure_convexHull_gradientClusterSet_of_differentiableAt
    (hdomain hy) hy (hdu hy) hp

/-- Open-domain version of
`localSubgradientClusterDensityOn_of_forall_differentiableAt`. -/
theorem localSubgradientClusterDensityOn_of_isOpen_of_forall_differentiableAt
    {domain sample : Set E} {u : E → ℝ}
    (hopen : IsOpen domain) (hsubset : sample ⊆ domain)
    (hdu : ∀ ⦃y : E⦄, y ∈ sample → DifferentiableAt ℝ u y) :
    LocalSubgradientClusterDensityOn domain sample u :=
  localSubgradientClusterDensityOn_of_forall_differentiableAt
    (fun {_} hy => hopen.mem_nhds (hsubset hy)) hdu

omit [CompleteSpace E] in
/-- In an open domain, sufficiently small positive steps in any fixed direction remain in the
domain.

This is the local interior replacement for the half-line/interior step in Rockafellar 25.6. In
the global closed-function proof, one must show that the exposing half-line meets
`int (dom f)`. In the local source-cube theorem, the base point is already in an open domain, so
openness gives the needed small positive ray directly. -/
theorem IsOpen.exists_pos_forall_pos_lt_add_smul_mem
    {domain : Set E} {y normal : E}
    (hopen : IsOpen domain) (hy : y ∈ domain) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃t : ℝ⦄, 0 < t → t < δ → y + t • normal ∈ domain := by
  have hpre : {t : ℝ | y + t • normal ∈ domain} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt (fun t : ℝ => y + t • normal) 0 := by fun_prop
    have hdomain0 : domain ∈ 𝓝 ((fun t : ℝ => y + t • normal) 0) := by
      simpa using hopen.mem_nhds hy
    change ((fun t : ℝ => y + t • normal) ⁻¹' domain) ∈ 𝓝 0
    exact hcont hdomain0
  rw [Metric.mem_nhds_iff] at hpre
  rcases hpre with ⟨δ, hδ_pos, hδ_sub⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht_pos ht_lt
  exact hδ_sub (by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos ht_pos]
    exact ht_lt)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A map tending to `y` and eventually lying in `D` tends to `y` through `D`.

This small wrapper records the filter shape of the differentiability sequence in Rockafellar
25.6: after choosing differentiability points, the only remaining topological datum is ordinary
convergence to the base point plus eventual membership in the differentiability set. -/
theorem tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_mem
    {ι : Type*} {l : Filter ι} {D : Set E} {φ : ι → E} {y : E}
    (hφ : Filter.Tendsto φ l (𝓝 y))
    (hmem : ∀ᶠ a in l, φ a ∈ D) :
    Filter.Tendsto φ l (𝓝[D] y) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hφ, hmem⟩

omit [CompleteSpace E] in
/-- If the scalar parameter tends to zero, then the corresponding short ray tends to its base
point.

This is the topological core of the sequence
`x_i ≈ y + ε_i • normal`, `ε_i → 0`, used in the exposed-point argument of Rockafellar 25.6. -/
theorem tendsto_add_smul_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} {y normal : E}
    (hε : Filter.Tendsto ε l (𝓝 0)) :
    Filter.Tendsto (fun a => y + ε a • normal) l (𝓝 y) := by
  have hsmul : Filter.Tendsto (fun a => ε a • normal) l (𝓝 (0 : E)) := by
    simpa using hε.smul (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => normal) l (𝓝 normal))
  simpa using (tendsto_const_nhds.add hsmul :
    Filter.Tendsto (fun a : ι => y + ε a • normal) l (𝓝 (y + (0 : E))))

omit [CompleteSpace E] in
/-- Rockafellar's ray-approach sequence tends to the base point through the chosen set.

The intended use is: `D` is the differentiability set, `φ i` is a differentiability point chosen
near `y + ε i • normal`, `ε i → 0`, and the error norm tends to zero. The conclusion is exactly
the approach-filter hypothesis needed by the directional exposed-subgradient cluster bridge. -/
theorem tendsto_nhdsWithin_of_tendsto_norm_sub_ray_zero
    {ι : Type*} {l : Filter ι} {D : Set E} {φ : ι → E} {ε : ι → ℝ} {y normal : E}
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hmem : ∀ᶠ a in l, φ a ∈ D)
    (hclose :
      Filter.Tendsto (fun a => ‖φ a - (y + ε a • normal)‖) l (𝓝 0)) :
    Filter.Tendsto φ l (𝓝[D] y) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_mem ?_ hmem
  have herror :
      Filter.Tendsto (fun a => φ a - (y + ε a • normal)) l (𝓝 (0 : E)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using hclose
  have hray : Filter.Tendsto (fun a => y + ε a • normal) l (𝓝 y) :=
    tendsto_add_smul_of_tendsto_zero hε
  have hsum :
      Filter.Tendsto
        (fun a => (φ a - (y + ε a • normal)) + (y + ε a • normal)) l
        (𝓝 ((0 : E) + y)) :=
    herror.add hray
  simpa [sub_eq_add_neg, add_assoc] using hsum

omit [CompleteSpace E] in
/-- The explicit `ε_i^2` closeness estimate in Rockafellar's construction forces the ray error
to tend to zero. -/
theorem tendsto_norm_sub_ray_zero_of_eventually_norm_sub_le_sq
    {ι : Type*} {l : Filter ι} {φ : ι → E} {ε : ι → ℝ} {y normal : E}
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hclose :
      ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) :
    Filter.Tendsto (fun a => ‖φ a - (y + ε a • normal)‖) l (𝓝 0) := by
  have hsq : Filter.Tendsto (fun a => (ε a) ^ 2) l (𝓝 0) := by
    simpa [pow_two] using hε.mul hε
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hclose hsq

omit [CompleteSpace E] in
/-- Rockafellar's explicit `ε_i^2` ray-approximation sequence tends to the base point through the
chosen set. -/
theorem tendsto_nhdsWithin_of_eventually_norm_sub_ray_le_sq
    {ι : Type*} {l : Filter ι} {D : Set E} {φ : ι → E} {ε : ι → ℝ} {y normal : E}
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hmem : ∀ᶠ a in l, φ a ∈ D)
    (hclose :
      ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) :
    Filter.Tendsto φ l (𝓝[D] y) :=
  tendsto_nhdsWithin_of_tendsto_norm_sub_ray_zero hε hmem
    (tendsto_norm_sub_ray_zero_of_eventually_norm_sub_le_sq hε hclose)

omit [CompleteSpace E] in
/-- Normalizing a positive scalar multiple does not change the unit direction. -/
theorem unitDirection_pos_smul {t : ℝ} (ht : 0 < t) (v : E) :
    ‖t • v‖⁻¹ • (t • v) = ‖v‖⁻¹ • v := by
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    simp [hv0]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
  congr 1
  field_simp [ht.ne', hv]

omit [CompleteSpace E] in
/-- The scaled error in Rockafellar's `ε_i^2` ray approximation tends to zero.

If `φ i` is within `ε_i^2` of `y + ε_i • normal` and `ε_i > 0`, then after rescaling by
`ε_i^{-1}` the error is bounded by `ε_i`, hence tends to zero. -/
theorem tendsto_inv_smul_sub_ray_of_eventually_norm_sub_le_sq
    {ι : Type*} {l : Filter ι} {φ : ι → E} {ε : ι → ℝ} {y normal : E}
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hεpos : ∀ᶠ a in l, 0 < ε a)
    (hclose :
      ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) :
    Filter.Tendsto
      (fun a => (ε a)⁻¹ • (φ a - (y + ε a • normal))) l (𝓝 (0 : E)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hε
  filter_upwards [hεpos, hclose] with a hpos hle
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc
    (ε a)⁻¹ * ‖φ a - (y + ε a • normal)‖
        ≤ (ε a)⁻¹ * (ε a) ^ 2 :=
      mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hpos))
    _ = ε a := by
      field_simp [hpos.ne']

omit [CompleteSpace E] in
/-- Rockafellar's explicit ray-approximation sequence approaches the exposing direction after
normalization.

This formalizes the line in the source proof saying that from
`||x_i - (x + ε_i y)|| < ε_i^2`, `ε_i ↓ 0`, and `||y|| = 1`, one gets
`(x_i - x) / ||x_i - x|| -> y`. The statement is written with `≤` and filters, in the form used
by the directional outer-semicontinuity bridge. -/
theorem tendsto_unitDirection_sub_of_eventually_norm_sub_ray_le_sq
    {ι : Type*} {l : Filter ι} {φ : ι → E} {ε : ι → ℝ} {y normal : E}
    (hnormal : ‖normal‖ = 1)
    (hε : Filter.Tendsto ε l (𝓝 0))
    (hεpos : ∀ᶠ a in l, 0 < ε a)
    (hclose :
      ∀ᶠ a in l, ‖φ a - (y + ε a • normal)‖ ≤ (ε a) ^ 2) :
    Filter.Tendsto (fun a => ‖φ a - y‖⁻¹ • (φ a - y)) l (𝓝 normal) := by
  let error : ι → E := fun a => φ a - (y + ε a • normal)
  have hscaled :
      Filter.Tendsto (fun a => (ε a)⁻¹ • error a) l (𝓝 (0 : E)) :=
    tendsto_inv_smul_sub_ray_of_eventually_norm_sub_le_sq hε hεpos hclose
  have hinner :
      Filter.Tendsto (fun a => normal + (ε a)⁻¹ • error a) l (𝓝 normal) := by
    simpa using (tendsto_const_nhds.add hscaled :
      Filter.Tendsto (fun a => normal + (ε a)⁻¹ • error a) l (𝓝 (normal + (0 : E))))
  have hnormal_norm_ne : ‖normal‖ ≠ 0 := by
    simp [hnormal]
  have hcont :
      ContinuousAt (fun v : E => ‖v‖⁻¹ • v) normal := by
    exact (continuous_norm.continuousAt.inv₀ hnormal_norm_ne).smul continuousAt_id
  have hnormalized :
      Filter.Tendsto
        (fun a => ‖normal + (ε a)⁻¹ • error a‖⁻¹ •
          (normal + (ε a)⁻¹ • error a)) l (𝓝 normal) := by
    have hlimit : ‖normal‖⁻¹ • normal = normal := by
      simp [hnormal]
    simpa [Function.comp_def, hlimit] using hcont.tendsto.comp hinner
  refine hnormalized.congr' ?_
  filter_upwards [hεpos] with a hpos
  let w : E := normal + (ε a)⁻¹ • error a
  have hsub : φ a - y = ε a • w := by
    dsimp [w, error]
    rw [smul_add, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    abel
  calc
    ‖normal + (ε a)⁻¹ • error a‖⁻¹ •
          (normal + (ε a)⁻¹ • error a)
        = ‖w‖⁻¹ • w := rfl
    _ = ‖ε a • w‖⁻¹ • (ε a • w) := (unitDirection_pos_smul hpos w).symm
    _ = ‖φ a - y‖⁻¹ • (φ a - y) := by rw [← hsub]

/-- At an interior differentiability point of a convex function, the gradient is a subgradient.

This is the finite-valued local version of the standard convex fact used in Rockafellar 25.6 at
nearby differentiability points. -/
theorem ConvexOn.subgradientOn_gradient_of_differentiableAt
    {domain : Set E} {u : E → ℝ} {x : E}
    (hu : ConvexOn ℝ domain u) (hx : x ∈ interior domain)
    (hd : DifferentiableAt ℝ u x) :
    SubgradientOn domain u x (gradient u x) :=
  ConvexOn.subgradientOn_of_hasFDerivAt_of_forall_eq_inner
    hu hx hd.hasFDerivAt
    (fun v => by
      simp)

/-- A gradient cluster value is a subgradient at the base point.

This packages the first closed-graph step in Rockafellar 25.6: gradients at nearby
differentiability points are subgradients at those nearby points, and closedness of the
subdifferential graph passes the supporting inequality to the cluster limit. -/
theorem GradientClusterSet.subset_subgradientOn_of_convexOn
    {domain sample : Set E} {u : E → ℝ} {y q : E}
    (hu : ConvexOn ℝ domain u)
    (hsample : sample ⊆ interior domain)
    (hy : y ∈ sample)
    (hcont : ContinuousAt u y)
    (hq :
      q ∈ HasSubgradientLinearizationOnAt.GradientClusterSet
        (differentiabilitySetOn sample u) (gradient u) y) :
    SubgradientOn domain u y q := by
  let D : Set E := differentiabilitySetOn sample u
  let F : Filter E := 𝓝[D] y
  let l : Filter E := F ⊓ Filter.comap (gradient u) (𝓝 q)
  have hq_cluster : MapClusterPt q F (gradient u) := by
    simpa [D, F, HasSubgradientLinearizationOnAt.GradientClusterSet] using hq
  have hne_l : Filter.NeBot l := by
    change Filter.NeBot (F ⊓ Filter.comap (gradient u) (𝓝 q))
    exact (Filter.neBot_inf_comap_iff_map
      (f := gradient u) (F := F) (G := 𝓝 q)).2
      (by simpa [mapClusterPt_def, ClusterPt, inf_comm] using hq_cluster)
  have hxs : Filter.Tendsto id l (𝓝 y) := by
    exact Filter.tendsto_id'.2 ((inf_le_left : l ≤ F).trans nhdsWithin_le_nhds)
  have hps : Filter.Tendsto (gradient u) l (𝓝 q) := by
    exact Filter.tendsto_iff_comap.2
      (show l ≤ Filter.comap (gradient u) (𝓝 q) from inf_le_right)
  have hsub :
      ∀ᶠ w in l, SubgradientOn domain u w (gradient u w) := by
    have hmemD : ∀ᶠ w in F, w ∈ D := self_mem_nhdsWithin
    filter_upwards [hmemD.filter_mono (inf_le_left : l ≤ F)] with w hw
    rcases hw with ⟨hw_sample, hw_diff⟩
    exact ConvexOn.subgradientOn_gradient_of_differentiableAt hu (hsample hw_sample) hw_diff
  have : Filter.NeBot l := hne_l
  exact
    SubgradientOn.of_tendsto_of_continuousAt
      (s := domain) (u := u) (x := y) (p := q)
      (xs := id) (ps := gradient u) (l := l)
      (interior_subset (hsample hy)) hxs hps hcont hsub

/-- The local theorem shape corresponding to the interior-point consequence of Rockafellar 25.6.

This is not an axiom; it is a named target for the remaining finite-dimensional convex-analysis
work. In the source-cube application, `domain = Q_3` and `sample = Q_{3/2}`. -/
def RockafellarLocalSubgradientClusterDensityStatement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Prop :=
  ∀ {domain sample : Set E} {u : E → ℝ},
    IsOpen domain →
      IsOpen sample →
        sample ⊆ domain →
          ConvexOn ℝ domain u →
            LocalSubgradientClusterDensityOn domain sample u

end AleksandrovDifferentiability
