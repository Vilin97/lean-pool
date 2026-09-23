/-
Copyright (c) 2026 Lasse Rempe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lasse Rempe
-/

module

public import LeanPool.ExpChaotic.Covering
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Topology.UniformSpace.OfCompactT2

/-!
# Spherical non-equicontinuity and non-normality

Iterates map the plane to the sphere. Two target values obstruct equicontinuity
and locally uniform spherical subsequential limits.

Part of Lasse Rempe's formalisation of Shen and Rempe-Gillen's exponential-map paper,
with generative AI assistance including Copilot, Claude, and particularly ChatGPT.
The initial proof architecture uses John Harrison's HOL Light formalisation.
See `LeanPool.ExpChaotic` for attribution and the upstream source.
-/

@[expose] public section

open Function Filter Set Metric
open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-! ## Spherical non-equicontinuity

The domain is `ℂ` with its usual Euclidean topology. The codomain is `OnePoint ℂ`
with the canonical compact Hausdorff uniformity, identified below with the metric
unit sphere by a uniform equivalence. Equicontinuity uses mathlib's standard
`EquicontinuousAt` definition. The iterates remain defined only on the plane.
-/

/-- Every sufficiently late iterate of a nonempty open set contains both `1` and `2`. -/
theorem eventually_hits_one_and_two {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ z ∈ U, expIterate n z = 1) ∧ (∃ z ∈ U, expIterate n z = 2) := by
  obtain ⟨N₁, h₁⟩ := eventually_hits_nonzero hU hUne (w := 1) (by norm_num)
  obtain ⟨N₂, h₂⟩ := eventually_hits_nonzero hU hUne (w := 2) (by norm_num)
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_trans (le_max_left _ _) hn), h₂ n (le_trans (le_max_right _ _) hn)⟩⟩

/-- The two-target obstruction to equicontinuity, for any separated uniform target
and any target map distinguishing `1` and `2`. The domain is the Euclidean plane. -/
theorem not_equicontinuousAt_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hq : q 1 ≠ q 2) (z : ℂ) :
    ¬ EquicontinuousAt (fun n w => q (expIterate n w)) z := by
  intro h
  apply hq
  -- Equicontinuity would force the two distinct target values into every entourage.
  apply eq_of_uniformity
  intro W hW
  obtain ⟨V, hV, hpair⟩ := equicontinuousAt_iff_pair.mp h W hW
  obtain ⟨U, hUV, hU, hxU⟩ := _root_.mem_nhds_iff.mp hV
  -- At a common sufficiently late time, points of this small neighborhood hit both targets.
  obtain ⟨N, hN⟩ := eventually_hits_one_and_two hU ⟨z, hxU⟩
  obtain ⟨⟨a, ha, h₁⟩, ⟨b, hb, h₂⟩⟩ := hN N le_rfl
  have hab := hpair a (hUV ha) b (hUV hb) N
  simpa only [h₁, h₂] using hab

/-- The Riemann sphere, represented as the one-point compactification of `ℂ`. -/
abbrev RiemannSphere := OnePoint ℂ

/-- The canonical uniform structure on the compact Hausdorff Riemann sphere. -/
instance riemannSphereUniformSpace : UniformSpace RiemannSphere :=
  uniformSpaceOfCompactR1

/-- A checked identification with the ordinary metric unit sphere in `ℝ³`.
Both directions are uniformly continuous by compactness. -/
def riemannSphereUniformEquivUnitSphere :
    RiemannSphere ≃ᵤ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let e : RiemannSphere ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  exact
    { e.toEquiv with
      uniformContinuous_toFun := CompactSpace.uniformContinuous_of_continuous e.continuous
      uniformContinuous_invFun := CompactSpace.uniformContinuous_of_continuous e.symm.continuous }

/-- The exponential iterates from the Euclidean plane to the Riemann sphere. -/
def sphericalExpIterate (n : ℕ) (z : ℂ) : RiemannSphere :=
  (expIterate n z : OnePoint ℂ)

/-- The exponential iterates fail to be spherically equicontinuous at every finite point. -/
theorem not_equicontinuousAt_sphericalExpIterate (z : ℂ) :
    ¬ EquicontinuousAt sphericalExpIterate z := by
  apply not_equicontinuousAt_expIterate_comp
    (q := fun w : ℂ => (w : OnePoint ℂ)) _ z
  exact fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)

/-- The same non-equicontinuity statement with the ordinary metric sphere as codomain. -/
theorem not_equicontinuousAt_unitSphereExpIterate (z : ℂ) :
    ¬ EquicontinuousAt
      (fun n w => riemannSphereUniformEquivUnitSphere (sphericalExpIterate n w)) z := by
  apply not_equicontinuousAt_expIterate_comp
    (q := fun w : ℂ => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)) _ z
  intro h
  exact (by norm_num : (1 : ℂ) ≠ 2)
    (OnePoint.coe_injective (riemannSphereUniformEquivUnitSphere.injective h))

/-! ## No locally uniform subsequential limits

For a continuous map into any separated uniform space distinguishing `1` and `2`,
the corresponding iterates have no locally uniform limit along an increasing subsequence
on a nonempty open set. In particular, this applies to the spherical uniformity and
allows arbitrary sphere-valued limit functions, including functions taking the value infinity.
-/

/-- Eventual point covering obstructs all locally uniform subsequential limits in any
separated uniform target, provided the continuous target map distinguishes `1` and `2`. -/
theorem not_tendstoLocallyUniformlyOn_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → Y) :
    ¬ TendstoLocallyUniformlyOn (fun n z => q (expIterate (φ n) z)) g atTop U := by
  intro hlim
  obtain ⟨x, hx⟩ := hUne
  have hg : ContinuousOn g U := hlim.continuousOn
    (Filter.Eventually.of_forall (fun n =>
      (hqcont.comp (continuous_expIterate (φ n))).continuousOn)).frequently
  -- Every nonzero target would have to equal the same limit value at x.
  have hvalue (w : ℂ) (hw : w ≠ 0) : g x = q w := by
    apply eq_of_uniformity
    intro E hE
    obtain ⟨V, hV, hVV⟩ := comp_mem_uniformity_sets hE
    obtain ⟨T, hT, hconv⟩ := hlim V hV x hx
    have hclose : ∀ᶠ z in 𝓝[U] x, (g x, g z) ∈ V :=
      Uniform.continuousWithinAt_iff'_right.mp (hg x hx) hV
    rw [hU.nhdsWithin_eq hx] at hT hclose
    obtain ⟨W, hWsub, hWopen, hxW⟩ :=
      _root_.mem_nhds_iff.mp (inter_mem hT hclose)
    obtain ⟨N, hN⟩ := eventually_hits_nonzero hWopen ⟨x, hxW⟩ hw
    obtain ⟨n, hnconv, hnlarge⟩ :=
      (hconv.and (hφ.tendsto_atTop.eventually (eventually_ge_atTop N))).exists
    obtain ⟨z, hz, hzw⟩ := hN (φ n) hnlarge
    apply hVV
    apply SetRel.prodMk_mem_comp (hWsub hz).2
    simpa only [hzw] using hnconv z (hWsub hz).1
  exact hq ((hvalue 1 one_ne_zero).symm.trans (hvalue 2 (by norm_num)))

/-- The two-target obstruction with the limit function defined only on its domain `U`.
The auxiliary extension in the proof serves solely to use Mathlib's ambient-domain API. -/
theorem not_tendstoLocallyUniformly_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : U → Y) :
    ¬ TendstoLocallyUniformly (fun n (z : U) => q (expIterate (φ n) z)) g atTop := by
  classical
  let g' : ℂ → Y := fun z => if h : z ∈ U then g ⟨z, h⟩ else q 1
  have hrestrict : (fun z : U => g' z) = g := by
    funext z
    simp [g', z.property]
  intro h
  apply not_tendstoLocallyUniformlyOn_expIterate_comp hqcont hq hU hUne hφ g'
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  change TendstoLocallyUniformly _ (fun z : U => g' z) atTop
  rwa [hrestrict]

/-- No increasing subsequence of exponential iterates converges locally uniformly in
the spherical uniformity on a nonempty open set, to any sphere-valued function. -/
theorem not_tendstoLocallyUniformlyOn_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → RiemannSphere) :
    ¬ TendstoLocallyUniformlyOn (fun n => sphericalExpIterate (φ n)) g atTop U := by
  apply not_tendstoLocallyUniformlyOn_expIterate_comp
    (q := fun w : ℂ => (w : OnePoint ℂ)) OnePoint.continuous_coe _ hU hUne hφ g
  exact fun h => (by norm_num : (1 : ℂ) ≠ 2) (OnePoint.coe_injective h)

/-- Sensitive dependence for maps from the plane to a metric target. The iterates themselves
remain plane-valued; `q` changes only the metric used to compare their values. -/
def HasSensitiveDependenceVia {Y : Type*} [MetricSpace Y] (q : ℂ → Y) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set ℂ, IsOpen U → U.Nonempty →
    ∃ n : ℕ, ∃ z ∈ U, ∃ w ∈ U,
      δ ≤ dist (q (expIterate n z)) (q (expIterate n w))

/-- **Corollary 4.4.** The exponential map has sensitive dependence with respect to spherical
distance, represented by the ordinary metric on the unit sphere in `ℝ³`. -/
theorem spherical_sensitive_dependence_exp :
    HasSensitiveDependenceVia
      (fun w : ℂ => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)) := by
  let q : ℂ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun w => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)
  have hq : q 1 ≠ q 2 := by
    intro h
    exact (by norm_num : (1 : ℂ) ≠ 2)
      (OnePoint.coe_injective (riemannSphereUniformEquivUnitSphere.injective h))
  refine ⟨dist (q 1) (q 2), dist_pos.mpr hq, fun U hU hUne => ?_⟩
  obtain ⟨N, hN⟩ := eventually_hits_one_and_two hU hUne
  obtain ⟨⟨z, hzU, hz⟩, ⟨w, hwU, hw⟩⟩ := hN N le_rfl
  refine ⟨N, z, hzU, w, hwU, ?_⟩
  simpa only [hz, hw, q] using le_rfl

end

end ExponentialJuliaSetMisiurewicz
