/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.FunctionSpace
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IdentityPrinciple
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyBounded

/-!
# Montel's and Vitali's theorems

A family of holomorphic maps which is bounded uniformly on each compact subset of its domain is
equicontinuous. For finite-dimensional targets it has compact closure in the compact-open
topology. Compactness is supplied by Mathlib's Arzelà–Ascoli theorem. For uniformly bounded
sequences, a subsequence theorem is also provided on arbitrary finite-dimensional complex source
spaces. Vitali convergence follows from compactness and the identity theorem: pointwise
convergence on a nonempty open subset determines every cluster limit uniquely.

## Main results

`equicontinuous_of_holomorphic_bounded_on_compacts` is equicontinuity of a family bounded on compact
sets. `isCompact_closure_of_holomorphic_bounded_on_compacts` is Montel's theorem for
finite-dimensional targets. `exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto` is Vitali
convergence from pointwise convergence on a nonempty open subset.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public section

open Complex Filter Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Compact-local bounds on a holomorphic family give equicontinuity. Banach targets are allowed
here; finite dimensionality is needed only for compactness in Montel's theorem. -/
theorem equicontinuous_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens E} {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) :
    Equicontinuous (fun f : S => (f.val.val : U → F)) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds c.property)
  obtain ⟨M, hM⟩ := hb (closedBall (c : E) R) hRU (isCompact_closedBall _ _)
  let C : ℝ := 2 * max M 0 / R
  have hC : 0 ≤ C := div_nonneg (by positivity) hR.le
  refine ⟨min R (ε / (C + 1)), lt_min hR (div_pos hε (by positivity)), ?_⟩
  intro w hw f
  have hwr : dist (w : E) c < R := (lt_min_iff.mp hw).1
  have hwe : dist (w : E) c < ε / (C + 1) := (lt_min_iff.mp hw).2
  have hmaps : MapsTo (openExtension U f.val.val) (ball (c : E) R)
      (closedBall (openExtension U f.val.val c) (2 * max M 0)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖openExtension U f.val.val z - openExtension U f.val.val c‖ ≤
          ‖openExtension U f.val.val z‖ + ‖openExtension U f.val.val c‖ := norm_sub_le _ _
      _ ≤ max M 0 + max M 0 := add_le_add
        ((hM f.val f.property z (ball_subset_closedBall hz)).trans (le_max_left _ _))
        ((hM f.val f.property c (mem_closedBall_self hR.le)).trans (le_max_left _ _))
      _ = 2 * max M 0 := by ring
  have hn := dist_le_div_mul_dist_of_mapsTo_ball
    (f.val.property.differentiableOn.mono (ball_subset_closedBall.trans hRU)) hmaps hwr
  simp only [openExtension_coe] at hn
  have hlt : (C + 1) * dist (w : E) c < ε := by
    nlinarith [(lt_div_iff₀ (by positivity : 0 < C + 1)).mp hwe]
  rw [dist_comm]
  change dist (f.val.val w) (f.val.val c) < ε
  change dist (f.val.val w) (f.val.val c) ≤ C * dist (w : E) c at hn
  nlinarith [show 0 ≤ dist (w : E) (c : E) from dist_nonneg]

/-- **Montel's theorem.** A compact-locally bounded family of holomorphic maps into a
finite-dimensional complex normed space has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) := by
  let := FiniteDimensional.proper ℂ F
  let := UniformOnFun.t2Space_of_covering (β := F)
    (𝔖 := {K : Set U | IsCompact K}) (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have he : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
        (fun f : HolomorphicMap U F => (f.val : U → F))) := by
    exact (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.comp
      isUniformEmbedding_subtype_val).isClosedEmbedding
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) he
  · intro K hK
    exact (equicontinuous_of_holomorphic_bounded_on_compacts hb).equicontinuousOn K
  · intro K hK z hz
    obtain ⟨M, hM⟩ := hb {(z : E)} (singleton_subset_iff.mpr z.property) isCompact_singleton
    refine ⟨closedBall (0 : F) (max M 0), isCompact_closedBall _ _, ?_⟩
    intro f hf
    have h := (hM f hf z (mem_singleton _)).trans (le_max_left M 0)
    simpa using h

/-- **Vitali's theorem ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.4.24)** in the compact-open
function space.
A locally bounded sequence converging pointwise on a nonempty open subset of a
preconnected domain converges in the whole holomorphic-map space. -/
theorem exists_tendsto_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens E}
    (hconn : IsPreconnected (U : Set E)) (f : ℕ → HolomorphicMap U F)
    (hb : ∀ K ⊆ (U : Set E), IsCompact K → ∃ M : ℝ,
      ∀ n, ∀ z ∈ K, ‖openExtension U (f n).val z‖ ≤ M)
    {V : Set E} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (hp : ∀ z ∈ V, ∃ y : F,
      Tendsto (fun n => openExtension U (f n).val z) atTop (𝓝 y)) :
    ∃ g : HolomorphicMap U F, Tendsto f atTop (𝓝 g) := by
  have hc : IsCompact (closure (range f)) :=
    isCompact_closure_of_holomorphic_bounded_on_compacts (by
      intro K hKU hK
      obtain ⟨M, hM⟩ := hb K hKU hK
      exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩)
  have hm : ∀ᶠ n in atTop, f n ∈ closure (range f) :=
    .of_forall fun n => subset_closure (mem_range_self n)
  obtain ⟨g, _, hg⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  refine ⟨g, hc.tendsto_nhds_of_unique_mapClusterPt hm ?_⟩
  intro q _ hq
  have hvalue : ∀ (r : HolomorphicMap U F), MapClusterPt r atTop f →
      ∀ z ∈ V, ∀ y : F,
      Tendsto (fun n => openExtension U (f n).val z) atTop (𝓝 y) →
      openExtension U r.val z = y := by
    intro r hr z hz y hy
    have he := hr.continuousAt_comp
      (continuous_holomorphicMap_eval U ⟨z, hVU hz⟩).continuousAt
    obtain ⟨φ, hφ, hlim⟩ := he.tendsto_subseq
    have hy' : Tendsto (fun n => (f n).val ⟨z, hVU hz⟩) atTop (𝓝 y) := by
      simpa only [openExtension_apply U _ (hVU hz)] using hy
    simpa only [openExtension_apply U _ (hVU hz)] using
      tendsto_nhds_unique hlim (hy'.comp hφ.tendsto_atTop)
  have heq : EqOn (openExtension U q.val) (openExtension U g.val) U :=
    DifferentiableOn.eqOn_of_preconnected_of_eqOn U.isOpen hconn q.property.differentiableOn
      g.property.differentiableOn hV hne hVU (by
        intro z hz
        obtain ⟨y, hy⟩ := hp z hz
        exact (hvalue q hq z hz y hy).trans (hvalue g hg z hz y hy).symm)
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  simpa only [openExtension_coe] using heq z.property

/-- **Vitali's theorem** for holomorphic functions on a finite-dimensional complex normed space.
The limit is holomorphic and convergence is locally uniform on the whole domain.
Finite-dimensional complex targets, including scalar-valued functions, are allowed. -/
theorem exists_tendstoLocallyUniformlyOn_of_forall_exists_tendsto [FiniteDimensional ℂ F]
    {D V : Set E}
    (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℕ → E → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) D)
    (hb : ∀ K ⊆ D, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hV : IsOpen V) (hne : V.Nonempty) (hVD : V ⊆ D)
    (hp : ∀ z ∈ V, ∃ y : F, Tendsto (fun n => f n z) atTop (𝓝 y)) :
    ∃ g : E → F, DifferentiableOn ℂ g D ∧
      TendstoLocallyUniformlyOn f g atTop D := by
  let U : TopologicalSpace.Opens E := ⟨D, hD⟩
  let s : ℕ → HolomorphicMap U F := fun n =>
    ⟨⟨fun z => f n z, (hf n).continuousOn.domRestrict⟩,
      by
        apply AnalyticOnNhd.congr hD ((hf n).analyticOnNhd_of_finiteDimensional hD)
        intro z hz
        simp [openExtension, U, hz]
        rfl⟩
  have hs : ∀ n, ∀ z ∈ D, openExtension U (s n).val z = f n z := by
    intro n z hz
    exact openExtension_apply U _ hz
  obtain ⟨g, hg⟩ := exists_tendsto_of_holomorphic_bounded_on_compacts hconn s
    (by
      intro K hKD hK
      obtain ⟨M, hM⟩ := hb K hKD hK
      refine ⟨M, fun n z hz => ?_⟩
      rw [hs n z (hKD hz)]
      exact hM n z hz) hV hne hVD (by
      intro z hz
      simpa only [hs _ z (hVD hz)] using hp z hz)
  refine ⟨openExtension U g.val, g.property.differentiableOn, ?_⟩
  exact (holomorphicMap_tendsto_iff.mp hg).congr
    (fun n z hz => hs n z hz)

/-- A uniformly bounded holomorphic sequence on a finite-dimensional complex space has a locally
uniformly convergent subsequence, with holomorphic limit. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] {U : Set E} (hU : IsOpen U) {f : ℕ → E → F}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) {M : ℝ}
    (hM : ∀ n z, z ∈ U → ‖f n z‖ ≤ M) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ AnalyticOnNhd ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by
  let e := (Module.finBasis ℂ E).equivFunL
  let V : TopologicalSpace.Opens (Fin (Module.finrank ℂ E) → ℂ) :=
    ⟨e.symm ⁻¹' U, hU.preimage e.symm.continuous⟩
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  have hA (n) : AnalyticOnNhd ℂ (f n ∘ e.symm) V :=
    (hf n).comp (e.symm.toContinuousLinearMap.analyticOnNhd _) (fun _ hz => hz)
  let G (n : ℕ) : HolomorphicMap V F :=
    ⟨⟨fun z => f n (e.symm z), (hA n).continuousOn.domRestrict⟩,
      (hA n).congr V.isOpen (fun z hz => by rw [openExtension_apply V _ hz]; rfl)⟩
  have hc : IsCompact (closure (range G)) :=
    isCompact_closure_of_holomorphic_bounded_on_compacts (by
      intro K hKV _
      refine ⟨M, ?_⟩
      rintro _ ⟨n, rfl⟩ z hz
      rw [openExtension_apply V _ (hKV hz)]
      exact hM n _ (hKV hz))
  have : (uniformity C(V, F)).IsCountablyGenerated := inferInstance
  have : (uniformity (HolomorphicMap V F)).IsCountablyGenerated :=
    Filter.comap.isCountablyGenerated _ _
  have hm : ∀ᶠ n in atTop, G n ∈ closure (range G) :=
    .of_forall fun n => subset_closure (mem_range_self n)
  obtain ⟨g, _, hg⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  obtain ⟨φ, hφ, hlim⟩ := hg.tendsto_subseq
  let g' : E → F := fun z => openExtension V g.val (e z)
  have hmaps : MapsTo e U V := fun z hz => by simpa [V] using hz
  refine ⟨g', φ, hφ, g.property.comp (e.toContinuousLinearMap.analyticOnNhd U) hmaps, ?_⟩
  have hl := (holomorphicMap_tendsto_iff.mp hlim).comp e hmaps e.continuous.continuousOn
  apply hl.congr
  intro n z hz
  simp only [Function.comp_apply, openExtension_apply V _ (hmaps hz), G]
  change f (φ n) (e.symm (e z)) = f (φ n) z
  rw [e.symm_apply_apply]

end SeveralComplexVariables

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
