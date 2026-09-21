/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T04.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]); refactored into a
span-to-span core plus corollaries by Claude Opus 4.8 (claude-opus-4-8[1m]);
folded and turned into a `def` with an `@[simp]` apply lemma following review
by @wwylele on mathlib4 PR #40567.  After the PR was closed, restructured for
elegance by Claude Fable 5 (claude-fable-5[1m]): the quotient plumbing is now a
standalone *isometric first isomorphism theorem* (`LinearMap.rangeEquivOfInnerEq`)
about an arbitrary pair of linear maps, whose `@[simp]` apply lemma carries an
arbitrary membership proof so that every downstream proof is a short `simp`;
the span, ambient, and `gram` statements are thin corollaries.
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Isomorphisms
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences


/-! # Gram matrix rigidity

Two families of vectors in inner product spaces over `𝕜 = ℝ, ℂ` with equal
pairwise inner products are related by a linear isometry.  In finite dimension
this upgrades to a linear isometry *equivalence* of the ambient space, and the
hypothesis can be packaged as equality of `Matrix.gram` matrices.

The engine is a general fact about a pair of linear maps, an isometric
refinement of the first isomorphism theorem:

* `LinearMap.ker_eq_ker_of_inner_eq`: linear maps `S`, `T` (out of a common
  module, into two inner product spaces) with equal pullback inner products
  `⟪S x, S y⟫ = ⟪T x, T y⟫` have equal kernels, since `S x = 0` iff
  `⟪S x, S x⟫ = 0`.
* `LinearMap.rangeEquivOfInnerEq`: consequently `S x ↦ T x` descends to a
  linear isometry equivalence `range S ≃ₗᵢ range T`: both ranges are canonically
  isomorphic to the coimage `M ⧸ ker S = M ⧸ ker T` by the first isomorphism
  theorem, and the hypothesis says exactly that the two induced inner products
  on the coimage agree.

Everything else is specialization.  Applying it to the two linear-combination
maps `Finsupp.linearCombination 𝕜 φ` and `Finsupp.linearCombination 𝕜 ψ` of
families `φ`, `ψ` with equal pairwise inner products (their pullback inner
products then agree by sesquilinearity, `inner_linearCombination_eq_of_inner_eq`)
turns "equal Gram data" into an isometry of spans:

* `linearIsometryEquivSpanOfInnerEq`: a linear isometry equivalence
  `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each `φ i` to `ψ i`.
  No finiteness is assumed, and the ambient spaces may differ.
* `exists_linearIsometryEquiv_map_eq_of_inner_eq`: in a finite-dimensional
  ambient space this extends (by `LinearIsometry.extend`) to a linear isometry
  equivalence of the whole space.
* `TauCeti.Matrix.gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq`: the
  same statement packaged as a characterization of `Matrix.gram` equality.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University
  Press, 2013 — Gram matrices and factorization up to a unitary factor.
* T.-Y. Chien and S. Waldron, *A Characterization of Projective Unitary
  Equivalence of Finite Frames and Applications*, SIAM J. Discrete Math. **30**
  (2016), no. 2, 976–994, arXiv:1312.5393 — the frame-theoretic form: finite
  frames are unitarily equivalent iff their Gram matrices coincide.
-/

public section

namespace TauCeti

open scoped Topology
open scoped InnerProductSpace

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### The isometric first isomorphism theorem -/

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable (S : M →ₗ[𝕜] E) (T : M →ₗ[𝕜] F) (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜)
include h

/-- Linear maps with equal pullback inner products have equal kernels:
`S x = 0` iff `⟪S x, S x⟫ = 0` iff `⟪T x, T x⟫ = 0` iff `T x = 0`. -/
theorem ker_eq_ker_of_inner_eq : LinearMap.ker S = LinearMap.ker T := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), h x x,
    inner_self_eq_zero]

/-- **Isometric first isomorphism theorem.**  Two linear maps `S`, `T` out of a common
module with equal pullback inner products, `⟪S x, S y⟫ = ⟪T x, T y⟫`, have canonically
isometric ranges, by `S x ↦ T x`.  This is well defined because both ranges are
first-isomorphism-theorem images of the common coimage `M ⧸ ker S = M ⧸ ker T`
(`ker_eq_ker_of_inner_eq`), and isometric because the hypothesis is precisely the
statement that the two inner products induced on the coimage agree. -/
noncomputable def rangeEquivOfInnerEq : LinearMap.range S ≃ₗᵢ[𝕜] LinearMap.range T :=
  (S.quotKerEquivRange.symm.trans <| (Submodule.quotEquivOfEq _ _
      (ker_eq_ker_of_inner_eq S T h)).trans T.quotKerEquivRange).isometryOfInner fun x y => by
    -- Walk the coimage identification explicitly: `S x ↦ mkQ x ↦ mkQ x ↦ T x`.  `simp` used to
    -- close this on its own but no longer takes the `quotKerEquivRange` steps unprompted, and
    -- the destructuring below leaves the range membership in its unfolded `∃ y, S y = S x`
    -- form, which `simp only` will not match against `S x ∈ LinearMap.range S`.  Stating the
    -- step as `key`, with the membership canonical and universally quantified, sidesteps that:
    -- `rw` closes the gap up to proof irrelevance where `simp only` cannot.
    have key : ∀ (x : M) (hx : S x ∈ LinearMap.range S),
        ((S.quotKerEquivRange.symm.trans <| (Submodule.quotEquivOfEq _ _
          (ker_eq_ker_of_inner_eq S T h)).trans T.quotKerEquivRange) ⟨S x, hx⟩ : F) = T x := by
      intro x hx
      simp only [LinearEquiv.trans_apply, LinearMap.quotKerEquivRange_symm_apply_image,
        Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk]
    obtain ⟨-, x, rfl⟩ := x
    obtain ⟨-, y, rfl⟩ := y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    -- `rw [key x]` still cannot fire: assigning its membership argument would have to see
    -- through `∈ LinearMap.range S`, which `rw` does not do.  `exact` checks up to defeq.
    exact (congrArg₂ (inner 𝕜) (key x _) (key y _)).trans (h x y).symm

/-- The equivalence built from equal Gram data sends `φ i` to `ψ i`; this is the property that
characterises it, the construction itself going through linear combinations. -/
@[simp]
theorem rangeEquivOfInnerEq_apply (x : M) (hx : S x ∈ LinearMap.range S) :
    (rangeEquivOfInnerEq S T h ⟨S x, hx⟩ : F) = T x := by
  simp [rangeEquivOfInnerEq]

end LinearMap

/-! ### Families with equal pairwise inner products

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.GramMatrix`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `56f7495`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

section
variable {φ : ι → E} {ψ : ι → F} (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜)
include h

/-- For families `φ`, `ψ` with equal pairwise inner products, the maps of linear combinations
`∑ cᵢ • φ i` and `∑ cᵢ • ψ i` have equal pairwise inner products. -/
theorem inner_linearCombination_eq_of_inner_eq (c c' : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 φ c, Finsupp.linearCombination 𝕜 φ c'⟫_𝕜
      = ⟪Finsupp.linearCombination 𝕜 ψ c, Finsupp.linearCombination 𝕜 ψ c'⟫_𝕜 := by
  simp [inner_linearCombination_linearCombination, h]

/-- Families with equal pairwise inner products have linear-combination maps with equal kernels:
`∑ cᵢ • φ i = 0 ↔ ∑ cᵢ • ψ i = 0`. -/
theorem ker_linearCombination_eq_of_inner_eq :
    LinearMap.ker (Finsupp.linearCombination 𝕜 φ)
      = LinearMap.ker (Finsupp.linearCombination 𝕜 ψ) :=
  LinearMap.ker_eq_ker_of_inner_eq _ _ (inner_linearCombination_eq_of_inner_eq h)

variable (φ ψ)

/-- A linear isometry equivalence `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each
`φ i` to `ψ i`, when the families `φ`, `ψ` (in possibly different inner product spaces over `𝕜`)
have equal pairwise inner products.  It is the isometric first isomorphism theorem
`LinearMap.rangeEquivOfInnerEq` applied to the two linear-combination maps, whose ranges
are the spans.  No finiteness is required, and the ambient spaces need not coincide.

Such an isometry is determined on the spanning family `φ` (`LinearMap.eqOn_span`), hence unique;
this uniqueness is not separately formalized here. -/
noncomputable def linearIsometryEquivSpanOfInnerEq :
    (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜).symm).trans
    ((LinearMap.rangeEquivOfInnerEq _ _ (inner_linearCombination_eq_of_inner_eq h)).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)))

/-- `linearIsometryEquivSpanOfInnerEq` computes on linear combinations:
it sends `∑ cᵢ • φ i` to `∑ cᵢ • ψ i`. -/
@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply_linearCombination (c : ι →₀ 𝕜)
    (hc : Finsupp.linearCombination 𝕜 φ c ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨Finsupp.linearCombination 𝕜 φ c, hc⟩ : F)
      = Finsupp.linearCombination 𝕜 ψ c := by
  simp [linearIsometryEquivSpanOfInnerEq]

/-- `linearIsometryEquivSpanOfInnerEq` sends each generator `φ i` to `ψ i`: the
`c = Finsupp.single i 1` case of
`linearIsometryEquivSpanOfInnerEq_apply_linearCombination`. -/
@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply (i : ι)
    (hi : φ i ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨φ i, hi⟩ : F) = ψ i := by
  simpa using linearIsometryEquivSpanOfInnerEq_apply_linearCombination φ ψ h
    (Finsupp.single i 1) (by simpa using Submodule.subset_span (Set.mem_range_self (f := φ) i))

end

/-- If two families `φ ψ : ι → E` in a finite-dimensional inner product space have equal
pairwise inner products, then there is a linear isometry equivalence `W` of `E` with
`W (φ i) = ψ i` for every `i`.  The span-to-span equivalence
`linearIsometryEquivSpanOfInnerEq` is extended to `E` by `LinearIsometry.extend` and
bundled as an equivalence by finite dimensionality. -/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  let L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] E :=
    (Submodule.span 𝕜 (Set.range ψ)).subtypeₗᵢ.comp
      (linearIsometryEquivSpanOfInnerEq φ ψ h).toLinearIsometry
  exact ⟨L.extend.toLinearIsometryEquiv rfl, fun i => by
    simpa [L] using L.extend_apply ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩⟩

/-- **Rigid-motion rigidity.** Two families in a finite-dimensional real inner product space
with equal pairwise *distances* differ by a rigid motion: there is a linear isometry
equivalence `W` and a translation `b` with `ψ i = W (φ i) + b` for every `i`.

This is the affine companion of `exists_linearIsometryEquiv_map_eq_of_inner_eq`, which needs
equal inner products.  Recentring at a base index turns equal distances into equal inner
products by polarisation, and the linear statement then supplies `W`.

It is the classical fact underlying multidimensional scaling: a configuration is determined by
its pairwise distances only up to a rigid motion, so a distance-based embedding can be compared
with a target configuration only after alignment. -/
theorem exists_rigidMotion_of_dist_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} [Nonempty ι] {φ ψ : ι → F}
    (h : ∀ i j, ‖φ i - φ j‖ = ‖ψ i - ψ j‖) :
    ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ψ i = W (φ i) + b := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set φ' : ι → F := fun i => φ i - φ i₀ with hφ'
  set ψ' : ι → F := fun i => ψ i - ψ i₀ with hψ'
  have hnorm : ∀ i, ‖φ' i‖ = ‖ψ' i‖ := fun i => h i i₀
  have hdiff : ∀ i j, ‖φ' i - φ' j‖ = ‖ψ' i - ψ' j‖ := by
    intro i j
    have hφsub : φ' i - φ' j = φ i - φ j := by simp only [hφ']; abel
    have hψsub : ψ' i - ψ' j = ψ i - ψ j := by simp only [hψ']; abel
    rw [hφsub, hψsub]
    exact h i j
  -- polarisation turns equal distances into equal inner products
  have hinner : ∀ i j, ⟪φ' i, φ' j⟫_ℝ = ⟪ψ' i, ψ' j⟫_ℝ := by
    intro i j
    have hφ := norm_sub_sq_real (φ' i) (φ' j)
    have hψ := norm_sub_sq_real (ψ' i) (ψ' j)
    have h1 := hnorm i
    have h2 := hnorm j
    have h3 := hdiff i j
    rw [h1, h2, h3] at hφ
    linarith [hφ, hψ]
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq (𝕜 := ℝ) hinner
  refine ⟨W, ψ i₀ - W (φ i₀), fun i => ?_⟩
  have hWi := hW i
  simp only [hφ', hψ'] at hWi
  rw [map_sub] at hWi
  have hfinal : ψ i = W (φ i) - W (φ i₀) + ψ i₀ := by
    have := congrArg (fun v => v + ψ i₀) hWi
    simpa using this.symm
  rw [hfinal]
  abel

/-- **Approximate rigid-motion rigidity.** If the pairwise distances of a sequence of finite
configurations converge to those of a target, then eventually each configuration is carried
arbitrarily close to the target by some rigid motion.

This is the asymptotic form of `exists_rigidMotion_of_dist_eq`, and it is what a distance-based
consistency statement needs: multidimensional scaling determines a configuration only up to a
rigid motion, so convergence of the estimates can be asserted only after alignment.

The proof is a compactness argument and uses **no spectral hypothesis**.  Recentring at a base
index leaves all distances unchanged and bounds the configurations; a bounded sequence in a
finite-dimensional space has a convergent subsequence; the limit has exactly the target's
pairwise distances; and the exact statement then supplies a rigid motion, which by continuity
serves the whole tail. -/
theorem eventually_exists_rigidMotion_dist_lt
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} [Finite ι] [Nonempty ι] {φ : ℕ → ι → F} {ψ : ι → F}
    (h : ∀ i j, Filter.Tendsto (fun u => ‖φ u i - φ u j‖) Filter.atTop (𝓝 ‖ψ i - ψ j‖)) :
    ∀ ε > 0, ∀ᶠ u in Filter.atTop,
      ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ u i) + b - ψ i‖ < ε := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set φ' : ℕ → ι → F := fun u i => φ u i - φ u i₀ with hφ'
  have hsub : ∀ u i j, φ' u i - φ' u j = φ u i - φ u j := by
    intro u i j; simp only [hφ']; abel
  have hdist' : ∀ i j, Filter.Tendsto (fun u => ‖φ' u i - φ' u j‖) Filter.atTop
      (𝓝 ‖ψ i - ψ j‖) := fun i j => (h i j).congr fun u => by rw [hsub]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨σ, hσmono, hσ⟩ := Filter.extraction_of_frequently_atTop hcon
  -- each recentred coordinate is a bounded sequence
  have hbdd : ∀ i, ∃ R : ℝ, ∀ k, ‖φ' (σ k) i‖ ≤ R := by
    intro i
    have hlim : Filter.Tendsto (fun u => ‖φ' u i‖) Filter.atTop (𝓝 ‖ψ i - ψ i₀‖) := by
      refine (hdist' i i₀).congr fun u => ?_
      congr 1
      simp only [hφ']
      abel
    have hb := Metric.isBounded_range_of_tendsto _ (hlim.comp hσmono.tendsto_atTop)
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    refine ⟨R, fun k => ?_⟩
    have := hR (Set.mem_range_self k)
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (mem_closedBall_zero_iff.mp this)
  choose R hR using hbdd
  set Rmax : ℝ := (Finset.univ.sup' Finset.univ_nonempty R) with hRmax
  have hRle : ∀ k i, ‖φ' (σ k) i‖ ≤ Rmax :=
    fun k i => le_trans (hR i k) (Finset.le_sup' R (Finset.mem_univ i))
  -- so the configurations lie in a bounded set of the finite-dimensional space `ι → F`
  have hmem : ∀ k, φ' (σ k) ∈ Metric.closedBall (0 : ι → F) Rmax := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg]
    · exact fun i => hRle k i
    · exact le_trans (norm_nonneg _) (hRle 0 i₀)
  obtain ⟨χ, -, τ, hτmono, hτ⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  -- the limit configuration has exactly the target's pairwise distances
  have hχ : ∀ i j, ‖χ i - χ j‖ = ‖ψ i - ψ j‖ := by
    intro i j
    have hconv : Filter.Tendsto (fun k => ‖φ' (σ (τ k)) i - φ' (σ (τ k)) j‖) Filter.atTop
        (𝓝 ‖χ i - χ j‖) := by
      have hi : Filter.Tendsto (fun k => φ' (σ (τ k)) i) Filter.atTop (𝓝 (χ i)) :=
        (continuous_apply i).continuousAt.tendsto.comp hτ
      have hj : Filter.Tendsto (fun k => φ' (σ (τ k)) j) Filter.atTop (𝓝 (χ j)) :=
        (continuous_apply j).continuousAt.tendsto.comp hτ
      exact (hi.sub hj).norm
    have hconv' : Filter.Tendsto (fun k => ‖φ' (σ (τ k)) i - φ' (σ (τ k)) j‖) Filter.atTop
        (𝓝 ‖ψ i - ψ j‖) :=
      ((hdist' i j).comp hσmono.tendsto_atTop).comp hτmono.tendsto_atTop
    exact tendsto_nhds_unique hconv hconv'
  obtain ⟨W, b, hWb⟩ := exists_rigidMotion_of_dist_eq (φ := χ) (ψ := ψ) hχ
  -- for large `k` the same rigid motion works, contradicting the choice of `σ`
  have hgo : Filter.Tendsto (fun k => ‖φ' (σ (τ k)) - χ‖) Filter.atTop (𝓝 0) := by
    have hd : Filter.Tendsto (fun k => φ' (σ (τ k)) - χ) Filter.atTop (𝓝 (0 : ι → F)) := by
      simpa using hτ.sub (tendsto_const_nhds (x := χ))
    simpa using hd.norm
  rw [Metric.tendsto_atTop] at hgo
  obtain ⟨K, hK⟩ := hgo ε hε
  have hbad := hσ (τ K)
  refine hbad ⟨W, b - W (φ (σ (τ K)) i₀), fun i => ?_⟩
  have hrw : W (φ (σ (τ K)) i) + (b - W (φ (σ (τ K)) i₀)) - ψ i
      = W (φ' (σ (τ K)) i) + b - ψ i := by
    simp only [hφ', map_sub]
    abel
  rw [hrw, hWb i]
  have hstep : W (φ' (σ (τ K)) i) + b - (W (χ i) + b) = W (φ' (σ (τ K)) i - χ i) := by
    have hms : W (φ' (σ (τ K)) i - χ i) = W (φ' (σ (τ K)) i) - W (χ i) := map_sub W _ _
    rw [hms]
    abel
  rw [hstep, LinearIsometryEquiv.norm_map]
  have hle : ‖φ' (σ (τ K)) i - χ i‖ ≤ ‖φ' (σ (τ K)) - χ‖ := by
    simpa using norm_le_pi_norm (φ' (σ (τ K)) - χ) i
  have := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  exact lt_of_le_of_lt hle this
/-- **Uniform approximate rigid-motion rigidity.** For a fixed finite index type, a fixed
tolerance `ε` and a fixed bound `D` on the diameter of the target, one `δ > 0` serves *every*
pair of configurations: if the target has diameter at most `D` and the pairwise distances agree
to within `δ`, then some rigid motion carries the estimate to within `ε` of the target.

`eventually_exists_rigidMotion_dist_lt` is the sequential form of the same fact; the uniform
form is what a *random* target needs, where a modulus that depends on the sample is of no use.
The diameter bound cannot be dropped: the hypothesis and conclusion both scale linearly under a
simultaneous rescaling of the two configurations, so `δ` must be allowed to depend on the size
of the target.

The proof is again pure compactness and uses **no spectral hypothesis**: a counterexample
sequence, recentred at a base index, is bounded in the finite-dimensional space of
configurations, so both the estimates and the targets subconverge; the two limits have equal
pairwise distances; `exists_rigidMotion_of_dist_eq` aligns them exactly; and that one rigid
motion then serves a whole tail of the counterexample sequence. -/
theorem exists_delta_forall_exists_rigidMotion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} [Finite ι] [Nonempty ι] (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ φ ψ : ι → F,
      (∀ i j, ‖ψ i - ψ j‖ ≤ D) →
      (∀ i j, |‖φ i - φ j‖ - ‖ψ i - ψ j‖| ≤ δ) →
      ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ i) + b - ψ i‖ ≤ ε := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  by_contra hcon
  push Not at hcon
  have hchoice : ∀ k : ℕ, ∃ q : (ι → F) × (ι → F),
      (∀ i j, ‖q.2 i - q.2 j‖ ≤ D) ∧
      (∀ i j, |‖q.1 i - q.1 j‖ - ‖q.2 i - q.2 j‖| ≤ 1 / ((k : ℝ) + 1)) ∧
      ∀ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∃ i, ε < ‖W (q.1 i) + b - q.2 i‖ := by
    intro k
    obtain ⟨φ, ψ, h1, h2, h3⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨(φ, ψ), h1, h2, h3⟩
  choose p hD hδ hbad using hchoice
  have hDnn : 0 ≤ D := by simpa using hD 0 i₀ i₀
  have hone : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_one hpos]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  set Φ : ℕ → ι → F := fun k i => (p k).1 i - (p k).1 i₀ with hΦ
  set Ψ : ℕ → ι → F := fun k i => (p k).2 i - (p k).2 i₀ with hΨ
  have hΦsub : ∀ k i j, Φ k i - Φ k j = (p k).1 i - (p k).1 j := by
    intro k i j; simp only [hΦ]; abel
  have hΨsub : ∀ k i j, Ψ k i - Ψ k j = (p k).2 i - (p k).2 j := by
    intro k i j; simp only [hΨ]; abel
  have hΨle : ∀ k i, ‖Ψ k i‖ ≤ D := fun k i => hD k i i₀
  have hΦle : ∀ k i, ‖Φ k i‖ ≤ D + 1 := by
    intro k i
    have h1 := abs_le.mp (hδ k i i₀)
    have h2 := hD k i i₀
    have h3 := hone k
    simp only [hΦ]
    linarith [h1.1, h1.2]
  -- both counterexample families are bounded in the finite-dimensional configuration space
  have hmemΦ : ∀ k, Φ k ∈ Metric.closedBall (0 : ι → F) (D + 1) := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg]
    · exact fun i => hΦle k i
    · linarith
  obtain ⟨χ, -, σ, hσmono, hσ⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmemΦ
  have hmemΨ : ∀ k, Ψ (σ k) ∈ Metric.closedBall (0 : ι → F) D := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hDnn]
    exact fun i => hΨle (σ k) i
  obtain ⟨ζ, -, τ, hτmono, hτ⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmemΨ
  have hΦlim : Filter.Tendsto (fun k => Φ (σ (τ k))) Filter.atTop (𝓝 χ) :=
    hσ.comp hτmono.tendsto_atTop
  have hΨlim : Filter.Tendsto (fun k => Ψ (σ (τ k))) Filter.atTop (𝓝 ζ) := hτ
  have hσats : Filter.Tendsto (fun k => σ (τ k)) Filter.atTop Filter.atTop :=
    (hσmono.comp hτmono).tendsto_atTop
  -- the two limit configurations have exactly the same pairwise distances
  have hlim : ∀ i j, ‖χ i - χ j‖ = ‖ζ i - ζ j‖ := by
    intro i j
    have hA : Filter.Tendsto (fun k => ‖Φ (σ (τ k)) i - Φ (σ (τ k)) j‖) Filter.atTop
        (𝓝 ‖χ i - χ j‖) :=
      ((((continuous_apply i).continuousAt.tendsto.comp hΦlim).sub
        ((continuous_apply j).continuousAt.tendsto.comp hΦlim))).norm
    have hB : Filter.Tendsto (fun k => ‖Ψ (σ (τ k)) i - Ψ (σ (τ k)) j‖) Filter.atTop
        (𝓝 ‖ζ i - ζ j‖) :=
      ((((continuous_apply i).continuousAt.tendsto.comp hΨlim).sub
        ((continuous_apply j).continuousAt.tendsto.comp hΨlim))).norm
    have hg : Filter.Tendsto (fun k => 1 / ((σ (τ k) : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hσats
    have hsq : Filter.Tendsto
        (fun k => ‖Φ (σ (τ k)) i - Φ (σ (τ k)) j‖ - ‖Ψ (σ (τ k)) i - Ψ (σ (τ k)) j‖)
        Filter.atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) hg
      rw [Real.norm_eq_abs, hΦsub, hΨsub]
      exact hδ (σ (τ k)) i j
    have := tendsto_nhds_unique hsq (hA.sub hB)
    linarith [this]
  obtain ⟨W, b, hWb⟩ := exists_rigidMotion_of_dist_eq (φ := χ) (ψ := ζ) hlim
  -- for large `k` the same rigid motion aligns the counterexample, which is a contradiction
  have hgoΦ : Filter.Tendsto (fun k => ‖Φ (σ (τ k)) - χ‖) Filter.atTop (𝓝 0) := by
    have hd : Filter.Tendsto (fun k => Φ (σ (τ k)) - χ) Filter.atTop (𝓝 (0 : ι → F)) := by
      simpa using hΦlim.sub (tendsto_const_nhds (x := χ))
    simpa using hd.norm
  have hgoΨ : Filter.Tendsto (fun k => ‖Ψ (σ (τ k)) - ζ‖) Filter.atTop (𝓝 0) := by
    have hd : Filter.Tendsto (fun k => Ψ (σ (τ k)) - ζ) Filter.atTop (𝓝 (0 : ι → F)) := by
      simpa using hΨlim.sub (tendsto_const_nhds (x := ζ))
    simpa using hd.norm
  rw [Metric.tendsto_atTop] at hgoΦ hgoΨ
  obtain ⟨K₁, hK₁⟩ := hgoΦ (ε / 2) (by linarith)
  obtain ⟨K₂, hK₂⟩ := hgoΨ (ε / 2) (by linarith)
  set K : ℕ := max K₁ K₂ with hK
  set m : ℕ := σ (τ K) with hm
  have hb1 : ‖Φ m - χ‖ < ε / 2 := by
    have := hK₁ K (le_max_left _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  have hb2 : ‖Ψ m - ζ‖ < ε / 2 := by
    have := hK₂ K (le_max_right _ _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  obtain ⟨i, hi⟩ := hbad m W (b - W ((p m).1 i₀) + (p m).2 i₀)
  have hrw : W ((p m).1 i) + (b - W ((p m).1 i₀) + (p m).2 i₀) - (p m).2 i
      = (W (Φ m i) + b) - Ψ m i := by
    simp only [hΦ, hΨ, map_sub]
    abel
  rw [hrw] at hi
  have hstep : (W (Φ m i) + b) - Ψ m i
      = W (Φ m i - χ i) + (ζ i - Ψ m i) := by
    have h1 : W (Φ m i - χ i) = W (Φ m i) - W (χ i) := map_sub W _ _
    rw [h1, hWb i]
    abel
  have hfin : ‖(W (Φ m i) + b) - Ψ m i‖ ≤ ‖Φ m i - χ i‖ + ‖ζ i - Ψ m i‖ := by
    rw [hstep]
    refine le_trans (norm_add_le _ _) ?_
    rw [LinearIsometryEquiv.norm_map]
  have hc1 : ‖Φ m i - χ i‖ ≤ ‖Φ m - χ‖ := by
    simpa using norm_le_pi_norm (Φ m - χ) i
  have hc2 : ‖ζ i - Ψ m i‖ ≤ ‖Ψ m - ζ‖ := by
    have : ‖Ψ m i - ζ i‖ ≤ ‖Ψ m - ζ‖ := by simpa using norm_le_pi_norm (Ψ m - ζ) i
    rwa [norm_sub_rev] at this
  linarith [hi, hfin, hc1, hc2, hb1, hb2]

/-! ### Alignment error and the aligned configuration

Multidimensional scaling recovers a configuration only up to a rigid motion, so the quantity a
distance-based consistency statement can control is not the uniform distance to the target but
the least uniform distance achievable after moving the estimate by a rigid motion.  That is
`alignmentError`, and `alignedConfig` is an estimate that very nearly attains it. -/

/-- The uniform tolerances achievable by carrying `φ` onto `ψ` with a rigid motion. -/
def rigidTolerances {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (ψ φ : ι → F) : Set ℝ :=
  {r : ℝ | ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ i) + b - ψ i‖ ≤ r}

/-- The **alignment error** of a configuration `φ` against a target `ψ`: the least uniform
distance to `ψ` achievable by moving `φ` with a rigid motion.  It vanishes exactly when the two
configurations are congruent, and by `exists_delta_forall_exists_rigidMotion` it is small
whenever the pairwise distances are close and the target is not too large. -/
noncomputable def alignmentError {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (ψ φ : ι → F) : ℝ :=
  sInf (rigidTolerances ψ φ)

/-- The set of rigidity tolerances is nonempty. -/
theorem rigidTolerances_nonempty {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Finite ι] [Nonempty ι] (ψ φ : ι → F) :
    (rigidTolerances ψ φ).Nonempty := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun i => ‖φ i - ψ i‖),
    LinearIsometryEquiv.refl ℝ F, 0, fun i => ?_⟩
  have hrfl : ‖(LinearIsometryEquiv.refl ℝ F) (φ i) + 0 - ψ i‖ = ‖φ i - ψ i‖ := by simp
  rw [hrfl]
  exact Finset.le_sup' (fun i => ‖φ i - ψ i‖) (Finset.mem_univ i)

/-- The set of rigidity tolerances is bounded below, so its infimum exists. -/
theorem bddBelow_rigidTolerances {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Nonempty ι] (ψ φ : ι → F) : BddBelow (rigidTolerances ψ φ) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨0, fun r hr => ?_⟩
  obtain ⟨W, b, hW⟩ := hr
  exact le_trans (norm_nonneg _) (hW i)

/-- The alignment error is nonnegative. -/
theorem alignmentError_nonneg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Nonempty ι] (ψ φ : ι → F) : 0 ≤ alignmentError ψ φ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine Real.sInf_nonneg fun r hr => ?_
  obtain ⟨W, b, hW⟩ := hr
  exact le_trans (norm_nonneg _) (hW i)

/-- Any rigid motion achieving a uniform tolerance bounds the alignment error. -/
theorem alignmentError_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Nonempty ι] {ψ φ : ι → F} {r : ℝ}
    (h : ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ i) + b - ψ i‖ ≤ r) :
    alignmentError ψ φ ≤ r :=
  csInf_le (bddBelow_rigidTolerances ψ φ) h

/-- The alignment error is approached: for every positive slack some rigid motion achieves it. -/
theorem exists_rigidMotion_norm_le_alignmentError_add {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ι : Type*} [Finite ι] [Nonempty ι] (ψ φ : ι → F) {t : ℝ}
    (ht : 0 < t) :
    ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ i) + b - ψ i‖ ≤ alignmentError ψ φ + t := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (rigidTolerances_nonempty ψ φ)
    (show alignmentError ψ φ < alignmentError ψ φ + t by linarith)
  obtain ⟨W, b, hW⟩ := hr
  exact ⟨W, b, fun i => le_trans (hW i) hlt.le⟩

open Classical in
/-- The **aligned configuration**: `φ` moved by a rigid motion that comes within slack `t` of
the alignment error, and `φ` itself in the degenerate case where no such motion exists (which
`exists_rigidMotion_norm_le_alignmentError_add` rules out for `0 < t`).

This is the object a consistency statement can compare with the target *without* quantifying
the alignment inside the probability: the motion is chosen sample by sample, so the statement
"the aligned estimate converges to the target" needs no external alignment sequence. -/
noncomputable def alignedConfig {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} (ψ φ : ι → F) (t : ℝ) : ι → F :=
  if h : ∃ (W : F ≃ₗᵢ[ℝ] F) (b : F), ∀ i, ‖W (φ i) + b - ψ i‖ ≤ alignmentError ψ φ + t
    then fun i => h.choose (φ i) + h.choose_spec.choose
    else φ

/-- The defining property of `alignedConfig`. -/
theorem norm_alignedConfig_sub_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Finite ι] [Nonempty ι] (ψ φ : ι → F) {t : ℝ} (ht : 0 < t) (i : ι) :
    ‖alignedConfig ψ φ t i - ψ i‖ ≤ alignmentError ψ φ + t := by
  classical
  have h := exists_rigidMotion_norm_le_alignmentError_add ψ φ ht
  unfold alignedConfig
  split
  · rename_i h'
    exact h'.choose_spec.choose_spec i
  · rename_i h'
    exact absurd h h'

/-- The `dist` form of `norm_alignedConfig_sub_le`. -/
theorem dist_alignedConfig_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Finite ι] [Nonempty ι] (ψ φ : ι → F) {t : ℝ} (ht : 0 < t) (i : ι) :
    dist (alignedConfig ψ φ t i) (ψ i) ≤ alignmentError ψ φ + t := by
  rw [dist_eq_norm]
  exact norm_alignedConfig_sub_le ψ φ ht i

/-- **Uniform approximate rigidity, alignment-error form.** One `δ` serves every pair: pairwise
distances within `δ` of a target of diameter at most `D` force the alignment error below `ε`.

This is the shape a convergence-in-probability argument consumes, because `δ` does not depend
on the sample. -/
theorem exists_delta_alignmentError_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type*} [Finite ι] [Nonempty ι]
    (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ φ ψ : ι → F,
      (∀ i j, ‖ψ i - ψ j‖ ≤ D) →
      (∀ i j, |‖φ i - φ j‖ - ‖ψ i - ψ j‖| ≤ δ) →
      alignmentError ψ φ ≤ ε := by
  obtain ⟨δ, hδpos, h⟩ := exists_delta_forall_exists_rigidMotion (F := F) (ι := ι) D hε
  exact ⟨δ, hδpos, fun φ ψ h1 h2 => alignmentError_le (h φ ψ h1 h2)⟩


namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro hg
    exact exists_linearIsometryEquiv_map_eq_of_inner_eq fun i j => by
      simpa using congrFun₂ hg i j
  · rintro ⟨W, hW⟩
    ext i j
    simp [gram_apply, ← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix

section CoordinateFamily

variable {d : ℕ}

/-- The linear map `EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E` sending the `j`-th standard
basis vector to `v j` (extended linearly): `x ↦ ∑ j, x j • v j`. -/
noncomputable def familyMap (v : Fin d → E) : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
  (Fintype.linearCombination 𝕜 v).comp (WithLp.linearEquiv 2 𝕜 (Fin d → 𝕜)).toLinearMap

/-- The family map, unfolded to its expansion in the family. -/
@[simp] theorem familyMap_apply (v : Fin d → E) (x : EuclideanSpace 𝕜 (Fin d)) :
    familyMap v x = ∑ i, x i • v i := by
  rw [familyMap, LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

/-- The coordinate map of an orthonormal family preserves inner products. -/
theorem familyMap_inner_map_map {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x y : EuclideanSpace 𝕜 (Fin d)) :
    ⟪familyMap v x, familyMap v y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  rw [familyMap_apply, familyMap_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i i, ite_eq_left rfl, mul_one,
      RCLike.inner_apply]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i j,
      ite_eq_right (Ne.symm hji), mul_zero, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The bundled coordinate isometry `EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E` of an
orthonormal family `v`, sending `eⱼ ↦ vⱼ`. -/
noncomputable def familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E :=
  (familyMap v).isometryOfInner (familyMap_inner_map_map hv)

/-- The bundled isometry acts as the family map. -/
@[simp] theorem familyIsometry_apply {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) : familyIsometry hv x = ∑ i, x i • v i := by
  rw [familyIsometry, LinearMap.coe_isometryOfInner, familyMap_apply]

/-- It sends the `k`-th standard basis vector to `v k`. -/
@[simp] theorem familyIsometry_single {v : Fin d → E} (hv : Orthonormal 𝕜 v) (k : Fin d) :
    familyIsometry hv (EuclideanSpace.single k 1) = v k := by
  rw [familyIsometry_apply]
  rw [Finset.sum_eq_single k]
  · rw [PiLp.single_apply, ite_eq_left rfl, one_smul]
  · intro i _ hik; rw [PiLp.single_apply, ite_eq_right hik, zero_smul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

end CoordinateFamily

end TauCeti
