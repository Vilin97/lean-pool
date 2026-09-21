/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The Cayley transform

This file constructs the bounded Cayley transform of a possibly unbounded self-adjoint operator.
The key point is that `A + iI`, regarded as a map from the domain of `A`, is bijective. Its inverse
can therefore be composed with `A - iI`, and the resulting everywhere-defined linear map is an
isometry, hence continuous.
-/

open scoped LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private def plusI (A : E →ₗ.[ℂ] E) : A.domain →ₗ[ℂ] E :=
  A.toFun + Complex.I • A.domain.subtype

private def minusI (A : E →ₗ.[ℂ] E) : A.domain →ₗ[ℂ] E :=
  A.toFun - Complex.I • A.domain.subtype

private theorem formalSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact h

private theorem inner_apply_self_im (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : (inner ℂ (A x) (x : E)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [inner_conj_symm]
  exact (formalSelfAdjoint A hA x x).symm

private theorem plusI_norm_sq (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) :
    ‖plusI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  change ‖A x + Complex.I • (x : E)‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ)]
  have hcross : RCLike.re (Complex.I * inner ℂ (A x) (x : E)) = 0 := by
    change (Complex.I * inner ℂ (A x) (x : E)).re = 0
    rw [Complex.I_mul_re, inner_apply_self_im A hA x, neg_zero]
  rw [inner_smul_right, hcross, mul_zero, add_zero, norm_smul, Complex.norm_I, one_mul]

private theorem minusI_norm_sq (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) :
    ‖minusI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  change ‖A x - Complex.I • (x : E)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hcross : RCLike.re (Complex.I * inner ℂ (A x) (x : E)) = 0 := by
    change (Complex.I * inner ℂ (A x) (x : E)).re = 0
    rw [Complex.I_mul_re, inner_apply_self_im A hA x, neg_zero]
  rw [inner_smul_right, hcross, mul_zero, sub_zero, norm_smul, Complex.norm_I, one_mul]

private theorem norm_le_plusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : ‖(x : E)‖ ≤ ‖plusI A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [plusI_norm_sq A hA]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem norm_le_minusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : ‖(x : E)‖ ≤ ‖minusI A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [minusI_norm_sq A hA]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem plusI_injective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Injective (plusI A) := by
  intro x y hxy
  have hzero : plusI A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnorm : ‖((x - y : A.domain) : E)‖ ≤ 0 := by
    simpa only [hzero, norm_zero] using norm_le_plusI A hA (x - y)
  have hxy0 : (x - y : A.domain) = 0 := by
    apply Subtype.ext
    apply norm_eq_zero.mp
    exact le_antisymm hnorm (norm_nonneg _)
  exact sub_eq_zero.mp hxy0

private theorem isClosed_range_plusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    IsClosed ((LinearMap.range (plusI A) : Submodule ℂ E) : Set E) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y y₀ hy hylim
  choose x hx using hy
  have hyCauchy : CauchySeq y := hylim.cauchySeq
  have hdist (m n : ℕ) :
      dist ((x m : A.domain) : E) ((x n : A.domain) : E) ≤ dist (y m) (y n) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(((x m - x n : A.domain) : E))‖ ≤ ‖plusI A (x m - x n)‖ :=
        norm_le_plusI A hA (x m - x n)
      _ = ‖y m - y n‖ := by rw [map_sub, hx m, hx n]
  have hxCauchy : CauchySeq (fun n => ((x n : A.domain) : E)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyCauchy ε hε
    exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
  obtain ⟨x₀, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hIlim :
      Filter.Tendsto (fun n => Complex.I • ((x n : A.domain) : E)) Filter.atTop
        (nhds (Complex.I • x₀)) :=
    tendsto_const_nhds.smul hxlim
  have hAlim : Filter.Tendsto (fun n => A (x n)) Filter.atTop
      (nhds (y₀ - Complex.I • x₀)) := by
    have heq : (fun n => A (x n)) =
        (fun n => y n - Complex.I • ((x n : A.domain) : E)) := by
      funext n
      rw [← hx n]
      change A (x n) = (A (x n) + Complex.I • ((x n : A.domain) : E)) -
        Complex.I • ((x n : A.domain) : E)
      rw [add_sub_cancel_right]
    rw [heq]
    exact hylim.sub hIlim
  have hgraph : (x₀, y₀ - Complex.I • x₀) ∈ A.graph := by
    apply hA.isClosed.mem_of_tendsto (hxlim.prodMk_nhds hAlim)
    exact Filter.Eventually.of_forall fun n => A.mem_graph (x n)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨x₀', hx₀', hAx₀'⟩ := hgraph
  refine ⟨x₀', ?_⟩
  change A x₀' + Complex.I • (x₀' : E) = y₀
  rw [hAx₀', hx₀', sub_add_cancel]

private theorem orthogonal_range_plusI_eq_bot (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : (LinearMap.range (plusI A))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyOrth := (LinearMap.range (plusI A)).mem_orthogonal' y |>.mp hy
  have hwitness (x : A.domain) :
      inner ℂ (Complex.I • y) (x : E) = inner ℂ y (A x) := by
    have hzero := hyOrth (plusI A x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    change inner ℂ y (A x + Complex.I • (x : E)) = 0 at hzero
    rw [inner_add_right, inner_smul_right] at hzero
    rw [inner_smul_left, Complex.conj_I]
    linear_combination -hzero
  have hyAdj : y ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨Complex.I • y, hwitness⟩
  have hyDom : y ∈ A.domain := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hA]
    exact hyAdj
  let yDom : A.domain := ⟨y, hyDom⟩
  have hAy : A yDom = Complex.I • y := by
    apply hA.dense_domain.eq_of_inner_left ℂ
    intro x hx
    let xDom : A.domain := ⟨x, hx⟩
    calc
      inner ℂ (A yDom) x = inner ℂ y (A xDom) := formalSelfAdjoint A hA yDom xDom
      _ = inner ℂ (Complex.I • y) x := (hwitness xDom).symm
  have hminus : minusI A yDom = 0 := by
    change A yDom - Complex.I • y = 0
    rw [hAy, sub_self]
  have hynorm : ‖y‖ ≤ 0 := by
    simpa only [hminus, norm_zero] using norm_le_minusI A hA yDom
  exact norm_eq_zero.mp (le_antisymm hynorm (norm_nonneg _))

private theorem plusI_surjective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (plusI A) := by
  let K : Submodule ℂ E := LinearMap.range (plusI A)
  have hclosed : IsClosed (K : Set E) := isClosed_range_plusI A hA
  have horth : Kᗮ = ⊥ := orthogonal_range_plusI_eq_bot A hA
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  have htop : K = ⊤ := by
    calc
      K = K.topologicalClosure := hclosed.submodule_topologicalClosure_eq.symm
      _ = ⊤ := hclosure
  intro y
  apply LinearMap.mem_range.mp
  change y ∈ K
  rw [htop]
  exact Submodule.mem_top

private theorem isClosed_range_minusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    IsClosed ((LinearMap.range (minusI A) : Submodule ℂ E) : Set E) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y y₀ hy hylim
  choose x hx using hy
  have hyCauchy : CauchySeq y := hylim.cauchySeq
  have hdist (m n : ℕ) :
      dist ((x m : A.domain) : E) ((x n : A.domain) : E) ≤ dist (y m) (y n) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(((x m - x n : A.domain) : E))‖ ≤ ‖minusI A (x m - x n)‖ :=
        norm_le_minusI A hA (x m - x n)
      _ = ‖y m - y n‖ := by rw [map_sub, hx m, hx n]
  have hxCauchy : CauchySeq (fun n => ((x n : A.domain) : E)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyCauchy ε hε
    exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
  obtain ⟨x₀, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hIlim :
      Filter.Tendsto (fun n => Complex.I • ((x n : A.domain) : E)) Filter.atTop
        (nhds (Complex.I • x₀)) :=
    tendsto_const_nhds.smul hxlim
  have hAlim : Filter.Tendsto (fun n => A (x n)) Filter.atTop
      (nhds (y₀ + Complex.I • x₀)) := by
    have heq : (fun n => A (x n)) =
        (fun n => y n + Complex.I • ((x n : A.domain) : E)) := by
      funext n
      rw [← hx n]
      change A (x n) = (A (x n) - Complex.I • ((x n : A.domain) : E)) +
        Complex.I • ((x n : A.domain) : E)
      rw [sub_add_cancel]
    rw [heq]
    exact hylim.add hIlim
  have hgraph : (x₀, y₀ + Complex.I • x₀) ∈ A.graph := by
    apply hA.isClosed.mem_of_tendsto (hxlim.prodMk_nhds hAlim)
    exact Filter.Eventually.of_forall fun n => A.mem_graph (x n)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨x₀', hx₀', hAx₀'⟩ := hgraph
  refine ⟨x₀', ?_⟩
  change A x₀' - Complex.I • (x₀' : E) = y₀
  rw [hAx₀', hx₀', add_sub_cancel_right]

private theorem orthogonal_range_minusI_eq_bot (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : (LinearMap.range (minusI A))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyOrth := (LinearMap.range (minusI A)).mem_orthogonal' y |>.mp hy
  have hwitness (x : A.domain) :
      inner ℂ ((-Complex.I) • y) (x : E) = inner ℂ y (A x) := by
    have hzero := hyOrth (minusI A x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    change inner ℂ y (A x - Complex.I • (x : E)) = 0 at hzero
    rw [inner_sub_right, inner_smul_right] at hzero
    rw [neg_smul, inner_neg_left, inner_smul_left, Complex.conj_I]
    linear_combination -hzero
  have hyAdj : y ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨(-Complex.I) • y, hwitness⟩
  have hyDom : y ∈ A.domain := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hA]
    exact hyAdj
  let yDom : A.domain := ⟨y, hyDom⟩
  have hAy : A yDom = (-Complex.I) • y := by
    apply hA.dense_domain.eq_of_inner_left ℂ
    intro x hx
    let xDom : A.domain := ⟨x, hx⟩
    calc
      inner ℂ (A yDom) x = inner ℂ y (A xDom) := formalSelfAdjoint A hA yDom xDom
      _ = inner ℂ ((-Complex.I) • y) x := (hwitness xDom).symm
  have hplus : plusI A yDom = 0 := by
    change A yDom + Complex.I • y = 0
    rw [hAy, neg_smul, neg_add_cancel]
  have hynorm : ‖y‖ ≤ 0 := by
    simpa only [hplus, norm_zero] using norm_le_plusI A hA yDom
  exact norm_eq_zero.mp (le_antisymm hynorm (norm_nonneg _))

private theorem minusI_surjective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (minusI A) := by
  let K : Submodule ℂ E := LinearMap.range (minusI A)
  have hclosed : IsClosed (K : Set E) := isClosed_range_minusI A hA
  have horth : Kᗮ = ⊥ := orthogonal_range_minusI_eq_bot A hA
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  have htop : K = ⊤ := by
    calc
      K = K.topologicalClosure := hclosed.submodule_topologicalClosure_eq.symm
      _ = ⊤ := hclosure
  intro y
  apply LinearMap.mem_range.mp
  change y ∈ K
  rw [htop]
  exact Submodule.mem_top

/-- For a self-adjoint operator, `A + iI` maps its domain onto the ambient space. -/
theorem add_I_surjective_of_isSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x + Complex.I • (x : E)) := by
  exact plusI_surjective A hA

/-- For a self-adjoint operator, `A - iI` maps its domain onto the ambient space. -/
theorem sub_I_surjective_of_isSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x - Complex.I • (x : E)) := by
  exact minusI_surjective A hA

private noncomputable def cayleyLinearMap (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : E →ₗ[ℂ] E :=
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  (minusI A).comp e.symm.toLinearMap

private theorem cayleyLinearMap_norm_le (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (y : E) : ‖cayleyLinearMap A hA y‖ ≤ 1 * ‖y‖ := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  let x : A.domain := e.symm y
  have hplus : plusI A x = y := by
    change e x = y
    exact e.apply_symm_apply y
  have hnorm : ‖minusI A x‖ = ‖plusI A x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [minusI_norm_sq A hA, plusI_norm_sq A hA]
  change ‖minusI A x‖ ≤ 1 * ‖y‖
  rw [hnorm, hplus, one_mul]

/-- The Cayley transform `(A - iI)(A + iI)⁻¹` of a self-adjoint partial linear map. -/
noncomputable def cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  (cayleyLinearMap A hA).mkContinuous 1 (cayleyLinearMap_norm_le A hA)

/-- The Cayley transform sends `(A + iI)x` to `(A - iI)x`. -/
theorem cayleyTransform_apply_plus
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (x : A.domain) :
    cayleyTransform A hA (A x + Complex.I • (x : E)) =
      A x - Complex.I • (x : E) := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  change minusI A (e.symm (plusI A x)) = minusI A x
  change minusI A (e.symm (e x)) = minusI A x
  rw [e.symm_apply_apply]

/-- The Cayley transform preserves the norm. -/
theorem norm_cayleyTransform (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (y : E) : ‖cayleyTransform A hA y‖ = ‖y‖ := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  let x : A.domain := e.symm y
  have hplus : plusI A x = y := by
    change e x = y
    exact e.apply_symm_apply y
  have hnorm : ‖minusI A x‖ = ‖plusI A x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [minusI_norm_sq A hA, plusI_norm_sq A hA]
  change ‖minusI A x‖ = ‖y‖
  rw [hnorm, hplus]
