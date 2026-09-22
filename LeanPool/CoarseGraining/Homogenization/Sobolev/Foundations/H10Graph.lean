/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
import Mathlib.Analysis.Normed.Operator.Banach

/-! # H10Graph -/

namespace Homogenization

/-!
# The `H¹₀` graph inside the typed `L²` product

This file starts the closed-range bridge needed to remove the last Sobolev
realization hypothesis from the coarse Poincare theorem surface.

The carrier is the graph of the map

`u ↦ (u, ∇u) : H¹₀(U) → L²(U) × L²(U; ℝᵈ)`.

We immediately close this graph in the Hilbert product. The zero-trace Poincare
estimate extends to that closed graph by a closed-set argument; this is the
coercive ingredient needed for the eventual closed-range theorem for the
gradient projection.
-/

open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

@[simp] theorem H1Function.toScalarL2_zero :
    (0 : H1Function U).toScalarL2 = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_toScalarL2 (0 : H1Function U),
        MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)]
    with x hscalar hzero
  rw [hscalar, hzero]
  rfl

@[simp] theorem H1Function.gradToHilbertVectorL2_zero :
    (0 : H1Function U).gradToHilbertVectorL2 = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [H1Function.coeFn_gradToHilbertVectorL2 (0 : H1Function U),
        MeasureTheory.Lp.coeFn_zero (E := HilbertVec d) (p := (2 : ENNReal))
          (μ := volumeMeasureOn U)]
    with x hgrad hzero
  rw [hgrad, hzero]
  simp [hilbertifyVecField]

/-- The graph of the typed `H¹₀(U)` realization inside
`L²(U) × L²(U; ℝᵈ)`. -/
noncomputable def h10GraphSubmodule
    (U : Set (Vec d)) : Submodule ℝ (ScalarL2 U × HilbertVectorL2 U) where
  carrier :=
    {z | ∃ u : H10Function U,
      u.toH1Function.toScalarL2 = z.1 ∧
      u.toH1Function.gradToHilbertVectorL2 = z.2}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · change (0 : H1Function U).toScalarL2 = 0
      simp
    · change (0 : H1Function U).gradToHilbertVectorL2 = 0
      simp
  add_mem' := by
    intro z w hz hw
    rcases hz with ⟨u, huz, hgradz⟩
    rcases hw with ⟨v, hvw, hgradw⟩
    refine ⟨u + v, ?_, ?_⟩
    · calc
        (u + v).toH1Function.toScalarL2
            = (u.toH1Function + v.toH1Function).toScalarL2 := rfl
        _ = u.toH1Function.toScalarL2 + v.toH1Function.toScalarL2 :=
            H1Function.toScalarL2_add u.toH1Function v.toH1Function
        _ = (z + w).1 := by simp [huz, hvw]
    · calc
        (u + v).toH1Function.gradToHilbertVectorL2
            = (u.toH1Function + v.toH1Function).gradToHilbertVectorL2 := rfl
        _ = u.toH1Function.gradToHilbertVectorL2 +
              v.toH1Function.gradToHilbertVectorL2 :=
            H1Function.gradToHilbertVectorL2_add u.toH1Function v.toH1Function
        _ = (z + w).2 := by simp [hgradz, hgradw]
  smul_mem' := by
    intro c z hz
    rcases hz with ⟨u, huz, hgradz⟩
    refine ⟨c • u, ?_, ?_⟩
    · calc
        (c • u).toH1Function.toScalarL2
            = (c • u.toH1Function).toScalarL2 := rfl
        _ = c • u.toH1Function.toScalarL2 :=
            H1Function.toScalarL2_smul c u.toH1Function
        _ = (c • z).1 := by simp [huz]
    · calc
        (c • u).toH1Function.gradToHilbertVectorL2
            = (c • u.toH1Function).gradToHilbertVectorL2 := rfl
        _ = c • u.toH1Function.gradToHilbertVectorL2 :=
            H1Function.gradToHilbertVectorL2_smul c u.toH1Function
        _ = (c • z).2 := by simp [hgradz]

/-- An `H¹₀` function determines a point of the `H¹₀` graph. -/
theorem h10_pair_mem_h10GraphSubmodule (u : H10Function U) :
    (u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2) ∈
      h10GraphSubmodule U :=
  ⟨u, rfl, rfl⟩

/-- The closed `H¹₀` graph in the typed Hilbert product. -/
noncomputable def h10GraphClosedSubmodule
    (U : Set (Vec d)) : ClosedSubmodule ℝ (ScalarL2 U × HilbertVectorL2 U) :=
  (h10GraphSubmodule U).closure

/-- The `H¹₀` graph is contained in the weak `H¹` graph. -/
theorem h10GraphSubmodule_le_h1GraphClosedSubmodule :
    h10GraphSubmodule U ≤ (h1GraphClosedSubmodule (U := U)).toSubmodule := by
  intro z hz
  rcases hz with ⟨u, hval, hgrad⟩
  have hz' :
      z = (u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2) := by
    cases z
    simp_all
  rw [hz']
  exact h1_pair_mem_h1GraphClosedSubmodule (U := U) u.toH1Function

/-- The closed `H¹₀` graph stays inside the weak `H¹` graph. -/
theorem h10GraphClosedSubmodule_le_h1GraphClosedSubmodule :
    (h10GraphClosedSubmodule U).toSubmodule ≤
      (h1GraphClosedSubmodule (U := U)).toSubmodule := by
  exact
    (Submodule.closure_le
      (s := h10GraphSubmodule U)
      (t := h1GraphClosedSubmodule (U := U))).2
        (h10GraphSubmodule_le_h1GraphClosedSubmodule (U := U))

/-- If a Poincare estimate holds on honest `H¹₀` functions, it extends to the
closed `H¹₀` graph. -/
theorem h10GraphClosedSubmodule_norm_value_le_of_forall_h10
    {C : ℝ}
    (hC : ∀ u : H10Function U,
      ‖u.toH1Function.toScalarL2‖ ≤ C * ‖u.toH1Function.gradToHilbertVectorL2‖)
    {z : ScalarL2 U × HilbertVectorL2 U}
    (hz : z ∈ h10GraphClosedSubmodule U) :
    ‖z.1‖ ≤ C * ‖z.2‖ := by
  let K : Set (ScalarL2 U × HilbertVectorL2 U) := {z | ‖z.1‖ ≤ C * ‖z.2‖}
  have hsubset : ((h10GraphSubmodule U : Submodule ℝ
      (ScalarL2 U × HilbertVectorL2 U)) : Set (ScalarL2 U × HilbertVectorL2 U)) ⊆ K := by
    intro z hz
    rcases hz with ⟨u, hval, hgrad⟩
    simpa [K, hval, hgrad] using hC u
  have hclosed : IsClosed K := by
    have hleft : Continuous (fun z : ScalarL2 U × HilbertVectorL2 U => ‖z.1‖) :=
      continuous_norm.comp continuous_fst
    have hright : Continuous (fun z : ScalarL2 U × HilbertVectorL2 U => C * ‖z.2‖) :=
      continuous_const.mul (continuous_norm.comp continuous_snd)
    dsimp [K]
    exact isClosed_le hleft hright
  have hclosure :
      closure (((h10GraphSubmodule U : Submodule ℝ
        (ScalarL2 U × HilbertVectorL2 U)) : Set
          (ScalarL2 U × HilbertVectorL2 U))) ⊆ K :=
    closure_minimal hsubset hclosed
  exact hclosure (by simpa [h10GraphClosedSubmodule] using! hz)

/-- On bounded open convex domains, the zero-trace Poincare estimate extends
to the closed `H¹₀` graph. -/
theorem h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ScalarL2 U × HilbertVectorL2 U,
        z ∈ h10GraphClosedSubmodule U → ‖z.1‖ ≤ C * ‖z.2‖ := by
  rcases H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
      (U := U) hU with ⟨C0, hC0, hC0_bound⟩
  refine ⟨C0 * d, by positivity, ?_⟩
  intro z hz
  refine h10GraphClosedSubmodule_norm_value_le_of_forall_h10 (U := U) ?_ hz
  intro u
  have hbase :
      ‖u.toH1Function.toScalarL2‖ ≤ C0 * u.toH1Function.gradientCoordL2NormSum :=
    hC0_bound u
  have hsum :
      u.toH1Function.gradientCoordL2NormSum ≤
        d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
    calc
      u.toH1Function.gradientCoordL2NormSum ≤
          d * ‖u.toH1Function.gradToVectorL2‖ :=
        u.toH1Function.gradientCoordL2NormSum_le
      _ ≤ d * ‖u.toH1Function.gradToHilbertVectorL2‖ := by
          exact mul_le_mul_of_nonneg_left
            (H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
              (U := U) u.toH1Function)
            (Nat.cast_nonneg d)
  calc
    ‖u.toH1Function.toScalarL2‖ ≤ C0 * u.toH1Function.gradientCoordL2NormSum := hbase
    _ ≤ C0 * (d * ‖u.toH1Function.gradToHilbertVectorL2‖) := by
          exact mul_le_mul_of_nonneg_left hsum hC0
    _ = (C0 * d) * ‖u.toH1Function.gradToHilbertVectorL2‖ := by ring

/-- Curried form of `h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient`. -/
theorem h10GraphClosedSubmodule_norm_value_le_of_isOpenBoundedConvexDomain
    [NeZero d] (hU : IsOpenBoundedConvexDomain U)
    {z : ScalarL2 U × HilbertVectorL2 U}
    (hz : z ∈ h10GraphClosedSubmodule U) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖z.1‖ ≤ C * ‖z.2‖ := by
  rcases h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient
      (U := U) hU with ⟨C, hC, hbound⟩
  exact ⟨C, hC, hbound z hz⟩

/-- The closed `H¹₀` graph as a normed carrier. -/
noncomputable abbrev H10GraphClosedSpace (U : Set (Vec d)) :=
  ↥((h10GraphClosedSubmodule U).toSubmodule)

/-! ### Representative upgrade for the closed `H¹₀` graph

The missing analytic ingredient for the potential-zero-trace realization
theorem is that every point of the closed `H¹₀` graph is the pair
`(u.toScalarL2, u.gradToHilbertVectorL2)` for an actual `H¹₀` function. The
construction diagonalises the closure approximation sequence against each
graph approximant's internal smooth compactly supported approximation data
using the `approxH1` packaging from `CoerciveH10`.
-/

/-- The `L²` distance between scalar representatives of two `H¹` functions is
the scalar `L²` distance between their `toScalarL2` realisations. -/
private theorem eLpNorm_toFun_sub_eq_edist_toScalarL2
    (u v : H1Function U) :
    MeasureTheory.eLpNorm (fun x => u.toFun x - v.toFun x) 2 (volumeMeasureOn U)
      = edist u.toScalarL2 v.toScalarL2 := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_toScalarL2, v.coeFn_toScalarL2] with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- The coordinate-wise `L²` distance between weak gradients equals the
`ScalarL2` distance between `gradCoordToScalarL2` realisations. -/
private theorem eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      = edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) := by
  rw [MeasureTheory.Lp.edist_def]
  refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
  filter_upwards [u.coeFn_gradCoordToScalarL2 i, v.coeFn_gradCoordToScalarL2 i]
    with x hu hv
  simp [Pi.sub_apply, hu, hv]

/-- Coordinate-wise `L²` distance of two weak gradients is controlled by the
`HilbertVectorL2` distance of their gradient realisations. -/
private theorem eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => u.grad x i - v.grad x i) 2 (volumeMeasureOn U)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  have hrhs :
      edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2
        = MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec (u.grad x - v.grad x)) 2
            (volumeMeasureOn U) := by
    rw [MeasureTheory.Lp.edist_def]
    refine MeasureTheory.eLpNorm_congr_ae ?_
    filter_upwards
        [u.coeFn_gradToHilbertVectorL2, v.coeFn_gradToHilbertVectorL2] with x hu hv
    simp [Pi.sub_apply, hu, hv, hilbertifyVecField]
  rw [hrhs]
  refine MeasureTheory.eLpNorm_mono_ae
    ((u.grad_memL2 i).sub (v.grad_memL2 i)).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro x
  have hcoord : ‖u.grad x i - v.grad x i‖ ≤ ‖u.grad x - v.grad x‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (u.grad x - v.grad x) i
  have hVec_le_Hilbert :
      ‖u.grad x - v.grad x‖ ≤ ‖HilbertVec.ofVec (u.grad x - v.grad x)‖ :=
    HilbertVec.norm_le_norm_ofVec (u.grad x - v.grad x)
  exact hcoord.trans hVec_le_Hilbert

/-- `ScalarL2` distance on `gradCoordToScalarL2` is controlled by the
`HilbertVectorL2` distance on `gradToHilbertVectorL2`. -/
private theorem edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
    (u v : H1Function U) (i : Fin d) :
    edist (u.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i)
      ≤ edist u.gradToHilbertVectorL2 v.gradToHilbertVectorL2 := by
  rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
  exact eLpNorm_grad_coord_sub_le_edist_gradToHilbertVectorL2 u v i

/-- Every point of the closed `H¹₀` graph is realized by an honest `H¹₀`
function on bounded open convex domains. The witness is obtained by
diagonalising closure approximations against each graph approximant's internal
smooth compactly supported approximation data. -/
theorem exists_h10Function_of_mem_h10GraphClosedSubmodule
    [NeZero d] (hU : IsOpenBoundedConvexDomain U)
    {z : ScalarL2 U × HilbertVectorL2 U}
    (hz : z ∈ (h10GraphClosedSubmodule U).toSubmodule) :
    ∃ u : H10Function U,
      u.toH1Function.toScalarL2 = z.1
        ∧ u.toH1Function.gradToHilbertVectorL2 = z.2 := by
  classical
  have hUopen : IsOpen U := hU.isOpen
  -- (1) H¹ witness from the weaker graph containment.
  have hzH1 : z ∈ h1GraphClosedSubmodule (U := U) :=
    h10GraphClosedSubmodule_le_h1GraphClosedSubmodule (U := U) hz
  set v : H1Function U := toH1FunctionOfMemH1Graph (U := U) z hzH1 with v_def
  have hv_val : v.toScalarL2 = z.1 :=
    toH1FunctionOfMemH1Graph_toScalarL2 (U := U) z hzH1
  have hv_grad : v.gradToHilbertVectorL2 = z.2 :=
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2 (U := U) z hzH1
  -- (2) Closure → approximating sequence of graph points.
  have hz_closure :
      z ∈ closure ((h10GraphSubmodule U : Submodule ℝ
        (ScalarL2 U × HilbertVectorL2 U)) : Set (ScalarL2 U × HilbertVectorL2 U)) := by
    have hzSub : z ∈ (h10GraphSubmodule U).topologicalClosure := hz
    simpa [Submodule.topologicalClosure_coe] using! hzSub
  obtain ⟨ψ, hψ_mem, hψ_tendsto⟩ := mem_closure_iff_seq_limit.mp hz_closure
  choose φ hφ_val hφ_grad using hψ_mem
  -- (3) Component-wise convergence.
  have hval_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.toScalarL2) Filter.atTop
        (nhds v.toScalarL2) := by
    rw [hv_val]
    exact hψ_tendsto.fst_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_val n).symm)
  have hgrad_tendsto :
      Filter.Tendsto (fun n => (φ n).toH1Function.gradToHilbertVectorL2) Filter.atTop
        (nhds v.gradToHilbertVectorL2) := by
    rw [hv_grad]
    exact hψ_tendsto.snd_nhds.congr'
      (Filter.Eventually.of_forall fun n => (hφ_grad n).symm)
  -- (4) Convergence of `gradCoordToScalarL2 i` for each `i`, via the coord bound.
  have hgrad_edist_zero :
      Filter.Tendsto
        (fun n => edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
        Filter.atTop (nhds 0) := by
    rw [← edist_self v.gradToHilbertVectorL2]
    exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp hgrad_tendsto
  have hgradcoord_edist_zero :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => edist ((φ n).toH1Function.gradCoordToScalarL2 i)
          (v.gradCoordToScalarL2 i))
        Filter.atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ => (0 : ENNReal))
      (h := fun n =>
        edist (φ n).toH1Function.gradToHilbertVectorL2 v.gradToHilbertVectorL2)
      tendsto_const_nhds hgrad_edist_zero (fun _ => bot_le) ?_
    intro n
    exact edist_gradCoordToScalarL2_le_edist_gradToHilbertVectorL2
      (φ n).toH1Function v i
  have hgradcoord_tendsto :
      ∀ i : Fin d, Filter.Tendsto
        (fun n => (φ n).toH1Function.gradCoordToScalarL2 i) Filter.atTop
        (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine (EMetric.tendsto_nhds).mpr ?_
    intro ε hε
    exact (hgradcoord_edist_zero i).eventually (gt_mem_nhds hε)
  -- (5) Reformulate: we want convergence in `ScalarL2 U` of
  -- `(approxH1 hUopen (φ n) m).toScalarL2 → (φ n).toScalarL2`, which is
  -- directly the content of `tendsto_approxH1_toScalarL2` from `CoerciveH10`.
  have happroxH1_val :
      ∀ n : ℕ, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).toScalarL2)
        Filter.atTop (nhds (φ n).toH1Function.toScalarL2) :=
    fun n => H10Function.tendsto_approxH1_toScalarL2 hUopen (φ n)
  have happroxH1_gradcoord :
      ∀ n : ℕ, ∀ i : Fin d, Filter.Tendsto
        (fun m => (H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
        Filter.atTop (nhds ((φ n).toH1Function.gradCoordToScalarL2 i)) :=
    fun n i =>
      H10Function.tendsto_approxH1_gradCoordToScalarL2 hUopen (φ n) i
  -- (6) Diagonal: for each n, choose m n so that
  --     dist ((approxH1 (φ n) (m n)).toScalarL2) ((φ n).toScalarL2) ≤ 1/(n+1)
  --     dist ((approxH1 (φ n) (m n)).gradCoordToScalarL2 i) ((φ n).gradCoordToScalarL2 i) ≤ 1/(n+1)
  have diagonal :
      ∀ n : ℕ, ∃ m : ℕ,
        dist (H10Function.approxH1 hUopen (φ n) m).toScalarL2
            (φ n).toH1Function.toScalarL2 ≤ ((n : ℝ) + 1)⁻¹ ∧
        (∀ i : Fin d,
          dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
            ((φ n).toH1Function.gradCoordToScalarL2 i) ≤ ((n : ℝ) + 1)⁻¹) := by
    intro n
    have hε_pos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by
      refine inv_pos.mpr ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hscalar := (Metric.tendsto_atTop.mp (happroxH1_val n)) _ hε_pos
    have hcoords : ∀ i : Fin d, ∃ N : ℕ, ∀ m ≥ N,
        dist ((H10Function.approxH1 hUopen (φ n) m).gradCoordToScalarL2 i)
          ((φ n).toH1Function.gradCoordToScalarL2 i) < ((n : ℝ) + 1)⁻¹ := fun i =>
      (Metric.tendsto_atTop.mp (happroxH1_gradcoord n i)) _ hε_pos
    choose Nc hNc using hcoords
    obtain ⟨Nv, hNv⟩ := hscalar
    let M : ℕ := max Nv ((Finset.univ : Finset (Fin d)).sup Nc)
    have hMv : Nv ≤ M := le_max_left _ _
    have hMc : ∀ i : Fin d, Nc i ≤ M := by
      intro i
      refine le_max_of_le_right ?_
      exact Finset.le_sup (f := Nc) (Finset.mem_univ i)
    refine ⟨M, (hNv M hMv).le, ?_⟩
    intro i
    exact (hNc i M (hMc i)).le
  choose m hm_val hm_grad using diagonal
  -- (7) Build the H¹₀ function whose approximants are the chosen diagonal.
  -- First produce `a n : H1Function U` as the diagonal smooth H¹-packaging.
  let a : ℕ → H1Function U := fun n => H10Function.approxH1 hUopen (φ n) (m n)
  -- (a n).toScalarL2 → v.toScalarL2
  -- Helper: 1/(n+1) is small eventually.
  have hinv_small : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ((n : ℝ) + 1)⁻¹ < ε := by
    intro ε hε
    have htend_one_div :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq : (fun n : ℕ => 1 / ((n : ℝ) + 1)) =
        fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
      funext n; rw [one_div]
    rw [heq] at htend_one_div
    have hev := Metric.tendsto_atTop.mp htend_one_div ε hε
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hnn := hN n hn
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by
      refine inv_nonneg.mpr ?_
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 1)⁻¹ = |((n : ℝ) + 1)⁻¹| := (abs_of_nonneg hpos).symm
      _ = dist (((n : ℝ) + 1)⁻¹) 0 := by rw [Real.dist_eq, sub_zero]
      _ < ε := hnn
  have ha_val :
      Filter.Tendsto (fun n => (a n).toScalarL2) Filter.atTop (nhds v.toScalarL2) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hval_tendsto (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist (a n).toScalarL2 v.toScalarL2 ≤
        dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
          + dist (φ n).toH1Function.toScalarL2 v.toScalarL2 := dist_triangle _ _ _
    have hm_val_n : dist (a n).toScalarL2 (φ n).toH1Function.toScalarL2
        ≤ ((n : ℝ) + 1)⁻¹ := hm_val n
    have hN₂_n : dist (φ n).toH1Function.toScalarL2 v.toScalarL2 < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith
  have ha_gradcoord :
      ∀ i : Fin d, Filter.Tendsto (fun n => (a n).gradCoordToScalarL2 i)
        Filter.atTop (nhds (v.gradCoordToScalarL2 i)) := by
    intro i
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨N₁, hN₁⟩ := hinv_small (ε / 2) hε2
    obtain ⟨N₂, hN₂⟩ :=
      Metric.tendsto_atTop.mp (hgradcoord_tendsto i) (ε / 2) hε2
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := le_of_max_le_left hn
    have hn2 : N₂ ≤ n := le_of_max_le_right hn
    have htri : dist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) ≤
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          + dist ((φ n).toH1Function.gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i) :=
      dist_triangle _ _ _
    have hm_grad_n :
        dist ((a n).gradCoordToScalarL2 i) ((φ n).toH1Function.gradCoordToScalarL2 i)
          ≤ ((n : ℝ) + 1)⁻¹ := hm_grad n i
    have hN₂_n : dist ((φ n).toH1Function.gradCoordToScalarL2 i)
        (v.gradCoordToScalarL2 i) < ε / 2 := hN₂ n hn2
    have hN₁_n : ((n : ℝ) + 1)⁻¹ < ε / 2 := hN₁ n hn1
    linarith
  -- Convert these ScalarL2 tendsto's to the eLpNorm tendsto required by H10Function.
  have htendsto_val_eLpNorm :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => (φ n).approx (m n) x - v.toFun x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    -- (a n).toScalarL2 = ((φ n).approx (m n)).toScalarL2 via ofContDiff.
    -- Use edist characterization.
    have hedist :
        Filter.Tendsto (fun n => edist (a n).toScalarL2 v.toScalarL2) Filter.atTop
          (nhds 0) := by
      rw [← edist_self v.toScalarL2]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp ha_val
    refine hedist.congr ?_
    intro n
    -- edist (a n).toScalarL2 v.toScalarL2
    --   = eLpNorm ((a n).toFun - v.toFun) 2 μ
    --   = eLpNorm ((φ n).approx (m n) - v.toFun) 2 μ
    rw [← eLpNorm_toFun_sub_eq_edist_toScalarL2]
    -- (a n).toFun = (φ n).approx (m n)
    rfl
  have htendsto_grad_eLpNorm :
      ∀ i : Fin d, Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ ((φ n).approx (m n)) x) (basisVec i) -
                v.grad x i) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0) := by
    intro i
    have hedist :
        Filter.Tendsto
          (fun n => edist ((a n).gradCoordToScalarL2 i) (v.gradCoordToScalarL2 i))
          Filter.atTop (nhds 0) := by
      rw [← edist_self (v.gradCoordToScalarL2 i)]
      exact (continuous_id.edist continuous_const).continuousAt.tendsto.comp
        (ha_gradcoord i)
    refine hedist.congr ?_
    intro n
    rw [← eLpNorm_grad_coord_sub_eq_edist_gradCoordToScalarL2]
    -- (a n).grad x i = (fderiv ℝ ((φ n).approx (m n)) x) (basisVec i)
    rfl
  -- Now assemble the H¹₀ function.
  let u : H10Function U :=
    { toH1Function := v
      approx := fun n => (φ n).approx (m n)
      approx_smooth := fun n => (φ n).approx_smooth (m n)
      approx_hasCompactSupport := fun n => (φ n).approx_hasCompactSupport (m n)
      approx_support_subset := fun n => (φ n).approx_support_subset (m n)
      tendsto_approx := htendsto_val_eLpNorm
      tendsto_approx_grad := htendsto_grad_eLpNorm }
  exact ⟨u, hv_val, hv_grad⟩

namespace H10GraphClosed

noncomputable instance : CompleteSpace (H10GraphClosedSpace (d := d) U) := by
  simpa [H10GraphClosedSpace] using!
    (h10GraphClosedSubmodule U).isClosed.completeSpace_coe

/-- Scalar value component of a closed `H¹₀` graph point. -/
abbrev value (z : H10GraphClosedSpace (d := d) U) : ScalarL2 U :=
  z.1.1

/-- Gradient component of a closed `H¹₀` graph point. -/
abbrev gradient (z : H10GraphClosedSpace (d := d) U) : HilbertVectorL2 U :=
  z.1.2

/-- Continuous scalar-value projection from the closed `H¹₀` graph. -/
noncomputable def valueCLM :
    H10GraphClosedSpace (d := d) U →L[ℝ] ScalarL2 U :=
  (ContinuousLinearMap.fst ℝ (ScalarL2 U) (HilbertVectorL2 U)).comp
    ((h10GraphClosedSubmodule U).toSubmodule.subtypeL)

@[simp] theorem valueCLM_apply (z : H10GraphClosedSpace (d := d) U) :
    valueCLM (U := U) z = value (U := U) z :=
  rfl

/-- Continuous gradient projection from the closed `H¹₀` graph. -/
noncomputable def gradientCLM :
    H10GraphClosedSpace (d := d) U →L[ℝ] HilbertVectorL2 U :=
  (ContinuousLinearMap.snd ℝ (ScalarL2 U) (HilbertVectorL2 U)).comp
    ((h10GraphClosedSubmodule U).toSubmodule.subtypeL)

@[simp] theorem gradientCLM_apply (z : H10GraphClosedSpace (d := d) U) :
    gradientCLM (U := U) z = gradient (U := U) z :=
  rfl

/-- The zero-trace Poincare estimate on the closed graph, stated on the graph
carrier. -/
theorem exists_norm_value_le_mul_norm_gradient
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : H10GraphClosedSpace (d := d) U,
        ‖value (U := U) z‖ ≤ C * ‖gradient (U := U) z‖ := by
  rcases h10GraphClosedSubmodule_exists_norm_value_le_mul_norm_gradient
      (U := U) hU with ⟨C, hC, hbound⟩
  exact ⟨C, hC, fun z => hbound z.1 z.2⟩

/-- The closed graph norm is controlled by the gradient norm on bounded open
convex domains. -/
theorem exists_norm_le_mul_norm_gradient
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : H10GraphClosedSpace (d := d) U,
        ‖z‖ ≤ M * ‖gradient (U := U) z‖ := by
  rcases exists_norm_value_le_mul_norm_gradient (U := U) hU with ⟨C, hC, hbound⟩
  refine ⟨C + 1, by positivity, ?_⟩
  intro z
  let a : ℝ := ‖value (U := U) z‖
  let b : ℝ := ‖gradient (U := U) z‖
  have ha : 0 ≤ a := by simp [a]
  have hb : 0 ≤ b := by simp [b]
  have hvalue : a ≤ C * b := by
    simpa [a, b] using hbound z
  calc
    ‖z‖ = max a b := by
      change ‖(z.1 : ScalarL2 U × HilbertVectorL2 U)‖ = max a b
      rw [Prod.norm_def]
    _ ≤ (C + 1) * b := by
      refine max_le ?_ ?_
      · nlinarith [hvalue, hb]
      · nlinarith [hC, hb]

/-- The gradient projection from the closed `H¹₀` graph is anti-Lipschitz on
bounded open convex domains. -/
theorem exists_antilipschitzWith_gradientCLM
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) :
    ∃ K : NNReal, AntilipschitzWith K (gradientCLM (d := d) (U := U)) := by
  rcases exists_norm_le_mul_norm_gradient (U := U) hU with ⟨M, hM, hbound⟩
  refine ⟨⟨M, hM⟩, ?_⟩
  apply (gradientCLM (d := d) (U := U)).antilipschitz_of_bound
  intro z
  simpa using! hbound z

/-- The range of the gradient projection from the closed `H¹₀` graph is closed. -/
theorem isClosed_range_gradientCLM
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) :
    IsClosed (Set.range (gradientCLM (d := d) (U := U))) := by
  rcases exists_antilipschitzWith_gradientCLM (U := U) hU with ⟨K, hK⟩
  exact hK.isClosed_range (gradientCLM (d := d) (U := U)).uniformContinuous

end H10GraphClosed

end Homogenization
