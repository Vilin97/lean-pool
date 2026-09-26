/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FoldNorm
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.FoldTransport
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Truncation.WeakGradientLimit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Box
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero

/-! # Extension -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization Homogenization.H1Function
open scoped ENNReal NNReal BigOperators Topology

/-!
# Even-fold extension of an `H¹(box)` function

Given `u ∈ H¹(Box lo hi)`, its even-fold extension `Eu (x) = u (Fold lo hi x)`
(with the signed folded gradient) is an `H¹(Box3 lo hi)` function whose `L²`
norms on the tripled box are controlled by `(3^d)^{1/2}` times the `L²` norms of
`u` on the base box, and which agrees with `u` a.e. on the base box.

The construction feeds the globally smooth `convexApproxSmoothH1` approximants of
`u`, cut off to compact support, through the per-approximant fold weak-gradient
identity (`hasWeakPartialDerivOn_univ_foldComp`) and closes under `L²` limits
(`HasWeakGradientOn.of_tendsto_eLpNorm_two`); the norm transport is supplied by
`FoldNorm`.
-/

noncomputable section

variable {d : ℕ}

/-! ## Geometry of the base box -/

theorem isOpen_Box (lo hi : Vec d) : IsOpen (Box lo hi) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isOpenBoundedConvexDomain_Box (lo hi : Vec d) :
    IsOpenBoundedConvexDomain (Box lo hi) := by
  refine ⟨isOpen_Box lo hi, ?_, ?_⟩
  · exact Homogenization.Bornology.IsBounded.isBoundedDomain <|
      Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _
  · exact convex_pi fun _ _ => convex_Ioo _ _

/-- The tripled box is the base box for the reflected corners. -/
theorem Box3_eq_Box (lo hi : Vec d) :
    Box3 lo hi = Box (fun k => 2 * lo k - hi k) (fun k => 2 * hi k - lo k) := rfl

/-- The cutoff with half the cube side as margin is compactly supported in the tripled
box, equals one on the base box, and has coordinate derivatives bounded by `32 / L`. -/
theorem boxCutoff_halfSide_properties (z hi : Vec d) (L : ℝ) (hL : 0 < L)
    (hval : ∀ k, hi k = z k + L) :
    HasCompactSupport (boxCutoff z hi (L / 2)) ∧
      (∀ x ∈ Box z hi, boxCutoff z hi (L / 2) x = 1) ∧
      tsupport (boxCutoff z hi (L / 2)) ⊆ Box3 z hi ∧
      (∀ x i, |fderiv ℝ (boxCutoff z hi (L / 2)) x (basisVec i)| ≤ 32 / L) := by
  have hℓ : (0 : ℝ) < L / 2 := by linarith
  set χ : Vec d → ℝ := boxCutoff z hi (L / 2) with hχ
  have hχ_cptsupp : HasCompactSupport χ := by
    apply HasCompactSupport.intro
      (K := Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2)) isCompact_Icc
    intro x hx; exact boxCutoff_eq_zero hℓ hx
  have hχ_one : ∀ x ∈ Box z hi, χ x = 1 := by
    intro x hx
    exact boxCutoff_eq_one hℓ (Set.mem_Icc.2
      ⟨fun k => (Set.mem_univ_pi.1 hx k).1.le, fun k => (Set.mem_univ_pi.1 hx k).2.le⟩)
  have hχ_sub : tsupport χ ⊆ Box3 z hi := by
    have hsupp : Function.support χ ⊆ Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2) :=
      fun x hx => by by_contra hxn; exact hx (boxCutoff_eq_zero hℓ hxn)
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    rw [Box3_eq_Box]
    intro x hx
    rw [Set.mem_Icc] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    exact ⟨by have := hx.1 k; have := hval k; simp only [] at *; linarith,
      by have := hx.2 k; have := hval k; simp only [] at *; linarith⟩
  have hχ_deriv : ∀ x i, |fderiv ℝ χ x (basisVec i)| ≤ 32 / L := by
    intro x i
    have := boxCutoff_deriv_bound (lo := z) (hi := hi) hℓ x i
    have h2 : (16 : ℝ) / (L / 2) = 32 / L := by field_simp; ring
    simpa [hχ, basisVec, h2] using this
  exact ⟨hχ_cptsupp, hχ_one, hχ_sub, hχ_deriv⟩

/-- A concrete closed ball inside a nonempty base box. -/
theorem exists_ball_subset_Box (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) (hd : 0 < d) :
    ∃ (x0 : Vec d) (r : ℝ), 0 < r ∧ Metric.closedBall x0 r ⊆ Box lo hi := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  set m : ℝ := Finset.univ.inf' hne (fun k => hi k - lo k) with hm
  have hm_pos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff hne]
    exact fun k _ => by linarith [hlt k]
  refine ⟨fun k => (lo k + hi k) / 2, m / 3, by linarith, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)] at hx
  refine Set.mem_univ_pi.2 fun k => ?_
  have hxk : dist (x k) ((lo k + hi k) / 2) ≤ m / 3 := hx k
  rw [Real.dist_eq, abs_le] at hxk
  have hmk : m ≤ hi k - lo k := Finset.inf'_le _ (Finset.mem_univ k)
  constructor <;> [skip; skip] <;> [nlinarith [hxk.1, hxk.2]; nlinarith [hxk.1, hxk.2]]

/-! ## `eLpNorm` convergence of the smooth approximants -/

/-- Convergence in `L²(U)` of the `convexApproxSmoothH1` approximants, in the
`eLpNorm` form the closure lemma consumes. -/
theorem tendsto_eLpNorm_convexApproxSmoothH1 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {x0 : Vec d} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x0 r ⊆ U) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => (convexApproxSmoothH1 hU u x0 hr n).toFun x - u.toFun x) 2
        (volume.restrict U))
      Filter.atTop (nhds 0) := by
  set ψ : ℕ → H1Function U := convexApproxSmoothH1 hU u x0 hr with hψ
  have hedist : ∀ n, eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 2 (volume.restrict U)
      = edist (ψ n).toScalarL2 u.toScalarL2 := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [(ψ n).coeFn_toScalarL2, u.coeFn_toScalarL2] with x hu1 hu2
    simp [Pi.sub_apply, hu1, hu2]
  have h1 : Filter.Tendsto (fun n => (ψ n).toScalarL2) Filter.atTop (nhds u.toScalarL2) :=
    tendsto_convexApproxSmoothH1_toScalarL2 hU u hball hr
  have h2 : Filter.Tendsto (fun n => edist (ψ n).toScalarL2 u.toScalarL2)
      Filter.atTop (nhds 0) := by
    simpa using h1.edist (tendsto_const_nhds (x := u.toScalarL2))
  exact h2.congr (fun n => (hedist n).symm)

/-- Convergence in `L²(U)` of the coordinate gradients of the approximants. -/
theorem tendsto_eLpNorm_grad_convexApproxSmoothH1 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {x0 : Vec d} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x0 r ⊆ U) (i : Fin d) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => (convexApproxSmoothH1 hU u x0 hr n).grad x i - u.grad x i) 2
        (volume.restrict U))
      Filter.atTop (nhds 0) := by
  set ψ : ℕ → H1Function U := convexApproxSmoothH1 hU u x0 hr with hψ
  have hedist : ∀ n, eLpNorm (fun x => (ψ n).grad x i - u.grad x i) 2 (volume.restrict U)
      = edist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i) := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [(ψ n).coeFn_gradCoordToScalarL2 i, u.coeFn_gradCoordToScalarL2 i]
      with x hu1 hu2
    simp [Pi.sub_apply, hu1, hu2]
  have h1 : Filter.Tendsto (fun n => (ψ n).gradCoordToScalarL2 i) Filter.atTop
      (nhds (u.gradCoordToScalarL2 i)) :=
    tendsto_convexApproxSmoothH1_gradCoordToScalarL2 hU u hball hr i
  have h2 : Filter.Tendsto (fun n => edist ((ψ n).gradCoordToScalarL2 i)
      (u.gradCoordToScalarL2 i)) Filter.atTop (nhds 0) := by
    simpa using h1.edist (tendsto_const_nhds (x := u.gradCoordToScalarL2 i))
  exact h2.congr (fun n => (hedist n).symm)

/-! ## The fold extension -/

/-- The fold-extension data bundle. -/
structure FoldExtension (lo hi : Vec d) (u : H1Function (Box lo hi)) where
  /-- The extended `H¹` function on the tripled box. -/
  Eu : H1Function (Box3 lo hi)
  /-- The extension agrees with `u` a.e. on the base box. -/
  toFun_ae : Eu.toFun =ᵐ[volume.restrict (Box lo hi)] u.toFun
  /-- The extension's gradient agrees with `u`'s a.e. on the base box. -/
  grad_ae : ∀ i, (fun x => Eu.grad x i) =ᵐ[volume.restrict (Box lo hi)] fun x => u.grad x i
  /-- `L²` control of the extension by the constant `(3^d)^{1/2}`. -/
  eLpNorm_le : eLpNorm Eu.toFun 2 (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) * eLpNorm u.toFun 2 (volume.restrict (Box lo hi))
  /-- `L²` control of the extension's coordinate gradients. -/
  grad_eLpNorm_le : ∀ i, eLpNorm (fun x => Eu.grad x i) 2 (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2)
      * eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box lo hi))

/-- `Cd = (3^d)^{1/2}` is finite. -/
theorem Cd_ne_top : (((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2)) ≠ ⊤ :=
  (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.pow_ne_top (by simp))).ne

theorem measurable_foldSign_comp (lo hi : Vec d) (i : Fin d) :
    Measurable (fun x : Vec d => foldSign (lo i) (hi i) (x i)) := by
  have hsign : Measurable (foldSign (lo i) (hi i)) := by
    unfold foldSign
    refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  exact hsign.comp (measurable_pi_apply i)

theorem norm_foldSign_le_one (lo hi t : ℝ) : ‖foldSign lo hi t‖ ≤ 1 := by
  unfold foldSign; split_ifs <;> simp

/-- **Even-fold extension of an `H¹(box)` function.** -/
def foldExtension {m : ℕ} (lo hi : Vec (m + 1)) (hlt : ∀ k, lo k < hi k)
    (u : H1Function (Box lo hi)) : FoldExtension lo hi u := by
  classical
  set lo3 : Vec (m + 1) := fun k => 2 * lo k - hi k with hlo3
  set hi3 : Vec (m + 1) := fun k => 2 * hi k - lo k with hhi3
  have hlt3 : ∀ k, lo3 k < hi3 k := fun k => by
    simp only [hlo3, hhi3]; linarith [hlt k]
  have hbox3 : Box3 lo hi = Box lo3 hi3 := rfl
  have hU : IsOpenBoundedConvexDomain (Box lo hi) := isOpenBoundedConvexDomain_Box lo hi
  have hFold_cont : Continuous (Fold lo hi) := continuous_Fold lo hi (fun k => (hlt k).le)
  have hFold_meas : Measurable (Fold lo hi) := hFold_cont.measurable
  -- the finite transport constant
  set Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ ((1 : ℝ) / 2) with hCd
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.pow_ne_top (by simp))
  -- measurable representatives of `u` and its gradient
  have hg_asm : AEStronglyMeasurable u.toFun (volume.restrict (Box lo hi)) :=
    u.memL2.aestronglyMeasurable
  set g : Vec (m + 1) → ℝ := hg_asm.mk u.toFun with hg_def
  have hg_meas : Measurable g := hg_asm.stronglyMeasurable_mk.measurable
  have hg_ae : u.toFun =ᵐ[volume.restrict (Box lo hi)] g := hg_asm.ae_eq_mk
  have hgi_asm : ∀ i, AEStronglyMeasurable (fun x => u.grad x i) (volume.restrict (Box lo hi)) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable
  set gi : Fin (m + 1) → Vec (m + 1) → ℝ := fun i => (hgi_asm i).mk (fun x => u.grad x i) with hgi_def
  have hgi_meas : ∀ i, Measurable (gi i) := fun i => (hgi_asm i).stronglyMeasurable_mk.measurable
  have hgi_ae : ∀ i, (fun x => u.grad x i) =ᵐ[volume.restrict (Box lo hi)] gi i :=
    fun i => (hgi_asm i).ae_eq_mk
  -- a concrete ball inside the base box
  set x0 : Vec (m + 1) := fun k => (lo k + hi k) / 2 with hx0
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun k => hi k - lo k) with hδ
  have hδ_pos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff Finset.univ_nonempty]; exact fun k _ => by linarith [hlt k]
  set r : ℝ := δ / 3 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hball : Metric.closedBall x0 r ⊆ Box lo hi := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff hr.le] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    have hxk : dist (x k) (x0 k) ≤ r := hx k
    rw [Real.dist_eq, abs_le] at hxk
    have hmk : δ ≤ hi k - lo k := Finset.inf'_le _ (Finset.mem_univ k)
    simp only [hx0, hrdef] at hxk
    exact ⟨by nlinarith [hxk.1], by nlinarith [hxk.2]⟩
  -- the approximants and their smoothness
  set A : ℕ → H1Function (Box lo hi) := convexApproxSmoothH1 hU u x0 hr with hA
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n).toFun := by
    intro n
    rw [hA, convexApproxSmoothH1_toFun]
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel) (by norm_num : (1 : ENNReal) ≤ 2)
      u.memL2 hr (by dsimp [unitConvexApproxScale]; positivity)
  have hφ_grad : ∀ n x i, (A n).grad x i = fderiv ℝ ((A n).toFun) x (basisVec i) := by
    intro n x i
    simp only [hA, convexApproxSmoothH1_grad, convexApproxSmoothH1_toFun]
  -- the cutoff (identically one on a neighbourhood of the tripled box)
  set χ : Vec (m + 1) → ℝ := boxCutoff lo3 hi3 1 with hχ
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_cptsupp : HasCompactSupport χ := by
    apply HasCompactSupport.intro (K := Set.Icc (fun k => lo3 k - 1) (fun k => hi3 k + 1))
      isCompact_Icc
    intro x hx
    exact boxCutoff_eq_zero (by norm_num) hx
  have hχ_one : ∀ x ∈ Set.Icc lo3 hi3, χ x = 1 := fun x hx => boxCutoff_eq_one (by norm_num) hx
  -- membership of `Box lo hi` and `Box3` in the plateau
  have hBox_Icc : ∀ x ∈ Box lo hi, x ∈ Set.Icc lo3 hi3 := by
    intro x hx
    have hx' := Set.mem_univ_pi.1 hx
    refine Set.mem_Icc.2 ⟨fun k => ?_, fun k => ?_⟩
    · have := (hx' k).1; simp only [hlo3]; linarith [hlt k]
    · have := (hx' k).2; simp only [hhi3]; linarith [hlt k]
  -- the cut-off approximants
  set wn : ℕ → Vec (m + 1) → ℝ := fun n x => χ x * (A n).toFun x with hwn
  have hw_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (wn n) := fun n => hχ_smooth.mul (hφ_smooth n)
  have hw_cont : ∀ n, Continuous (wn n) := fun n => (hw_smooth n).continuous
  have hw_meas : ∀ n, Measurable (wn n) := fun n => (hw_cont n).measurable
  have hw_cptsupp : ∀ n, HasCompactSupport (wn n) := fun n => hχ_cptsupp.mul_right
  have hw_memLp : ∀ n, MemLp (wn n) 2 (volume.restrict (Box lo hi)) := fun n =>
    ((hw_cont n).memLp_of_hasCompactSupport (hw_cptsupp n)).restrict _
  -- `wn = φ` on the plateau, and fderiv agree there
  have hw_eq_φ : ∀ n, ∀ x ∈ Set.Icc lo3 hi3, wn n x = (A n).toFun x := by
    intro n x hx; simp only [hwn, hχ_one x hx, one_mul]
  have hfderiv_eq : ∀ n, ∀ y ∈ Box lo hi, fderiv ℝ (wn n) y = fderiv ℝ ((A n).toFun) y := by
    intro n y hy
    have hy3 : y ∈ Box3 lo hi := by
      rw [hbox3]
      refine Set.mem_univ_pi.2 fun k => ?_
      have hyk := (Set.mem_univ_pi.1 hy k)
      exact ⟨by have := hyk.1; simp only [hlo3]; linarith [hlt k],
        by have := hyk.2; simp only [hhi3]; linarith [hlt k]⟩
    have hnbhd : Box3 lo hi ∈ 𝓝 y :=
      (by rw [hbox3]; exact isOpen_Box lo3 hi3 : IsOpen (Box3 lo hi)).mem_nhds hy3
    have heq : wn n =ᶠ[𝓝 y] (A n).toFun := by
      refine Filter.eventuallyEq_of_mem hnbhd fun x hx => ?_
      refine hw_eq_φ n x ?_
      rw [hbox3] at hx
      have hx' := Set.mem_univ_pi.1 hx
      exact Set.mem_Icc.2 ⟨fun k => (hx' k).1.le, fun k => (hx' k).2.le⟩
    exact heq.fderiv_eq
  -- `L²` membership of the candidate extension and its gradient
  have hEu_mem : MemLp (fun x => g (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi)) := by
    refine ⟨(hg_meas.comp hFold_meas).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_foldComp hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae]
    exact ENNReal.mul_lt_top hCd_lt u.memL2.eLpNorm_lt_top
  have hEu_grad_mem : ∀ i, MemLp
      (fun x => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)) 2
      (volume.restrict (Box3 lo hi)) := by
    intro i
    refine ⟨(((hgi_meas i).comp hFold_meas).mul
      (measurable_foldSign_comp lo hi i)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (b := eLpNorm (fun x => gi i (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi)))
      (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)) ?_
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_foldSign_le_one _ _ _)
    · rw [eLpNorm_foldComp (hgi_meas i) lo hi hlt, ← eLpNorm_congr_ae (hgi_ae i)]
      exact ENNReal.mul_lt_top hCd_lt (u.gradMemL2 i).eLpNorm_lt_top
  -- `L²` membership of the approximants and their gradients
  have hEn_mem : ∀ n, MemLp (fun x => wn n (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi)) := by
    intro n
    refine ⟨((hw_cont n).comp hFold_cont).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_foldComp (hw_meas n) lo hi hlt]
    exact ENNReal.mul_lt_top hCd_lt (hw_memLp n).eLpNorm_lt_top
  have hDEn_mem : ∀ n, GradMemL2On (Box3 lo hi)
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) * foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have hcont : Continuous (fun y => fderiv ℝ (wn n) y (basisVec i)) :=
      (((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv (by simp)).clm_apply
        continuous_const
    refine ⟨((hcont.measurable.comp hFold_meas).mul
      (measurable_foldSign_comp lo hi i)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (b := eLpNorm (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i)) 2
        (volume.restrict (Box3 lo hi)))
      (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)) ?_
    · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_foldSign_le_one _ _ _)
    · rw [eLpNorm_foldComp hcont.measurable lo hi hlt]
      have hmem : MemLp (fun y => fderiv ℝ (wn n) y (basisVec i)) 2
          (volume.restrict (Box lo hi)) :=
        (hcont.memLp_of_hasCompactSupport
          ((hw_cptsupp n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict _
      exact ENNReal.mul_lt_top hCd_lt hmem.eLpNorm_lt_top
  -- the per-approximant weak gradient on the tripled box
  have hweak : ∀ n, HasWeakGradientOn (Box3 lo hi) (fun x => wn n (Fold lo hi x))
      (fun x i => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) * foldSign (lo i) (hi i) (x i)) := by
    intro n i
    have huniv := hasWeakPartialDerivOn_univ_foldComp
      ((hw_smooth n).of_le (by exact_mod_cast le_top)) (hw_cptsupp n) lo hi
      (fun k => (hlt k).le) i
    exact huniv.restrict (by rw [hbox3]; exact isOpen_Box lo3 hi3) (Set.subset_univ _)
  -- `L²` convergence of the approximants
  have htend_u : Filter.Tendsto (fun n => eLpNorm
      (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi)))
      Filter.atTop (nhds 0) := by
    have heq : ∀ n, eLpNorm (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) 2
        (volume.restrict (Box3 lo hi))
        = Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) 2 (volume.restrict (Box lo hi)) := by
      intro n
      have hcomp : eLpNorm (fun x => wn n (Fold lo hi x) - g (Fold lo hi x)) 2
            (volume.restrict (Box3 lo hi))
          = Cd * eLpNorm (fun y => wn n y - g y) 2 (volume.restrict (Box lo hi)) :=
        eLpNorm_foldComp ((hw_meas n).sub hg_meas) lo hi hlt
      rw [hcomp]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
      have hχ1 : χ x = 1 := hχ_one x (hBox_Icc x hxU)
      simp only [hwn, hχ1, one_mul, hgx]
    have hmul : Filter.Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).toFun x - u.toFun x) 2 (volume.restrict (Box lo hi)))
        Filter.atTop (nhds (Cd * 0)) :=
      ENNReal.Tendsto.const_mul (tendsto_eLpNorm_convexApproxSmoothH1 hU u hr hball)
        (Or.inr hCd_lt.ne)
    rw [mul_zero] at hmul
    exact hmul.congr (fun n => (heq n).symm)
  have htend_Du : ∀ i, Filter.Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) * foldSign (lo i) (hi i) (x i)
        - gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)) 2 (volume.restrict (Box3 lo hi)))
      Filter.atTop (nhds 0) := by
    intro i
    have hbound : ∀ n, eLpNorm (fun x => fderiv ℝ (wn n) (Fold lo hi x) (basisVec i)
          * foldSign (lo i) (hi i) (x i) - gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)) 2
        (volume.restrict (Box3 lo hi))
        ≤ Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) 2 (volume.restrict (Box lo hi)) := by
      intro n
      refine le_trans
        (b := eLpNorm (fun x => (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y) (Fold lo hi x))
          2 (volume.restrict (Box3 lo hi)))
        (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)) ?_
      · show ‖_‖ ≤ ‖(fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y) (Fold lo hi x)‖
        rw [show fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) * foldSign (lo i) (hi i) (x i)
              - gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)
            = (fderiv ℝ (wn n) (Fold lo hi x) (basisVec i) - gi i (Fold lo hi x))
              * foldSign (lo i) (hi i) (x i) by ring, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_foldSign_le_one _ _ _)
      · have hcomp : eLpNorm (fun x => (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y) (Fold lo hi x))
            2 (volume.restrict (Box3 lo hi))
          = Cd * eLpNorm (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y) 2 (volume.restrict (Box lo hi)) :=
          eLpNorm_foldComp
            ((((hw_smooth n).of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 (wn n)).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.measurable.sub (hgi_meas i)) lo hi hlt
        rw [hcomp]
        have hae : (fun y => fderiv ℝ (wn n) y (basisVec i) - gi i y)
            =ᵐ[volume.restrict (Box lo hi)] (fun x => (A n).grad x i - u.grad x i) := by
          filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
            with x hxU hgix
          show fderiv ℝ (wn n) x (basisVec i) - gi i x = (A n).grad x i - u.grad x i
          rw [hfderiv_eq n x hxU, ← hφ_grad n x i, ← hgix]
        rw [eLpNorm_congr_ae hae]
    have hrhs : Filter.Tendsto
        (fun n => Cd * eLpNorm (fun x => (A n).grad x i - u.grad x i) 2 (volume.restrict (Box lo hi)))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (tendsto_eLpNorm_grad_convexApproxSmoothH1 hU u hr hball i)
        (Or.inr hCd_lt.ne)
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => zero_le) hbound
  -- assemble
  exact
    { Eu :=
        { toFun := fun x => g (Fold lo hi x)
          grad := fun x i => gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i)
          memL2 := hEu_mem
          gradMemL2 := hEu_grad_mem
          hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_two hEu_mem hEu_grad_mem
            hEn_mem hDEn_mem hweak htend_u htend_Du }
      toFun_ae := by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hg_ae] with x hxU hgx
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le, (Set.mem_univ_pi.1 hxU k).2.le⟩
        show g (Fold lo hi x) = u.toFun x
        rw [hfold, hgx]
      grad_ae := fun i => by
        filter_upwards [ae_restrict_mem (isOpen_Box lo hi).measurableSet, hgi_ae i]
          with x hxU hgix
        have hxk := Set.mem_univ_pi.1 hxU i
        have hfold : Fold lo hi x = x :=
          Fold_of_mem fun k => ⟨(Set.mem_univ_pi.1 hxU k).1.le, (Set.mem_univ_pi.1 hxU k).2.le⟩
        have hsign : foldSign (lo i) (hi i) (x i) = 1 := by
          unfold foldSign; rw [if_neg (not_lt.mpr hxk.1.le), if_neg (not_lt.mpr hxk.2.le)]
        show gi i (Fold lo hi x) * foldSign (lo i) (hi i) (x i) = u.grad x i
        rw [hfold, hsign, mul_one, hgix]
      eLpNorm_le := le_of_eq (by
        rw [eLpNorm_foldComp hg_meas lo hi hlt, ← eLpNorm_congr_ae hg_ae])
      grad_eLpNorm_le := fun i =>
        le_trans (b := eLpNorm (fun x => gi i (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi)))
          (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => by
            rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_foldSign_le_one _ _ _)))
          (le_of_eq (by rw [eLpNorm_foldComp (hgi_meas i) lo hi hlt,
            ← eLpNorm_congr_ae (hgi_ae i)])) }

end

end Homogenization
