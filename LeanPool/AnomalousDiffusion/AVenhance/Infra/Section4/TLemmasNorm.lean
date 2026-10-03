/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.H1.Definitions
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.L2Space

/-! Minkowski inequalities in the exact periodic cell norms used by the two
T-iterate lemmas.  Vector-valued gradients use `PiLp 2`, so their pointwise
norm is the Euclidean norm from the `vecNormSq` definition. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4
open AVenhance

theorem TLemmasNorm.lp_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) ∂μ :=
      MeasureTheory.L2.inner_def _ _
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]

theorem TLemmasNorm.lp_norm_eq_sqrt_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {f : α → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  calc
    ‖hf.toLp f‖ = Real.sqrt (‖hf.toLp f‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
      rw [TLemmasNorm.lp_norm_sq_eq_integral hf]

/-- The cell scalar `L²` norm is subadditive. -/
theorem sqrt_l2NormSq_add_le {f g : Vec 2 → ℝ}
    (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    Real.sqrt (l2NormSq (fun x => f x + g x)) ≤
      Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) := by
  have hsum : MemLp (fun x => f x + g x) 2 (volume.restrict unitCube) := by
    change MemLp f 2 (volume.restrict unitCube) at hf
    change MemLp g 2 (volume.restrict unitCube) at hg
    change MemLp (f + g) 2 (volume.restrict unitCube)
    exact hf.add hg
  have hLp : hsum.toLp (fun x => f x + g x) =
      hf.toLp f + hg.toLp g := by
    apply Lp.ext
    filter_upwards [hsum.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x hsum' hf' hg' hadd
    calc
      hsum.toLp (fun x => f x + g x) x = (f + g) x := hsum'
      _ = hf.toLp f x + hg.toLp g x := by
        change f x + g x = _
        rw [← hf', ← hg']
      _ = (hf.toLp f + hg.toLp g) x := hadd.symm
  have htriangle : ‖hsum.toLp (fun x => f x + g x)‖ ≤
      ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
    rw [hLp]
    exact norm_add_le _ _
  have hleft : ‖hsum.toLp (fun x => f x + g x)‖ =
      Real.sqrt (l2NormSq (fun x => f x + g x)) := by
    rw [TLemmasNorm.lp_norm_eq_sqrt_integral hsum]
    simp [l2NormSq, Real.norm_eq_abs, sq_abs]
  have hright₁ : ‖hf.toLp f‖ = Real.sqrt (l2NormSq f) := by
    rw [TLemmasNorm.lp_norm_eq_sqrt_integral hf]
    simp [l2NormSq, Real.norm_eq_abs, sq_abs]
  have hright₂ : ‖hg.toLp g‖ = Real.sqrt (l2NormSq g) := by
    rw [TLemmasNorm.lp_norm_eq_sqrt_integral hg]
    simp [l2NormSq, Real.norm_eq_abs, sq_abs]
  rw [hleft, hright₁, hright₂] at htriangle
  exact htriangle

theorem TLemmasNorm.memLp_finset_sum {ι α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {p : ENNReal} {μ : Measure α}
    {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun x => ∑ i ∈ s, f i x) p μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact MemLp.zero
  | @insert a s ha ih =>
      have htail : MemLp (fun x => ∑ i ∈ s, f i x) p μ :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hadd := (hf a (Finset.mem_insert_self a s)).add htail
      have hEq : (fun x => ∑ i ∈ insert a s, f i x) =
          fun x => f a x + ∑ i ∈ s, f i x := by
        funext x
        simp [Finset.sum_insert, ha]
      rw [hEq]
      exact hadd

/-- Minkowski for any finite family of scalar cell functions. -/
theorem sqrt_l2NormSq_finset_sum_le {ι : Type*}
    (s : Finset ι) (f : ι → Vec 2 → ℝ)
    (hf : ∀ i ∈ s, MemL2On unitCube (f i)) :
    Real.sqrt (l2NormSq (fun x => ∑ i ∈ s, f i x)) ≤
      ∑ i ∈ s, Real.sqrt (l2NormSq (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2NormSq]
  | @insert a s ha ih =>
      have htail : MemL2On unitCube (fun x => ∑ i ∈ s, f i x) := by
        change MemLp (fun x => ∑ i ∈ s, f i x) 2 (volume.restrict unitCube)
        exact TLemmasNorm.memLp_finset_sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have hsum := sqrt_l2NormSq_add_le (hf a (Finset.mem_insert_self a s)) htail
      have hEq : (fun x => ∑ i ∈ insert a s, f i x) =
          fun x => f a x + ∑ i ∈ s, f i x := by
        funext x
        simp [Finset.sum_insert, ha]
      rw [hEq]
      calc
        _ ≤ Real.sqrt (l2NormSq (f a)) +
            Real.sqrt (l2NormSq (fun x => ∑ i ∈ s, f i x)) := hsum
        _ ≤ Real.sqrt (l2NormSq (f a)) +
            ∑ i ∈ s, Real.sqrt (l2NormSq (f i)) :=
          add_le_add le_rfl (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        _ = _ := by rw [Finset.sum_insert ha]

/-- Two-dimensional real vectors equipped with the Euclidean norm. -/
abbrev EuclideanVec2 := PiLp 2 (fun _ : Fin 2 => ℝ)

/-- Realize a `Vec 2` field in the Euclidean `L²` carrier used for
spacetime Minkowski estimates. -/
def euclideanVec2Lift (v : Vec 2) : EuclideanVec2 := WithLp.toLp 2 v

theorem TLemmasNorm.euclideanVec2Lift_norm_sq (v : Vec 2) :
    ‖euclideanVec2Lift v‖ ^ 2 = vecNormSq v := by
  have hn : ‖euclideanVec2Lift v‖ = Real.sqrt (vecNormSq v) := by
    change ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin 2 => ℝ))‖ = _
    rw [PiLp.norm_eq_of_L2]
    congr 1
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Fin.sum_univ_two]
    ring
  rw [hn, Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)]

theorem TLemmasNorm.memLp_euclideanLift_finset_sum {ι : Type*}
    (s : Finset ι) (F : ι → ℝ × Vec 2 → Vec 2)
    (hF : ∀ i ∈ s, MemLp (fun p => euclideanVec2Lift (F i p))
      2 (volume.restrict timeCube)) :
    MemLp (fun p => euclideanVec2Lift (∑ i ∈ s, F i p))
      2 (volume.restrict timeCube) := by
  classical
  have hsum : MemLp (fun p => ∑ i ∈ s, euclideanVec2Lift (F i p))
      2 (volume.restrict timeCube) := TLemmasNorm.memLp_finset_sum hF
  have hEq : (fun p => euclideanVec2Lift (∑ i ∈ s, F i p)) =
      fun p => ∑ i ∈ s, euclideanVec2Lift (F i p) := by
    funext p
    change WithLp.toLp 2 (∑ i ∈ s, F i p) = _
    rw [WithLp.toLp_sum]
    rfl
  rw [hEq]
  exact hsum

theorem TLemmasNorm.spaceGrad_finset_sum {ι : Type*}
    (s : Finset ι) (u : ι → ℝ → Vec 2 → ℝ)
    (hD : ∀ i ∈ s, ∀ t, 0 < t → Differentiable ℝ (u i t))
    (t : ℝ) (ht : 0 < t) (x : Vec 2) :
    spaceGrad (fun y => ∑ i ∈ s, u i t y) x =
      ∑ i ∈ s, spaceGrad (u i t) x := by
  classical
  funext j
  change fderiv ℝ (fun y => ∑ i ∈ s, u i t y) x (basisVec j) = _
  have hAt : ∀ i ∈ s, DifferentiableAt ℝ (fun y => u i t y) x := by
    intro i hi
    exact hD i hi t ht x
  have hsumfun : (fun y => ∑ i ∈ s, u i t y) =
      ∑ i ∈ s, fun y => u i t y := by
    funext y
    simp only [Finset.sum_apply]
  rw [hsumfun, fderiv_sum hAt]
  simp [spaceGrad]

end AVenhance.Infra.Section4

end
