/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpGradientLimit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.H10GradientUpgrade
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ZeroTraceClosure
public import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Canonical zero-trace finite-`L^p` solution limits

The canonical bounded-data `H¹₀` solutions have finite-`L^p` gradients and
therefore have exact `W^{1,p}_0` upgrades.  Zero-trace Poincare control turns the
already constructed gradient convergence into scalar-value Cauchy control.
Completeness of `L^p` then supplies the scalar representative paired with the
canonical limiting gradient.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory _root_.Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private instance instFiniteLpW10pLimitFactOneLe (q : FiniteLpExponent) :
    Fact (1 ≤ q.exponent) :=
  ⟨q.one_lt.le⟩

/-- The selected canonical bounded-data solution, upgraded to `W^{1,p}_0` without
changing either its value or gradient representative. -/
noncomputable def finiteLpW10pSolutionApproximation
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N : ℕ) : W10pFunction (openCubeSet (originCube d m)) q.exponent :=
  (finiteLpSolutionApproximation m hsigma0 h
      (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toW10pOfGradMemLp
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) q
    (finiteLpSolutionApproximation_gradMemLp m hsigma0 h
      (finiteLpGradientLimitSubsequence q m hsigma0 h N))

@[simp] theorem finiteLpW10pSolutionApproximation_toFun
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N : ℕ) :
    (finiteLpW10pSolutionApproximation q m hsigma0 h N).toFun =
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.toFun :=
  H10Function.toW10pOfGradMemLp_toFun _ _ _ _

@[simp] theorem finiteLpW10pSolutionApproximation_grad
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N : ℕ) :
    (finiteLpW10pSolutionApproximation q m hsigma0 h N).grad =
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad :=
  H10Function.toW10pOfGradMemLp_grad _ _ _ _

private theorem tendsto_eLpNorm_finiteLpSolutionApproximation_grad_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun nk : ℕ × ℕ => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
  let Du := finiteLpGradientLimit q m hsigma0 h
  let F : ℕ → Vec d → HilbertVec d := fun N x => HilbertVec.ofVec
    ((finiteLpW10pSolutionApproximation q m hsigma0 h N).grad x - Du x)
  have hbase :=
    tendsto_eLpNorm_finiteLpSolutionApproximation_grad_sub_finiteLpGradientLimit
      q m hsigma0 h
  have hfst : Filter.Tendsto (Prod.fst : ℕ × ℕ → ℕ) Filter.atTop Filter.atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst : Filter.Tendsto (Prod.fst : ℕ × ℕ → ℕ)
        (Filter.atTop ×ˢ Filter.atTop) Filter.atTop)
  have hsnd : Filter.Tendsto (Prod.snd : ℕ × ℕ → ℕ) Filter.atTop Filter.atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd : Filter.Tendsto (Prod.snd : ℕ × ℕ → ℕ)
        (Filter.atTop ×ˢ Filter.atTop) Filter.atTop)
  have hfst_norm : Filter.Tendsto (fun nk : ℕ × ℕ => eLpNorm (F nk.1)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
    simpa only [F, finiteLpW10pSolutionApproximation_grad, Du] using! hbase.comp hfst
  have hsnd_norm : Filter.Tendsto (fun nk : ℕ × ℕ => eLpNorm (F nk.2)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
    simpa only [F, finiteLpW10pSolutionApproximation_grad, Du] using! hbase.comp hsnd
  have hsum := hfst_norm.add hsnd_norm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hsum) (fun _ => zero_le) (fun nk => ?_)
  have hfn : MemLp (F nk.1) q.exponent
      (volume.restrict (openCubeSet (originCube d m))) := by
    rw [memLp_piLp_iff]
    intro i
    simpa only [F, Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply,
      Pi.sub_apply] using!
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).gradMemLp i).sub
        (finiteLpGradientLimit_gradMemLp q m hsigma0 h i)
  have hfk : MemLp (F nk.2) q.exponent
      (volume.restrict (openCubeSet (originCube d m))) := by
    rw [memLp_piLp_iff]
    intro i
    simpa only [F, Function.comp_apply, HilbertVec.ofVec, PiLp.toLp_apply,
      Pi.sub_apply] using!
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).gradMemLp i).sub
        (finiteLpGradientLimit_gradMemLp q m hsigma0 h i)
  have heq : (fun x => HilbertVec.ofVec
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x)) =
      fun x => F nk.1 x - F nk.2 x := by
    funext x
    simp only [F]
    rw [show
      (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x =
        ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x - Du x) -
          ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x - Du x) by abel]
    exact (HilbertVec.ofVecL d).map_sub _ _
  rw [heq]
  exact eLpNorm_sub_le hfn.aestronglyMeasurable hfk.aestronglyMeasurable q.one_lt.le

private theorem tendsto_sum_eLpNorm_finiteLpSolutionApproximation_gradCoord_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun nk : ℕ × ℕ => ∑ i : Fin d, eLpNorm (fun x =>
      (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
  have hvec := tendsto_eLpNorm_finiteLpSolutionApproximation_grad_pair q m hsigma0 h
  have hright : Filter.Tendsto (fun nk : ℕ × ℕ => (d : ℝ≥0∞) * eLpNorm
      (fun x => HilbertVec.ofVec
        ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using! ENNReal.Tendsto.const_mul hvec (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
    (fun _ => zero_le) (fun nk => ?_)
  calc
    ∑ i : Fin d, eLpNorm (fun x =>
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m))) ≤
      ∑ _i : Fin d, eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x))
        q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [Pi.sub_apply] using coordinate_eLpNorm_le_euclidean
            (volume.restrict (openCubeSet (originCube d m))) q
            (fun x =>
              (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
                (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x) i
    _ = (d : ℝ≥0∞) * eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem finiteLpW10pSolutionApproximation_poincare_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (C : ℝ) (hPoincare : ∀ u : W10pFunction (openCubeSet (originCube d m)) q.exponent,
      ENNReal.toReal (eLpNorm u.toFun q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) ≤
        C * ∑ i : Fin d, ENNReal.toReal (eLpNorm (fun x => u.grad x i) q.exponent
          (volume.restrict (openCubeSet (originCube d m)))))
    (nk : ℕ × ℕ) :
    ENNReal.toReal (eLpNorm (fun x =>
      finiteLpW10pSolutionApproximation q m hsigma0 h nk.1 x -
        finiteLpW10pSolutionApproximation q m hsigma0 h nk.2 x)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) ≤
      C * ∑ i : Fin d, ENNReal.toReal (eLpNorm (fun x =>
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m)))) := by
  let v : H10Function (openCubeSet (originCube d m)) :=
    finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.1) -
      finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.2)
  have hvgrad : GradMemLpOn (openCubeSet (originCube d m)) q.exponent
      v.toH1Function.grad := by
    intro i
    rw [show v.toH1Function.grad = fun x =>
        (finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h nk.1)).toH1Function.grad x -
        (finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientLimitSubsequence q m hsigma0 h nk.2)).toH1Function.grad x by
      dsimp only [v]
      exact H1Function.sub_grad _ _]
    exact (finiteLpSolutionApproximation_gradMemLp m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.1) i).sub
      (finiteLpSolutionApproximation_gradMemLp m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.2) i)
  let w : W10pFunction (openCubeSet (originCube d m)) q.exponent :=
    v.toW10pOfGradMemLp
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) q hvgrad
  have hvfun : v.toH1Function.toFun = fun x =>
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.1)).toH1Function.toFun x -
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.2)).toH1Function.toFun x := by
    dsimp only [v]
    exact H1Function.sub_toFun _ _
  have hvgrad_eq : v.toH1Function.grad = fun x =>
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.1)).toH1Function.grad x -
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h nk.2)).toH1Function.grad x := by
    dsimp only [v]
    exact H1Function.sub_grad _ _
  have hbound := hPoincare w
  rw [show w.toFun = v.toH1Function.toFun by
    exact H10Function.toW10pOfGradMemLp_toFun _ _ _ _,
    show w.grad = v.toH1Function.grad by
      exact H10Function.toW10pOfGradMemLp_grad _ _ _ _, hvfun, hvgrad_eq] at hbound
  simpa only [finiteLpW10pSolutionApproximation_toFun,
    finiteLpW10pSolutionApproximation_grad, Pi.sub_apply] using hbound

private theorem tendsto_sum_toReal_eLpNorm_finiteLpSolutionApproximation_gradCoord_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun nk : ℕ × ℕ => ∑ i : Fin d,
      ENNReal.toReal (eLpNorm (fun x =>
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m))))) Filter.atTop (nhds 0) := by
  have hgrad :=
    tendsto_sum_eLpNorm_finiteLpSolutionApproximation_gradCoord_pair q m hsigma0 h
  let A : ℕ × ℕ → Fin d → ℝ≥0∞ := fun nk i => eLpNorm (fun x =>
    (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
      (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
    q.exponent (volume.restrict (openCubeSet (originCube d m)))
  have hsum_top : ∀ nk : ℕ × ℕ, (∑ i : Fin d, A nk i) ≠ ∞ := by
    intro nk
    apply ENNReal.sum_ne_top.2
    intro i _
    exact (((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).gradMemLp i).sub
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).gradMemLp i)).eLpNorm_ne_top
  have hgrad' : Filter.Tendsto (fun nk => ∑ i : Fin d, A nk i)
      Filter.atTop (nhds 0) := by
    simpa only [A] using hgrad
  have hreal := (ENNReal.tendsto_toReal_zero_iff hsum_top).2 hgrad'
  have heq : (fun nk => ENNReal.toReal (∑ i : Fin d, A nk i)) =
      fun nk => ∑ i : Fin d, ENNReal.toReal (A nk i) := by
    funext nk
    apply ENNReal.toReal_sum
    intro i _
    exact (((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).gradMemLp i).sub
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).gradMemLp i)).eLpNorm_ne_top
  rw [heq] at hreal
  simpa only [A] using hreal

private theorem tendsto_toReal_eLpNorm_finiteLpW10pSolutionApproximation_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun nk : ℕ × ℕ => ENNReal.toReal (eLpNorm (fun x =>
      finiteLpW10pSolutionApproximation q m hsigma0 h nk.1 x -
        finiteLpW10pSolutionApproximation q m hsigma0 h nk.2 x)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, _hCnonneg, hPoincare⟩ :=
    W10pFunction.exists_poincare_constant_of_isOpenBoundedConvexDomain
      q.one_lt q.lt_top.ne (isOpenBoundedConvexDomain_openCubeSet (originCube d m))
  have hgrad_real :=
    tendsto_sum_toReal_eLpNorm_finiteLpSolutionApproximation_gradCoord_pair
      q m hsigma0 h
  have hright : Filter.Tendsto (fun nk : ℕ × ℕ => C * ∑ i : Fin d,
      ENNReal.toReal (eLpNorm (fun x =>
        (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).grad x i -
          (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m))))) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hgrad_real
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
    (fun _ => ENNReal.toReal_nonneg) (fun nk => ?_)
  exact finiteLpW10pSolutionApproximation_poincare_pair q m hsigma0 h C
    (by simpa only [volumeMeasureOn] using hPoincare) nk

private theorem tendsto_eLpNorm_finiteLpW10pSolutionApproximation_pair
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun nk : ℕ × ℕ => eLpNorm (fun x =>
      finiteLpW10pSolutionApproximation q m hsigma0 h nk.1 x -
        finiteLpW10pSolutionApproximation q m hsigma0 h nk.2 x)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop (nhds 0) := by
  let B : ℕ × ℕ → ℝ≥0∞ := fun nk => eLpNorm (fun x =>
    finiteLpW10pSolutionApproximation q m hsigma0 h nk.1 x -
      finiteLpW10pSolutionApproximation q m hsigma0 h nk.2 x)
    q.exponent (volume.restrict (openCubeSet (originCube d m)))
  have hBtop : ∀ nk, B nk ≠ ∞ := by
    intro nk
    exact (((finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).memLp).sub
      ((finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).memLp)).eLpNorm_ne_top
  have hreal : Filter.Tendsto (fun nk => ENNReal.toReal (B nk)) Filter.atTop (nhds 0) := by
    simpa only [B] using
      tendsto_toReal_eLpNorm_finiteLpW10pSolutionApproximation_pair q m hsigma0 h
  have hB := (ENNReal.tendsto_toReal_zero_iff hBtop).1 hreal
  simpa only [B] using hB

private noncomputable def finiteLpW10pSolutionApproximationLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N : ℕ) :
    Lp ℝ q.exponent (volume.restrict (openCubeSet (originCube d m))) :=
  (finiteLpW10pSolutionApproximation q m hsigma0 h N).memLp.toLp _

private theorem cauchySeq_finiteLpW10pSolutionApproximationLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    CauchySeq (finiteLpW10pSolutionApproximationLp q m hsigma0 h) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
  have hpair := tendsto_eLpNorm_finiteLpW10pSolutionApproximation_pair q m hsigma0 h
  refine hpair.congr' ?_
  filter_upwards [] with nk
  apply eLpNorm_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (finiteLpW10pSolutionApproximation q m hsigma0 h nk.1).memLp,
    MemLp.coeFn_toLp
      (finiteLpW10pSolutionApproximation q m hsigma0 h nk.2).memLp] with x hx hy
  simp only [finiteLpW10pSolutionApproximationLp, Pi.sub_apply]
  rw [hx, hy]

private noncomputable def finiteLpW10pSolutionLimitLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Lp ℝ q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
  letI : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  exact Classical.choose (cauchySeq_tendsto_of_complete
    (cauchySeq_finiteLpW10pSolutionApproximationLp q m hsigma0 h))

private theorem tendsto_finiteLpW10pSolutionApproximationLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (finiteLpW10pSolutionApproximationLp q m hsigma0 h) Filter.atTop
      (nhds (finiteLpW10pSolutionLimitLp q m hsigma0 h)) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete
    (cauchySeq_finiteLpW10pSolutionApproximationLp q m hsigma0 h))

private theorem tendsto_eLpNorm_finiteLpW10pSolutionApproximation_sub_limitLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun N => eLpNorm (fun x =>
      finiteLpW10pSolutionApproximation q m hsigma0 h N x -
        finiteLpW10pSolutionLimitLp q m hsigma0 h x)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop
      (nhds 0) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  have htend := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (finiteLpW10pSolutionApproximationLp q m hsigma0 h)
    (finiteLpW10pSolutionLimitLp q m hsigma0 h)).1
    (tendsto_finiteLpW10pSolutionApproximationLp q m hsigma0 h)
  refine htend.congr' ?_
  filter_upwards [] with N
  apply eLpNorm_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (finiteLpW10pSolutionApproximation q m hsigma0 h N).memLp] with x hx
  simp only [finiteLpW10pSolutionApproximationLp, Pi.sub_apply]
  rw [hx]

/-- The canonical arbitrary-data zero-trace `W^{1,p}_0` solution selected by
completion of the bounded-data approximants. -/
noncomputable def finiteLpW10pSolutionLimit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    W10pFunction (openCubeSet (originCube d m)) q.exponent :=
  W10pFunction.ofTendstoELpNorm q
    (MeasureTheory.Lp.memLp (finiteLpW10pSolutionLimitLp q m hsigma0 h))
    (finiteLpGradientLimit_gradMemLp q m hsigma0 h)
    (finiteLpW10pSolutionApproximation q m hsigma0 h)
    (tendsto_eLpNorm_finiteLpW10pSolutionApproximation_sub_limitLp q m hsigma0 h)
    (fun i => by
      simpa only [finiteLpW10pSolutionApproximation_grad] using
        tendsto_eLpNorm_finiteLpSolutionApproximation_gradCoord_sub_finiteLpGradientLimit
          q m hsigma0 h i)

@[simp] private theorem finiteLpW10pSolutionLimit_toFun
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    (finiteLpW10pSolutionLimit q m hsigma0 h).toFun =
      finiteLpW10pSolutionLimitLp q m hsigma0 h :=
  W10pFunction.ofTendstoELpNorm_toFun _ _ _ _ _ _

@[simp] theorem finiteLpW10pSolutionLimit_grad
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    (finiteLpW10pSolutionLimit q m hsigma0 h).grad =
      finiteLpGradientLimit q m hsigma0 h :=
  W10pFunction.ofTendstoELpNorm_grad _ _ _ _ _ _

/-- The selected bounded-data solution values converge strongly in the raw
cube `L^p` norm to the canonical zero-trace limit. -/
theorem tendsto_eLpNorm_finiteLpW10pSolutionApproximation_sub_limit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Filter.Tendsto (fun N => eLpNorm (fun x =>
      finiteLpW10pSolutionApproximation q m hsigma0 h N x -
        finiteLpW10pSolutionLimit q m hsigma0 h x)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop
      (nhds 0) := by
  simpa only [finiteLpW10pSolutionLimit_toFun] using
    tendsto_eLpNorm_finiteLpW10pSolutionApproximation_sub_limitLp q m hsigma0 h

/-- The selected bounded-data solution gradients converge coordinatewise to
the exact gradient of the canonical zero-trace limit. -/
theorem tendsto_eLpNorm_finiteLpW10pSolutionApproximation_gradCoord_sub_limit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (i : Fin d) :
    Filter.Tendsto (fun N => eLpNorm (fun x =>
      (finiteLpW10pSolutionApproximation q m hsigma0 h N).grad x i -
        (finiteLpW10pSolutionLimit q m hsigma0 h).grad x i)
      q.exponent (volume.restrict (openCubeSet (originCube d m)))) Filter.atTop
      (nhds 0) := by
  simpa only [finiteLpW10pSolutionApproximation_grad,
    finiteLpW10pSolutionLimit_grad] using
    tendsto_eLpNorm_finiteLpSolutionApproximation_gradCoord_sub_finiteLpGradientLimit
      q m hsigma0 h i

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
