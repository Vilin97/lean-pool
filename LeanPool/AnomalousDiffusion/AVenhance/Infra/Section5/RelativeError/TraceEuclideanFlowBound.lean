/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.VecDiv
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.VariationalEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC1
public import Mathlib.Analysis.ODE.Gronwall

/-! # RelativeError: Euclidean energy control for divergence-free flow derivatives

The carrier `Vec 2` has the coordinate sup norm, whereas `vecNormSq` is the
sum of coordinate squares. In dimension two, the trace-free condition lets
the latter energy grow at rate at most twice the sup-operator bound.
-/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Section5.RelativeError

theorem TraceEuclideanFlowBound.row_abs_sum_le_of_opNorm
    {A : Vec 2 →L[ℝ] Vec 2} {B : ℝ} (hA : ‖A‖ ≤ B)
    (i : Fin 2) :
    |A (basisVec 0) i| + |A (basisVec 1) i| ≤ B := by
  let p : Vec 2 := fun _ => 1
  let m : Vec 2 := fun i => if i = 0 then 1 else -1
  have hp : ‖p‖ = 1 := by simp [p]
  have hm : ‖m‖ = 1 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro j
      fin_cases j <;> simp [m]
    · have h := (pi_norm_le_iff_of_nonneg (norm_nonneg m)).1 le_rfl 0
      simpa [m] using h
  have hplus : |A p i| ≤ B := by
    have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (A p))).1 le_rfl i
    have h' : ‖A p‖ ≤ B := by
      calc
        ‖A p‖ ≤ ‖A‖ * ‖p‖ := A.le_opNorm p
        _ ≤ B := by rw [hp, mul_one]; exact hA
    rw [Real.norm_eq_abs] at h
    exact h.trans h'
  have hminus : |A m i| ≤ B := by
    have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (A m))).1 le_rfl i
    have h' : ‖A m‖ ≤ B := by
      calc
        ‖A m‖ ≤ ‖A‖ * ‖m‖ := A.le_opNorm m
        _ ≤ B := by rw [hm, mul_one]; exact hA
    rw [Real.norm_eq_abs] at h
    exact h.trans h'
  have hpcoord : A p i = A (basisVec 0) i + A (basisVec 1) i := by
    have heq : p = basisVec 0 + basisVec 1 := by
      ext j
      fin_cases j <;> simp [p, basisVec]
    rw [heq, map_add]
    simp only [Pi.add_apply]
  have hmcoord : A m i = A (basisVec 0) i - A (basisVec 1) i := by
    have heq : m = basisVec 0 - basisVec 1 := by
      ext j
      fin_cases j <;> simp [m, basisVec]
    rw [heq, map_sub]
    simp only [Pi.sub_apply]
  rw [hpcoord] at hplus
  rw [hmcoord] at hminus
  have hplus' := abs_le.mp hplus
  have hminus' := abs_le.mp hminus
  rcases hplus' with ⟨hplusLo, hplusHi⟩
  rcases hminus' with ⟨hminusLo, hminusHi⟩
  rcases le_total 0 (A (basisVec 0) i) with h₀ | h₀
  · rcases le_total 0 (A (basisVec 1) i) with h₁ | h₁
    · calc
        |A (basisVec 0) i| + |A (basisVec 1) i| =
            A (basisVec 0) i + A (basisVec 1) i := by
              rw [abs_of_nonneg h₀, abs_of_nonneg h₁]
        _ ≤ B := hplusHi
    · calc
        |A (basisVec 0) i| + |A (basisVec 1) i| =
            A (basisVec 0) i - A (basisVec 1) i := by
              rw [abs_of_nonneg h₀, abs_of_nonpos h₁]
              ring
        _ ≤ B := hminusHi
  · rcases le_total 0 (A (basisVec 1) i) with h₁ | h₁
    · calc
        |A (basisVec 0) i| + |A (basisVec 1) i| =
            -(A (basisVec 0) i - A (basisVec 1) i) := by
              rw [abs_of_nonpos h₀, abs_of_nonneg h₁]
              ring
        _ ≤ B := by linarith
    · calc
        |A (basisVec 0) i| + |A (basisVec 1) i| =
            -(A (basisVec 0) i + A (basisVec 1) i) := by
              rw [abs_of_nonpos h₀, abs_of_nonpos h₁]
              ring
        _ ≤ B := by linarith

theorem TraceEuclideanFlowBound.traceFree_quadratic_le
    {A : Vec 2 →L[ℝ] Vec 2} {B : ℝ}
    (hA : ‖A‖ ≤ B)
    (htr : A (basisVec 0) 0 + A (basisVec 1) 1 = 0)
    (z : Vec 2) :
    vecDot (A z) z ≤ B * vecNormSq z := by
  let a : ℝ := A (basisVec 0) 0
  let b : ℝ := A (basisVec 1) 0
  let c : ℝ := A (basisVec 0) 1
  have hd : A (basisVec 1) 1 = -a := by
    dsimp [a] at htr ⊢
    linarith
  have hab : |a| + |b| ≤ B := by
    simpa [a, b] using TraceEuclideanFlowBound.row_abs_sum_le_of_opNorm hA 0
  have hac : |a| + |c| ≤ B := by
    have hrow := TraceEuclideanFlowBound.row_abs_sum_le_of_opNorm hA 1
    rw [hd] at hrow
    simpa [a, c, abs_neg, add_comm] using hrow
  have hab' : |b| ≤ B - |a| := by linarith
  have hac' : |c| ≤ B - |a| := by linarith
  have hBminus : 0 ≤ B - |a| := by linarith [hab, abs_nonneg b]
  have hcoords : A z 0 = a * z 0 + b * z 1 := by
    have hz : z = z 0 • basisVec 0 + z 1 • basisVec 1 := by
      ext i
      fin_cases i <;> simp [basisVec]
    have hzA := congrArg (fun w : Vec 2 => A w 0) hz
    calc
      A z 0 = A (z 0 • basisVec 0 + z 1 • basisVec 1) 0 := hzA
      _ = a * z 0 + b * z 1 := by
        rw [map_add, map_smul, map_smul]
        simp only [Pi.add_apply, Pi.smul_apply, a, b]
        ring
  have hcoord1 : A z 1 = c * z 0 - a * z 1 := by
    have hz : z = z 0 • basisVec 0 + z 1 • basisVec 1 := by
      ext i
      fin_cases i <;> simp [basisVec]
    have hzA := congrArg (fun w : Vec 2 => A w 1) hz
    calc
      A z 1 = A (z 0 • basisVec 0 + z 1 • basisVec 1) 1 := hzA
      _ = c * z 0 - a * z 1 := by
        rw [map_add, map_smul, map_smul]
        simp only [Pi.add_apply, Pi.smul_apply, c, hd]
        ring
  have hx : 0 ≤ |z 0| := abs_nonneg _
  have hy : 0 ≤ |z 1| := abs_nonneg _
  have hquad :
      a * (z 0) ^ 2 + (b + c) * (z 0 * z 1) - a * (z 1) ^ 2 ≤
        B * ((z 0) ^ 2 + (z 1) ^ 2) := by
    have habsA : |a| ≤ B := by linarith
    have hbc : |b + c| ≤ 2 * (B - |a|) := by
      calc
        |b + c| ≤ |b| + |c| := abs_add_le _ _
        _ ≤ 2 * (B - |a|) := by linarith
    have hquadUpper :
        a * (z 0) ^ 2 + (b + c) * (z 0 * z 1) - a * (z 1) ^ 2 ≤
          |a| * |(z 0) ^ 2 - (z 1) ^ 2| +
            2 * (B - |a|) * |z 0| * |z 1| := by
      have hdiag : a * ((z 0) ^ 2 - (z 1) ^ 2) ≤
          |a| * |(z 0) ^ 2 - (z 1) ^ 2| := by
        have h₁ : a * ((z 0) ^ 2 - (z 1) ^ 2) ≤
            |a * ((z 0) ^ 2 - (z 1) ^ 2)| := le_abs_self _
        rw [abs_mul] at h₁
        exact h₁
      have hoff : (b + c) * (z 0 * z 1) ≤
          |b + c| * (|z 0| * |z 1|) := by
        have h₁ : (b + c) * (z 0 * z 1) ≤
            |(b + c) * (z 0 * z 1)| := le_abs_self _
        rw [abs_mul, abs_mul] at h₁
        exact h₁
      calc
        a * (z 0) ^ 2 + (b + c) * (z 0 * z 1) - a * (z 1) ^ 2 =
            a * ((z 0) ^ 2 - (z 1) ^ 2) + (b + c) * (z 0 * z 1) := by ring
        _ ≤ |a| * |(z 0) ^ 2 - (z 1) ^ 2| +
              |b + c| * (|z 0| * |z 1|) := add_le_add hdiag hoff
        _ ≤ |a| * |(z 0) ^ 2 - (z 1) ^ 2| +
              2 * (B - |a|) * |z 0| * |z 1| := by
          have hxy' : 0 ≤ |z 0| * |z 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_right hbc hxy']
    by_cases hxy : (z 0) ^ 2 ≤ (z 1) ^ 2
    · have hxy' : |z 0| ≤ |z 1| := by
        apply (sq_le_sq₀ hx hy).1
        simpa only [sq_abs] using hxy
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hquadUpper
      have hfactor :
          B * ((z 0) ^ 2 + (z 1) ^ 2) -
              (|a| * ((z 1) ^ 2 - (z 0) ^ 2) +
                2 * (B - |a|) * |z 0| * |z 1|) =
            (B - |a|) * (|z 1| - |z 0|) ^ 2 + 2 * |a| * (z 0) ^ 2 := by
        nlinarith [sq_abs (z 0), sq_abs (z 1), sq_nonneg (|z 1| - |z 0|)]
      have hnonneg : 0 ≤ (B - |a|) * (|z 1| - |z 0|) ^ 2 +
          2 * |a| * (z 0) ^ 2 := by positivity
      nlinarith only [hquadUpper, hfactor, hnonneg]
    · have hxy' : |z 1| ≤ |z 0| := by
        apply (sq_le_sq₀ hy hx).1
        have hxy'' : (z 1) ^ 2 ≤ (z 0) ^ 2 := le_of_not_ge hxy
        simpa only [sq_abs] using hxy''
      have hxy'' : (z 1) ^ 2 ≤ (z 0) ^ 2 := by nlinarith [sq_abs (z 0), sq_abs (z 1)]
      rw [abs_of_nonneg (sub_nonneg.mpr hxy'')] at hquadUpper
      have hfactor :
          B * ((z 0) ^ 2 + (z 1) ^ 2) -
              (|a| * ((z 0) ^ 2 - (z 1) ^ 2) +
                2 * (B - |a|) * |z 0| * |z 1|) =
            (B - |a|) * (|z 0| - |z 1|) ^ 2 + 2 * |a| * (z 1) ^ 2 := by
        nlinarith [sq_abs (z 0), sq_abs (z 1), sq_nonneg (|z 0| - |z 1|)]
      have hnonneg : 0 ≤ (B - |a|) * (|z 0| - |z 1|) ^ 2 +
          2 * |a| * (z 1) ^ 2 := by positivity
      nlinarith only [hquadUpper, hfactor, hnonneg]
  simp only [vecDot, vecNormSq, Fin.sum_univ_two]
  rw [hcoords, hcoord1]
  nlinarith [hquad]

/-- The divergence-free differential of a two-dimensional vector field has
Euclidean logarithmic norm bounded by its operator norm on `Vec 2`. -/
theorem divergenceFree_spatialDerivative_quadratic_le
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B : ℝ} (hDb : ∀ t x,
      ‖Infra.Flow.jointSpatialFDeriv b t x‖ ≤ B)
    (t : ℝ) (x z : Vec 2) :
    vecDot (Infra.Flow.jointSpatialFDeriv b t x z) z ≤ B * vecNormSq z := by
  let A := Infra.Flow.jointSpatialFDeriv b t x
  have hslice : ContDiff ℝ ∞ (fun y : Vec 2 => b t y) := by
    have hmap : ContDiff ℝ ∞ (fun y : Vec 2 => (t, y)) := by fun_prop
    change ContDiff ℝ ∞ (Function.uncurry b ∘ fun y : Vec 2 => (t, y))
    exact hb.smooth.comp hmap
  have hV : HasFDerivAt (fun y : Vec 2 => b t y) A x := by
    have hdiff : DifferentiableAt ℝ (fun y : Vec 2 => b t y) x :=
      hslice.differentiable (by norm_num) x
    change HasFDerivAt (fun y : Vec 2 => b t y)
      (Infra.Flow.jointSpatialFDeriv b t x) x
    rw [Infra.Flow.jointSpatialFDeriv_eq_slice hb t x]
    exact hdiff.hasFDerivAt
  have hdivFormula : vecDiv (b t) x =
      ∑ i : Fin 2, (A (basisVec i)) i := by
    unfold vecDiv
    apply Finset.sum_congr rfl
    intro i hi
    have hcoord : HasFDerivAt (fun y => b t y i)
        ((ContinuousLinearMap.proj i).comp A) x := by
      exact (ContinuousLinearMap.proj i).hasFDerivAt.comp x hV
    rw [spaceGrad, hcoord.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have htrace : A (basisVec 0) 0 + A (basisVec 1) 1 = 0 := by
    have h := hdiv t x
    rw [hdivFormula, Fin.sum_univ_two] at h
    exact h
  exact TraceEuclideanFlowBound.traceFree_quadratic_le (hDb t x) htrace z

/-- The Euclidean squared norm of a forward flow derivative grows at the
same exponential rate as the divergence-free logarithmic norm. -/
theorem forwardFlow_derivative_vecNormSq_le
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B : ℝ} (hDb : ∀ r y,
      ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {s t : ℝ} (hst : s ≤ t) (x v : Vec 2) :
    vecNormSq (fderiv ℝ (fun y => X t y s) x v) ≤
      vecNormSq v * Real.exp (2 * B * (t - s)) := by
  obtain ⟨V, J, hV, hJ, hderiv⟩ :=
    AVenhance.Infra.Flow.exists_flow_hasFDerivAt_spatial_of_le hb hX x s t hst
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => Infra.Flow.jointSpatialFDeriv b r (X r x s)
  let E : ℝ → ℝ := fun r => vecNormSq (V r v s)
  have hVcont : Continuous (fun r => V r v s) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hV.2 v s r).continuousAt
  have hEcont : Continuous E := by
    have h0 := (continuous_apply 0).comp hVcont
    have h1 := (continuous_apply 1).comp hVcont
    unfold E vecNormSq vecDot
    simp only [Fin.sum_univ_two]
    exact (h0.mul h0).add (h1.mul h1)
  have hEderiv (r : ℝ) : HasDerivAt E
      (2 * vecDot (A r (V r v s)) (V r v s)) r := by
    have h0 : HasDerivAt (fun q => V q v s 0)
        (A r (V r v s) 0) r := by
      have h := (ContinuousLinearMap.proj 0).hasFDerivAt.comp_hasDerivAt
        r (hV.2 v s r)
      simpa [Function.comp_def, A, Infra.Flow.linearizedFieldAlongFlow,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h
    have h1 : HasDerivAt (fun q => V q v s 1)
        (A r (V r v s) 1) r := by
      have h := (ContinuousLinearMap.proj 1).hasFDerivAt.comp_hasDerivAt
        r (hV.2 v s r)
      simpa [Function.comp_def, A, Infra.Flow.linearizedFieldAlongFlow,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h
    have hsum : HasDerivAt
        (fun q => (V q v s 0) ^ 2 + (V q v s 1) ^ 2)
        (2 * (V r v s 0) * A r (V r v s) 0 +
          2 * (V r v s 1) * A r (V r v s) 1) r := by
      have h0sq : HasDerivAt (fun q => (V q v s 0) ^ 2)
          (2 * V r v s 0 * A r (V r v s) 0) r := by
        convert h0.mul h0 using 1
        · ext q
          simp [pow_two]
        · ring
      have h1sq : HasDerivAt (fun q => (V q v s 1) ^ 2)
          (2 * V r v s 1 * A r (V r v s) 1) r := by
        convert h1.mul h1 using 1
        · ext q
          simp [pow_two]
        · ring
      exact h0sq.add h1sq
    have hEval (q : ℝ) :
        E q = (V q v s 0) ^ 2 + (V q v s 1) ^ 2 := by
      simp [E, vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    rw [show E = fun q => (V q v s 0) ^ 2 + (V q v s 1) ^ 2 by
      funext q; exact hEval q]
    convert hsum using 1
    simp [vecDot, Fin.sum_univ_two]
    ring
  have hEbound (r : ℝ) (_hr : r ∈ Set.Ico s t) :
      (2 * vecDot (A r (V r v s)) (V r v s)) ≤ 2 * B * E r := by
    have hquad := divergenceFree_spatialDerivative_quadratic_le
      hb hdiv hDb r (X r x s) (V r v s)
    dsimp [E] at hquad ⊢
    nlinarith [mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 2)]
  have hstart : E s ≤ vecNormSq v := by
    simp [E, hV.1 v s]
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun r => 2 * vecDot (A r (V r v s)) (V r v s))
    (δ := vecNormSq v) (K := 2 * B) (ε := 0) (a := s) (b := t)
    (hEcont.continuousOn) (fun r hr C hC =>
      (hEderiv r).hasDerivWithinAt.liminf_right_slope_le hC)
    hstart (fun r hr => by simpa using hEbound r hr)
  have hEt := hgron t ⟨hst, le_rfl⟩
  rw [gronwallBound_ε0] at hEt
  calc
    vecNormSq (fderiv ℝ (fun y => X t y s) x v) = E t := by
      rw [hderiv.fderiv, hJ v]
    _ ≤ vecNormSq v * Real.exp (2 * B * (t - s)) := by
      simpa [E] using hEt

/-- The Euclidean transpose action, written in the coordinate basis of `Vec 2`.
It is the action that appears on gradients after composing with a map. -/
def euclideanTransposeApply (L : Vec 2 →L[ℝ] Vec 2) (w : Vec 2) : Vec 2 :=
  fun i => ∑ j : Fin 2, L (basisVec i) j * w j

theorem TraceEuclideanFlowBound.vecDot_sq_le (x y : Vec 2) :
    (vecDot x y) ^ 2 ≤ vecNormSq x * vecNormSq y := by
  simp only [vecDot, vecNormSq, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]

theorem TraceEuclideanFlowBound.vecDot_transposeApply_eq
    (L : Vec 2 →L[ℝ] Vec 2) (w z : Vec 2) :
    vecDot (euclideanTransposeApply L w) z = vecDot w (L z) := by
  have hz : z = z 0 • basisVec 0 + z 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  rw [hz, map_add, map_smul]
  simp [vecDot, euclideanTransposeApply, Fin.sum_univ_two, basisVec]
  ring

/-- If a linear map has Euclidean energy norm at most `C`, then so does its
transpose. The proof uses the dual characterization of the Euclidean norm. -/
theorem euclideanTranspose_vecNormSq_le
    (L : Vec 2 →L[ℝ] Vec 2) {C : ℝ}
    (hL : ∀ z, vecNormSq (L z) ≤ C ^ 2 * vecNormSq z) (w : Vec 2) :
    vecNormSq (euclideanTransposeApply L w) ≤ C ^ 2 * vecNormSq w := by
  let y := euclideanTransposeApply L w
  let q := vecNormSq y
  have hq : 0 ≤ q := vecNormSq_nonneg y
  have hnorm : vecDot y y = q := by
    simp [q, vecDot, vecNormSq]
  have hpair : vecDot y y = vecDot w (L y) := by
    simpa [y] using TraceEuclideanFlowBound.vecDot_transposeApply_eq L w y
  have hCS := TraceEuclideanFlowBound.vecDot_sq_le w (L y)
  have hLin := hL y
  change q ≤ C ^ 2 * vecNormSq w
  by_cases hq0 : q = 0
  · rw [hq0]
    exact mul_nonneg (sq_nonneg C) (vecNormSq_nonneg w)
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hCS' : q ^ 2 ≤ vecNormSq w * vecNormSq (L y) := by
      rw [← hnorm, hpair]
      exact hCS
    have hprod : q ^ 2 ≤ (C ^ 2 * vecNormSq w) * q := by
      calc
        q ^ 2 ≤ vecNormSq w * vecNormSq (L y) := hCS'
        _ ≤ vecNormSq w * (C ^ 2 * q) := by
          exact mul_le_mul_of_nonneg_left hLin (vecNormSq_nonneg w)
        _ = (C ^ 2 * vecNormSq w) * q := by ring
    have hresult : q ≤ C ^ 2 * vecNormSq w := by
      by_contra hnot
      have hlt : C ^ 2 * vecNormSq w < q := lt_of_not_ge hnot
      have hgap : 0 < q - C ^ 2 * vecNormSq w := by linarith
      have hbad := mul_pos hqpos hgap
      nlinarith only [hprod, hbad]
    simpa [y, q] using hresult

/-- Reverse-time vector field in the Euclidean trace flow bound. -/
def TraceEuclideanFlowBound.reverseTimeField (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → Vec 2 := fun t x => -b (-t) x

/-- Flow with both times reversed in the Euclidean trace flow bound. -/
def TraceEuclideanFlowBound.reverseTimeFlow (X : ℝ → Vec 2 → ℝ → Vec 2) :
    ℝ → Vec 2 → ℝ → Vec 2 := fun t x s => X (-t) x (-s)

theorem TraceEuclideanFlowBound.reverseTimeField_smoothPeriodic
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b) :
    Infra.Flow.SmoothPeriodicField (TraceEuclideanFlowBound.reverseTimeField b) := by
  refine ⟨?_, ?_⟩
  · change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => -Function.uncurry b (-p.1, p.2))
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by
      fun_prop
    exact contDiff_neg.comp (hb.smooth.comp hmap)
  · intro m k t x
    have h := hb.periodic (-m) k (-t) x
    simpa [TraceEuclideanFlowBound.reverseTimeField, neg_add, add_comm] using congrArg Neg.neg h

theorem TraceEuclideanFlowBound.reverseTimeFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) :
    IsFlow (TraceEuclideanFlowBound.reverseTimeField b) (TraceEuclideanFlowBound.reverseTimeFlow
        X) := by
  constructor
  · intro x s
    exact hX.1 x (-s)
  · intro x s t
    have hbase : HasDerivAt (fun r => X r x (-s))
        (b (0 - t) (X (0 - t) x (-s))) (0 - t) := by
      simpa only [zero_sub] using hX.2 x (-s) (-t)
    simpa only [TraceEuclideanFlowBound.reverseTimeField, TraceEuclideanFlowBound.reverseTimeFlow,
        zero_sub] using
      hbase.comp_const_sub 0 t

theorem TraceEuclideanFlowBound.reverseTimeField_div_free
    {b : ℝ → Vec 2 → Vec 2} (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (r : ℝ) (x : Vec 2) : vecDiv (TraceEuclideanFlowBound.reverseTimeField b r) x = 0 := by
  have h := hdiv (-r) x
  simpa [TraceEuclideanFlowBound.reverseTimeField, vecDiv, spaceGrad, fderiv_neg] using
    congrArg Neg.neg h

theorem TraceEuclideanFlowBound.reverseTimeField_derivBound
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {B : ℝ} (hDb : ∀ r y,
      ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    (r : ℝ) (y : Vec 2) :
    ‖Infra.Flow.jointSpatialFDeriv (TraceEuclideanFlowBound.reverseTimeField b) r y‖ ≤ B := by
  have hbr := TraceEuclideanFlowBound.reverseTimeField_smoothPeriodic hb
  have heq : (fun z : Vec 2 => TraceEuclideanFlowBound.reverseTimeField b r z) =
      fun z => -b (-r) z := rfl
  calc
    ‖Infra.Flow.jointSpatialFDeriv (TraceEuclideanFlowBound.reverseTimeField b) r y‖ =
        ‖fderiv ℝ (fun z => TraceEuclideanFlowBound.reverseTimeField b r z) y‖ := by
          rw [Infra.Flow.jointSpatialFDeriv_eq_slice hbr]
    _ = ‖-fderiv ℝ (fun z => b (-r) z) y‖ := by
          rw [heq]
          change ‖fderiv ℝ (-(fun z => b (-r) z)) y‖ = _
          rw [fderiv_neg]
    _ = ‖Infra.Flow.jointSpatialFDeriv b (-r) y‖ := by
          rw [← Infra.Flow.jointSpatialFDeriv_eq_slice hb]
          simp
    _ ≤ B := hDb (-r) y

/-- The inverse-flow spatial derivative has the same Euclidean energy bound
as the forward derivative. -/
theorem inverseFlow_derivative_vecNormSq_le
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B : ℝ} (hDb : ∀ r y,
      ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {s t : ℝ} (hst : t ≤ s) (x v : Vec 2) :
    vecNormSq (fderiv ℝ (fun y => X t y s) x v) ≤
      vecNormSq v * Real.exp (2 * B * (s - t)) := by
  have hrev := forwardFlow_derivative_vecNormSq_le
    (TraceEuclideanFlowBound.reverseTimeField_smoothPeriodic hb)
        (TraceEuclideanFlowBound.reverseTimeFlow_isFlow hX)
    (TraceEuclideanFlowBound.reverseTimeField_div_free hdiv)
        (TraceEuclideanFlowBound.reverseTimeField_derivBound hb hDb)
    (s := -s) (t := -t) (by linarith) (x := x) (v := v)
  simpa [TraceEuclideanFlowBound.reverseTimeFlow, sub_eq_add_neg, add_comm] using hrev

end AVenhance.Infra.Section5.RelativeError

end
