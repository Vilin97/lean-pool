/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaCellBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaIntegrationByParts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.FlowTransportTest
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTestSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus

/-! # RelativeError: the transported Laplacian pairing as a Piola pairing -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Torus

theorem classicalSpaceLap_contDiff_three {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (spaceLap f) := by
  unfold spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ 2 (fun x => spaceGrad f x i) := by
    change ContDiff ℝ 2 (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  change ContDiff ℝ 1
    (fun x => fderiv ℝ (fun y => spaceGrad f y i) x (basisVec i))
  exact (hgrad.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem classicalSpaceLap_contDiff_top {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (spaceLap f) := by
  unfold spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => spaceGrad f y i) x (basisVec i))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem classicalSpaceLap_periodic {f : Vec 2 → ℝ}
    (hper : IsZ2Periodic f) : IsZ2Periodic (spaceLap f) := by
  intro k x
  unfold spaceLap
  apply Finset.sum_congr rfl
  intro i hi
  exact AVenhance.Infra.Classical.periodic_spaceGrad_component
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i) i k x

/-- The inverse-flow Piola vector made from a smooth potential is smooth in
space. -/
theorem inverseFlow_piolaVector_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      Matrix.mulVec
        (FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
        (spaceGrad f (X 0 x t))) := by
  let Y : Vec 2 → Vec 2 := fun x => X 0 x t
  let Q : Vec 2 → FaaDiBruno.FlowMatrix := fun x =>
    FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix Y x)
  let W : Vec 2 → Vec 2 := fun x => Matrix.mulVec (Q x) (spaceGrad f (Y x))
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := by
    have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x, (0 : ℝ))) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
        fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hInv.comp hmap
  have hmatrix : ContDiff ℝ (⊤ : ℕ∞) (FaaDiBruno.spatialGradientMatrix Y) := by
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j) i)
    have hYi : ContDiff ℝ (⊤ : ℕ∞) (fun x => Y x i) :=
      (contDiff_apply ℝ ℝ i).comp hY
    have hD := hYi.contDiff_fderiv_apply (m := ∞) (by simp)
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (x, FaaDiBruno.coordinateVector 2 j)) := by
      fun_prop
    have hv := hD.comp hmap
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun z => Y z i) x
        (FaaDiBruno.coordinateVector 2 j)) at hv
    have hfun :
        (fun x => fderiv ℝ (fun z => Y z i) x
          (FaaDiBruno.coordinateVector 2 j)) =
        (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j) i) := by
      funext x
      have hdiff := hY.differentiable (by simp) x
      rw [fderiv_apply hdiff i]
      rfl
    rw [hfun] at hv
    simpa [FaaDiBruno.spatialGradientMatrix] using hv
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (FaaDiBruno.flowCofactorCLM ∘ FaaDiBruno.spatialGradientMatrix Y)
    exact FaaDiBruno.flowCofactorCLM.contDiff.comp hmatrix
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f) := by
    apply contDiff_pi.2
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hgradComp : ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f (Y x)) :=
    hgrad.comp hY
  have hWi : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => W x i) := by
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ∑ j : Fin 2, Q x i j * spaceGrad f (Y x) j)
    apply ContDiff.sum
    intro j hj
    exact ((contDiff_pi.1 (contDiff_pi.1 hQ i) j)).mul
      ((contDiff_pi.1 hgradComp) j)
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := contDiff_pi.2 hWi
  change ContDiff ℝ (⊤ : ℕ∞) W
  exact hW

/-- Continuity of the Piola vector only needs three derivatives of the scalar
potential; the full smoothness theorem above is used when the potential is
smooth. -/
theorem inverseFlow_piolaVector_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 3 f) (t : ℝ) :
    Continuous (fun x =>
      Matrix.mulVec
        (FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
        (spaceGrad f (X 0 x t))) := by
  let Y : Vec 2 → Vec 2 := fun x => X 0 x t
  let Q : Vec 2 → FaaDiBruno.FlowMatrix := fun x =>
    FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix Y x)
  let W : Vec 2 → Vec 2 := fun x => Matrix.mulVec (Q x) (spaceGrad f (Y x))
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := by
    have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x, (0 : ℝ))) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
        fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hInv.comp hmap
  have hmatrix : ContDiff ℝ (⊤ : ℕ∞) (FaaDiBruno.spatialGradientMatrix Y) := by
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j) i)
    have hYi : ContDiff ℝ (⊤ : ℕ∞) (fun x => Y x i) :=
      (contDiff_apply ℝ ℝ i).comp hY
    have hD := hYi.contDiff_fderiv_apply (m := ∞) (by simp)
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (x, FaaDiBruno.coordinateVector 2 j)) := by
      fun_prop
    have hv := hD.comp hmap
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun z => Y z i) x
        (FaaDiBruno.coordinateVector 2 j)) at hv
    have hfun :
        (fun x => fderiv ℝ (fun z => Y z i) x
          (FaaDiBruno.coordinateVector 2 j)) =
        (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j) i) := by
      funext x
      have hdiff := hY.differentiable (by simp) x
      rw [fderiv_apply hdiff i]
      rfl
    rw [hfun] at hv
    simpa [FaaDiBruno.spatialGradientMatrix] using hv
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (FaaDiBruno.flowCofactorCLM ∘ FaaDiBruno.spatialGradientMatrix Y)
    exact FaaDiBruno.flowCofactorCLM.contDiff.comp hmatrix
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hgrad : ContDiff ℝ 0 (spaceGrad f) := by
    apply contDiff_pi.2
    intro i
    change ContDiff ℝ 0 (fun x => fderiv ℝ f x (basisVec i))
    have hD := hf1.fderiv_right (m := 0) (by norm_num)
    exact hD.clm_apply contDiff_const
  have hgradComp : Continuous (fun x => spaceGrad f (Y x)) :=
    hgrad.continuous.comp hY.continuous
  have hQcont : Continuous Q := hQ.continuous
  have hWi : ∀ i : Fin 2, Continuous (fun x => W x i) := by
    intro i
    change Continuous (fun x => ∑ j : Fin 2, Q x i j * spaceGrad f (Y x) j)
    apply continuous_finsetSum
    intro j hj
    have hQi : Continuous (fun x => Q x i) :=
      (continuous_apply i).comp hQcont
    have hQij : Continuous (fun x => Q x i j) :=
      (continuous_apply j).comp hQi
    have hgradj : Continuous (fun x => spaceGrad f (Y x) j) :=
      (continuous_apply j).comp hgradComp
    exact hQij.mul hgradj
  have hWcont : Continuous W := continuous_pi hWi
  change Continuous W
  exact hWcont

/-- The transported test with initial value `-Δf` is the negative divergence
of the inverse-flow Piola vector. Pairing it against a periodic scalar and
integrating by parts gives an exact gradient pairing. -/
theorem inverseFlow_laplacian_pairing_eq_piola
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {u₀ f : Vec 2 → ℝ}
    (hu : ContDiff ℝ 1 u₀) (huper : IsZ2Periodic u₀)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfper : IsZ2Periodic f) (t : ℝ) :
    (∫ x in unitCell 2,
      u₀ x * inverseFlowTransportTest
        (h₀ := fun y => -spaceLap f y) X t x) =
    ∫ x in unitCell 2, vecDot (spaceGrad u₀ x)
      (Matrix.mulVec
        (FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
        (spaceGrad f (X 0 x t))) := by
  let W : Vec 2 → Vec 2 := fun x => Matrix.mulVec
    (FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
    (spaceGrad f (X 0 x t))
  have hWper := inverseFlow_piolaVector_periodic hb hX hfper t
  have hWper' : ∀ i : Fin 2, IsZ2Periodic (fun x => W x i) := by
    intro i k x
    exact congrFun (hWper k x) i
  have hlap := inverseFlow_transportLaplacian hb hX hdiv
    (hf.of_le (by norm_num)) t
  have hWdiff : ContDiff ℝ 1 W :=
    (inverseFlow_piolaVector_contDiff_infty hb hX hf t).of_le
      (by norm_num)
  have hIBP := integral_unitCell_scalar_mul_vecDiv hu hWdiff huper hWper'
  have hpoint (x : Vec 2) :
      inverseFlowTransportTest (h₀ := fun y => -spaceLap f y) X t x =
        -vecDiv W x := by
    dsimp [inverseFlowTransportTest, W]
    rw [hlap x]
  calc
    (∫ x in unitCell 2,
      u₀ x * inverseFlowTransportTest
        (h₀ := fun y => -spaceLap f y) X t x) =
      ∫ x in unitCell 2, u₀ x * (-vecDiv W x) := by
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        change u₀ x * inverseFlowTransportTest
          (h₀ := fun y => -spaceLap f y) X t x =
            u₀ x * (-vecDiv W x)
        exact congrArg (fun z => u₀ x * z) (hpoint x)
    _ = -∫ x in unitCell 2, u₀ x * vecDiv W x := by
      rw [show (fun x => u₀ x * -vecDiv W x) =
        fun x => -(u₀ x * vecDiv W x) by funext x; ring, integral_neg]
    _ = ∫ x in unitCell 2, vecDot (spaceGrad u₀ x) (W x) := by
      simpa [W] using congrArg Neg.neg hIBP

/-- The transported Laplacian test is jointly smooth when its datum is smooth;
the periodicity of its initial datum follows from the periodic Laplacian. -/
theorem inverseFlow_laplacianTransport_contDiff_infty
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry
        (inverseFlowTransportTest (h₀ := fun y => -spaceLap f y) X)) := by
  apply inverseFlowTransportTest_contDiff_infty hb hX
  exact contDiff_neg.comp (classicalSpaceLap_contDiff_top hf)

theorem TransportTracePairing.vecDot_abs_le_sqrt_energy (v w : Vec 2) :
    |vecDot v w| ≤ Real.sqrt (vecNormSq v) * Real.sqrt (vecNormSq w) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 2))
    (fun i => |v i|) (fun i => |w i|)
  have htriangle :
      |∑ i : Fin 2, v i * w i| ≤ ∑ i : Fin 2, |v i| * |w i| := by
    calc
      |∑ i : Fin 2, v i * w i| ≤
          ∑ i : Fin 2, |v i * w i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin 2, |v i| * |w i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
  have hcs' :
      (∑ i : Fin 2, |v i| * |w i|) ≤
        Real.sqrt (vecNormSq v) * Real.sqrt (vecNormSq w) := by
    have hv : (∑ i : Fin 2, |v i| ^ 2) = vecNormSq v := by
      simp [vecNormSq, vecDot, Fin.sum_univ_two, sq_abs]
      ring
    have hw : (∑ i : Fin 2, |w i| ^ 2) = vecNormSq w := by
      simp [vecNormSq, vecDot, Fin.sum_univ_two, sq_abs]
      ring
    calc
      (∑ i : Fin 2, |v i| * |w i|) ≤
          Real.sqrt (∑ i : Fin 2, |v i| ^ 2) *
            Real.sqrt (∑ i : Fin 2, |w i| ^ 2) := hcs
      _ = Real.sqrt (vecNormSq v) * Real.sqrt (vecNormSq w) := by
        rw [hv, hw]
  simpa [vecDot, Fin.sum_univ_two] using htriangle.trans hcs'

/-- Cauchy--Schwarz on the periodic cell for the Euclidean vector energy
`vecNormSq`, despite `Vec` itself carrying the coordinate sup norm. -/
theorem integral_unitCell_vecDot_abs_le
    {F G : Vec 2 → Vec 2} (hF : Continuous F) (hG : Continuous G) :
    |∫ x in unitCell 2, vecDot (F x) (G x)| ≤
      Real.sqrt (∫ x in unitCell 2, vecNormSq (F x)) *
        Real.sqrt (∫ x in unitCell 2, vecNormSq (G x)) := by
  let f : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (F x))
  let g : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (G x))
  have hf : Continuous f := by
    exact Real.continuous_sqrt.comp
      (AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hF)
  have hg : Continuous g := by
    exact Real.continuous_sqrt.comp
      (AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hG)
  have hdot : Continuous (fun x => vecDot (F x) (G x)) := by
    change Continuous (fun x => ∑ i : Fin 2, F x i * G x i)
    exact continuous_finsetSum Finset.univ (fun i hi =>
      (continuous_apply i).comp hF |>.mul ((continuous_apply i).comp hG))
  have hpoint (x : Vec 2) : |vecDot (F x) (G x)| ≤ f x * g x := by
    exact TransportTracePairing.vecDot_abs_le_sqrt_energy (F x) (G x)
  have hAbsInt : IntegrableOn
      (fun x => |vecDot (F x) (G x)|) (unitCell 2) := by
    apply AVenhance.Infra.Classical.continuous_integrableOn_unitCell
    exact hdot.abs
  have hProdInt : IntegrableOn (fun x => f x * g x) (unitCell 2) := by
    apply AVenhance.Infra.Classical.continuous_integrableOn_unitCell
    exact hf.mul hg
  have hmono := setIntegral_mono_on hAbsInt hProdInt
    (Infra.Torus.measurableSet_unitCell 2) (by
      intro x hx
      exact hpoint x)
  have hcs := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
    (μ := volume.restrict (unitCell 2)) (f := f) (g := g)
    (by
      apply AVenhance.Infra.Classical.continuous_integrableOn_unitCell
      exact hf.pow 2)
    (by
      apply AVenhance.Infra.Classical.continuous_integrableOn_unitCell
      exact hg.pow 2)
    hProdInt
  calc
    |∫ x in unitCell 2, vecDot (F x) (G x)| ≤
        ∫ x in unitCell 2, |vecDot (F x) (G x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in unitCell 2, f x * g x := hmono
    _ ≤ Real.sqrt (∫ x in unitCell 2, f x ^ 2) *
        Real.sqrt (∫ x in unitCell 2, g x ^ 2) := by simpa using hcs
    _ = Real.sqrt (∫ x in unitCell 2, vecNormSq (F x)) *
        Real.sqrt (∫ x in unitCell 2, vecNormSq (G x)) := by
      congr 2 <;>
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2) <;>
        intro x hx <;>
        simp [f, g, Real.sq_sqrt, vecNormSq_nonneg]

end AVenhance.Infra.Section5.RelativeError

end
