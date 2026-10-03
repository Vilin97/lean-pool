/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2JointInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Section2FlowIdentities
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.AppB2FieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.ExplicitBarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GradientDeviation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.FlowDnInduction.Remainder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.FlowDnInduction.PositiveTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.FlowDnInduction.SmallTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportTimeAnalyticity

/-! Joint regularity lemmas for the per-scale §2 flow displays. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Construction

theorem Section2FlowRegularityCore.derivativeSup_postCLM_le
    {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    (hL : ‖L‖ ≤ 1) :
    FaaDiBruno.derivativeSup n (fun x => L (f x)) ≤
      FaaDiBruno.derivativeSup n f := by
  classical
  have hpartial (I : Fin n → Fin 2) (x : Vec 2) :
      FaaDiBruno.orderedPartial n (fun y => L (f y)) x I =
        L (FaaDiBruno.orderedPartial n f x I) := by
    let z : FaaDiBruno.VecOne 2 := WithLp.toLp 1 x
    have hcomp := L.iteratedFDeriv_comp_left
      (f := FaaDiBruno.liftVecOne f)
      (FaaDiBruno.contDiff_liftVecOne hf).contDiffAt
      (i := n) le_rfl (x := z)
    have hcomp' :
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne (fun y => L (f y))) z =
          L.compContinuousMultilinearMap
            (iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z) := by
      simpa [FaaDiBruno.liftVecOne, Function.comp_def, z] using hcomp
    have heval := congrArg
      (fun D => D (fun j => FaaDiBruno.coordinateVectorOne 2 (I j))) hcomp'
    simpa [FaaDiBruno.orderedPartial, z] using heval
  unfold FaaDiBruno.derivativeSup
  refine iSup_le fun I => ?_
  calc
    FaaDiBruno.partialSup n (fun x => L (f x)) I ≤
        FaaDiBruno.partialSup n f I := by
      unfold FaaDiBruno.partialSup
      apply eLpNormEssSup_mono_enorm_ae
      filter_upwards with x
      rw [hpartial I x]
      have hnorm : ‖L (FaaDiBruno.orderedPartial n f x I)‖ ≤
          ‖FaaDiBruno.orderedPartial n f x I‖ := by
        calc
          ‖L (FaaDiBruno.orderedPartial n f x I)‖ ≤
              ‖L‖ * ‖FaaDiBruno.orderedPartial n f x I‖ := L.le_opNorm _
          _ ≤ 1 * ‖FaaDiBruno.orderedPartial n f x I‖ :=
            mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = ‖FaaDiBruno.orderedPartial n f x I‖ := by ring
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    _ ≤ FaaDiBruno.derivativeSup n f := le_iSup_of_le I le_rfl

theorem Section2FlowRegularityCore.snorm_postCLM_le
    {n : ℕ} {R : ℝ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    (hL : ‖L‖ ≤ 1) :
    FaaDiBruno.snorm (fun x => L (f x)) n R ≤ FaaDiBruno.snorm f n R := by
  unfold FaaDiBruno.snorm
  gcongr
  exact Section2FlowRegularityCore.derivativeSup_postCLM_le L f hf hL

/-- Negation preserves the coordinate derivative seminorm of a vector field. -/
theorem snorm_neg_eq_vec {n : ℕ} {R : ℝ} (f : Vec 2 → Vec 2) :
    FaaDiBruno.snorm (fun x => -f x) n R = FaaDiBruno.snorm f n R := by
  open FaaDiBruno in
  have hpartial (I : Fin n → Fin 2) :
      partialSup n (fun x => -f x) I = partialSup n f I := by
    unfold partialSup
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    apply essSup_congr_ae
    filter_upwards with x
    have h : orderedPartial n (fun x => -f x) x I = -orderedPartial n f x I := by
      change iteratedFDeriv ℝ n
        (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
          (fun j => coordinateVectorOne 2 (I j)) =
        -iteratedFDeriv ℝ n
          (fun z : VecOne 2 => f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
            (fun j => coordinateVectorOne 2 (I j))
      rw [show (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) =
        -(fun z : VecOne 2 => f ((vecOneEquiv 2) z)) by rfl, iteratedFDeriv_neg]
      rfl
    rw [h]
    simp
  have hderiv : FaaDiBruno.derivativeSup n (fun x => -f x) =
      FaaDiBruno.derivativeSup n f := by
    unfold FaaDiBruno.derivativeSup
    apply le_antisymm
    · refine iSup_le fun I => ?_
      rw [hpartial I]
      exact le_iSup_of_le I le_rfl
    · refine iSup_le fun I => ?_
      rw [← hpartial I]
      exact le_iSup_of_le I le_rfl
  unfold FaaDiBruno.snorm
  rw [hderiv]

/-- Extract a matrix entry as a continuous linear functional. -/
noncomputable def Section2FlowRegularityCore.flowMatrixEntryCLM
    (i j : Fin 2) : FaaDiBruno.FlowMatrix →L[ℝ] ℝ :=
  ContinuousLinearMap.mk
    { toFun := fun A => A i j
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
    (by fun_prop)

theorem Section2FlowRegularityCore.flowMatrixEntryCLM_norm_le (i j : Fin 2) :
    ‖Section2FlowRegularityCore.flowMatrixEntryCLM i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  calc
    ‖Section2FlowRegularityCore.flowMatrixEntryCLM i j A‖ = ‖A i j‖ := rfl
    _ ≤ ‖A i‖ := norm_le_pi_norm _ _
    _ ≤ ‖A‖ := norm_le_pi_norm _ _
    _ = 1 * ‖A‖ := by ring

theorem Section2FlowRegularityCore.flowMatrixBarNorm_le_snorm
    (F : Vec 2 → FaaDiBruno.FlowMatrix) (n : ℕ) (R B : ℝ)
    (hF : ContDiff ℝ n F)
    (hbound : FaaDiBruno.snorm F n R ≤ ENNReal.ofReal B) :
    (⨆ i : Fin 2, ⨆ j : Fin 2,
      AVenhance.barNorm n R (fun x => F x i j)) ≤ ENNReal.ofReal B := by
  refine iSup_le fun i => iSup_le fun j => ?_
  let L := Section2FlowRegularityCore.flowMatrixEntryCLM i j
  let g : Vec 2 → ℝ := fun x => L (F x)
  have hg : ContDiff ℝ n g := L.contDiff.comp hF
  have hfun : (fun x : Vec 2 => F x i j) = g := by
    funext x
    rfl
  calc
    AVenhance.barNorm n R (fun x => F x i j) = FaaDiBruno.snorm g n R := by
      rw [hfun]
      exact AVenhance.Infra.Construction.barNorm_eq_snorm g n R hg
    _ ≤ FaaDiBruno.snorm F n R :=
      Section2FlowRegularityCore.snorm_postCLM_le L F hF
          (Section2FlowRegularityCore.flowMatrixEntryCLM_norm_le i j)
    _ ≤ ENNReal.ofReal B := hbound

/-- Componentwise flow-Jacobian seminorms are controlled by the matrix
gradient seminorm. -/
theorem flowJacobianBarNorm_le_spatialGradient_snorm
    (f : Vec 2 → Vec 2) (n : ℕ) (R B : ℝ)
    (hGrad : ContDiff ℝ n (FaaDiBruno.spatialGradientMatrix f))
    (hbound : FaaDiBruno.snorm (FaaDiBruno.spatialGradientMatrix f) n R ≤
      ENNReal.ofReal B) :
    flowJacobianBarNorm n R (fun x => fderiv ℝ f x) ≤ ENNReal.ofReal B := by
  unfold flowJacobianBarNorm
  refine iSup_le fun i => iSup_le fun j => ?_
  let L := Section2FlowRegularityCore.flowMatrixEntryCLM i j
  let S : Vec 2 → FaaDiBruno.FlowMatrix := FaaDiBruno.spatialGradientMatrix f
  let g : Vec 2 → ℝ := fun x => L (S x)
  have hg : ContDiff ℝ n g := L.contDiff.comp hGrad
  have hentry (x : Vec 2) : g x = (fderiv ℝ f x (basisVec j)) i := by
    simp [g, S, L, Section2FlowRegularityCore.flowMatrixEntryCLM, FaaDiBruno.spatialGradientMatrix,
      FaaDiBruno.coordinateVector, Homogenization.basisVec]
  calc
    AVenhance.barNorm n R (fun x => (fderiv ℝ f x (basisVec j)) i) =
        FaaDiBruno.snorm g n R := by
          have hfun : (fun x => (fderiv ℝ f x (basisVec j)) i) = g := by
            funext x
            exact (hentry x).symm
          rw [hfun]
          exact AVenhance.Infra.Construction.barNorm_eq_snorm g n R hg
    _ ≤ FaaDiBruno.snorm S n R := Section2FlowRegularityCore.snorm_postCLM_le L S hGrad
      (Section2FlowRegularityCore.flowMatrixEntryCLM_norm_le i j)
    _ ≤ ENNReal.ofReal B := hbound

theorem Section2FlowRegularityCore.partialFDeriv_joint_contDiff
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : P × E → F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × E => fderiv ℝ (fun y : E => G (z.1, y)) z.2) := by
  let D : P × E → E →L[ℝ] F := fun z =>
    (fderiv ℝ G z).comp (ContinuousLinearMap.inr ℝ P E)
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := by
    exact (hG.fderiv_right (by simp)).clm_comp contDiff_const
  have hEq (z : P × E) :
      fderiv ℝ (fun y : E => G (z.1, y)) z.2 = D z := by
    rcases z with ⟨p, x⟩
    have htotal : HasFDerivAt G (fderiv ℝ G (p, x)) (p, x) :=
      (hG.differentiable (by simp) (p, x)).hasFDerivAt
    have hcomp := htotal.comp x (hasFDerivAt_prodMk_right p x)
    have hslice : HasFDerivAt (fun y : E => G (p, y)) (D (p, x)) x := by
      simpa [D, Function.comp_def] using hcomp
    simpa using hslice.fderiv
  simpa only [hEq] using hD

/-- Joint all-orders smoothness of a constructed §2 flow. -/
theorem constructionFlow_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ => constructionFlow hseq m p.1 p.2.1 p.2.2) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  simpa [X] using Infra.Flow.flow_joint_contDiff_infty hb hX

/-- Joint all-orders smoothness of the inverse of a constructed §2 flow. -/
theorem constructionFlowInv_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ => constructionFlowInv hseq m p.1 p.2.1 p.2.2) := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
  have heq : (fun p : ℝ × Vec 2 × ℝ =>
      constructionFlowInv hseq m p.1 p.2.1 p.2.2) =
      (fun p => X p.2.2 p.2.1 p.1) := by
    funext p
    simp [constructionFlowInv, constructionFlow, AVenhance.flowInv, X]
  rw [heq]
  exact hInv

/-- The forward spatial Jacobian is jointly smooth in its start time,
increment, and evaluation point. -/
theorem Section2FlowRegularityCore.constructionFlowJacobian_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionFlowJacobian hseq m p.1.2 p.1.1 p.2) := by
  have hX := constructionFlow_joint_smooth hseq m
  let G : (ℝ × ℝ) × Vec 2 → Vec 2 := fun p =>
    constructionFlow hseq m (p.1.1 + p.1.2) p.2 p.1.1
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        (p.1.1 + p.1.2, p.2, p.1.1)) := by
    fun_prop
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    simpa only [Function.comp_def] using hX.comp hmap
  have hpartial := Section2FlowRegularityCore.partialFDeriv_joint_contDiff G hG
  have heq (p : (ℝ × ℝ) × Vec 2) :
      fderiv ℝ (fun y : Vec 2 => G (p.1, y)) p.2 =
        constructionFlowJacobian hseq m p.1.2 p.1.1 p.2 := by
    simp [G, constructionFlowJacobian, constructionFlow]
  simpa only [heq] using hpartial

theorem Section2FlowRegularityCore.constructionFlowInvJacobian_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionFlowInvJacobian hseq m p.1.2 p.1.1 p.2) := by
  have hInv := constructionFlowInv_joint_smooth hseq m
  let G : (ℝ × ℝ) × Vec 2 → Vec 2 := fun p =>
    constructionFlowInv hseq m (p.1.1 + p.1.2) p.2 p.1.1
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 => (p.1.1 + p.1.2, p.2, p.1.1)) := by
    fun_prop
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    simpa only [Function.comp_def] using hInv.comp hmap
  have hpartial := Section2FlowRegularityCore.partialFDeriv_joint_contDiff G hG
  have heq (p : (ℝ × ℝ) × Vec 2) :
      fderiv ℝ (fun y : Vec 2 => G (p.1, y)) p.2 =
        constructionFlowInvJacobian hseq m p.1.2 p.1.1 p.2 := by
    simp [G, constructionFlowInvJacobian]
  simpa only [heq] using hpartial

/-- Time-translate a flow and its vector field by the same base time. -/
theorem constructionFlow_shift_isFlow
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) (s : ℝ) :
    IsFlow (fun t x => b (s + t) x)
      (fun t x r => X (s + t) x (s + r)) := by
  refine ⟨?_, ?_⟩
  · intro x r
    exact hX.1 x (s + r)
  · intro x r t
    have hbase : HasDerivAt (fun z => X z x (s + r))
        (b (t + s) (X (t + s) x (s + r))) (t + s) := by
      simpa [add_comm] using hX.2 x (s + r) (s + t)
    have hshifted := hbase.comp_add_const t s
    convert hshifted using 1 <;> simp [add_comm]

/-- The composed Jacobian is jointly smooth in the two flow times and space. -/
theorem Section2FlowRegularityCore.constructionComposedFlowJacobian_joint_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2) := by
  have hJ := Section2FlowRegularityCore.constructionFlowJacobian_joint_smooth hseq m
  have hInv := constructionFlowInv_joint_smooth hseq m
  let H : (ℝ × ℝ) × Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun p =>
    constructionFlowJacobian hseq m p.1.2 p.1.1
      (constructionFlowInv hseq m (p.1.1 + p.1.2) p.2 p.1.1)
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        ((p.1.1, p.1.2),
          constructionFlowInv hseq m (p.1.1 + p.1.2) p.2 p.1.1)) := by
    have hinv : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × ℝ) × Vec 2 =>
          constructionFlowInv hseq m (p.1.1 + p.1.2) p.2 p.1.1) := by
      have hm : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (ℝ × ℝ) × Vec 2 => (p.1.1 + p.1.2, p.2, p.1.1)) := by
        fun_prop
      have hcomp := hInv.comp hm
      simpa only [Function.comp_def] using hcomp
    exact contDiff_fst.prodMk hinv
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    simpa only [H, Function.comp_def] using hJ.comp hmap
  have heq (p : (ℝ × ℝ) × Vec 2) :
      H p = constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2 := by
    rfl
  have hfun : H = (fun p : (ℝ × ℝ) × Vec 2 =>
      constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2) := by
    funext p
    exact heq p
  rw [← hfun]
  exact hH

/-- Smooth spatial representative required when evaluating the composed
Jacobian seminorm. -/
theorem section2_composed_jacobian_smooth
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => constructionComposedFlowJacobian hseq m s t x) := by
  have hComp := Section2FlowRegularityCore.constructionComposedFlowJacobian_joint_smooth (hseq :=
      hseq) m
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => ((s, t), x)) := by fun_prop
  have h := hComp.comp hmap
  simpa only [Function.comp_def] using h

/-- The entries in the composed Jacobian are differentiable in target time. -/
theorem section2_material_jacobian_time_diff
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (s t : ℝ)
    (i j : Fin 2) (x : Vec 2) :
    DifferentiableAt ℝ
      (fun r => constructionComposedFlowJacobian hseq m s r x (basisVec j) i) t := by
  have hComp := Section2FlowRegularityCore.constructionComposedFlowJacobian_joint_smooth (hseq :=
      hseq) m
  have hentry : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2
          (basisVec j) i) := by
    exact (contDiff_apply ℝ ℝ i).comp (hComp.clm_apply contDiff_const)
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => ((s, r), x)) := by fun_prop
  have h := hentry.comp hmap
  have hEq : (fun r : ℝ =>
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2
          (basisVec j) i) ((s, r), x)) =
      (fun r => constructionComposedFlowJacobian hseq m s r x
        (basisVec j) i) := by
    funext r
    rfl
  have hd := (h.contDiffAt (x := t)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (fun r : ℝ =>
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionComposedFlowJacobian hseq m p.1.1 p.1.2 p.2
          (basisVec j) i) ((s, r), x)) t := by
    simpa only [Function.comp_def] using hd
  rw [hEq] at hd'
  exact hd'

/-- The inverse-flow spatial Jacobian is differentiable in target time. -/
theorem section2_inverse_jacobian_time_diff
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (m : ℕ) (t s : ℝ) (x : Vec 2) :
    DifferentiableAt ℝ (fun r => constructionFlowInvJacobian hseq m r s x) t := by
  have hJ := Section2FlowRegularityCore.constructionFlowInvJacobian_joint_smooth hseq m
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : ℝ => ((s, r), x)) := by fun_prop
  have h := hJ.comp hmap
  have hEq : (fun r : ℝ =>
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionFlowInvJacobian hseq m p.1.2 p.1.1 p.2) ((s, r), x)) =
      (fun r => constructionFlowInvJacobian hseq m r s x) := by
    funext r
    rfl
  have hd := (h.contDiffAt (x := t)).differentiableAt (by simp)
  have hd' : DifferentiableAt ℝ (fun r : ℝ =>
      (fun p : (ℝ × ℝ) × Vec 2 =>
        constructionFlowInvJacobian hseq m p.1.2 p.1.1 p.2) ((s, r), x)) t := by
    simpa only [Function.comp_def] using hd
  rw [hEq] at hd'
  exact hd'

/-- The paper's first-derivative flow closeness estimate follows from the
current scale's induction bound. The previous-scale adapter below obtains
that bound through the already-proved Section 2 induction step. -/
theorem Section2FlowRegularityCore.section2_flow_close_from_current_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (m : ℕ) (hcurrent : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) (x : Vec 2) :
    ‖constructionFlowJacobian hseq m t s x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4 := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  let Rm : ℝ := R m
  let Mm : ℝ := M m
  let Cf : ℝ := Mm / Rm
  have hRm : 0 < Rm := by dsimp [Rm]; exact section2_radius_pos hscales m
  have hMm : 0 < Mm := by dsimp [Mm]; exact section2_amplitude_pos hscales m
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hMbound : Mm ≤ 2 ^ 19 * a β I.Λ m := by
    dsimp [Mm]
    exact full_amplitude_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R M hscales.radius_zero hscales.amplitude_zero
      hscales.radius_step hscales.amplitude_step m
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hfield : ∀ r, FaaDiBruno.snorm (b r) 1 Rm ≤ ENNReal.ofReal Cf := by
    intro r
    have hs := section2_streamVel_snorm_bound (hseq := hseq)
      (hprev := hcurrent) (m := m) (n := 1) (by norm_num) hRm hMm r
    simpa [b, Rm, Mm, Cf] using hs
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hDb := Infra.Flow.jointSpatialFDeriv_bound_of_snorm hb hCf hRm hfield
  have hLnonneg : 0 ≤ Mm / 2 := by positivity
  have hDb' : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ Mm / 2 := by
    intro r y
    have hd := hDb r y
    have heq : 2 * Cf * Rm / 4 = Mm / 2 := by
      dsimp [Cf, Rm, Mm]
      calc
        2 * (M m / R m) * R m / 4 = (M m / R m) * R m / 2 := by ring
        _ = M m / 2 := by rw [div_mul_cancel₀ _ (ne_of_gt hRm)]
    rw [heq] at hd
    simpa [Mm] using hd
  have htimeSmall : (Mm / 2) * |(s + t) - s| ≤ 1 := by
    have hma : Mm * (a β I.Λ m)⁻¹ ≤ 2 ^ 19 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ ha).2
      dsimp [Mm] at hMbound
      nlinarith [hMbound]
    have htM : (Mm / 2) * |t| ≤
        (Mm / 2) * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have htM' : (Mm / 2) * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) ≤ 1 := by
      have hpow : (2 : ℝ) ^ (-25 : ℤ) = 1 / 2 ^ 25 := by norm_num
      rw [hpow]
      have hfactor : (Mm / 2) * ((1 / 2 ^ 25) * (a β I.Λ m)⁻¹) =
          (Mm * (a β I.Λ m)⁻¹) / 2 ^ 26 := by ring
      rw [hfactor]
      have hbound : (2 : ℝ) ^ 19 / (2 : ℝ) ^ 26 ≤ 1 := by norm_num
      exact (div_le_div_of_nonneg_right hma (by positivity)).trans hbound
    have habs : |(s + t) - s| = |t| := by congr 1; ring
    rw [habs]
    exact htM.trans htM'
  have hdev := Infra.Flow.flow_fderiv_deviation_of_small_time hb hX
    hLnonneg hDb' s (s + t) x htimeSmall
  have hdev' :
      ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ Mm * |t| := by
    have habs : |(s + t) - s| = |t| := by congr 1; ring
    rw [habs] at hdev
    have hdevBound : 2 * (Mm / 2) * |t| = Mm * |t| := by ring
    rw [hdevBound] at hdev
    have hid : (1 : Vec 2 →L[ℝ] Vec 2) = ContinuousLinearMap.id ℝ (Vec 2) := by
      ext y i
      simp
    simpa [constructionFlowJacobian, X, constructionFlow, habs, hid] using hdev
  have hnorm : Mm * |t| ≤ 2 ^ 23 * |t| * a β I.Λ m := by
    calc
      Mm * |t| ≤ (2 ^ 19 * a β I.Λ m) * |t| :=
        mul_le_mul_of_nonneg_right hMbound (abs_nonneg t)
      _ ≤ 2 ^ 23 * |t| * a β I.Λ m := by nlinarith [mul_nonneg (abs_nonneg t) ha.le]
  have hsmall : 2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4 := by
    have ht' := mul_le_mul_of_nonneg_right ht ha.le
    have hpow : (2 : ℝ) ^ (-25 : ℤ) = 1 / 2 ^ 25 := by norm_num
    rw [hpow] at ht'
    have hmul : |t| * (a β I.Λ m) ≤ (1 / 2 ^ 25) := by
      calc
        |t| * a β I.Λ m ≤ (1 / 2 ^ 25 * (a β I.Λ m)⁻¹) * a β I.Λ m := by
          nlinarith [ht']
        _ = 1 / 2 ^ 25 := by field_simp [ha.ne']
    calc
      2 ^ 23 * |t| * a β I.Λ m = 2 ^ 23 * (|t| * a β I.Λ m) := by ring
      _ ≤ 2 ^ 23 * (1 / 2 ^ 25) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = 1 / 4 := by norm_num
  exact ⟨hdev'.trans hnorm, hsmall⟩

/-- `flow_close` in `Section2FlowBoundsAtScale`, derived from the preceding
induction hypothesis and the Section 2 recursion. -/
theorem section2_flow_close_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (x : Vec 2) :
    ‖constructionFlowJacobian hseq m t s x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4 := by
  exact Section2FlowRegularityCore.section2_flow_close_from_current_induction hscales m
    (section2_stream_induction_step hscales happB2 m hm hprev) s t ht x

theorem Section2FlowRegularityCore.flowMatrixCofactor_add_identity_local (A :
    FaaDiBruno.FlowMatrix) :
    FaaDiBruno.flowMatrixCofactorTranspose
        (fun i j => (if i = j then (1 : ℝ) else 0) + A i j) =
      fun i j => (if i = j then (1 : ℝ) else 0) +
        FaaDiBruno.flowMatrixCofactorTranspose A i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FaaDiBruno.flowMatrixCofactorTranspose]

private theorem composed_flow_jacobian_matrixEntry1 :
  ∀ {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ} (m : ℕ) (s t : ℝ),
    let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m);
    let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m;
    let bShift : ℝ → Vec 2 → Vec 2 := fun u x => b (s + u) x;
    let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
      fun u x r => X (s + u) x (s + r);
    Flow.SmoothPeriodicField bShift →
      IsFlow bShift XShift →
        (∀ (u : ℝ) (x : Vec 2), Flow.spatialDivergence bShift u x = 0) →
          let disp : Vec 2 → Vec 2 := fun x => XShift 0 x t - x;
          ContDiff ℝ ∞ disp →
            ∀ (x : Vec 2) (i j : Fin 2),
              (constructionComposedFlowJacobian hseq m s t x - ContinuousLinearMap.id ℝ (Vec 2))
                  (basisVec j) i =
                FaaDiBruno.flowCofactorCLM (FaaDiBruno.spatialGradientMatrix disp x) i j
    := by
  intro β I Φ hseq m s t b X bShift XShift hbShift hXShift hdiv disp hdispSmooth x i j
  have hcof := FaaDiBruno.flow_spatialGradientMatrix_composed_inverse_eq_cofactor
    hbShift hXShift hdiv t x
  have hDidentity : FaaDiBruno.spatialGradientMatrix
      (fun y : Vec 2 => XShift 0 y t) x =
      fun k l => (if k = l then (1 : ℝ) else 0) +
        FaaDiBruno.spatialGradientMatrix disp x k l := by
    have hdecomp : (fun y : Vec 2 => XShift 0 y t) = disp + id := by
      funext y
      simp [disp]
    have hderiv := congrArg (fun f : Vec 2 → Vec 2 => fderiv ℝ f x) hdecomp
    rw [fderiv_add (hdispSmooth.differentiable (by simp) x)
      (differentiable_id x), fderiv_id] at hderiv
    ext k l
    have hentry := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 =>
      L (FaaDiBruno.coordinateVector 2 l) k) hderiv
    have hbasis : (ContinuousLinearMap.id ℝ (Vec 2))
        (FaaDiBruno.coordinateVector 2 l) k = if k = l then (1 : ℝ) else 0 := by
      simp [FaaDiBruno.coordinateVector, Pi.single_apply]
    calc
      _ = (fderiv ℝ disp x) (FaaDiBruno.coordinateVector 2 l) k +
          (ContinuousLinearMap.id ℝ (Vec 2))
            (FaaDiBruno.coordinateVector 2 l) k := by
        exact hentry
      _ = (if k = l then (1 : ℝ) else 0) +
          (fderiv ℝ disp x) (FaaDiBruno.coordinateVector 2 l) k := by
        rw [hbasis]
        ring
      _ = (if k = l then (1 : ℝ) else 0) +
          FaaDiBruno.spatialGradientMatrix disp x k l := by
        rfl
  have hcof' := hcof
  rw [hDidentity, Section2FlowRegularityCore.flowMatrixCofactor_add_identity_local] at hcof'
  have hentry : (constructionComposedFlowJacobian hseq m s t x)
      (basisVec j) i =
      (if i = j then (1 : ℝ) else 0) +
        FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix disp x) i j := by
    have hcomposed : constructionComposedFlowJacobian hseq m s t x =
        fderiv ℝ (fun y : Vec 2 => XShift t y 0) (XShift 0 x t) := by
      have hinv : constructionFlowInv hseq m (s + t) x s = XShift 0 x t := by
        simp [constructionFlowInv, constructionFlow, XShift, X, AVenhance.flowInv]
      have hforward : (fun y : Vec 2 => constructionFlow hseq m (s + t) y s) =
          (fun y => XShift t y 0) := by
        funext y
        simp [XShift, X, add_zero]
      dsimp [constructionComposedFlowJacobian, constructionFlowJacobian]
      rw [hinv, hforward]
    rw [hcomposed]
    have hmatrix := congrFun (congrFun hcof' i) j
    simpa [FaaDiBruno.spatialGradientMatrix, FaaDiBruno.coordinateVector,
      basisVec, Pi.single_apply, eq_comm] using hmatrix
  change (constructionComposedFlowJacobian hseq m s t x (basisVec j) i) -
      (ContinuousLinearMap.id ℝ (Vec 2) (basisVec j)) i = _
  rw [hentry]
  have hid : (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i =
      if i = j then (1 : ℝ) else 0 := by
    simp [Homogenization.basisVec, Pi.single_apply]
  rw [hid]
  simp [FaaDiBruno.flowCofactorCLM, FaaDiBruno.flowMatrixCofactorTranspose]

private theorem composed_flow_jacobian_RpaperTarget2 :
  ∀ {β : ℝ} {I : Ingredients β} {R M : ℕ → ℝ} (m : ℕ) (t : ℝ),
    let Rm : ℝ := R m;
    let Mm : ℝ := M m;
    let Cf : ℝ := Mm / Rm;
    0 < Rm →
      0 < Mm →
        0 < epsilon β I.Λ m →
          let Rpaper : ℝ := Rm * (1 + 8 * |t| * Cf * Rm) ^ 2;
          let Rtarget : ℝ := 2 ^ 10 * (epsilon β I.Λ m)⁻¹;
          1 + 8 * |t| * Cf * Rm ≤ 9 / 8 → Rm ≤ 131 * (epsilon β I.Λ m)⁻¹ → Rpaper ≤ Rtarget
    := by
  intro β I R M m t Rm Mm Cf hRm hMm he Rpaper Rtarget hfactor hR131
  dsimp [Rpaper, Rtarget]
  calc
    R m * (1 + 8 * |t| * Cf * Rm) ^ 2 ≤ Rm * (9 / 8) ^ 2 :=
      mul_le_mul_of_nonneg_left (by
        have hlow : 0 ≤ 1 + 8 * |t| * Cf * Rm := by positivity
        have hgap : 0 ≤ 9 / 8 - (1 + 8 * |t| * Cf * Rm) := sub_nonneg.mpr hfactor
        have hsum : 0 ≤ 9 / 8 + (1 + 8 * |t| * Cf * Rm) := by positivity
        nlinarith [mul_nonneg hgap hsum]) hRm.le
    _ ≤ 131 * (epsilon β I.Λ m)⁻¹ * (9 / 8) ^ 2 :=
      mul_le_mul_of_nonneg_right hR131 (sq_nonneg _)
    _ ≤ 2 ^ 10 * (epsilon β I.Λ m)⁻¹ := by
      have hinv : 0 ≤ (epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr he.le
      nlinarith [hinv]

private theorem composed_flow_jacobian_conclusion1 :
  ∀ {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ},
    Section2Scales I R M →
      ∀ (m n : ℕ),
        1 ≤ m →
          Section2StreamInductionHypothesis (Φ := Φ) R M m →
            ∀ (s t : ℝ),
              let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m);
              let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m;
              let Rm : ℝ := R m;
              let Mm : ℝ := M m;
              let Cf : ℝ := Mm / Rm;
              0 < Rm →
                0 < Mm →
                  0 < epsilon β I.Λ m →
                    0 < Cf →
                      Mm * |t| ≤ 1 / 64 →
                        Cf * Rm = Mm →
                          |t| ≤ 1 / (8 * Cf * Rm) →
                            let bShift : ℝ → Vec 2 → Vec 2 := fun u x => b (s + u) x;
                            let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
                              fun u x r => X (s + u) x (s + r);
                            Flow.SmoothPeriodicField bShift →
                              IsFlow bShift XShift →
                                (ContDiff ℝ ∞ fun (p : (ℝ × Vec 2) × ℝ) => XShift p.1.1 p.1.2 p.2) →
                                  (∀ (u : ℝ) (x : Vec 2), Flow.spatialDivergence bShift u x = 0) →
                                    (flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹) fun (x :
                                        Vec 2) =>
                                        constructionComposedFlowJacobian hseq m s t x -
                                          ContinuousLinearMap.id ℝ (Vec 2)) ≤
                                      ENNReal.ofReal 40
    := by
  intro β I Φ hseq R M hscales m n hm hcurrent s t b X Rm Mm Cf hRm hMm he hCf hMtime hCfRm
      hpaperTime bShift XShift hbShift hXShift hXShiftSmooth hdiv
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := section2_streamVel_snorm_bound (hseq := hseq)
      (hprev := hcurrent) (m := m) (n := k) hk hRm hMm (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  have hY := FaaDiBruno.flow_inverse_displacement_isTransportSolution_of_jointSmooth
    hbShift hXShift hXShiftSmooth
  have hnegSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun u x => -bShift u x)) := by
    convert contDiff_neg.comp hbShift.smooth using 1
    rfl
  have hGfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (fun x => -bShift u x) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    rw [snorm_neg_eq_vec]
    exact hBfield u k hk hkn
  have hdisplacementGradient := FaaDiBruno.transportSolution_gradient_snorm_equalRadius
    (N := n + 1) (n := n) (by omega) hY hbShift.smooth hnegSmooth hXShift
    hCf hCf.le hRm hBfield hGfield hpaperTime
  let Rpaper : ℝ := Rm * (1 + 8 * |t| * Cf * Rm) ^ 2
  let Rtarget : ℝ := 2 ^ 10 * (epsilon β I.Λ m)⁻¹
  have hpaperPositive : 0 < Rpaper := by dsimp [Rpaper]; positivity
  have hfactor : 1 + 8 * |t| * Cf * Rm ≤ 9 / 8 := by
    rw [show 8 * |t| * Cf * Rm = 8 * (Mm * |t|) by rw [← hCfRm]; ring]
    nlinarith [hMtime]
  have hRtargetPositive : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hR131 : Rm ≤ 131 * (epsilon β I.Λ m)⁻¹ := by
    dsimp [Rm]
    have hr := radius_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R hscales.radius_zero hscales.radius_step (m := m) hm
    simpa only [show (3 : ℝ) + (2 : ℝ) ^ 7 = 131 by norm_num] using hr
  have hRpaperTarget : Rpaper ≤ Rtarget := by
    exact @composed_flow_jacobian_RpaperTarget2 β I R M m t hRm hMm he hfactor hR131
  let disp : Vec 2 → Vec 2 := fun x => XShift 0 x t - x
  have hdispSmooth : ContDiff ℝ (⊤ : ℕ∞) disp := by
    have hslice : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => XShift 0 x t) := by
      have hshiftMap : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : Vec 2 => (((0 : ℝ), x), t)) := by fun_prop
      exact hXShiftSmooth.comp hshiftMap
    simpa [disp] using hslice.sub contDiff_id
  have hD : ContDiff ℝ (⊤ : ℕ∞)
      (FaaDiBruno.spatialGradientMatrix disp) := by
    unfold FaaDiBruno.spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => fderiv ℝ disp x (FaaDiBruno.coordinateVector 2 j)) :=
      hdispSmooth.fderiv_right (by simp) |>.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp hcolumn
  have hDfinite : ContDiff ℝ n (FaaDiBruno.spatialGradientMatrix disp) :=
    hD.of_le (by simp)
  have hpaper' : FaaDiBruno.snorm (FaaDiBruno.spatialGradientMatrix disp) n Rpaper ≤
      ENNReal.ofReal 8 := by
    have hratio : 8 * Cf / Cf = 8 := by field_simp [ne_of_gt hCf]
    rw [hratio] at hdisplacementGradient
    simpa [disp, XShift, Rpaper, X] using hdisplacementGradient
  have hDtarget : FaaDiBruno.snorm (FaaDiBruno.spatialGradientMatrix disp) n Rtarget ≤
      ENNReal.ofReal 8 :=
    FaaDiBruno.snorm_le_of_radius_le _ hpaperPositive hRtargetPositive hRpaperTarget
      (by norm_num) hpaper'
  have hcofactorBound : FaaDiBruno.snorm
      (fun x => FaaDiBruno.flowCofactorCLM
        (FaaDiBruno.spatialGradientMatrix disp x)) n Rtarget ≤ ENNReal.ofReal 8 := by
    exact Section2FlowRegularityCore.snorm_postCLM_le FaaDiBruno.flowCofactorCLM
      (FaaDiBruno.spatialGradientMatrix disp) hDfinite
      FaaDiBruno.flowCofactorCLM_norm_le |>.trans hDtarget
  have hmatrixEntry : ∀ x i j,
      (constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i =
        FaaDiBruno.flowCofactorCLM
          (FaaDiBruno.spatialGradientMatrix disp x) i j := by
    exact @composed_flow_jacobian_matrixEntry1 β I Φ hseq m s t hbShift hXShift hdiv hdispSmooth
  have hbar := Section2FlowRegularityCore.flowMatrixBarNorm_le_snorm
    (fun x => FaaDiBruno.flowCofactorCLM
      (FaaDiBruno.spatialGradientMatrix disp x)) n Rtarget 8
    ((contDiff_const.clm_apply hD).of_le (by simp)) hcofactorBound
  unfold flowJacobianBarNorm
  refine iSup_le fun i => iSup_le fun j => ?_
  have hfun : (fun x =>
      (constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i) =
      (fun x => FaaDiBruno.flowCofactorCLM
        (FaaDiBruno.spatialGradientMatrix disp x) i j) := by
    funext x
    exact hmatrixEntry x i j
  rw [hfun]
  have hbar' : (⨆ i : Fin 2, ⨆ j : Fin 2,
      AVenhance.barNorm n Rtarget
        (fun x => FaaDiBruno.flowCofactorCLM
          (FaaDiBruno.spatialGradientMatrix disp x) i j)) ≤ ENNReal.ofReal 40 := by
    exact hbar.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hbar'' : (⨆ i : Fin 2, ⨆ j : Fin 2,
      AVenhance.barNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
        (fun x => FaaDiBruno.flowCofactorCLM
          (FaaDiBruno.spatialGradientMatrix disp x) i j)) ≤ ENNReal.ofReal 40 := by
    simpa [Rtarget] using hbar'
  have hinner : AVenhance.barNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => FaaDiBruno.flowCofactorCLM
        (FaaDiBruno.spatialGradientMatrix disp x) i j) ≤
      ⨆ j' : Fin 2, AVenhance.barNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
        (fun x => FaaDiBruno.flowCofactorCLM
          (FaaDiBruno.spatialGradientMatrix disp x) i j') :=
    le_iSup_of_le j (show _ ≤ _ from le_rfl)
  have houter : AVenhance.barNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => FaaDiBruno.flowCofactorCLM
        (FaaDiBruno.spatialGradientMatrix disp x) i j) ≤
      ⨆ i' : Fin 2, ⨆ j' : Fin 2,
        AVenhance.barNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
          (fun x => FaaDiBruno.flowCofactorCLM
            (FaaDiBruno.spatialGradientMatrix disp x) i' j') :=
    le_iSup_of_le i hinner
  exact houter.trans hbar''

/-- The composed Jacobian minus identity is the cofactor of the inverse-flow
displacement gradient. The corrected equal-radius transport estimate therefore
gives the consumed `flow_jacobian_composed` display. -/
theorem Section2FlowRegularityCore.section2_flow_jacobian_composed_from_current_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (m n : ℕ) (hm : 1 ≤ m)
    (hcurrent : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :
    flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40 := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  let Rm : ℝ := R m
  let Mm : ℝ := M m
  let Cf : ℝ := Mm / Rm
  have hRm : 0 < Rm := by dsimp [Rm]; exact section2_radius_pos hscales m
  have hMm : 0 < Mm := by dsimp [Mm]; exact section2_amplitude_pos hscales m
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hMbound : Mm ≤ 2 ^ 19 * a β I.Λ m := by
    dsimp [Mm]
    exact full_amplitude_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R M hscales.radius_zero hscales.amplitude_zero
      hscales.radius_step hscales.amplitude_step m
  have hma : Mm * (a β I.Λ m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)).2
    dsimp [Mm] at hMbound
    nlinarith [hMbound]
  have hMtime : Mm * |t| ≤ 1 / 64 := by
    calc
      Mm * |t| ≤ Mm * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left ht hMm.le
      _ = 2 ^ (-25 : ℤ) * (Mm * (a β I.Λ m)⁻¹) := by ring
      _ ≤ 2 ^ (-25 : ℤ) * 2 ^ 19 :=
        mul_le_mul_of_nonneg_left hma (by positivity)
      _ = 1 / 64 := by norm_num
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) := mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  let bShift : ℝ → Vec 2 → Vec 2 := fun u x => b (s + u) x
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u x r => X (s + u) x (s + r)
  have hbShift : Infra.Flow.SmoothPeriodicField bShift := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
      change ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro k ell r x
      dsimp [bShift]
      simpa [add_assoc] using hb.periodic k ell (s + r) x
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using constructionFlow_shift_isFlow hX s
  have hXjoint := constructionFlow_joint_smooth hseq m
  have hXShiftSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Vec 2) × ℝ => XShift p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × Vec 2) × ℝ =>
          (s + p.1.1, p.1.2, s + p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
        (fun p : (ℝ × Vec 2) × ℝ => (s + p.1.1, p.1.2, s + p.2)))
    exact hXjoint.comp hmap
  have hdiv : ∀ u x, Infra.Flow.spatialDivergence bShift u x = 0 := by
    intro u x
    have hshiftDeriv : Infra.Flow.jointSpatialFDeriv bShift u x =
        Infra.Flow.jointSpatialFDeriv b (s + u) x := by
      rw [Infra.Flow.jointSpatialFDeriv_eq_slice hbShift,
        Infra.Flow.jointSpatialFDeriv_eq_slice hb]
    simpa [Infra.Flow.spatialDivergence, hshiftDeriv] using
      streamVel_spatialDivergence_eq_zero hφ (s + u) x
  exact @composed_flow_jacobian_conclusion1 β I Φ hseq R M hscales m n hm hcurrent s t hRm hMm he
      hCf hMtime hCfRm hpaperTime hbShift hXShift hXShiftSmooth hdiv
/-- `flow_jacobian_composed` in `Section2FlowBoundsAtScale`, derived from the
previous scale by first advancing the Section 2 stream induction. -/
theorem section2_flow_jacobian_composed_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :
    flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
      (fun x => constructionComposedFlowJacobian hseq m s t x -
        ContinuousLinearMap.id ℝ (Vec 2)) ≤ ENNReal.ofReal 40 := by
  exact Section2FlowRegularityCore.section2_flow_jacobian_composed_from_current_induction hscales
      m n hm
    (section2_stream_induction_step hscales happB2 m hm hprev) s t ht

theorem Section2FlowRegularityCore.section2_flow_jacobian_from_current_induction
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ} (hscales : Section2Scales I R M)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcurrent : Section2StreamInductionHypothesis (Φ := Φ) R M m)
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :
    flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
      (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12 := by
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let X : ℝ → Vec 2 → ℝ → Vec 2 := constructionFlow hseq m
  let Rm : ℝ := R m
  let Mm : ℝ := M m
  let Cf : ℝ := Mm / Rm
  have hRm : 0 < Rm := by dsimp [Rm]; exact section2_radius_pos hscales m
  have hMm : 0 < Mm := by dsimp [Mm]; exact section2_amplitude_pos hscales m
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  have hMbound : Mm ≤ 2 ^ 19 * a β I.Λ m := by
    dsimp [Mm]
    exact full_amplitude_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R M hscales.radius_zero hscales.amplitude_zero
      hscales.radius_step hscales.amplitude_step m
  have hma : Mm * (a β I.Λ m)⁻¹ ≤ 2 ^ 19 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ ha).2
    dsimp [Mm] at hMbound
    nlinarith [hMbound]
  have hMtime : Mm * |t| ≤ 1 / 64 := by
    calc
      Mm * |t| ≤ Mm * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left ht hMm.le
      _ = 2 ^ (-25 : ℤ) * (Mm * (a β I.Λ m)⁻¹) := by ring
      _ ≤ 2 ^ (-25 : ℤ) * 2 ^ 19 :=
        mul_le_mul_of_nonneg_left hma (by positivity)
      _ = 1 / 64 := by norm_num
  have hCfRm : Cf * Rm = Mm := by
    dsimp [Cf, Rm, Mm]
    exact div_mul_cancel₀ _ (ne_of_gt hRm)
  have hpaperTime : |t| ≤ 1 / (8 * Cf * Rm) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      |t| * (8 * Cf * Rm) = 8 * (Cf * Rm * |t|) := by ring
      _ = 8 * (Mm * |t|) := by rw [hCfRm]
      _ ≤ 8 * (1 / 64) :=
        mul_le_mul_of_nonneg_left hMtime (by norm_num)
      _ ≤ 1 := by norm_num
  have hφ := streamSeq_isAdmissible hseq m
  have hb : Infra.Flow.SmoothPeriodicField b := by
    dsimp [b]
    exact smoothPeriodic_streamVel hφ
  have hX : IsFlow b X := by
    dsimp [X, b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  let bShift : ℝ → Vec 2 → Vec 2 := fun u x => b (s + u) x
  let XShift : ℝ → Vec 2 → ℝ → Vec 2 :=
    fun u x r => X (s + u) x (s + r)
  have hbShift : Infra.Flow.SmoothPeriodicField bShift := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
      change ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro k ell r x
      dsimp [bShift]
      simpa [add_assoc] using hb.periodic k ell (s + r) x
  have hXShift : IsFlow bShift XShift := by
    simpa [bShift, XShift] using constructionFlow_shift_isFlow hX s
  have hXjoint := constructionFlow_joint_smooth hseq m
  have hXShiftSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × Vec 2) × ℝ => XShift p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × Vec 2) × ℝ =>
          (s + p.1.1, p.1.2, s + p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
        (fun p : (ℝ × Vec 2) × ℝ => (s + p.1.1, p.1.2, s + p.2)))
    exact hXjoint.comp hmap
  have hBfield : ∀ u k, 1 ≤ k → k ≤ n + 1 →
      FaaDiBruno.snorm (bShift u) k Rm ≤ ENNReal.ofReal Cf := by
    intro u k hk hkn
    have hs := section2_streamVel_snorm_bound (hseq := hseq)
      (hprev := hcurrent) (m := m) (n := k) hk hRm hMm (s + u)
    simpa [bShift, b, Rm, Mm, Cf] using hs
  have hpaper := FaaDiBruno.flow_spatialGradient_snorm_paper
    (N := n + 1) (n := n) hn (by omega) hbShift hXShift hXShiftSmooth hCf hRm hBfield
    (t := t) hpaperTime
  let Rpaper : ℝ := 8 * 2 * Rm *
    (1 + (8 * 2 * Cf * Rm) * |t|)
  let Rtarget : ℝ := 2 ^ 14 * (epsilon β I.Λ m)⁻¹
  have hpaperRadiusPositive : 0 < Rpaper := by
    dsimp [Rpaper]
    positivity
  have hradFactor : 1 + (8 * 2 * Cf * Rm) * |t| ≤ 5 / 4 := by
    have heq : (8 : ℝ) * 2 * Cf * Rm * |t| = 16 * (Mm * |t|) := by
      calc
        (8 : ℝ) * 2 * Cf * Rm * |t| = 16 * (Cf * Rm * |t|) := by ring
        _ = 16 * (Mm * |t|) := by rw [hCfRm]
    rw [heq]
    nlinarith [hMtime]
  have hRpaper20 : Rpaper ≤ 20 * Rm := by
    dsimp [Rpaper]
    nlinarith [hRm, hradFactor]
  have hR131 : Rm ≤ 131 * (epsilon β I.Λ m)⁻¹ := by
    dsimp [Rm]
    have hr := radius_recurrence_bound I.one_lt_beta I.beta_lt
      I.two_pow_seven_le R hscales.radius_zero hscales.radius_step (m := m)
        hm
    simpa only [show (3 : ℝ) + (2 : ℝ) ^ 7 = 131 by norm_num] using hr
  have hRtarget : 0 < Rtarget := by dsimp [Rtarget]; positivity
  have hRpaperTarget : Rpaper ≤ Rtarget := by
    dsimp [Rtarget]
    calc
      Rpaper ≤ 20 * Rm := hRpaper20
      _ ≤ 20 * (131 * (epsilon β I.Λ m)⁻¹) :=
        mul_le_mul_of_nonneg_left hR131 (by norm_num)
      _ = 2620 * (epsilon β I.Λ m)⁻¹ := by ring
      _ ≤ 2 ^ 14 * (epsilon β I.Λ m)⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (inv_nonneg.mpr he.le)
  let f : Vec 2 → Vec 2 := fun y => X (s + t) y s
  have hfSmooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec 2 => (s + t, y, s)) := by fun_prop
    have h := hXjoint.comp hmap
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ =>
        constructionFlow hseq m p.1 p.2.1 p.2.2) ∘
        (fun y : Vec 2 => (s + t, y, s)))
    exact hXjoint.comp hmap
  have hFderiv : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x) :=
    hfSmooth.fderiv_right (by simp)
  have hGrad : ContDiff ℝ (⊤ : ℕ∞)
      (FaaDiBruno.spatialGradientMatrix f) := by
    unfold FaaDiBruno.spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => fderiv ℝ f x (FaaDiBruno.coordinateVector 2 j)) :=
      hFderiv.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp hcolumn
  have hpaper' : FaaDiBruno.snorm
      (FaaDiBruno.spatialGradientMatrix f) n Rpaper ≤ ENNReal.ofReal 12 := by
    simpa [f, XShift, X, constructionFlow, Rpaper] using hpaper
  have hpaperTarget : FaaDiBruno.snorm
      (FaaDiBruno.spatialGradientMatrix f) n Rtarget ≤ ENNReal.ofReal 12 :=
    FaaDiBruno.snorm_le_of_radius_le _ hpaperRadiusPositive hRtarget hRpaperTarget
      (by norm_num) hpaper'
  have hbar := flowJacobianBarNorm_le_spatialGradient_snorm f n Rtarget 12
    (hGrad.of_le (by simp)) hpaperTarget
  have hfun : (fun x => constructionFlowJacobian hseq m t s x) =
      (fun x => fderiv ℝ f x) := by
    funext x
    rfl
  simpa only [hfun, Rtarget] using hbar

/-- `flow_jacobian` in `Section2FlowBoundsAtScale`, derived from the previous
scale by first proving its current `e.indyhyp` step. -/
theorem section2_flow_jacobian_from_previous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} {R M : ℕ → ℝ}
    (hscales : Section2Scales I R M)
    (happB2 : AppB2InverseFlowData I Φ hseq R M)
    (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n)
    (hprev : Section2StreamInductionHypothesis (Φ := Φ) R M (m - 1))
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) :
    flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
      (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12 := by
  exact Section2FlowRegularityCore.section2_flow_jacobian_from_current_induction hscales m n hm hn
    (section2_stream_induction_step hscales happB2 m hm hprev) s t ht

end AVenhance.Infra.Construction

end
