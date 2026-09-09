/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordTime
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets

/-! An actual ordinary L² path with coherent Sobolev realizations has
genuine smooth spatial representatives and continuous L² tensor jets.
The unit-cylinder lift is only a realization in an already complete
Sobolev space; the resulting ordinary field equals the prescribed L²
path. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerMetricTransport EulerLpFiniteTensor
open scoped ContDiff Topology

local instance instOrdinarySobolevTower1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Sobolev tower data, collecting `field`, `realization`, `value_eq`. -/
structure SobolevTower (T : ℝ) where
  /-- Underlying field of `SobolevTower`, of type `C(Icc (0 : ℝ) T,EulerMeanSolenoidal.L2)`. -/
  field : C(Icc (0 : ℝ) T,EulerMeanSolenoidal.L2)
  /-- Realization of `SobolevTower`, of type `∀ q, C(Icc (0 : ℝ) T,SobolevSpace 1 q)`. -/
  realization : ∀ q, C(Icc (0 : ℝ) T,SobolevSpace 1 q)
  value_eq : ∀ q t, value 1 (realization q t)=ordinaryLift (field t)

namespace SobolevTower

variable {T : ℝ} (A : SobolevTower T)

/-- Cylinder, bundling `field`, `realization`, `value_eq`. -/
def cylinder : EulerAllOrderCorrectionData.FieldTower 1 T where
  field := ordinaryLift.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T) A.field
  realization := A.realization
  value_eq := A.value_eq

/-- Smooth field, given by `A.cylinder.zeroGraphField t`. -/
def smoothField (t : Icc (0 : ℝ) T) : SmoothL2Field Space := A.cylinder.zeroGraphField t

theorem smoothField_toLp (t : Icc (0 : ℝ) T) : (A.smoothField t).toLp=A.field t := by
  have ha : (ordinaryLift (A.field t) : LiftDomain 1 → Space) =ᵐ[liftMeasure 1]
      A.cylinder.pointField t := A.cylinder.pointField_ae t
  obtain ⟨f,hf,hfa⟩ := exists_smooth_of_lift (A.field t) (A.cylinder.pointField t)
    (A.cylinder.pointField_smooth t) ha
  have hrep : (ordinaryLift (A.field t) : LiftDomain 1 → Space) =ᵐ[liftMeasure 1]
      (fun x : LiftDomain 1 => f x.1) :=
    (ordinaryLift_ae (A.field t)).trans
        (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae hfa)
  have he := A.cylinder.pointField_unique t (fun x : LiftDomain 1 => f x.1)
    (hf.continuous.comp continuous_fst) hrep
  have hv : (A.smoothField t).field=f := by
    funext x
    change (A.cylinder.zeroGraphField t).field x=f x
    rw [EulerAllOrderCorrectionData.FieldTower.zeroGraphField_apply,he]
    rfl
  apply Lp.ext
  have hv' : (A.smoothField t).field=ᵐ[volume] f := Eventually.of_forall (congrFun hv)
  exact (A.smoothField t).toLp_ae.trans (hv'.trans hfa.symm)

theorem smoothField_jet_continuous (n : ℕ) :
    Continuous (fun t => (A.smoothField t).jetLp n) := A.cylinder.zeroGraphField_jetLp_continuous n

theorem smoothField_realization (q : ℕ) (t : Icc (0 : ℝ) T) :
    ordinarySobolev q (A.smoothField t).toLp (A.smoothField t).translation_contDiff=A.realization q
        t := by
  apply value_injective 1
  erw [ordinarySobolev_value,A.smoothField_toLp,A.value_eq]

theorem smoothField_path (q : ℕ) :
    sobolevPath A.smoothField A.smoothField_jet_continuous q=A.realization q := by
  apply ContinuousMap.ext
  exact A.smoothField_realization q

end SobolevTower

/-- Ordinary tensor operator as an element of `SobolevSpace 1 q →L[ℝ] Lp (Space [×q]→L[ℝ] Space)
2 (volume : Measure Space)`. -/
def ordinaryTensorOperator (q : ℕ) :
    SobolevSpace 1 q →L[ℝ] Lp (Space [×q]→L[ℝ] Space) 2 (volume : Measure Space) :=
  (tensorLpReassembly (V := Space) (volume : Measure Space) q).comp
    (ContinuousLinearMap.pi (fun w : Fin q → Fin 3 => ordinaryWordOperator w))

theorem ordinaryTensorOperator_apply (A : SmoothL2Field Space) (q : ℕ) :
    ordinaryTensorOperator q (ordinarySobolev q A.toLp A.translation_contDiff)=A.jetLp q := by
  have he : ordinaryTensorOperator q (ordinarySobolev q A.toLp A.translation_contDiff) =
      tensorLpReassembly (volume : Measure Space) q (fun w : Fin q → Fin 3 => (wordField A w).toLp)
          := by
    unfold ordinaryTensorOperator
    rw [ContinuousLinearMap.comp_apply]
    congr 1
    funext w
    exact ordinaryWordOperator_apply A w
  rw [he]
  apply Lp.ext
  apply (tensorLpReassembly_eq_ae (volume : Measure Space) q
    (fun w : Fin q → Fin 3 => (wordField A w).toLp) (iteratedFDeriv ℝ q A.field) ?_).trans
    (A.jetLp_ae q).symm
  intro w
  filter_upwards [(wordField A w).toLp_ae] with x hx
  rw [hx,wordField_field]
  rfl

theorem SobolevTower.tensorOperator_realization {T : ℝ} (A : SobolevTower T)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    ordinaryTensorOperator q (A.realization q t)=(A.smoothField t).jetLp q := by
  rw [← A.smoothField_realization q t]
  exact ordinaryTensorOperator_apply _ q

end EulerOrdinarySobolev
