/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderOrbitSobolev
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher

/-!
# Exact classical mixed-word norms of the reconstructed cylinder field

The actual classical spatial/angular derivatives represent the exact L²
translation words. Consequently the fixed-Hq external-word sum equals the
block used by the inverse estimate, with no alphabet factor or radius loss.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSobolev EulerSpatialSobolevInverse
  EulerPressureSpatialRegularity EulerMetricTransport EulerStrongSmoothJet EulerParameterWordGevrey
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The actual strong L² derivative for an ordered mixed word. -/
def strongWord (u : LiftL2 period) {n : ℕ} (w : Fin n → Fin 4) : LiftL2 period :=
  wordDerivative standardDirection (fun a : LiftTangent => translate period a u) w 0

@[simp] theorem strongWord_zero (u : LiftL2 period) (w : Fin 0 → Fin 4) : strongWord period u w = u
    := by
  simp only [strongWord,wordDerivative_zero,translate_zero]

/-- Appending a direction differentiates the actual field. -/
theorem strongWord_snoc (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) (i : Fin 4) :
    strongWord period u (Fin.snoc w i) = strongWord period (orbitDerivative period u
        (standardDirection i)) w := by
  have he : directional standardDirection (fun a : LiftTangent => translate period a u) i =
      fun a : LiftTangent => translate period a (orbitDerivative period u (standardDirection i)) :=
    funext (fun a => (orbitDerivative_translation period u hu (standardDirection i) a).symm)
  unfold strongWord
  rw [wordDerivative_snoc standardDirection _ hu w i 0,he]

/-- A strong word is the actual mixed derivative at each translated label. -/
theorem strongWord_translation (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) (a : LiftTangent) :
    translate period a (strongWord period u w) =
      wordDerivative standardDirection (fun b : LiftTangent => translate period b u) w a := by
  induction n generalizing u with
  | zero => simp only [strongWord_zero,wordDerivative_zero]
  | succ n ih =>
    have ho : strongWord period u w =
        strongWord period (orbitDerivative period u (standardDirection (w (Fin.last n)))) (Fin.init
            w) := by
      simpa only [Fin.snoc_init_self] using strongWord_snoc period u hu (Fin.init w) (w (Fin.last
          n))
    rw [ho,ih _ (orbitDerivative_smooth period u hu _) (Fin.init w)]
    have he : directional standardDirection (fun b : LiftTangent => translate period b u) (w
        (Fin.last n)) =
        fun b : LiftTangent => translate period b (orbitDerivative period u (standardDirection (w
            (Fin.last n)))) :=
      funext (fun b => (orbitDerivative_translation period u hu _ b).symm)
    simpa only [Fin.snoc_init_self,he] using
      (wordDerivative_snoc standardDirection (fun b : LiftTangent => translate period b u) hu
        (Fin.init w) (w (Fin.last n)) a).symm

/-- Every strong word has its genuine smooth full mixed orbit. -/
theorem strongWord_smooth (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) : SmoothOrbit period (strongWord period u w) := by
  have he : (fun a : LiftTangent => translate period a (strongWord period u w)) =
      wordDerivative standardDirection (fun a : LiftTangent => translate period a u) w :=
    funext (strongWord_translation period u hu w)
  change ContDiff ℝ ∞ _
  rw [he]
  exact wordDerivative_contDiff standardDirection _ hu w

/-- The genuine strong word represents the literal classical cylinder derivative. -/
theorem strongWord_ae (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) :
    (strongWord period u w : LiftDomain period → Space) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (representative period u hu) := by
  have h := jet_word_ae period (le_refl n) u (spatialJet period n u hu) w
    (representative period u hu) (representative_ae period u hu) (representative_smooth period u hu)
  rw [spatialJet_word period n n (le_refl n)] at h
  exact h

/-- The reconstructed derivative representative equals the actual classical derivative pointwise. -/
theorem representative_strongWord (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) :
    representative period (strongWord period u w) (strongWord_smooth period u hu w) =
      iteratedFieldDerivative period w (representative period u hu) := by
  apply Measure.eq_of_ae_eq
    ((representative_ae period _ (strongWord_smooth period u hu w)).symm.trans (strongWord_ae
        period u hu w))
  · exact smoothField_continuous period _ (representative_smooth period _ _)
  · exact smoothField_continuous period _
      (iteratedFieldDerivative_smooth period w _ (representative_smooth period u hu))

/-- Every actual classical mixed derivative lies in L²; this is proved from the solved orbit. -/
theorem classicalWord_memLp (u : LiftL2 period) (hu : SmoothOrbit period u)
    {n : ℕ} (w : Fin n → Fin 4) :
    MemLp (iteratedFieldDerivative period w (representative period u hu)) 2 (liftMeasure period) :=
  (Lp.memLp (strongWord period u w)).ae_eq (strongWord_ae period u hu w)

/-- The actual classical Hq norm is exactly the finite mixed-word base sum. -/
theorem classicalBaseSize_eq (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) :
    liftSobolevNorm period q (representative period u hu) =
      baseSize standardDirection q (fun a : LiftTangent => translate period a u) 0 := by
  rw [← jet_sobolevNorm_eq period u (spatialJet period q u hu) (representative period u hu)
    (representative_ae period u hu) (representative_smooth period u hu)]
  exact spatialJet_norm period q u hu

/-- The source's actual fixed-Hq external-word sum, on the literal classical field. -/
def classicalBlockSize (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 4, liftSobolevNorm period q
    (iteratedFieldDerivative period w (representative period u hu))

/-- Exact norm identification, with no dimension factor and no radius enlargement. -/
theorem classicalBlockSize_eq (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) (n : ℕ) :
    classicalBlockSize period q u hu n =
      block standardDirection q (fun a : LiftTangent => translate period a u) n 0 := by
  unfold classicalBlockSize block
  apply sum_congr rfl
  intro w _
  rw [← representative_strongWord period u hu w,classicalBaseSize_eq]
  exact congrArg (fun g : LiftTangent → LiftL2 period => baseSize standardDirection q g 0)
    (funext (strongWord_translation period u hu w))

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Time evaluation is a contraction, including for the full actual mixed-word Hq norm. -/
theorem path_classicalBlockSize_le (q : ℕ) (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p))
    (t : K) (n : ℕ) :
    classicalBlockSize period q (p t) (path_evaluation_smooth period p hp t) n ≤
      block standardDirection q (fun a : LiftTangent => pathTranslate period a p) n 0 := by
  rw [classicalBlockSize_eq]
  have hn : ‖(ContinuousMap.evalCLM ℝ t : C(K,LiftL2 period) →L[ℝ] LiftL2 period)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul,ContinuousMap.evalCLM_apply] using f.norm_coe_le_norm t
  have h := block_comp_clm_le standardDirection q
    (ContinuousMap.evalCLM ℝ t : C(K,LiftL2 period) →L[ℝ] LiftL2 period)
    (fun a : LiftTangent => pathTranslate period a p) hp n 0
  exact h.trans ((mul_le_mul_of_nonneg_right hn
    (block_nonneg standardDirection q _ n 0)).trans_eq (one_mul _))

end EulerCylinderSmoothOrbit
