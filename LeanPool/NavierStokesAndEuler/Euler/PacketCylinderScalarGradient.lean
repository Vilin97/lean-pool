/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime

@[expose] public section

/-! The literal spatial gradient of an actual scalar cylinder path is an actual vector path. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory ContinuousLinearMap InnerProductSpace Finset EulerSmoothLimit
  EulerLiftedGradientSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderConstantMap EulerCylinderScalarPrimitive EulerCylinderPathProduct
  EulerPacketPointJets EulerPacketProfileRecursion EulerCylinderSobolev
open scoped ContDiff

def gradientComponent (i : Fin 3) : Space →L[ℝ] Space :=
  (toSpanSingleton ℝ (basisVector i)).comp scalarProject

theorem gradientComponent_norm (i : Fin 3) : ‖gradientComponent i‖ ≤ 1 := by
  have h := opNorm_comp_le (toSpanSingleton ℝ (basisVector i)) scalarProject
  simpa only [gradientComponent, norm_toSpanSingleton, scalarProject_norm,
    basisVector, PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one] using h

theorem gradient_eq_sum (D : LiftTangent →L[ℝ] ℝ) :
    (toDual ℝ Space).symm (D.comp (inl ℝ Space ℝ)) =
      ∑ i : Fin 3, D (standardDirection i.succ) • basisVector i := by
  have hc (i : Fin 3) : component i ((toDual ℝ Space).symm (D.comp (inl ℝ Space ℝ))) =
      D (standardDirection i.succ) := by
    change ((toDual ℝ Space).symm (D.comp (inl ℝ Space ℝ))) i = _
    have h := toDual_symm_apply (𝕜 := ℝ)
      (x := basisVector i) (y := D.comp (inl ℝ Space ℝ))
    simpa only [component, basisVector,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul, comp_apply,
      inl_apply, standardDirection_succ] using h
  rw [← sum_components ((toDual ℝ Space).symm (D.comp (inl ℝ Space ℝ)))]
  exact sum_congr rfl (fun i _ => congrArg (fun r : ℝ => r • basisVector i) (hc i))

variable {P T : ℝ} [Fact (0 < P)] (raw : ScalarField)
  (p : C(Icc (0 : ℝ) T,CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (he : ∀ (t : Icc (0 : ℝ) T) x θ,
    raw (t,(x,θ)) = scalarPointField P p hp t (x,(θ : AddCircle P)))

/-- A norm-one scalar embedding retains the actual continuous L² path. -/
def scalarEmbeddingField : Field P T (fun z => scalarEmbed (raw z)) :=
  Field.ofLifted (pathMap P scalarEmbed p) (pathMap_orbit_contDiff P scalarEmbed p hp)
    (fun t x => scalarEmbed (scalarPointField P p hp t x))
    (fun t => scalarEmbed.continuous.comp (scalarPointField_continuous P p hp t))
    (fun t => by
      filter_upwards [map_ae P scalarEmbed (p t),scalarPointField_ae P p hp t] with x hm hs
      exact hm.trans (congrArg scalarEmbed hs))
    (fun t x θ => congrArg scalarEmbed (he t x θ))

include he in
theorem scalarRaw_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun y : LiftTangent => raw (t,y)) := by
  have h : (fun y : LiftTangent => raw (t,y)) =
      fun y : LiftTangent => scalarPointField P p hp t (y.1,(y.2 : AddCircle P)) :=
    funext (fun y => he t y.1 y.2)
  rw [h]
  exact coverField_contDiff P _ (scalarPointField_smooth P p hp t)

/-- This witness is the spatial gradient used by `pressureJet`; it needs no time derivative. -/
def scalarGradientField : Field P T (pressureGradient raw) :=
  (Field.finsetSum (univ : Finset (Fin 3))
    (fun i z => gradientComponent i
      (fderiv ℝ (fun y => scalarEmbed (raw (z.1,y))) z.2 (standardDirection i.succ)))
    (fun i => ((scalarEmbeddingField raw p hp he).derivative i.succ).map (gradientComponent
      i))).congr
    (fun t x θ => by
      have hd : fderiv ℝ (fun y => scalarEmbed (raw (t,y))) (x,θ) =
          scalarEmbed.comp (fderiv ℝ (fun y => raw (t,y)) (x,θ)) :=
        (scalarEmbed.hasFDerivAt.comp (x,θ)
          (((scalarRaw_smooth raw p hp he t).differentiable (by simp)) (x,θ)).hasFDerivAt).fderiv
      have hpressure : (pressureJet raw (t,(x,θ))).2.comp spatialInjection =
          (fderiv ℝ (fun y => raw (t,y)) (x,θ)).comp (inl ℝ Space ℝ) := by
        apply ContinuousLinearMap.ext
        intro v
        simp only [comp_apply,pressureJet_space,inl_apply]
      change (toDual ℝ Space).symm ((pressureJet raw (t,(x,θ))).2.comp spatialInjection) = _
      rw [hpressure,gradient_eq_sum]
      simp only [Finset.sum_apply,hd,gradientComponent,comp_apply,
        project_embed,toSpanSingleton_apply])

end EulerPacketCylinderField
