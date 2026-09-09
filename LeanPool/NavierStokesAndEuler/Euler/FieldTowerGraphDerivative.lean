/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraph
public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphDerivative

@[expose] public section

/-! Genuine Sobolev time derivatives of coherent towers pass to actual
spatial L² derivatives after restriction to any fixed phase graph. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerMetricTransport EulerTransportDerivatives
  EulerCylinderGraphTrace EulerVolterraConvolution
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)]
  (A B : EulerAllOrderCorrectionData.FieldTower P T)
  (f g : Icc (0 : ℝ) T → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hg : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (g t) x))
  (ha : ∀ t, (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)
  (hb : ∀ t, (B.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g t)
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

theorem graphWordPath_hasDerivWithinAt (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T)
    (hd : HasDerivWithinAt (extendPath T hT (A.realization (n+1)))
      (B.realization (n+1) t) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
      (B.graphWordPath g hg hb θ hθ n w t) (Icc (0 : ℝ) T) t := by
  refine graph_hasDerivWithinAt P
    (extendPath T hT (A.derivativeWordPath (n+1) n w (by omega)))
    (extendPath T hT (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl))
    (fun r => iteratedFieldDerivative P w (f (projIcc 0 T hT r)))
    (fun r => iteratedFieldDerivative_smooth P w _ (hf (projIcc 0 T hT r)))
    (fun r => A.derivativeWordPath_ae f hf ha (n+1) n w (by omega) (projIcc 0 T hT r))
    (fun r => A.graphWord_angular_ae f hf ha n w (projIcc 0 T hT r)) θ hθ
    (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
    (fun r => A.graphWordPath_ae f hf ha θ hθ n w (projIcc 0 T hT r))
    (iteratedFieldDerivative P w (g t))
    (iteratedFieldDerivative_smooth P w _ (hg t))
    (B.derivativeWordPath (n+1) n w (by omega) t)
    (B.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t)
    (B.derivativeWordPath_ae g hg hb (n+1) n w (by omega) t)
    (B.graphWord_angular_ae g hg hb n w t)
    (B.graphWordPath g hg hb θ hθ n w t)
    (B.graphWordPath_ae g hg hb θ hθ n w t) (Icc (0 : ℝ) T) t ?_ ?_
  · exact (wordOperator P (⟨⟨n,by omega⟩,w⟩ : SobolevWord (n+1))).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) hd
  · exact (wordOperator P (⟨⟨n+1,by omega⟩,Fin.cons 0 w⟩ : SobolevWord
    (n+1))).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) hd

theorem graphWordPath_hasDerivAt (hT : 0 ≤ T) (n : ℕ) (w : Fin n → Fin 4)
    (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hd : HasDerivAt (extendPath T hT (A.realization (n+1)))
      (B.realization (n+1) ⟨t,ht.1.le,ht.2.le⟩) t) :
    HasDerivAt (extendPath T hT (A.graphWordPath f hf ha θ hθ n w))
      (B.graphWordPath g hg hb θ hθ n w ⟨t,ht.1.le,ht.2.le⟩) t :=
  (A.graphWordPath_hasDerivWithinAt B f g hf hg ha hb θ hθ hT n w
    ⟨t,ht.1.le,ht.2.le⟩ hd.hasDerivWithinAt).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end EulerAllOrderCorrectionData.FieldTower
