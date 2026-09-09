/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

/-! A genuine determinant-one flow transports continuous spatial L² paths
through its actual inverse, preserving the norm exactly. -/

noncomputable section

namespace EulerFlowL2Transport

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport

def inverseHomeomorph (X Y : Vector3 → Vector3)
    (hYX : Function.LeftInverse Y X) (hXY : Function.RightInverse Y X)
    (hX : Continuous X) (hY : Continuous Y) : Vector3 ≃ₜ Vector3 where
  toFun := X
  invFun := Y
  left_inv := hYX
  right_inv := hXY
  continuous_toFun := hX
  continuous_invFun := hY

theorem inverse_measurePreserving (X Y : Vector3 → Vector3)
    (F : Vector3 → Vector3 →L[ℝ] Vector3)
    (hX : ∀ x, HasFDerivAt X (F x) x)
    (hYX : Function.LeftInverse Y X) (hXY : Function.RightInverse Y X)
    (hY : Continuous Y) (hdet : ∀ x, (F x).det=1) :
    MeasurePreserving Y volume volume := by
  let e := inverseHomeomorph X Y hYX hXY
    (continuous_iff_continuousAt.mpr (fun x => (hX x).continuousAt)) hY
  have hm : MeasurePreserving e.toMeasurableEquiv volume volume :=
    EulerDeformationVolume.measurePreserving_of_det_one volume X F hX
      ⟨hYX.injective,hXY.surjective⟩ hdet
  exact MeasurePreserving.symm e.toMeasurableEquiv hm

variable {K E : Type*} [TopologicalSpace K] [NormedAddCommGroup E]
  (X Y : K → Vector3 → Vector3) (F : K → Vector3 → Vector3 →L[ℝ] Vector3)
  (hX : ∀ t x, HasFDerivAt (X t) (F t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y)) (hdet : ∀ t x, (F t x).det=1)

def inversePath : C(K,C(Vector3,Vector3)) :=
  (⟨Function.uncurry Y,hY⟩ : C(K × Vector3,Vector3)).curry

include hX hYX hXY hY hdet in
theorem inversePath_measurePreserving (t : K) :
    MeasurePreserving (inversePath Y hY t) volume volume :=
  inverse_measurePreserving (X t) (Y t) (F t) (hX t) (hYX t) (hXY t)
    (Continuous.uncurry_left t hY) (hdet t)

/-- No operator-norm continuity of composition is assumed. Joint strong
continuity follows from actual continuity and preservation of volume. -/
def transportPath (u : C(K,Lp E 2 (volume : Measure Vector3))) :
    C(K,Lp E 2 (volume : Measure Vector3)) where
  toFun t := Lp.compMeasurePreserving (inversePath Y hY t)
    (inversePath_measurePreserving X Y F hX hYX hXY hY hdet t) (u t)
  continuous_toFun := u.continuous.compMeasurePreservingLp
    (inversePath Y hY).continuous
    (inversePath_measurePreserving X Y F hX hYX hXY hY hdet) (by norm_num)

theorem transportPath_norm (u : C(K,Lp E 2 (volume : Measure Vector3))) (t : K) :
    ‖transportPath X Y F hX hYX hXY hY hdet u t‖ = ‖u t‖ :=
  Lp.norm_compMeasurePreserving (u t)
    (inversePath_measurePreserving X Y F hX hYX hXY hY hdet t)

theorem transportPath_ae (u : C(K,Lp E 2 (volume : Measure Vector3)))
    (f : K → Vector3 → E) (hu : ∀ t, (u t : Vector3 → E) =ᵐ[volume] f t) (t : K) :
    (transportPath X Y F hX hYX hXY hY hdet u t : Vector3 → E) =ᵐ[volume]
      fun x => f t (Y t x) :=
  (Lp.coeFn_compMeasurePreserving (u t)
    (inversePath_measurePreserving X Y F hX hYX hXY hY hdet t)).trans
    ((inversePath_measurePreserving X Y F hX hYX hXY hY hdet t).quasiMeasurePreserving.ae_eq_comp
      (hu t))

end EulerFlowL2Transport
