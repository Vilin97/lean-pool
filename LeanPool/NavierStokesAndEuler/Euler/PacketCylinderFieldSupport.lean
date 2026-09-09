/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProductSupport
public import LeanPool.NavierStokesAndEuler.Euler.CylinderLocalSupport

@[expose] public section

/-! Support of a raw packet witness is exactly support of its actual L² path. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpSupportedSubspace EulerMetricTransport

variable {P T : ℝ} [Fact (0 < P)] {raw : EulerPacketProfileRecursion.VectorField}
  (G : Field P T raw) (S : Set Space) (hS : MeasurableSet S)

theorem supported_of_raw_zero
    (h : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) : G.path t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (G.path t)).mpr
  filter_upwards [pointField_ae P G.path G.orbit t] with z hz hzs
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z.2
  have he := G.raw_eq t z.1 θ
  rw [hθ] at he
  exact hz.trans (he.symm.trans (h t z.1 hzs θ))

theorem raw_zero_of_supported (hSc : IsClosed S)
    (h : ∀ t : Icc (0 : ℝ) T, G.path t ∈ Supported P Space S hS)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    raw (t,(x,θ)) = 0 := by
  rw [G.raw_eq]
  exact EulerCylinderLocalSupport.pointField_zero_outside P S hS G.path G.orbit hSc h t
    (x,(θ : AddCircle P)) hx

end EulerPacketCylinderField.Field
