/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderSpatialJet

/-! The actual spatial derivatives and nonlinear jet terms preserve joint odd velocity parity. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

/-- Joint odd: an abbreviation for `∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(-x,-θ)) = -raw
(t,(x,θ))`. -/
abbrev JointOdd (T : ℝ) (raw : VectorField) : Prop :=
  ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ))

namespace JointOdd

variable {T : ℝ} {f g : VectorField}

theorem zero (T : ℝ) : JointOdd T (0 : VectorField) := by
  intro t x θ
  simp only [Pi.zero_apply,neg_zero]

theorem add (hf : JointOdd T f) (hg : JointOdd T g) : JointOdd T (f+g) := by
  intro t x θ
  simp only [Pi.add_apply,hf t x θ,hg t x θ,neg_add]

theorem neg (hf : JointOdd T f) : JointOdd T (-f) := by
  intro t x θ
  simp only [Pi.neg_apply,hf t x θ]

theorem sub (hf : JointOdd T f) (hg : JointOdd T g) : JointOdd T (f-g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem congr (hf : JointOdd T f)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, g (t, (x, θ)) = f (t, (x, θ))) : JointOdd T g := by
  intro t x θ
  rw [he,he,hf]

end JointOdd

variable {P T : ℝ} [Fact (0 < P)]

theorem Field.raw_fderiv_even_of_odd {raw : VectorField} (G : Field P T raw)
    (hodd : JointOdd T raw) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    fderiv ℝ (fun y : LiftTangent => raw (t,y)) (-x,-θ) =
      fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) := by
  have hf := G.raw_smooth t
  have he : (fun y : LiftTangent => raw (t,-y)) =
      fun y : LiftTangent => -raw (t,y) := funext (fun y => hodd t y.1 y.2)
  have h₁ := ((hf.differentiable (by simp) (-(x,θ))).hasFDerivAt).comp (x,θ)
    ((hasFDerivAt_id (𝕜 := ℝ) (x,θ)).neg)
  have h₂ := ((hf.differentiable (by simp) (x,θ)).hasFDerivAt).neg
  have hfd : fderiv ℝ (fun y : LiftTangent => -raw (t,y)) (x,θ) =
      -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) := h₂.fderiv
  have hd : -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (x,θ) =
      -fderiv ℝ (fun y : LiftTangent => raw (t,y)) (-(x,θ)) := by
    simpa only [Function.comp_def,he,hfd,comp_neg,comp_id] using h₁.fderiv
  exact neg_injective hd.symm

namespace SpatialJetField

variable {J K : Domain → VectorJet} (H : SpatialJetField P T K)

include H

theorem spatial_even_of_value_odd (hK : JointOdd T (fun z => (K z).1))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) (v : SpatialDomain) :
    (K (t,(-x,-θ))).2 (0,v) = (K (t,(x,θ))).2 (0,v) := by
  have hr : JointOdd T H.raw := by
    intro s y η
    rw [← H.value_eq,← H.value_eq]
    exact hK s y η
  rw [H.spatial_eq,H.spatial_eq,H.field.raw_fderiv_even_of_odd hr t x θ]

theorem slowAdvection_odd (inverse : Domain → Space →L[ℝ] Space)
    (hI : ∀ (t : Icc (0 : ℝ) T) x θ, inverse (t, (-x, -θ)) = inverse (t, (x, θ)))
    (hJ : JointOdd T (fun z => (J z).1)) (hK : JointOdd T (fun z => (K z).1)) :
    JointOdd T (fun z => EulerPacketPointJets.slowAdvection (inverse z) (J z) (K z)) := by
  intro t x θ
  have hD : (K (t,(-x,-θ))).2.comp spatialInjection =
      (K (t,(x,θ))).2.comp spatialInjection := by
    apply ContinuousLinearMap.ext
    intro v
    exact H.spatial_even_of_value_odd hK t x θ (v,0)
  change ((K (t,(-x,-θ))).2.comp spatialInjection) (inverse (t,(-x,-θ)) (J (t,(-x,-θ))).1) =
    -((K (t,(x,θ))).2.comp spatialInjection) (inverse (t,(x,θ)) (J (t,(x,θ))).1)
  have hj : (J (t,(-x,-θ))).1 = -(J (t,(x,θ))).1 := hJ t x θ
  rw [hD,hI t x θ,hj,map_neg,map_neg]

theorem fastAdvection_odd (normal : VectorField)
    (hN : ∀ (t : Icc (0 : ℝ) T) x θ, normal (t, (-x, -θ)) = normal (t, (x, θ)))
    (hJ : JointOdd T (fun z => (J z).1)) (hK : JointOdd T (fun z => (K z).1)) :
    JointOdd T (fun z => EulerPacketPointJets.fastAdvection (normal z) (J z) (K z)) := by
  intro t x θ
  change inner ℝ (normal (t,(-x,-θ))) (J (t,(-x,-θ))).1 • (K (t,(-x,-θ))).2 (0,(0,1)) =
    -(inner ℝ (normal (t,(x,θ))) (J (t,(x,θ))).1 • (K (t,(x,θ))).2 (0,(0,1)))
  have hj : (J (t,(-x,-θ))).1 = -(J (t,(x,θ))).1 := hJ t x θ
  rw [hN t x θ,hj,H.spatial_even_of_value_odd hK t x θ (0,1),inner_neg_right,neg_smul]

end SpatialJetField

end EulerPacketCylinderField
