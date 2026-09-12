/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra

/-!
# Literal spatial parts of the packet jets

The nonlinear terms use the value and spatial/angular part of each jet.
These are reconstructed from actual raw-path witnesses and finite sums.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

/-- Spatial jet field data, collecting `raw`, `field`, `value_eq`, `spatial_eq`. -/
structure SpatialJetField (P T : ℝ) [Fact (0 < P)] (J : Domain → VectorJet) where
  /-- Raw of `SpatialJetField`, of type `VectorField`. -/
  raw : VectorField
  /-- Underlying field of `SpatialJetField`, of type `Field P T raw`. -/
  field : Field P T raw
  value_eq : ∀ (t : Icc (0 : ℝ) T) x θ, (J (t,(x,θ))).1 = raw (t,(x,θ))
  spatial_eq : ∀ (t : Icc (0 : ℝ) T) x θ (v : SpatialDomain),
    (J (t,(x,θ))).2 (0,v) = fderiv ℝ (fun y => raw (t,y)) (x,θ) v

namespace SpatialJetField

variable {P T : ℝ} [Fact (0 < P)] {J K J' : Domain → VectorJet}

/-- Of field, bundling `raw`, `field`, `value_eq`, `spatial_eq`. -/
def ofField {raw : VectorField} (s : Set ℝ) (G : Field P T raw) :
    SpatialJetField P T (slicedJet s raw) where
  raw := raw
  field := G
  value_eq _ _ _ := rfl
  spatial_eq t x θ v := by
    change joinDerivative _ _ (0,v) = _
    simp only [joinDerivative_apply,zero_smul,zero_add]

/-- Zero, bundling `raw`, `field`, `value_eq`, `spatial_eq`. -/
def zero (P T : ℝ) [Fact (0 < P)] : SpatialJetField P T (0 : Domain → VectorJet) where
  raw := 0
  field := Field.zero P T
  value_eq _ _ _ := rfl
  spatial_eq t x θ v := by simp

/-- Congr, bundling `raw`, `field`, `value_eq`, `spatial_eq`. -/
def congr (G : SpatialJetField P T J)
    (he : ∀ (t : Icc (0 : ℝ) T) x θ, J' (t, (x, θ)) = J (t, (x, θ))) : SpatialJetField P T J' where
  raw := G.raw
  field := G.field
  value_eq t x θ := by rw [he]; exact G.value_eq t x θ
  spatial_eq t x θ v := by rw [he]; exact G.spatial_eq t x θ v

/-- Add, bundling `raw`, `field`, `value_eq`, `spatial_eq` and the required compatibility
proofs. -/
def add (G : SpatialJetField P T J) (H : SpatialJetField P T K) : SpatialJetField P T (J+K) where
  raw := G.raw+H.raw
  field := G.field.add H.field
  value_eq t x θ := by
    change (J (t,(x,θ))).1+(K (t,(x,θ))).1 = G.raw (t,(x,θ))+H.raw (t,(x,θ))
    rw [G.value_eq,H.value_eq]
  spatial_eq t x θ v := by
    change (J (t,(x,θ))).2 (0,v)+(K (t,(x,θ))).2 (0,v) =
      fderiv ℝ (fun y => G.raw (t,y)+H.raw (t,y)) (x,θ) v
    rw [G.spatial_eq,H.spatial_eq,fderiv_fun_add
      ((G.field.raw_smooth t).differentiable (by simp) (x,θ))
      ((H.field.raw_smooth t).differentiable (by simp) (x,θ))]
    rfl

end SpatialJetField
end EulerPacketCylinderField
