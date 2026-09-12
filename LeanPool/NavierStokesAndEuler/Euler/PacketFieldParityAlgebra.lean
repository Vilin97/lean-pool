/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteParity

/-! Oddness of actual cylinder paths is preserved by scalar multiplication,
time identification, and multiplication by an even matrix coefficient. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerCylinderFieldReflection
  EulerPacketPointJets

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

/-- Reflection odd: an abbreviation for `∀ t : Icc (0 : ℝ) T, reflection P (G.path t) = -G.path
t`. -/
abbrev ReflectionOdd (G : Field P T raw) : Prop :=
  ∀ t : Icc (0 : ℝ) T, reflection P (G.path t) = -G.path t

theorem reflectionOdd_of_raw (G : Field P T raw) (h : JointOdd T raw) : G.ReflectionOdd :=
  fun t => G.reflection_neg_of_raw_odd t (h t)

theorem ReflectionOdd.raw_odd {G : Field P T raw} (h : G.ReflectionOdd) : JointOdd T raw :=
  fun t => G.raw_odd_of_reflection_neg t (h t)

theorem ReflectionOdd.smul {G : Field P T raw} (h : G.ReflectionOdd) (c : ℝ) :
    (G.smul c).ReflectionOdd := by
  intro t
  change reflection P (c • G.path t) = -(c • G.path t)
  rw [map_smul,h t,smul_neg]

theorem ReflectionOdd.changeTime {G : Field P T raw} (h : G.ReflectionOdd)
    {T' : ℝ} (he : T = T') : (G.changeTime he).ReflectionOdd := by
  subst T'
  exact h

theorem ReflectionOdd.multiply {G : Field P T raw} (h : G.ReflectionOdd)
    {a : Domain → Space →L[ℝ] Space} (A : MatrixCoefficient T a)
    (ha : ∀ (t : Icc (0 : ℝ) T) x θ, a (t, (-x, -θ)) = a (t, (x, θ))) :
    (A.multiply G).ReflectionOdd :=
  (A.multiply G).reflectionOdd_of_raw (h.raw_odd.matrix_apply a ha)

end EulerPacketCylinderField.Field
