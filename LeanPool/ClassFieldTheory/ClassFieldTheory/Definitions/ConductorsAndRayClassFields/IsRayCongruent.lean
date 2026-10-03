/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
/-!
# Ray congruences
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u

/-- The diagonal embedding of field units into a finite completion. -/
def finitePlaceUnitEmbedding
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom

/-- A field unit satisfies the finite congruences and real positivity
conditions specified by a ray modulus. -/
def IsRayCongruent
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) (x : Kˣ) : Prop :=
  (∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v x ∈
        rayLocalHigherUnitGroup v (m.finitePart v)) ∧
    (∀ v, v ∈ m.infinitePart →
      0 < v.1.embedding_of_isReal v.2 (x : K))

namespace IsRayCongruent

/-- The identity satisfies every ray congruence. -/
theorem one {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : IsRayCongruent m 1 := by
  constructor
  · intro v _
    simpa only [map_one] using (rayLocalHigherUnitGroup v (m.finitePart v)).one_mem
  · intro v _
    simp

/-- Ray-congruent nonzero elements are closed under multiplication. -/
theorem mul {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K} {x y : Kˣ}
    (hx : IsRayCongruent m x) (hy : IsRayCongruent m y) :
    IsRayCongruent m (x * y) := by
  constructor
  · intro v hv
    simpa only [map_mul] using
      (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx.1 v hv) (hy.1 v hv)
  · intro v hv
    simpa only [Units.val_mul, map_mul] using mul_pos (hx.2 v hv) (hy.2 v hv)

/-- Ray-congruent nonzero elements are closed under inversion. -/
theorem inv {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K} {x : Kˣ}
    (hx : IsRayCongruent m x) : IsRayCongruent m x⁻¹ := by
  constructor
  · intro v hv
    simpa only [map_inv] using
      (rayLocalHigherUnitGroup v (m.finitePart v)).inv_mem (hx.1 v hv)
  · intro v hv
    simpa only [Units.val_inv_eq_inv_val, map_inv₀] using inv_pos.mpr (hx.2 v hv)

end IsRayCongruent

end ClassFieldTheory
