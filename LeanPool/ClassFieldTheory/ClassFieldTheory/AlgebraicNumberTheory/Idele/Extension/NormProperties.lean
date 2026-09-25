/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Mathlib.RingTheory.Norm.Transitivity
/-!
# Functorial properties of the idele norm

In the tensor-product presentation `𝔸_L = 𝔸_K ⊗_K L`, the idele norm is
the determinant norm of a finite free algebra.  Thus transitivity is the
general transitivity theorem for determinant norms.  The remaining
statements record the base-field power formula and compatibility with
principal ideles and Galois conjugation.
-/

@[expose] public section

open scoped BigOperators
open NumberField

noncomputable section


namespace RelativeIdeleGroup

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L] in
/-- The field norm, regarded in `L`, is the product of all Galois
conjugates.  This is the unit-valued form used for principal ideles in
the Galois product norm formula. -/
theorem fieldNormUnits_eq_prod_conjugates
    [IsGalois K L] (x : Lˣ) :
    Units.map (algebraMap K L)
        (Units.map (_root_.Algebra.norm K) x) =
      ∏ σ : L ≃ₐ[K] L,
        Units.map σ.toRingEquiv.toMonoidHom x := by
  apply Units.ext
  simp only [Units.coe_map, Units.coe_prod]
  convert
    (_root_.Algebra.norm_eq_prod_automorphisms K (x : L))
    using 1 <;> rfl

omit [NumberField L] in
/-- On the diagonal copy of `Lˣ`, after extending the norm
back to `L`, the principal idele of the norm is the product of the
Galois-conjugate principal ideles. -/
theorem inclusion_norm_principalIdele_eq_prod_conjugates
    [IsGalois K L] (x : Lˣ) :
    inclusion K L (norm K L (principalIdele K L x)) =
      ∏ σ : L ≃ₐ[K] L,
        σ • principalIdele K L x := by
  rw [norm_principalIdele, inclusion_principalIdele]
  simp_rw [smul_principalIdele]
  rw [← map_prod]
  exact congrArg (principalIdele K L)
    (fieldNormUnits_eq_prod_conjugates K L x)

end RelativeIdeleGroup
