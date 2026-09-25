/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Finsupp
/-!
# Continuous additive maps of p-adic modules are p-adic linear

This is the density argument used explicitly in the local-field structure theory,
the field-unit structure theorem: compatibility with ordinary integral powers, together with
continuity of the p-adic scalar orbit, forces compatibility with every
p-adic scalar.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

/-- Turn a topological group equivalence whose source is an additive group
written multiplicatively into the inverse topological additive equivalence. -/
noncomputable def continuousAddEquivOfMultiplicativeSource
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : Multiplicative C ≃ₜ* G) : Additive G ≃ₜ+ C :=
  { (MulEquiv.toAdditiveRight e.toMulEquiv).symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

/-- Turn a topological additive equivalence into the corresponding
topological multiplicative equivalence after tagging the source
multiplicatively. -/
noncomputable def continuousMulEquivOfAdditiveTarget
    {C G : Type*} [AddZeroClass C] [MulOneClass G]
    [TopologicalSpace C] [TopologicalSpace G]
    (e : C ≃ₜ+ Additive G) : Multiplicative C ≃ₜ* G :=
  { e.toAddEquiv.toMultiplicativeLeft with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

variable {p : ℕ} [Fact p.Prime]
variable {A B : Type*}
variable [TopologicalSpace A] [TopologicalSpace B]
variable [AddCommMonoid A] [AddCommMonoid B]
variable [Module ℤ_[p] A] [Module ℤ_[p] B]
variable [ContinuousSMul ℤ_[p] A] [ContinuousSMul ℤ_[p] B]
variable [T2Space B]

/-- A continuous additive homomorphism between topological `Z_p`-modules is
`Z_p`-linear.  The proof checks natural scalars and extends over the dense
copy of `ℕ` in `Z_p`. -/
theorem map_padicInt_smul_of_continuous
    (f : A →+ B) (hf : Continuous f) (a : ℤ_[p]) (x : A) :
    f (a • x) = a • f x := by
  have hleft : Continuous (fun z : ℤ_[p] => f (z • x)) :=
    hf.comp (continuous_id.smul continuous_const)
  have hright : Continuous (fun z : ℤ_[p] => z • f x) :=
    continuous_id.smul continuous_const
  have hclosed : IsClosed {z : ℤ_[p] | f (z • x) = z • f x} :=
    isClosed_eq hleft hright
  refine PadicInt.denseRange_natCast.induction_on a hclosed ?_
  intro n
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Package the preceding density argument as a linear equivalence. -/
noncomputable def padicLinearEquivOfContinuousAddEquiv
    (e : A ≃+ B) (he : Continuous e) : A ≃ₗ[ℤ_[p]] B :=
  { e with
    map_smul' := fun a x =>
      map_padicInt_smul_of_continuous e.toAddMonoidHom he a x }

/-- Every `Z_p`-linear map from a finite Cartesian power of `Z_p` is
continuous when the target has continuous addition and scalar multiplication.
This is the elementary finite-basis continuity step used in the
mixed-characteristic part of the field-unit structure theorem. -/
theorem continuous_padicInt_finPi_linearMap
    {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    [Module ℤ_[p] M] [ContinuousAdd M] [ContinuousSMul ℤ_[p] M]
    (d : ℕ) (f : (Fin d → ℤ_[p]) →ₗ[ℤ_[p]] M) : Continuous f := by
  classical
  have hfun :
      (fun x : Fin d → ℤ_[p] => f x) =
        fun x => ∑ i : Fin d,
          x i • f (Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) := by
    funext x
    have hx : x = ∑ i : Fin d,
        x i • Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1 :=
      pi_eq_sum_univ' x
    calc
      f x = f (∑ i : Fin d,
          x i • Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) :=
        congrArg f hx
      _ = ∑ i : Fin d,
          x i • f (Pi.single (M := fun _ : Fin d => ℤ_[p]) i 1) := by
        simp only [map_sum, map_smul]
  change Continuous (fun x : Fin d → ℤ_[p] => f x)
  rw [hfun]
  fun_prop

/-- Finite generation across a short exact sequence, phrased for a
surjective linear map.  This avoids unfolding a large ambient module when a
finite kernel and finite quotient are already available. -/
theorem moduleFinite_of_surjective_of_ker
    {R M N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R N] [Module.Finite R (LinearMap.ker f)] :
    Module.Finite R M := by
  let e : (M ⧸ LinearMap.ker f) ≃ₗ[R] N :=
    f.quotKerEquivOfSurjective hf
  let : Module.Finite R (M ⧸ LinearMap.ker f) :=
    Module.Finite.equiv e.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

end LocalFieldTheory.DiscreteValuationField
