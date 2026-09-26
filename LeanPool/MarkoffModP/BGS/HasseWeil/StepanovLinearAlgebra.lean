/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointHeight
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear-algebra core of the Bombieri--Stepanov argument

This file isolates the rank-nullity step from the geometry.  A finite
controlled-degree space `V` has two restriction maps.  If the second map has
target dimension smaller than `V`, while the first map is injective, there is
an auxiliary vector which vanishes under the second restriction but remains
nonzero under the first.  Once the first restriction is known to lie in a
one-point Riemann space and to vanish at every rational intersection point,
the exhaustive divisor zero count bounds the number of those points.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial TensorProduct

noncomputable section

variable {k V W₁ W₂ : Type*} [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W₁] [Module k W₁]
  [AddCommGroup W₂] [Module k W₂]

/-- Rank-nullity produces an auxiliary vector killed by `second` but not by
the injective map `first`. -/
theorem exists_auxiliary_of_finrank_lt
    [FiniteDimensional k V] [FiniteDimensional k W₂]
    (first : V →ₗ[k] W₁) (second : V →ₗ[k] W₂)
    (hfirst : Function.Injective first)
    (hdim : Module.finrank k W₂ < Module.finrank k V) :
    ∃ v : V, v ≠ 0 ∧ second v = 0 ∧ first v ≠ 0 := by
  have hnotInjective : ¬ Function.Injective second := by
    intro hinjective
    have := LinearMap.finrank_le_finrank_of_injective hinjective
    omega
  rw [Function.not_injective_iff] at hnotInjective
  obtain ⟨x, y, heq, hxy⟩ := hnotInjective
  refine ⟨x - y, sub_ne_zero.mpr hxy, ?_, ?_⟩
  · simpa using sub_eq_zero.mpr heq
  · exact (map_ne_zero_iff first hfirst).mpr (sub_ne_zero.mpr hxy)

/-- Riemann-space lower bounds and a target upper bound imply the strict
dimension inequality needed by rank-nullity on a tensor product. -/
theorem tensor_finrank_gt_of_bounds
    {A B W : Type*}
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {a b targetBound : ℕ}
    (hA : a ≤ Module.finrank k A)
    (hB : b ≤ Module.finrank k B)
    (hW : Module.finrank k W ≤ targetBound)
    (hnumeric : targetBound < a * b) :
    Module.finrank k W < Module.finrank k (A ⊗[k] B) := by
  rw [Module.finrank_tensorProduct]
  exact hW.trans_lt (hnumeric.trans_le (Nat.mul_le_mul hA hB))

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance stepanovLinearAlgebraConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance stepanovLinearAlgebraConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Abstract Stepanov zero-count theorem.

The hypotheses after rank-nullity are exactly the geometric obligations left
to an application: the first restriction has controlled poles, the selected
places are distinct, and vanishing of the second restriction forces positive
order of the first restriction at each selected place. -/
theorem card_le_mul_placeDegree_of_stepanov_restrictions
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (P : FiniteExtensionPlace K L) (n : ℕ)
    (first : V →ₗ[K] L) (second : V →ₗ[K] W)
    (hfirst : Function.Injective first)
    (hdim : Module.finrank K W < Module.finrank K V)
    (hspace : ∀ v, first v ∈
      finiteExtensionOnePointRiemannSpace K L P n)
    (place : ι → FiniteExtensionPlace K L)
    (hplace : Function.Injective place)
    (hvanish : ∀ v, v ≠ 0 → second v = 0 → ∀ i,
      0 < finiteExtensionPrincipalDivisor K L (first v) (place i)) :
    Fintype.card ι ≤ n * finiteExtensionPlaceDegree K L P := by
  obtain ⟨v, hv, hsecond, hfirstv⟩ :=
    exists_auxiliary_of_finrank_lt first second hfirst hdim
  exact Fintype.card_le_mul_placeDegree_of_onePointRiemannSpace
    K L P n (first v) hfirstv (hspace v) place hplace
      (hvanish v hv hsecond)

/-- Degree-one version of the abstract Stepanov zero-count theorem. -/
theorem card_le_of_stepanov_restrictions_degree_one
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {ι : Type*} [Fintype ι]
    (P : FiniteExtensionPlace K L) (n : ℕ)
    (first : V →ₗ[K] L) (second : V →ₗ[K] W)
    (hfirst : Function.Injective first)
    (hdim : Module.finrank K W < Module.finrank K V)
    (hspace : ∀ v, first v ∈
      finiteExtensionOnePointRiemannSpace K L P n)
    (hdegree : finiteExtensionPlaceDegree K L P = 1)
    (place : ι → FiniteExtensionPlace K L)
    (hplace : Function.Injective place)
    (hvanish : ∀ v, v ≠ 0 → second v = 0 → ∀ i,
      0 < finiteExtensionPrincipalDivisor K L (first v) (place i)) :
    Fintype.card ι ≤ n := by
  simpa [hdegree] using
    card_le_mul_placeDegree_of_stepanov_restrictions
      K L P n first second hfirst hdim hspace place hplace hvanish

end

end BGS.HasseWeil
