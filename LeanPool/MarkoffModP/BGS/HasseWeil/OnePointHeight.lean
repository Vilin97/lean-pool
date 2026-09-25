/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannSpace
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZeroCounting

/-!
# Heights and zero counts in a one-point Riemann space

This file supplies the direct bridge from membership in the one-point
Riemann space `L(nP)` to the pole height used by the exhaustive
principal-divisor API.

For a nonzero `x ∈ L(nP)`, every negative-order place is `P` and its pole
order is at most `n`.  Unfolding `finiteExtensionHeight` therefore gives the
bound `height(x) ≤ n * deg(P)`.  Combining this with the existing positive-order
place count gives the corresponding Tao-style zero-count estimate.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance onePointHeightConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance onePointHeightConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A nonzero function in `L(nP)` has pole height at most `n * deg(P)`.

This is proved directly from the exhaustive principal-divisor support and
the definition of `finiteExtensionHeight`; it does not invoke an abstract
divisor-degree estimate. -/
theorem finiteExtensionHeight_le_of_mem_onePointRiemannSpace
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) (hx : x ≠ 0)
    (hxSpace : x ∈ finiteExtensionOnePointRiemannSpace K L P n) :
    finiteExtensionHeight K L x ≤ n * finiteExtensionPlaceDegree K L P := by
  classical
  have hxDescription :=
    (mem_finiteExtensionOnePointRiemannSpace_iff K L P n x).mp hxSpace
  rcases hxDescription with hxZero | ⟨_hx, hP, hAway⟩
  · exact (hx hxZero).elim
  let D := finiteExtensionPrincipalDivisor K L x
  let negativeSupport := D.support.filter (fun v ↦ D v < 0)
  have hsubset : negativeSupport ⊆ {P} := by
    intro v hv
    have hvneg : D v < 0 := (Finset.mem_filter.mp hv).2
    apply Finset.mem_singleton.mpr
    by_contra hvP
    have hvnonneg : 0 ≤ D v := hAway v hvP
    omega
  have horder : (-D P).toNat ≤ n := by
    have hP' : -(n : ℤ) ≤ D P := by simpa [D] using hP
    rw [Int.toNat_le]
    omega
  calc
    finiteExtensionHeight K L x =
        ∑ v ∈ negativeSupport, (-D v).toNat * finiteExtensionPlaceDegree K L v := rfl
    _ ≤ ∑ v ∈ ({P} : Finset (FiniteExtensionPlace K L)),
        (-D v).toNat * finiteExtensionPlaceDegree K L v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
    _ = (-D P).toNat * finiteExtensionPlaceDegree K L P := by simp
    _ ≤ n * finiteExtensionPlaceDegree K L P :=
      Nat.mul_le_mul_right (finiteExtensionPlaceDegree K L P) horder

/-- Degree-one specialization of
`finiteExtensionHeight_le_of_mem_onePointRiemannSpace`. -/
theorem finiteExtensionHeight_le_of_mem_onePointRiemannSpace_degree_one
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) (hx : x ≠ 0)
    (hxSpace : x ∈ finiteExtensionOnePointRiemannSpace K L P n)
    (hdegree : finiteExtensionPlaceDegree K L P = 1) :
    finiteExtensionHeight K L x ≤ n := by
  simpa [hdegree] using
    finiteExtensionHeight_le_of_mem_onePointRiemannSpace K L P n x hx hxSpace

/-- Tao-style zero count: a finite family injecting into positive-order
places of a nonzero `x ∈ L(nP)` has cardinality at most `n * deg(P)`. -/
theorem Fintype.card_le_mul_placeDegree_of_onePointRiemannSpace
    {ι : Type*} [Fintype ι]
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) (hx : x ≠ 0)
    (hxSpace : x ∈ finiteExtensionOnePointRiemannSpace K L P n)
    (place : ι → FiniteExtensionPlace K L)
    (hinjective : Function.Injective place)
    (hpositive : ∀ i, 0 < finiteExtensionPrincipalDivisor K L x (place i)) :
    Fintype.card ι ≤ n * finiteExtensionPlaceDegree K L P := by
  exact (Fintype.card_le_finiteExtensionHeight_of_injective_orders_positive
    K L x hx place hinjective hpositive).trans
      (finiteExtensionHeight_le_of_mem_onePointRiemannSpace K L P n x hx hxSpace)

/-- Degree-one specialization of the one-point zero count. -/
theorem Fintype.card_le_of_onePointRiemannSpace_degree_one
    {ι : Type*} [Fintype ι]
    (P : FiniteExtensionPlace K L) (n : ℕ) (x : L) (hx : x ≠ 0)
    (hxSpace : x ∈ finiteExtensionOnePointRiemannSpace K L P n)
    (hdegree : finiteExtensionPlaceDegree K L P = 1)
    (place : ι → FiniteExtensionPlace K L)
    (hinjective : Function.Injective place)
    (hpositive : ∀ i, 0 < finiteExtensionPrincipalDivisor K L x (place i)) :
    Fintype.card ι ≤ n := by
  simpa [hdegree] using
    Fintype.card_le_mul_placeDegree_of_onePointRiemannSpace
      K L P n x hx hxSpace place hinjective hpositive

end

end BGS.HasseWeil
