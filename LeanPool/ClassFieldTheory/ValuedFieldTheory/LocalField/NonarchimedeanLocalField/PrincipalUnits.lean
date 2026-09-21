/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
/-!
# Principal units

Defines the filtration `U^n = 1 + 𝓂^n`, proves its basic order properties, and
constructs the quotient of valuation-ring units by the first filtration step.
-/
namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The actual principal-unit filtration `U^n = {u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂[K]^n}`. -/
def principalUnits (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Subgroup 𝒪[K]ˣ where
  carrier := {u | ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])}
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    change ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show ((a : 𝒪[K]) * (b : 𝒪[K]) - 1) =
        ((a : 𝒪[K]) - 1) * (b : 𝒪[K]) + ((b : 𝒪[K]) - 1) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
    rw [show (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
        -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) by
      calc
        (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1)
            = ((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K])
              - (((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (a : 𝒪[K])) := by
                simp
        _ = -(((a⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((a : 𝒪[K]) - 1)) := by
          ring]
    exact (𝓂[K] ^ n : Ideal 𝒪[K]).neg_mem (Ideal.mul_mem_left _ _ ha)

/-- A valuation-ring unit lies in the `n`-th principal-unit group exactly when it is congruent to
one modulo the `n`-th maximal-ideal power. -/
theorem mem_principalUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (u : 𝒪[K]ˣ) (n : Nat) :
    u ∈ principalUnits K n ↔ ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  Iff.rfl

/-- An automorphism of the valuation integer ring preserves the principal-unit
filtration whenever it preserves the corresponding maximal-ideal power. -/
theorem principalUnits_integerRingEquiv_mem (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (σ𝒪 : 𝒪[K] ≃+* 𝒪[K])
    (hpow : ∀ x : 𝒪[K],
      x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) → σ𝒪 x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]))
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K n) :
    Units.mapEquiv σ𝒪.toMulEquiv u ∈ principalUnits K n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmem : σ𝒪 ((u : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) :=
    hpow ((u : 𝒪[K]) - 1) hu
  simpa using hmem

/-- The zeroth principal-unit group is the full unit group of the valuation ring. -/
@[simp] theorem principalUnits_zero (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 0 = ⊤ := by
  ext u
  simp [principalUnits]

/-- Principal-unit groups decrease as the filtration index increases. -/
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits K n ≤ principalUnits K m := by
  intro u hu
  exact Ideal.pow_le_pow_right h hu

/-- Each successor principal-unit group is contained in the preceding filtration step. -/
theorem principalUnits_succ_le (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnits K (n + 1) ≤ principalUnits K n :=
  principalUnits_antitone K (Nat.le_succ n)

/-- Every positive-index principal unit lies in the first principal-unit group. -/
theorem principalUnits_le_one (K : Type u) [Field K] [ValuativeRel K]
    {n : Nat} (hn : 1 ≤ n) :
    principalUnits K n ≤ principalUnits K 1 :=
  principalUnits_antitone K hn

/-- Quotient of integer units by the actual principal-unit filtration. -/
def IntegerUnitsPrincipalQuot (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- The quotient of valuation-ring units by an `n`-th principal-unit subgroup is a commutative
group. -/
instance integerUnitsPrincipalQuotCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsPrincipalQuot K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- Explicit access to the concrete quotient model.  Public consumers should
use the named constructor and eliminators below instead of unfolding the
quotient representation. -/
def integerUnitsPrincipalQuotConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsPrincipalQuot K n ≃* (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _

/-- The quotient map `𝒪[K]ˣ → 𝒪[K]ˣ/U^n`. -/
def integerUnitsPrincipalQuotMk (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : 𝒪[K]ˣ →* IntegerUnitsPrincipalQuot K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

/-- The concrete quotient equivalence sends the class of a valuation-ring unit to its quotient-group
class. -/
@[simp]
theorem integerUnitsPrincipalQuotConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotConcreteEquiv K n
        (integerUnitsPrincipalQuotMk K n u) =
      QuotientGroup.mk u :=
  rfl

/-- Every principal-unit quotient class has a valuation-ring unit representative. -/
theorem integerUnitsPrincipalQuotMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (integerUnitsPrincipalQuotMk K n) :=
  QuotientGroup.mk'_surjective (principalUnits K n)

/-- The kernel of the principal-unit quotient map is the `n`-th principal-unit subgroup. -/
theorem integerUnitsPrincipalQuotMk_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.ker (integerUnitsPrincipalQuotMk K n) = principalUnits K n :=
  QuotientGroup.ker_mk' (N := principalUnits K n)

/-- A unit maps to the identity quotient class exactly when it lies in the `n`-th principal-unit
subgroup. -/
@[simp]
theorem integerUnitsPrincipalQuotMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotMk K n u = 1 ↔ u ∈ principalUnits K n := by
  change QuotientGroup.mk' (principalUnits K n) u = 1 ↔ _
  exact QuotientGroup.eq_one_iff (N := principalUnits K n) u

/-- Two units determine the same quotient class exactly when their quotient lies in the `n`-th
principal-unit subgroup. -/
@[simp]
theorem integerUnitsPrincipalQuotMk_eq_iff_div_mem
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (u v : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotMk K n u =
        integerUnitsPrincipalQuotMk K n v ↔
      u / v ∈ principalUnits K n := by
  change (QuotientGroup.mk u : 𝒪[K]ˣ ⧸ principalUnits K n) =
      QuotientGroup.mk v ↔ _
  exact QuotientGroup.eq_iff_div_mem (N := principalUnits K n)

/-- Descend a homomorphism that kills `U^n` to the named quotient. -/
def integerUnitsPrincipalQuotLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker) :
    IntegerUnitsPrincipalQuot K n →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) →* M
  exact QuotientGroup.lift (principalUnits K n) f h

/-- A homomorphism lifted from the principal-unit quotient agrees with the original map on
representatives. -/
@[simp]
theorem integerUnitsPrincipalQuotLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (u : 𝒪[K]ˣ) :
    integerUnitsPrincipalQuotLift n f h
        (integerUnitsPrincipalQuotMk K n u) = f u :=
  rfl

/-- Eliminate a quotient class through the canonical class map on arbitrary
representatives. -/
protected theorem IntegerUnitsPrincipalQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsPrincipalQuot K n → Prop}
    (q : IntegerUnitsPrincipalQuot K n)
    (h : ∀ u : 𝒪[K]ˣ, motive (integerUnitsPrincipalQuotMk K n u)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u

/-- Algebra identity used to prove multiplicative closure of principal units. -/
lemma unit_mul_sub_one_eq (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    ((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
      ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) +
        ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1) := by
  simp only [Units.val_mul]
  ring

/-- Powers of the maximal ideal decrease as their exponent increases. -/
lemma maximalIdeal_pow_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    (𝓂[K] ^ n : Ideal 𝒪[K]) ≤ (𝓂[K] ^ m : Ideal 𝒪[K]) :=
  Ideal.pow_le_pow_right h

end
end LocalFieldTheory
