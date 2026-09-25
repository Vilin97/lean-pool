/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
public import Mathlib.RingTheory.RootsOfUnity.Basic
/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]


/-- The identity element is an `n`-th power and hence lies in the range of the power endomorphism.
The identity element is an `n`-th power and hence lies in the range of the power endomorphism. -/
theorem powMonoidHom_range_one_mem (n : ℕ) :
    (1 : G) ∈ (powMonoidHom n : G →* G).range := by
  rw [MonoidHom.mem_range]
  exact ⟨1, one_pow n⟩

/-- A subgroup of a commutative group contains the powers indexed by its
index. -/
theorem powMonoidHom_range_index_le (H : Subgroup G) :
    (powMonoidHom H.index : G →* G).range ≤ H := by
  intro x hx
  obtain ⟨y, rfl⟩ := (MonoidHom.mem_range (G := G)).1 hx
  exact H.pow_index_mem y

/-- In a finite commutative group, the `n`-th-power quotient has the same
cardinality as the subgroup of `n`-torsion elements.  This is the finite
kernel/cokernel equality for the power endomorphism. -/
theorem card_nthPowerQuotient_eq_nthPowerKernel
    [Finite G] (n : ℕ) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card ((powMonoidHom n : G →* G).ker) := by
  change ((powMonoidHom n : G →* G)).range.index = Nat.card ((powMonoidHom n : G →* G)).ker
  rw [Subgroup.index_range]

/-- A multiplicative equivalence transports `n`-torsion kernels. -/
def nthPowerKernelEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    (powMonoidHom n : G →* G).ker ≃* (powMonoidHom n : H →* H).ker where
  toFun x :=
    ⟨e (x : G), by
      have hx : (x : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.property
      change (e (x : G)) ^ n = 1
      simpa [map_pow] using congrArg e hx⟩
  invFun y :=
    ⟨e.symm (y : H), by
      have hy : (y : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 y.property
      change (e.symm (y : H)) ^ n = 1
      simpa [map_pow] using congrArg e.symm hy⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- A multiplicative equivalence carries the range of the `n`-th power map onto the corresponding
range. -/
theorem powMonoidHom_range_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).range).map e.toMonoidHom = (powMonoidHom n : H →* H).range := by
  exact e.map_range_powMonoidHom n

/-- A multiplicative equivalence transports `n`-torsion kernels. -/
theorem powMonoidHom_ker_map (n : ℕ) (e : G ≃* H) :
    ((powMonoidHom n : G →* G).ker).map e.toMonoidHom =
      (powMonoidHom n : H →* H).ker := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (MonoidHom.mem_ker (G := H)).2 (by
      have hxpow : x ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 hx
      change (e.toMonoidHom x) ^ n = 1
      simpa [map_pow] using congrArg e hxpow)
  · intro hy
    refine ⟨e.symm y, ?_, ?_⟩
    · exact (MonoidHom.mem_ker (G := G)).2 (by
      have hypow : y ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 hy
      change (e.symm y) ^ n = 1
      simpa [map_pow] using congrArg e.symm hypow)
    · simp

/-- An injective multiplicative homomorphism transports finiteness of the
ambient power kernel to the source power kernel. -/
theorem finite_nthPowerKernel_of_injective
    (n : ℕ) (f : G →* H) (hf : Function.Injective f)
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : G →* G).ker) := by
  let mapKernel : (powMonoidHom n : G →* G).ker →
      (powMonoidHom n : H →* H).ker := fun x =>
    ⟨f x, (MonoidHom.mem_ker (G := H)).2 (by
      have hx : (x : G) ^ n = 1 := by
        simpa only [powMonoidHom_apply] using
          (MonoidHom.mem_ker (G := G)).1 x.property
      rw [powMonoidHom_apply, ← map_pow, hx, map_one])⟩
  exact Finite.of_injective mapKernel fun x y hxy => by
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy)

/-- The power kernel in the unit group of a commutative ring is Mathlib's
group of roots of unity. -/
theorem powMonoidHom_ker_units_eq_rootsOfUnity
    (R : Type*) [CommRing R] (n : ℕ) :
    (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
  ext x
  exact MonoidHom.mem_ker

/-- For nonzero exponent over a domain, the unit-group power kernel is
finite because it is the finite set of roots of `X ^ n - 1`. -/
noncomputable instance finite_powMonoidHom_ker_units
    (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) [NeZero n] :
    Finite ((powMonoidHom n : Rˣ →* Rˣ).ker) := by
  rw [powMonoidHom_ker_units_eq_rootsOfUnity]
  infer_instance

/-- A multiplicative equivalence transports quotients by `n`-th powers. -/
def nthPowerQuotientEquivOfMulEquiv (n : ℕ) (e : G ≃* H) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr ((powMonoidHom n : G →* G).range) ((powMonoidHom n : H →* H).range) e
    (powMonoidHom_range_map G H n e)

/-- The quotient equivalence induced by a multiplicative equivalence maps each power-class
representative to its image. -/
theorem nthPowerQuotientEquivOfMulEquiv_mk (n : ℕ) (e : G ≃* H) (x : G) :
    nthPowerQuotientEquivOfMulEquiv G H n e
        (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x) =
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) (e x) :=
  rfl

/-- Finiteness of a power quotient transports backwards along a
multiplicative equivalence. -/
theorem finite_nthPowerQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* H)
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) :=
  Finite.of_equiv
    (H ⧸ (powMonoidHom n : H →* H).range)
    (nthPowerQuotientEquivOfMulEquiv G H n e).symm.toEquiv

/-- The `n`-torsion kernel of a product is the product of the two
`n`-torsion kernels. -/
def nthPowerKernelProductEquiv (n : ℕ) :
    (powMonoidHom n : (G × H) →* (G × H)).ker ≃*
      (powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker where
  toFun x :=
    (⟨(x : G × H).1, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hfst := congrArg Prod.fst hx
        simpa using hfst⟩,
      ⟨(x : G × H).2, by
        have hx : (x : G × H) ^ n = 1 :=
          (MonoidHom.mem_ker (G := G × H)).1 x.property
        have hsnd := congrArg Prod.snd hx
        simpa using hsnd⟩)
  invFun x :=
    ⟨((x.1 : G), (x.2 : H)), by
      have hx₁ : (x.1 : G) ^ n = 1 :=
        (MonoidHom.mem_ker (G := G)).1 x.1.property
      have hx₂ : (x.2 : H) ^ n = 1 :=
        (MonoidHom.mem_ker (G := H)).1 x.2.property
      change (((x.1 : G), (x.2 : H)) : G × H) ^ n = 1
      ext <;> simp [hx₁, hx₂]⟩
  left_inv x := by
    ext <;> rfl
  right_inv x := by
    ext <;> rfl
  map_mul' x y := by
    ext <;> rfl

/-- Finiteness of the two factor kernels transports across the canonical
product-kernel equivalence. -/
noncomputable instance finite_powMonoidHom_ker_prod (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Finite ((powMonoidHom n : (G × H) →* (G × H)).ker) :=
  Finite.of_equiv
    ((powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker)
    (nthPowerKernelProductEquiv G H n).symm.toEquiv

/-- General cardinal form of the product-kernel decomposition.  This is the
source of truth before any finiteness specialization. -/
theorem cardinal_mk_nthPowerKernelProduct (n : ℕ) :
    Cardinal.mk ((powMonoidHom n : (G × H) →* (G × H)).ker) =
      Cardinal.mk
        ((powMonoidHom n : G →* G).ker × (powMonoidHom n : H →* H).ker) :=
  Cardinal.mk_congr (nthPowerKernelProductEquiv G H n).toEquiv

/-- Cardinality form of `nthPowerKernelProductEquiv`. -/
theorem card_nthPowerKernelProduct (n : ℕ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)] :
    Nat.card ((powMonoidHom n : (G × H) →* (G × H)).ker) =
      Nat.card ((powMonoidHom n : G →* G).ker) *
        Nat.card ((powMonoidHom n : H →* H).ker) := by
  rw [Nat.card_congr (nthPowerKernelProductEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the cardinality of
the `n`-torsion kernel as the product of the two factor kernels. -/
theorem card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : H →* H).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : H →* H).ker) *
        Nat.card ((powMonoidHom n : U →* U).ker) := by
  calc
    Nat.card ((powMonoidHom n : G →* G).ker) =
        Nat.card ((powMonoidHom n : (H × U) →* (H × U)).ker) := by
      rw [Nat.card_congr
        (nthPowerKernelEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card ((powMonoidHom n : H →* H).ker) *
          Nat.card ((powMonoidHom n : U →* U).ker) :=
      card_nthPowerKernelProduct H U n

/-- General cardinal form of the kernel decomposition transported by a
multiplicative product equivalence. -/
theorem cardinal_mk_nthPowerKernel_eq_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U) :
    Cardinal.lift.{max uH uU, uG}
        (Cardinal.mk ((powMonoidHom n : G →* G).ker)) =
      Cardinal.lift.{uG, max uH uU} (Cardinal.mk
        ((powMonoidHom n : H →* H).ker × (powMonoidHom n : U →* U).ker)) :=
  Cardinal.mk_congr_lift
    ((nthPowerKernelEquivOfMulEquiv G (H × U) n e).trans
      (nthPowerKernelProductEquiv H U n)).toEquiv

/-- The product map from a product group to the product of its `n`-th-power
quotients. -/
def nthPowerProductQuotientHom (n : ℕ) :
    G × H →* (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) where
  toFun x :=
    (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
      QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Every pair of power classes is represented by a power class in the product group. -/
theorem nthPowerProductQuotientHom_surjective (n : ℕ) :
    Function.Surjective (nthPowerProductQuotientHom G H n) := by
  intro q
  rcases q with ⟨qG, qH⟩
  refine Quotient.inductionOn' qG ?_
  intro g
  refine Quotient.inductionOn' qH ?_
  intro h
  exact ⟨(g, h), rfl⟩

/-- The product power-class homomorphism has trivial kernel. -/
theorem nthPowerProductQuotientHom_ker (n : ℕ) :
    (nthPowerProductQuotientHom G H n).ker =
      (powMonoidHom n : (G × H) →* (G × H)).range := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change
      (QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1,
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2) = 1 at hx
    have hxG :
        QuotientGroup.mk' ((powMonoidHom n : G →* G).range) x.1 = 1 :=
      congrArg Prod.fst hx
    have hxH :
        QuotientGroup.mk' ((powMonoidHom n : H →* H).range) x.2 = 1 :=
      congrArg Prod.snd hx
    have hxGmem : x.1 ∈ (powMonoidHom n : G →* G).range :=
      (QuotientGroup.eq_one_iff x.1).1 hxG
    have hxHmem : x.2 ∈ (powMonoidHom n : H →* H).range :=
      (QuotientGroup.eq_one_iff x.2).1 hxH
    rw [MonoidHom.mem_range] at hxGmem hxHmem ⊢
    rcases hxGmem with ⟨g, hg⟩
    rcases hxHmem with ⟨h, hh⟩
    refine ⟨(g, h), ?_⟩
    ext
    · change g ^ n = x.1
      simpa only [powMonoidHom_apply] using hg
    · change h ^ n = x.2
      simpa only [powMonoidHom_apply] using hh
  · intro hx
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    apply Prod.ext
    · exact (QuotientGroup.eq_one_iff ((y.1) ^ n)).2
        ((MonoidHom.mem_range (G := G)).2 ⟨y.1, rfl⟩)
    · exact (QuotientGroup.eq_one_iff ((y.2) ^ n)).2
        ((MonoidHom.mem_range (G := H)).2 ⟨y.2, rfl⟩)

/-- Quotienting a product by `n`-th powers is the product of the two
`n`-th-power quotients. -/
def nthPowerProductQuotientEquiv (n : ℕ) :
    (G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range ≃*
      (G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range) :=
  (QuotientGroup.quotientMulEquivOfEq
      (nthPowerProductQuotientHom_ker G H n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (nthPowerProductQuotientHom G H n)
      (nthPowerProductQuotientHom_surjective G H n))

/-- Finiteness of the factor power quotients transports across the canonical
product-quotient equivalence. -/
noncomputable instance finite_powMonoidHom_rangeQuotient_prod (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Finite ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) :=
  Finite.of_equiv
    ((G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range))
    (nthPowerProductQuotientEquiv G H n).symm.toEquiv

/-- General cardinal form of the product-quotient decomposition. -/
theorem cardinal_mk_nthPowerProductQuotient (n : ℕ) :
    Cardinal.mk ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) =
      Cardinal.mk
        ((G ⧸ (powMonoidHom n : G →* G).range) × (H ⧸ (powMonoidHom n : H →* H).range)) :=
  Cardinal.mk_congr (nthPowerProductQuotientEquiv G H n).toEquiv

/-- The number of `n`-th power classes in a product is the product of the two factor class numbers.
The number of `n`-th power classes in a product is the product of the two factor class numbers. -/
theorem card_nthPowerProductQuotient (n : ℕ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)] :
    Nat.card ((G × H) ⧸ (powMonoidHom n : (G × H) →* (G × H)).range) =
      Nat.card (G ⧸ (powMonoidHom n : G →* G).range) *
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) := by
  rw [Nat.card_congr (nthPowerProductQuotientEquiv G H n).toEquiv,
    Nat.card_prod]

/-- A product decomposition of a commutative group splits the `n`-th-power
quotient index as the product of the two factor indices. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((H × U) ⧸ (powMonoidHom n : (H × U) →* (H × U)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (H × U) n e).toEquiv]
    _ =
        Nat.card (H ⧸ (powMonoidHom n : H →* H).range) *
          Nat.card (U ⧸ (powMonoidHom n : U →* U).range) :=
      card_nthPowerProductQuotient H U n

/-- General cardinal form of the quotient decomposition transported by a
multiplicative product equivalence. -/
theorem cardinal_mk_nthPowerQuotient_eq_of_mulEquiv_prod
    (n : ℕ) (e : G ≃* H × U) :
    Cardinal.lift.{max uH uU, uG}
        (Cardinal.mk (G ⧸ (powMonoidHom n : G →* G).range)) =
      Cardinal.lift.{uG, max uH uU} (Cardinal.mk
        ((H ⧸ (powMonoidHom n : H →* H).range) × (U ⧸ (powMonoidHom n : U →* U).range))) :=
  Cardinal.mk_congr_lift
    ((nthPowerQuotientEquivOfMulEquiv G (H × U) n e).trans
      (nthPowerProductQuotientEquiv H U n)).toEquiv

/-- For multiplicative integers, the range of the `n`-th power map is the subgroup of additive
multiples of `n`. -/
theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rw [mem_integerMultipleSubgroup_iff, powMonoidHom_apply, Int.toAdd_pow]
    exact ⟨y.toAdd, by ring⟩
  · intro hx
    rw [mem_integerMultipleSubgroup_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [powMonoidHom_apply, Int.toAdd_pow, toAdd_ofAdd, hk]
    ring

/-- For nonzero `n`, multiplicative integers modulo `n`-th powers form a finite quotient. -/
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative
      ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  exact Finite.of_equiv
    (Multiplicative (ZMod (n : ℤ).natAbs))
    (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ)).symm.toEquiv

/-- An explicit `G ≃ U × ℤ` decomposition transports finiteness of the
unit-factor power quotient to the full group.  This is deliberately a
constructor rather than a global instance: callers must expose the
decomposition and the exact finite boundary. -/
theorem finite_nthPowerQuotient_of_mulEquiv_units_prod_int
    {n : ℕ} [NeZero n] (e : G ≃* U × Multiplicative ℤ)
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  let : Finite
      (Multiplicative ℤ ⧸
        (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
    finite_multiplicativeInt_nthPowerQuotient (NeZero.ne n)
  exact finite_nthPowerQuotient_of_mulEquiv
    G (U × Multiplicative ℤ) n e

/-- General cardinal identification of the integer-direction power quotient.
For `n = 0` the right side is infinite; the natural-cardinality specialization
below is therefore intentionally restricted to `n ≠ 0`. -/
theorem cardinal_mk_multiplicativeInt_nthPowerQuotient (n : ℕ) :
    Cardinal.mk
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) =
      Cardinal.mk (Multiplicative (ZMod (n : ℤ).natAbs)) :=
  Cardinal.mk_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv

/-- For nonzero `n`, the multiplicative-integer power quotient has cardinality `n`. -/
theorem card_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0)
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative
      ℤ)).range)] :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) =
          n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.toAdd :
      Multiplicative (ZMod ((n : ℤ).natAbs)) ≃ ZMod ((n : ℤ).natAbs))]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  have hcard : Nat.card (ZMod ((n : ℤ).natAbs)) = (n : ℤ).natAbs :=
    Nat.card_zmod ((n : ℤ).natAbs)
  simp at hcard ⊢

/-- For nonzero `n`, the `n`-th power map on multiplicative integers has trivial kernel. -/
theorem powMonoidHom_ker_multiplicativeInt_eq_bot
    {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    have hmul : (n : ℤ) * Multiplicative.toAdd x = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa [Int.toAdd_pow] using h
    have hnZ : (n : ℤ) ≠ 0 := by
      exact_mod_cast hn
    exact (mul_eq_zero.mp hmul).resolve_left hnZ
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [MonoidHom.mem_ker, hx, powMonoidHom_apply, one_pow]

/-- The kernel of a nonzero power map on multiplicative integers is finite. -/
theorem finite_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0) :
    Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot (n := n) hn]
  infer_instance

/-- The kernel of a nonzero power map on multiplicative integers has one element. -/
theorem card_multiplicativeInt_nthPowerKernel
    {n : ℕ} (hn : n ≠ 0)
    [Finite ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker)] :
    Nat.card ((powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker) = 1 := by
  rw [powMonoidHom_ker_multiplicativeInt_eq_bot (n := n) hn]
  simp

/-- If a commutative group splits as `U × Multiplicative ℤ`, its `n`-th-power
quotient index is `n` times the corresponding quotient index for `U`. -/
theorem card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (U ⧸ (powMonoidHom n : U →* U).range)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
  let := finite_multiplicativeInt_nthPowerQuotient hn
  calc
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
        Nat.card ((U × Multiplicative ℤ) ⧸
          (powMonoidHom n : (U × Multiplicative ℤ) →* (U × Multiplicative ℤ)).range) := by
      rw [Nat.card_congr
        (nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).toEquiv]
    _ =
        Nat.card (U ⧸ (powMonoidHom n : U →* U).range) *
          Nat.card (Multiplicative ℤ ⧸
            (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) :=
      card_nthPowerProductQuotient U (Multiplicative ℤ) n
    _ = Nat.card (U ⧸ (powMonoidHom n : U →* U).range) * n := by
      rw [card_multiplicativeInt_nthPowerQuotient hn]
    _ = n * Nat.card (U ⧸ (powMonoidHom n : U →* U).range) := by
      rw [Nat.mul_comm]

/-- General cardinal form of the `U × Multiplicative ℤ` quotient
decomposition, valid without a nonzero or finiteness hypothesis. -/
theorem cardinal_mk_nthPowerQuotient_eq_of_mulEquiv_units_prod_int
    (n : ℕ) (e : G ≃* U × Multiplicative ℤ) :
    Cardinal.lift.{uU, uG} (Cardinal.mk (G ⧸ (powMonoidHom n : G →* G).range)) =
      Cardinal.lift.{uG, uU} (Cardinal.mk
        ((U ⧸ (powMonoidHom n : U →* U).range) ×
          (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative
            ℤ)).range))) :=
  Cardinal.mk_congr_lift
    ((nthPowerQuotientEquivOfMulEquiv G (U × Multiplicative ℤ) n e).trans
      (nthPowerProductQuotientEquiv U (Multiplicative ℤ) n)).toEquiv

/-- For nonzero `n`, a decomposition `G ≃ U × ℤ` identifies the `n`-torsion
kernel of `G` with the `n`-torsion kernel of the unit factor. -/
theorem card_nthPowerKernel_eq_of_mulEquiv_units_prod_int
    {n : ℕ} (hn : n ≠ 0) (e : G ≃* U × Multiplicative ℤ)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite ((powMonoidHom n : U →* U).ker)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card ((powMonoidHom n : U →* U).ker) := by
  let := finite_multiplicativeInt_nthPowerKernel hn
  rw [card_nthPowerKernel_eq_mul_of_mulEquiv_prod
    G U (Multiplicative ℤ) n e]
  rw [card_multiplicativeInt_nthPowerKernel hn, Nat.mul_one]

/-- General cardinal form of the `U × Multiplicative ℤ` kernel decomposition. -/
theorem cardinal_mk_nthPowerKernel_eq_of_mulEquiv_units_prod_int
    (n : ℕ) (e : G ≃* U × Multiplicative ℤ) :
    Cardinal.lift.{uU, uG}
        (Cardinal.mk ((powMonoidHom n : G →* G).ker)) =
      Cardinal.lift.{uG, uU} (Cardinal.mk
        ((powMonoidHom n : U →* U).ker ×
          (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).ker)) :=
  Cardinal.mk_congr_lift
    ((nthPowerKernelEquivOfMulEquiv G (U × Multiplicative ℤ) n e).trans
      (nthPowerKernelProductEquiv U (Multiplicative ℤ) n)).toEquiv

end NthPowers

section AdditivePowers

universe uA uB uG

variable (A : Type uA) [AddCommGroup A]

/-- The additive homomorphism `x ↦ n • x`. -/
abbrev nsmulAddHom (n : ℕ) : A →+ A :=
  nsmulAddMonoidHom n

/-- The additive subgroup of `n`-fold multiples. -/
abbrev nsmulAddSubgroup (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range

/-- The additive subgroup killed by `x ↦ n • x`. -/
abbrev nsmulAddKernel (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).ker

/-- Membership in the image of multiplication by `n` is equivalent to being an `n`-fold additive
multiple. -/
theorem mem_nsmulAddSubgroup_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddSubgroup A n ↔ ∃ y : A, n • y = x := by
  simp [nsmulAddSubgroup, AddMonoidHom.mem_range]

/-- Membership in the kernel of multiplication by `n` is equivalent to being annihilated by `n`. -/
theorem mem_nsmulAddKernel_iff {n : ℕ} {x : A} :
    x ∈ nsmulAddKernel A n ↔ n • x = 0 := by
  simp [nsmulAddKernel, AddMonoidHom.mem_ker]

/-- Under the `Multiplicative` wrapper, `n`-th powers are exactly additive
`n`-fold multiples. -/
theorem powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range =
      AddSubgroup.toSubgroup (nsmulAddSubgroup A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    rw [MonoidHom.mem_range]
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddSubgroup A n := by
      simpa using hx
    rw [mem_nsmulAddSubgroup_iff] at hxadd
    rcases hxadd with ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [hy]

/-- General cardinal form of the multiplicative/additive quotient
translation. -/
theorem cardinal_mk_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ) :
    Cardinal.mk
        (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) =
      Cardinal.mk (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  rfl

/-- The underlying quotient types in multiplicative and additive notation
are canonically equivalent. -/
def multiplicativeNthPowerQuotientEquivAdditive (n : ℕ) :
    (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) ≃
      (A ⧸ nsmulAddSubgroup A n) := by
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive quotient transports to its multiplicative
presentation without any choice of representatives. -/
noncomputable instance finite_multiplicative_nthPowerQuotient
    (n : ℕ) [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Finite
      (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range) :=
  Finite.of_equiv (A ⧸ nsmulAddSubgroup A n)
    (multiplicativeNthPowerQuotientEquivAdditive A n).symm

/-- Cardinality/index form of
`powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup`. -/
theorem card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative
      A)).range)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative
      A)).range) =
      (nsmulAddSubgroup A n).index := by
  rw [← Subgroup.index_eq_card
    (H := (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
  rw [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup]
  simp

/-- Under logarithmic/additive notation, the `n`-th-power quotient is the
additive quotient by `n`-fold multiples. -/
theorem card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient
    (n : ℕ)
    [Finite (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (Multiplicative A ⧸ (powMonoidHom n : (Multiplicative A) →* (Multiplicative
      A)).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [card_multiplicative_nthPowerQuotient_eq_nsmulAddSubgroup_index]
  rw [AddSubgroup.index_eq_card]

/-- Under the `Multiplicative` wrapper, `n`-torsion is exactly the additive
kernel of `x ↦ n • x`. -/
theorem powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker =
      AddSubgroup.toSubgroup (nsmulAddKernel A n) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.toAdd x ∈ nsmulAddKernel A n
    rw [mem_nsmulAddKernel_iff]
    have h := congrArg Multiplicative.toAdd hx
    simpa using h
  · intro hx
    have hxadd : Multiplicative.toAdd x ∈ nsmulAddKernel A n := by
      simpa using hx
    rw [mem_nsmulAddKernel_iff] at hxadd
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    simpa using hxadd

/-- General cardinal form of the multiplicative/additive kernel
translation. -/
theorem cardinal_mk_multiplicative_nthPowerKernel_eq_nsmulAddKernel
    (n : ℕ) :
    Cardinal.mk ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) =
      Cardinal.mk (nsmulAddKernel A n) := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  rfl

/-- The multiplicative power kernel and additive scalar kernel have the same
underlying type. -/
def multiplicativeNthPowerKernelEquivAdditive (n : ℕ) :
    (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker ≃ nsmulAddKernel A n := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  exact Equiv.refl _

/-- Finiteness of the additive scalar kernel transports to multiplicative
notation without introducing a noncanonical enumeration. -/
noncomputable instance finite_multiplicative_nthPowerKernel
    (n : ℕ) [Finite (nsmulAddKernel A n)] :
    Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) :=
  Finite.of_equiv (nsmulAddKernel A n)
    (multiplicativeNthPowerKernelEquivAdditive A n).symm

section AdditiveProducts

variable (B : Type uB) [AddCommGroup B]

/-- Finiteness of additive scalar quotients is stable under binary products. -/
noncomputable instance finite_nsmulAddQuotient_prod (n : ℕ)
    [Finite (A ⧸ nsmulAddSubgroup A n)]
    [Finite (B ⧸ nsmulAddSubgroup B n)] :
    Finite ((A × B) ⧸ nsmulAddSubgroup (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      (Multiplicative (A × B) ⧸
        (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range) :=
    finite_nthPowerQuotient_of_mulEquiv
      (Multiplicative (A × B))
      (Multiplicative A × Multiplicative B) n e
  exact Finite.of_equiv
    (Multiplicative (A × B) ⧸
      (powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).range)
    (multiplicativeNthPowerQuotientEquivAdditive (A × B) n)

/-- Finiteness of additive scalar kernels is stable under binary products. -/
noncomputable instance finite_nsmulAddKernel_prod (n : ℕ)
    [Finite (nsmulAddKernel A n)]
    [Finite (nsmulAddKernel B n)] :
    Finite (nsmulAddKernel (A × B) n) := by
  let e := MulEquiv.prodMultiplicative A B
  let : Finite
      ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker) :=
    Finite.of_equiv
      ((powMonoidHom n : (Multiplicative A × Multiplicative B) →* (Multiplicative A ×
        Multiplicative B)).ker)
      (nthPowerKernelEquivOfMulEquiv
        (Multiplicative (A × B))
        (Multiplicative A × Multiplicative B) n e).symm.toEquiv
  exact Finite.of_equiv
    ((powMonoidHom n : (Multiplicative (A × B)) →* (Multiplicative (A × B))).ker)
    (multiplicativeNthPowerKernelEquivAdditive (A × B) n)

end AdditiveProducts

/-- Cardinality form of the multiplicative/additive kernel translation. -/
theorem card_multiplicative_nthPowerKernel_eq_nsmulAddKernel
    (n : ℕ)
    [Finite ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup]
  rfl

/-- Finite additive kernel/cokernel equality for the map `x ↦ n • x`, proved
through the multiplicative `n`-th-power translation. -/
theorem card_additive_nsmulQuotient_eq_nsmulKernel
    [Finite A] (n : ℕ) :
    Nat.card (A ⧸ nsmulAddSubgroup A n) =
      Nat.card (nsmulAddKernel A n) := by
  rw [← card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n]
  rw [card_nthPowerQuotient_eq_nthPowerKernel
    (Multiplicative A) n]
  exact card_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n

variable (G : Type uG) [CommGroup G]

/-- General cardinal form of a logarithmic quotient transport. -/
theorem cardinal_mk_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A) :
    Cardinal.lift.{uA, uG} (Cardinal.mk (G ⧸ (powMonoidHom n : G →* G).range)) =
      Cardinal.lift.{uG, uA} (Cardinal.mk (A ⧸ nsmulAddSubgroup A n)) := by
  calc
    Cardinal.lift.{uA, uG} (Cardinal.mk (G ⧸ (powMonoidHom n : G →* G).range)) =
        Cardinal.lift.{uG, uA}
          (Cardinal.mk (Multiplicative A ⧸
            (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range)) :=
      Cardinal.mk_congr_lift
        (nthPowerQuotientEquivOfMulEquiv G (Multiplicative A) n e).toEquiv
    _ = Cardinal.lift.{uG, uA}
        (Cardinal.mk (A ⧸ nsmulAddSubgroup A n)) :=
      congrArg Cardinal.lift
        (cardinal_mk_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n)

/-- A logarithmic multiplicative equivalence transports an `n`-th-power quotient
to the additive quotient by `n`-fold multiples. -/
theorem card_nthPowerQuotient_eq_additive_nsmulQuotient_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite (G ⧸ (powMonoidHom n : G →* G).range)]
    [Finite (A ⧸ nsmulAddSubgroup A n)] :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      Nat.card (A ⧸ nsmulAddSubgroup A n) := by
  rw [Nat.card_congr
    (nthPowerQuotientEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerQuotient_eq_additive_nsmulQuotient A n

/-- A logarithmic multiplicative equivalence transports the `n`-torsion kernel
to the additive kernel of `x ↦ n • x`. -/
theorem card_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A)
    [Finite ((powMonoidHom n : G →* G).ker)]
    [Finite (nsmulAddKernel A n)] :
    Nat.card ((powMonoidHom n : G →* G).ker) =
      Nat.card (nsmulAddKernel A n) := by
  rw [Nat.card_congr
    (nthPowerKernelEquivOfMulEquiv G (Multiplicative A) n e).toEquiv]
  exact card_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n

/-- General cardinal form of a logarithmic kernel transport. -/
theorem cardinal_mk_nthPowerKernel_eq_additive_nsmulKernel_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A) :
    Cardinal.lift.{uA, uG}
        (Cardinal.mk ((powMonoidHom n : G →* G).ker)) =
      Cardinal.lift.{uG, uA} (Cardinal.mk (nsmulAddKernel A n)) := by
  calc
    Cardinal.lift.{uA, uG}
        (Cardinal.mk ((powMonoidHom n : G →* G).ker)) =
      Cardinal.lift.{uG, uA}
        (Cardinal.mk ((powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker)) :=
      Cardinal.mk_congr_lift
        (nthPowerKernelEquivOfMulEquiv G (Multiplicative A) n e).toEquiv
    _ = Cardinal.lift.{uG, uA} (Cardinal.mk (nsmulAddKernel A n)) :=
      congrArg Cardinal.lift
        (cardinal_mk_multiplicative_nthPowerKernel_eq_nsmulAddKernel A n)

/-- Under a logarithmic multiplicative equivalence, the `n`-th-power subgroup
is the inverse image of the additive `n`-fold-multiple subgroup. -/
theorem powMonoidHom_range_eq_comap_nsmulAddSubgroup_toSubgroup_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A) :
    (powMonoidHom n : G →* G).range =
      (AddSubgroup.toSubgroup (nsmulAddSubgroup A n)).comap e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    change e x ∈ AddSubgroup.toSubgroup (nsmulAddSubgroup A n)
    have hxpow : e x ∈ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range := by
      rw [MonoidHom.mem_range] at hx ⊢
      rcases hx with ⟨y, hy⟩
      refine ⟨e y, ?_⟩
      rw [← hy]
      simp only [powMonoidHom_apply, map_pow]
    simpa [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
      (A := A) n] using hxpow
  · intro hx
    change e x ∈ AddSubgroup.toSubgroup (nsmulAddSubgroup A n) at hx
    have hxpow : e x ∈ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).range := by
      simpa [powMonoidHom_range_multiplicative_eq_nsmulAddSubgroup_toSubgroup
        (A := A) n] using hx
    rw [MonoidHom.mem_range] at hxpow
    rcases hxpow with ⟨y, hy⟩
    rw [MonoidHom.mem_range]
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [powMonoidHom_apply] at hy
    rw [powMonoidHom_apply, map_pow, MulEquiv.apply_symm_apply, hy]

/-- Kernel version of
`powMonoidHom_range_eq_comap_nsmulAddSubgroup_toSubgroup_of_mulEquiv`. -/
theorem powMonoidHom_ker_eq_comap_nsmulAddKernel_toSubgroup_of_mulEquiv
    (n : ℕ) (e : G ≃* Multiplicative A) :
    (powMonoidHom n : G →* G).ker =
      (AddSubgroup.toSubgroup (nsmulAddKernel A n)).comap e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    change e x ∈ AddSubgroup.toSubgroup (nsmulAddKernel A n)
    have hxker : e x ∈ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker := by
      exact (MonoidHom.mem_ker
        (G := Multiplicative A)).2 (by
        have hxpow : x ^ n = 1 :=
          (MonoidHom.mem_ker (G := G)).1 hx
        change (e x) ^ n = 1
        simpa [map_pow] using congrArg e hxpow)
    simpa [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
      (A := A) n] using hxker
  · intro hx
    change e x ∈ AddSubgroup.toSubgroup (nsmulAddKernel A n) at hx
    have hxker : e x ∈ (powMonoidHom n : (Multiplicative A) →* (Multiplicative A)).ker := by
      simpa [powMonoidHom_ker_multiplicative_eq_nsmulAddKernel_toSubgroup
        (A := A) n] using hx
    rw [MonoidHom.mem_ker] at hxker ⊢
    apply e.injective
    simpa [map_pow] using hxker

/-- If the additive `n`-fold multiples have already been identified with a
specific additive subgroup, a logarithmic equivalence transports that equality
back to the original multiplicative group. -/
theorem powMonoidHom_range_eq_comap_toSubgroup_of_nsmulAddSubgroup_eq
    (n : ℕ) (e : G ≃* Multiplicative A) (B : AddSubgroup A)
    (hB : nsmulAddSubgroup A n = B) :
    (powMonoidHom n : G →* G).range =
      (AddSubgroup.toSubgroup B).comap e.toMonoidHom := by
  rw [← hB]
  exact powMonoidHom_range_eq_comap_nsmulAddSubgroup_toSubgroup_of_mulEquiv
    (A := A) (G := G) n e

/-- Kernel analogue of
`powMonoidHom_range_eq_comap_toSubgroup_of_nsmulAddSubgroup_eq`. -/
theorem powMonoidHom_ker_eq_comap_toSubgroup_of_nsmulAddKernel_eq
    (n : ℕ) (e : G ≃* Multiplicative A) (B : AddSubgroup A)
    (hB : nsmulAddKernel A n = B) :
    (powMonoidHom n : G →* G).ker =
      (AddSubgroup.toSubgroup B).comap e.toMonoidHom := by
  rw [← hB]
  exact powMonoidHom_ker_eq_comap_nsmulAddKernel_toSubgroup_of_mulEquiv
    (A := A) (G := G) n e

end AdditivePowers

end LocalFieldTheory

end
