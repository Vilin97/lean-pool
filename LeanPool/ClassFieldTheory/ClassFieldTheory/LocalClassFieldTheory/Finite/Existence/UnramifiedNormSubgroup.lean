/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
/-!
# Unramified norm subgroups

For a nonarchimedean local field, the norm subgroup of an unramified
extension of degree n is characterized by divisibility of the normalized
valuation by n. This file packages that subgroup, its quotient map, and
the canonical identification of the quotient with ZMod n.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalClassFieldTheory

/-- The normalized valuation map reduced modulo a positive or zero degree n. -/
noncomputable def valuationModDegree (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Additive Kˣ →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K)

/-- Evaluates the normalized valuation map after reduction modulo `n`. -/
@[simp]
theorem valuationModDegree_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ) :
    valuationModDegree K n x =
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n) :=
  rfl

/-- The normalized valuation remains surjective after reduction modulo `n`. -/
theorem valuationModDegree_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Function.Surjective (valuationModDegree K n) := by
  intro z
  rcases ZMod.intCast_surjective z with ⟨m, rfl⟩
  rcases LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective K m with ⟨x, hx⟩
  exact ⟨x, by simp [hx]⟩

/-- A reduced valuation vanishes exactly when `n` divides the original valuation. -/
theorem valuationModDegree_eq_zero_iff_dvd (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ) :
    valuationModDegree K n x = 0 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x := by
  rw [valuationModDegree_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) n

/-- Two reduced valuations agree exactly when `n` divides their difference. -/
theorem valuationModDegree_eq_iff_dvd_sub (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x y : Additive Kˣ) :
    valuationModDegree K n x = valuationModDegree K n y ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K y := by
  rw [← sub_eq_zero, ← map_sub, valuationModDegree_eq_zero_iff_dvd, map_sub]

/-- Multiplicative form of the normalized valuation map modulo a degree. -/
noncomputable def valuationModDegreeMulHom (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Kˣ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicativeRight (valuationModDegree K n)

/-- Evaluates the multiplicative form of the valuation-modulo-degree map. -/
@[simp]
theorem valuationModDegreeMulHom_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ) :
    valuationModDegreeMulHom K n x =
      Multiplicative.ofAdd
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) : ZMod n) :=
  rfl

/-- The multiplicative valuation-modulo-degree map is surjective. -/
theorem valuationModDegreeMulHom_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Function.Surjective (valuationModDegreeMulHom K n) := by
  intro z
  rcases valuationModDegree_surjective K n (Multiplicative.toAdd z) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  apply Multiplicative.toAdd.injective
  simpa using hx

/-- A unit maps to one exactly when its valuation is divisible by `n`. -/
theorem valuationModDegreeMulHom_eq_one_iff_dvd (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    valuationModDegreeMulHom K n x = 1 ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  change valuationModDegree K n (Additive.ofMul x) = 0 ↔ _
  exact valuationModDegree_eq_zero_iff_dvd K n (Additive.ofMul x)

/-- Two units have the same image exactly when `n` divides their valuation difference. -/
theorem valuationModDegreeMulHom_eq_iff_dvd_sub (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x y : Kˣ) :
    valuationModDegreeMulHom K n x = valuationModDegreeMulHom K n y ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y) := by
  change valuationModDegree K n (Additive.ofMul x) =
      valuationModDegree K n (Additive.ofMul y) ↔ _
  exact valuationModDegree_eq_iff_dvd_sub K n (Additive.ofMul x) (Additive.ofMul y)

/-- The unramified norm subgroup of degree `n`: field units whose normalized
valuation lies in `nℤ`. -/
def unramifiedNormSubgroup (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) : Subgroup Kˣ where
  carrier := {x | (n : Int) ∣
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)}
  one_mem' := by
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (1 : Kˣ))
    rw [show Additive.ofMul (1 : Kˣ) = 0 by rfl, map_zero]
    exact dvd_zero (n : Int)
  mul_mem' := by
    intro x y hx hy
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (x * y))
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y by rfl,
      map_add]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x⁻¹)
    rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x by rfl, map_neg]
    exact dvd_neg.mpr hx

/-- Characterizes the unramified norm subgroup by divisibility of the normalized valuation. -/
theorem mem_unramifiedNormSubgroup_iff (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ) :
    x ∈ unramifiedNormSubgroup K n ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) :=
  Iff.rfl

/-- The quotient map from field units to degree-`n` unramified norm classes. -/
def unramifiedNormClass (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Kˣ →* Kˣ ⧸ unramifiedNormSubgroup K n :=
  QuotientGroup.mk' (unramifiedNormSubgroup K n)

/-- Every unramified norm class is represented by a field unit. -/
theorem unramifiedNormClass_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Function.Surjective (unramifiedNormClass K n) :=
  QuotientGroup.mk'_surjective (unramifiedNormSubgroup K n)

/-- The kernel of the quotient map is the unramified norm subgroup. -/
theorem unramifiedNormClass_ker (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    MonoidHom.ker (unramifiedNormClass K n) =
      unramifiedNormSubgroup K n :=
  QuotientGroup.ker_mk' (N := unramifiedNormSubgroup K n)

/-- A unit has trivial norm class exactly when its valuation is divisible by the degree. -/
theorem unramifiedNormClass_eq_one_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
        := by
  exact (QuotientGroup.eq_one_iff (N := unramifiedNormSubgroup K n) x).trans
    (mem_unramifiedNormSubgroup_iff K n x)

/-- A unit has trivial norm class exactly when it belongs to the unramified norm subgroup. -/
theorem unramifiedNormClass_eq_one_iff_mem (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔ x ∈ unramifiedNormSubgroup K n := by
  rw [unramifiedNormClass_eq_one_iff, mem_unramifiedNormSubgroup_iff]

/-- The unramified norm subgroup is the kernel of the multiplicative reduced valuation. -/
theorem unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n := by
  ext x
  rw [MonoidHom.mem_ker, mem_unramifiedNormSubgroup_iff,
    valuationModDegreeMulHom_eq_one_iff_dvd]

/-- Membership in the unramified norm subgroup is detected by the reduced valuation. -/
theorem mem_unramifiedNormSubgroup_iff_valuationModDegreeMulHom_eq_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ) :
    x ∈ unramifiedNormSubgroup K n ↔ valuationModDegreeMulHom K n x = 1 := by
  rw [mem_unramifiedNormSubgroup_iff, valuationModDegreeMulHom_eq_one_iff_dvd]

/-- The valuation quotient model
`Kˣ / {x | n ∣ v(x)} ≃ Z/nZ`, in multiplicative notation. -/
noncomputable def unramifiedNormQuotientEquivZMod (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    Kˣ ⧸ unramifiedNormSubgroup K n ≃* Multiplicative (ZMod n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom K n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (valuationModDegreeMulHom K n)
      (valuationModDegreeMulHom_surjective K n))

/-- The quotient equivalence sends a unit class to its valuation modulo the degree. -/
@[simp]
theorem unramifiedNormQuotientEquivZMod_mk (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormQuotientEquivZMod K n (QuotientGroup.mk x) =
      valuationModDegreeMulHom K n x := by
  simp only [unramifiedNormQuotientEquivZMod, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]

/-- Cardinality of the valuation quotient for arbitrary `n`.  This statement
remains meaningful at `n = 0`, when `ZMod 0` and the quotient are infinite. -/
theorem unramifiedNormQuotient_cardinal_eq_zmod (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    Cardinal.mk (Kˣ ⧸ unramifiedNormSubgroup K n) =
      Cardinal.lift (Cardinal.mk (ZMod n)) := by
  simpa only [Cardinal.lift_id'] using Cardinal.mk_congr_lift
    ((unramifiedNormQuotientEquivZMod K n).toEquiv.trans
      (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n))

/-- A nonzero valuation modulus gives a finite norm quotient. -/
noncomputable instance finiteUnramifiedNormQuotient (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) [NeZero n] : Finite (Kˣ ⧸ unramifiedNormSubgroup K n) :=
  Finite.of_equiv (Multiplicative (ZMod n))
    (unramifiedNormQuotientEquivZMod K n).symm.toEquiv

/-- For nonzero degree, the unramified norm quotient has cardinality equal to that degree. -/
theorem unramifiedNormQuotient_card_eq_degree (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n := by
  calc
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) =
        Nat.card (Multiplicative (ZMod n)) :=
      Nat.card_congr (unramifiedNormQuotientEquivZMod K n).toEquiv
    _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
    _ = n := Nat.card_zmod n

/-- Two units define the same norm class exactly when the degree divides their valuation
difference. -/
theorem unramifiedNormClass_eq_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x y : Kˣ) :
    unramifiedNormClass K n x =
        unramifiedNormClass K n y ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y) := by
  change (QuotientGroup.mk x : Kˣ ⧸ unramifiedNormSubgroup K n) =
      QuotientGroup.mk y ↔ _
  constructor
  · intro h
    have hmap := congrArg (unramifiedNormQuotientEquivZMod K n) h
    rw [unramifiedNormQuotientEquivZMod_mk,
      unramifiedNormQuotientEquivZMod_mk] at hmap
    exact (valuationModDegreeMulHom_eq_iff_dvd_sub K n x y).1 hmap
  · intro h
    apply (unramifiedNormQuotientEquivZMod K n).injective
    rw [unramifiedNormQuotientEquivZMod_mk,
      unramifiedNormQuotientEquivZMod_mk]
    exact (valuationModDegreeMulHom_eq_iff_dvd_sub K n x y).2 h

/-- The quotient images agree exactly when the reduced valuation difference vanishes. -/
theorem unramifiedNormQuotientEquivZMod_eq_iff_valuation_sub_eq_zero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x y : Kˣ) :
    unramifiedNormQuotientEquivZMod K n
        (unramifiedNormClass K n x) =
        unramifiedNormQuotientEquivZMod K n
          (unramifiedNormClass K n y) ↔
      ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) -
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y) : Int) :
        ZMod n) = 0 := by
  change unramifiedNormQuotientEquivZMod K n
        (QuotientGroup.mk x : Kˣ ⧸ unramifiedNormSubgroup K n) =
        unramifiedNormQuotientEquivZMod K n
          (QuotientGroup.mk y : Kˣ ⧸ unramifiedNormSubgroup K n) ↔ _
  rw [unramifiedNormQuotientEquivZMod_mk,
    unramifiedNormQuotientEquivZMod_mk, valuationModDegreeMulHom_apply,
    valuationModDegreeMulHom_apply]
  change
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) : ZMod n) =
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y) : ZMod n) ↔
    ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) -
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul y) : Int) :
      ZMod n) = 0
  rw [Int.cast_sub, sub_eq_zero]


end LocalClassFieldTheory
