/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Hahn series with strictly negative support

This file defines the series denoted by `K((G^{<0}))` in LM24, Section 2.1. Inside the ring of
nonpositive Hahn series, they are exactly the kernel of the constant-coefficient homomorphism.
This realizes them simultaneously as a two-sided ideal and as a nonunital ring.

For a coefficient subring `Z`, the truncation integer part is proved to have the source
presentation `Z + K((G^{<0}))`. The Lean definition remains the intrinsic pullback along the
constant-coefficient homomorphism; the presentation theorem supplies the exact printed form
without replacing the carrier by a chosen pair of summands.
-/

open scoped Pointwise

universe u v

public noncomputable section

namespace HahnSeries

variable (Γ : Type u) (R : Type v)
variable [AddCommGroup Γ] [PartialOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

/-- The ideal of nonpositive Hahn series with zero constant coefficient. Its elements are exactly
the Hahn series with strictly negative support. -/
def negativeIdeal : Ideal (Nonpositive Γ R) :=
  RingHom.ker (Nonpositive.constantCoeff (Γ := Γ) (R := R))

/-- Membership in `negativeIdeal` means that every support exponent is strictly negative. -/
@[simp]
theorem mem_negativeIdeal {x : Nonpositive Γ R} :
    x ∈ negativeIdeal Γ R ↔ (x : R⟦Γ⟧).support ⊆ Set.Iio 0 := by
  rw [negativeIdeal, RingHom.mem_ker, Nonpositive.constantCoeff_apply]
  constructor
  · intro hx g hg
    have hg_nonpos := Nonpositive.support_subset x hg
    have hg_ne : g ≠ 0 := by
      intro hg0
      subst g
      exact (HahnSeries.mem_support (x : R⟦Γ⟧) 0).mp hg hx
    exact lt_of_le_of_ne hg_nonpos hg_ne
  · intro hx
    by_contra h0
    exact (hx ((HahnSeries.mem_support (x : R⟦Γ⟧) 0).mpr h0)).ne rfl

/-- Strictly negative Hahn series, represented as the subtype of `negativeIdeal`. -/
abbrev Negative := ↥(negativeIdeal Γ R)

instance negativeIdealIsTwoSided : (negativeIdeal Γ R).IsTwoSided := by
  change (RingHom.ker (Nonpositive.constantCoeff (Γ := Γ) (R := R))).IsTwoSided
  infer_instance

namespace Negative

variable {Γ R}

/-- A strictly negative Hahn series has zero constant coefficient. -/
theorem constantCoeff_eq_zero (x : Negative Γ R) :
    Nonpositive.constantCoeff (Γ := Γ) (R := R) x = 0 :=
  RingHom.mem_ker.mp x.2

/-- The coefficient at exponent zero of a strictly negative Hahn series is zero. -/
@[simp]
theorem coeff_zero (x : Negative Γ R) : (x : R⟦Γ⟧).coeff 0 = 0 := by
  rw [← Nonpositive.constantCoeff_apply]
  exact constantCoeff_eq_zero x

/-- The support of a strictly negative Hahn series is contained in `Set.Iio 0`. -/
theorem support_subset (x : Negative Γ R) :
    (x : R⟦Γ⟧).support ⊆ Set.Iio 0 :=
  (mem_negativeIdeal (Γ := Γ) (R := R)).mp x.2

/-- A single monomial with strictly negative exponent, regarded as a strictly negative Hahn
series. -/
def single (g : Γ) (r : R) (hg : g < 0) : Negative Γ R :=
  ⟨Nonpositive.single g r hg.le, by
    rw [negativeIdeal, RingHom.mem_ker, Nonpositive.constantCoeff_apply,
      Nonpositive.coe_single]
    exact HahnSeries.coeff_single_of_ne hg.ne'⟩

@[simp]
theorem coe_single (g : Γ) (r : R) (hg : g < 0) :
    (single g r hg : R⟦Γ⟧) = HahnSeries.single g r :=
  Nonpositive.coe_single g r hg.le

end Negative

namespace Nonpositive

/-- Remove the constant coefficient from a nonpositive Hahn series. -/
def negativePart : Nonpositive Γ R →+ Negative Γ R where
  toFun x := ⟨x - C (constantCoeff x), by
    rw [negativeIdeal, RingHom.mem_ker]
    simp⟩
  map_zero' := by ext; simp
  map_add' x y := by
    apply Subtype.ext
    change x + y - C (constantCoeff (x + y)) =
      (x - C (constantCoeff x)) + (y - C (constantCoeff y))
    rw [map_add, map_add]
    abel

@[simp]
theorem coe_negativePart (x : Nonpositive Γ R) :
    (negativePart Γ R x : Nonpositive Γ R) = x - C (constantCoeff x) :=
  (rfl)

/-- The support of the strictly negative part is the intersection of the original support with
the strict negative cone. -/
theorem support_negativePart (x : Nonpositive Γ R) :
    ((negativePart Γ R x : Negative Γ R) : R⟦Γ⟧).support =
      (x : R⟦Γ⟧).support ∩ Set.Iio 0 := by
  ext g
  rw [HahnSeries.mem_support]
  by_cases hg : g = 0
  · subst g
    simp
  · have hnegativePart := congrArg Subtype.val (coe_negativePart Γ R x)
    have hsub := map_sub (nonpositiveSubring Γ R).subtype x (C (constantCoeff x))
    rw [hnegativePart]
    change
      (((nonpositiveSubring Γ R).subtype (x - C (constantCoeff x))).coeff g ≠ 0) ↔
        g ∈ (x : R⟦Γ⟧).support ∩ Set.Iio 0
    rw [hsub, HahnSeries.coeff_sub]
    simp only [Subring.coe_subtype]
    rw [coe_C]
    change
      ((x : R⟦Γ⟧).coeff g -
          (HahnSeries.C (constantCoeff x) : R⟦Γ⟧).coeff g ≠ 0) ↔
        g ∈ (x : R⟦Γ⟧).support ∩ Set.Iio 0
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg, sub_zero,
      Set.mem_inter_iff, Set.mem_Iio]
    rw [HahnSeries.mem_support]
    constructor
    · intro hx
      exact ⟨hx, lt_of_le_of_ne (support_subset x hx) hg⟩
    · exact fun hx ↦ hx.1

/-- A nonpositive Hahn series is the sum of its constant term and its strictly negative part. -/
theorem constant_add_negativePart (x : Nonpositive Γ R) :
    C (constantCoeff x) + (negativePart Γ R x : Nonpositive Γ R) = x := by
  rw [coe_negativePart]
  abel

/-- The strictly negative part of a constant series is zero. -/
@[simp]
theorem negativePart_C (r : R) :
    negativePart Γ R (C (Γ := Γ) (R := R) r) = 0 := by
  apply Subtype.ext
  rw [coe_negativePart]
  simp

/-- Removing the constant coefficient from a strictly negative series leaves it unchanged. -/
@[simp]
theorem negativePart_coe (x : Negative Γ R) :
    negativePart Γ R (x : Nonpositive Γ R) = x := by
  apply Subtype.ext
  rw [coe_negativePart, Negative.constantCoeff_eq_zero]
  simp

end Nonpositive

/-- The image in the nonpositive Hahn ring of a subring of the coefficient ring. -/
def constantSubring (Z : Subring R) : Subring (Nonpositive Γ R) :=
  Z.map (Nonpositive.C (Γ := Γ) (R := R))

/-- Membership in the constant copy of `Z` means equality with the constant series attached to
some element of `Z`. -/
theorem mem_constantSubring {Z : Subring R} {x : Nonpositive Γ R} :
    x ∈ constantSubring Γ R Z ↔
      ∃ z : Z, Nonpositive.C (Γ := Γ) (R := R) z = x := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact Subring.mem_map.mpr ⟨z, z.2, rfl⟩

/-- A nonpositive Hahn series belongs to the truncation integer part exactly when it is the sum
of a constant series from `Z` and a strictly negative Hahn series. -/
theorem mem_truncationIntegerPart_iff_exists_add_negative {Z : Subring R}
    {x : Nonpositive Γ R} :
    x ∈ truncationIntegerPart Γ Z ↔
      ∃ z : Z, ∃ n : Negative Γ R,
        x = Nonpositive.C (Γ := Γ) (R := R) z + (n : Nonpositive Γ R) := by
  constructor
  · intro hx
    have hz : Nonpositive.constantCoeff x ∈ Z := by
      rw [Nonpositive.constantCoeff_apply]
      exact (mem_truncationIntegerPart (Γ := Γ) (R := R)).mp hx
    let z : Z := ⟨Nonpositive.constantCoeff x, hz⟩
    exact ⟨z, Nonpositive.negativePart Γ R x, by
      exact (Nonpositive.constant_add_negativePart Γ R x).symm⟩
  · rintro ⟨z, n, rfl⟩
    rw [mem_truncationIntegerPart, ← Nonpositive.constantCoeff_apply, map_add]
    rw [Negative.constantCoeff_eq_zero]
    simp

/-- The expression of a nonpositive Hahn series as a constant series from `Z` plus a strictly
negative series is unique. -/
theorem constant_add_negative_eq_iff {Z : Subring R} {z z' : Z} {n n' : Negative Γ R} :
    Nonpositive.C (Γ := Γ) (R := R) z + (n : Nonpositive Γ R) =
        Nonpositive.C (Γ := Γ) (R := R) z' + (n' : Nonpositive Γ R) ↔
      z = z' ∧ n = n' := by
  constructor
  · intro h
    have hz : (z : R) = z' := by
      calc
        (z : R) = Nonpositive.constantCoeff (Γ := Γ) (R := R)
            (Nonpositive.C (Γ := Γ) (R := R) z + n) := by
              rw [map_add, Negative.constantCoeff_eq_zero]
              simp
        _ = Nonpositive.constantCoeff (Γ := Γ) (R := R)
            (Nonpositive.C (Γ := Γ) (R := R) z' + n') := congrArg _ h
        _ = (z' : R) := by
          rw [map_add, Negative.constantCoeff_eq_zero]
          simp
    have hzz : z = z' := Subtype.ext hz
    subst z'
    exact ⟨rfl, Subtype.ext (add_left_cancel h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The carrier of a truncation integer part is the pointwise sum of the constant copy of `Z`
and the ideal of strictly negative Hahn series. This is the equality
`Z + K((G^{<0}))` used in LM24. -/
theorem coe_truncationIntegerPart_eq_constantSubring_add_negativeIdeal (Z : Subring R) :
    (truncationIntegerPart Γ Z : Set (Nonpositive Γ R)) =
      (constantSubring Γ R Z : Set (Nonpositive Γ R)) +
        (negativeIdeal Γ R : Set (Nonpositive Γ R)) := by
  ext x
  rw [Set.mem_add]
  constructor
  · intro hx
    rcases (mem_truncationIntegerPart_iff_exists_add_negative
      (Γ := Γ) (R := R)).mp hx with ⟨z, n, rfl⟩
    exact ⟨Nonpositive.C (Γ := Γ) (R := R) z,
      (mem_constantSubring (Γ := Γ) (R := R)).mpr ⟨z, rfl⟩, n, n.2, rfl⟩
  · rintro ⟨c, hc, n, hn, rfl⟩
    rcases (mem_constantSubring (Γ := Γ) (R := R)).mp hc with ⟨z, rfl⟩
    exact (mem_truncationIntegerPart_iff_exists_add_negative
      (Γ := Γ) (R := R)).mpr
      ⟨z, ⟨n, hn⟩, rfl⟩

end HahnSeries
