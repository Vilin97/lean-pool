/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.RiemannSpaceFinitePlaceIncrement
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The local pole filtration of a discrete valuation ring

This file isolates the exact local calculation behind principal parts.  If
`R` is a discrete valuation ring in its fraction field `L` and `π` is a
uniformizer, the functions whose pole order is at most `n` form a
`K`-submodule of `L`.  Consecutive levels have quotient equal to the residue
field of `R`.

Unlike the corresponding global Riemann-space increment, this calculation is
an equality: locally every leading residue has a lift.
-/

@[expose] public section

namespace BGS.HasseWeil

open scoped nonZeroDivisors

noncomputable section

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

/-- The local functions whose denominator is bounded by `π ^ n`. -/
def localPoleSpace (π : R) (n : ℕ) : Submodule K L where
  carrier := {x | ∃ r : R, algebraMap R L (π ^ n) * x = algebraMap R L r}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨rx, hx⟩ ⟨ry, hy⟩
    refine ⟨rx + ry, ?_⟩
    rw [map_add, ← hx, ← hy]
    ring
  smul_mem' := by
    rintro c x ⟨r, hr⟩
    refine ⟨c • r, ?_⟩
    rw [show algebraMap R L (c • r) = c • algebraMap R L r by
      exact map_smul (IsScalarTower.toAlgHom K R L) c r]
    simp only [Algebra.smul_def]
    rw [← hr]
    ring

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
theorem mem_localPoleSpace_iff (π : R) (n : ℕ) (x : L) :
    x ∈ localPoleSpace (K := K) (L := L) π n ↔
      ∃ r : R, algebraMap R L (π ^ n) * x = algebraMap R L r :=
  Iff.rfl

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
/-- Increasing the allowed pole order enlarges the local pole space. -/
theorem localPoleSpace_mono (π : R) (n : ℕ) :
    localPoleSpace (K := K) (L := L) π n ≤
      localPoleSpace (K := K) (L := L) π (n + 1) := by
  rintro x ⟨r, hr⟩
  refine ⟨π * r, ?_⟩
  calc
    algebraMap R L (π ^ (n + 1)) * x =
        algebraMap R L π * (algebraMap R L (π ^ n) * x) := by
      rw [pow_succ, map_mul]
      ring
    _ = algebraMap R L π * algebraMap R L r := congrArg _ hr
    _ = algebraMap R L (π * r) := by rw [map_mul]

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L] in
private theorem localPoleSpace_regular
    (π : R) (n : ℕ) :
    ∀ x : localPoleSpace (K := K) (L := L) π n,
      ∃ r : R, algebraMap R L (π ^ n) * x.1 = algebraMap R L r := by
  intro x
  exact x.2

/-- The leading-residue map on the `n`th local pole space. -/
def localPoleLeadingResidueMap (π : R) (n : ℕ) :
    localPoleSpace (K := K) (L := L) π n →ₗ[K]
      IsLocalRing.ResidueField R :=
  localLeadingResidueLinearMap
    (localPoleSpace (K := K) (L := L) π n)
    (algebraMap R L (π ^ n))
    (by exact localPoleSpace_regular (K := K) (L := L) π n)

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] in
private theorem localPoleNormalizedLift_eq
    (π : R) (n : ℕ)
    (x : localPoleSpace (K := K) (L := L) π n) (r : R)
    (hr : algebraMap R L (π ^ n) * x.1 = algebraMap R L r) :
    localNormalizedLift
        (localPoleSpace (K := K) (L := L) π n)
        (algebraMap R L (π ^ n))
        (localPoleSpace_regular (K := K) (L := L) π n) x = r := by
  apply IsFractionRing.injective R L
  rw [← hr]
  exact (localNormalizedLift_spec
    (localPoleSpace (K := K) (L := L) π n)
    (algebraMap R L (π ^ n))
    (localPoleSpace_regular (K := K) (L := L) π n) x).symm

/-- Every residue class occurs as a leading coefficient. -/
theorem localPoleLeadingResidueMap_surjective
    (π : R) (hπ : π ≠ 0) (n : ℕ) :
    Function.Surjective
      (localPoleLeadingResidueMap (K := K) (L := L) π n) := by
  intro z
  obtain ⟨r, hr⟩ :=
    (Ideal.Quotient.mk_surjective
      (I := IsLocalRing.maximalIdeal R)) z
  let πL : L := algebraMap R L π
  have hπL : πL ≠ 0 := by
    simpa [πL] using (IsFractionRing.injective R L).ne hπ
  let x : L := (algebraMap R L (π ^ n))⁻¹ * algebraMap R L r
  have hdenom : algebraMap R L (π ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero n hπL
  have hx : algebraMap R L (π ^ n) * x = algebraMap R L r := by
    dsimp only [x]
    rw [← mul_assoc, mul_inv_cancel₀ hdenom, one_mul]
  let x' : localPoleSpace (K := K) (L := L) π n := ⟨x, r, hx⟩
  refine ⟨x', ?_⟩
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
    (localNormalizedLift
      (localPoleSpace (K := K) (L := L) π n)
      (algebraMap R L (π ^ n))
      (localPoleSpace_regular (K := K) (L := L) π n) x') = z
  rw [localPoleNormalizedLift_eq (K := K) (L := L) π n x' r hx]
  exact hr

/-- The kernel of the leading-residue map is the preceding local pole
space. -/
theorem localPoleLeadingResidueMap_ker
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ) :
    (localPoleLeadingResidueMap (K := K) (L := L) π (n + 1)).ker =
      Submodule.comap
        (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
        (localPoleSpace (K := K) (L := L) π n) := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  rw [localPoleLeadingResidueMap, localLeadingResidueLinearMap_eq_zero_iff]
  constructor
  · intro hx
    change localNormalizedLift
      (localPoleSpace (K := K) (L := L) π (n + 1))
      (algebraMap R L (π ^ (n + 1)))
      (localPoleSpace_regular (K := K) (L := L) π (n + 1)) x ∈
        (IsDiscreteValuationRing.maximalIdeal R).asIdeal at hx
    rw [hπIdeal, Ideal.mem_span_singleton] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    have hlift := localNormalizedLift_spec
      (localPoleSpace (K := K) (L := L) π (n + 1))
      (algebraMap R L (π ^ (n + 1)))
      (localPoleSpace_regular (K := K) (L := L) π (n + 1)) x
    rw [hs] at hlift
    have hπL : algebraMap R L π ≠ 0 :=
      by simpa using (IsFractionRing.injective R L).ne hπ
    apply mul_left_cancel₀ hπL
    calc
      algebraMap R L π * (algebraMap R L (π ^ n) * x.1) =
          algebraMap R L (π ^ (n + 1)) * x.1 := by
        rw [pow_succ, map_mul]
        ring
      _ = algebraMap R L (π * s) := hlift
      _ = algebraMap R L π * algebraMap R L s := by rw [map_mul]
  · rintro ⟨s, hs⟩
    have hliftEq : localNormalizedLift
        (localPoleSpace (K := K) (L := L) π (n + 1))
        (algebraMap R L (π ^ (n + 1)))
        (localPoleSpace_regular (K := K) (L := L) π (n + 1)) x = π * s := by
      apply localPoleNormalizedLift_eq
      calc
        algebraMap R L (π ^ (n + 1)) * x.1 =
            algebraMap R L π * (algebraMap R L (π ^ n) * x.1) := by
          rw [pow_succ, map_mul]
          ring
        _ = algebraMap R L π * algebraMap R L s := congrArg _ hs
        _ = algebraMap R L (π * s) := by rw [map_mul]
    rw [hliftEq]
    change π * s ∈ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
    rw [hπIdeal, Ideal.mem_span_singleton]
    exact ⟨s, rfl⟩

/-- Consecutive local pole spaces have quotient the residue field. -/
noncomputable def localPoleQuotientEquivResidueField
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ) :
    (localPoleSpace (K := K) (L := L) π (n + 1) ⧸
      Submodule.comap
        (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
        (localPoleSpace (K := K) (L := L) π n)) ≃ₗ[K]
      IsLocalRing.ResidueField R := by
  let f := localPoleLeadingResidueMap (K := K) (L := L) π (n + 1)
  have hsurj : Function.Surjective f :=
    localPoleLeadingResidueMap_surjective (K := K) (L := L) π hπ (n + 1)
  have hker := localPoleLeadingResidueMap_ker
    (K := K) (L := L) π hπ hπIdeal n
  rw [← hker]
  exact f.quotKerEquivOfSurjective hsurj

/-- The exact dimension of one local principal-part layer. -/
theorem localPoleQuotient_finrank
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : (IsDiscreteValuationRing.maximalIdeal R).asIdeal =
      Ideal.span {π}) (n : ℕ)
    [Module.Finite K (IsLocalRing.ResidueField R)] :
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π (n + 1) ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π (n + 1)).subtype
            (localPoleSpace (K := K) (L := L) π n)) =
      Module.finrank K (IsLocalRing.ResidueField R) :=
  (localPoleQuotientEquivResidueField
    (K := K) (L := L) π hπ hπIdeal n).finrank_eq

end

end BGS.HasseWeil
