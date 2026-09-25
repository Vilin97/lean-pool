/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Perfectness of a finite nondegenerate Hilbert pairing

When the power-class group is finite and the field contains a primitive
`n`-th root of unity, its full group of `μₙ`-valued characters has the same
order. Hence a nondegenerate pairing gives an equivalence with that dual.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory.HilbertPairing

universe u

private theorem powerClass_pow_order
    (K : Type u) [Field K] (n : ℕ+)
    (a : PowerClassGroup K n) : a ^ (n : ℕ) = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  change (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x) ^
      (n : ℕ) = 1
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

private def characterUnitsEquiv
    (K : Type u) [Field K] (n : ℕ+) :
    (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K) ≃
      (PowerClassGroup K n →* Kˣ) where
  toFun f := (rootsOfUnity (n : ℕ) K).subtype.comp f
  invFun f := f.codRestrict (rootsOfUnity (n : ℕ) K) (by
    intro a
    change (f a) ^ (n : ℕ) = 1
    rw [← map_pow, powerClass_pow_order K n a, map_one])
  left_inv f := by
    ext a
    rfl
  right_inv f := by
    ext a
    rfl

/-- A finite nondegenerate pairing on power classes is perfect: its adjoint
map onto the full group of `μₙ`-valued characters is bijective. -/
theorem IsNondegenerate.bijective
    {K : Type u} [Field K] {n : ℕ+}
    [Finite (PowerClassGroup K n)]
    {B : HilbertPairing K n}
    (hB : B.IsNondegenerate)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Bijective B := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : HasEnoughRootsOfUnity K (n : ℕ) :=
    { prim := by
        obtain ⟨ζ, hζ⟩ := hmu
        exact ⟨ζ, (mem_primitiveRoots n.pos).1 hζ⟩
      cyc := inferInstance }
  have hExp : Monoid.exponent (PowerClassGroup K n) ∣ (n : ℕ) :=
    Monoid.exponent_dvd_of_forall_pow_eq_one
      (powerClass_pow_order K n)
  let : HasEnoughRootsOfUnity K
      (Monoid.exponent (PowerClassGroup K n)) :=
    HasEnoughRootsOfUnity.of_dvd K hExp
  have hCard : Nat.card (PowerClassGroup K n) =
      Nat.card (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K) := by
    calc
      Nat.card (PowerClassGroup K n) =
          Nat.card (PowerClassGroup K n →* Kˣ) :=
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
          (PowerClassGroup K n) K).symm
      _ = Nat.card (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K) :=
        (Nat.card_congr (characterUnitsEquiv K n)).symm
  have : Finite
      (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K) :=
    Nat.finite_of_card_ne_zero (by
      rw [← hCard]
      exact (Nat.card_pos (α := PowerClassGroup K n)).ne')
  have hinj : Function.Injective B := by
    intro a b hab
    have hOne : B (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hEq : a * b⁻¹ = 1 := hB.1 _ (fun c => DFunLike.congr_fun hOne c)
    exact (mul_inv_eq_one).mp hEq
  exact (Nat.bijective_iff_injective_and_card B).2 ⟨hinj, hCard⟩

end ClassFieldTheory.HilbertPairing
