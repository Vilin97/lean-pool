/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv
/-!
# Rigidity of the rational cyclotomic character

The actual rational cyclotomic character is detected by all of its
prime-power reductions.  In particular, if every reduction of every
`p`-adic character coordinate has square one, then the underlying
automorphism of the full rational cyclotomic field has square one.
-/

@[expose] public section



noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalCyclotomicCharacterRigidityPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalCyclotomicCharacterRigidityPrimeFact

open scoped Classical in
/-- An automorphism of the full rational cyclotomic field has square one
as soon as every prime-power reduction of its genuine cyclotomic
character has square one. -/
theorem rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
    (σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                σ p) ^ 2 =
          1) :
    σ ^ 2 = 1 := by
  apply
    KummerTheory.rationalCyclotomicCharacterPrimeProduct_injective
  rw [map_pow, map_one]
  funext p
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let u : ℤ_[p.1]ˣ :=
    KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p
  let f : ℤ_[p.1] →* ZMod (p.1 ^ k) :=
    (PadicInt.toZModPow k).toMonoidHom
  have hk : Units.map f (u ^ 2) = 1 := by
    change
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p ^ 2) =
        1
    rw [map_pow]
    exact h p k
  simp only [Pi.pow_apply, Pi.one_apply]
  calc
    (PadicInt.toZModPow k)
          ↑(KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p ^ 2) =
        f ↑(u ^ 2) := rfl
    _ = ↑(Units.map f (u ^ 2)) :=
      (Units.coe_map f (u ^ 2)).symm
    _ = ↑(1 : (ZMod (p.1 ^ k))ˣ) :=
      congrArg Units.val hk
    _ = f ↑(1 : ℤ_[p.1]ˣ) := (map_one f).symm
    _ = (PadicInt.toZModPow k) ↑(1 : ℤ_[p.1]ˣ) := rfl

end Reciprocity
end GlobalClassFieldTheory
