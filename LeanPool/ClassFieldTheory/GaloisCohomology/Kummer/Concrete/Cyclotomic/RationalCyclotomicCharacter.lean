/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicField
public import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerUnits
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
/-!
# The cyclotomic character of the rational cyclotomic field

This file assembles mathlib's `p`-adic cyclotomic characters of the
actual extension `rationalCyclotomicField / ℚ`.  Their product takes
values in the canonical product of the local unit groups, and the
topological Chinese-remainder equivalence identifies that product with
`ZHatˣ`.

No abstract copy of either the Galois group or its expected target is
introduced here.
-/

@[expose] public section

noncomputable
section

namespace KummerTheory

open ClassFormation

/-- The actual rational cyclotomic field contains primitive roots of
unity of every nonzero order. -/
noncomputable instance rationalCyclotomicField_hasEnoughRootsOfUnity
    (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity rationalCyclotomicField n where
  prim :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := (Set.univ : Set ℕ))
      ℚ rationalCyclotomicField (Set.mem_univ n) (NeZero.ne n)
  cyc := rootsOfUnity.isCyclic rationalCyclotomicField n

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The product, over all rational primes, of mathlib's `p`-adic
cyclotomic characters of `Gal(rationalCyclotomicField / ℚ)`. -/
noncomputable def rationalCyclotomicCharacterPrimeProduct :
    (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField) →ₜ*
      ((p : Nat.Primes) → ℤ_[p.1]ˣ) where
  toMonoidHom :=
    MonoidHom.pi fun p =>
      (cyclotomicCharacter rationalCyclotomicField p.1).comp
        (MulSemiringAction.toRingAut
          (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
          rationalCyclotomicField)
  continuous_toFun :=
    continuous_pi fun p =>
      cyclotomicCharacter.continuous
        p.1 ℚ rationalCyclotomicField

/-- Evaluation at a prime is the corresponding mathlib cyclotomic
character. -/
@[simp]
theorem rationalCyclotomicCharacterPrimeProduct_apply
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) :
    rationalCyclotomicCharacterPrimeProduct σ p =
      cyclotomicCharacter rationalCyclotomicField p.1
        (MulSemiringAction.toRingAut
          (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
          rationalCyclotomicField σ) :=
  rfl

section PrimePowerCharacter

-- Expose the exact prime-power index to instance synthesis. Both
-- proposition-valued instances are supplied by the existing canonical factories.
local instance primePowerLevelNumberField (p : Nat.Primes) (k : ℕ) :
    NumberField (rationalCyclotomicLevel ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevel_numberField ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance primePowerLevelIsGalois (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ (rationalCyclotomicLevel ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevel_isGalois ⟨p.1 ^ k, pow_pos p.2.pos k⟩

/-- Reduction of the `p`-coordinate modulo `p ^ k` is the standard
mathlib character of the finite internal cyclotomic level. -/
theorem rationalCyclotomicCharacterPrimeProduct_toZModPow
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (σ.restrictNormal
          (rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)) := by
  let n : ℕ+ := ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  let F := rationalCyclotomicLevel n
  let : IsCyclotomicExtension {p.1 ^ k} ℚ F := by
    change IsCyclotomicExtension {(n : ℕ)} ℚ (rationalCyclotomicLevel n)
    exact rationalCyclotomicLevel_isCyclotomicExtension n
  let ζ : F :=
    IsCyclotomicExtension.zeta (p.1 ^ k) ℚ F
  have hζ : IsPrimitiveRoot ζ (p.1 ^ k) :=
    IsCyclotomicExtension.zeta_spec (p.1 ^ k) ℚ F
  let t : rationalCyclotomicField :=
    algebraMap F rationalCyclotomicField ζ
  have ht : t ^ (p.1 ^ k) = 1 := by
    dsimp only [t]
    rw [← map_pow, hζ.pow_eq_one, map_one]
  let g : rationalCyclotomicField ≃+* rationalCyclotomicField :=
    MulSemiringAction.toRingAut
      (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
      rationalCyclotomicField σ
  have hinfinite :
      g t =
        t ^ ((cyclotomicCharacter
          rationalCyclotomicField p.1 g).val.toZModPow k).val :=
    cyclotomicCharacter.spec p.1 g t ht
  have hfinite :
      (σ.restrictNormal F) ζ =
        ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k) F (σ.restrictNormal F)).val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (p.1 ^ k) F (σ.restrictNormal F) hζ.pow_eq_one
  have hζmap : IsPrimitiveRoot t (p.1 ^ k) := by
    exact hζ.map_of_injective
      (algebraMap F rationalCyclotomicField).injective
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k) F (σ.restrictNormal F)
  apply Units.ext
  apply ZMod.val_injective
  apply hζmap.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    t ^ ((PadicInt.toZModPow k)
        (rationalCyclotomicCharacterPrimeProduct σ p).val).val =
        g t := by
      rw [rationalCyclotomicCharacterPrimeProduct_apply]
      exact hinfinite.symm
    _ = σ t := rfl
    _ = algebraMap F rationalCyclotomicField
        ((σ.restrictNormal F) ζ) :=
      (AlgEquiv.restrictNormal_commutes σ F ζ).symm
    _ = algebraMap F rationalCyclotomicField
        (ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k) F (σ.restrictNormal F)).val.val) := by
      rw [hfinite]
    _ = t ^ (IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k) F (σ.restrictNormal F)).val.val := by
      rw [map_pow]

end PrimePowerCharacter

/-- The rational cyclotomic character with its canonical profinite
integer-unit target. -/
noncomputable def rationalCyclotomicCharacter :
    (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField) →ₜ* ZHatˣ :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    zHatUnitsContinuousMulEquivPrimeProduct.symm).comp
      rationalCyclotomicCharacterPrimeProduct

end KummerTheory
