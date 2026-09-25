/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Compatibility of Hilbert pairings at divisible exponents

Pairings constructed from the same arithmetic local Artin maps can be chosen
compatibly when `m ∣ n`. Their values are compared in `Kˣ`, since they belong
to different roots-of-unity subgroups. The public norm criterion places the
radical in the first argument. With that convention, the root-quotient
formula for arithmetic Artin has an inverse; the inverse occurs on both
sides of the exponent comparison and does not change the formula below.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u

/-- For `m ∣ n`, there are local Hilbert pairings at exponents `m` and `n`
whose values satisfy `(a,b)ₘ = (a,b)ₙ ^ (n/m)` in the base-field unit group.
Neither pairing is asserted to be determined by the algebraic laws alone. -/
theorem exists_compatibleLocalHilbertPairings_of_dvd
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (m n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmuN : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmn : (m : ℕ) ∣ (n : ℕ)) :
    ∃ Bm : HilbertPairing K m,
      HilbertPairing.IsLocalHilbertPairing Bm ∧
      ∃ Bn : HilbertPairing K n,
        HilbertPairing.IsLocalHilbertPairing Bn ∧
        ∀ a b : Kˣ,
          (Bm (powerClass K m a) (powerClass K m b)).1 =
            (Bn (powerClass K n a) (powerClass K n b)).1 ^
              ((n : ℕ) / (m : ℕ)) := by
  obtain ⟨q, hq⟩ := hmn
  let : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  let S := Shrink.{0} K
  let : ValuativeRel S := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  let : IsNonarchimedeanLocalField S :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  let e : S ≃+* K := Shrink.ringEquiv K
  have hnS : ((n : ℕ) : S) ≠ 0 := by
    intro hz
    apply hnK
    have hzK := congrArg e hz
    simpa [e] using hzK
  have hmS : ((m : ℕ) : S) ≠ 0 := by
    intro hz
    apply hnS
    rw [hq, Nat.cast_mul, hz, zero_mul]
  have hmuNS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmuN
    refine ⟨e.symm ζ, ?_⟩
    exact (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective e.symm.injective)
  have hmuMS : (primitiveRoots (m : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmuNS
    refine ⟨ζ ^ q, (mem_primitiveRoots m.pos).2 ?_⟩
    exact IsPrimitiveRoot.pow n.pos ((mem_primitiveRoots n.pos).1 hζ)
      (by rw [mul_comm]; exact hq)
  let Bm₀ : HilbertPairing S m := localHilbertPairing S m hmS hmuMS
  let Bn₀ : HilbertPairing S n := localHilbertPairing S n hnS hmuNS
  let Bm : HilbertPairing K m := hilbertPairingOfRingEquiv e m hmuMS Bm₀
  let Bn : HilbertPairing K n := hilbertPairingOfRingEquiv e n hmuNS Bn₀
  refine ⟨Bm,
    hilbertPairingOfRingEquiv_isLocalHilbertPairing e m hmuMS Bm₀
      (localHilbertPairing_isLocalHilbertPairing S m hmS hmuMS),
    Bn,
    hilbertPairingOfRingEquiv_isLocalHilbertPairing e n hmuNS Bn₀
      (localHilbertPairing_isLocalHilbertPairing S n hnS hmuNS), ?_⟩
  intro a b
  let eu : Sˣ ≃* Kˣ := Units.mapEquiv e.toMulEquiv
  let a₀ : Sˣ := eu.symm a
  let b₀ : Sˣ := eu.symm b
  have hsource :
      (Bm₀ (powerClass S m a₀) (powerClass S m b₀)).1 =
        (Bn₀ (powerClass S n a₀) (powerClass S n b₀)).1 ^
          ((n : ℕ) / (m : ℕ)) := by
    change (localHilbertPairing S m hmS hmuMS
        (powerClass S m a₀) (powerClass S m b₀)).1 =
      (localHilbertPairing S n hnS hmuNS
        (powerClass S n a₀) (powerClass S n b₀)).1 ^
          ((n : ℕ) / (m : ℕ))
    rw [localHilbertPairing_powerClass, localHilbertPairing_powerClass]
    change
      (LocalClassFieldTheory.Kummer.localHilbertSymbol
        S m hmS hmuMS a₀ b₀).1 =
      (LocalClassFieldTheory.Kummer.localHilbertSymbol
        S n hnS hmuNS a₀ b₀).1 ^ ((n : ℕ) / (m : ℕ))
    exact LocalClassFieldTheory.Kummer.localHilbertSymbol_exponentCompatibility
      S m n hmS hnS hmuMS hmuNS ⟨q, hq⟩ a₀ b₀
  have htransport
      (r : ℕ+) (hmuR : (primitiveRoots (r : ℕ) S).Nonempty)
      (x : rootsOfUnity (r : ℕ) S) :
      (rootsOfUnityEquivOfRingEquiv e r hmuR x).1 = eu x.1 := by
    let : NeZero (r : ℕ) := ⟨r.pos.ne'⟩
    apply Units.ext
    exact (val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe
      e.injective hmuR x).symm
  change
    (hilbertPairingOfRingEquiv e m hmuMS Bm₀
      (powerClass K m a) (powerClass K m b)).1 =
    (hilbertPairingOfRingEquiv e n hmuNS Bn₀
      (powerClass K n a) (powerClass K n b)).1 ^
        ((n : ℕ) / (m : ℕ))
  rw [hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    htransport m hmuMS, htransport n hmuNS]
  simpa only [eu, a₀, b₀, map_pow] using congrArg eu hsource

end ClassFieldTheory
