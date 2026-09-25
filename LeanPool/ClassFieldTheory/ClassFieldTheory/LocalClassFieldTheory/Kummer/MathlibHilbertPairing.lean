/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.All
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteGeneration
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Mathlib-facing local Hilbert pairing

The existing local Artin construction is transported to the public
power-class group and root-of-unity subgroup.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

variable (K : Type) [Field K]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The local norm-residue Hilbert symbol, expressed in Mathlib's
`rootsOfUnity` rather than the internal subgroup of units. -/
noncomputable def localHilbertSymbol
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    rootsOfUnity (n : ℕ) K :=
  (KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ))
    (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b)

/-- The descended local pairing, transported to Mathlib's
`PowerClassGroup` and `rootsOfUnity`. -/
noncomputable def localHilbertPairing
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    HilbertPairing K n :=
  ((MonoidHom.compHom (M := PowerClassGroup K n)
      (N := KummerTheory.nthRootsSubgroup K (n : ℕ))
      (P := rootsOfUnity (n : ℕ) K))
      (KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).toMonoidHom).comp
    (LocalClassFieldTheory.Kummer.localHilbertPairing K n hnK hmu)

/-- The public pairing evaluates to the public Hilbert symbol on
representatives. -/
theorem localHilbertPairing_powerClass
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertPairing K n hnK hmu (powerClass K n a) (powerClass K n b) =
      localHilbertSymbol K n hnK hmu a b := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  change
    e (LocalClassFieldTheory.Kummer.localHilbertPairing K n hnK hmu
      (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
      (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b)) =
      e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b)
  exact congrArg e
    (LocalClassFieldTheory.Kummer.localHilbertPairing_apply
      K n hnK hmu a b)

/-- The local Hilbert symbol is multiplicative in its first variable. -/
theorem localHilbertSymbol_mul_left
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b c : Kˣ) :
    localHilbertSymbol K n hnK hmu (a * b) c =
      localHilbertSymbol K n hnK hmu a c *
        localHilbertSymbol K n hnK hmu b c := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  let h := LocalClassFieldTheory.Kummer.localHilbertSymbolHom K n hnK hmu c
  change e (h (a * b)) = e (h a) * e (h b)
  calc
    e (h (a * b)) = e (h a * h b) := congrArg e (map_mul h a b)
    _ = e (h a) * e (h b) := map_mul e (h a) (h b)

/-- The local Hilbert symbol is multiplicative in its second variable. -/
theorem localHilbertSymbol_mul_right
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b c : Kˣ) :
    localHilbertSymbol K n hnK hmu a (b * c) =
      localHilbertSymbol K n hnK hmu a b *
        localHilbertSymbol K n hnK hmu a c := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  change
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a (b * c)) =
      e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) *
        e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a c)
  calc
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a (b * c)) =
        e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b *
          LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a c) :=
      congrArg e
        (LocalClassFieldTheory.Kummer.localHilbertSymbol_mul_right
          K n hnK hmu a b c)
    _ = e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) *
        e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a c) :=
      map_mul e _ _

/-- The local Hilbert symbol satisfies the Steinberg relation
`(a, 1 - a) = 1`. -/
theorem localHilbertSymbol_steinberg
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (h_one_sub : 1 - (a : K) ≠ 0) :
    localHilbertSymbol K n hnK hmu a
        (Units.mk0 (1 - (a : K)) h_one_sub) = 1 := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  change
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a
      (Units.mk0 (1 - (a : K)) h_one_sub)) = 1
  calc
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a
        (Units.mk0 (1 - (a : K)) h_one_sub)) = e 1 :=
      congrArg e
        (LocalClassFieldTheory.Kummer.localHilbertSymbol_steinberg
          K n hnK hmu a h_one_sub)
    _ = 1 := map_one e

/-- The local Hilbert symbol is skew-symmetric. -/
theorem localHilbertSymbol_skew
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbol K n hnK hmu a b =
      (localHilbertSymbol K n hnK hmu b a)⁻¹ := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  change
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) =
      (e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu b a))⁻¹
  calc
    e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) =
        e ((LocalClassFieldTheory.Kummer.localHilbertSymbol
          K n hnK hmu b a)⁻¹) :=
      congrArg e
        (LocalClassFieldTheory.Kummer.localHilbertSymbol_skew
          K n hnK hmu a b)
    _ = (e (LocalClassFieldTheory.Kummer.localHilbertSymbol
        K n hnK hmu b a))⁻¹ := map_inv e _

/-- The common left kernel of the local Hilbert symbol is the subgroup of
`n`-th powers. -/
theorem localHilbertSymbol_left_kernel
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    (∀ b : Kˣ, localHilbertSymbol K n hnK hmu a b = 1) ↔
      a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  constructor
  · intro h
    apply (LocalClassFieldTheory.Kummer.localHilbertSymbol_left_kernel
      K n hnK hmu a).1
    intro b
    apply e.injective
    calc
      e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) =
          localHilbertSymbol K n hnK hmu a b := rfl
      _ = 1 := h b
      _ = e 1 := (map_one e).symm
  · intro ha b
    have hInternal :=
      (LocalClassFieldTheory.Kummer.localHilbertSymbol_left_kernel
        K n hnK hmu a).2 ha b
    calc
      localHilbertSymbol K n hnK hmu a b =
          e (LocalClassFieldTheory.Kummer.localHilbertSymbol
            K n hnK hmu a b) := rfl
      _ = e 1 := congrArg e hInternal
      _ = 1 := map_one e

/-- The common right kernel of the local Hilbert symbol is the subgroup of
`n`-th powers. -/
theorem localHilbertSymbol_right_kernel
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (∀ a : Kˣ, localHilbertSymbol K n hnK hmu a b = 1) ↔
      b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  constructor
  · intro h
    apply (LocalClassFieldTheory.Kummer.localHilbertSymbol_right_kernel
      K n hnK hmu b).1
    intro a
    apply e.injective
    calc
      e (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b) =
          localHilbertSymbol K n hnK hmu a b := rfl
      _ = 1 := h a
      _ = e 1 := (map_one e).symm
  · intro hb a
    have hInternal :=
      (LocalClassFieldTheory.Kummer.localHilbertSymbol_right_kernel
        K n hnK hmu b).2 hb a
    calc
      localHilbertSymbol K n hnK hmu a b =
          e (LocalClassFieldTheory.Kummer.localHilbertSymbol
            K n hnK hmu a b) := rfl
      _ = e 1 := congrArg e hInternal
      _ = 1 := map_one e

/-- The local Hilbert pairing separates power classes in both variables. -/
theorem localHilbertPairing_nondegenerate
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (∀ a : PowerClassGroup K n,
      (∀ b : PowerClassGroup K n,
        localHilbertPairing K n hnK hmu a b = 1) → a = 1) ∧
    (∀ b : PowerClassGroup K n,
      (∀ a : PowerClassGroup K n,
        localHilbertPairing K n hnK hmu a b = 1) → b = 1) := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  let B := LocalClassFieldTheory.Kummer.localHilbertPairing K n hnK hmu
  have hB := LocalClassFieldTheory.Kummer.localHilbertPairing_nondegenerate
    K n hnK hmu
  constructor
  · intro a ha
    apply hB.1 a
    intro b
    apply e.injective
    calc
      e (B a b) = localHilbertPairing K n hnK hmu a b := rfl
      _ = 1 := ha b
      _ = e 1 := (map_one e).symm
  · intro b hb
    apply hB.2 b
    intro a
    apply e.injective
    calc
      e (B a b) = localHilbertPairing K n hnK hmu a b := rfl
      _ = 1 := hb a
      _ = e 1 := (map_one e).symm

/-- A local Hilbert symbol vanishes exactly when its second argument is a
norm from the canonical, possibly reducible Kummer algebra of the first. -/
theorem localHilbertSymbol_eq_one_iff_isKummerNorm
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbol K n hnK hmu a b = 1 ↔ IsKummerNorm K n a b := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
  have hmap : localHilbertSymbol K n hnK hmu a b = 1 ↔
      LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b = 1 := by
    change e (LocalClassFieldTheory.Kummer.localHilbertSymbol
      K n hnK hmu a b) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff]
  have hskew : LocalClassFieldTheory.Kummer.localHilbertSymbol
      K n hnK hmu a b = 1 ↔
      LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu b a = 1 := by
    rw [LocalClassFieldTheory.Kummer.localHilbertSymbol_skew K n hnK hmu a b]
    simp only [inv_eq_one]
  have hnorm : b ∈ LocalFieldTheory.localNormSubgroup K E ↔
      ∃ z : Eˣ, Algebra.norm K (z : E) = (b : K) := by
    change (∃ z : Eˣ, LocalFieldTheory.normUnits K E z = b) ↔ _
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      exact congrArg (fun u : Kˣ => (u : K)) hz
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Units.ext
      exact hz
  calc
    localHilbertSymbol K n hnK hmu a b = 1 ↔
        LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu a b = 1 :=
      hmap
    _ ↔ LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu b a = 1 :=
      hskew
    _ ↔ b ∈ LocalFieldTheory.localNormSubgroup K E :=
      LocalClassFieldTheory.Kummer.localHilbertSymbol_eq_one_iff_mem_localNormSubgroup
        K n hnK hmu b a
    _ ↔ (∃ z : Eˣ, Algebra.norm K (z : E) = (b : K)) := hnorm
    _ ↔ IsKummerNorm K n a b :=
      (LocalClassFieldTheory.Kummer.adjoinRoot_norm_iff_chosenSimpleKummerNorm
        K n hnK hmu a b).symm

/-- The Mathlib-facing local Hilbert pairing obeys all local algebraic laws,
including the canonical Kummer norm-residue criterion. -/
theorem localHilbertPairing_isLocalHilbertPairing
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    HilbertPairing.IsLocalHilbertPairing
      (localHilbertPairing K n hnK hmu) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change localHilbertPairing K n hnK hmu (powerClass K n a)
      (powerClass K n (Units.mk0 (1 - (a : K)) ha)) = 1
    rw [localHilbertPairing_powerClass]
    exact localHilbertSymbol_steinberg K n hnK hmu a ha
  · intro x y
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y ?_
    intro b
    change localHilbertPairing K n hnK hmu
      (powerClass K n a) (powerClass K n b) =
        (localHilbertPairing K n hnK hmu
          (powerClass K n b) (powerClass K n a))⁻¹
    rw [localHilbertPairing_powerClass, localHilbertPairing_powerClass]
    exact localHilbertSymbol_skew K n hnK hmu a b
  · exact localHilbertPairing_nondegenerate K n hnK hmu
  · intro a b
    change localHilbertPairing K n hnK hmu (powerClass K n a)
      (powerClass K n b) = 1 ↔ IsKummerNorm K n a b
    rw [localHilbertPairing_powerClass]
    exact localHilbertSymbol_eq_one_iff_isKummerNorm K n hnK hmu a b

end ClassFieldTheory

namespace ClassFieldTheory

/-- After mapping the public Hilbert value into the simple Kummer extension,
it is the quotient of the Artin image of the chosen root by that root.
The left pairing argument is the input to the canonical local Artin map. -/
theorem localHilbertPairing_artin_rootQuotient
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    Units.map (algebraMap K E).toMonoidHom
        (localHilbertPairing K n hnK hmu
          (powerClass K n b) (powerClass K n a)).1 =
      KummerTheory.rootQuotient
        (K := K) (L := E)
        (KummerTheory.chosenSimpleKummerRootUnit K n hnK a)
        (LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
          K n hnK hmu a b) := by
  dsimp only
  rw [localHilbertPairing_powerClass]
  have h := congrArg Subtype.val
    (LocalClassFieldTheory.Kummer.localHilbertSymbol_map_eq_rootQuotient
      K n hnK hmu b a)
  change
    Units.map
      (algebraMap K (KummerTheory.chosenSimpleKummerExtension K n hnK a)).toMonoidHom
      (LocalClassFieldTheory.Kummer.localHilbertSymbol K n hnK hmu b a).1 =
      KummerTheory.rootQuotient
        (K := K) (L := KummerTheory.chosenSimpleKummerExtension K n hnK a)
        (KummerTheory.chosenSimpleKummerRootUnit K n hnK a)
        (LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
          K n hnK hmu a b) at h
  exact h

/-- The public Type 0 Hilbert value agrees with the Artin root quotient for
any root of `a` in the chosen simple Kummer extension, not only the root
used to construct that extension. The pairing remains Artin-first. -/
theorem localHilbertPairing_artin_rootQuotient_of_same_pow
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ)
    (u : (KummerTheory.chosenSimpleKummerExtension K n hnK a)ˣ)
    (hu : u ^ (n : ℕ) =
      Units.map
        (algebraMap K (KummerTheory.chosenSimpleKummerExtension K n hnK a)).toMonoidHom
        a) :
    Units.map
        (algebraMap K (KummerTheory.chosenSimpleKummerExtension K n hnK a)).toMonoidHom
        (localHilbertPairing K n hnK hmu
          (powerClass K n b) (powerClass K n a)).1 =
      KummerTheory.rootQuotient
        (K := K) (L := KummerTheory.chosenSimpleKummerExtension K n hnK a)
        u
        (LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
          K n hnK hmu a b) := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let beta : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  let sigma : E ≃ₐ[K] E :=
    LocalClassFieldTheory.Kummer.chosenSimpleKummerNormResidueAutomorphism
      K n hnK hmu a b
  have hbeta : beta ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom a :=
    KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a
  change u ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom a at hu
  have hpow : (u / beta) ^ (n : ℕ) = 1 :=
    KummerTheory.div_pow_eq_one_of_pow_eq_pow (hu.trans hbeta.symm)
  obtain ⟨zeta, hzeta⟩ :=
    (KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := E) n hmu) (u / beta) hpow
  have hquot : KummerTheory.rootQuotient (K := K) (L := E)
      (u / beta) sigma = 1 := by
    rw [← hzeta]
    exact KummerTheory.rootQuotient_algebraMap_unit zeta sigma
  have hroot : KummerTheory.rootQuotient (K := K) (L := E) u sigma =
      KummerTheory.rootQuotient (K := K) (L := E) beta sigma :=
    div_eq_one.mp
      ((KummerTheory.rootQuotient_changeRoot (K := K) (L := E)
        u beta sigma).trans hquot)
  have hchosen :
      Units.map (algebraMap K E).toMonoidHom
          (localHilbertPairing K n hnK hmu
            (powerClass K n b) (powerClass K n a)).1 =
        KummerTheory.rootQuotient (K := K) (L := E) beta sigma := by
    simpa only [E, beta, sigma] using
      (localHilbertPairing_artin_rootQuotient K n hnK hmu a b)
  exact hchosen.trans hroot.symm

end ClassFieldTheory
