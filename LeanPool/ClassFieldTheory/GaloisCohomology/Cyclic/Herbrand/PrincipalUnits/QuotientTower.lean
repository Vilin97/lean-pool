/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
/-! Provides the public declarations in the
  `CyclicCohomology.Herbrand.PrincipalUnits.QuotientTower` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The natural projection `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` for `n ≤ m`. -/
def integerUnitsModPrincipalUnitsMapOfLe
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m) :
    IntegerUnitsModPrincipalUnitsAtLevel K m →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift m
    (integerUnitsModPrincipalUnitsAtLevelMk K n)
    (by
      intro x hx
      rw [MonoidHom.mem_ker,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact principalUnits_antitone K hnm hx)

/-- The level-change map sends a unit class to the class of the same unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfLe_mk
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfLe K hnm
        (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x

/-- The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsSuccMap
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)

/-- The successor-level map sends a unit representative to its successor quotient class. -/
@[simp]
theorem integerUnitsModPrincipalUnitsSuccMap_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsSuccMap K n
        (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x :=
  integerUnitsModPrincipalUnitsMapOfLe_mk K (Nat.le_succ n) x

/-- The map to the successor principal-unit quotient is surjective. -/
theorem integerUnitsModPrincipalUnitsSuccMap_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Surjective (integerUnitsModPrincipalUnitsSuccMap K n) := by
  intro q
  refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
    (motive := fun q => ∃ a, integerUnitsModPrincipalUnitsSuccMap K n a = q)
    q ?_
  intro x
  exact ⟨integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x, by simp⟩

/-- The induced homomorphism on the finite quotient `𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    IntegerUnitsModPrincipalUnitsAtLevel K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact principalUnits_integerRingEquiv_mem_self K n e u hu)

/-- An integer-ring equivalence maps a unit quotient class via its representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
        (integerUnitsModPrincipalUnitsAtLevelMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K n
        (Units.mapEquiv e.toMulEquiv u) :=
  integerUnitsModPrincipalUnitsAtLevelLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K n).comp
      (Units.mapEquiv e.toMulEquiv).toMonoidHom) _ u

/-- A valuation-integer-ring equivalence descends to the finite quotient
`𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      IntegerUnitsModPrincipalUnitsAtLevel K n where
  toFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
  invFun := integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
  left_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.symm.toMulEquiv (Units.mapEquiv e.toMulEquiv u) = u := by
      ext
      simp
    exact congrArg
      (integerUnitsModPrincipalUnitsAtLevelMk K n) h
  right_inv := by
    intro x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e
            (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e.symm x) = x)
      x ?_
    intro u
    rw [integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk,
      integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk]
    have h :
        Units.mapEquiv e.toMulEquiv (Units.mapEquiv e.symm.toMulEquiv u) = u := by
      ext
      simp
    exact congrArg
      (integerUnitsModPrincipalUnitsAtLevelMk K n) h
  map_mul' := by
    intro x y
    exact map_mul (integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv K n e) x y

/-- The induced quotient equivalence acts on a class through its unit representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv K n e
        (integerUnitsModPrincipalUnitsAtLevelMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K n
        (Units.mapEquiv e.toMulEquiv u) :=
  integerUnitsModPrincipalUnitsMapOfIntegerRingEquiv_mk K n e u

/-- The graded quotient `U_K^n/U_K^(n+1)` as the kernel source inside
`𝒪_Kˣ/U_K^(n+1)`. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) :=
  principalUnitsSuccQuotLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype)
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
      exact hu)

/-- The principal-unit quotient map sends a representative to its integer-unit class. -/
@[simp]
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
        (principalUnitsSuccQuotMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ) :=
  principalUnitsSuccQuotLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype) _ u

/-- The principal-unit inclusion followed by the successor map is the canonical quotient map. -/
theorem integerUnitsSuccMap_comp_principalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1 := by
  ext q
  refine PrincipalUnitsSuccQuot.inductionOn n
    (motive := fun q =>
      ((integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n)) q =
          (1 : PrincipalUnitsSuccQuot K n →*
            IntegerUnitsModPrincipalUnitsAtLevel K n) q)
    q ?_
  intro u
  rw [MonoidHom.comp_apply,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  rw [integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
  exact u.2

/-- Exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
      MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) x = 1
    rw [integerUnitsSuccMap_comp_principalUnitsSuccQuot]
    rfl
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    have hx : x ∈ principalUnits K n := by
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1
        (by simpa using hq)
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, by
      rw [principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk]⟩

/-- The induced map from the successive principal-unit quotient is injective. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_injective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    Function.Injective (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := principalUnitsSuccQuotMk_surjective K n x
  obtain ⟨v, rfl⟩ := principalUnitsSuccQuotMk_surjective K n y
  apply (principalUnitsSuccQuotMk_eq_iff_div_mem K n u v).2
  have hq :
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ) =
        integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (v : 𝒪[K]ˣ) := by
    simpa only [principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk] using hxy
  have hmem :
      ((u : 𝒪[K]ˣ) / (v : 𝒪[K]ˣ)) ∈ principalUnits K (n + 1) :=
    (integerUnitsModPrincipalUnitsAtLevelMk_eq_iff_div_mem K (n + 1)
      (u : 𝒪[K]ˣ) (v : 𝒪[K]ˣ)).1 hq
  change ((u / v : principalUnits K n) : 𝒪[K]ˣ) ∈ principalUnits K (n + 1)
  simpa using hmem

/-- A unit maps to the identity at the successor level exactly when it has a principal-unit lift. -/
theorem integerUnitsModPrincipalUnitsSuccMap_eq_one_iff_exists
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : IntegerUnitsModPrincipalUnitsAtLevel K (n + 1)) :
    integerUnitsModPrincipalUnitsSuccMap K n x = 1 ↔
      ∃ y : PrincipalUnitsSuccQuot K n,
        principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n y = x := by
  change x ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) ↔
    x ∈ MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n)
  rw [← principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker K n]

/-- Integral-closure Galois action on the finite quotient
`𝒪_Lˣ/U_L^n`. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) :
    IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
      IntegerUnitsModPrincipalUnitsAtLevel L n :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- The Galois-induced quotient equivalence acts on a class through its representative. -/
@[simp]
theorem galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (u : 𝒪[L]ˣ) :
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (integerUnitsModPrincipalUnitsAtLevelMk L n u) =
      integerUnitsModPrincipalUnitsAtLevelMk L n
        (Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv u) :=
  integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv_mk L n
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) u

/-- Integral-closure Galois action on finite principal-unit
quotients as a group homomorphism. -/
def galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    Gal(L / K) →*
      (IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n) where
  toFun := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
  map_one' := by
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n 1 x = x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1
  map_mul' := by
    intro σ τ
    ext x
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn n
      (motive := fun x =>
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
            K L n (σ * τ) x =
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n σ *
            galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
              K L n τ) x)
      x ?_
    intro u
    rw [galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    change
      integerUnitsModPrincipalUnitsAtLevelMk L n
          (Units.mapEquiv
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ)).toMulEquiv u) =
        galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
          (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ
            (integerUnitsModPrincipalUnitsAtLevelMk L n u))
    rw [
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk,
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
    congr 1

/-- Integral-closure Galois action on finite principal-unit
quotients, packaged for low-degree Herbrand quotients. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) :
    MulDistribMulAction (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) where
  smul σ x := galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x
  one_smul := by
    intro x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n 1 x = x
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_one (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n))
    exact h
  mul_smul := by
    intro σ τ x
    change galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n
        (σ * τ) x =
      galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ
        (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n τ x)
    have h := congrArg (fun e : IntegerUnitsModPrincipalUnitsAtLevel L n ≃*
        IntegerUnitsModPrincipalUnitsAtLevel L n => e x)
      (map_mul (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivHomOfIsIntegralClosure K L n)
        σ τ)
    exact h
  smul_mul := by
    intro σ x y
    exact map_mul (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure
      K L n σ) x y
  smul_one := by
    intro σ
    exact map_one (galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ)

/-- The Galois action on integer units modulo principal units is induced on representatives. -/
theorem galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (x : IntegerUnitsModPrincipalUnitsAtLevel L n) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L n
    σ • x = galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure K L n σ x :=
  rfl

/-- The successive finite-principal-unit quotient map is equivariant for the
integral-closure Galois actions. -/
theorem integerUnitsModPrincipalUnitsSuccMap_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K))
    (x : IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L (n + 1)
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L n
    integerUnitsModPrincipalUnitsSuccMap L n (σ • x) =
      σ • integerUnitsModPrincipalUnitsSuccMap L n x := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L (n + 1)
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
    (motive := fun x =>
      integerUnitsModPrincipalUnitsSuccMap L n (σ • x) =
        σ • integerUnitsModPrincipalUnitsSuccMap L n x)
    x ?_
  intro u
  rw [galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk,
    galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]

/-- The kernel-source map `U_L^n/U_L^(n+1) → 𝒪_Lˣ/U_L^(n+1)` is equivariant
for the integral-closure Galois actions. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_galoisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (σ : Gal(L/K)) (x : PrincipalUnitsSuccQuot L n) :
    letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L (n + 1)
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc L n (σ • x) =
      σ • principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc L n x := by
  let := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L (n + 1)
  refine PrincipalUnitsSuccQuot.inductionOn n
    (motive := fun x =>
      principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc L n (σ • x) =
        σ • principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc L n x)
    x ?_
  intro u
  rw [galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure_smul,
    galoisGroupPrincipalUnitsSuccQuotMapEquivOfIsIntegralClosure,
    principalUnitsSuccQuotMapEquivOfIntegerRingEquiv_apply,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure_smul,
    galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk]
  rfl

/-- The quotient `𝒪_Kˣ/U_K^0` is finite because `U_K^0 = 𝒪_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_zero
    (K : Type u) [Field K] [ValuativeRel K] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0) := by
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [principalUnits_zero]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv

/-- The initial nontrivial quotient `𝒪_Kˣ/U_K^1` is finite via
`𝒪_Kˣ/U_K^1 ≃ 𝓀_Kˣ`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K 1) := by
  let e : IntegerUnitsModPrincipalUnitsAtLevel K 1 ≃* ResidueUnits K :=
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 1).trans
      ((integerUnitsModPrincipalUnitsConcreteEquiv K).symm.trans
        (integerUnitsModPrincipalUnitsEquivResidueUnits K))
  exact Finite.of_equiv (ResidueUnits K) e.symm.toEquiv

/-- If the previous finite quotient and the graded quotient are finite, then
the next finite quotient is finite. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    [Finite (PrincipalUnitsSuccQuot K n)]
    [Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)] :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K (n + 1)) := by
  let i := principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
  have : Finite i.range :=
    Finite.of_surjective
      (fun a : PrincipalUnitsSuccQuot K n => (⟨i a, ⟨a, rfl⟩⟩ : i.range))
      (by
        intro x
        rcases x with ⟨b, ⟨a, ha⟩⟩
        exact ⟨a, Subtype.ext ha⟩)
  let f := integerUnitsModPrincipalUnitsSuccMap K n
  exact (f.finite_iff_finite_ker_range).2 (by
    constructor
    · rw [← principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker K n]
      infer_instance
    · infer_instance)

/-- Every finite principal-unit quotient `𝒪_Kˣ/U_K^n` is finite over a
nonarchimedean local field. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  induction n with
  | zero =>
      exact integerUnitsModPrincipalUnitsAtLevel_finite_zero K
  | succ n ih =>
      cases n with
      | zero =>
          exact integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField K
      | succ k =>
          have : Finite (PrincipalUnitsSuccQuot K (k + 1)) :=
            finite_principalUnitsSuccQuot K (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
          exact integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite K (k + 1)

/-- Actual `H⁰` finiteness for the finite quotient `𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_herbrandH0_finite_of_isNonarchimedeanLocalField
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L/K))] (n : Nat) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)) := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  infer_instance

/-- Actual `H^{-1}` finiteness for the finite quotient `𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_herbrandHMinusOne_finite_of_isNonarchimedeanLocalField
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L/K))] (n : Nat) (σ : Gal(L / K)) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ) := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  infer_instance

/-- Actual finite-cyclic-module endpoint for the finite quotient
`𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_herbrandQuotient_eq_one_of_isNonarchimedeanLocalField
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L/K))] (n : Nat) (σ : Gal(L/K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers σ) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
      integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
      (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ = 1 := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  exact CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_finite_module_eq_one
    (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ hgen

/-- GC Herbrand multiplicativity specialized to the actual finite principal-unit
quotient tower
`U_L^n/U_L^(n+1) → 𝒪_Lˣ/U_L^(n+1) → 𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsSucc_herbrandQuotient_exact_multiplicative_of_isIntegralClosure
    (K L : Type) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L/K))] (n : Nat) (σ : Gal(L / K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers σ)
    (hA0 :
      letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n)))
    (hAm :
      letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ))
    (hB0 :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L (n + 1)
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))))
    (hBm :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L (n + 1)
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ))
    (hC0 :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)))
    (hCm :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ)) :
    letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L (n + 1)
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n)) := hA0
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ) := hAm
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))) := hB0
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ) := hBm
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)) := hC0
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ) := hCm
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
        (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ =
      CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
          (G := Gal(L / K)) (A := PrincipalUnitsSuccQuot L n) σ *
        CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
          (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ := by
  let := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L (n + 1)
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (PrincipalUnitsSuccQuot L n)) := hA0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ) := hAm
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))) := hB0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ) := hBm
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)) := hC0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ) := hCm
  exact CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_exact_multiplicative
    (G := Gal(L / K))
    (A := PrincipalUnitsSuccQuot L n)
    (B := IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))
    (C := IntegerUnitsModPrincipalUnitsAtLevel L n)
    (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc L n)
    (integerUnitsModPrincipalUnitsSuccMap L n)
    (by
      intro g x
      exact
        principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_galoisGroup_of_isIntegralClosure
          K L n g x)
    (by
      intro g x
      exact integerUnitsModPrincipalUnitsSuccMap_galoisGroup_of_isIntegralClosure K L n g x)
    (integerUnitsModPrincipalUnitsSuccMap_eq_one_iff_exists L n)
    (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_injective L n)
    (by
      intro x
      exact integerUnitsModPrincipalUnitsSuccMap_surjective L n x)
    σ hgen

/-- If the graded quotient and the previous finite quotient both have Herbrand
quotient `1`, the next finite quotient has Herbrand quotient `1`. -/
theorem integerUnitsModPrincipalUnitsSucc_herbrandQuotient_eq_one_of_isIntegralClosure
    (K L : Type) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L/K))] (n : Nat) (σ : Gal(L / K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers σ)
    (hA0 :
      letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n)))
    (hAm :
      letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ))
    (hB0 :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L (n + 1)
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))))
    (hBm :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L (n + 1)
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ))
    (hC0 :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)))
    (hCm :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
        K L n
      Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ))
    (hA :
      letI := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
      letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
          (Gal(L / K)) (PrincipalUnitsSuccQuot L n)) := hA0
      letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
          (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ) := hAm
      CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
        (G := Gal(L / K)) (A := PrincipalUnitsSuccQuot L n) σ = 1)
    (hC :
      letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
      letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
          (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)) := hC0
      letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
          (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ) := hCm
      CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
        (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ = 1) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
      K L (n + 1)
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))) := hB0
    letI : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
        (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ) := hBm
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
      (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ = 1 := by
  let := galoisGroupPrincipalUnitsSuccQuotMulDistribMulActionOfIsIntegralClosure K L n
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure
    K L (n + 1)
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (PrincipalUnitsSuccQuot L n)) := hA0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (PrincipalUnitsSuccQuot L n) σ) := hAm
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1))) := hB0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L (n + 1)) σ) := hBm
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n)) := hC0
  let : Finite (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      (Gal(L / K)) (IntegerUnitsModPrincipalUnitsAtLevel L n) σ) := hCm
  rw [integerUnitsModPrincipalUnitsSucc_herbrandQuotient_exact_multiplicative_of_isIntegralClosure
    K L n σ hgen hA0 hAm hB0 hBm hC0 hCm, hA, hC, one_mul]

end
end CyclicCohomology
