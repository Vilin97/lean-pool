/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.TowerInvariants
/-!
# Hilbert ramification theory: number-field prime ideals in the fixed fields

This file proves the ramification and inertia invariant statements for the
contracted primes `P_Z` and `P_T` appearing in
the decomposition and inertia fixed-field tower.
-/

@[expose] public section

noncomputable
section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The prime-decomposition tower identity:
`P` is the only prime of `O_L` above `P_Z`. -/
theorem dedekindTower_decompositionFieldPrime_primesOver_ncard_eq_one
    (P : Ideal (𝓞 L)) [P.IsPrime]
    [Finite G] [IsGaloisGroup G K L] :
    ((decompositionFieldPrime (K := K) (L := L) G P).primesOver (𝓞 L)).ncard =
      1 := by
  let :
      IsGaloisGroup (decompositionGroup P G)
        (decompositionField (K := K) (L := L) G P) L :=
    IsGaloisGroup.subgroup G K L (decompositionGroup P G)
  let :
      IsGaloisGroup (decompositionGroup P G)
        (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (decompositionGroup P G)
      (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L)
      (decompositionField (K := K) (L := L) G P) L
  have horbit :
      MulAction.orbit (decompositionGroup P G) P =
        (decompositionFieldPrime (K := K) (L := L) G P).primesOver (𝓞 L) := by
    exact
      IsInvariant.orbit_eq_primesOver
        (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L)
        (decompositionGroup P G)
        (decompositionFieldPrime (K := K) (L := L) G P) P
  rw [← horbit]
  exact dedekindTower_decompositionGroup_orbit_ncard_eq_one P G

/-- The prime-decomposition tower identity:
over the decomposition field, the local product `e(P/P_Z) * f(P/P_Z)`
equals the original product `e(P/p) * f(P/p)`.  This is the exact
`e' f' = e f` product comparison in the prime-decomposition proof. -/
theorem dedekindTower_decompositionFieldPrime_product_eq_base_product
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L] :
    Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) P *
        P.inertiaDeg
          (𝓞 (decompositionField (K := K) (L := L) G P)) =
      Ideal.ramificationIdx' (basePrime (K := K) P) P *
        P.inertiaDeg (𝓞 K) := by
  let :
      IsGaloisGroup (decompositionGroup P G)
        (decompositionField (K := K) (L := L) G P) L :=
    IsGaloisGroup.subgroup G K L (decompositionGroup P G)
  let :
      IsGaloisGroup (decompositionGroup P G)
        (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (decompositionGroup P G)
      (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L)
      (decompositionField (K := K) (L := L) G P) L
  have :
      Module.Finite
        (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L) :=
    ringOfIntegers_moduleFinite
      (K := decompositionField (K := K) (L := L) G P) (L := L)
  have : Module.Finite (𝓞 K) (𝓞 L) :=
    ringOfIntegers_moduleFinite (K := K) (L := L)
  have htop :
      Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) P *
          P.inertiaDeg
            (𝓞 (decompositionField (K := K) (L := L) G P)) =
        Nat.card (decompositionGroup P G) := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (decompositionFieldPrime (K := K) (L := L) G P) P
      (decompositionFieldPrime_ne_bot (K := K) (L := L) G P)]
    exact
      dedekindTower_ramificationIdx_mul_inertiaDeg_eq_card_of_nonsplit
        (A := 𝓞 (decompositionField (K := K) (L := L) G P))
        (B := 𝓞 L)
        (p := decompositionFieldPrime (K := K) (L := L) G P)
        (P := P)
        (decompositionFieldPrime_ne_bot (K := K) (L := L) G P)
        (decompositionGroup P G)
        (dedekindTower_decompositionFieldPrime_primesOver_ncard_eq_one
          (K := K) (L := L) G P)
  have hbase :
      Nat.card (decompositionGroup P G) =
        Ideal.ramificationIdx' (basePrime (K := K) P) P *
          P.inertiaDeg (𝓞 K) := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (basePrime (K := K) P) P (basePrime_ne_bot (K := K) P)]
    exact
      dedekindTower_decomposition_card_eq_ramificationIdx_mul_inertiaDeg
        (A := 𝓞 K) (B := 𝓞 L)
        (basePrime (K := K) P) (basePrime_ne_bot (K := K) P) P G
  exact htop.trans hbase

/-- The prime-decomposition tower identity:
for the decomposition field prime `P_Z`, the top extension has the original
ramification index and inertia degree, while `P_Z/p` has both invariants
equal to `1`. -/
theorem dedekindTower_decompositionFieldPrime_tower_invariants
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L] :
    Ideal.ramificationIdx' (basePrime (K := K) P) (decompositionFieldPrime (K := K) (L := L) G
      P) = 1 ∧
      (decompositionFieldPrime (K := K) (L := L) G P).inertiaDeg
          (𝓞 K) = 1 ∧
      Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) P =
        Ideal.ramificationIdx' (basePrime (K := K) P) P ∧
      P.inertiaDeg (𝓞 (decompositionField (K := K) (L := L) G P)) =
        P.inertiaDeg (𝓞 K) := by
  have :
      Module.Finite
        (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L) :=
    ringOfIntegers_moduleFinite
      (K := decompositionField (K := K) (L := L) G P) (L := L)
  have hPZ_ne :
      Ideal.map
          (algebraMap
            (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L))
          (decompositionFieldPrime (K := K) (L := L) G P) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (decompositionFieldPrime_ne_bot (K := K) (L := L) G P)
  have hp_ne :
      Ideal.map (algebraMap (𝓞 K) (𝓞 L))
          (basePrime (K := K) P) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (basePrime_ne_bot (K := K) P)
  have hPZ_le :
      Ideal.map
          (algebraMap
            (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L))
          (decompositionFieldPrime (K := K) (L := L) G P) ≤ P := by
    rw [decompositionFieldPrime, Ideal.under_def]
    exact Ideal.map_comap_le
  exact
    dedekindTower_ideal_tower_invariants_of_top_product
      (A := 𝓞 K)
      (B := 𝓞 (decompositionField (K := K) (L := L) G P))
      (C := 𝓞 L)
      (p := basePrime (K := K) P)
      (P := decompositionFieldPrime (K := K) (L := L) G P)
      (Q := P)
      hPZ_ne hp_ne hPZ_le
      (dedekindTower_decompositionFieldPrime_product_eq_base_product
        (K := K) (L := L) G P)

/-- A prime-decomposition consequence:
`P` is the only prime of `O_L` above `P_T`. -/
theorem dedekindRamification_inertiaFieldPrime_primesOver_ncard_eq_one
    (P : Ideal (𝓞 L)) [P.IsPrime]
    [Finite G] [IsGaloisGroup G K L] :
    ((inertiaFieldPrime (K := K) (L := L) G P).primesOver (𝓞 L)).ncard =
      1 := by
  let :
      IsGaloisGroup (inertiaGroup P G)
        (inertiaField (K := K) (L := L) G P) L :=
    IsGaloisGroup.subgroup G K L (inertiaGroup P G)
  let :
      IsGaloisGroup (inertiaGroup P G)
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (inertiaGroup P G)
      (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L)
      (inertiaField (K := K) (L := L) G P) L
  have horbit :
      MulAction.orbit (inertiaGroup P G) P =
        (inertiaFieldPrime (K := K) (L := L) G P).primesOver (𝓞 L) := by
    exact
      IsInvariant.orbit_eq_primesOver
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L)
        (inertiaGroup P G)
        (inertiaFieldPrime (K := K) (L := L) G P) P
  rw [← horbit]
  exact dedekindRamification_inertiaGroup_orbit_ncard_eq_one P G

/-- A prime-decomposition consequence:
over the inertia field, the local product `e(P/P_T) * f(P/P_T)` equals the
original ramification index `e(P/p)` when the residue extension is separable.
-/
theorem dedekindRamification_inertiaFieldPrime_product_eq_base_ramificationIdx
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Ideal.ramificationIdx' (inertiaFieldPrime (K := K) (L := L) G P) P *
        P.inertiaDeg
          (𝓞 (inertiaField (K := K) (L := L) G P)) =
      Ideal.ramificationIdx' (basePrime (K := K) P) P := by
  let :
      IsGaloisGroup (inertiaGroup P G)
        (inertiaField (K := K) (L := L) G P) L :=
    IsGaloisGroup.subgroup G K L (inertiaGroup P G)
  let :
      IsGaloisGroup (inertiaGroup P G)
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (inertiaGroup P G)
      (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L)
      (inertiaField (K := K) (L := L) G P) L
  have :
      Module.Finite
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    ringOfIntegers_moduleFinite
      (K := inertiaField (K := K) (L := L) G P) (L := L)
  have : Module.Finite (𝓞 K) (𝓞 L) :=
    ringOfIntegers_moduleFinite (K := K) (L := L)
  have htop :
      Ideal.ramificationIdx' (inertiaFieldPrime (K := K) (L := L) G P) P *
          P.inertiaDeg
            (𝓞 (inertiaField (K := K) (L := L) G P)) =
        Nat.card (inertiaGroup P G) := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (inertiaFieldPrime (K := K) (L := L) G P) P
      (inertiaFieldPrime_ne_bot (K := K) (L := L) G P)]
    exact
      dedekindTower_ramificationIdx_mul_inertiaDeg_eq_card_of_nonsplit
        (A := 𝓞 (inertiaField (K := K) (L := L) G P))
        (B := 𝓞 L)
        (p := inertiaFieldPrime (K := K) (L := L) G P)
        (P := P)
        (inertiaFieldPrime_ne_bot (K := K) (L := L) G P)
        (inertiaGroup P G)
        (dedekindRamification_inertiaFieldPrime_primesOver_ncard_eq_one
          (K := K) (L := L) G P)
  have hbase :
      Nat.card (inertiaGroup P G) =
        Ideal.ramificationIdx' (basePrime (K := K) P) P := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (basePrime (K := K) P) P (basePrime_ne_bot (K := K) P)]
    exact
      inertia_card_eq_ramificationIdx
        (A := 𝓞 K) (B := 𝓞 L)
        (basePrime (K := K) P) P G (basePrime_ne_bot (K := K) P)
  exact htop.trans hbase

omit [NumberField K] [NumberField L] in
/-- A prime-decomposition consequence:
the residue extension for `P/P_T` is separable whenever the original residue
extension `kappa(P)/kappa(p)` is separable. -/
theorem dedekindRamification_inertiaFieldPrime_residue_isSeparable
    (P : Ideal (𝓞 L)) [P.IsMaximal]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Algebra.IsSeparable
      ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
        inertiaFieldPrime (K := K) (L := L) G P)
      ((𝓞 L) ⧸ P) := by
  have hKT :=
    (inertiaFieldPrime (K := K) (L := L) G P).over_def
      (basePrime (K := K) P)
  have hTL :=
    P.over_def (inertiaFieldPrime (K := K) (L := L) G P)
  have hKL :=
    P.over_def (basePrime (K := K) P)
  let :
      Algebra ((𝓞 K) ⧸ basePrime (K := K) P)
        ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
          inertiaFieldPrime (K := K) (L := L) G P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hKT.le
  let :
      Algebra
        ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
          inertiaFieldPrime (K := K) (L := L) G P)
        ((𝓞 L) ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hTL.le
  let :
      Algebra ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap hKL.le
  let :
      IsScalarTower
        ((𝓞 K) ⧸ basePrime (K := K) P)
        ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
          inertiaFieldPrime (K := K) (L := L) G P)
        ((𝓞 L) ⧸ P) :=
    IsScalarTower.of_algebraMap_eq <| by
      rintro ⟨x⟩
      exact
        congr_arg _
          (IsScalarTower.algebraMap_apply
            (𝓞 K) (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) x)
  exact
    Algebra.isSeparable_tower_top_of_isSeparable
      ((𝓞 K) ⧸ basePrime (K := K) P)
      ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
        inertiaFieldPrime (K := K) (L := L) G P)
      ((𝓞 L) ⧸ P)

/-- A prime-decomposition consequence:
`P/P_T` has residue degree one. -/
theorem dedekindRamification_inertiaFieldPrime_inertiaDeg_eq_one
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    P.inertiaDeg (𝓞 (inertiaField (K := K) (L := L) G P)) = 1 := by
  let :
      IsGaloisGroup (inertiaGroup P G)
        (inertiaField (K := K) (L := L) G P) L :=
    IsGaloisGroup.subgroup G K L (inertiaGroup P G)
  let :
      IsGaloisGroup (inertiaGroup P G)
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (inertiaGroup P G)
      (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L)
      (inertiaField (K := K) (L := L) G P) L
  have :
      Module.Finite
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    ringOfIntegers_moduleFinite
      (K := inertiaField (K := K) (L := L) G P) (L := L)
  have :
      Algebra.IsSeparable
        ((𝓞 (inertiaField (K := K) (L := L) G P)) ⧸
          inertiaFieldPrime (K := K) (L := L) G P)
        ((𝓞 L) ⧸ P) :=
    dedekindRamification_inertiaFieldPrime_residue_isSeparable (K := K) (L := L) G P
  have hquot :
      Nat.card
          (decompositionGroup P (inertiaGroup P G) ⧸
            (inertiaGroup P (inertiaGroup P G)).subgroupOf
              (decompositionGroup P (inertiaGroup P G))) =
        P.inertiaDeg (𝓞 (inertiaField (K := K) (L := L) G P)) := by
    exact
      dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
        (A := 𝓞 (inertiaField (K := K) (L := L) G P)) (B := 𝓞 L)
        (inertiaFieldPrime (K := K) (L := L) G P) P (inertiaGroup P G)
  have hsubtop :
      (inertiaGroup P (inertiaGroup P G)).subgroupOf
          (decompositionGroup P (inertiaGroup P G)) = ⊤ := by
    rw [dedekindRamification_inertiaGroup_inertiaGroup_eq_top (B := 𝓞 L) P G,
      dedekindRamification_inertiaGroup_decompositionGroup_eq_top (B := 𝓞 L) P G,
      Subgroup.top_subgroupOf]
  have hquot_one :
      Nat.card
          (decompositionGroup P (inertiaGroup P G) ⧸
            (inertiaGroup P (inertiaGroup P G)).subgroupOf
              (decompositionGroup P (inertiaGroup P G))) = 1 := by
    rw [hsubtop]
    exact
      Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
  exact hquot.symm.trans hquot_one

/-- Ramification over the inertia field:
over the inertia field, `P` has ramification index `e` and residue degree `1`.
-/
theorem dedekindRamification_inertiaFieldPrime_top_invariants
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Ideal.ramificationIdx' (inertiaFieldPrime (K := K) (L := L) G P) P =
        Ideal.ramificationIdx' (basePrime (K := K) P) P ∧
      P.inertiaDeg (𝓞 (inertiaField (K := K) (L := L) G P)) = 1 := by
  have hf :
      P.inertiaDeg (𝓞 (inertiaField (K := K) (L := L) G P)) = 1 :=
    dedekindRamification_inertiaFieldPrime_inertiaDeg_eq_one (K := K) (L := L) G P
  refine ⟨?_, hf⟩
  have hprod :=
    dedekindRamification_inertiaFieldPrime_product_eq_base_ramificationIdx
      (K := K) (L := L) G P
  rwa [hf, mul_one] at hprod

/-- Ramification between the decomposition and inertia fields:
between the decomposition field and inertia field, `P_T/P_Z` has
ramification index `1` and residue degree `f`. -/
theorem dedekindRamification_inertiaFieldPrime_middle_invariants
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) (inertiaFieldPrime (K
      := K) (L := L) G P) = 1 ∧
      (inertiaFieldPrime (K := K) (L := L) G P).inertiaDeg
          (𝓞 (decompositionField (K := K) (L := L) G P)) =
        P.inertiaDeg (𝓞 K) := by
  have :
      Module.Finite
        (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L) :=
    ringOfIntegers_moduleFinite
      (K := inertiaField (K := K) (L := L) G P) (L := L)
  have hPT_ne :
      Ideal.map
          (algebraMap
            (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L))
          (inertiaFieldPrime (K := K) (L := L) G P) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (inertiaFieldPrime_ne_bot (K := K) (L := L) G P)
  have hPZ_ne :
      Ideal.map
          (algebraMap
            (𝓞 (decompositionField (K := K) (L := L) G P)) (𝓞 L))
          (decompositionFieldPrime (K := K) (L := L) G P) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot
      (decompositionFieldPrime_ne_bot (K := K) (L := L) G P)
  have hPT_le :
      Ideal.map
          (algebraMap
            (𝓞 (inertiaField (K := K) (L := L) G P)) (𝓞 L))
          (inertiaFieldPrime (K := K) (L := L) G P) ≤ P := by
    rw [inertiaFieldPrime, Ideal.under_def]
    exact Ideal.map_comap_le
  have htop :=
    dedekindRamification_inertiaFieldPrime_top_invariants (K := K) (L := L) G P
  have hdecomposition :=
    dedekindTower_decompositionFieldPrime_tower_invariants
      (K := K) (L := L) G P
  have heTop :
      Ideal.ramificationIdx' (inertiaFieldPrime (K := K) (L := L) G P) P =
        Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) P :=
    htop.1.trans hdecomposition.2.2.1.symm
  have hmiddle :
      Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) (inertiaFieldPrime
        (K := K) (L := L) G P) = 1 ∧
        (inertiaFieldPrime (K := K) (L := L) G P).inertiaDeg
            (𝓞 (decompositionField (K := K) (L := L) G P)) =
          P.inertiaDeg
            (𝓞 (decompositionField (K := K) (L := L) G P)) :=
    dedekindRamification_ideal_tower_middle_invariants_of_top_invariants
      (A := 𝓞 (decompositionField (K := K) (L := L) G P))
      (B := 𝓞 (inertiaField (K := K) (L := L) G P))
      (C := 𝓞 L)
      (p := decompositionFieldPrime (K := K) (L := L) G P)
      (P := inertiaFieldPrime (K := K) (L := L) G P)
      (Q := P)
      hPT_ne hPZ_ne hPT_le heTop htop.2
  exact ⟨hmiddle.1, hmiddle.2.trans hdecomposition.2.2.2⟩

/-- A prime-decomposition consequence:
`[L : T_P] = e`. -/
theorem dedekindRamification_inertiaField_finrank_eq_base_ramificationIdx
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Module.finrank (inertiaField (K := K) (L := L) G P) L =
      P.ramificationIdx (𝓞 K) := by
  calc
    Module.finrank (inertiaField (K := K) (L := L) G P) L =
        Nat.card (inertiaGroup P G) :=
      dedekindRamification_inertiaField_finrank_eq_inertia_card
        (K := K) (L := L) G P
    _ =
        P.ramificationIdx (𝓞 K) := by
      exact
        inertia_card_eq_ramificationIdx
          (A := 𝓞 K) (B := 𝓞 L)
          (basePrime (K := K) P) P G (basePrime_ne_bot (K := K) P)

/-- A prime-decomposition consequence:
`[T_P : Z_P] = f`. -/
theorem dedekindRamification_inertiaFieldOverDecompositionField_finrank_eq_base_inertiaDeg
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Module.finrank (decompositionField (K := K) (L := L) G P)
        (inertiaFieldOverDecompositionField (K := K) (L := L) G P) =
      P.inertiaDeg (𝓞 K) := by
  calc
    Module.finrank (decompositionField (K := K) (L := L) G P)
        (inertiaFieldOverDecompositionField (K := K) (L := L) G P) =
        Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) :=
      dedekindRamification_inertiaFieldOverDecompositionField_finrank_eq_quotient_card
        (K := K) (L := L) G P
    _ =
        P.inertiaDeg (𝓞 K) := by
      exact
        dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
          (A := 𝓞 K) (B := 𝓞 L) (basePrime (K := K) P) P G

/-- Degree and cardinality relations in the fixed-field tower:
`#I_P = [L:T_P] = e` and `#(G_P/I_P) = [T_P:Z_P] = f`. -/
theorem dedekindRamification_inertiaField_degree_cardinalities
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Nat.card (inertiaGroup P G) =
        P.ramificationIdx (𝓞 K) ∧
      Module.finrank (inertiaField (K := K) (L := L) G P) L =
        P.ramificationIdx (𝓞 K) ∧
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        P.inertiaDeg (𝓞 K) ∧
      Module.finrank (decompositionField (K := K) (L := L) G P)
          (inertiaFieldOverDecompositionField (K := K) (L := L) G P) =
        P.inertiaDeg (𝓞 K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      inertia_card_eq_ramificationIdx
        (A := 𝓞 K) (B := 𝓞 L)
        (basePrime (K := K) P) P G (basePrime_ne_bot (K := K) P)
  · exact
      dedekindRamification_inertiaField_finrank_eq_base_ramificationIdx
        (K := K) (L := L) G P
  · exact
      dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
        (A := 𝓞 K) (B := 𝓞 L) (basePrime (K := K) P) P G
  · exact
      dedekindRamification_inertiaFieldOverDecompositionField_finrank_eq_base_inertiaDeg
        (K := K) (L := L) G P

/-- Ramification and residue degrees in the ideal-level fixed-field tower:
`Z_P -> T_P -> L` has ramification indices `1, e` and residue degrees
`f, 1`. -/
theorem dedekindRamification_inertiaFieldPrime_tower_invariants
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    Ideal.ramificationIdx' (inertiaFieldPrime (K := K) (L := L) G P) P =
        Ideal.ramificationIdx' (basePrime (K := K) P) P ∧
      P.inertiaDeg (𝓞 (inertiaField (K := K) (L := L) G P)) = 1 ∧
      Ideal.ramificationIdx' (decompositionFieldPrime (K := K) (L := L) G P) (inertiaFieldPrime
        (K := K) (L := L) G P) = 1 ∧
      (inertiaFieldPrime (K := K) (L := L) G P).inertiaDeg
          (𝓞 (decompositionField (K := K) (L := L) G P)) =
        P.inertiaDeg (𝓞 K) := by
  have htop :=
    dedekindRamification_inertiaFieldPrime_top_invariants (K := K) (L := L) G P
  have hmiddle :=
    dedekindRamification_inertiaFieldPrime_middle_invariants (K := K) (L := L) G P
  exact ⟨htop.1, htop.2, hmiddle.1, hmiddle.2⟩

omit [SMulCommClass G K L] in
/-- A trivial-inertia special case:
under the separable residue hypothesis, `I_P = 1` if and only if `P` is
unramified over `O_K`. -/
theorem inertiaGroup_eq_bot_iff_isUnramifiedAt
    {P : Ideal (𝓞 L)} [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    inertiaGroup P G = ⊥ ↔ Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hunram :
      Algebra.IsUnramifiedAt (𝓞 K) P ↔
        P.ramificationIdx (𝓞 K) = 1 :=
    (Ideal.ramificationIdx_eq_one_iff (q := P) (R := 𝓞 K)).symm
  have hram :
      inertiaGroup P G = ⊥ ↔
        P.ramificationIdx (𝓞 K) = 1 := by
    rw [← Subgroup.card_eq_one,
      inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 L)
      (basePrime (K := K) P) P G (basePrime_ne_bot (K := K) P)]
  exact hram.trans hunram.symm

/-- A trivial-inertia special case:
under the separable residue hypothesis, `T_P = L` if and only if `P` is
unramified over `O_K`. -/
theorem dedekindRamification_inertiaField_eq_top_iff_isUnramifiedAt
    {P : Ideal (𝓞 L)} [P.IsPrime] [P.IsMaximal]
    [Finite G] [IsGaloisGroup G K L]
    [Algebra.IsSeparable ((𝓞 K) ⧸ basePrime (K := K) P) ((𝓞 L) ⧸ P)] :
    inertiaField (K := K) (L := L) G P = ⊤ ↔
      Algebra.IsUnramifiedAt (𝓞 K) P :=
  (dedekindRamification_inertiaField_eq_top_iff_inertiaGroup_eq_bot
    (K := K) (L := L) (G := G) (P := P)).trans
    (inertiaGroup_eq_bot_iff_isUnramifiedAt
      (K := K) (L := L) (G := G) (P := P))

end Dedekind
end HilbertRamification
