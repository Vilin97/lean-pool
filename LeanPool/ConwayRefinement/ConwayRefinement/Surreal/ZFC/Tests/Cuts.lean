/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Cuts

/-!
# Imported checks for class-coded Conway cuts

The infinite left set of all natural numbers excludes a construction restricted to finite cuts
or collapsing a cut to one of its options. A nonempty right-option code representing zero separates
literal ZFC code equality from numerical Conway equivalence. The ordinary empty and singleton cuts
are interface smoke tests, not substitutes for these semantic separators.
-/

universe u

public noncomputable section

open Set

namespace Tests.ClassSurrealCuts

example (s t : Set ZFSet.Surreal.{u}) [Small.{u} s] [Small.{u} t]
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ZFSet.Surreal.toSurreal (!{s | t}'h) =
      !{ZFSet.Surreal.toSurreal '' s | ZFSet.Surreal.toSurreal '' t}'
        (ZFSet.Surreal.toSurreal_separated s t h) :=
  ZFSet.Surreal.toSurreal_ofSets s t h

example (s t : Set ZFSet.GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ZFSet.Surreal.mk (ZFSet.GameCode.ofSets s t)
        (ZFSet.GameCode.isNumeric_ofSets s t hs ht h) =
      !{ZFSet.Surreal.codeValues s hs | ZFSet.Surreal.codeValues t ht}'
        (ZFSet.Surreal.codeValues_separated s t hs ht h) :=
  ZFSet.Surreal.mk_ofSets s t hs ht h

example (s t : Set ZFSet.GameCode.{u}) [Small.{u} s] [Small.{u} t] :
    (ZFSet.GameCode.ofSets s t : ZFSet.{u}) = ZFSet.pair
      (ZFSet.range fun x : s ↦ (x.1 : ZFSet.{u}))
      (ZFSet.range fun x : t ↦ (x.1 : ZFSet.{u})) :=
  ZFSet.GameCode.coe_ofSets s t

example : (!{∅ | ∅} : ZFSet.Surreal.{u}) = 0 := by
  apply ZFSet.Surreal.toSurreal_injective
  simp only [ZFSet.Surreal.toSurreal_ofSets, Set.image_empty, ZFSet.Surreal.toSurreal_zero]
  rw [Surreal.zero_def]
  congr 1
  funext p
  cases p <;> rfl

example : (!{{0} | ∅} : ZFSet.Surreal.{u}) = 1 := by
  apply ZFSet.Surreal.toSurreal_injective
  simpa only [ZFSet.Surreal.toSurreal_ofSets, Set.image_singleton, Set.image_empty,
    ZFSet.Surreal.toSurreal_zero, ZFSet.Surreal.toSurreal_one] using Surreal.one_def.symm

example : (0 : ZFSet.Surreal.{u}) < !{{0} | {1}} ∧
    (!{{0} | {1}} : ZFSet.Surreal.{u}) < 1 := by
  exact ⟨ZFSet.Surreal.lt_ofSets_of_mem_left (Set.mem_singleton _),
    ZFSet.Surreal.ofSets_lt_of_mem_right (Set.mem_singleton _)⟩

/-- A class cut whose left set is infinite, with every natural number as a left option. -/
def aboveNaturals : ZFSet.Surreal.{u} := !{Set.range (fun n : ℕ ↦ (n : ZFSet.Surreal.{u})) | ∅}

/-- The infinite cut is strictly above every natural number, not merely a finite option bound. -/
theorem nat_lt_aboveNaturals (n : ℕ) : (n : ZFSet.Surreal.{u}) < aboveNaturals :=
  ZFSet.Surreal.lt_ofSets_of_mem_left (Set.mem_range_self n)

/-- The infinite cut is not any finite natural number. -/
theorem aboveNaturals_ne_nat (n : ℕ) : aboveNaturals.{u} ≠ (n : ZFSet.Surreal.{u}) :=
  (nat_lt_aboveNaturals n).ne'

/-- The raw code with no left options and the single right option one. -/
def noncanonicalZero : ZFSet.GameCode.{u} := ZFSet.GameCode.ofSets ∅ {1}

/-- The noncanonical zero code is numeric because all its options are numeric and separated. -/
theorem noncanonicalZero_numeric : noncanonicalZero.{u}.IsNumeric :=
  ZFSet.GameCode.isNumeric_ofSets ∅ {1} (by simp) (by simp) (by simp)

/-- The noncanonical zero code is not literally the empty-option zero code. -/
theorem noncanonicalZero_ne_zero : noncanonicalZero.{u} ≠ 0 := by
  intro h
  have hm := congrArg (fun x : ZFSet.GameCode.{u} ↦ x.toIGame.moves Player.right) h
  simp [noncanonicalZero] at hm

/-- The noncanonical zero code nevertheless represents precisely the zero class value. -/
theorem mk_noncanonicalZero :
    ZFSet.Surreal.mk noncanonicalZero.{u} noncanonicalZero_numeric = 0 := by
  apply ZFSet.Surreal.toSurreal_injective
  apply Surreal.toGame_inj.1
  rw [ZFSet.Surreal.toSurreal_mk, Surreal.toGame_mk,
    ZFSet.Surreal.toSurreal_zero, Surreal.toGame_zero]
  apply ConwayGame.mk_eq
  rw [noncanonicalZero, ZFSet.GameCode.toIGame_ofSets]
  apply IGame.fits_zero_iff_equiv.1
  simp [IGame.Fits]

end Tests.ClassSurrealCuts
