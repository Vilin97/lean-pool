/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.FinitePlaceHilbertBadSet
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport
/-!
# Finiteness of the possible bad finite places

The set is defined by three explicit valuation conditions, independently of
any choice of local Hilbert symbols or of a larger auxiliary support.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- Only finitely many places fail to make `a`, `b`, and `n` all units. -/
theorem finitePlaceHilbertBadSet_finite
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (a b : Fˣ) :
    (finitePlaceHilbertBadSet F n a b).Finite := by
  classical
  let hnF : ((n : ℕ) : F) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Fˣ := Units.mk0 ((n : ℕ) : F) hnF
  let T : Finset (HeightOneSpectrum (𝓞 F)) :=
    (KummerTheory.chosenUnitFiniteSupport (K := F) a ∪
      KummerTheory.chosenUnitFiniteSupport (K := F) b) ∪
      KummerTheory.chosenUnitFiniteSupport (K := F) nUnit
  apply T.finite_toSet.subset
  intro v hv
  by_contra hvT
  have hvaSupport : v ∉ KummerTheory.chosenUnitFiniteSupport (K := F) a := by
    intro h
    exact hvT (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hvbSupport : v ∉ KummerTheory.chosenUnitFiniteSupport (K := F) b := by
    intro h
    exact hvT (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hvnSupport :
      v ∉ KummerTheory.chosenUnitFiniteSupport (K := F) nUnit := by
    intro h
    exact hvT (Finset.mem_union_right _ h)
  have hva : v.valuation F (a : F) = 1 :=
    (mem_SUnitGroup_iff (K := F)
      (KummerTheory.chosenUnitFiniteSupport (K := F) a) a).mp
      (KummerTheory.mem_sUnitGroup_chosenUnitFiniteSupport (K := F) a)
        v hvaSupport
  have hvb : v.valuation F (b : F) = 1 :=
    (mem_SUnitGroup_iff (K := F)
      (KummerTheory.chosenUnitFiniteSupport (K := F) b) b).mp
      (KummerTheory.mem_sUnitGroup_chosenUnitFiniteSupport (K := F) b)
        v hvbSupport
  have hvn : v.valuation F ((n : ℕ) : F) = 1 := by
    have hnUnitVal : v.valuation F (nUnit : F) = 1 :=
      (mem_SUnitGroup_iff (K := F)
        (KummerTheory.chosenUnitFiniteSupport (K := F) nUnit) nUnit).mp
        (KummerTheory.mem_sUnitGroup_chosenUnitFiniteSupport (K := F) nUnit)
          v hvnSupport
    change v.valuation F ((n : ℕ) : F) = 1 at hnUnitVal
    exact hnUnitVal
  change v.valuation F (a : F) ≠ 1 ∨
    v.valuation F (b : F) ≠ 1 ∨
    v.valuation F ((n : ℕ) : F) ≠ 1 at hv
  rcases hv with ha | hb | hn
  · exact ha hva
  · exact hb hvb
  · exact hn hvn

end ClassFieldTheory
