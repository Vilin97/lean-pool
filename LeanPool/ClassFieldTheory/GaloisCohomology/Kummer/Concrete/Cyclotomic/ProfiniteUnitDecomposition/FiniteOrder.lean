/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate
/-!
# Finite-order local coordinates of profinite units
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- If the free `p`-adic coordinate of a profinite unit vanishes, its
actual `p`-adic unit coordinate has finite order. -/
theorem zHatUnit_padicCoordinate_isOfFinOrder_of_freeCoordinate_eq_zero
    (u : ZHatˣ) (p : Nat.Primes)
    (hfree :
      zHatToPadicInt p
          (Multiplicative.toAdd
            (zHatUnitsDecomposition u).1) = 0) :
    IsOfFinOrder
      (zHatUnitsContinuousMulEquivPrimeProduct u p) := by
  let a :=
    ((padicUnitDecomposition p.1).symm
      (zHatUnitsContinuousMulEquivPrimeProduct u p)).1
  have hsecond :
      ((padicUnitDecomposition p.1).symm
        (zHatUnitsContinuousMulEquivPrimeProduct u p)).2 = 1 := by
    apply Multiplicative.ext
    simpa using
      (zHatUnitsDecomposition_freeCoordinate u p).symm.trans hfree
  have hpair :
      IsOfFinOrder
        (a, (1 : Multiplicative ℤ_[p.1])) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨orderOf a, orderOf_pos a, ?_⟩
    ext
    · exact pow_orderOf_eq_one a
    · simp
  have hsource :
      (a, (1 : Multiplicative ℤ_[p.1])) =
        (padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p) := by
    apply Prod.ext
    · rfl
    · exact hsecond.symm
  have himage :
      IsOfFinOrder
        (padicUnitDecomposition p.1
          (a, (1 : Multiplicative ℤ_[p.1]))) :=
    (Function.Injective.isOfFinOrder_iff
      (f := (padicUnitDecomposition p.1).toMonoidHom)
      (padicUnitDecomposition p.1).injective).2 hpair
  rw [hsource,
    (padicUnitDecomposition p.1).apply_symm_apply] at himage
  exact himage

end KummerTheory
