/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebraNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
import Mathlib.NumberTheory.LocalField.Basic
/-!
# The reducible Kummer algebra at one

Even when its rank is `n`, the algebra `K[X]/(Xⁿ-1)` has surjective norm
under the local Kummer hypotheses. This is the simplest instance showing
that norm index and algebra rank are different invariants.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- The Kummer algebra defined by `Xⁿ-1` has full unit norm image. -/
theorem kummerAlgebraNormSubgroup_one_eq_top
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    kummerAlgebraNormSubgroup K n 1 = ⊤ := by
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
  have hmuS : (primitiveRoots (n : ℕ) S).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    refine ⟨e.symm ζ, ?_⟩
    exact (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective e.symm.injective)
  let B₀ : HilbertPairing S n := localHilbertPairing S n hnS hmuS
  let B : HilbertPairing K n := hilbertPairingOfRingEquiv e n hmuS B₀
  have hB : HilbertPairing.IsLocalHilbertPairing B :=
    hilbertPairingOfRingEquiv_isLocalHilbertPairing e n hmuS B₀
      (localHilbertPairing_isLocalHilbertPairing S n hnS hmuS)
  apply top_unique
  intro b _
  have hbNorm : IsKummerNorm K n 1 b :=
    (hB.2.2.2 1 b).1 (by simp [HilbertPairing.symbol])
  obtain ⟨y, hy⟩ := hbNorm
  refine ⟨y, ?_⟩
  apply Units.ext
  exact hy

end ClassFieldTheory
