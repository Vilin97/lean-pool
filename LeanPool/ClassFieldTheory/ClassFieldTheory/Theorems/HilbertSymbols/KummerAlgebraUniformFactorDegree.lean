/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraUniformFieldFactors
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraFinrank
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraFiniteEtale
import Mathlib.LinearAlgebra.Dimension.Constructions
/-!
# Degree and number of uniform Kummer factors

When the `n`-th roots of unity lie in the base field, every field factor of
the Kummer algebra has the same positive degree `d`. The total rank `n` is
the number of factors times `d`.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- The uniform finite separable factors have common positive degree `d`,
and their number is `n / d`. This includes degree-one and reducible cases. -/
theorem kummerAlgebra_exists_uniformFactorDegree
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ (I : Type u) (_ : Finite I) (E : I → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (_ : KummerAlgebra K n a ≃ₐ[K] ∀ i, E i) (d : ℕ),
      0 < d ∧
      (∀ i, Module.Finite K (E i) ∧ Algebra.IsSeparable K (E i) ∧
        Module.finrank K (E i) = d) ∧
      (∀ i j, Nonempty (E i ≃ₐ[K] E j)) ∧
      Nat.card I * d = (n : ℕ) ∧ Nat.card I = (n : ℕ) / d := by
  classical
  obtain ⟨I, hI, E, hField, hAlgebra, e, hFactors, hIso⟩ :=
    kummerAlgebra_exists_algEquiv_pi_isomorphicFields K n a hn hmu
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (E i) := hField i
  let (i : I) : Algebra K (E i) := hAlgebra i
  let (i : I) : Module.Finite K (E i) := (hFactors i).1
  let : Module.Finite K (KummerAlgebra K n a) :=
    (kummerAlgebra_finiteEtale K n a hn).1
  have hSum : (∑ i : I, Module.finrank K (E i)) = (n : ℕ) := by
    calc
      _ = Module.finrank K (∀ i, E i) := (Module.finrank_pi_fintype K).symm
      _ = Module.finrank K (KummerAlgebra K n a) :=
        e.toLinearEquiv.finrank_eq.symm
      _ = (n : ℕ) := kummerAlgebra_finrank K n a
  have hSumNe : (∑ i : I, Module.finrank K (E i)) ≠ 0 := by
    rw [hSum]
    exact n.pos.ne'
  obtain ⟨i₀, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSumNe
  let d : ℕ := Module.finrank K (E i₀)
  have hDPos : 0 < d := Module.finrank_pos (R := K) (M := E i₀)
  have hCommon (i : I) : Module.finrank K (E i) = d := by
    obtain ⟨f⟩ := hIso i i₀
    exact f.toLinearEquiv.finrank_eq
  have hMul : Nat.card I * d = (n : ℕ) := by
    calc
      Nat.card I * d = ∑ _i : I, d := by
        simp only [Nat.card_eq_fintype_card, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      _ = ∑ i : I, Module.finrank K (E i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hCommon i).symm
      _ = (n : ℕ) := hSum
  have hCard : Nat.card I = (n : ℕ) / d := by
    calc
      Nat.card I = (d * Nat.card I) / d :=
        (Nat.mul_div_cancel_left (Nat.card I) hDPos).symm
      _ = (n : ℕ) / d := by rw [mul_comm d (Nat.card I), hMul]
  refine ⟨I, hI, E, hField, hAlgebra, e, d, hDPos, ?_, hIso, hMul, hCard⟩
  intro i
  exact ⟨(hFactors i).1, (hFactors i).2.1, hCommon i⟩

end ClassFieldTheory
