/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.KummerAlgebraUniformFactorDegree
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Fintype.EquivFin
/-!
# Exact number of copies of one Kummer field factor

When the `n`-th roots of unity lie in the base field, the finite field
factors of the Kummer algebra are all isomorphic. We choose one factor and
reindex the product by `Fin (n / d)`, where `d` is that factor's degree.
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- A Kummer algebra of exponent `n` is a product of exactly `n / d` copies
of one finite separable field factor of degree `d`. The norm is the product
of the coordinate field norms under this algebra equivalence. -/
theorem kummerAlgebra_exists_pi_copies_simpleFactor
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ)
    (hn : IsUnit ((n : ℕ) : K))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (_ : Module.Finite K F) (_ : Algebra.IsSeparable K F) (d : ℕ),
      0 < d ∧ Module.finrank K F = d ∧
      ((n : ℕ) / d) * d = (n : ℕ) ∧
      ∃ e : KummerAlgebra K n a ≃ₐ[K] (Fin ((n : ℕ) / d) → F),
        ∀ z : KummerAlgebra K n a,
          Algebra.norm K z = ∏ j : Fin ((n : ℕ) / d), Algebra.norm K (e z j) := by
  classical
  obtain ⟨I, hI, E, hField, hAlgebra, e, d, hDPos, hFactors, hIso,
      hMul, hCard⟩ :=
    kummerAlgebra_exists_uniformFactorDegree K n a hn hmu
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (E i) := hField i
  let (i : I) : Algebra K (E i) := hAlgebra i
  have hCardNe : Nat.card I ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hMul
    exact n.pos.ne' hMul.symm
  have hFCardPos : 0 < Fintype.card I := by
    simpa only [Nat.card_eq_fintype_card, Nat.cast_id] using
      (Nat.pos_of_ne_zero hCardNe)
  let i₀ : I := Classical.choice (Fintype.card_pos_iff.mp hFCardPos)
  let F := E i₀
  let : Module.Finite K F := (hFactors i₀).1
  have hFCard : Fintype.card I = (n : ℕ) / d := by
    simpa only [Nat.card_eq_fintype_card, Nat.cast_id] using hCard
  let σ : I ≃ Fin ((n : ℕ) / d) := Fintype.equivFinOfCardEq hFCard
  let f (i : I) : E i ≃ₐ[K] F := Classical.choice (hIso i i₀)
  let eFactors : (∀ i : I, E i) ≃ₐ[K] (I → F) :=
    AlgEquiv.piCongrRight f
  let eIndex : (I → F) ≃ₐ[K] (Fin ((n : ℕ) / d) → F) :=
    AlgEquiv.piCongrLeft' K (fun _ : I => F) σ
  let eTotal : KummerAlgebra K n a ≃ₐ[K] (Fin ((n : ℕ) / d) → F) :=
    (e.trans eFactors).trans eIndex
  have hCount : ((n : ℕ) / d) * d = (n : ℕ) := by
    rw [← hCard]
    exact hMul
  refine ⟨F, hField i₀, hAlgebra i₀, (hFactors i₀).1,
    (hFactors i₀).2.1, d, hDPos, (hFactors i₀).2.2, hCount, eTotal, ?_⟩
  intro z
  calc
    Algebra.norm K z = Algebra.norm K (eTotal z) :=
      (Algebra.norm_eq_of_algEquiv eTotal z).symm
    _ = ∏ j : Fin ((n : ℕ) / d), Algebra.norm K (eTotal z j) :=
      ValuationTheory.Completion.algebra_norm_pi_apply
        (fun _ : Fin ((n : ℕ) / d) => F) (eTotal z)

end ClassFieldTheory
