/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.CoisotropicTranslation


/-!
# Base-relative Poisson closure

The vertical-translation argument needs only brackets whose left entry comes
from the base-coordinate ring.  This file isolates that exact hypothesis and
shows that it suffices for the existing Hamiltonian-iteration argument.

No assertion is made here that a radical initial ideal, or the reduced
characteristic ideal of a Weyl module, satisfies this condition.  Supplying
that fact is the remaining Gabber input.
-/

@[expose] public section

namespace Stafford38.Characteristic.BaseRelativePoisson

open Stafford38.Characteristic
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/--
The exact base-relative fragment of Poisson involutivity:
`{J ∩ k[x], J} ⊆ J`, expressed using the canonical base embedding.
-/
def IsBaseRelativePoisson (J : Ideal (SymbolRing k n)) : Prop :=
  ∀ f : MvPolynomial (Fin n) k, baseLift f ∈ J →
    ∀ g ∈ J, poissonBracket (baseLift f) g ∈ J

/-- Full Poisson closure implies the base-relative fragment. -/
theorem IsPoisson.isBaseRelativePoisson
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J) :
    IsBaseRelativePoisson J := by
  intro f hf g hg
  exact hJ (baseLift f) hf g

/-- Base-relative closure is preserved through all iterated Hamiltonian brackets. -/
theorem hamiltonIter_mem_of_isBaseRelativePoisson
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    ∀ m, hamiltonIter f m g ∈ J := by
  intro m
  induction m with
  | zero => exact hg
  | succ m hm => exact hJ f hf (hamiltonIter f m g) hm

/--
The fibre-line polynomial vanishes under the exact base-relative Gabber
fragment; full Poisson closure is not needed.
-/
theorem fibreLinePolynomial_eq_zero_of_isBaseRelativePoisson
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    fibreLinePolynomial y (differentialAt y f) g = 0 := by
  apply polynomial_eq_zero_of_eval_iterate_derivative_zero
  intro m
  rw [iterate_derivative_fibreLinePolynomial, eval_zero_fibreLinePolynomial]
  exact hzero _ (hamiltonIter_mem_of_isBaseRelativePoisson J hJ f hf g hg m)

/--
A zero-section common zero remains a common zero after translation by
`t df_y`, assuming only `{J ∩ k[x], J} ⊆ J`.
-/
theorem zeroSection_stable_under_differential_translation_of_isBaseRelativePoisson
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (differentialTranslatePoint y f t) g = 0 := by
  have heval :
      MvPolynomial.eval (differentialTranslatePoint y f t) g =
        MvPolynomial.eval (Sum.elim y (fun i => t * differentialAt y f i)) g := by
    apply MvPolynomial.eval₂_congr
    intro i c hi hc
    rcases i with i | i <;> rfl
  rw [heval, ← eval_fibreLinePolynomial]
  rw [fibreLinePolynomial_eq_zero_of_isBaseRelativePoisson J hJ y hzero f hf g hg]
  exact Polynomial.eval_zero


end

end Stafford38.Characteristic.BaseRelativePoisson
