/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.UniversalAssembly


/-! The (actual) Bernstein degree, read directly from checked PBW normal form. -/

@[expose] public section


namespace Stafford38.FixedSource

open Stafford38
open Stafford38.WeylFiltration
open Stafford38.Characteristic
open Stafford38.WeylPBW
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylSymplectic
open Stafford38.WeylLeadingSymbol
open Stafford

noncomputable section
universe u


/-- The Bernstein degree computed from the total weight of the checked PBW normal form. -/
def bernsteinDegree (k : Type u) [Field k] {n : ℕ}
    (d : PresentedWeyl k n) : ℕ :=
  MvPolynomial.weightedTotalDegree (@bernsteinWeight n)
    (presentedNormalFormLinearEquiv k n d)

/-- A presented Weyl coordinate arising from an invertible symplectic change of generators. -/
def IsLinearWeylCoordinate (k : Type u) [Field k] (n : ℕ)
    (ell : PresentedWeyl k (n + 1)) : Prop :=
  ∃ (M N : Matrix (PhaseVar (n + 1)) (PhaseVar (n + 1)) k)
      (_hM : M * standardForm k (n + 1) * Matrix.transpose M = standardForm k (n + 1))
      (_hN : N * standardForm k (n + 1) * Matrix.transpose N = standardForm k (n + 1))
      (_hMN : M * N = 1) (_hNM : N * M = 1),
      ell = freeWeylLinearCombination N
        (freeWeylGenerator (standardForm k (n + 1)))
        (.inl (0 : Fin (n + 1)))

/-- The exact fixed-source strengthening: the source exponent is the actual
Bernstein degree of the input operator, and the source coordinate is obtained
from an invertible linear symplectic change of Weyl generators. -/
def UniversalFixedSourceStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (d : PresentedWeyl k (n + 1)), d ≠ 0 →
      ∃ ell R S : PresentedWeyl k (n + 1),
        IsLinearWeylCoordinate k n ell ∧
          (1 : PresentedWeyl k (n + 1)) =
            d * R + ell ^ bernsteinDegree k d * d * S

theorem bernsteinDegree_eq_of_piece_of_principal_ne_zero
    (k : Type u) [Field k] {n N : ℕ} {d : PresentedWeyl k n}
    (hp : d ∈ bernsteinPiece k n N)
    (hP : presentedPrincipalComponent k (@bernsteinWeight n) N d ≠ 0) :
    bernsteinDegree k d = N := by
  let f := presentedNormalFormLinearEquiv k n d
  have hle : bernsteinDegree k d ≤ N := by
    apply Finset.sup_le
    intro m hm
    exact (hp m (MvPolynomial.mem_support_iff.mp hm))
  rcases MvPolynomial.support_nonempty.mpr hP with ⟨m, hm⟩
  have hm : (presentedPrincipalComponent k (@bernsteinWeight n) N d).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hcoeff := hm
  rw [coeff_presentedPrincipalComponent] at hcoeff
  have hweight : monomialWeight (@bernsteinWeight n) m = N := by
    by_contra hne
    have hz : (presentedPrincipalComponent k (@bernsteinWeight n) N d).coeff m = 0 := by
      rw [coeff_presentedPrincipalComponent]
      simp [hne]
    exact hm hz
  have hfd : f.coeff m ≠ 0 := by
    rw [ite_eq_left hweight] at hcoeff
    simpa [f] using hcoeff
  have hge : N ≤ bernsteinDegree k d := by
    calc
      N = monomialWeight (@bernsteinWeight n) m := hweight.symm
      _ ≤ bernsteinDegree k d :=
        MvPolynomial.le_weightedTotalDegree _ (MvPolynomial.mem_support_iff.mpr hfd)
  exact Nat.le_antisymm hle hge

end
end Stafford38.FixedSource
