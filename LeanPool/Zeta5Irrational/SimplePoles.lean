/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module
public import Mathlib.LinearAlgebra.Lagrange

/-! # Partial fractions for rational polynomials with simple integer poles

This generic API is shared by the Zeta5 and Zeta32 arithmetic and contour proofs. -/

public section

open Finset Polynomial

namespace Zeta5Irrational

/-- `∏_{r ∈ Pl} (x - r)`. -/
@[expose] noncomputable def piPl (Pl : Finset ℤ) : ℚ[X] :=
  ∏ r ∈ Pl, (X - C (r : ℚ))

lemma piPl_monic (Pl : Finset ℤ) : (piPl Pl).Monic :=
  monic_prod_of_monic _ _ fun _r _ => monic_X_sub_C _

lemma natDegree_piPl (Pl : Finset ℤ) : (piPl Pl).natDegree = Pl.card := by
  unfold piPl
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C _]
  rw [Finset.sum_congr rfl fun (r : ℤ) _ => natDegree_X_sub_C ((r : ℤ) : ℚ)]
  simp

/-- The polynomial part. -/
@[expose] noncomputable def polyPart (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  A /ₘ piPl Pl

/-- The residue at `r`. -/
@[expose] noncomputable def resP (A : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) : ℚ :=
  A.eval (r : ℚ) / ∏ s ∈ Pl.erase r, ((r : ℚ) - s)

lemma lagrange_basis_eq (Pl : Finset ℤ) (r : ℤ) :
    Lagrange.basis Pl (fun s : ℤ => (s : ℚ)) r =
      C (∏ s ∈ Pl.erase r, ((r : ℚ) - s))⁻¹ * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
  unfold Lagrange.basis Lagrange.basisDivisor
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]

/-- **Partial fractions**. -/
theorem partial_fractionsP (A : ℚ[X]) (Pl : Finset ℤ) :
    A = polyPart A Pl * piPl Pl + ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) :=
  by
  have hinj : Set.InjOn (fun s : ℤ => (s : ℚ)) Pl := fun a _ b _ h => by simpa using h
  have hmod : A %ₘ piPl Pl = ∑ r ∈ Pl, C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) := by
    rw [Lagrange.eq_interpolate_of_eval_eq (f := A %ₘ piPl Pl) (fun r : ℤ => A.eval (r : ℚ)) hinj
        (by
          have := degree_modByMonic_lt A (piPl_monic Pl)
          rwa [degree_eq_natDegree (piPl_monic Pl).ne_zero, natDegree_piPl] at this)
        (fun r hr => by
          have h1 := modByMonic_add_div A (piPl Pl)
          have h2 : (piPl Pl).eval (r : ℚ) = 0 := by
            unfold piPl; rw [eval_prod]
            exact Finset.prod_eq_zero hr (by simp)
          conv_rhs => rw [← h1]
          rw [eval_add, eval_mul, h2, zero_mul, add_zero])]
    simp only [Lagrange.interpolate_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lagrange_basis_eq, resP, div_eq_mul_inv, C_mul, mul_assoc]
  conv_lhs => rw [← modByMonic_add_div A (piPl Pl)]
  rw [hmod, polyPart, add_comm, mul_comm]

lemma natDegree_polyPart_le (A : ℚ[X]) (Pl : Finset ℤ) :
    (polyPart A Pl).natDegree ≤ A.natDegree - Pl.card := by
  unfold polyPart
  rw [natDegree_divByMonic A (piPl_monic Pl), natDegree_piPl]


end Zeta5Irrational

end
