/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.RegularTrace

/-!
# Class functions give central elements

The group-algebra element attached to a conjugation-invariant
coefficient function is central — pure coefficient algebra, no
representation theory.
-/

@[expose] public section

namespace RS

open Finset

variable {G : Type*}

/-- The group-algebra element attached to a coefficient
function. -/
noncomputable def classElem [Group G] [Fintype G]
    (c : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ g : G, c g • MonoidAlgebra.single g 1

/-- The element built from a coefficient function has exactly those
coefficients. -/
theorem classElem_coeff [Group G] [Fintype G]
    (c : G → ℂ) (k : G) :
    (classElem c).coeff k = c k := by
  classical
  rw [classElem]
  rw [show ((∑ g : G, c g • MonoidAlgebra.single g 1).coeff k) =
    ∑ g : G, (c g • MonoidAlgebra.single g (1 : ℂ)).coeff k from by
      rw [MonoidAlgebra.coeff_sum]
      exact Finsupp.finsetSum_apply _ _ _]
  rw [Finset.sum_congr rfl (fun g _ => show
      (c g • MonoidAlgebra.single g (1 : ℂ)).coeff k =
      if g = k then c g else 0 from by
    rw [show (c g • MonoidAlgebra.single g (1 : ℂ)).coeff k =
        c g • (MonoidAlgebra.single g (1 : ℂ)).coeff k from
      MonoidAlgebra.coeff_smul_apply (c g) _ k]
    rw [show (MonoidAlgebra.single g (1 : ℂ)).coeff k =
      if g = k then 1 else 0 from Finsupp.single_apply]
    by_cases h : g = k <;> simp [h])]
  rw [Finset.sum_ite_eq' Finset.univ k c]
  rw [ite_eq_left (Finset.mem_univ k)]

/-- **Class functions give central elements.** -/
theorem classElem_mul_comm [Group G] [Fintype G]
    (c : G → ℂ)
    (hc : ∀ g h : G, c (h * g * h⁻¹) = c g)
    (y : MonoidAlgebra ℂ G) :
    classElem c * y = y * classElem c := by
  classical
  induction y using MonoidAlgebra.induction_on with
  | of m =>
    refine MonoidAlgebra.coeff_injective ?_
    ext k
    change (classElem c * MonoidAlgebra.of ℂ G m).coeff k =
      (MonoidAlgebra.of ℂ G m * classElem c).coeff k
    rw [show MonoidAlgebra.of ℂ G m =
      MonoidAlgebra.single m (1 : ℂ) from rfl]
    rw [show (classElem c * MonoidAlgebra.single m (1 : ℂ)).coeff k =
        (classElem c).coeff (k * m⁻¹) * 1 from
      MonoidAlgebra.coeff_mul_single_apply (classElem c) 1 m k,
      show (MonoidAlgebra.single m (1 : ℂ) * classElem c).coeff k =
        1 * (classElem c).coeff (m⁻¹ * k) from
      MonoidAlgebra.coeff_single_mul_apply (classElem c) 1 m k]
    rw [classElem_coeff, classElem_coeff, mul_one, one_mul]
    have := hc (k * m⁻¹) m⁻¹
    rw [show m⁻¹ * (k * m⁻¹) * m⁻¹⁻¹ = m⁻¹ * k from by group] at this
    exact this.symm
  | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  | smul r a ha => rw [mul_smul_comm, smul_mul_assoc, ha]

end RS
