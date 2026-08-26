/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132WeiE2.Algebra.G10
import LeanPool.Erdos132WeiE2.Counting.Endgame
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Six-distance assembly for the E2 diameter-heptagon pattern

This module combines the algebraic exclusions and finite counting endgame.
-/

namespace LeanPool.Erdos132WeiE2.Counting

open LeanPool.Erdos132WeiE2.Algebra

theorem six_distances_of_parametrization
    (p : Fin 7 → EuclideanSpace ℝ (Fin 2))
    (h03 : dist (p 0) (p 3) = 1)
    (hs02 : dist (p 0) (p 2) < 1) (hs05 : dist (p 0) (p 5) < 1)
    (_hs13 : dist (p 1) (p 3) < 1)
    (hBAe : dist (p 1) (p 2) < dist (p 4) (p 5))
    (hACe : dist (p 4) (p 5) < dist (p 0) (p 1))
    (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hCpi : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi)
    (hclosure : 2 * Real.sin (A / 2) * (1 + 2 * Real.cos (A + B)) = 1)
    (heC : dist (p 0) (p 1) = 2 * Real.sin (C / 2))
    (heB : dist (p 1) (p 2) = 2 * Real.sin (B / 2))
    (heA : dist (p 4) (p 5) = 2 * Real.sin (A / 2))
    (hQ : (dist (p 0) (p 2)) ^ 2 =
      3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B))
    (hRA : (dist (p 0) (p 5)) ^ 2 =
      4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B))
    (hRB : (dist (p 1) (p 3)) ^ 2 =
      4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B)) :
    6 ≤ ((Finset.univ.filter fun q : Fin 7 × Fin 7 => q.1 ≠ q.2).image
      fun q => dist (p q.1) (p q.2)).card := by
  let V : Finset ℝ :=
    (Finset.univ.filter fun q : Fin 7 × Fin 7 => q.1 ≠ q.2).image
      fun q => dist (p q.1) (p q.2)
  let eB : ℝ := dist (p 1) (p 2)
  let eA : ℝ := dist (p 4) (p 5)
  let eC : ℝ := dist (p 0) (p 1)
  let Q : ℝ := dist (p 0) (p 2)
  let RA : ℝ := dist (p 0) (p 5)
  let RB : ℝ := dist (p 1) (p 3)
  have heCv : eC = 2 * Real.sin (C / 2) := heC
  have heBv : eB = 2 * Real.sin (B / 2) := heB
  have heAv : eA = 2 * Real.sin (A / 2) := heA
  have hQv : Q ^ 2 =
      3 - 2 * Real.cos A - 2 * Real.cos B + 2 * Real.cos (A + B) := hQ
  have hRAv : RA ^ 2 =
      4 - 4 * Real.cos A - 2 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (2 * A + B) := hRA
  have hRBv : RB ^ 2 =
      4 - 2 * Real.cos A - 4 * Real.cos B + 4 * Real.cos (A + B) -
        2 * Real.cos (A + 2 * B) := hRB
  have mem_dist (i j : Fin 7) (hij : i ≠ j) : dist (p i) (p j) ∈ V := by
    refine Finset.mem_image.mpr ⟨(i, j), ?_, rfl⟩
    simp [hij]
  have hmemB : eB ∈ V := mem_dist 1 2 (by decide)
  have hmemA : eA ∈ V := mem_dist 4 5 (by decide)
  have hmemC : eC ∈ V := mem_dist 0 1 (by decide)
  have hmemQ : Q ∈ V := mem_dist 0 2 (by decide)
  have hmemRA : RA ∈ V := mem_dist 0 5 (by decide)
  have hmemRB : RB ∈ V := mem_dist 1 3 (by decide)
  have hmem1 : (1 : ℝ) ∈ V := by
    simpa only [h03] using mem_dist 0 3 (by decide)
  have hApos : 0 < A := lt_trans hB hBA
  have hApi : A < Real.pi := by linarith [Real.pi_pos]
  have hSpos : 0 < A + B := by linarith
  have hSltTwo := add_lt_two_pi_div_three A B C hB hBA hAC hCpi hsum
  have hSpi : A + B < Real.pi := by linarith [Real.pi_pos]
  have hTwoAlt := two_mul_add_lt_pi A B C hB hBA hAC hCpi hsum
  have hAddTwoPos := add_two_mul_pos A B C hB hBA hAC hCpi hsum
  have hAddTwoLt := add_two_mul_lt_two_mul_add A B C hB hBA hAC hCpi hsum
  have hfactor : 0 < 1 + 2 * Real.cos (A + B) :=
    one_add_two_cos_pos hSpos hSltTwo
  have hsinA : 0 < Real.sin (A / 2) := sin_A_half_pos hApos hApi
  have hBpi : B < Real.pi := by linarith
  have hsinB : 0 < Real.sin (B / 2) := sin_B_half_pos hB hBpi
  have hidRA : RA ^ 2 - eA ^ 2 =
      4 * Real.sin (A / 2) ^ 2 * (1 + 2 * Real.cos (A + B)) := by
    rw [hRAv, heAv]
    exact ra_sq_sub_ea_sq_identity A B
  have hidRB : RB ^ 2 - eB ^ 2 =
      4 * Real.sin (B / 2) ^ 2 * (1 + 2 * Real.cos (A + B)) := by
    rw [hRBv, heBv]
    exact rb_sq_sub_eb_sq_identity A B
  have hidRARB : RA ^ 2 - RB ^ 2 =
      2 * ((Real.cos B - Real.cos A) +
        (Real.cos (A + 2 * B) - Real.cos (2 * A + B))) := by
    rw [hRAv, hRBv]
    exact ra_sq_sub_rb_sq_identity A B
  have hcosBA : Real.cos A < Real.cos B := cos_B_gt_cos_A hB hBA hApi
  have hcosAdd : Real.cos (2 * A + B) < Real.cos (A + 2 * B) :=
    cos_add_two_mul_gt_cos_two_mul_add hAddTwoPos hAddTwoLt hTwoAlt
  have hRASq : eA ^ 2 < RA ^ 2 := ra_sq_gt_ea_sq RA eA A B hidRA hsinA hfactor
  have hRBSq : eB ^ 2 < RB ^ 2 := rb_sq_gt_eb_sq RB eB A B hidRB hsinB hfactor
  have hRARBSq : RB ^ 2 < RA ^ 2 :=
    ra_sq_gt_rb_sq RA RB A B hidRARB hcosBA hcosAdd
  have rA1 : eA < RA := ra_gt_ea hRASq dist_nonneg dist_nonneg
  have rB1 : eB < RB := rb_gt_eb hRBSq dist_nonneg dist_nonneg
  have rB2 : RB < RA := ra_gt_rb hRARBSq dist_nonneg dist_nonneg
  have o3 : eC < Q := ec_lt_q_of_interface A B C eC Q hB hBA hAC hCpi hsum
    hclosure heCv hQv dist_nonneg dist_nonneg
  let x : ℝ := Real.tan (A / 4)
  let y : ℝ := Real.tan ((A + B) / 2)
  have hx : x = Real.tan (A / 4) := rfl
  have hy : y = Real.tan ((A + B) / 2) := rfl
  have hF' := closure_implies_polynomial A B x y hApos hApi hSpos hSpi hx hy hclosure
  have hF : x ^ 2 * y ^ 2 + x ^ 2 + 4 * x * y ^ 2 - 12 * x + y ^ 2 + 1 = 0 := by
    simpa only [closurePolynomial] using hF'
  have x1 : ¬(RA = Q ∧ RB = eC) := by
    rintro ⟨hRAQ, hRBeC⟩
    have hpRQ := ra_eq_q_implies_pRQ A B x y RA Q hApos hApi hSpos hSpi hx hy
      hclosure hRAv hQv hRAQ
    have hpBC := rb_eq_ec_implies_pBC A B C x y RB eC hsum hApos hApi hSpos hSpi
      hx hy hclosure hRBv heCv hRBeC
    exact exclude_ra_q_rb_ec x y hF hpRQ hpBC
  have x2 : ¬(RA = Q ∧ RB = eA) := by
    rintro ⟨hRAQ, hRBeA⟩
    have hpRQ := ra_eq_q_implies_pRQ A B x y RA Q hApos hApi hSpos hSpi hx hy
      hclosure hRAv hQv hRAQ
    have hpBA := rb_eq_ea_implies_pBA A B x y RB eA hApos hApi hSpos hSpi hx hy
      hclosure hRBv heAv hRBeA
    exact exclude_ra_q_rb_ea x y hF hpRQ hpBA
  have x3 : ¬(RA = eC ∧ RB = eA) := by
    rintro ⟨hRAeC, hRBeA⟩
    have hpRC := ra_eq_ec_implies_pRC A B C x y RA eC hsum hApos hApi hSpos hSpi
      hx hy hclosure hRAv heCv hRAeC
    have hpBA := rb_eq_ea_implies_pBA A B x y RB eA hApos hApi hSpos hSpi hx hy
      hclosure hRBv heAv hRBeA
    exact exclude_ra_ec_rb_ea x y hF hpRC hpBA
  exact six_le_card_of_values V eB eA eC Q RA RB hmemB hmemA hmemC hmemQ hmem1
    hmemRA hmemRB hBAe hACe o3 hs02 rA1 hs05 rB1 rB2 x1 x2 x3

end LeanPool.Erdos132WeiE2.Counting
