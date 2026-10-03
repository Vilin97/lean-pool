/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticIdempotence

/-!
# Consequences of the quartic idempotence equation

The nine-coordinate bridge is applied to an equation `F * c = F`, where
`F` is affine plus a Hankel target and `c` is affine plus a rational target.
Every summand except target times rational has degree at most three, so the
quartic equation is exactly the rational-annihilator probe.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem anfQuarticAnnihilatorProbe_eq_zero_of_mem_targetAmbient
    {p : ANF 8} (hp : p ∈ targetAmbient 8 (mulTarget 4)) (k : Fin 9) :
    anfQuarticAnnihilatorProbe p k = 0 := by
  change
    (if (quarticAnnihilatorSet k).card = 4 then
      p.coeff ⟨quarticAnnihilatorSet k⟩ else 0) = 0
  rw [quarticAnnihilatorSet_card]
  exact targetAmbient_coeff_zero_of_three_le hp
    ⟨quarticAnnihilatorSet k⟩ (by simp)

@[simp] theorem anfQuarticAnnihilatorProbe_affineANF
    (a : F₂) (ell : LinearForm) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (affineANF a ell) k = 0 := by
  apply anfQuarticAnnihilatorProbe_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_left (affineANF_mem a ell)

@[simp] theorem anfQuarticAnnihilatorProbe_targetANF
    (c : TargetCoeff) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (targetANF c) k = 0 := by
  apply anfQuarticAnnihilatorProbe_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_right (targetANF_mem_mulTarget c)

private theorem anfQuarticAnnihilatorProbe_one (k : Fin 9) :
    anfQuarticAnnihilatorProbe (1 : ANF 8) k = 0 := by
  apply anfQuarticAnnihilatorProbe_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_left (one_mem_affine 8)

private theorem anfQuarticAnnihilatorProbe_X (i : Fin 8) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (X i) k = 0 := by
  apply anfQuarticAnnihilatorProbe_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_left (X_mem_affine i)

private theorem anfQuarticAnnihilatorProbe_X_mul_X
    (i j : Fin 8) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (X i * X j) k = 0 := by
  rw [show X i * X j = monomial {i, j} by simp [X]]
  rw [anfQuarticAnnihilatorProbe_monomial]
  split
  · rename_i heq
    have hc := congrArg Finset.card heq
    have hle : ({i, j} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
    rw [quarticAnnihilatorSet_card] at hc
    omega
  · rfl

@[simp] theorem anfQuarticAnnihilatorProbe_affine_mul_affine
    (a b : F₂) (ell m : LinearForm) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (affineANF a ell * affineANF b m) k = 0 := by
  rw [affineANF, affineANF, linearANF, linearANF]
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  change anfQuarticAnnihilatorProbeLinear k _ = 0
  simp only [map_add, map_sum, map_smul, anfQuarticAnnihilatorProbeLinear_apply,
    anfQuarticAnnihilatorProbe_one, anfQuarticAnnihilatorProbe_X,
    anfQuarticAnnihilatorProbe_X_mul_X, smul_zero, add_zero, Finset.sum_const_zero]

private theorem anfQuarticAnnihilatorProbe_X_mul_targetPair
    (r : Fin 8) (i j : Fin 4) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (X r * monomial (targetPair i j)) k = 0 := by
  rw [X, monomial_mul, anfQuarticAnnihilatorProbe_monomial]
  split
  · rename_i heq
    have hc := congrArg Finset.card heq
    have hpair : (targetPair i j).card = 2 := by
      fin_cases i <;> fin_cases j <;> decide
    have hle : ({r} ∪ targetPair i j).card ≤ 3 := by
      calc
        ({r} ∪ targetPair i j).card ≤
            ({r} : Finset (Fin 8)).card + (targetPair i j).card :=
          Finset.card_union_le ({r} : Finset (Fin 8)) (targetPair i j)
        _ = 3 := by simp [hpair]
    rw [quarticAnnihilatorSet_card] at hc
    omega
  · rfl

private theorem anfQuarticAnnihilatorProbe_linear_mul_targetANF
    (ell : LinearForm) (c : TargetCoeff) (k : Fin 9) :
    anfQuarticAnnihilatorProbe (linearANF ell * targetANF c) k = 0 := by
  rw [linearANF, targetANF_eq_double_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  change anfQuarticAnnihilatorProbeLinear k _ = 0
  simp only [map_sum, map_smul, anfQuarticAnnihilatorProbeLinear_apply,
    anfQuarticAnnihilatorProbe_X_mul_targetPair, smul_zero, Finset.sum_const_zero]

@[simp] theorem anfQuarticAnnihilatorProbe_affine_mul_targetANF
    (a : F₂) (ell : LinearForm) (c : TargetCoeff) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (affineANF a ell * targetANF c) k = 0 := by
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, anfQuarticAnnihilatorProbe_add,
    anfQuarticAnnihilatorProbe_smul, anfQuarticAnnihilatorProbe_targetANF,
    anfQuarticAnnihilatorProbe_linear_mul_targetANF, smul_zero, add_zero]

@[simp] theorem anfQuarticAnnihilatorProbe_targetANF_mul_affine
    (c : TargetCoeff) (a : F₂) (ell : LinearForm) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (targetANF c * affineANF a ell) k = 0 := by
  rw [mul_comm]
  exact anfQuarticAnnihilatorProbe_affine_mul_targetANF a ell c k

@[simp] theorem anfQuarticAnnihilatorProbe_affine_mul_rationalANF
    (a : F₂) (ell : LinearForm) (delta : Fin 3 → F₂) (k : Fin 9) :
    anfQuarticAnnihilatorProbe
        (affineANF a ell * rationalANF delta) k = 0 := by
  exact anfQuarticAnnihilatorProbe_affine_mul_targetANF
    a ell (rationalCoeffRep delta) k

/-- Normal forms extracted from the right idempotence equation.  The target
coefficient is nonrational because `F` lies outside the rational-low state,
and its quartic product with the rational part of `c` vanishes. -/
theorem quartic_data_of_right_idempotence
    {F c : ANF 8}
    (hFAmbient : F ∈ targetAmbient 8 (mulTarget 4))
    (hFNotLow : F ∉ rationalLowSpace)
    (hcLow : c ∈ rationalLowSpace)
    (hFc : F * c = F) :
    ∃ (a b : F₂) (ell m : LinearForm)
        (C : TargetCoeff) (delta : Fin 3 → F₂),
      F = affineANF a ell + targetANF C ∧
      c = affineANF b m + rationalANF delta ∧
      ¬ IsRationalCoeff C ∧
      VanishesOnQuarticAnnihilatorProbe C delta := by
  rcases exists_targetAmbient_rep hFAmbient with ⟨u, C, hu, hFRep⟩
  rcases exists_affineANF_of_mem hu with ⟨a, ell, huRep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hcLow with
    ⟨b, m, delta, hcRep⟩
  have hFRep' : F = affineANF a ell + targetANF C := by
    rw [hFRep, huRep]
  have hCNotRational : ¬ IsRationalCoeff C := by
    intro hC
    rcases (IsRationalCoeff_iff C).mp hC with ⟨gamma, hgamma⟩
    apply hFNotLow
    rw [hFRep', hgamma]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left (affineANF_mem a ell)
    · apply Submodule.mem_sup_right
      exact (mem_rationalTargetSpace_iff _).mpr ⟨gamma, rfl⟩
  have hprobe : VanishesOnQuarticAnnihilatorProbe C delta := by
    intro k
    have h := congrArg
      (fun p : ANF 8 => anfQuarticAnnihilatorProbe p k) hFc
    rw [hFRep', hcRep] at h
    simp only [add_mul, mul_add, anfQuarticAnnihilatorProbe_add,
      anfQuarticAnnihilatorProbe_affine_mul_affine,
      anfQuarticAnnihilatorProbe_affine_mul_rationalANF,
      anfQuarticAnnihilatorProbe_targetANF_mul_affine,
      anfQuarticAnnihilatorProbe_target_mul_rational, anfQuarticAnnihilatorProbe_affineANF,
      anfQuarticAnnihilatorProbe_targetANF, zero_add] at h
    exact h
  exact ⟨a, b, ell, m, C, delta, hFRep', hcRep,
    hCNotRational, hprobe⟩

end

end N4
end UnrestrictedBooleanMul
