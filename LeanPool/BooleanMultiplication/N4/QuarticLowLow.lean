/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticAllPairs

/-!
# Orbit-free low--low quartic exclusion

For independent rational coefficient words `α, β`, choose a nonzero
`2 × 2` minor.  The corresponding two direct cubic components reconstruct
the two linear differences.  Their quadratic wedge shadow therefore lies in
one of the three support-pair spaces certified in `QuarticAllPairs`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A two-by-two minor of two rational coefficient vectors. -/
@[expose] def rationalCoeffMinor (α β : Fin 3 → F₂) (i j : Fin 3) : F₂ :=
  α i * β j + α j * β i

@[simp] theorem f2_mul_self_quartic (u : F₂) : u * u = u := by
  rcases f2_eq_zero_or_one u with rfl | rfl <;> simp

theorem exists_supportPair_minor_one (α β : Fin 3 → F₂)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    ∃ pair : Fin 3,
      rationalCoeffMinor α β (quarticSupportPair pair).1
        (quarticSupportPair pair).2 = 1 := by
  revert α β
  decide +kernel

theorem rational_coeff_independent_of_wedge_ne_zero
    (α β : Fin 3 → F₂)
    (h : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0) :
    α ≠ 0 ∧ β ≠ 0 ∧ α ≠ β := by
  refine ⟨?_, ?_, ?_⟩
  · intro hα
    apply h
    rw [hα, rationalTwo_zero]
    funext i j k l
    simp [wedgeTwo]
  · intro hβ
    apply h
    rw [hβ, rationalTwo_zero]
    funext i j k l
    simp [wedgeTwo]
  · intro hαβ
    apply h
    rw [hαβ, wedgeTwo_self]

/-- The placewise linear inputs expressing a cubic difference as a direct sum. -/
def cubicDifferenceInput (α β : Fin 3 → F₂)
    (x y : LinearForm) : Fin 3 → LinearForm :=
  fun theta => β theta • x + α theta • y

theorem cubicDifference_directSum
    (α β : Fin 3 → F₂) (x y : LinearForm) :
    rationalCubicDirectSum (cubicDifferenceInput α β x y) =
      vectorWedgeTwo x (rationalTwo β) +
        vectorWedgeTwo y (rationalTwo α) := by
  funext i j k
  simp [rationalCubicDirectSum, cubicPlaceLinear, cubicDifferenceInput, rationalTwo,
    Fin.sum_univ_succ, vectorWedgeTwo_add_left, vectorWedgeTwo_smul_left,
    vectorWedgeTwo_add_right_h, vectorWedgeTwo_smul_right_h]
  ring

theorem reconstruct_first_from_minor
    (α β : Fin 3 → F₂) (x y : LinearForm) (i j : Fin 3)
    (hminor : rationalCoeffMinor α β i j = 1) :
    x = α j • cubicDifferenceInput α β x y i +
      α i • cubicDifferenceInput α β x y j := by
  funext k
  have hm := hminor
  simp only [rationalCoeffMinor] at hm
  simp only [cubicDifferenceInput, smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← one_mul (x k), ← hm]
  ring_nf
  simp [pow_two, f2_mul_self_quartic, N3Certificate.two_eq_zero_f2]

theorem reconstruct_second_from_minor
    (α β : Fin 3 → F₂) (x y : LinearForm) (i j : Fin 3)
    (hminor : rationalCoeffMinor α β i j = 1) :
    y = β j • cubicDifferenceInput α β x y i +
      β i • cubicDifferenceInput α β x y j := by
  funext k
  have hm := hminor
  simp only [rationalCoeffMinor] at hm
  simp only [cubicDifferenceInput, smul_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← one_mul (y k), ← hm]
  ring_nf
  simp [pow_two, f2_mul_self_quartic, N3Certificate.two_eq_zero_f2]

/-- A rational-place coefficient vector supported at one place. -/
def singlePlaceCoeff3 (theta : Fin 3) : Fin 3 → F₂ :=
  fun phi => if phi = theta then 1 else 0

@[simp] theorem rationalTwo_singlePlaceCoeff3 (theta : Fin 3) :
    rationalTwo (singlePlaceCoeff3 theta) = rationalPlaceTwo theta := by
  funext i j
  fin_cases theta <;> fin_cases i <;> fin_cases j <;>
    simp [singlePlaceCoeff3, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ]

theorem cubicDifference_contraction_sum
    (α β : Fin 3 → F₂) (x y : LinearForm) :
    booleanContraction x (rationalTwo β) +
        booleanContraction y (rationalTwo α) =
      ∑ theta : Fin 3,
        booleanContraction (cubicDifferenceInput α β x y theta)
          (rationalPlaceTwo theta) := by
  funext i j
  simp [booleanContraction, cubicDifferenceInput, rationalTwo, Fin.sum_univ_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem cubicDifference_contraction_mem
    (α β : Fin 3 → F₂) (x y : LinearForm)
    (hkernel : rationalCubicDirectSum
      (cubicDifferenceInput α β x y) = 0) :
    booleanContraction x (rationalTwo β) +
        booleanContraction y (rationalTwo α) ∈ rationalPlaceTwoSpace := by
  have hd := rationalCubicDirectSum_kernel
    (cubicDifferenceInput α β x y) hkernel
  rw [cubicDifference_contraction_sum]
  apply Submodule.sum_mem
  intro theta _
  rcases hd theta with ⟨a, b, htheta⟩
  rw [← rationalTwo_singlePlaceCoeff3 theta]
  apply rational_contraction_mem_of_cubic_zero
    (singlePlaceCoeff3 theta) (cubicDifferenceInput α β x y theta)
  rw [rationalTwo_singlePlaceCoeff3, htheta]
  simp only [rationalPlaceTwo, vectorWedgeTwo_add_left, vectorWedgeTwo_smul_left,
    vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right, smul_zero, add_zero]

private theorem rationalProductCubic_equal_kernel_general
    (ell₀ m₀ ell₁ m₁ : LinearForm) (α β : Fin 3 → F₂)
    (h : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ α β) :
    rationalCubicDirectSum
        (cubicDifferenceInput α β (ell₀ + ell₁) (m₀ + m₁)) = 0 := by
  rw [cubicDifference_directSum]
  exact rationalProductCubic_equal_kernel ell₀ m₀ ell₁ m₁ α β h

/-- The complete aligned low--low quartic collision theorem, with no orbit
case split. -/
theorem aligned_lowLow_quartic_target_is_rational
    (α β : Fin 3 → F₂)
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0)
    (hcubic : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ α β)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β) :
    IsRationalCoeff t := by
  let x : LinearForm := ell₀ + ell₁
  let y : LinearForm := m₀ + m₁
  let M : Fin 3 → LinearForm := cubicDifferenceInput α β x y
  have hkernel : rationalCubicDirectSum M = 0 := by
    exact rationalProductCubic_equal_kernel_general
      ell₀ m₀ ell₁ m₁ α β hcubic
  have hind := rational_coeff_independent_of_wedge_ne_zero α β hquartic
  rcases exists_supportPair_minor_one α β hind.1 hind.2.1 hind.2.2 with
    ⟨pair, hminor⟩
  let theta : Fin 3 := (quarticSupportPair pair).1
  let phi : Fin 3 := (quarticSupportPair pair).2
  have hminor' : rationalCoeffMinor α β theta phi = 1 := hminor
  have hd := rationalCubicDirectSum_kernel M hkernel
  rcases hd theta with ⟨a, b, htheta⟩
  rcases hd phi with ⟨c, d, hphi⟩
  have htheta' : M theta = quarticSupportVector theta a b := by
    simpa [quarticSupportVector] using htheta
  have hphi' : M phi = quarticSupportVector phi c d := by
    simpa [quarticSupportVector] using hphi
  have hx : x = α phi • M theta + α theta • M phi := by
    exact reconstruct_first_from_minor α β x y theta phi hminor'
  have hy : y = β phi • M theta + β theta • M phi := by
    exact reconstruct_second_from_minor α β x y theta phi hminor'
  have hwedge :
      vectorWedge (M theta) (α phi • m₀ + β phi • ell₁) +
        vectorWedge (M phi) (α theta • m₀ + β theta • ell₁) =
      vectorWedge x m₀ + vectorWedge ell₁ y := by
    rw [hx, hy]
    funext i j
    simp only [vectorWedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hwedgePair :
      vectorWedge (M (quarticSupportPair pair).1)
          (α (quarticSupportPair pair).2 • m₀ +
            β (quarticSupportPair pair).2 • ell₁) +
        vectorWedge (M (quarticSupportPair pair).2)
          (α (quarticSupportPair pair).1 • m₀ +
            β (quarticSupportPair pair).1 • ell₁) =
      vectorWedge x m₀ + vectorWedge ell₁ y := by
    simpa [theta, phi] using hwedge
  let rho : TwoForm :=
    a₀ • rationalTwo β + b₀ • rationalTwo α +
    a₁ • rationalTwo β + b₁ • rationalTwo α +
    booleanContraction x (rationalTwo β) +
    booleanContraction y (rationalTwo α)
  have hrho : rho ∈ rationalPlaceTwoSpace := by
    rw [show rho =
      (a₀ • rationalTwo β + b₀ • rationalTwo α +
        a₁ • rationalTwo β + b₁ • rationalTwo α) +
      (booleanContraction x (rationalTwo β) +
        booleanContraction y (rationalTwo α)) by
          dsimp only [rho]
          module]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _
            (Submodule.smul_mem _ _ (rationalTwo_mem β))
            (Submodule.smul_mem _ _ (rationalTwo_mem α)))
          (Submodule.smul_mem _ _ (rationalTwo_mem β)))
        (Submodule.smul_mem _ _ (rationalTwo_mem α)))
      (cubicDifference_contraction_mem α β x y hkernel)
  rcases exists_rationalTwo_of_mem hrho with ⟨gamma, hgamma⟩
  apply target_eq_rational_add_supportPair_is_rational
    t gamma pair a b c d
    (α phi • m₀ + β phi • ell₁)
    (α theta • m₀ + β theta • ell₁)
  rw [← hgamma, hquadratic]
  rw [← htheta', ← hphi']
  rw [show theta = (quarticSupportPair pair).1 by rfl,
    show phi = (quarticSupportPair pair).2 by rfl]
  rw [show
    rho +
        vectorWedge (M (quarticSupportPair pair).1)
          (α (quarticSupportPair pair).2 • m₀ +
            β (quarticSupportPair pair).2 • ell₁) +
        vectorWedge (M (quarticSupportPair pair).2)
          (α (quarticSupportPair pair).1 • m₀ +
            β (quarticSupportPair pair).1 • ell₁) =
      rho +
        (vectorWedge (M (quarticSupportPair pair).1)
            (α (quarticSupportPair pair).2 • m₀ +
              β (quarticSupportPair pair).2 • ell₁) +
          vectorWedge (M (quarticSupportPair pair).2)
            (α (quarticSupportPair pair).1 • m₀ +
              β (quarticSupportPair pair).1 • ell₁)) by module]
  rw [hwedgePair]
  funext i j
  simp only [rho, x, y, rationalProductQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    booleanContraction, vectorWedge, twoHadamard]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- A rational quadratic offset does not affect the aligned collision
conclusion. -/
theorem aligned_lowLow_quartic_target_is_rational_add_rational
    (α β eta : Fin 3 → F₂)
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hquartic : wedgeTwo (rationalTwo α) (rationalTwo β) ≠ 0)
    (hcubic : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ α β)
    (hquadratic : targetTwo t = rationalTwo eta +
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β) :
    IsRationalCoeff t := by
  let delta : TargetCoeff := t + rationalCoeffRep eta
  have hdelta : targetTwo delta =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β := by
    rw [show targetTwo delta = targetTwo t +
      targetTwo (rationalCoeffRep eta) by
        exact targetTwoLinear.map_add _ _]
    rw [targetTwo_rationalCoeffRep, hquadratic]
    funext i j
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hrat := aligned_lowLow_quartic_target_is_rational
    α β a₀ b₀ a₁ b₁ ell₀ m₀ ell₁ m₁ delta
    hquartic hcubic hdelta
  rcases (IsRationalCoeff_iff delta).mp hrat with ⟨mu, hmu⟩
  apply (IsRationalCoeff_iff t).mpr
  refine ⟨mu + eta, ?_⟩
  rw [rationalCoeffRep_add, ← hmu]
  dsimp [delta]
  funext i
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

end

end N4
end UnrestrictedBooleanMul
