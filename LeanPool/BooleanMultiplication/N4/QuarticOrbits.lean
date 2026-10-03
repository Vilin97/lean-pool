/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicDirect

/-!
# The three rational quartic-plane orbits

This file finishes the coordinate part of the low--low quartic exclusion.
The only finite certificate is the left inverse in `CubicDirect`; the orbit
arguments below are ordinary exterior algebra and coordinate extensionality.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Select evaluation at infinity among the three rational-place coordinates. -/
def infinityPlaceCoeff3 : Fin 3 → F₂ := ![0, 0, 1]

/-- The sum of the evaluation-at-one and evaluation-at-infinity coordinates. -/
def oneInfinityCoeff3 : Fin 3 → F₂ :=
  onePlaceCoeff3 + infinityPlaceCoeff3

/-- The sum of the evaluation-at-zero and evaluation-at-one coordinates. -/
def zeroOneCoeff3 : Fin 3 → F₂ :=
  zeroPlaceCoeff3 + onePlaceCoeff3

/-- The sum of the evaluation-at-zero and evaluation-at-infinity coordinates. -/
def zeroInfinityCoeff3 : Fin 3 → F₂ :=
  zeroPlaceCoeff3 + infinityPlaceCoeff3

@[simp] theorem rationalTwo_infinityPlaceCoeff3 :
    rationalTwo infinityPlaceCoeff3 = rationalPlaceTwo 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [infinityPlaceCoeff3, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ]

@[simp] theorem rationalTwo_oneInfinityCoeff3 :
    rationalTwo oneInfinityCoeff3 =
      rationalPlaceTwo 1 + rationalPlaceTwo 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneInfinityCoeff3, onePlaceCoeff3, infinityPlaceCoeff3, rationalTwo,
      rationalPlaceTwo, vectorWedge, placeA, placeB, Fin.sum_univ_succ]

@[simp] theorem rationalTwo_zeroOneCoeff3 :
    rationalTwo zeroOneCoeff3 =
      rationalPlaceTwo 0 + rationalPlaceTwo 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroOneCoeff3, zeroPlaceCoeff3, onePlaceCoeff3, rationalTwo, rationalPlaceTwo,
      vectorWedge, placeA, placeB, Fin.sum_univ_succ]

@[simp] theorem rationalTwo_zeroInfinityCoeff3 :
    rationalTwo zeroInfinityCoeff3 =
      rationalPlaceTwo 0 + rationalPlaceTwo 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroInfinityCoeff3, zeroPlaceCoeff3, infinityPlaceCoeff3, rationalTwo,
      rationalPlaceTwo, vectorWedge, placeA, placeB, Fin.sum_univ_succ]

private def orbitBInput (x y : LinearForm) : Fin 3 → LinearForm :=
  ![y, x, x]

private def orbitCInput (x y : LinearForm) : Fin 3 → LinearForm :=
  ![x + y, y, x]

private theorem orbitB_direct_sum (x y : LinearForm)
    (h : vectorWedgeTwo x
          (rationalPlaceTwo 1 + rationalPlaceTwo 2) +
        vectorWedgeTwo y (rationalPlaceTwo 0) = 0) :
    rationalCubicDirectSum (orbitBInput x y) = 0 := by
  funext i j k
  have hc := congrFun (congrFun (congrFun h i) j) k
  simp [rationalCubicDirectSum, cubicPlaceLinear, orbitBInput, Fin.sum_univ_succ,
    vectorWedgeTwo_add_right_h] at hc ⊢
  linear_combination hc

private theorem orbitC_direct_sum (x y : LinearForm)
    (h : vectorWedgeTwo x
          (rationalPlaceTwo 0 + rationalPlaceTwo 2) +
        vectorWedgeTwo y
          (rationalPlaceTwo 0 + rationalPlaceTwo 1) = 0) :
    rationalCubicDirectSum (orbitCInput x y) = 0 := by
  funext i j k
  have hc := congrFun (congrFun (congrFun h i) j) k
  simp [rationalCubicDirectSum, cubicPlaceLinear, orbitCInput, Fin.sum_univ_succ,
    vectorWedgeTwo_add_left, vectorWedgeTwo_add_right_h] at hc ⊢
  linear_combination hc

/-- Orbit `span(r₀,r₁+r∞)`: the coefficient of the second generator
vanishes, and the remaining coefficient lies in `P₀`. -/
theorem quartic_cubic_kernel_zero_oneInfinity (x y : LinearForm)
    (h : vectorWedgeTwo x
          (rationalPlaceTwo 1 + rationalPlaceTwo 2) +
        vectorWedgeTwo y (rationalPlaceTwo 0) = 0) :
    x = 0 ∧ ∃ c d : F₂, y = quarticPzeroVector c d := by
  have hd := rationalCubicDirectSum_kernel (orbitBInput x y)
    (orbitB_direct_sum x y h)
  rcases hd 0 with ⟨c, d, hy⟩
  rcases hd 1 with ⟨a, b, hxOne⟩
  rcases hd 2 with ⟨e, f, hxInf⟩
  change y = c • placeA 0 + d • placeB 0 at hy
  change x = a • placeA 1 + b • placeB 1 at hxOne
  change x = e • placeA 2 + f • placeB 2 at hxInf
  have ha : a = 0 := by
    have hc := congrFun (hxOne.symm.trans hxInf) 0
    simpa [orbitBInput, placeA, placeB] using hc
  have hb : b = 0 := by
    have hc := congrFun (hxOne.symm.trans hxInf) 4
    simpa [orbitBInput, placeA, placeB] using hc
  have hx : x = 0 := by
    rw [hxOne, ha, hb]
    simp
  refine ⟨hx, c, d, ?_⟩
  simpa [orbitBInput, quarticPzeroVector] using hy

/-- Orbit `span(r₀+r₁,r₀+r∞)`: cubic cancellation kills both linear
differences. -/
theorem quartic_cubic_kernel_zeroOne_zeroInfinity (x y : LinearForm)
    (h : vectorWedgeTwo x
          (rationalPlaceTwo 0 + rationalPlaceTwo 2) +
        vectorWedgeTwo y
          (rationalPlaceTwo 0 + rationalPlaceTwo 1) = 0) :
    x = 0 ∧ y = 0 := by
  have hd := rationalCubicDirectSum_kernel (orbitCInput x y)
    (orbitC_direct_sum x y h)
  rcases hd 0 with ⟨c, d, hxyZero⟩
  rcases hd 1 with ⟨a, b, hyOne⟩
  rcases hd 2 with ⟨e, f, hxInf⟩
  change x + y = c • placeA 0 + d • placeB 0 at hxyZero
  change y = a • placeA 1 + b • placeB 1 at hyOne
  change x = e • placeA 2 + f • placeB 2 at hxInf
  have ha : a = 0 := by
    have hc := congrFun hxyZero 1
    have hyc := congrFun hyOne 1
    have hxc := congrFun hxInf 1
    simp only [Fin.isValue, Pi.add_apply, placeA, Matrix.cons_val_zero, Matrix.smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, placeB, Matrix.cons_val_one,
      add_zero, Matrix.cons_val] at hc hyc hxc
    rw [hxc, zero_add] at hc
    exact hyc.symm.trans hc
  have hb : b = 0 := by
    have hc := congrFun hxyZero 5
    have hyc := congrFun hyOne 5
    have hxc := congrFun hxInf 5
    simp only [Fin.isValue, Pi.add_apply, placeA, Matrix.cons_val_zero, Matrix.smul_cons,
      smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, placeB, Matrix.cons_val, add_zero,
      Matrix.cons_val_one, zero_add] at hc hyc hxc
    rw [hxc, zero_add] at hc
    exact hyc.symm.trans hc
  have hy : y = 0 := by
    rw [hyOne, ha, hb]
    simp
  have hxZero : x = c • placeA 0 + d • placeB 0 := by
    simpa [orbitCInput, hy] using hxyZero
  have hc : c = 0 := by
    have hz := congrFun (hxZero.symm.trans hxInf) 0
    simpa [orbitCInput, placeA, placeB] using hz
  have hd' : d = 0 := by
    have hz := congrFun (hxZero.symm.trans hxInf) 4
    simpa [orbitCInput, placeA, placeB] using hz
  have hx : x = 0 := by
    rw [hxZero, hc, hd']
    simp
  exact ⟨hx, hy⟩

theorem rationalProductCubic_equal_kernel
    (ell₀ m₀ ell₁ m₁ : LinearForm) (α β : Fin 3 → F₂)
    (h : rationalProductCubic ell₀ m₀ α β =
      rationalProductCubic ell₁ m₁ α β) :
    vectorWedgeTwo (ell₀ + ell₁) (rationalTwo β) +
      vectorWedgeTwo (m₀ + m₁) (rationalTwo α) = 0 := by
  rw [vectorWedgeTwo_add_left, vectorWedgeTwo_add_left]
  have hsum :
      rationalProductCubic ell₀ m₀ α β +
        rationalProductCubic ell₁ m₁ α β = 0 := by
    rw [h]
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  calc
    (vectorWedgeTwo ell₀ (rationalTwo β) +
        vectorWedgeTwo ell₁ (rationalTwo β)) +
        (vectorWedgeTwo m₀ (rationalTwo α) +
          vectorWedgeTwo m₁ (rationalTwo α)) =
      (vectorWedgeTwo ell₀ (rationalTwo β) +
        vectorWedgeTwo m₀ (rationalTwo α)) +
        (vectorWedgeTwo ell₁ (rationalTwo β) +
          vectorWedgeTwo m₁ (rationalTwo α)) := by ac_rfl
    _ = 0 := by simpa [rationalProductCubic] using hsum

/-- Shared quadratic-shadow argument for the three low--low quartic
orbits.  Its hypotheses are exactly the output of the cubic direct-sum
calculation: the two linear differences lie in `P₁` and `P₀`, and their
cubic contractions vanish. -/
theorem aligned_lowLow_target_is_rational_of_kernel
    (α β : Fin 3 → F₂)
    (a₀ b₀ a₁ b₁ ax bx ay dy : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hx : ell₀ + ell₁ = quarticPoneVector ax bx)
    (hy : m₀ + m₁ = quarticPzeroVector ay dy)
    (hxw : vectorWedgeTwo (ell₀ + ell₁) (rationalTwo β) = 0)
    (hyw : vectorWedgeTwo (m₀ + m₁) (rationalTwo α) = 0)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀ α β +
        rationalProductQuadratic a₁ b₁ ell₁ m₁ α β) :
    IsRationalCoeff t := by
  let x : LinearForm := ell₀ + ell₁
  let y : LinearForm := m₀ + m₁
  let rho : TwoForm :=
    a₀ • rationalTwo β + b₀ • rationalTwo α +
    a₁ • rationalTwo β + b₁ • rationalTwo α +
    booleanContraction x (rationalTwo β) +
    booleanContraction y (rationalTwo α)
  have hrho : rho ∈ rationalPlaceTwoSpace := by
    dsimp only [rho]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.add_mem _
            (Submodule.add_mem _
              (Submodule.smul_mem _ _ (rationalTwo_mem β))
              (Submodule.smul_mem _ _ (rationalTwo_mem α)))
            (Submodule.smul_mem _ _ (rationalTwo_mem β)))
          (Submodule.smul_mem _ _ (rationalTwo_mem α)))
        (by
          apply rational_contraction_mem_of_cubic_zero β x
          simpa [x] using hxw))
      (by
        apply rational_contraction_mem_of_cubic_zero α y
        simpa [y] using hyw)
  rcases exists_rationalTwo_of_mem hrho with ⟨gamma, hgamma⟩
  apply target_eq_rational_add_pone_pzero_is_rational
    t gamma ax bx ay dy m₀ ell₁
  rw [← hgamma, hquadratic]
  rw [← hx, ← hy]
  funext i j
  simp only [rho, x, y, rationalProductQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    booleanContraction, vectorWedge, twoHadamard]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- Low--low quartic collision for the orbit
`span(r₀,r₁+r∞)`. -/
theorem aligned_zero_oneInfinity_lowLow_target_is_rational
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hcubic :
      rationalProductCubic ell₀ m₀ zeroPlaceCoeff3 oneInfinityCoeff3 =
        rationalProductCubic ell₁ m₁ zeroPlaceCoeff3 oneInfinityCoeff3)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀
          zeroPlaceCoeff3 oneInfinityCoeff3 +
        rationalProductQuadratic a₁ b₁ ell₁ m₁
          zeroPlaceCoeff3 oneInfinityCoeff3) :
    IsRationalCoeff t := by
  have hk := rationalProductCubic_equal_kernel ell₀ m₀ ell₁ m₁
    zeroPlaceCoeff3 oneInfinityCoeff3 hcubic
  simp only [rationalTwo_zeroPlaceCoeff3, rationalTwo_oneInfinityCoeff3] at hk
  rcases quartic_cubic_kernel_zero_oneInfinity
      (ell₀ + ell₁) (m₀ + m₁) hk with ⟨hx, ay, dy, hy⟩
  apply aligned_lowLow_target_is_rational_of_kernel
    zeroPlaceCoeff3 oneInfinityCoeff3 a₀ b₀ a₁ b₁ 0 0 ay dy
    ell₀ m₀ ell₁ m₁ t
  · simp [hx, quarticPoneVector]
  · exact hy
  · rw [hx]
    exact vectorWedgeTwo_zero_left _
  · rw [hy]
    simp only [quarticPzeroVector, rationalTwo_zeroPlaceCoeff3, rationalPlaceTwo,
      vectorWedgeTwo_add_left, vectorWedgeTwo_smul_left, vectorWedgeTwo_repeated_left,
      vectorWedgeTwo_repeated_right, smul_zero, add_zero]
  · exact hquadratic

/-- Low--low quartic collision for the orbit
`span(r₀+r₁,r₀+r∞)`. -/
theorem aligned_zeroOne_zeroInfinity_lowLow_target_is_rational
    (a₀ b₀ a₁ b₁ : F₂)
    (ell₀ m₀ ell₁ m₁ : LinearForm)
    (t : TargetCoeff)
    (hcubic :
      rationalProductCubic ell₀ m₀ zeroOneCoeff3 zeroInfinityCoeff3 =
        rationalProductCubic ell₁ m₁ zeroOneCoeff3 zeroInfinityCoeff3)
    (hquadratic : targetTwo t =
      rationalProductQuadratic a₀ b₀ ell₀ m₀
          zeroOneCoeff3 zeroInfinityCoeff3 +
        rationalProductQuadratic a₁ b₁ ell₁ m₁
          zeroOneCoeff3 zeroInfinityCoeff3) :
    IsRationalCoeff t := by
  have hk := rationalProductCubic_equal_kernel ell₀ m₀ ell₁ m₁
    zeroOneCoeff3 zeroInfinityCoeff3 hcubic
  simp only [rationalTwo_zeroOneCoeff3, rationalTwo_zeroInfinityCoeff3] at hk
  rcases quartic_cubic_kernel_zeroOne_zeroInfinity
      (ell₀ + ell₁) (m₀ + m₁) hk with ⟨hx, hy⟩
  apply aligned_lowLow_target_is_rational_of_kernel
    zeroOneCoeff3 zeroInfinityCoeff3 a₀ b₀ a₁ b₁ 0 0 0 0
    ell₀ m₀ ell₁ m₁ t
  · simp [hx, quarticPoneVector]
  · simp [hy, quarticPzeroVector]
  · rw [hx]
    exact vectorWedgeTwo_zero_left _
  · rw [hy]
    exact vectorWedgeTwo_zero_left _
  · exact hquadratic

end

end N4
end UnrestrictedBooleanMul
