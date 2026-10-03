/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.PDE.DirichletRHS

/-! # Energy Identities -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# PDE energy identities

This file collects coefficient-weighted energy densities and weak-solution
energy identities that are not specific to the Coarse Poincare recurrence.
-/

/-- The intrinsic coefficient energy density `F · symm(a) F`. -/
noncomputable def coefficientEnergyDensity {d : ℕ}
    (a : CoeffField d) (F : Vec d → Vec d) : Vec d → ℝ :=
  fun x => vecDot (F x) (matVecMul (symmPart (a x)) (F x))

theorem abs_le_half_add_half_of_sq_le_mul {u A B : ℝ}
    (hu_sq : u ^ 2 ≤ A * B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |u| ≤ A / 2 + B / 2 := by
  have habsSq : |u| ^ 2 ≤ A * B := by simpa [sq_abs] using hu_sq
  have hsumSq : (2 * |u|) ^ 2 ≤ (A + B) ^ 2 := by
    have h0 : 0 ≤ (A - B) ^ 2 := sq_nonneg _
    nlinarith [habsSq, h0]
  have hsum_nonneg : 0 ≤ A + B := add_nonneg hA hB
  have habs2u : 2 * |u| ≤ A + B := le_of_sq_le_sq hsumSq hsum_nonneg
  linarith

theorem abs_vecDot_matVecMul_symmPart_le_half_add_half_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ η : Vec d) :
    |vecDot ξ (matVecMul (symmPart A) η)| ≤
      vecDot ξ (matVecMul (symmPart A) ξ) / 2 +
        vecDot η (matVecMul (symmPart A) η) / 2 := by
  have hsq := sq_vecDot_matVecMul_symmPart_le_of_isEllipticMatrix hA ξ η
  have hξ_nonneg : 0 ≤ vecDot ξ (matVecMul (symmPart A) ξ) := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hA ξ
    have hnorm : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
    have hlam_pos : 0 < lam := hA.1
    nlinarith
  have hη_nonneg : 0 ≤ vecDot η (matVecMul (symmPart A) η) := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
    have hnorm : 0 ≤ vecNormSq η := vecNormSq_nonneg η
    have hlam_pos : 0 < lam := hA.1
    nlinarith
  exact abs_le_half_add_half_of_sq_le_mul hsq hξ_nonneg hη_nonneg

theorem vecDot_matVecMul_symmPart_sub_le_two_mul_add_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ η : Vec d) :
    vecDot (ξ - η) (matVecMul (symmPart A) (ξ - η)) ≤
      2 * (vecDot ξ (matVecMul (symmPart A) ξ) +
        vecDot η (matVecMul (symmPart A) η)) := by
  let S : Mat d := symmPart A
  have hsymm : S.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [S, symmPart]
    ring
  have hcomm : vecDot ξ (matVecMul S η) = vecDot η (matVecMul S ξ) :=
    vecDot_matVecMul_comm_of_isSymm hsymm ξ η
  have hquad :
      vecDot (ξ - η) (matVecMul S (ξ - η)) =
        vecDot ξ (matVecMul S ξ) - 2 * vecDot ξ (matVecMul S η) +
          vecDot η (matVecMul S η) := by
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
    simp [vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm]
    ring
  have hcross_abs :=
    abs_vecDot_matVecMul_symmPart_le_half_add_half_of_isEllipticMatrix hA ξ η
  have hcross :
      -2 * vecDot ξ (matVecMul S η) ≤
        vecDot ξ (matVecMul S ξ) + vecDot η (matVecMul S η) := by
    have hneg : -vecDot ξ (matVecMul S η) ≤ |vecDot ξ (matVecMul S η)| :=
      neg_le_abs _
    nlinarith [hcross_abs, hneg]
  rw [hquad]
  nlinarith

theorem coefficientEnergyDensity_eq_unsymmetrized {d : ℕ}
    (a : CoeffField d) (F : Vec d → Vec d) (x : Vec d) :
    coefficientEnergyDensity a F x =
      vecDot (F x) (matVecMul (a x) (F x)) := by
  unfold coefficientEnergyDensity
  rw [vecDot_matVecMul_symmPart]

namespace IsZeroTraceDirichletRhsWeakSolution

variable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
variable {u : H10Function U} {g : Vec d → Vec d}

/-- Zero-trace RHS weak solutions identify the intrinsic coefficient energy
with the forcing pairing after subtracting any constant vector. -/
theorem coefficientEnergy_identity_sub_const
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (h : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hmem : MemVectorL2 U g) (c : Vec d) :
    ∫ x in U,
        coefficientEnergyDensity a (fun x => u.toH1Function.grad x) x
          ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  calc
    ∫ x in U,
        coefficientEnergyDensity a (fun x => u.toH1Function.grad x) x
          ∂MeasureTheory.volume
        =
          ∫ x in U,
            vecDot (u.toH1Function.grad x)
              (matVecMul (a x) (u.toH1Function.grad x)) ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by
              simpa using
                coefficientEnergyDensity_eq_unsymmetrized a
                  (fun x => u.toH1Function.grad x) x
    _ =
      ∫ x in U, vecDot (g x - c) (u.toH1Function.grad x)
        ∂MeasureTheory.volume :=
      h.energy_identity_sub_const hmem c

end IsZeroTraceDirichletRhsWeakSolution

theorem coefficientEnergyDensity_nonneg_of_isEllipticFieldOn {d : ℕ}
    {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (F : Vec d → Vec d) :
    ∀ x ∈ U, 0 ≤ coefficientEnergyDensity a F x := by
  intro x hx
  unfold coefficientEnergyDensity
  have hlower := lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (F x)
  have hnorm : 0 ≤ vecNormSq (F x) := vecNormSq_nonneg (F x)
  have hlam_pos : 0 < lam := (hEll.2 x hx).1
  nlinarith

theorem integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn {d : ℕ}
    {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) :
    MeasureTheory.IntegrableOn (coefficientEnergyDensity a F) U := by
  unfold coefficientEnergyDensity
  exact integrableOn_vecDot_of_memVectorL2 hF
    (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hF)

theorem coefficientEnergyDensity_sub_le_two_mul_add_of_isEllipticFieldOn
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (F G : Vec d → Vec d) :
    ∀ x ∈ U,
      coefficientEnergyDensity a (fun y => F y - G y) x ≤
        2 * (coefficientEnergyDensity a F x + coefficientEnergyDensity a G x) := by
  intro x hx
  exact vecDot_matVecMul_symmPart_sub_le_two_mul_add_of_isEllipticMatrix
    (hEll.2 x hx) (F x) (G x)

end

end Homogenization
