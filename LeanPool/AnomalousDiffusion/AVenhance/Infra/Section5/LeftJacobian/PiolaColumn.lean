/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-!: the Piola column lemma. For a constant matrix `P`, the matrix field
`κ I + F_kᵀ P` (with `F_k` the `l_k` flow gradient) has zero column divergence, so the
divergence of `(κ I + F_kᵀ P) V` is the Frobenius contraction with `∇V`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The transposed `l_k` flow gradient is the row cofactor of the inverse-flow Jacobian. -/
theorem flowGradK_transpose_eq_rowCofactor (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ)
    (t : ℝ) (y : Vec 2) :
    (flowGradK I hΦ m k t y).transpose =
      rowCofactor (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) :=
  (xFlowInv_rowCofactor_eq_flowGrad_transpose I hΦ m (lIdx β I.Λ m k) t y
    (streamVel_spatialDivergence_eq_zero I hΦ m)).symm

/-- The entries of `κ I + F_kᵀ P` are differentiable, with zero column divergence. -/
theorem piola_column_hasFDerivAt (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) (κm : ℝ) (x : Vec 2) :
    ∃ LA : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ,
      (∀ i j, HasFDerivAt (fun y => (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k t y).transpose * P) i j) (LA i j) x) ∧
      ∀ j, ∑ i : Fin 2, LA i j (basisVec i) = 0 := by
  obtain ⟨hQ, hdiv⟩ := xFlowInv_cofactor_piolaInputs I hΦ m (lIdx β I.Λ m k) t x
  set D : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ := fun i p => fderiv ℝ (fun y => rowCofactor
    (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i p) x with hD
  refine ⟨fun i j => ∑ p : Fin 2, (P p j) • D i p, ?_, ?_⟩
  · intro i j
    have hfun : (fun y => (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k t y).transpose * P) i j) =
        fun y => κm * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
          ∑ p : Fin 2, rowCofactor (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i p *
            P p j := by
      funext y
      rw [flowGradK_transpose_eq_rowCofactor]
      simp [Matrix.mul_apply]
    rw [hfun]
    refine HasFDerivAt.const_add _ ?_
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun p y => rowCofactor
      (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y) i p * P p j)
      (A' := fun p => (P p j) • D i p) (x := x)
      (fun p _ => (hQ i p).mul_const (P p j))
    exact hs
  · intro j
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro p _
    rw [← Finset.mul_sum]
    have := hdiv p
    simp only [hD]
    rw [this, mul_zero]

theorem matDiv_piola_column (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) (κm : ℝ) (x : Vec 2) :
    matDiv (fun y => κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (flowGradK I hΦ m k t y).transpose * P) x = 0 := by
  obtain ⟨LA, hA, hdiv⟩ := piola_column_hasFDerivAt I hΦ m k t P κm x
  funext j
  unfold matDiv
  have : ∀ i, spaceGrad (fun y => (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (flowGradK I hΦ m k t y).transpose * P) i j) x i = LA i j (basisVec i) := by
    intro i
    rw [spaceGrad, (hA i j).fderiv]
  simp only [this]
  exact hdiv j

/-- Divergence of `(κ I + F_kᵀ P) V` is the Frobenius contraction with `∇V`. -/
theorem vecDiv_piola_mulVec (hΦ : IsStreamSeq I Φ) (m : ℕ) (k : ℤ) (t : ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) (κm : ℝ) (V : Vec 2 → Vec 2) (x : Vec 2)
    (hV : DifferentiableAt ℝ V x) :
    vecDiv (fun y => (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (flowGradK I hΦ m k t y).transpose * P).mulVec (V y)) x =
      frob (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m k t x).transpose * P) (gradMatrix V x) := by
  obtain ⟨LA, hA, _⟩ := piola_column_hasFDerivAt I hΦ m k t P κm x
  have h := vecDiv_matrixMulVec_frob hA hV.hasFDerivAt
  rw [h, matDiv_piola_column]
  simp [vecDot]

end AVenhance.Infra.Section5.LeftJacobian

end
