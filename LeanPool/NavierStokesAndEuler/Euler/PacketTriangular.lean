/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPointJets
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeTriangular

@[expose] public section

/-! The actual nonlinear packet operators have the triangular dependence claimed in (14). -/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades InnerProductSpace

theorem fastAdvection_tangent_left (m : Space) (J K : VectorJet)
    (hJ : ⟪m, J.1⟫_ℝ=0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hJ]

theorem fastAdvection_angleConstant_right (m : Space) (J K : VectorJet)
    (hK : K.2 angleDirection=0) : fastAdvection m J K=0 := by
  simp [fastAdvection, hK]

def nonlinearGrade (M p : ℕ) (FInv : Space →L[ℝ] Space) (m : Space)
    (u : ℕ → VectorJet) : Space :=
  convolution M (slowAdvection FInv) u u p + convolution M (fastAdvection m) u u (p+1)

/-- Changing the new high coefficient and mean coefficient leaves just the mean-primary interaction. -/
theorem nonlinearGrade_update (M p : ℕ) (hp : 2 ≤ p) (hMp : p+1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u u' : ℕ → VectorJet)
    (A B : VectorJet) (hu0 : u 0=0) (hu : ∀ i < p, u' i=u i)
    (hnew : u' p=u p+(A+B)) (hprimary : ⟪m, (u 1).1⟫_ℝ=0)
    (hA : ⟪m, A.1⟫_ℝ=0) :
    nonlinearGrade M p FInv m u' = nonlinearGrade M p FInv m u + fastAdvection m B (u 1) := by
  unfold nonlinearGrade
  rw [convolution_strict_congr M p (by omega) (by omega) _ u u' hu0 hu,
    convolution_next_delta M p hp hMp _ u u' (A+B) hu0 hu hnew]
  rw [map_add, LinearMap.add_apply,
    fastAdvection_tangent_left m A (u 1) hA,
    fastAdvection_tangent_left m (u 1) (A+B) hprimary]
  simp only [zero_add, add_zero, add_assoc]

/-- The surviving unknown term is literally (m dot B) times the primary angular derivative. -/
theorem nonlinearGrade_update_formula (M p : ℕ) (hp : 2 ≤ p) (hMp : p+1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u u' : ℕ → VectorJet)
    (A B : VectorJet) (hu0 : u 0=0) (hu : ∀ i < p, u' i=u i)
    (hnew : u' p=u p+(A+B)) (hprimary : ⟪m, (u 1).1⟫_ℝ=0)
    (hA : ⟪m, A.1⟫_ℝ=0) :
    nonlinearGrade M p FInv m u' = nonlinearGrade M p FInv m u +
      ⟪m, B.1⟫_ℝ • (u 1).2 angleDirection :=
  nonlinearGrade_update M p hp hMp FInv m u u' A B hu0 hu hnew hprimary hA

end EulerPacketPointJets
