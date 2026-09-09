/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTriangular
public import LeanPool.NavierStokesAndEuler.Euler.PeriodicDerivativeMean

@[expose] public section

/-! The known forcing at a recursive grade uses only previously constructed coefficients. -/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerFiniteGrades InnerProductSpace

def history (p : ℕ) (u : ℕ → VectorJet) (previousCorrector : VectorJet) (i : ℕ) : VectorJet :=
  if i<p then u i else if i=p then previousCorrector else 0

/-- No unspecified coefficient at or above p enters the known part. -/
theorem history_congr (p : ℕ) (u v : ℕ → VectorJet) (c : VectorJet)
    (huv : ∀ i<p, u i=v i) : history p u c=history p v c := by
  funext i
  by_cases hi : i<p
  · simp only [history, hi, ite_true, huv i hi]
  · simp only [history, hi, ite_false]

/-- The only new nonlinear term is the mean coefficient against the primary angular derivative. -/
theorem nonlinearGrade_eq_history (M p : ℕ) (hp : 2 ≤ p) (hMp : p+1 ≤ M)
    (FInv : Space →L[ℝ] Space) (m : Space) (u : ℕ → VectorJet)
    (A B c : VectorJet) (hu0 : u 0=0) (hnew : u p=c+(A+B))
    (hprimary : ⟪m,(u 1).1⟫_ℝ=0) (hA : ⟪m,A.1⟫_ℝ=0) :
    nonlinearGrade M p FInv m u = nonlinearGrade M p FInv m (history p u c)+
      fastAdvection m B (u 1) := by
  have h0 : history p u c 0=0 := by simp [history, show 0<p by omega, hu0]
  have h1 : history p u c 1=u 1 := by simp [history, show 1<p by omega]
  have hsame : ∀ i<p, u i=history p u c i := by
    intro i hi
    simp [history, hi]
  have hnew' : u p=history p u c p+(A+B) := by simpa [history] using hnew
  simpa only [h1] using nonlinearGrade_update M p hp hMp FInv m (history p u c) u A B
    h0 hsame hnew' (by simpa only [h1] using hprimary) hA

/-- The unknown mean-primary interaction has exactly zero angular mean. -/
theorem mean_primary_interaction_zero (P : ℝ) (m B : Space) (A Aθ : ℝ → Space)
    (hA : ∀ θ, HasDerivAt A (Aθ θ) θ) (hAθ : Continuous Aθ)
    (hper : Function.Periodic A P) :
    (∫ θ in 0..P, ⟪m,B⟫_ℝ • Aθ θ)=0 :=
  EulerPeriodicDerivativeMean.integral_constant_smul_derivative_eq_zero P ⟪m,B⟫_ℝ
    A Aθ hA hAθ hper

end EulerPacketPointJets
