/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain

/-! Product-rule lemmas for the transport identity of the finite cutoff ansatz. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- Derivative of the vector pairing along a curve. -/
theorem hasDerivAt_vecDot
    {χ G : ℝ → Vec 2} {χ' G' : Vec 2} {t : ℝ}
    (hχ : HasDerivAt χ χ' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun s => vecDot (χ s) (G s))
      (vecDot χ' (G t) + vecDot (χ t) G') t := by
  have hχ0 : HasDerivAt (fun s => χ s 0) (χ' 0) t :=
    (hasDerivAt_pi.mp hχ) 0
  have hχ1 : HasDerivAt (fun s => χ s 1) (χ' 1) t :=
    (hasDerivAt_pi.mp hχ) 1
  have hG0 : HasDerivAt (fun s => G s 0) (G' 0) t :=
    (hasDerivAt_pi.mp hG) 0
  have hG1 : HasDerivAt (fun s => G s 1) (G' 1) t :=
    (hasDerivAt_pi.mp hG) 1
  have hsum := (hχ0.mul hG0).add (hχ1.mul hG1)
  convert hsum using 1
  · funext s
    simp [vecDot, Fin.sum_univ_two]
  · simp [vecDot, Fin.sum_univ_two]
    ring

/-- Derivative of a finite cutoff ansatz along any differentiable curve. The
two summands inside each product are kept separate, matching `e.timecomp.0`.
-/
theorem hasDerivAt_finiteAnsatz
    {ι : Type*} (S : Finset ι)
    (T H T' H' : ℝ → ℝ) (ξ ξ' : ι → ℝ → ℝ)
    (χ G χ' G' : ι → ℝ → Vec 2)
    {t : ℝ}
    (hT : HasDerivAt T (T' t) t)
    (hH : HasDerivAt H (H' t) t)
    (hξ : ∀ k ∈ S, HasDerivAt (ξ k) (ξ' k t) t)
    (hχ : ∀ k ∈ S, HasDerivAt (χ k) (χ' k t) t)
    (hG : ∀ k ∈ S, HasDerivAt (G k) (G' k t) t) :
    HasDerivAt
      (fun s => T s + (∑ k ∈ S, ξ k s * vecDot (χ k s) (G k s)) + H s)
      (T' t +
        (∑ k ∈ S, (
          ξ' k t * vecDot (χ k t) (G k t) +
            ξ k t * (vecDot (χ' k t) (G k t) +
              vecDot (χ k t) (G' k t)))) + H' t) t := by
  have hsum : HasDerivAt
      (fun s => ∑ k ∈ S, ξ k s * vecDot (χ k s) (G k s))
      (∑ k ∈ S, (
        ξ' k t * vecDot (χ k t) (G k t) +
          ξ k t * (vecDot (χ' k t) (G k t) +
            vecDot (χ k t) (G' k t)))) t := by
    have hfun :
        (fun s => ∑ k ∈ S, ξ k s * vecDot (χ k s) (G k s)) =
          ∑ k ∈ S, (fun s => ξ k s * vecDot (χ k s) (G k s)) := by
      funext s
      simp
    rw [hfun]
    apply HasDerivAt.sum
    intro k hk
    exact (hξ k hk).mul (hasDerivAt_vecDot (hχ k hk) (hG k hk))
  exact hT.add hsum |>.add hH

end AVenhance.Infra.Section5
