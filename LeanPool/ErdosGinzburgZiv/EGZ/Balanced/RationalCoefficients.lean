/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RealCoefficients
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalApproximation

/-!
# Rational balanced coefficients

Approximation inside the strict caps preserves the exact rational affine
equations. The largest centrality keeps the resulting coefficients uniform
over every admissible centrality parameter.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace EGZ.BalancedCombination.Data

variable {d : ℕ} (D : Data d)

theorem positive_rational_capped_barycenter_exists {η : ℝ} (hη : 0 < η) :
    ∃ β : D.support → ℚ, (∀ q, 0 < β q) ∧ (∑ q, β q = 1) ∧
      (∀ i, ∑ q, β q * (q.val i : ℚ) = (D.center i : ℚ)) ∧
      ∀ θ, 0 < θ → IsCentral D.support D.weight θ D.center.real →
        ∀ q, (β q : ℝ) ≤ (1 + η) * D.weight q / (θ * ∑ r, D.weight r) := by
  classical
  obtain ⟨x, hxpos, hxsum, hxvec, hxcap⟩ := D.positive_capped_barycenter_exists hη
  let A : Matrix (Option (Fin d)) D.support ℚ :=
    fun i q ↦ i.elim 1 (fun j ↦ (q.val j : ℚ))
  let b : Option (Fin d) → ℚ := fun i ↦ i.elim 1 (fun j ↦ (D.center j : ℚ))
  have hx : (A.map (Rat.castHom ℝ)) *ᵥ x = (fun i ↦ (b i : ℝ)) := by
    funext i
    cases i with
    | none => simpa [Matrix.mulVec, Matrix.map, dotProduct, A, b] using hxsum
    | some i =>
      have hi := congrFun hxvec i
      simpa [Matrix.mulVec, Matrix.map, dotProduct, A, b, Finset.sum_apply,
        Pi.smul_apply, IntCoord.real, mul_comm] using hi
  let U : Set (D.support → ℝ) := {z | ∀ q, 0 < z q ∧
    z q < (1 + η) * D.weight q / (D.maxCentrality * ∑ r, D.weight r)}
  have hU : IsOpen U := by
    unfold U
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro q
    exact (isOpen_lt continuous_const (continuous_apply q)).inter
      (isOpen_lt (continuous_apply q) continuous_const)
  obtain ⟨β, hβ, hβU⟩ := exists_rational_solution_mem_open A b x hx U hU
    (fun q ↦ ⟨hxpos q, hxcap q⟩)
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro q
    have hq : (0 : ℝ) < (β q : ℝ) := (hβU q).1
    exact_mod_cast hq
  · simpa [Matrix.mulVec, dotProduct, A, b] using congrFun hβ none
  · intro i
    simpa [Matrix.mulVec, dotProduct, A, b, mul_comm] using congrFun hβ (some i)
  · intro θ hθ hc q
    exact (hβU q).2.le.trans (D.relaxed_max_cap_le hη.le hθ hc q)

end EGZ.BalancedCombination.Data
