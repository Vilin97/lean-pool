/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra

@[expose] public section

/-! Finite grade convolution of actual raw cylinder fields. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

/-- A grade selector and two finite sums preserve genuine raw-field admissibility. -/
def convolution (M n : ℕ) (f : ℕ → ℕ → VectorField) (G : ∀ i j, Field P T (f i j)) :
    Field P T (fun z => ∑ i ∈ range (M+1), ∑ j ∈ range (M+1),
      if i+j=n then f i j z else 0) := by
  classical
  let h (i j : ℕ) : Field P T (if i+j=n then f i j else 0) := by
    by_cases hij : i+j=n
    · simpa only [hij,ite_true] using G i j
    · simpa only [hij,ite_false] using Field.zero P T
  let row (i : ℕ) := Field.finsetSum (range (M+1)) (fun j => if i+j=n then f i j else 0) (h i)
  let total := Field.finsetSum (range (M+1))
    (fun i => ∑ j ∈ range (M+1), if i+j=n then f i j else 0) row
  exact total.congr (fun _ _ _ => by simp only [Finset.sum_apply,ite_apply,Pi.zero_apply])

end EulerPacketCylinderField.Field
