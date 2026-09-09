/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderConvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds

/-! Fixed-radius word bounds for the actual finite grade convolution. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

theorem wordBound_convolution (M n : ℕ) (f : ℕ → ℕ → VectorField)
    (G : ∀ i j, Field P T (f i j)) (q : ℕ) (R A : ℝ) (d : ℕ)
    (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hG : ∀ i ∈ range (M + 1), ∀ j ∈ range (M + 1), i + j = n → (G i j).WordBound q R A d) :
    (Field.convolution M n f G).WordBound q R (((M+1 : ℕ) : ℝ)^2*A) d := by
  classical
  let K : ∀ i j, Field P T (if i+j=n then f i j else 0) := fun i j => by
    by_cases hij : i+j=n
    · exact (G i j).congr (fun _ _ _ => by rw [ite_eq_left hij])
    · exact (Field.zero P T).congr (fun _ _ _ => by rw [ite_eq_right hij])
  have hK : ∀ i ∈ range (M+1), ∀ j ∈ range (M+1), (K i j).WordBound q R A d := by
    intro i hi j hj
    by_cases hij : i+j=n
    · exact (hG i hi j hj hij).ofRawEq (K i j) (fun _ _ _ => by rw [ite_eq_left hij])
    · exact (wordBound_of_zero (K i j) (fun _ _ _ => by
        rw [ite_eq_right hij]; rfl) q R d).mono_amplitude hR hA
  let row : (i : ℕ) → Field P T (∑ j ∈ range (M+1), if i+j=n then f i j else 0) := fun i =>
    Field.finsetSum (range (M+1)) (fun j => if i+j=n then f i j else 0) (K i)
  have hr : ∀ i ∈ range (M+1), (row i).WordBound q R (((M+1 : ℕ) : ℝ)*A) d := by
    intro i hi
    have h := wordBound_finsetSum (range (M+1)) (fun j => if i+j=n then f i j else 0) (K i)
      (fun _ => A) (hK i hi)
    simpa only [sum_const,card_range,nsmul_eq_mul] using h
  have ht := wordBound_finsetSum (range (M+1))
    (fun i => ∑ j ∈ range (M+1), if i+j=n then f i j else 0) row
    (fun _ => ((M+1 : ℕ) : ℝ)*A) hr
  have he : ∑ _i ∈ range (M+1), ((M+1 : ℕ) : ℝ)*A = ((M+1 : ℕ) : ℝ)^2*A := by
    simp only [sum_const,card_range,nsmul_eq_mul]
    ring
  rw [he] at ht
  apply ht.ofRawEq (Field.convolution M n f G)
  intro t x θ
  simp only [Finset.sum_apply,ite_apply,Pi.zero_apply]

end EulerPacketCylinderField.Field
