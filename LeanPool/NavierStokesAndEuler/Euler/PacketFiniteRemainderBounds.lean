/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteSumBounds

/-! Removing the literal leading coefficient before bounding the packet remainder. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerPacketPointJets EulerPacketProfileRecursion EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)]

/-- Evaluate remainder as an element of `Field P T (fieldSum M κ f-κ • f 1)`. -/
def evaluateRemainder (M : ℕ) (hM : 1 ≤ M) (κ : ℝ) (f : ℕ → VectorField)
    (G : ∀ i, Field P T (f i)) : Field P T (fieldSum M κ f-κ • f 1) := by
  let W := Field.finsetSum ((range (M+1)).erase 1) (fun i => κ^i • f i) (fun i => (G i).smul (κ^i))
  refine W.congr ?_
  intro t x θ
  change fieldSum M κ f (t,(x,θ))-κ • f 1 (t,(x,θ)) = _
  have hm : 1 ∈ range (M+1) := mem_range.mpr (by omega)
  have he := Finset.sum_erase_add (range (M+1)) (fun i => κ^i • f i (t,(x,θ))) hm
  rw [pow_one] at he
  change (∑ i ∈ range (M+1), κ^i • f i (t,(x,θ)))-κ • f 1 (t,(x,θ)) = _
  simp only [Finset.sum_apply,Pi.smul_apply]
  exact (eq_sub_iff_add_eq.mpr he).symm

theorem wordBound_evaluateRemainder (N : ℕ) (hN : 1 ≤ N) (κ B C₂ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hsmall : κ * B ≤ 1 / 2)
    (f : ℕ → VectorField) (G : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ (t : Icc (0 : ℝ) T) x θ, f 0 (t, (x, θ)) = 0)
    (htwo : (G 2).WordBound q R C₂ 0)
    (htail : ∀ n, 3 ≤ n → n ≤ N + 1 → (G n).WordBound q R (B ^ (n + 1)) 0) :
    (evaluateRemainder (N+1) (by omega) κ f G).WordBound q R (κ^2*C₂+2*B*(κ*B)^3) 0 := by
  have hG : ∀ i ∈ (range (N+1+1)).erase 1,
      (G i).WordBound q R (lowHighEnvelope B 0 C₂ i) 0 := by
    intro i hi
    have hi1 := (mem_erase.mp hi).1
    have him := mem_range.mp (mem_erase.mp hi).2
    by_cases hi0 : i=0
    · subst i
      simpa only [lowHighEnvelope,ite_true] using wordBound_of_zero (G 0) hzero q R 0
    · by_cases hi2 : i=2
      · subst i
        simpa only [lowHighEnvelope,show ¬(2:ℕ)=0 by omega,show ¬(2:ℕ)=1 by omega,
          ite_false,ite_true] using htwo
      · simpa only [lowHighEnvelope,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2] using
          htail i (by omega) (by omega)
  have hs := wordBound_finsetSum ((range (N+1+1)).erase 1)
    (fun i => κ^i • f i) (fun i => (G i).smul (κ^i))
    (fun i => κ^i*lowHighEnvelope B 0 C₂ i) (fun i hi => by
      simpa only [abs_of_nonneg (pow_nonneg hκ i)] using (hG i hi).smul (κ^i))
  have he : (∑ i ∈ (range (N+1+1)).erase 1, κ^i*lowHighEnvelope B 0 C₂ i) =
      ∑ i ∈ range (N+1+1), κ^i*lowHighEnvelope B 0 C₂ i :=
    Finset.sum_erase (range (N+1+1)) (by simp [lowHighEnvelope])
  rw [he] at hs
  have hb := weighted_low_high_sum_le N hN κ B 0 C₂ hκ hB hsmall (lowHighEnvelope B 0 C₂)
    (by simp [lowHighEnvelope]) (by simp [lowHighEnvelope]) (by simp [lowHighEnvelope])
    (fun n hn _ => by simp [lowHighEnvelope,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega])
  simp only [mul_zero,zero_add] at hb
  exact (hs.mono_amplitude hR hb).of_path_eq _ rfl

end EulerPacketCylinderField.Field
