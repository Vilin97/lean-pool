/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound

@[expose] public section

/-! A finite packet sum keeps its first two grades separate from the geometric tail. -/

noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerPacketProfileRecursion EulerPacketTailBound

theorem weighted_low_high_sum_le (N : ℕ) (hN : 1 ≤ N) (κ B C₁ C₂ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hsmall : κ*B ≤ 1/2) (A : ℕ → ℝ)
    (hzero : A 0=0) (hone : A 1 ≤ C₁) (htwo : A 2 ≤ C₂)
    (htail : ∀ n, 3 ≤ n → n ≤ N+1 → A n ≤ B^(n+1)) :
    (∑ n ∈ range (N+2), κ^n*A n) ≤ κ*C₁+κ^2*C₂+2*B*(κ*B)^3 := by
  have hlow : (∑ n ∈ range 3, κ^n*A n) ≤ κ*C₁+κ^2*C₂ := by
    simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,hzero,mul_zero,zero_add]
    exact add_le_add (mul_le_mul_of_nonneg_left hone hκ)
      (mul_le_mul_of_nonneg_left htwo (sq_nonneg κ))
  have hhigh : (∑ n ∈ Ico 3 (N+2), κ^n*A n) ≤ 2*B*(κ*B)^3 := by
    calc
      _ ≤ ∑ n ∈ Ico 3 (N+2), κ^n*B^(n+1) := sum_le_sum (fun n hn =>
        mul_le_mul_of_nonneg_left (htail n (mem_Ico.mp hn).1 (by have := (mem_Ico.mp hn).2; omega))
          (pow_nonneg hκ _))
      _ = B*(∑ n ∈ Ico 3 (N+2), (κ*B)^n) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        simp only [pow_succ,mul_pow]
        ring
      _ ≤ B*(2*(κ*B)^3) := mul_le_mul_of_nonneg_left
        (sum_geometric_Ico_le (κ*B) (mul_nonneg hκ hB) hsmall _ _) hB
      _ = _ := by ring
  rw [← sum_range_add_sum_Ico _ (show 3 ≤ N+2 by omega)]
  exact add_le_add hlow hhigh

def lowHighEnvelope (B C₁ C₂ : ℝ) (n : ℕ) : ℝ :=
  if n=0 then 0 else if n=1 then C₁ else if n=2 then C₂ else B^(n+1)

namespace Field

variable {P T : ℝ} [Fact (0 < P)]

theorem wordBound_evaluateFamily (M : ℕ) (κ : ℝ) (f : ℕ → VectorField)
    (G : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (A : ℕ → ℝ) (d : ℕ) (hκ : 0 ≤ κ)
    (hG : ∀ i ∈ range (M+1), (G i).WordBound q R (A i) d) :
    (evaluateFamily M κ f G).WordBound q R (∑ i ∈ range (M+1), κ^i*A i) d := by
  have h := wordBound_finsetSum (range (M+1)) (fun i => κ^i • f i) (fun i => (G i).smul (κ^i))
    (fun i => κ^i*A i) (fun i hi => by
      simpa only [abs_of_nonneg (pow_nonneg hκ i)] using (hG i hi).smul (κ^i))
  exact h.of_path_eq _ rfl

theorem wordBound_evaluate_low_high (N : ℕ) (hN : 1 ≤ N) (κ B C₁ C₂ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hsmall : κ*B ≤ 1/2)
    (f : ℕ → VectorField) (G : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ (t : Icc (0 : ℝ) T) x θ, f 0 (t,(x,θ))=0)
    (hone : (G 1).WordBound q R C₁ 0) (htwo : (G 2).WordBound q R C₂ 0)
    (htail : ∀ n, 3 ≤ n → n ≤ N+1 → (G n).WordBound q R (B^(n+1)) 0) :
    (evaluateFamily (N+1) κ f G).WordBound q R (κ*C₁+κ^2*C₂+2*B*(κ*B)^3) 0 := by
  have hG : ∀ i ∈ range (N+1+1), (G i).WordBound q R (lowHighEnvelope B C₁ C₂ i) 0 := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      simpa only [lowHighEnvelope,ite_true] using wordBound_of_zero (G 0) hzero q R 0
    · by_cases hi1 : i=1
      · subst i
        simpa only [lowHighEnvelope,show ¬(1:ℕ)=0 by omega,ite_false,ite_true] using hone
      · by_cases hi2 : i=2
        · subst i
          simpa only [lowHighEnvelope,show ¬(2:ℕ)=0 by omega,show ¬(2:ℕ)=1 by omega,
            ite_false,ite_true] using htwo
        · simpa only [lowHighEnvelope,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2] using
            htail i (by omega) (by have := mem_range.mp hi; omega)
  have hs := wordBound_evaluateFamily (N+1) κ f G q R (lowHighEnvelope B C₁ C₂) 0 hκ hG
  apply hs.mono_amplitude hR
  exact weighted_low_high_sum_le N hN κ B C₁ C₂ hκ hB hsmall (lowHighEnvelope B C₁ C₂)
    (by simp [lowHighEnvelope]) (by simp [lowHighEnvelope]) (by simp [lowHighEnvelope])
    (fun n hn _ => by simp [lowHighEnvelope,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega])

end Field
end EulerPacketCylinderField
