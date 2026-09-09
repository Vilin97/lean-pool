/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketResidualTailFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound

/-! The actual finite residual tail inherits the geometric-series word bound. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

theorem weighted_tail_sum_le (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hsmall : κ * B ≤ 1 / 2) (N : ℕ) :
    (∑ n ∈ tailGrades N, κ^n*B^(n+1)) ≤ 2*B*(κ*B)^(N+1) := by
  calc
    _ = B*(∑ n ∈ Ico (N+1) (2*N+3), (κ*B)^n) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [pow_succ,mul_pow]
      ring
    _ ≤ B*(2*(κ*B)^(N+1)) := mul_le_mul_of_nonneg_left
      (EulerPacketTailBound.sum_geometric_Ico_le (κ*B) (mul_nonneg hκ hB) hsmall _ _) hB
    _ = _ := by ring

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {N : ℕ} {a : ℕ → Profile}

theorem PrefixFields.tailSum_bound_of_grades (F : PrefixFields P T (N + 1) a)
    (C : CoefficientData P T O) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector N (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a N).highPressure)) (ha : a 0 = 0)
    (q : ℕ) (R κ B : ℝ) (hR : 0 ≤ R) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hsmall : κ * B ≤ 1 / 2)
    (hgrade : ∀ n (hn : N + 1 ≤ n), n ≤ 2 * N + 2 →
      (F.tailGradeField C hT Ct hCt pressure ha n hn).WordBound q R (B ^ (n + 1)) 0) :
    (F.tailSumField C hT Ct hCt pressure ha κ).WordBound q R (2*B*(κ*B)^(N+1)) 0 := by
  let W := fun r : {n // n ∈ tailGrades N} =>
    (F.tailGradeField C hT Ct hCt pressure ha r.1 (Finset.mem_Ico.mp r.2).1).smul (κ^r.1)
  have hw : ∀ r ∈ (tailGrades N).attach,
      (W r).WordBound q R (κ^r.1*B^(r.1+1)) 0 := by
    intro r _
    have hm := Finset.mem_Ico.mp r.2
    have hb := (hgrade r.1 hm.1 (by omega)).smul (κ^r.1)
    simpa only [abs_of_nonneg (pow_nonneg hκ r.1)] using hb
  have hs := Field.wordBound_finsetSum (tailGrades N).attach _ W
    (fun r => κ^r.1*B^(r.1+1)) hw
  have hsum : (∑ r ∈ (tailGrades N).attach, κ^r.1*B^(r.1+1)) =
      ∑ n ∈ tailGrades N, κ^n*B^(n+1) :=
    Finset.sum_attach (tailGrades N) (fun n => κ^n*B^(n+1))
  rw [hsum] at hs
  exact (hs.mono_amplitude hR (weighted_tail_sum_le κ B hκ hB hsmall N)).of_path_eq
    (F.tailSumField C hT Ct hCt pressure ha κ) rfl

end EulerPacketCylinderField
