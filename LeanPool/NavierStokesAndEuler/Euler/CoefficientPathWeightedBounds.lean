/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyOperators
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathBounds
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound

/-!
Cutoff-independent weighted estimates for the actual coefficient jets.
The positive-order coefficient normalization is paid once by a fixed
coefficient radius, independent of the solution amplitude and grade.
-/

@[expose] public section


noncomputable section

namespace EulerCoefficientPath

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerSpatialSobolevInverse EulerJetProductBounds
  EulerParameterWordGevrey EulerGevrey EulerPacketWeights EulerSobolevGevreyOperators
  EulerPacketTailBound EulerOperatorGevreyCalculus
open scoped ContDiff BoundedContinuousFunction

/-- Normalized coefficient radius, given by `max 1 (sobolevCoefficientAmplitude (Fin 4) q Rc C)
* sobolevCoefficientRadius (Fin 4) Rc`. -/
def normalizedCoefficientRadius (q : ℕ) (Rc C : ℝ) : ℝ :=
  max 1 (sobolevCoefficientAmplitude (Fin 4) q Rc C) * sobolevCoefficientRadius (Fin 4) Rc

theorem normalizedCoefficientRadius_nonneg (q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) :
    0 ≤ normalizedCoefficientRadius q Rc C :=
  mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (sobolevCoefficientRadius_nonneg Rc hRc)

theorem amplitude_majorant_le_normalized (q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc)
    (n : ℕ) (hn : 1 ≤ n) :
    sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4) Rc) 0 n
        ≤
      majorant (normalizedCoefficientRadius q Rc C) 0 n := by
  have hp : sobolevCoefficientAmplitude (Fin 4) q Rc C ≤
      (max 1 (sobolevCoefficientAmplitude (Fin 4) q Rc C))^n :=
    (le_max_right _ _).trans (by
      simpa only [pow_one] using pow_le_pow_right₀
        (le_max_left (1 : ℝ) (sobolevCoefficientAmplitude (Fin 4) q Rc C)) hn)
  calc
    _ ≤ (max 1 (sobolevCoefficientAmplitude (Fin 4) q Rc C))^n *
        majorant (sobolevCoefficientRadius (Fin 4) Rc) 0 n :=
      mul_le_mul_of_nonneg_right hp (majorant_nonneg _ (sobolevCoefficientRadius_nonneg Rc hRc) 0 n)
    _ = _ := by simp only [majorant,normalizedCoefficientRadius,Nat.add_zero,mul_pow]; ring

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

theorem coefficientJet_block_normalized (s q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)
    (R : ℝ) (hR : normalizedCoefficientRadius q Rc C ≤ R)
    (n : ℕ) (hn : 1 ≤ n) (t : K) :
    EulerH6Pressure.coefficientBlock P (coefficientJet P A hA s t) q n ≤
      R^n*(n.factorial : ℝ)^2 := by
  have h := (coefficientJet_block_bound P A hA s q Rc C hRc hC hb n t).trans
    (amplitude_majorant_le_normalized q Rc C hRc n hn)
  exact h.trans (majorant_radius_mono _ R (normalizedCoefficientRadius_nonneg q Rc C hRc) hR 0 n)

private theorem weight_majorant_zero (ρ R : ℝ) (n : ℕ) :
    weight ρ n*majorant R 0 n = (ρ*R)^n := by
  unfold weight majorant
  simp only [Nat.add_zero,mul_pow]
  field_simp [factorial_cast_ne_zero n]

theorem coefficientJet_weighted_bound (s q N : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)
    (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * sobolevCoefficientRadius (Fin 4) Rc ≤ 1 / 2) (t : K) :
    weightedCoefficient P (coefficientJet P A hA s t) q N ρ ≤
      2*sobolevCoefficientAmplitude (Fin 4) q Rc C := by
  have hB := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q Rc C hRc hC
  calc
    _ ≤ ∑ n ∈ range (N+1), weight ρ n *
        (sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4)
            Rc) 0 n) := by
      apply sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_left (coefficientJet_block_bound P A hA s q Rc C hRc hC hb n t)
        (weight_pos hρ n).le
    _ = sobolevCoefficientAmplitude (Fin 4) q Rc C *
        ∑ n ∈ range (N+1), (ρ*sobolevCoefficientRadius (Fin 4) Rc)^n := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      rw [← weight_majorant_zero ρ (sobolevCoefficientRadius (Fin 4) Rc) n]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (sum_geometric_le_two _ (mul_nonneg hρ.le (sobolevCoefficientRadius_nonneg Rc hRc)) hsmall
          (N+1))
      hB).trans_eq (mul_comm _ _)

end EulerCoefficientPath
