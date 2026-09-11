/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCoefficientGevrey
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoefficientTower
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientJetPressureBounds
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants
public import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyOperators
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.PacketTailBound
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure

/-!
One quantitative coefficient budget for the actual source correction data.
Every constant is independent of the jet order, truncation level and frequency.
The assumptions are the original deformation and inverse-deformation derivative
bounds; all stored coefficient and pressure estimates are derived from them.
-/

section

/-!
The bounds stored in the actual recursive coefficient jet are controlled
by the true word derivatives of its bounded-field translation orbit. A
single enlargement of the coefficient radius gives fixed-base Sobolev
bounds, independent of the jet truncation.
-/

@[expose] public section

noncomputable section

namespace EulerCoefficientPath

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerMetricTransport EulerTransportDerivatives
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerJetProductBounds
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Coefficient directions, given by `(standardDirection i).1`. -/
def coefficientDirections (i : Fin 4) : Space := (standardDirection i).1

theorem coefficientDirections_norm (i : Fin 4) : ‖coefficientDirections i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [coefficientDirections]

omit [CompactSpace K] in
theorem translateCoefficientPath_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : C(K, Space →ᵇ V)) : translateCoefficientPath A 0 = A := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  change A t (x+0) = A t x
  rw [add_zero]

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathBounds1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathBounds2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathBounds3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathBounds4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

theorem coefficientJet_boundLevel_le_words (s n : ℕ) (t : K) :
    boundLevel P (coefficientJet P A hA s t) n ≤
      wordSum coefficientDirections (translateCoefficientPath A) n 0 := by
  induction s generalizing A n with
  | zero =>
    cases n with
    | zero =>
      rw [wordSum_zero,translateCoefficientPath_zero]
      simp only [coefficientJet,boundLevel,smoothCoefficient]
      exact A.norm_coe_le_norm t
    | succ n =>
      simp only [coefficientJet,boundLevel]
      exact wordSum_nonneg _ _ _ _
  | succ s ih =>
    cases n with
    | zero =>
      rw [wordSum_zero,translateCoefficientPath_zero]
      simp only [coefficientJet,boundLevel,smoothCoefficient]
      exact A.norm_coe_le_norm t
    | succ n =>
      rw [wordSum_succ coefficientDirections (translateCoefficientPath A) hA n 0]
      rw [coefficientJet, boundLevel.eq_def]
      apply sum_le_sum
      intro i _
      have hh := ih (orbitDerivativePath A (coefficientDirections i))
        (orbitDerivativePath_orbit A hA (coefficientDirections i)) n
      have he : translateCoefficientPath (orbitDerivativePath A (coefficientDirections i)) =
          directional coefficientDirections (translateCoefficientPath A) i :=
        funext (orbitDerivativePath_translation A hA (coefficientDirections i))
      rw [he] at hh
      exact hh

theorem coefficientJet_boundLevel_le_tensor (s n : ℕ) (t : K) :
    boundLevel P (coefficientJet P A hA s t) n ≤
      (4 : ℝ)^n*‖iteratedFDeriv ℝ n (translateCoefficientPath A) 0‖ := by
  have hh := wordSum_le coefficientDirections coefficientDirections_norm (translateCoefficientPath
      A) n 0
  norm_num only [Fintype.card_fin] at hh
  exact (coefficientJet_boundLevel_le_words P A hA s n t).trans hh

theorem coefficientJet_block_le_words (s q n : ℕ) (t : K) :
    EulerH6Pressure.coefficientBlock P (coefficientJet P A hA s t) q n ≤
      EulerParameterWordGevrey.coefficientBlock coefficientDirections q (translateCoefficientPath
          A) n 0 := by
  change (2 : ℝ)^q*(∑ r ∈ range (q+1),boundLevel P (coefficientJet P A hA s t) (n+r)) ≤
    (2 : ℝ)^q*block coefficientDirections q (translateCoefficientPath A) n 0
  rw [block_eq_sum_levels coefficientDirections q (translateCoefficientPath A) hA n 0]
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum (fun r _ => coefficientJet_boundLevel_le_words P A hA s (n+r) t)) (by positivity)

theorem coefficientJet_block_bound (s q : ℕ) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (t : K) :
    EulerH6Pressure.coefficientBlock P (coefficientJet P A hA s t) q n ≤
      sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4) Rc) 0
          n :=
  (coefficientJet_block_le_words P A hA s q n t).trans
    (coefficientBlock_of_tensor_bound coefficientDirections coefficientDirections_norm q
      (translateCoefficientPath A) hA Rc C hRc hC hb n 0)

end EulerCoefficientPath

end
end

end

section

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

end
end

end

section

/-! Actual coefficient-orbit bounds control the fixed H5/H6 pressure
constants uniformly over all higher jet truncations. -/

@[expose] public section

noncomputable section

namespace EulerCoefficientPath

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerSpatialSobolevInverse EulerJetProductBounds
  EulerParameterWordGevrey EulerGevrey EulerCoefficientJetPressureBounds EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

omit [Fact (0 < P)] in
theorem boundLevel_le_block_zero {s : ℕ} {A : SmoothCoefficient P}
    (J : CoefficientJet P standardDirection s A) (q r : ℕ) (hr : r ≤ q) :
    boundLevel P J r ≤ EulerH6Pressure.coefficientBlock P J q 0 := by
  let S := ∑ k ∈ range (q+1),boundLevel P J k
  have hsum : boundLevel P J r ≤ S := by
    exact single_le_sum (f := fun k => boundLevel P J k)
      (fun k _ => boundLevel_nonneg (n := k) J)
      (show r ∈ range (q+1) from mem_range.mpr (by omega))
  have hnon : 0 ≤ S := sum_nonneg (fun k _ => boundLevel_nonneg J)
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
  have hh : S ≤ (2 : ℝ)^q*S := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hnon
  simpa only [EulerH6Pressure.coefficientBlock,Nat.zero_add,S] using hsum.trans hh

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
  (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)

include hRc hC hb

theorem coefficientJet_base_bound (s q r : ℕ) (hr : r ≤ q) (t : K) :
    boundLevel P (coefficientJet P A hA s t) r ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C := by
  have hh := (boundLevel_le_block_zero P (coefficientJet P A hA s t) q r hr).trans
    (coefficientJet_block_bound P A hA s q Rc C hRc hC hb 0 t)
  simpa only [majorant,Nat.zero_add,pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using
      hh

theorem coefficientJet_restrictedPressure_bound (s q b : ℕ) (hq : q ≤ s) (hqb : q ≤ b)
    (c : ℝ) (hc : 0 < c) (t : K) :
    (EulerH6Pressure.CoefficientJet.restrict (coefficientJet P A hA s t) q hq).pressureConstant c ≤
      pressureCost c (sobolevCoefficientAmplitude (Fin 4) b Rc C) q := by
  apply TreeBound.pressureConstant_le _ c hc (sobolevCoefficientAmplitude_nonneg b Rc C hRc hC)
  apply treeBound_of_levels
  intro r hr
  rw [EulerH6Pressure.coefficient_restrict_level P (coefficientJet P A hA s t) hq hr]
  exact coefficientJet_base_bound P A hA Rc C hRc hC hb s b r (hr.trans hqb) t

end EulerCoefficientPath

end
end

end

section

/-! Quantitative bounds for the actual packet coefficient towers. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients EulerCoefficientPath
  EulerJetProductBounds EulerParameterWordGevrey EulerGevrey EulerSobolevGevreyOperators
  EulerCoefficientJetPressureBounds
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {raw : EulerPacketPointJets.Domain → Space →L[ℝ] Space}
  (A : MatrixCoefficient T raw) (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A.path) x‖ ≤ C * majorant Rc 0 n)

include hRc hC hb

theorem toCoefficientTower_block_bound (s q n : ℕ) (t : Icc (0 : ℝ) T) :
    EulerH6Pressure.coefficientBlock P ((A.toCoefficientTower P).jet s t) q n ≤
      sobolevCoefficientAmplitude (Fin 4) q Rc C * majorant (sobolevCoefficientRadius (Fin 4) Rc) 0
          n :=
  coefficientJet_block_bound P A.path A.orbit s q Rc C hRc hC hb n t

theorem toCoefficientTower_base_bound (s q r : ℕ) (hr : r ≤ q) (t : Icc (0 : ℝ) T) :
    boundLevel P ((A.toCoefficientTower P).jet s t) r ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C
        :=
  coefficientJet_base_bound P A.path A.orbit Rc C hRc hC hb s q r hr t

theorem toCoefficientTower_normalized_block (s q : ℕ) (R : ℝ)
    (hR : normalizedCoefficientRadius q Rc C ≤ R) (n : ℕ) (hn : 1 ≤ n) (t : Icc (0 : ℝ) T) :
    EulerH6Pressure.coefficientBlock P ((A.toCoefficientTower P).jet s t) q n ≤ R^n*(n.factorial :
        ℝ)^2 :=
  coefficientJet_block_normalized P A.path A.orbit s q Rc C hRc hC hb R hR n hn t

theorem toCoefficientTower_weighted_bound (s q N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ * sobolevCoefficientRadius (Fin 4) Rc ≤ 1 / 2) (t : Icc (0 : ℝ) T) :
    weightedCoefficient P ((A.toCoefficientTower P).jet s t) q N ρ ≤
      2*sobolevCoefficientAmplitude (Fin 4) q Rc C :=
  coefficientJet_weighted_bound P A.path A.orbit s q N Rc C hRc hC hb ρ hρ hsmall t

theorem toCoefficientTower_pressure_bound (s q b : ℕ) (hq : q ≤ s) (hqb : q ≤ b)
    (c : ℝ) (hc : 0 < c) (t : Icc (0 : ℝ) T) :
    (EulerH6Pressure.CoefficientJet.restrict ((A.toCoefficientTower P).jet s t) q
        hq).pressureConstant c ≤
      pressureCost c (sobolevCoefficientAmplitude (Fin 4) b Rc C) q :=
  coefficientJet_restrictedPressure_bound P A.path A.orbit Rc C hRc hC hb s q b hq hqb c hc t

end EulerPacketCylinderField.MatrixCoefficient

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set Finset EulerSmoothLimit EulerMeanCoefficients EulerPacketCylinderField
  EulerCoefficientPath EulerParameterWordGevrey EulerCoefficientJetPressureBounds
  EulerGevrey EulerJetProductBounds EulerSobolevGevreyOperators
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The coefficient part of the correction energy budget, uniformly at all
orders and all Fourier scales with absolute value at most one. -/
structure CorrectionCoefficientBudget (D : EulerTransversePacketProvider.Data U)
    (P : ℝ) [Fact (0 < P)] where
  /-- Rc of `CorrectionCoefficientBudget`, of type `ℝ`. -/
  Rc : ℝ
  /-- M of `CorrectionCoefficientBudget`, of type `ℝ`. -/
  M : ℝ
  /-- Bound parameter of `CorrectionCoefficientBudget`, of type `ℝ`. -/
  B : ℝ
  /-- A0 of `CorrectionCoefficientBudget`, of type `ℝ`. -/
  A0 : ℝ
  /-- A2 of `CorrectionCoefficientBudget`, of type `ℝ`. -/
  A2 : ℝ
  Rc_nonneg : 0 ≤ Rc
  M_one_le : 1 ≤ M
  B_nonneg : 0 ≤ B
  A0_nonneg : 0 ≤ A0
  A2_nonneg : 0 ≤ A2
  inverse_five : ∀ s (hs : 6 ≤ s) t,
    (EulerH6Pressure.CoefficientJet.restrict ((metricTower D P).jet s t) 5 (by
        omega)).pressureConstant
      D.normalLower ≤ M
  inverse_six : ∀ s (hs : 6 ≤ s) t,
    (EulerH6Pressure.CoefficientJet.restrict ((metricTower D P).jet s t) 6 hs).pressureConstant
      D.normalLower ≤ M
  metric_derivatives : ∀ s t l, 1 ≤ l →
    EulerH6Pressure.coefficientBlock P ((metricTower D P).jet s t) 6 l ≤ Rc^l*(l.factorial : ℝ)^2
  metric_base : ∀ s t r, r ≤ 6 → boundLevel P ((metricTower D P).jet s t) r ≤ B
  linear : ∀ s N ρ, 0 < ρ → 4*M*(ρ*Rc) ≤ 1 → ∀ t,
    weightedCoefficient P ((linearTower D P).jet s t) 6 N ρ ≤ A0
  quadratic : ∀ κ, |κ| ≤ 1 → ∀ s N ρ, 0 < ρ → 4*M*(ρ*Rc) ≤ 1 → ∀ t,
    (∑ i : Fin 3, weightedCoefficient P ((quadraticTower D P κ i).jet s t) 6 N ρ) ≤ A2

/-- Correction metric envelope, given by `sobolevCoefficientAmplitude (Fin 4) 6 (4*R)
(3*CI*CI)`. -/
def correctionMetricEnvelope (R CI : ℝ) : ℝ :=
  sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*CI)

/-- Correction linear envelope, given by `2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R)
(6*CI*C1)`. -/
def correctionLinearEnvelope (R C1 CI : ℝ) : ℝ :=
  2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (6*CI*C1)

/-- Correction quadratic envelope, given by `6*sobolevCoefficientAmplitude (Fin 4) 6 (4*R)
(3*CI*(C0*R))`. -/
def correctionQuadraticEnvelope (R C0 CI : ℝ) : ℝ :=
  6*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R))

/-- Correction coefficient radius, given by `max 1 (max (normalizedCoefficientRadius 6 (4*R)
(3*CI*CI)) (sobolevCoefficientRadius (Fin 4) (4*R)))`. -/
def correctionCoefficientRadius (R CI : ℝ) : ℝ :=
  max 1 (max (normalizedCoefficientRadius 6 (4*R) (3*CI*CI))
    (sobolevCoefficientRadius (Fin 4) (4*R)))

/-- Correction pressure envelope, given by `max 1 (max (pressureCost c (correctionMetricEnvelope
R CI) 5) (pressureCost c (correctionMetricEnvelope R CI) 6))`. -/
def correctionPressureEnvelope (c R CI : ℝ) : ℝ :=
  max 1 (max (pressureCost c (correctionMetricEnvelope R CI) 5)
    (pressureCost c (correctionMetricEnvelope R CI) 6))

private theorem series_radius_small (ρ Rc M B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hBR : B ≤ Rc) (hM : 1 ≤ M) (hg : 4 * M * (ρ * Rc) ≤ 1) : ρ*B ≤ 1/2 := by
  have hR : 0 ≤ Rc := hB.trans hBR
  have hp : 0 ≤ ρ*Rc := mul_nonneg hρ hR
  have hm := mul_le_mul_of_nonneg_right hM hp
  have hb := mul_le_mul_of_nonneg_left hBR hρ
  nlinarith

variable (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (R C0 C1 CI : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0 * majorant R
      0
      n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1 * majorant
      R
      0 n)
  (hFI : ∀ n t x, ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ CI *
      majorant
      R 0 n)

include hR hC0 hC1 hCI hF hF1 hFI

/-- All coefficient hypotheses of the correction energy estimate, derived
from genuine source spatial jets.  The radius condition is the same one used
by the projected inverse, rather than a separate cutoff-dependent restriction. -/
def correctionCoefficientBudget : CorrectionCoefficientBudget D P where
  Rc := correctionCoefficientRadius R CI
  M := correctionPressureEnvelope D.normalLower R CI
  B := correctionMetricEnvelope R CI
  A0 := correctionLinearEnvelope R C1 CI
  A2 := correctionQuadraticEnvelope R C0 CI
  Rc_nonneg := zero_le_one.trans (le_max_left _ _)
  M_one_le := le_max_left _ _
  B_nonneg := sobolevCoefficientAmplitude_nonneg 6 (4*R) (3*CI*CI) (by positivity) (by positivity)
  A0_nonneg := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*R) (6*CI*C1) (by positivity) (by positivity))
  A2_nonneg := mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg 6 (4*R) (3*CI*(C0*R)) (by positivity) (by positivity))
  inverse_five s hs t := by
    have h := MatrixCoefficient.toCoefficientTower_pressure_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 5 6 (by omega) (by omega)
      D.normalLower D.normalLower_pos t
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  inverse_six s hs t := by
    have h := MatrixCoefficient.toCoefficientTower_pressure_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6 6 hs le_rfl
      D.normalLower D.normalLower_pos t
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))
  metric_derivatives s t l hl := by
    exact MatrixCoefficient.toCoefficientTower_normalized_block P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6
      (correctionCoefficientRadius R CI) ((le_max_left _ _).trans (le_max_right _ _)) l hl t
  metric_base s t r hr :=
    MatrixCoefficient.toCoefficientTower_base_bound P (metricCoefficient D)
      (4*R) (3*CI*CI) (by positivity) (by positivity)
      (metricCoefficient_bound D R CI hR hCI hFI) s 6 r hr t
  linear s N ρ hρ hg t := by
    have hsmall := series_radius_small ρ (correctionCoefficientRadius R CI)
      (correctionPressureEnvelope D.normalLower R CI) (sobolevCoefficientRadius (Fin 4) (4*R))
      hρ.le (sobolevCoefficientRadius_nonneg (4*R) (by positivity))
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) hg
    exact MatrixCoefficient.toCoefficientTower_weighted_bound P (linearCoefficient D)
      (4*R) (6*CI*C1) (by positivity) (by positivity)
      (linearCoefficient_bound D R C1 CI hR hC1 hCI hF1 hFI) s 6 N ρ hρ hsmall t
  quadratic κ hκ s N ρ hρ hg t := by
    have hsmall := series_radius_small ρ (correctionCoefficientRadius R CI)
      (correctionPressureEnvelope D.normalLower R CI) (sobolevCoefficientRadius (Fin 4) (4*R))
      hρ.le (sobolevCoefficientRadius_nonneg (4*R) (by positivity))
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) hg
    have h : ∀ i : Fin 3,
        weightedCoefficient P ((quadraticTower D P κ i).jet s t) 6 N ρ ≤
          2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R)) := by
      intro i
      exact MatrixCoefficient.toCoefficientTower_weighted_bound P (quadraticCoefficient D κ i)
        (4*R) (3*CI*(C0*R)) (by positivity) (by positivity)
        (quadraticCoefficient_bound D R C0 CI hR hC0 hCI hF hFI κ hκ i) s 6 N ρ hρ hsmall t
    calc
      _ ≤ ∑ i : Fin 3, 2*sobolevCoefficientAmplitude (Fin 4) 6 (4*R) (3*CI*(C0*R)) :=
        sum_le_sum (fun i _ => h i)
      _ = _ := by
          simp only [sum_const, Fintype.card_fin, card_univ, nsmul_eq_mul,
              correctionQuadraticEnvelope]; ring

end EulerPacketCorrectionCoefficients
