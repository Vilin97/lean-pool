/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.LowerTransportSource

@[expose] public section

/-! The fixed-base transport commutator estimate with only H⁶ velocity norms. -/

noncomputable section

namespace EulerBaseTransportL2

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolev EulerMetricTransport
  EulerTransportDerivatives
  EulerH6Nonlinear EulerVectorCylinder EulerBaseTransportCommutator EulerExternalTransportCommutator
  EulerFunctionalVelocity EulerMixedH5Product
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The base transport constant depends only on the fixed Sobolev index and cylinder period. -/
def baseTransportConstant : ℝ := (4*63*5460*1365 : ℝ)*mixedConstant period

theorem baseTransportConstant_nonneg : 0 ≤ baseTransportConstant period :=
  mul_nonneg (by norm_num) (mixedConstant_nonneg period)

/-- The gradient H⁵ sum is controlled by the actual H⁶ norm with a fixed combinatorial factor. -/
theorem gradientFive_le_six {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : LiftDomain period → F) : gradientFiveNorm period f ≤ 5460*liftSobolevNorm period 6 f := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => derivative_H5_le_H6
    period i f)
  exact h.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]; ring)

/-- Summing actual L² fields respects the sum of their finite L² norms. -/
theorem fieldL2_sum_le {ι F : Type*} [NormedAddCommGroup F] (S : Finset ι)
    (f : ι → LiftDomain period → F) (hf : ∀ i ∈ S, MemLp (f i) 2 (liftMeasure period)) :
    (eLpNorm (∑ i ∈ S, f i) 2 (liftMeasure period)).toReal ≤
      ∑ i ∈ S, (eLpNorm (f i) 2 (liftMeasure period)).toReal := by
  have he := eLpNorm_sum_le (fun i hi => (hf i hi).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞)
    ≤ 2)
  have hfin : (∑ i ∈ S, eLpNorm (f i) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i hi => (hf i hi).eLpNorm_ne_top)
  have h := ENNReal.toReal_mono hfin he
  rw [ENNReal.toReal_sum (fun i hi => (hf i hi).eLpNorm_ne_top)] at h
  exact h

/-- The literal transport commutator through six base derivatives is in L² and bounded using only the two H⁶ norms. -/
theorem transport_base_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a g) 2 (liftMeasure
      period)) :
    MemLp (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period) ∧
    (eLpNorm (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period)).toReal ≤
      baseTransportConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  let h := fun i : Fin 4 => scalarCommutator period w (L i ∘ f) (fieldDerivative period
    (standardDirection i) g)
  have hs (i : Fin 4) := scalarCommutator_bound period hn w (L i ∘ f) (fieldDerivative period
    (standardDirection i) g)
    (postcomp_smooth period (L i) f hf) (fieldDerivative_smooth period _ g hg)
    (fun j hj a => postcomp_word_memLp period hj (L i) f hf (fun r _ b => hfL r b) a)
    (fun j _ a => derivative_all_memLp period g hgL i j a)
  have hgrad (i : Fin 4) : gradientFiveNorm period (L i ∘ f) ≤ 5460*liftSobolevNorm period 6 f :=
    (gradientFive_le_six period (L i ∘ f)).trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 6 (L i) (hL i) f hf (fun j _ a => hfL j a)) (by norm_num))
  have hp : (2 : ℝ)^n-1 ≤ 63 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h
    linarith
  have hcoef := mul_le_mul_of_nonneg_right hp (mixedConstant_nonneg period)
  have hb (i : Fin 4) : (eLpNorm (h i) 2 (liftMeasure period)).toReal ≤
      (63*5460*1365*mixedConstant period)*liftSobolevNorm period 6 f*liftSobolevNorm period 6 g :=
        by
    have h1 := mul_le_mul hcoef (hgrad i) (gradientFiveNorm_nonneg period (L i ∘ f))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 63) (mixedConstant_nonneg period))
    have h2 := mul_le_mul h1 (derivative_H5_le_H6 period i g) (liftSobolevNorm_nonneg period 5 _)
      (mul_nonneg (mul_nonneg (by norm_num) (mixedConstant_nonneg period))
        (mul_nonneg (by norm_num) (liftSobolevNorm_nonneg period 6 f)))
    exact (hs i).2.trans (h2.trans_eq (by ring))
  have heq : transportCommutator period w (velocityMap L ∘ f) g = ∑ i : Fin 4, h i := by
    rw [transportCommutator_eq_sum period w (velocityMap L ∘ f) g (postcomp_smooth period
      (velocityMap L) f hf) hg]
    rfl
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun i _ => (hs i).1), ?_⟩
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => hb i)
  exact (fieldL2_sum_le period Finset.univ h (fun i _ => (hs i).1)).trans
    (hsum.trans_eq (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; unfold baseTransportConstant; ring))

end EulerBaseTransportL2
