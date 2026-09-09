/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalL2Scaling

@[expose] public section

/-! Fixed physical Sobolev bounds from the genuine all-order cylinder
word bounds. The constants are finite polynomials at each fixed order;
the oscillating phase costs only the indicated power of its frequency. -/

noncomputable section


open scoped ContDiff

namespace EulerPhysicalL2Scaling

open Finset MeasureTheory EulerSmoothLimit

def derivativeSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (f : Space → V) : ℝ :=
  ∑ n ∈ range (m+1), lpNorm (iteratedFDeriv ℝ n f) 2 volume

def jetPolynomial (R : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ range (m+1), R^n*(n.factorial : ℝ)^2

theorem jetPolynomial_nonneg (R : ℝ) (hR : 0 ≤ R) (m : ℕ) :
    0 ≤ jetPolynomial R m := by
  unfold jetPolynomial
  positivity

def physicalDerivativeCost (P R C : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ range (m+1), (4*C)^n*Real.sqrt (2/P+2*P)*jetPolynomial R (n+1)

theorem physicalDerivativeCost_nonneg (P R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ physicalDerivativeCost P R C m := by
  apply sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Real.sqrt_nonneg _))
    (jetPolynomial_nonneg R hR _)

end EulerPhysicalL2Scaling

namespace EulerPacketCylinderField.Field

open Set Finset MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerPacketProfileRecursion
  EulerLpCylinderTranslation EulerParameterWordGevrey EulerCylinderPhysicalTensor
  EulerPhysicalL2Scaling EulerGevrey

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A : ℝ}

theorem WordBound.slice_word_le (hG : G.WordBound q R A d)
    (t : Icc (0 : ℝ) T) (n : ℕ) :
    wordSum standardDirection (fun a : LiftTangent => translate P a (G.path t)) n 0 ≤
      A*majorant R d n := by
  have he : wordSum standardDirection (fun a : LiftTangent => translate P a (G.path t)) n 0 ≤
      wordSum standardDirection (fun a : LiftTangent => pathTranslate P a G.path) n 0 := by
    apply sum_le_sum
    intro w _
    rw [path_word_evaluation P G.path G.orbit w t]
    exact ContinuousMap.norm_coe_le_norm _ t
  have hb : wordSum standardDirection (fun a : LiftTangent => pathTranslate P a G.path) n 0 ≤
      block standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0 := by
    rw [block_eq_sum_levels standardDirection q _ G.orbit]
    have h := single_le_sum (s := range (q+1))
      (f := fun j => wordSum standardDirection (fun a : LiftTangent => pathTranslate P a G.path)
        (n+j) 0)
      (fun j _ => wordSum_nonneg _ _ _ _) (show 0 ∈ range (q+1) by simp)
    simpa only [Nat.add_zero] using h
  exact he.trans (hb.trans (hG n))

theorem WordBound.tower_norm_le_polynomial (hG : G.WordBound q R A 0)
    (t : Icc (0 : ℝ) T) (s : ℕ) :
    ‖G.toFieldTower.realization s t‖ ≤ A*jetPolynomial R s := by
  apply (sobolev_norm_le_baseSize P s (G.path t) (path_evaluation_smooth P G.path G.orbit t)).trans
  change (∑ n ∈ range (s+1), wordSum standardDirection
    (fun a : LiftTangent => translate P a (G.path t)) n 0) ≤ _
  rw [jetPolynomial,mul_sum]
  apply sum_le_sum
  intro n _
  simpa only [majorant,Nat.add_zero,mul_assoc] using hG.slice_word_le t n

theorem raw_graph_tensor_memLp (G : Field P T raw) (t : Icc (0 : ℝ) T)
    (k : ℝ) (m : Space) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (fun x : Space => raw (t,(x,k*inner ℝ m x)))) 2 volume := by
  rw [G.raw_graph_eq_pointField]
  exact G.toFieldTower.physicalTensor_memLp k m n t

theorem WordBound.raw_graph_tensor_lpNorm_le (hG : G.WordBound q R A 0)
    (t : Icc (0 : ℝ) T) (k : ℝ) (m : Space) (n : ℕ) :
    lpNorm (iteratedFDeriv ℝ n (fun x : Space => raw (t,(x,k*inner ℝ m x)))) 2 volume ≤
      frequencyFactor k m^n*4^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1)) := by
  rw [G.raw_graph_eq_pointField]
  have he : lpNorm (iteratedFDeriv ℝ n (G.toFieldTower.physicalPointField k m t)) 2 volume =
      ‖G.toFieldTower.physicalTensorValue k m n t‖ := by
    rw [Lp.norm_def,eLpNorm_congr_ae (G.toFieldTower.physicalTensorValue_ae k m n t),
      toReal_eLpNorm (G.toFieldTower.physicalTensor_memLp k m n t).aestronglyMeasurable]
  change lpNorm (iteratedFDeriv ℝ n (G.toFieldTower.physicalPointField k m t)) 2 volume ≤ _
  rw [he]
  exact (G.toFieldTower.physicalTensorValue_norm_le k m n t).trans
    (mul_le_mul_of_nonneg_left (hG.tower_norm_le_polynomial t (n+1))
      (mul_nonneg (mul_nonneg (pow_nonneg (frequencyFactor_nonneg k m) n)
        (by positivity)) (Real.sqrt_nonneg _)))

theorem WordBound.scaled_graph_derivativeSum_le (hG : G.WordBound q R A 0)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (t : Icc (0 : ℝ) T)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (k : ℝ) (m : Space) (C K : ℝ) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (hfrequency : frequencyFactor k m ≤ C*K) (s : ℕ) :
    derivativeSum s (scale ell (fun x : Space => raw (t,(x,k*inner ℝ m x)))) ≤
      (ell⁻¹)^s*K^s*A*physicalDerivativeCost P R C s := by
  have hellinv : 1 ≤ ell⁻¹ := (one_le_inv₀ hell).mpr hell1
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  unfold derivativeSum physicalDerivativeCost
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hns : n ≤ s := by have := mem_range.mp hn; omega
  have hJ := jetPolynomial_nonneg R hR (n+1)
  have hp := hG.raw_graph_tensor_lpNorm_le t k m n
  have hs := lpNorm_scale_jet_le ell hell hell1 _ (G.raw_graph_contDiff t k m) n
    (G.raw_graph_tensor_memLp t k m n)
  have hf0 := frequencyFactor_nonneg k m
  have hePow := pow_le_pow_right₀ hellinv hns
  have hfPow := pow_le_pow_left₀ hf0 hfrequency n
  have hkPow := pow_le_pow_right₀ hK hns
  have htail : 0 ≤ (4 : ℝ)^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1)) := by positivity
  apply (hs.trans (mul_le_mul_of_nonneg_left hp (pow_nonneg (inv_nonneg.mpr hell.le) n))).trans
  calc
    _ = ((ell⁻¹)^n*frequencyFactor k m^n)*
        (4^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1))) := by ring
    _ ≤ ((ell⁻¹)^s*(C*K)^n)*
        (4^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hePow hfPow (pow_nonneg hf0 n) (pow_nonneg (inv_nonneg.mpr hell.le) s)) htail
    _ = ((ell⁻¹)^s*C^n*K^n)*
        (4^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1))) := by rw [mul_pow]; ring
    _ ≤ ((ell⁻¹)^s*C^n*K^s)*
        (4^n*Real.sqrt (2/P+2*P)*(A*jetPolynomial R (n+1))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkPow
          (mul_nonneg (pow_nonneg (inv_nonneg.mpr hell.le) s) (pow_nonneg hC n))) htail
    _ = _ := by rw [mul_pow]; ring

end EulerPacketCylinderField.Field
