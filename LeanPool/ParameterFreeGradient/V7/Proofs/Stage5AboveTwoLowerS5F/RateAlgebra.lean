/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.UnitInstance

namespace V7.Stage5AboveTwoLowerS5F

lemma rate_power_implication {p T A K eps : ℝ}
    (hp : 2 < p) (hT : 0 < T) (hA : 0 < A) (hK : 0 < K) (heps : 0 < eps)
    (hpower : T < (A / (K * eps)) ^ (p / (p + 2))) :
    eps < A / (K * T ^ (1 + 2 / p)) := by
  let alpha := p / (p + 2)
  let gamma := (p + 2) / p
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hbase : 0 < A / (K * eps) := div_pos hA (mul_pos hK heps)
  have hpow := Real.rpow_lt_rpow hT.le hpower hgamma
  have halphagamma : alpha * gamma = 1 := by
    dsimp [alpha, gamma]
    field_simp
  have hgammaEq : gamma = 1 + 2 / p := by
    dsimp [gamma]
    field_simp
  rw [← Real.rpow_mul hbase.le, halphagamma, Real.rpow_one, hgammaEq] at hpow
  have hTpow : 0 < T ^ (1 + 2 / p) := Real.rpow_pos_of_pos hT _
  rw [lt_div_iff₀ (mul_pos hK hTpow)]
  rw [div_eq_mul_inv] at hpow
  have hden : 0 < K * eps := mul_pos hK heps
  have := mul_lt_mul_of_pos_left hpow hden
  field_simp [hK.ne', heps.ne'] at this
  have hgammaEq' : (p + 2) / p = 1 + 2 / p := by
    simpa [gamma] using hgammaEq
  rw [hgammaEq'] at this
  calc
    eps * (K * T ^ (1 + 2 / p)) = K * eps * T ^ (1 + 2 / p) := by ring
    _ < A := this

end V7.Stage5AboveTwoLowerS5F
