/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ChildParticleFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.SobolevSourceExponent

@[expose] public section

/-! The explicit polynomial losses of child composition fit the
manuscript's C*=10(s+2). This includes the sum of the three actual
physical-label Hs word norms, not just a separate bound for each field. -/

noncomputable section

namespace EulerChildParticleFieldBounds.Data

open EulerPacketParentLabelBounds EulerSobolevSourceExponent EulerMeanClassicalWordBounds

variable (G : Data)

theorem amplitude_le_power (k : ℝ) (hk1 : 1 ≤ k)
    (hbig : 2+45*embeddingCost ≤ k) (hK : G.K ≤ k) (hM : G.amp ≤ k) :
    G.amplitude ≤ k^6 := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk1
  have hk15 : k ≤ k^5 := by simpa using pow_le_pow_right₀ hk1 (show 1 ≤ 5 by omega)
  have hk35 : k^3 ≤ k^5 := pow_le_pow_right₀ hk1 (by omega)
  have hprod3 : G.K^2*G.amp ≤ k^3 := by
    have h := mul_le_mul (pow_le_pow_left₀ G.K_nonneg hK 2) hM G.amp_nonneg (pow_nonneg hk0 2)
    exact h.trans_eq (by ring)
  have hprod5 : G.K^3*G.amp^2 ≤ k^5 := by
    have h := mul_le_mul (pow_le_pow_left₀ G.K_nonneg hK 3)
      (pow_le_pow_left₀ G.amp_nonneg hM 2) (sq_nonneg G.amp) (pow_nonneg hk0 3)
    exact h.trans_eq (by ring)
  have h3 : 9*embeddingCost*(G.K^2*G.amp) ≤ 9*embeddingCost*k^5 :=
    mul_le_mul_of_nonneg_left (hprod3.trans hk35) (mul_nonneg (by norm_num) embeddingCost_nonneg)
  have h5 : 36*embeddingCost*(G.K^3*G.amp^2) ≤ 36*embeddingCost*k^5 :=
    mul_le_mul_of_nonneg_left hprod5 (mul_nonneg (by norm_num) embeddingCost_nonneg)
  have hs := add_le_add (add_le_add (add_le_add (hK.trans hk15) (hM.trans hk15)) h3) h5
  have he : G.amplitude = G.K+G.amp+9*embeddingCost*(G.K^2*G.amp)+
      36*embeddingCost*(G.K^3*G.amp^2) := by
    unfold amplitude secondAmplitude firstAmplitude
    ring
  calc
    G.amplitude ≤ (2+45*embeddingCost)*k^5 := by rw [he]; nlinarith [hs]
    _ ≤ k*k^5 := mul_le_mul_of_nonneg_right hbig (pow_nonneg hk0 5)
    _ = k^6 := by ring

theorem radius_le_power (k : ℝ) (hk : 69 ≤ k)
    (hK : G.K ≤ k) (hM : G.amp ≤ k) (hR : G.rad ≤ k^2) : G.radius ≤ k^5 := by
  have hk0 : 0 ≤ k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hk2 : (1 : ℝ) ≤ k^2 := one_le_pow₀ hk1
  have hrad : 1+G.rad ≤ 2*k^2 := by linarith
  have hamp : 1+G.amp ≤ 2*k := by linarith
  have h16 : 16*G.K ≤ 16*k := mul_le_mul_of_nonneg_left hK (by norm_num)
  have hm := mul_le_mul hamp h16 (mul_nonneg (by norm_num) G.K_nonneg) (mul_nonneg (by norm_num)
    hk0)
  have hinner : (1+G.amp)*(16*G.K)+2 ≤ 34*k^2 := by nlinarith [hm]
  have hinner0 : 0 ≤ (1+G.amp)*(16*G.K)+2 := by
    have := G.amp_nonneg
    have := G.K_nonneg
    positivity
  have hprod := mul_le_mul hrad hinner hinner0 (mul_nonneg (by norm_num) (sq_nonneg k))
  have hk24 : k^2 ≤ k^4 := pow_le_pow_right₀ hk1 (by omega)
  have hsum := add_le_add hprod (hR.trans hk24)
  calc
    G.radius ≤ 69*k^4 := by unfold radius compositionRadius; nlinarith [hsum]
    _ ≤ k*k^4 := mul_le_mul_of_nonneg_right hk (pow_nonneg hk0 4)
    _ = k^5 := by ring

theorem source_physical_label_bound (q : ℕ) (k : ℝ) (hk : 69 ≤ k)
    (hbig : 2+45*embeddingCost ≤ k) (hcost : fixedCost q ≤ k)
    (hK : G.K ≤ k) (hM : G.amp ≤ k) (hR : G.rad ≤ k^2) (n : ℕ) :
    classicalBlockSize direction q G.childDisplacement.toLp
      G.childDisplacement.translation_contDiff n+
      classicalBlockSize direction q G.childVelocity.toLp G.childVelocity.translation_contDiff n+
      classicalBlockSize direction q G.childAcceleration.toLp
        G.childAcceleration.translation_contDiff n ≤
        (k^(10*(q+2)))^(n+1)*(n.factorial : ℝ)^2 :=
  source_triple_classical_bound q G.childDisplacement G.childVelocity G.childAcceleration k
    G.amplitude G.radius
    (by linarith) hcost G.amplitude_nonneg G.radius_nonneg
    (G.amplitude_le_power k (by linarith) hbig hK hM) (G.radius_le_power k hk hK hM hR)
    G.childDisplacement_bound G.childVelocity_bound G.childAcceleration_bound n

end EulerChildParticleFieldBounds.Data
