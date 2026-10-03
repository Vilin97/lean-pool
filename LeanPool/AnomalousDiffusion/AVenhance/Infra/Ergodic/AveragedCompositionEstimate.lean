/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragedCompositionNorm

/-! Sharp factorial resummation in the averaged composition estimate. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno AVenhance.Infra.Torus
namespace AVenhance.Infra.Ergodic

/-- The uniform coefficient attached to one ordered partition. -/
def compositionPartitionBound {n : ℕ} (c : OrderedFinpartition n)
    (Cf r CX R : ℝ) : ℝ :=
  (∏ b, CX * (c.partSize b).factorial * R ^ c.partSize b) *
    (Cf * c.length.factorial / r ^ c.length)

theorem compositionPartitionBound_nonneg {n : ℕ} (c : OrderedFinpartition n)
    {Cf r CX R : ℝ} (hCf : 0 ≤ Cf) (hr : 0 < r) (hCX : 0 ≤ CX) (hR : 0 ≤ R) :
    0 ≤ compositionPartitionBound c Cf r CX R := by
  unfold compositionPartitionBound
  positivity

/-- Each term has precisely one averaged outer derivative. -/
theorem compositionJetTerm_bound {d n : ℕ} (hn : 0 < n)
    (X : PeriodicVolumePreservingDiffeomorphism d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    {Cf r CX R : ℝ} (hCX : 0 ≤ CX) (hR : 0 ≤ R)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hfbound : ∀ k (j : Fin k → Fin d), 0 < k →
      eLpNorm (spatialJet k f j) p (volume.restrict (unitCell d)) ≤
        ENNReal.ofReal (Cf * k.factorial / r ^ k))
    (hXbound : ∀ k (v : Fin k → Fin d), 0 < k → ∀ x i,
      |(spatialJet k X.toFun v x) i| ≤ CX * k.factorial * R ^ k)
    (w : Fin n → Fin d) (c : OrderedFinpartition n) (j : Fin c.length → Fin d) :
    eLpNorm (compositionJetTerm f X.toFun w c j) p (volume.restrict (unitCell d)) ≤
      ENNReal.ofReal (compositionPartitionBound c Cf r CX R) := by
  have hu := spatialJet_continuous hf j
  have hpu := spatialJet_periodic hper j
  have he := eLpNorm_comp_flow_eq hu hpu X hp0 hpt
  have hb := compositionJetTerm_eLpNorm_le hf X.contDiff_toFun w c j hCX hR hXbound p
    (volume.restrict (unitCell d))
  rw [show (fun x => spatialJet c.length f j (X.toFun x)) =
    spatialJet c.length f j ∘ X.toFun from rfl, he] at hb
  have hh := hb.trans (mul_le_mul_right (hfbound _ j (c.length_pos hn)) _)
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ ∏ b, CX * (c.partSize b).factorial * R ^ c.partSize b)] at hh
  exact hh

/-- Finite coordinate assignments contribute d^k, and partition weights
resum to n! A(1+A)^(n-1). -/
theorem compositionPartitionBound_sum {d n : ℕ} (hn : 0 < n)
    {Cf r CX R : ℝ} (hr : 0 < r) :
    (∑ c : OrderedFinpartition n, ∑ _j : Fin c.length → Fin d,
      compositionPartitionBound c Cf r CX R) =
      Cf * R ^ n * (n.factorial : ℝ) * ((d : ℝ) * CX / r) *
        (1 + (d : ℝ) * CX / r) ^ (n - 1) := by
  classical
  have ht (c : OrderedFinpartition n) :
      (∑ _j : Fin c.length → Fin d, compositionPartitionBound c Cf r CX R) =
      Cf * R ^ n *
        (((d : ℝ) * CX / r) ^ c.length * c.length.factorial *
          (orderedPartitionFactorialProduct c : ℝ)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    unfold compositionPartitionBound orderedPartitionFactorialProduct
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, composition_block_size_sum,
      Nat.cast_prod, mul_pow, div_pow]
    field_simp [hr.ne']
  simp_rw [ht]
  rw [← Finset.mul_sum, orderedFinpartitionFactorialResummation10469 hn]
  ring

/-- The exact factorial envelope at the composed radius. -/
theorem compositionPartitionBound_sum_le {d n : ℕ} (hn : 0 < n)
    {Cf r CX R : ℝ} (hCf : 0 ≤ Cf) (hr : 0 < r) (hCX : 0 ≤ CX) (hR : 0 ≤ R) :
    (∑ c : OrderedFinpartition n, ∑ _j : Fin c.length → Fin d,
      compositionPartitionBound c Cf r CX R) ≤
      Cf * n.factorial / (r / (R * (r + (d : ℝ) * CX))) ^ n := by
  let A := (d : ℝ) * CX / r
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpow : A * (1 + A) ^ (n - 1) ≤ (1 + A) ^ n := by
    calc
      A * (1 + A) ^ (n - 1) ≤ (1 + A) * (1 + A) ^ (n - 1) := by
        gcongr
        linarith
      _ = (1 + A) ^ n := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [compositionPartitionBound_sum hn hr]
  calc
    _ = (Cf * R ^ n * n.factorial) * (A * (1 + A) ^ (n - 1)) := by ring
    _ ≤ (Cf * R ^ n * n.factorial) * (1 + A) ^ n :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by
      have hid : R * (r + (d : ℝ) * CX) / r = R * (1 + A) := by
        dsimp [A]
        field_simp
      have he : Cf * n.factorial / (r / (R * (r + (d : ℝ) * CX))) ^ n =
          Cf * n.factorial * (R * (r + (d : ℝ) * CX) / r) ^ n := by
        rw [div_pow, div_div_eq_mul_div, div_pow]
        ring
      rw [he, hid, mul_pow]
      ring

/-- Mixed averaged derivative bounds compose without a supremum bound on f. -/
theorem spatialJet_comp_eLpNorm_le {d n : ℕ} (hn : 0 < n)
    (X : PeriodicVolumePreservingDiffeomorphism d) {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    {Cf r CX R : ℝ} (hCf : 0 ≤ Cf) (hr : 0 < r) (hCX : 0 ≤ CX) (hR : 0 ≤ R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hfbound : ∀ k (j : Fin k → Fin d), 0 < k →
      eLpNorm (spatialJet k f j) p (volume.restrict (unitCell d)) ≤
        ENNReal.ofReal (Cf * k.factorial / r ^ k))
    (hXbound : ∀ k (v : Fin k → Fin d), 0 < k → ∀ x i,
      |(spatialJet k X.toFun v x) i| ≤ CX * k.factorial * R ^ k)
    (w : Fin n → Fin d) :
    eLpNorm (spatialJet n (f ∘ X.toFun) w) p (volume.restrict (unitCell d)) ≤
      ENNReal.ofReal (Cf * n.factorial /
        (r / (R * (r + (d : ℝ) * CX))) ^ n) := by
  classical
  have he : spatialJet n (f ∘ X.toFun) w =
      ∑ c : OrderedFinpartition n, ∑ j : Fin c.length → Fin d,
        compositionJetTerm f X.toFun w c j := by
    funext x
    simpa only [Finset.sum_apply] using spatialJet_comp_expansion hf X.contDiff_toFun w x
  rw [he]
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        eLpNorm (∑ j : Fin c.length → Fin d, compositionJetTerm f X.toFun w c j)
          p (volume.restrict (unitCell d)) := eLpNorm_sum_le hp
    _ ≤ ∑ c : OrderedFinpartition n, ∑ j : Fin c.length → Fin d,
        eLpNorm (compositionJetTerm f X.toFun w c j) p
          (volume.restrict (unitCell d)) := Finset.sum_le_sum fun c hc => eLpNorm_sum_le hp
    _ ≤ ∑ c : OrderedFinpartition n, ∑ _j : Fin c.length → Fin d,
        ENNReal.ofReal (compositionPartitionBound c Cf r CX R) := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro j hj
      exact compositionJetTerm_bound hn X hf hper hCX hR
        (ne_of_gt (lt_of_lt_of_le (by norm_num) hp)) hpt hfbound hXbound w c j
    _ = ENNReal.ofReal (∑ c : OrderedFinpartition n, ∑ _j : Fin c.length → Fin d,
        compositionPartitionBound c Cf r CX R) := by
      simp_rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j hj => compositionPartitionBound_nonneg _ hCf hr hCX hR)]
      rw [ENNReal.ofReal_sum_of_nonneg (fun c hc =>
        Finset.sum_nonneg fun j hj => compositionPartitionBound_nonneg _ hCf hr hCX hR)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (compositionPartitionBound_sum_le hn hCf hr hCX hR)

end AVenhance.Infra.Ergodic
