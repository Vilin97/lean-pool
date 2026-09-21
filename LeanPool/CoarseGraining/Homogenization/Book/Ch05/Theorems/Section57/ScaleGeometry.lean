/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.DeterministicThresholds

/-! # Scale Geometry -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Scale geometry for Section 5.7 bad-pair estimates

This file records the elementary arithmetic facts used to simplify the
deterministic scales after shifting by the annealed entry scale.
-/

noncomputable section

theorem nat_cast_add_sub_of_le
    {q m : ℕ} (hqm : q ≤ m) :
    (q : ℝ) + ((m - q : ℕ) : ℝ) = (m : ℝ) := by
  have hnat : q + (m - q) = m := Nat.add_sub_of_le hqm
  exact_mod_cast hnat

theorem nat_cast_sub_add_sub_of_le
    {n q m : ℕ} (hnq : n ≤ q) (hqm : q ≤ m) :
    ((m - q : ℕ) : ℝ) + ((q - n : ℕ) : ℝ) =
      ((m - n : ℕ) : ℝ) := by
  have hnat : (m - q) + (q - n) = m - n := by omega
  exact_mod_cast hnat

theorem int_toNat_nat_add_sub_nat_add_of_le
    {N n ℓ : ℕ} (hℓn : ℓ ≤ n) :
    Int.toNat ((((N + n : ℕ) : ℤ) - ((N + ℓ : ℕ) : ℤ))) = n - ℓ := by
  let z : ℤ := ((N + n : ℕ) : ℤ) - ((N + ℓ : ℕ) : ℤ)
  have hdiff_nonneg :
      0 ≤ z := by
    dsimp [z]
    exact sub_nonneg.mpr (by exact_mod_cast Nat.add_le_add_left hℓn N)
  have hsub_cast :
      (((N + n - (N + ℓ) : ℕ) : ℤ) =
        ((N + n : ℕ) : ℤ) - ((N + ℓ : ℕ) : ℤ)) := by
    exact_mod_cast
      (Nat.cast_sub (Nat.add_le_add_left hℓn N) :
        ((N + n - (N + ℓ) : ℕ) : ℤ) =
          ((N + n : ℕ) : ℤ) - ((N + ℓ : ℕ) : ℤ))
  have hnat_sub : N + n - (N + ℓ) = n - ℓ := by
    omega
  have htoNat_cast :
      ((Int.toNat z : ℤ) : ℤ) = ((N + n - (N + ℓ) : ℕ) : ℤ) := by
    calc
      ((Int.toNat z : ℤ) : ℤ) = z := Int.toNat_of_nonneg hdiff_nonneg
      _ = ((N + n - (N + ℓ) : ℕ) : ℤ) := by
          dsimp [z]
          rw [hsub_cast]
          simp [Nat.cast_add]
  have htoNat : Int.toNat z = N + n - (N + ℓ) := by
    exact_mod_cast htoNat_cast
  change Int.toNat z = n - ℓ
  exact htoNat.trans hnat_sub

theorem descendantsAtScale_originCube_nat_shift_card
    {d : ℕ} {N m n : ℕ} (hnm : n ≤ m) :
    (descendantsAtScale
      (originCube d (((N + m : ℕ) : ℤ)))
      (((N + n : ℕ) : ℤ))).card =
      (3 ^ d) ^ (m - n) := by
  have hnm_int : ((N + n : ℕ) : ℤ) ≤ ((N + m : ℕ) : ℤ) := by
    exact_mod_cast Nat.add_le_add_left hnm N
  rw [descendantsAtScale_eq_descendantsAtDepth
    (originCube d (((N + m : ℕ) : ℤ))) hnm_int]
  rw [descendantsAtDepth_card]
  congr 1
  exact int_toNat_nat_add_sub_nat_add_of_le hnm

theorem descendantsAtScale_originCube_nat_card
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m) :
    (descendantsAtScale
      (originCube d ((m : ℕ) : ℤ))
      ((n : ℕ) : ℤ)).card =
      (3 ^ d) ^ (m - n) := by
  simpa using
    descendantsAtScale_originCube_nat_shift_card
      (d := d) (N := 0) (m := m) (n := n) hnm

theorem log_descendantsAtScale_originCube_nat_shift_card
    {d : ℕ} {N m n : ℕ} (hnm : n ≤ m) :
    Real.log
        (((descendantsAtScale
          (originCube d (((N + m : ℕ) : ℤ)))
          (((N + n : ℕ) : ℤ))).card : ℝ)) =
      ((m - n : ℕ) : ℝ) * Real.log ((3 ^ d : ℕ) : ℝ) := by
  rw [descendantsAtScale_originCube_nat_shift_card
    (d := d) (N := N) (m := m) (n := n) hnm]
  norm_num [Nat.cast_pow, Real.log_pow]

theorem log_descendantsAtScale_originCube_nat_card
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m) :
    Real.log
        (((descendantsAtScale
          (originCube d ((m : ℕ) : ℤ))
          ((n : ℕ) : ℤ)).card : ℝ)) =
      ((m - n : ℕ) : ℝ) * Real.log ((3 ^ d : ℕ) : ℝ) := by
  simpa using
    log_descendantsAtScale_originCube_nat_shift_card
      (d := d) (N := 0) (m := m) (n := n) hnm

theorem three_mul_log_three_pow_dim_pos
    {d : ℕ} [NeZero d] :
    0 < 3 * Real.log (((3 ^ d : ℕ) : ℝ)) := by
  have hd_ne : d ≠ 0 := NeZero.ne d
  have hpow_gt : (1 : ℝ) < ((3 ^ d : ℕ) : ℝ) := by
    exact_mod_cast
      (one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) hd_ne :
        (1 : ℕ) < 3 ^ d)
  have hlog_pos : 0 < Real.log (((3 ^ d : ℕ) : ℝ)) :=
    Real.log_pos hpow_gt
  positivity

theorem three_mul_log_normalizedProbeIndex_univ_card_pos
    {d : ℕ} [NeZero d] :
    0 <
      3 * Real.log (((Finset.univ : Finset (NormalizedProbeIndex d)).card : ℝ)) := by
  classical
  let α : BlockCoord d := Classical.choice (inferInstance : Nonempty (BlockCoord d))
  let i₁ : NormalizedProbeIndex d := (α, α, NormalizedProbeKind.coord)
  let i₂ : NormalizedProbeIndex d := (α, α, NormalizedProbeKind.plus)
  have hne : i₁ ≠ i₂ := by
    simp [i₁, i₂]
  have hpair : ({i₁, i₂} : Finset (NormalizedProbeIndex d)).card = 2 :=
    Finset.card_pair hne
  have hcard_two :
      2 ≤ (Finset.univ : Finset (NormalizedProbeIndex d)).card := by
    have hle :
        ({i₁, i₂} : Finset (NormalizedProbeIndex d)).card ≤
          (Finset.univ : Finset (NormalizedProbeIndex d)).card :=
      Finset.card_le_card (by intro x hx; simp)
    omega
  have hlog_pos :
      0 < Real.log (((Finset.univ : Finset (NormalizedProbeIndex d)).card : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast hcard_two)
  positivity

theorem three_mul_log_descendantsAtScale_originCube_nat_shift_card_eq
    {d : ℕ} [NeZero d] {N m n : ℕ} (hnm : n ≤ m) :
    3 *
        Real.log
          (((descendantsAtScale
            (originCube d (((N + m : ℕ) : ℤ)))
            (((N + n : ℕ) : ℤ))).card : ℝ)) =
      ((m - n : ℕ) : ℝ) *
        (3 * Real.log (((3 ^ d : ℕ) : ℝ))) := by
  rw [log_descendantsAtScale_originCube_nat_shift_card
    (d := d) (N := N) (m := m) (n := n) hnm]
  ring

theorem rpow_three_mul_log_descendantsAtScale_originCube_nat_shift_card
    {d : ℕ} [NeZero d] {τ : ℝ} {N m n : ℕ}
    (hnm : n < m) :
    (3 *
        Real.log
          (((descendantsAtScale
            (originCube d (((N + m : ℕ) : ℤ)))
            (((N + n : ℕ) : ℤ))).card : ℝ))) ^ τ⁻¹ =
      (((m - n : ℕ) : ℝ) ^ τ⁻¹) *
        ((3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹) := by
  have hgap_nonneg : 0 ≤ ((m - n : ℕ) : ℝ) := by
    positivity
  have hconst_nonneg :
      0 ≤ 3 * Real.log (((3 ^ d : ℕ) : ℝ)) :=
    (three_mul_log_three_pow_dim_pos (d := d)).le
  rw [three_mul_log_descendantsAtScale_originCube_nat_shift_card_eq
    (d := d) (N := N) (m := m) (n := n) (le_of_lt hnm)]
  rw [Real.mul_rpow hgap_nonneg hconst_nonneg]

theorem rpow_three_mul_log_descendantsAtScale_originCube_nat_shift_card_le_parent
    {d : ℕ} [NeZero d] {τ : ℝ} (hτ : 0 < τ)
    {N m n : ℕ} (hnm : n < m) :
    (3 *
        Real.log
          (((descendantsAtScale
            (originCube d (((N + m : ℕ) : ℤ)))
            (((N + n : ℕ) : ℤ))).card : ℝ))) ^ τ⁻¹ ≤
      ((m : ℝ) ^ τ⁻¹) *
        ((3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹) := by
  rw [rpow_three_mul_log_descendantsAtScale_originCube_nat_shift_card
    (d := d) (τ := τ) (N := N) (m := m) (n := n) hnm]
  have hgap_nonneg : 0 ≤ ((m - n : ℕ) : ℝ) := by
    positivity
  have hgap_le_m : ((m - n : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.sub_le m n
  have hexp_nonneg : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hgap_pow_le :
      ((m - n : ℕ) : ℝ) ^ τ⁻¹ ≤ (m : ℝ) ^ τ⁻¹ :=
    Real.rpow_le_rpow hgap_nonneg hgap_le_m hexp_nonneg
  exact mul_le_mul_of_nonneg_right hgap_pow_le
    (Real.rpow_pos_of_pos
      (three_mul_log_three_pow_dim_pos (d := d)) τ⁻¹).le

theorem shiftedEnvelopeDenominator_le_parentPower
    {d : ℕ} [NeZero d] {τ R K C θ : ℝ}
    (hτ : 0 < τ) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hC : 0 ≤ C)
    {N m n : ℕ} (hnm : n < m) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale
        (originCube d (((N + m : ℕ) : ℤ)))
        (((N + n : ℕ) : ℤ))
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    R * (K *
      (((3 * Real.log (S.card : ℝ)) ^ τ⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ τ⁻¹) *
          (C * θ ^ (2 : ℕ))))) ≤
      (R * (K *
        (((3 * Real.log (S.card : ℝ)) ^ τ⁻¹) *
          (((3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹) *
            (C * θ ^ (2 : ℕ)))))) *
        ((m : ℝ) ^ τ⁻¹) := by
  intro D S
  let Sfac : ℝ := (3 * Real.log (S.card : ℝ)) ^ τ⁻¹
  let Dfac : ℝ := (3 * Real.log (D.card : ℝ)) ^ τ⁻¹
  let Gfac : ℝ := (3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹
  let Mfac : ℝ := (m : ℝ) ^ τ⁻¹
  have hSbase : 0 < 3 * Real.log (S.card : ℝ) := by
    simpa [S] using three_mul_log_normalizedProbeIndex_univ_card_pos (d := d)
  have hSfac_nonneg : 0 ≤ Sfac := by
    dsimp [Sfac]
    exact (Real.rpow_pos_of_pos hSbase _).le
  have htheta_sq_nonneg : 0 ≤ θ ^ (2 : ℕ) := by positivity
  have hconst_nonneg :
      0 ≤ R * K * Sfac * (C * θ ^ (2 : ℕ)) := by positivity
  have hDfac_le : Dfac ≤ Mfac * Gfac := by
    simpa [D, Dfac, Mfac, Gfac] using
      rpow_three_mul_log_descendantsAtScale_originCube_nat_shift_card_le_parent
        (d := d) (τ := τ) hτ (N := N) (m := m) (n := n) hnm
  calc
    R * (K * (Sfac * (Dfac * (C * θ ^ (2 : ℕ)))))
        = R * K * Sfac * (C * θ ^ (2 : ℕ)) * Dfac := by ring
    _ ≤ R * K * Sfac * (C * θ ^ (2 : ℕ)) * (Mfac * Gfac) := by
        exact mul_le_mul_of_nonneg_left hDfac_le hconst_nonneg
    _ =
      (R * (K * (Sfac * (Gfac * (C * θ ^ (2 : ℕ)))))) * Mfac := by
        ring

theorem shiftedEnvelopeDenominator_le_parentAddOnePower
    {d : ℕ} [NeZero d] {τ R K C θ : ℝ}
    (hτ : 0 < τ) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hC : 0 ≤ C)
    {N m n : ℕ} (hnm : n < m) :
    let D : Finset (TriadicCube d) :=
      descendantsAtScale
        (originCube d (((N + m : ℕ) : ℤ)))
        (((N + n : ℕ) : ℤ))
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    R * (K *
      (((3 * Real.log (S.card : ℝ)) ^ τ⁻¹) *
        (((3 * Real.log (D.card : ℝ)) ^ τ⁻¹) *
          (C * θ ^ (2 : ℕ))))) ≤
      (R * (K *
        (((3 * Real.log (S.card : ℝ)) ^ τ⁻¹) *
          (((3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹) *
            (C * θ ^ (2 : ℕ)))))) *
        (((m : ℝ) + 1) ^ τ⁻¹) := by
  intro D S
  have hparent :=
    shiftedEnvelopeDenominator_le_parentPower
      (d := d) (τ := τ) (R := R) (K := K) (C := C) (θ := θ)
      hτ hR hK hC (N := N) (m := m) (n := n) hnm
  dsimp only at hparent ⊢
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hm_le : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hinv_nonneg : 0 ≤ τ⁻¹ := inv_nonneg.mpr hτ.le
  have hpow_le : (m : ℝ) ^ τ⁻¹ ≤ ((m : ℝ) + 1) ^ τ⁻¹ :=
    Real.rpow_le_rpow hm_nonneg hm_le hinv_nonneg
  have hconst_nonneg :
      0 ≤
        R *
          (K *
            (((3 * Real.log (S.card : ℝ)) ^ τ⁻¹) *
              (((3 * Real.log (((3 ^ d : ℕ) : ℝ))) ^ τ⁻¹) *
                (C * θ ^ (2 : ℕ))))) := by
    have hSbase : 0 < 3 * Real.log (S.card : ℝ) := by
      simpa [S] using three_mul_log_normalizedProbeIndex_univ_card_pos (d := d)
    have hGbase : 0 < 3 * Real.log (((3 ^ d : ℕ) : ℝ)) :=
      three_mul_log_three_pow_dim_pos (d := d)
    positivity
  exact hparent.trans (mul_le_mul_of_nonneg_left hpow_le hconst_nonneg)

end

end Section57
end Ch05
end Book
end Homogenization
