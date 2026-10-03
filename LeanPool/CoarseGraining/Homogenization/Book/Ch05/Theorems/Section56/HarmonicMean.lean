/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.MatrixOrderBridge
public import Mathlib.Tactic.NoncommRing

/-! # Harmonic Mean -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators MatrixOrder

noncomputable section

/-!
# A finite matrix arithmetic-harmonic mean identity

This file records the elementary matrix identity behind the Section 5.6
small-contrast replacement of the harmonic mean by the arithmetic mean.
-/

/-- The arithmetic mean of a finite sequence of square real matrices. -/
noncomputable def matrixArithmeticMean {N d : ℕ} (b : Fin N → Mat d) : Mat d :=
  (N : ℝ)⁻¹ • ∑ i, b i

/-- The harmonic mean of a finite sequence of square real matrices. -/
noncomputable def matrixHarmonicMean {N d : ℕ} (b : Fin N → Mat d) : Mat d :=
  ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹)⁻¹

private theorem natCast_pos_of_neZero (N : ℕ) [NeZero N] : 0 < (N : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private theorem matrixAverage_inv_posDef {N d : ℕ} [NeZero N]
    {b : Fin N → Mat d} (hb : ∀ i, (b i).PosDef) :
    ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹).PosDef := by
  classical
  have hsum : (∑ i : Fin N, (b i)⁻¹).PosDef :=
    Matrix.posDef_sum (s := Finset.univ) Finset.univ_nonempty
      (fun i _hi => (hb i).inv)
  exact hsum.smul (inv_pos.mpr (natCast_pos_of_neZero N))

/-- The harmonic mean of positive definite matrices is positive definite. -/
theorem matrixHarmonicMean_posDef {N d : ℕ} [NeZero N]
    {b : Fin N → Mat d} (hb : ∀ i, (b i).PosDef) :
    (matrixHarmonicMean b).PosDef := by
  simp [matrixHarmonicMean, (matrixAverage_inv_posDef (b := b) hb).inv]

private theorem matrixHarmonicMean_inv_eq_average_inv {N d : ℕ} [NeZero N]
    {b : Fin N → Mat d} (hb : ∀ i, (b i).PosDef) :
    (matrixHarmonicMean b)⁻¹ = (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹ := by
  let S : Mat d := (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹
  have hS : S.PosDef := by
    simpa [S] using matrixAverage_inv_posDef (b := b) hb
  let _ := hS.isUnit.invertible
  change S⁻¹⁻¹ = S
  exact Matrix.inv_inv_of_invertible S

private theorem inv_natCast_smul_sum_const {N d : ℕ} [NeZero N] (G : Mat d) :
    (N : ℝ)⁻¹ • (∑ _i : Fin N, G) = G := by
  rw [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (natCast_pos_of_neZero N)), one_smul]

private theorem inv_natCast_smul_sum_mul_left_right {N d : ℕ} [NeZero N]
    (G : Mat d) (A : Fin N → Mat d) :
    (N : ℝ)⁻¹ • (∑ i, G * A i * G) =
      G * ((N : ℝ)⁻¹ • ∑ i, A i) * G := by
  calc
    (N : ℝ)⁻¹ • (∑ i, G * A i * G)
        = ∑ i, (N : ℝ)⁻¹ • (G * A i * G) := by
          rw [Finset.smul_sum]
    _ = ∑ i, G * ((N : ℝ)⁻¹ • A i) * G := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [Matrix.mul_assoc]
    _ = G * (∑ i, (N : ℝ)⁻¹ • A i) * G := by
          simp [Matrix.mul_sum, Matrix.sum_mul]
    _ = G * ((N : ℝ)⁻¹ • ∑ i, A i) * G := by
          rw [Finset.smul_sum]

private theorem quadratic_term_expand {d : ℕ} {B G : Mat d} (hB : B.PosDef) :
    (B - G) * B⁻¹ * (B - G) = B - G - G + G * B⁻¹ * G := by
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det (A := B)).mp hB.isUnit
  have hright : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hleft : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  noncomm_ring [hright, hleft]

private theorem harmonic_quadratic_term_expand {d : ℕ} {H G S : Mat d}
    (hH : H.PosDef) (hHinv : H⁻¹ = S) :
    (H - G) * H⁻¹ * (H - G) = H - G - G + G * S * G := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det (A := H)).mp hH.isUnit
  have hright : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hleft : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hexpand :
      (H - G) * H⁻¹ * (H - G) = H - G - G + G * H⁻¹ * G := by
    noncomm_ring [hright, hleft]
  rw [hexpand, hHinv]

private theorem average_quadratic_terms_expand {N d : ℕ} [NeZero N]
    {b : Fin N → Mat d} (G : Mat d) (hb : ∀ i, (b i).PosDef) :
    (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) =
      matrixArithmeticMean b - G - G +
        G * ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹) * G := by
  calc
    (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G))
        = (N : ℝ)⁻¹ •
            (∑ i, (b i - G - G + G * (b i)⁻¹ * G)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact quadratic_term_expand (G := G) (hb i)
    _ = (N : ℝ)⁻¹ •
          ((∑ i, b i) - (∑ _i : Fin N, G) - (∑ _i : Fin N, G) +
            ∑ i, G * (b i)⁻¹ * G) := by
          congr 1
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (N : ℝ)⁻¹ • (∑ i, b i) -
          (N : ℝ)⁻¹ • (∑ _i : Fin N, G) -
          (N : ℝ)⁻¹ • (∑ _i : Fin N, G) +
          (N : ℝ)⁻¹ • (∑ i, G * (b i)⁻¹ * G) := by
          simp [sub_eq_add_neg, smul_add]
    _ = matrixArithmeticMean b - G - G +
          G * ((N : ℝ)⁻¹ • ∑ i, (b i)⁻¹) * G := by
          rw [matrixArithmeticMean]
          rw [inv_natCast_smul_sum_const G]
          rw [inv_natCast_smul_sum_mul_left_right]

/-- Exact arithmetic-harmonic mean identity with an arbitrary comparison matrix. -/
theorem matrixArithmeticMean_eq_matrixHarmonicMean_add_average_quadratic_sub
    {N d : ℕ} [NeZero N] (b : Fin N → Mat d) (G : Mat d)
    (hb : ∀ i, (b i).PosDef) :
    matrixArithmeticMean b =
      matrixHarmonicMean b +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (matrixHarmonicMean b - G) * (matrixHarmonicMean b)⁻¹ *
            (matrixHarmonicMean b - G) := by
  let H : Mat d := matrixHarmonicMean b
  let S : Mat d := (N : ℝ)⁻¹ • ∑ i, (b i)⁻¹
  have hH : H.PosDef := by
    simpa [H] using matrixHarmonicMean_posDef (b := b) hb
  have hHinv : H⁻¹ = S := by
    simpa [H, S] using matrixHarmonicMean_inv_eq_average_inv (b := b) hb
  have hAvg := average_quadratic_terms_expand (b := b) G hb
  have hHquad := harmonic_quadratic_term_expand (H := H) (G := G) (S := S) hH hHinv
  calc
    matrixArithmeticMean b =
        H + (matrixArithmeticMean b - G - G + G * S * G) -
          (H - G - G + G * S * G) := by
          noncomm_ring
    _ = H +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (H - G) * H⁻¹ * (H - G) := by
          rw [← hAvg, ← hHquad]
    _ = matrixHarmonicMean b +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) -
          (matrixHarmonicMean b - G) * (matrixHarmonicMean b)⁻¹ *
            (matrixHarmonicMean b - G) := by
          rfl

private theorem harmonicMean_quadratic_posSemidef {N d : ℕ} [NeZero N]
    {b : Fin N → Mat d} {G : Mat d} (hb : ∀ i, (b i).PosDef) (hG : G.IsSymm) :
    ((matrixHarmonicMean b - G) * (matrixHarmonicMean b)⁻¹ *
      (matrixHarmonicMean b - G)).PosSemidef := by
  let H : Mat d := matrixHarmonicMean b
  have hH : H.PosDef := by
    simpa [H] using matrixHarmonicMean_posDef (b := b) hb
  have hHsymm : H.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm, H] using hH.isHermitian
  have hKherm : (H - G).IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hHsymm.sub hG
  have hPSD :
      (Matrix.conjTranspose (H - G) * H⁻¹ * (H - G)).PosSemidef :=
    hH.inv.posSemidef.conjTranspose_mul_mul_same (H - G)
  change ((H - G) * H⁻¹ * (H - G)).PosSemidef
  have hterm :
      Matrix.conjTranspose (H - G) * H⁻¹ * (H - G) =
        (H - G) * H⁻¹ * (H - G) := by
    rw [hKherm.eq]
  exact hterm ▸ hPSD

/-- Dropping the nonnegative harmonic square gives the first Loewner inequality. -/
theorem matrixArithmeticMean_le_matrixHarmonicMean_add_average_quadratic
    {N d : ℕ} [NeZero N] (b : Fin N → Mat d) (G : Mat d)
    (hb : ∀ i, (b i).PosDef) (hG : G.IsSymm) :
    matrixArithmeticMean b ≤
      matrixHarmonicMean b +
        (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) := by
  rw [Matrix.le_iff]
  have hId :=
    matrixArithmeticMean_eq_matrixHarmonicMean_add_average_quadratic_sub
      (b := b) G hb
  have hPSD := harmonicMean_quadratic_posSemidef (b := b) (G := G) hb hG
  convert hPSD using 1
  all_goals first
    | rfl
    | (rw [hId]; noncomm_ring)

/-- The comparison form used to replace the harmonic mean by the arithmetic mean. -/
theorem matrixArithmeticMean_sub_matrixHarmonicMean_le_average_quadratic
    {N d : ℕ} [NeZero N] (b : Fin N → Mat d) (G : Mat d)
    (hb : ∀ i, (b i).PosDef) (hG : G.IsSymm) :
    matrixArithmeticMean b - matrixHarmonicMean b ≤
      (N : ℝ)⁻¹ • (∑ i, (b i - G) * (b i)⁻¹ * (b i - G)) := by
  rw [Matrix.le_iff]
  have hId :=
    matrixArithmeticMean_eq_matrixHarmonicMean_add_average_quadratic_sub
      (b := b) G hb
  have hPSD := harmonicMean_quadratic_posSemidef (b := b) (G := G) hb hG
  convert hPSD using 1
  all_goals first
    | rfl
    | (rw [hId]; noncomm_ring)

end

end Section56
end Ch05
end Book
end Homogenization
