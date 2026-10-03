/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Logistic
public import LeanPool.Zeta5Irrational.Andreief

/-! the proof notes, §5.2: Heine determinant integral and absolute-value bound.

Every entry of `X • B + A` at `X = C_r` is `∫ t^i · t^k (t R_n)(t) w(y) dy` with `t = 1/2 + iy`
(`logistic_representation`). Andréief's identity turns the determinant into
`(1/h!) ∫ det[t_j^i] · det[t_j^i (tR_n)(t_j) w(y_j)] dy`; both determinants are Vandermonde
determinants in `t_j = 1/2 + i y_j`, and `|t_j − t_l| = |y_j − y_l|`, which gives `HeineBound`.
The statement `HeineBound` of `Interfaces.lean` is proved literally, for every `r` and `n`
(including `n = 0`). -/

public section

open MeasureTheory Finset Polynomial Matrix

namespace Zeta32.Analytic

open Zeta32.Analytic.Contour

noncomputable section

/-- The one-point factor `(t R_n)(t) w(y)` of `heineIntegrand`, `t = 1/2 + iy`. -/
def heinePhi (r : ℚ) (n : ℕ) (y : ℝ) : ℂ := tpt y * Rfun n (tpt y) * wfun r y

/-- Andréief row functions `t^i`. -/
def heineF (n : ℕ) : Fin (3*n) → ℝ → ℂ := fun i y => tpt y ^ (i : ℕ)

/-- Andréief column functions `t^k (t R_n)(t) w(y)`. -/
def heineG (r : ℚ) (n : ℕ) : Fin (3*n) → ℝ → ℂ := fun k y => tpt y ^ (k : ℕ) * heinePhi r n y

lemma heineF_mul_heineG (r : ℚ) (n : ℕ) (i k : Fin (3 * n)) (y : ℝ) :
    heineF n i y * heineG r n k y =
      tpt y * (tpt y ^ (i.val + k.val) * Rfun n (tpt y)) * wfun r y := by
  unfold heineF heineG heinePhi
  rw [pow_add]
  ring

/-- `Q_n(C_r)` as the determinant of the complex entries `C_r · slope + intercept`. -/
lemma heine_aeval_Q_eq_det (r : ℚ) (n : ℕ) :
    ((aeval (Cr r) (Q r n) : ℝ) : ℂ) =
      (Matrix.of fun i k : Fin (3*n) => ((Cr r : ℝ) : ℂ) * (slope n (i.val + k.val) : ℂ) +
        (intercept r n (i.val + k.val) : ℂ)).det := by
  rw [Q, AlgHom.map_det, show ∀ x : ℝ, (x : ℂ) = Complex.ofRealHom x from fun _ => rfl,
    RingHom.map_det]
  congr 1
  ext i k
  simp [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, B, A]
  ring

/-- **Heine identity**: `Q_n(C_r) = (1/h!) ∫ det[t_j^i] det[t_j^i (tR_n)(t_j) w(y_j)] dy`. -/
theorem heine_identity (r : ℚ) (n : ℕ) :
    ((aeval (Cr r) (Q r n) : ℝ) : ℂ) =
      (1 / ((3*n).factorial : ℂ)) * ∫ x : Fin (3*n) → ℝ,
        (Matrix.of fun i j => heineF n i (x j)).det *
          (Matrix.of fun i j => heineG r n i (x j)).det := by
  rw [heine_aeval_Q_eq_det]
  have hent : (Matrix.of fun i k : Fin (3*n) => ((Cr r : ℝ) : ℂ) * (slope n (i.val + k.val) : ℂ) +
      (intercept r n (i.val + k.val) : ℂ)) =
      Matrix.of fun i k => ∫ y, heineF n i y * heineG r n k y := by
    ext i k
    simp only [Matrix.of_apply, heineF_mul_heineG, logistic_representation]
  rw [hent, Zeta5Irrational.AndreiefGeneral.andreief (μ := volume) _ _ (fun i k => by
    simp_rw [heineF_mul_heineG]; exact logistic_integrable_entry r n _)]
  rfl

lemma heine_det_F (n : ℕ) (x : Fin (3 * n) → ℝ) :
    (Matrix.of fun i j => heineF n i (x j)).det =
      ∏ i : Fin (3*n), ∏ j ∈ Ioi i, (tpt (x j) - tpt (x i)) := by
  have h : (Matrix.of fun i j => heineF n i (x j)) = (vandermonde fun j => tpt (x j))ᵀ := by
    ext i j
    simp [heineF, vandermonde_apply]
  rw [h, det_transpose, det_vandermonde]

lemma heine_det_G (r : ℚ) (n : ℕ) (x : Fin (3 * n) → ℝ) :
    (Matrix.of fun i j => heineG r n i (x j)).det =
      (∏ j, heinePhi r n (x j)) * (Matrix.of fun i j => heineF n i (x j)).det := by
  rw [← det_mul_row]
  congr 1
  ext i j
  simp only [Matrix.of_apply, heineG, heineF]
  ring

lemma heine_tpt_sub (a b : ℝ) : tpt a - tpt b = Complex.I * ((a - b : ℝ) : ℂ) := by
  unfold tpt; push_cast; ring

lemma heine_norm_vandermonde_sq {m : ℕ} (x : Fin m → ℝ) :
    ‖∏ i : Fin m, ∏ j ∈ Ioi i, (tpt (x j) - tpt (x i))‖ ^ 2 =
      ∏ l, ∏ l' ∈ Finset.univ.filter (fun l' => l < l'), (x l - x l') ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hf : Finset.univ.filter (fun l' => i < l') = Ioi i := by ext; simp
  rw [norm_prod, ← Finset.prod_pow, hf]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [heine_tpt_sub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

lemma heine_norm_integrand (r : ℚ) (n : ℕ) (x : Fin (3 * n) → ℝ) :
    ‖(Matrix.of fun i j => heineF n i (x j)).det *
        (Matrix.of fun i j => heineG r n i (x j)).det‖ = heineIntegrand r n x := by
  rw [heine_det_G, heine_det_F, norm_mul, norm_mul, ← mul_assoc, mul_comm _ ‖∏ j, heinePhi r n
    (x j)‖,
    mul_assoc, ← sq, heine_norm_vandermonde_sq, norm_prod]
  rfl

/-- **the proof notes, 5.2 (Heine), bound form.** -/
theorem heine_bound : ∀ (r : ℚ) (n : ℕ), HeineBound r n := by
  intro r n
  unfold HeineBound
  rw [← Real.norm_eq_abs, ← Complex.norm_real, heine_identity, norm_mul]
  have hf : ‖(1 / ((3*n).factorial : ℂ))‖ = 1 / ((3*n).factorial : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hf]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  simp_rw [heine_norm_integrand]

end

end Zeta32.Analytic

end
