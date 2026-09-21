/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.HilbertSchmidtPairing
public import Mathlib.Tactic

/-!
# Algebraic closure of the nonnegative-Ricci almost-Schur estimate

Once geometry supplies the contracted-Bianchi pairing estimate and Bochner
supplies the trace-free Hessian bound, the sharp dimensional constant follows
by elementary algebra.  Isolating that cancellation here keeps the final
geometric theorem free of hidden division or zero-case assumptions.
-/

@[expose] public noncomputable section

namespace AlmostSchur

/-- The contracted-Bianchi pairing identity and Cauchy--Schwarz imply the
scaled pairing estimate used by the final cancellation. -/
theorem almostSchur_pairing_reduction {d A B H P : ℝ}
    (hidentity : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H) :
    (d - 2) ^ 2 * A ^ 2 ≤ 4 * d ^ 2 * B * H := by
  calc
    (d - 2) ^ 2 * A ^ 2 = ((d - 2) * A) ^ 2 := by ring
    _ = (2 * d * P) ^ 2 := by rw [hidentity]
    _ = 4 * d ^ 2 * P ^ 2 := by ring
    _ ≤ 4 * d ^ 2 * (B * H) :=
      mul_le_mul_of_nonneg_left hcauchy (by positivity)
    _ = 4 * d ^ 2 * B * H := by ring

/-- The integrated Bochner identity, nonnegative Ricci term, and exact
trace-free Hessian decomposition imply the required Hessian-energy bound. -/
theorem almostSchur_bochner_reduction {d A Hess Ric H : ℝ}
    (hd : 0 ≤ d) (hbochner : Hess + Ric = A) (hRic : 0 ≤ Ric)
    (htrace : d * H = d * Hess - A) :
    d * H ≤ (d - 1) * A := by
  nlinarith [mul_nonneg hd hRic]

/-- Polynomial form of the final cancellation.  Here `A` is the scalar
curvature variance, `B` the trace-free Ricci energy, and `H` the trace-free
Hessian energy. -/
theorem almostSchur_scaled_algebra {d A B H : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair : (d - 2) ^ 2 * A ^ 2 ≤ 4 * d ^ 2 * B * H)
    (hbochner : d * H ≤ (d - 1) * A) :
    (d - 2) ^ 2 * A ≤ 4 * d * (d - 1) * B := by
  by_cases hAz : A = 0
  · have hd0 : 0 ≤ d := (by linarith)
    have hd1 : 0 ≤ d - 1 := (by linarith)
    simpa [hAz] using mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hd0) hd1) hB
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hmult :
      4 * d ^ 2 * B * H ≤ (4 * d * (d - 1) * B) * A := by
    have hm := mul_le_mul_of_nonneg_left hbochner
      (mul_nonneg (mul_nonneg (by positivity) (by linarith : 0 ≤ d)) hB)
    nlinarith
  have hcancel :
      ((d - 2) ^ 2 * A) * A ≤ (4 * d * (d - 1) * B) * A := by
    nlinarith [hpair.trans hmult]
  exact le_of_mul_le_mul_right hcancel hApos

/-- The usual sharp dimensional constant
`4 d (d-1) / (d-2)^2` in the nonnegative-Ricci case. -/
theorem almostSchur_constant_algebra {d A B H : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpair : (d - 2) ^ 2 * A ^ 2 ≤ 4 * d ^ 2 * B * H)
    (hbochner : d * H ≤ (d - 1) * A) :
    A ≤ (4 * d * (d - 1) / (d - 2) ^ 2) * B := by
  have hden : 0 < (d - 2) ^ 2 := sq_pos_of_pos (sub_pos.mpr hd)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hden).2
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using
      almostSchur_scaled_algebra hd hA hB hpair hbochner)

/-- One-shot algebraic endpoint from the two identities delivered by geometry
and analysis. -/
theorem almostSchur_from_identities {d A B Hess Ric H P : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRic : 0 ≤ Ric)
    (hcontracted : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H)
    (hbochner : Hess + Ric = A)
    (htrace : d * H = d * Hess - A) :
    A ≤ (4 * d * (d - 1) / (d - 2) ^ 2) * B :=
  almostSchur_constant_algebra hd hA hB
    (almostSchur_pairing_reduction hcontracted hcauchy)
    (almostSchur_bochner_reduction (by linarith) hbochner hRic htrace)

/-- Equality of the trace-free Ricci energy to zero forces zero scalar
variance through the almost-Schur estimate. -/
theorem scalar_variance_eq_zero_of_almostSchur {d A B : ℝ}
    (_hd : 2 < d) (hA : 0 ≤ A) (hB : B = 0)
    (hbound : A ≤ (4 * d * (d - 1) / (d - 2) ^ 2) * B) :
    A = 0 := by
  rw [hB, mul_zero] at hbound
  exact le_antisymm hbound hA

/-! ## Equality algebra -/

theorem hilbertSchmidtSq_sub_smul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V →L[ℝ] V) (c : ℝ) :
    hilbertSchmidtSq (A - c • B) =
      hilbertSchmidtSq A - 2 * c * hilbertSchmidtInner B A +
        c ^ 2 * hilbertSchmidtSq B := by
  let b := stdOrthonormalBasis ℝ V
  rw [hilbertSchmidtSq_eq_sum_sq (A - c • B) b,
    hilbertSchmidtSq_eq_sum_sq A b, hilbertSchmidtSq_eq_sum_sq B b,
    hilbertSchmidtInner_eq_sum_mul B A b]
  simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left]
  simp_rw [sub_eq_add_neg, add_sq]
  simp_rw [Finset.sum_add_distrib]
  have hsum (k : ℝ) (f : Fin (Module.finrank ℝ V) →
      Fin (Module.finrank ℝ V) → ℝ) :
      (∑ x, ∑ y, k * f x y) = k * (∑ x, ∑ y, f x y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  have hcross :
      (∑ x, ∑ y, 2 * inner ℝ (A (b x)) (b y) *
        -(c * inner ℝ (B (b x)) (b y))) =
      -(2 * c * (∑ x, ∑ y, inner ℝ (B (b x)) (b y) *
        inner ℝ (A (b x)) (b y))) := by
    calc
      (∑ x, ∑ y, 2 * inner ℝ (A (b x)) (b y) *
          -(c * inner ℝ (B (b x)) (b y))) =
          ∑ x, ∑ y, (-2 * c) *
            (inner ℝ (B (b x)) (b y) * inner ℝ (A (b x)) (b y)) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (-2 * c) * (∑ x, ∑ y, inner ℝ (B (b x)) (b y) *
          inner ℝ (A (b x)) (b y)) := hsum _ _
      _ = _ := by ring
  have hsq :
      (∑ x, ∑ y, (-(c * inner ℝ (B (b x)) (b y))) ^ 2) =
      c ^ 2 * (∑ x, ∑ y, inner ℝ (B (b x)) (b y) ^ 2) := by
    calc
      (∑ x, ∑ y, (-(c * inner ℝ (B (b x)) (b y))) ^ 2) =
          ∑ x, ∑ y, c ^ 2 * inner ℝ (B (b x)) (b y) ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = _ := hsum _ _
  rw [hcross, hsq]

theorem almostSchur_equality_data {d A B Hess Ric H P : ℝ}
    (hd : 2 < d) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRic : 0 ≤ Ric)
    (hcontracted : (d - 2) * A = 2 * d * P)
    (hcauchy : P ^ 2 ≤ B * H)
    (hbochner : Hess + Ric = A)
    (htrace : d * H = d * Hess - A)
    (heq : A = (4 * d * (d - 1) / (d - 2) ^ 2) * B) :
    B = 0 ∨
      (0 < A ∧ 0 < B ∧ d * H = (d - 1) * A ∧ Ric = 0 ∧
        P ^ 2 = B * H ∧ (d - 2) * P = 2 * (d - 1) * B) := by
  have hboch : d * H ≤ (d - 1) * A :=
    almostSchur_bochner_reduction (by linarith) hbochner hRic htrace
  have hpair := almostSchur_pairing_reduction hcontracted hcauchy
  have hden : 0 < (d - 2) ^ 2 := sq_pos_of_pos (sub_pos.mpr hd)
  by_cases hAz : A = 0
  · left
    have hd1 : 0 < d - 1 := by linarith
    have hfac : 0 < 4 * d * (d - 1) / (d - 2) ^ 2 := by positivity
    rw [hAz] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left hfac.ne'
  · right
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have heq' : (d - 2) ^ 2 * A = 4 * d * (d - 1) * B := by
      calc
        (d - 2) ^ 2 * A = (d - 2) ^ 2 *
            ((4 * d * (d - 1) / (d - 2) ^ 2) * B) := by rw [heq]
        _ = 4 * d * (d - 1) * B := by
          field_simp [hden.ne', sub_ne_zero.mpr (by linarith : d ≠ 2)]
    have hBpos : 0 < B := by
      by_contra hBz
      have hBzero : B = 0 := le_antisymm (not_lt.mp hBz) hB
      rw [hBzero] at heq'
      nlinarith
    have hmul : 4 * d * B * (d * H) ≤
        4 * d * B * ((d - 1) * A) := by
      exact mul_le_mul_of_nonneg_left hboch (by positivity)
    have hupper : 4 * d ^ 2 * B * H ≤
        (d - 2) ^ 2 * A ^ 2 := by
      calc
        4 * d ^ 2 * B * H = 4 * d * B * (d * H) := by ring
        _ ≤ 4 * d * B * ((d - 1) * A) := hmul
        _ = (d - 2) ^ 2 * A ^ 2 := by
          calc
            4 * d * B * ((d - 1) * A) =
                (4 * d * (d - 1) * B) * A := by ring
            _ = ((d - 2) ^ 2 * A) * A := by rw [heq']
            _ = (d - 2) ^ 2 * A ^ 2 := by ring
    have hpair_eq : (d - 2) ^ 2 * A ^ 2 = 4 * d ^ 2 * B * H :=
        le_antisymm hpair hupper
    have hmul_eq : 4 * d * B * (d * H) =
        4 * d * B * ((d - 1) * A) := by
      have hreverse : 4 * d * B * ((d - 1) * A) =
          4 * d * B * (d * H) := by
        calc
          4 * d * B * ((d - 1) * A) =
              (4 * d * (d - 1) * B) * A := by ring
          _ = ((d - 2) ^ 2 * A) * A := by rw [heq']
          _ = (d - 2) ^ 2 * A ^ 2 := by ring
          _ = 4 * d ^ 2 * B * H := hpair_eq
          _ = 4 * d * B * (d * H) := by ring
      exact le_antisymm hmul hreverse.le
    have hfactor : 0 < 4 * d * B := by positivity
    have hH : d * H = (d - 1) * A :=
      mul_left_cancel₀ hfactor.ne' hmul_eq
    have hHess : Hess = A := by
      apply mul_left_cancel₀ (by positivity : (d : ℝ) ≠ 0)
      nlinarith [htrace, hH]
    have hRic0 : Ric = 0 := by linarith [hbochner, hHess]
    have hp : (d - 2) ^ 2 * A ^ 2 = 4 * d ^ 2 * P ^ 2 := by
      calc
        (d - 2) ^ 2 * A ^ 2 = ((d - 2) * A) ^ 2 := by ring
        _ = (2 * d * P) ^ 2 := by rw [hcontracted]
        _ = 4 * d ^ 2 * P ^ 2 := by ring
    have hP : 4 * d ^ 2 * P ^ 2 = 4 * d ^ 2 * (B * H) := by
      simpa [mul_assoc] using hp.symm.trans hpair_eq
    have hP' : P ^ 2 = B * H :=
      mul_left_cancel₀ (by positivity : (4 * d ^ 2 : ℝ) ≠ 0) hP
    have hscale : (d - 2) * P = 2 * (d - 1) * B := by
      have hscale' : 2 * d * ((d - 2) * P) =
          2 * d * (2 * (d - 1) * B) := by
        calc
          2 * d * ((d - 2) * P) = (d - 2) * (2 * d * P) := by ring
          _ = (d - 2) * ((d - 2) * A) := by rw [← hcontracted]
          _ = (d - 2) ^ 2 * A := by ring
          _ = 4 * d * (d - 1) * B := heq'
          _ = 2 * d * (2 * (d - 1) * B) := by ring
      exact mul_left_cancel₀ (by positivity : (2 * d : ℝ) ≠ 0) hscale'
    exact ⟨hApos, hBpos, hH, hRic0, hP', hscale⟩

end AlmostSchur
