/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta5Irrational.Arith.CoefficientMatrix
public import LeanPool.Zeta32.Arith.Small.Bern

/-! the proof notes, §7: the unitriangular change `t^i ↦ i!·binom(t,i)` gives
`Q_n/F_n = det[U_r(binom(t,a) binom(t,b) R_n)]`, and with one factor `S_n` per row,
`Qtilde r n = det[U_r(S_n D_n^4 binom(t,a) binom(t,b) / D_{5n})]`. -/

public section

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/NumeratorFunctional.lean
-- (linearity in the numerator), .../Base/Gram.lean (Gram basis change) and
-- .../Base/DecayNormalization.lean (binomial normalization `Qtilde = det binomGram`), which
-- are in turn
-- adapted from Apery/Arith/BasisChange.lean in mo271/Zeta5 by Moritz Firsching (Apache-2.0).
-- the functional is our `U_r` (poles `2jX + β_j`), layout (4,5,3).

open Polynomial
open scoped BigOperators
namespace Zeta32.Arith.Small
open Zeta32
noncomputable section

/-- The functional `U_r` on `F / D_{5n}`: polynomial part plus simple poles `U_r(1/(t+j)) = 2jX
+ β_j`. -/
@[expose]
def Ufun (r : ℚ) (n : ℕ) (F : ℚ[X]) : ℚ[X] :=
  C (polynomialMoment r (F /ₘ D (5*n))) +
    ∑ j ∈ Finset.Icc 1 (5*n),
      C (F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, ((l:ℚ)-(j:ℚ))) *
        (C (2*(j:ℚ)) * X + C (beta r j))

lemma divByMonic_add {q : ℚ[X]} (hq : q.Monic) (F G : ℚ[X]) :
    (F+G) /ₘ q = F /ₘ q + G /ₘ q := by
  refine (div_modByMonic_unique (F /ₘ q + G /ₘ q) (F %ₘ q + G %ₘ q) hq ⟨?_, ?_⟩).1
  · have hF := modByMonic_add_div F q
    have hG := modByMonic_add_div G q
    rw [mul_add]
    linear_combination hF + hG
  · exact (degree_add_le _ _).trans_lt
      (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (F : ℚ[X]) :
    (C c * F) /ₘ q = C c * (F /ₘ q) := by
  refine (div_modByMonic_unique (C c * (F /ₘ q)) (C c * (F %ₘ q)) hq ⟨?_, ?_⟩).1
  · have hF := modByMonic_add_div F q
    linear_combination C c * hF
  · rw [← smul_eq_C_mul]
    exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma Ufun_add (r : ℚ) (n : ℕ) (F G : ℚ[X]) :
    Ufun r n (F+G) = Ufun r n F + Ufun r n G := by
  unfold Ufun
  rw [divByMonic_add (D_monic _), polynomialMoment_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma Ufun_C_mul (r : ℚ) (n : ℕ) (c : ℚ) (F : ℚ[X]) :
    Ufun r n (C c * F) = C c * Ufun r n F := by
  unfold Ufun
  rw [divByMonic_C_mul (D_monic _), polynomialMoment_C_mul, map_mul, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]
  ring

lemma Ufun_sum {ι : Type*} (r : ℚ) (n : ℕ) (s : Finset ι) (F : ι → ℚ[X]) :
    Ufun r n (∑ i ∈ s, F i) = ∑ i ∈ s, Ufun r n (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := Ufun_C_mul r n 0 0
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Ufun_add, ih]

theorem Ufun_entry (r : ℚ) (n k : ℕ) :
    Ufun r n (numerator n k) = X * C (slope n k) + C (intercept r n k) := by
  unfold Ufun intercept slope polynomialPart residue
  simp only [mul_add, ← mul_assoc, ← C_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [← map_sum, map_add]
  ring

/-! ### Gram basis change -/

/-- Coefficient matrix of a finite family of polynomials. -/
noncomputable abbrev coeffMat {h : ℕ} (E : Fin h → ℚ[X]) :
    Matrix (Fin h) (Fin h) ℚ := Zeta5Irrational.coeffMat E

lemma sum_coeffMat {h : ℕ} (E : Fin h → ℚ[X])
    (hE : ∀ a, (E a).natDegree < h) (a : Fin h) :
    E a = ∑ k : Fin h, C (coeffMat E a k) * X ^ (k : ℕ) :=
  Zeta5Irrational.sum_coeffMat E hE a

/-- Hankel matrix obtained by applying `Ufun` to shifted copies of `R`. -/
def hankelFor (r : ℚ) (n h : ℕ) (R : ℚ[X]) : Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => Ufun r n (R * X^(i.val+j.val))

theorem gram_basis_change (r : ℚ) (n h : ℕ) (R : ℚ[X]) (E : Fin h → ℚ[X])
    (hE : ∀ a, (E a).natDegree < h) :
    (Matrix.of fun a b => Ufun r n (R * E a * E b)).det =
      C ((coeffMat E).det^2) * (hankelFor r n h R).det := by
  let T := (coeffMat E).map (C : ℚ →+* ℚ[X])
  have hM : (Matrix.of fun a b => Ufun r n (R * E a * E b)) =
      T * hankelFor r n h R * T.transpose := by
    apply Matrix.ext
    intro a b
    have he : R * E a * E b = ∑ k : Fin h, ∑ l : Fin h,
        C (coeffMat E a k * coeffMat E b l) * (R * X^(k.val+l.val)) := by
      rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [C_mul, pow_add]
      ring
    rw [Matrix.of_apply, he, Ufun_sum]
    simp only [Ufun_sum, Ufun_C_mul, Matrix.mul_apply,
      Matrix.transpose_apply, T, Matrix.map_apply, hankelFor, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [C_mul]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  dsimp only [T]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_pow]
  ring

lemma hankelFor_original (r : ℚ) (n : ℕ) : hankelFor r n (3*n) ((D n)^4) =
    (X:ℚ[X]) • (B n).map C + (A r n).map C := by
  apply Matrix.ext
  intro i j
  simp only [hankelFor, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, B, A, smul_eq_mul]
  rw [mul_comm ((D n)^4)]
  exact Ufun_entry r n (i.val+j.val)

theorem original_gram_basis_change (r : ℚ) (n : ℕ) (E : Fin (3 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 3 * n) :
    (Matrix.of fun a b => Ufun r n ((D n)^4 * E a * E b)).det =
      C ((coeffMat E).det^2) * Q r n := by
  rw [gram_basis_change _ _ _ _ _ hE, hankelFor_original]
  rfl

/-! ### Binomial normalization -/

lemma coeffMat_binom_lowerTriangular (h : ℕ) :
    (coeffMat (fun a : Fin h => binomPoly a)).BlockTriangular OrderDual.toDual := by
  intro a k hk
  exact coeff_eq_zero_of_natDegree_lt (by rw [binomPoly_natDegree]; exact hk)

lemma coeffMat_binom_det (h : ℕ) :
    (coeffMat (fun a : Fin h => binomPoly a)).det =
      ∏ i ∈ Finset.range h, ((i.factorial : ℚ))⁻¹ := by
  rw [Matrix.det_of_isLowerTriangular _ (coeffMat_binom_lowerTriangular h)]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℚ))⁻¹)]
  exact Finset.prod_congr rfl fun a _ => binomPoly_coeff_self a

lemma coeffMat_binom_det_sq (n : ℕ) :
    (coeffMat (fun a : Fin (3*n) => binomPoly a)).det ^ 2 = (Fn n)⁻¹ := by
  rw [coeffMat_binom_det, Fn, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [inv_pow]

/-- The binomial Gram matrix with the scalar `S_n` inside every entry. -/
@[expose]
def binomGram (r : ℚ) (n : ℕ) : Matrix (Fin (3*n)) (Fin (3*n)) ℚ[X] :=
  Matrix.of fun a b =>
    Ufun r n (C (Sn n) * (D n)^4 * binomPoly a * binomPoly b)

theorem Qtilde_eq_binomGram_det (r : ℚ) (n : ℕ) : Qtilde r n = (binomGram r n).det := by
  have hM : binomGram r n = C (Sn n) •
      Matrix.of fun a b : Fin (3*n) =>
        Ufun r n ((D n)^4 * binomPoly a * binomPoly b) := by
    apply Matrix.ext
    intro a b
    simp only [binomGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Ufun_C_mul]
    congr 1
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    original_gram_basis_change r n (fun a => binomPoly a)
      (fun a => by rw [binomPoly_natDegree]; exact a.isLt),
    coeffMat_binom_det_sq, Qtilde, scale, div_eq_mul_inv, C_mul, map_pow]
  ring

end
end Zeta32.Arith.Small

end
