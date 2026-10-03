/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module
public import LeanPool.Zeta5Irrational.Arith.CoefficientMatrix

public import LeanPool.Zeta5Irrational.Construction
import LeanPool.Zeta5Irrational.PartialFractions
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring.Basic

/-! # Linearity of `μ_X` and change of basis in the Hankel determinant

* `μX_add`, `μX_C_mul`, `μX_sum` : `μ_X` is `ℚ`-linear in the numerator;
* `det_basis_change` : for polynomials `E a` of degree `< h`,
  `det [μ_X(D_N⁶ E_a E_b / D_K)] = det(C)² Δ_K` where `C` is the coefficient matrix.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

lemma divByMonic_add' {q : ℚ[X]} (hq : q.Monic) (P Q : ℚ[X]) : (P + Q) /ₘ q = P /ₘ q + Q /ₘ q := by
  refine ((div_modByMonic_unique (P /ₘ q + Q /ₘ q) (P %ₘ q + Q %ₘ q) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    have h2 := modByMonic_add_div Q q
    rw [mul_add]; linear_combination h1 + h2
  · exact
      (degree_add_le _ _).trans_lt
        (max_lt (degree_modByMonic_lt _ hq) (degree_modByMonic_lt _ hq))

lemma divByMonic_C_mul' {q : ℚ[X]} (hq : q.Monic) (c : ℚ) (P : ℚ[X]) :
    (C c * P) /ₘ q = C c * (P /ₘ q) := by
  refine ((div_modByMonic_unique (C c * (P /ₘ q)) (C c * (P %ₘ q)) hq ⟨?_, ?_⟩).1)
  · have h1 := modByMonic_add_div P q
    linear_combination C c * h1
  · rw [← smul_eq_C_mul]; exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)

lemma μpoly_add (P Q : ℚ[X]) : μpoly (P + Q) = μpoly P + μpoly Q := by
  unfold μpoly
  exact Polynomial.sum_add_index _ _ _ (fun _ => by simp) (fun _ _ _ => by ring)

lemma μpoly_C_mul (c : ℚ) (P : ℚ[X]) : μpoly (C c * P) = c * μpoly P := by
  unfold μpoly
  rw [← smul_eq_C_mul, Polynomial.sum_smul_index _ _ _ (fun _ => by simp), Polynomial.sum,
    Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma μX_add (K : ℕ) (P Q : ℚ[X]) : μX K (P + Q) = μX K P + μX K Q := by
  unfold μX
  rw [divByMonic_add' (D_monic K), μpoly_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma μX_C_mul (K : ℕ) (c : ℚ) (P : ℚ[X]) : μX K (C c * P) = C c * μX K P := by
  unfold μX
  rw [divByMonic_C_mul' (D_monic K), μpoly_C_mul, map_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]; ring

lemma μX_sum {ι : Type*} (K : ℕ) (s : Finset ι) (f : ι → ℚ[X]) :
    μX K (∑ i ∈ s, f i) = ∑ i ∈ s, μX K (f i) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    have := μX_C_mul K 0 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, μX_add, ih]

/-- **Change of basis**. -/
theorem det_basis_change (n : ℕ) (E : Fin (37 * n) → ℚ[X]) (hE : ∀ a, (E a).natDegree < 37 * n) :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)).det =
      C ((coeffMat E).det ^ 2) * Δ n := by
  set Cm := (coeffMat E).map (C : ℚ →+* ℚ[X]) with hCm
  have hM :
    (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * E a * E b)) = Cm * G n * Cm.transpose := by
    refine Matrix.ext fun a b => ?_
    have hexp :
      D (3 * n) ^ 6 * E a * E b =
        ∑ k : Fin (37 * n),
          ∑ l : Fin (37 * n),
            C (coeffMat E a k * coeffMat E b l) * (D (3 * n) ^ 6 * X ^ ((k : ℕ) + (l : ℕ))) := by
      rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [Matrix.of_apply, hexp, μX_sum]
    simp only [μX_sum, μX_C_mul, Matrix.mul_apply, Matrix.transpose_apply, hCm, Matrix.map_apply,
      G, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCm, ← RingHom.mapMatrix_apply, ←
    RingHom.map_det, Δ, map_pow];
  ring

end Zeta5Irrational
