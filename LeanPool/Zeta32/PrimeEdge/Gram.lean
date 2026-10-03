/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Basis

/-! the proof notes, §6: Gram change of basis
`det[U_r(φ_a φ_c R_n)] = det(T)^2 · Q_n` for any family of degree `< h`
(adapted from `det_basis_change` in Arith/Local/Entry.lean and Li₂ Base/Gram.lean). -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- **S1-Gram.** -/
theorem gram_basis_change (r : ℚ) (n : ℕ) (E : Fin (3 * n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 3 * n) :
    (Matrix.of fun a b => Lfun r n (E a * E b * Zeta32.D n ^ 4)).det =
      C ((coeffMat E).det ^ 2) * Zeta32.Q r n := by
  set L := Lfun r n
  have hadd : ∀ A B, L (A + B) = L A + L B := Lfun_add r n
  have hC : ∀ c A, L (C c * A) = C c * L A := Lfun_C_mul r n
  have h0 : L 0 = 0 := by
    have := hC 0 0
    simpa using this
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → ℚ[X]),
      L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    intro ι s g
    classical
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  set W := Zeta32.D n ^ 4
  set Cm := (coeffMat E).map (C : ℚ →+* ℚ[X]) with hCm
  set G := Matrix.of fun i k : Fin (3 * n) => L (X ^ (i.val + k.val) * W) with hG
  have hM : (Matrix.of fun i k => L (E i * E k * W)) = Cm * G * Cm.transpose := by
    refine Matrix.ext fun a b => ?_
    have hexp : E a * E b * W = ∑ k : Fin (3 * n), ∑ l : Fin (3 * n),
        C (coeffMat E a k * coeffMat E b l) * (X ^ ((k : ℕ) + (l : ℕ)) * W) := by
      conv_lhs => rw [sum_coeffMat E hE a, sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul, pow_add]; ring
    rw [Matrix.of_apply, hexp, hsum]
    simp only [hsum, hC, Matrix.mul_apply, Matrix.transpose_apply, hCm, Matrix.map_apply, hG,
      Finset.sum_mul, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul]; ring
  have hQ : Zeta32.Q r n = G.det := by
    rw [Zeta32.Q, hankel_eq_Lfun]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCm, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, hQ, C_pow]
  ring

/-- The entry matrix `G_{ac} = U_r(φ_a φ_c R_n)` in the CRT basis, `n = p - 1`. -/
noncomputable def G (r : ℚ) (p : ℕ) : Matrix (Idx p) (Idx p) ℚ[X] :=
  Matrix.of fun a c => Lfun r (p - 1) (Aent p a c)

lemma G_apply (r : ℚ) (a c : Idx p) : G r p a c = Lfun r (p - 1) (Aent p a c) := rfl

/-- **S1.** `det G = det(T)^2 · Q_{p-1}`. -/
theorem G_det (r : ℚ) (hp : 5 ≤ p) :
    (G r p).det = C (basisDet p hp ^ 2) * Zeta32.Q r (p - 1) := by
  rw [← Matrix.det_submatrix_equiv_self (idxEquiv hp) (G r p)]
  have h := gram_basis_change r (p - 1) (fun i => crtBasis p (idxEquiv hp i))
    (fun i => crtBasis_natDegree_lt hp _)
  rw [basisDet, ← h]
  rfl

end Zeta32.PrimeEdge

end
