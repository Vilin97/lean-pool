/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Spectral.AlgConn

/-!
# Variational (Courant–Fischer) upper bound for algebraic connectivity

`algConn_mul_sq_le`: for any test vector `x` orthogonal to the all-ones vector
(`∑ i, x i = 0`), the second-smallest Laplacian eigenvalue is bounded by the
Rayleigh quotient of `x`, in division-free form
`algConn G * ‖x‖² ≤ xᵀ L x`.

This is the reusable bridge both clauses of the ACMAX conjecture rely on.
-/

@[expose] public section

namespace ACMax

open Matrix

open Classical in
theorem algConn_mul_sq_le {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (x : V → ℝ) (hx0 : ∑ i, x i = 0) :
    algConn G * (∑ i, (x i) ^ 2) ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x) := by
  classical
  set A : Matrix V V ℝ := G.lapMatrix ℝ with hAdef
  have hPSD : A.PosSemidef := SimpleGraph.posSemidef_lapMatrix ℝ G
  have hHerm : A.IsHermitian := hPSD.isHermitian
  set U := hHerm.eigenvectorUnitary with hUdef
  set lam : V → ℝ := hHerm.eigenvalues with hlamdef
  set D : Matrix V V ℝ := Matrix.diagonal lam with hDdef
  -- rewrite the squared norm as a dot product
  have hsum : (∑ i, (x i) ^ 2) = x ⬝ᵥ x := by
    have h : x ⬝ᵥ x = ∑ i, x i * x i := rfl
    rw [h]; simp [pow_two]
  rw [hsum]
  -- unitary facts
  have hU1 : (U : Matrix V V ℝ) * star (U : Matrix V V ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hU2 : star (U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hst : star (U : Matrix V V ℝ) = (U : Matrix V V ℝ)ᵀ := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply, star_trivial]
  rcases le_or_gt (algConn G) 0 with hc0 | hcpos
  · -- trivial case: LHS ≤ 0 ≤ RHS
    have hxx : 0 ≤ x ⬝ᵥ x := by rw [← hsum]; positivity
    have hrhs : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
      have h := hPSD.re_dotProduct_nonneg x
      simpa using h
    have hle : algConn G * (x ⬝ᵥ x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hxx
    linarith
  · -- main case: 0 < algConn G
    set y : V → ℝ := star (U : Matrix V V ℝ) *ᵥ x with hydef
    -- spectral relation A * U = U * D
    have hAU : A * (U : Matrix V V ℝ) = (U : Matrix V V ℝ) * D := by
      ext i j
      have hcol : (fun k => (U : Matrix V V ℝ) k j) = ⇑(hHerm.eigenvectorBasis j) := by
        funext k
        exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j
      have hL : (A * (U : Matrix V V ℝ)) i j = (lam j • ⇑(hHerm.eigenvectorBasis j)) i := by
        have hrfl : (A * (U : Matrix V V ℝ)) i j
            = (A *ᵥ (fun k => (U : Matrix V V ℝ) k j)) i := rfl
        rw [hrfl, hcol, hHerm.mulVec_eigenvectorBasis]
      rw [hL, hDdef, Matrix.mul_diagonal]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Matrix.IsHermitian.eigenvectorUnitary_apply hHerm i j]
      ring
    have hAgen : ∀ w : V → ℝ,
        A *ᵥ ((U : Matrix V V ℝ) *ᵥ w) = (U : Matrix V V ℝ) *ᵥ (D *ᵥ w) := by
      intro w
      rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec]
    -- x = U *ᵥ y
    have hxy : x = (U : Matrix V V ℝ) *ᵥ y := by
      rw [hydef, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
    have hAx : A *ᵥ x = (U : Matrix V V ℝ) *ᵥ (D *ᵥ y) := by
      rw [hxy]; exact hAgen y
    -- U preserves the dot product
    have hpres : ∀ a b : V → ℝ,
        ((U : Matrix V V ℝ) *ᵥ a) ⬝ᵥ ((U : Matrix V V ℝ) *ᵥ b) = a ⬝ᵥ b := by
      intro a b
      rw [Matrix.dotProduct_mulVec]
      have hv : Matrix.vecMul ((U : Matrix V V ℝ) *ᵥ a) (U : Matrix V V ℝ) = a := by
        rw [← Matrix.mulVec_transpose, ← hst, Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
      rw [hv]
    have hxx : x ⬝ᵥ x = y ⬝ᵥ y := by rw [hxy]; exact hpres y y
    have hquad : x ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ (D *ᵥ y) := by
      rw [hAx, hxy]; exact hpres y (D *ᵥ y)
    -- index data
    have hcard2 : Fintype.card V - 2 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
    let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
    have hlam : ∀ i, lam i = hHerm.eigenvalues₀ (e.symm i) := by intro i; rw [hlamdef]; rfl
    have hc : algConn G = hHerm.eigenvalues₀ ⟨Fintype.card V - 2, hcard2⟩ := rfl
    -- the diagonal kills z on the positive eigenvalues
    -- key: y i = 0 whenever lam i < algConn G
    have hzero : ∀ i, lam i < algConn G → y i = 0 := by
      intro i hi
      set ones : V → ℝ := fun _ => (1 : ℝ) with hones
      set z : V → ℝ := star (U : Matrix V V ℝ) *ᵥ ones with hz
      have hones_eq : ones = (U : Matrix V V ℝ) *ᵥ z := by
        rw [hz, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
      have hAones : A *ᵥ ones = 0 := by
        rw [hAdef]; exact SimpleGraph.lapMatrix_mulVec_one_eq_zero ℝ G
      have hUDz : (U : Matrix V V ℝ) *ᵥ (D *ᵥ z) = 0 := by
        rw [← hAgen z, ← hones_eq, hAones]
      have hDz : D *ᵥ z = 0 := by
        have hcong := congrArg (fun w => star (U : Matrix V V ℝ) *ᵥ w) hUDz
        simp only [Matrix.mulVec_zero] at hcong
        rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec] at hcong
        exact hcong
      have hlamz : ∀ k, lam k * z k = 0 := by
        intro k
        have hck := congrFun hDz k
        rw [hDdef, Matrix.mulVec_diagonal] at hck
        simpa using hck
      -- e.symm i sits strictly past card - 2
      have hk2 : (Fintype.card V - 2 : ℕ) < (e.symm i).val := by
        by_contra hcon
        rw [not_lt] at hcon
        have hle : (e.symm i) ≤ (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V)) :=
          Fin.le_def.mpr hcon
        have hmono := hHerm.eigenvalues₀_antitone hle
        rw [← hlam i, ← hc] at hmono
        linarith
      -- z vanishes off i
      have hknz : ∀ k, k ≠ i → z k = 0 := by
        intro k hk
        have hkne : (e.symm k).val ≠ (e.symm i).val := by
          intro h
          exact hk (e.symm.injective (Fin.ext h))
        have hle : (e.symm k) ≤ (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V)) := by
          rw [Fin.le_def]
          change (e.symm k).val ≤ Fintype.card V - 2
          have h1 := (e.symm i).isLt
          have h2 := (e.symm k).isLt
          omega
        have hge : algConn G ≤ lam k := by
          have hmono := hHerm.eigenvalues₀_antitone hle
          rwa [← hlam k, ← hc] at hmono
        have hkpos : lam k ≠ 0 := by linarith
        rcases mul_eq_zero.mp (hlamz k) with h | h
        · exact absurd h hkpos
        · exact h
      -- 1 = U j i * z i for every j
      have huzi : ∀ j, (U : Matrix V V ℝ) j i * z i = 1 := by
        intro j
        have h1 : (1 : ℝ) = ∑ k, (U : Matrix V V ℝ) j k * z k := by
          have hcj := congrFun hones_eq j
          simpa [hones, Matrix.mulVec, dotProduct] using hcj
        rw [Finset.sum_eq_single i] at h1
        · exact h1.symm
        · intro k _ hk; rw [hknz k hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      -- expand y i
      have hyi : y i = ∑ j, (U : Matrix V V ℝ) j i * x j := by
        rw [hydef]
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.star_apply, star_trivial]
      have key : z i * y i = 0 := by
        have h2 : z i * y i = ∑ j, x j := by
          rw [hyi, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← mul_assoc, mul_comm (z i) ((U : Matrix V V ℝ) j i), huzi j, one_mul]
        rw [h2, hx0]
      rcases mul_eq_zero.mp key with h | h
      · exfalso
        have hj := huzi (Classical.arbitrary V)
        rw [h, mul_zero] at hj
        exact one_ne_zero hj.symm
      · exact h
    -- assemble the bound
    rw [hxx, hquad]
    have e1 : y ⬝ᵥ y = ∑ j, y j ^ 2 := by
      have h : y ⬝ᵥ y = ∑ j, y j * y j := rfl
      rw [h]; apply Finset.sum_congr rfl; intro j _; rw [pow_two]
    have e2 : y ⬝ᵥ (D *ᵥ y) = ∑ j, lam j * y j ^ 2 := by
      have h : y ⬝ᵥ (D *ᵥ y) = ∑ j, y j * (D *ᵥ y) j := rfl
      rw [h]; apply Finset.sum_congr rfl; intro j _
      rw [hDdef, Matrix.mulVec_diagonal]; ring
    rw [e1, e2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rcases le_or_gt (algConn G) (lam j) with hle | hlt
    · exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    · rw [hzero j hlt]; simp

end ACMax
