/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Spectral.AlgConn

/-!
# Lower companion of the Courant–Fischer bridge

`le_algConn_of_forall`: if the Laplacian quadratic form dominates `c · ‖x‖²` for
every `x` orthogonal to the all-ones vector (`∑ i, x i = 0`), then `c ≤ algConn G`.
This is the reverse direction used to certify the *lower* bound `algConn ≥ 2`.
-/

public section

namespace ACMax

open Matrix

open Classical in
theorem le_algConn_of_forall {V : Type*} [Fintype V] [Nonempty V] [Nontrivial V]
    (G : SimpleGraph V) (c : ℝ)
    (h : ∀ x : V → ℝ, ∑ i, x i = 0 →
      c * (∑ i, (x i) ^ 2) ≤ dotProduct x ((G.lapMatrix ℝ).mulVec x)) :
    c ≤ algConn G := by
  classical
  set A : Matrix V V ℝ := G.lapMatrix ℝ with hAdef
  have hPSD : A.PosSemidef := SimpleGraph.posSemidef_lapMatrix ℝ G
  have hHerm : A.IsHermitian := hPSD.isHermitian
  set U := hHerm.eigenvectorUnitary with hUdef
  set lam : V → ℝ := hHerm.eigenvalues with hlamdef
  -- the unitary `star U * U = 1` gives orthonormality of the columns of `U`
  have hU2 : star (U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have horth : ∀ i j : V,
      (∑ k, (U : Matrix V V ℝ) k i * (U : Matrix V V ℝ) k j) = if i = j then 1 else 0 := by
    intro i j
    have hh := congrFun (congrFun hU2 i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.star_apply, star_trivial]
  -- index data: `j0` realises the second-smallest eigenvalue, `j1` the smallest
  have hcard2 : Fintype.card V - 2 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
  have hcard1 : Fintype.card V - 1 < Fintype.card V := Nat.sub_lt Fintype.card_pos (by norm_num)
  have hN : 1 < Fintype.card V := Fintype.one_lt_card
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  have hlam : ∀ i, lam i = hHerm.eigenvalues₀ (e.symm i) := by intro i; rw [hlamdef]; rfl
  have hc : algConn G = hHerm.eigenvalues₀ ⟨Fintype.card V - 2, hcard2⟩ := rfl
  set j0 : V := e ⟨Fintype.card V - 2, hcard2⟩ with hj0
  set j1 : V := e ⟨Fintype.card V - 1, hcard1⟩ with hj1
  have hej0 : e.symm j0 = ⟨Fintype.card V - 2, hcard2⟩ := by rw [hj0]; exact e.symm_apply_apply _
  have hej1 : e.symm j1 = ⟨Fintype.card V - 1, hcard1⟩ := by rw [hj1]; exact e.symm_apply_apply _
  have hj0ne1 : j0 ≠ j1 := by
    intro heq
    have h2 : (⟨Fintype.card V - 2, hcard2⟩ : Fin (Fintype.card V))
        = ⟨Fintype.card V - 1, hcard1⟩ := by rw [← hej0, ← hej1, heq]
    have h3 : Fintype.card V - 2 = Fintype.card V - 1 := Fin.mk_eq_mk.mp h2
    omega
  have hlamj0 : lam j0 = algConn G := by rw [hlam j0, hej0]; exact hc.symm
  have hlamj1 : lam j1 ≤ algConn G := by
    rw [hlam j1, hej1, hc]
    exact hHerm.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (by omega))
  -- the eigenvector columns of `U` and their spectral relation
  set v0 : V → ℝ := fun k => (U : Matrix V V ℝ) k j0 with hv0def
  set v1 : V → ℝ := fun k => (U : Matrix V V ℝ) k j1 with hv1def
  have hAv0 : A *ᵥ v0 = lam j0 • v0 := by
    have hcol : v0 = ⇑(hHerm.eigenvectorBasis j0) := by
      funext k; exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j0
    rw [hcol, hHerm.mulVec_eigenvectorBasis]
  have hAv1 : A *ᵥ v1 = lam j1 • v1 := by
    have hcol : v1 = ⇑(hHerm.eigenvectorBasis j1) := by
      funext k; exact Matrix.IsHermitian.eigenvectorUnitary_apply hHerm k j1
    rw [hcol, hHerm.mulVec_eigenvectorBasis]
  have hnorm0 : v0 ⬝ᵥ v0 = 1 := by
    have hr := horth j0 j0
    rw [ite_eq_left rfl] at hr
    exact hr
  have hnorm1 : v1 ⬝ᵥ v1 = 1 := by
    have hr := horth j1 j1
    rw [ite_eq_left rfl] at hr
    exact hr
  have hcross : v0 ⬝ᵥ v1 = 0 := by
    have hr := horth j0 j1
    rw [ite_eq_right hj0ne1] at hr
    exact hr
  have hcross' : v1 ⬝ᵥ v0 = 0 := by
    have hr := horth j1 j0
    rw [ite_eq_right (fun hh => hj0ne1 hh.symm)] at hr
    exact hr
  -- split on whether the second-smallest eigenvector is already orthogonal to `1`
  rcases eq_or_ne (∑ k, v0 k) 0 with hS0 | hS0
  · -- `v0 ⊥ 1`: it directly certifies the bound at the second-smallest eigenvalue
    have hb := h v0 hS0
    have hsq : (∑ k, (v0 k) ^ 2) = v0 ⬝ᵥ v0 := by
      have hr : v0 ⬝ᵥ v0 = ∑ k, v0 k * v0 k := rfl
      rw [hr]; apply Finset.sum_congr rfl; intro k _; rw [pow_two]
    have hAq : v0 ⬝ᵥ (A *ᵥ v0) = lam j0 := by
      rw [hAv0, dotProduct_smul, smul_eq_mul, hnorm0, mul_one]
    rw [hsq, hnorm0, mul_one, hAq, hlamj0] at hb
    exact hb
  · -- otherwise combine `v0`, `v1` into a kernel-of-`∑` vector with Rayleigh quotient
    -- bounded by `algConn`
    set w : V → ℝ := (∑ k, v1 k) • v0 - (∑ k, v0 k) • v1 with hwdef
    have hsumw : ∑ k, w k = 0 := by
      have h1 : ∑ k, w k
          = (∑ k, v1 k) * (∑ k, v0 k) - (∑ k, v0 k) * (∑ k, v1 k) := by
        simp only [hwdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
      rw [h1]; ring
    have hAw : A *ᵥ w
        = (∑ k, v1 k) • (lam j0 • v0) - (∑ k, v0 k) • (lam j1 • v1) := by
      rw [hwdef, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hAv0, hAv1]
    have hnormw : w ⬝ᵥ w = (∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2 := by
      conv_lhs => rw [hwdef]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hnorm0, hnorm1, hcross, hcross']
      ring
    have hquadw : w ⬝ᵥ (A *ᵥ w)
        = (∑ k, v1 k) ^ 2 * lam j0 + (∑ k, v0 k) ^ 2 * lam j1 := by
      rw [hAw]
      conv_lhs => rw [hwdef]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hnorm0, hnorm1, hcross, hcross']
      ring
    have hbnd := h w hsumw
    have hsqw : (∑ k, (w k) ^ 2) = w ⬝ᵥ w := by
      have hr : w ⬝ᵥ w = ∑ k, w k * w k := rfl
      rw [hr]; apply Finset.sum_congr rfl; intro k _; rw [pow_two]
    rw [hsqw, hnormw, hquadw] at hbnd
    have hpos : 0 < (∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2 := by
      have h2 : 0 < (∑ k, v0 k) ^ 2 := by rw [pow_two]; exact mul_self_pos.mpr hS0
      nlinarith [sq_nonneg (∑ k, v1 k)]
    have hub : (∑ k, v1 k) ^ 2 * lam j0 + (∑ k, v0 k) ^ 2 * lam j1
        ≤ algConn G * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2) := by
      rw [hlamj0]
      nlinarith [mul_le_mul_of_nonneg_left hlamj1 (sq_nonneg (∑ k, v0 k)),
        sq_nonneg (∑ k, v1 k), sq_nonneg (∑ k, v0 k)]
    have hfin : c * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2)
        ≤ algConn G * ((∑ k, v0 k) ^ 2 + (∑ k, v1 k) ^ 2) := le_trans hbnd hub
    exact le_of_mul_le_mul_right hfin hpos

end ACMax
