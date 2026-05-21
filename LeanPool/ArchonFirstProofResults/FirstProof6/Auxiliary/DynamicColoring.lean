/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.ColoringFramework
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.LoewnerPullback

/-!
# Problem 6: Large epsilon-light vertex subsets -- Dynamic Coloring

Key infrastructure for the dynamic BSS coloring:
pseudo-inverse pullback, projection identity, normalized monochromatic PSD.
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inducedLaplacian_posSemidef
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (inducedLaplacian G S).PosSemidef := by
  rw [inducedLaplacian_eq_lapMatrix]
  exact SimpleGraph.posSemidef_lapMatrix ℝ (inducedSubgraph G S)

lemma inducedLaplacian_le_graphLaplacian
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (graphLaplacian G - inducedLaplacian G S).PosSemidef := by
  rw [graphLaplacian_eq_lapMatrix, inducedLaplacian_eq_lapMatrix]
  exact lapMatrix_loewner_mono (inducedSubgraph_le G S)

omit [DecidableEq V] in
lemma hermitian_mulVec_zero_of_sq_zero
    (Lhalf : Matrix V V ℝ) (hLhalf_herm : Lhalf.IsHermitian) (x : V → ℝ)
    (hx : (Lhalf * Lhalf) *ᵥ x = 0) :
    Lhalf *ᵥ x = 0 := by
  suffices h_zero : ∀ i, (Lhalf *ᵥ x) i = 0 by ext i; exact h_zero i
  intro i
  have h_sq_sum : ∑ j, (Lhalf *ᵥ x) j * (Lhalf *ᵥ x) j = 0 := by
    change (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = 0
    have h2 : (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = x ⬝ᵥ ((Lhalf * Lhalf) *ᵥ x) := by
      rw [show Lhalf * Lhalf = Lhalfᴴ * Lhalf from by rw [hLhalf_herm.eq]]
      simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
      simp [star_trivial]
    rw [h2, hx, dotProduct_zero]
  exact mul_self_eq_zero.mp
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg _) |>.mp h_sq_sum i
      (Finset.mem_univ i))

lemma pinv_pullback_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP1 : Lhalf * Lhalf_pinv * Lhalf = Lhalf)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    Lhalf * (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv) * Lhalf =
      inducedLaplacian G S := by
  set P := Lhalf * Lhalf_pinv with hP_def
  have h_lhs : Lhalf * (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv) * Lhalf =
      P * inducedLaplacian G S * P := by
    rw [hP_def]
    calc Lhalf * (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv) * Lhalf
        = (Lhalf * Lhalf_pinv) * inducedLaplacian G S * (Lhalf_pinv * Lhalf) := by
          simp only [Matrix.mul_assoc]
      _ = P * inducedLaplacian G S * P := by rw [hP_def, ← hMP4]
  rw [h_lhs]
  have hP_herm : P.IsHermitian := by
    change Pᴴ = P
    rw [hP_def, Matrix.conjTranspose_mul, hpinv_herm.eq, hLhalf_herm.eq, ← hMP4]
  have hP_idem : P * P = P := hMP3
  have hP_ker : ∀ x : V → ℝ, graphLaplacian G *ᵥ x = 0 ↔ P *ᵥ x = 0 := by
    have hLP_half : Lhalf * P = Lhalf := by
      calc Lhalf * P = Lhalf * (Lhalf_pinv * Lhalf) := by rw [hMP4]
        _ = (Lhalf * Lhalf_pinv) * Lhalf := by rw [Matrix.mul_assoc]
        _ = P * Lhalf := rfl
        _ = Lhalf := hMP1
    intro x; constructor
    · intro hLx
      have hLhalf_x : Lhalf *ᵥ x = 0 :=
        hermitian_mulVec_zero_of_sq_zero Lhalf hLhalf_herm x (by rw [hLhalf_sq]; exact hLx)
      rw [show P = Lhalf_pinv * Lhalf from hMP4, ← Matrix.mulVec_mulVec,
          hLhalf_x, Matrix.mulVec_zero]
    · intro hPx
      have hLhalf_x : Lhalf *ᵥ x = 0 := by
        calc Lhalf *ᵥ x = (Lhalf * P) *ᵥ x := by rw [hLP_half]
          _ = Lhalf *ᵥ (P *ᵥ x) := by rw [← Matrix.mulVec_mulVec]
          _ = Lhalf *ᵥ 0 := by rw [hPx]
          _ = 0 := Matrix.mulVec_zero Lhalf
      rw [← hLhalf_sq, ← Matrix.mulVec_mulVec, hLhalf_x, Matrix.mulVec_zero]
  set L_S := inducedLaplacian G S with hLS_def
  have hmv : ∀ x : V → ℝ, L_S *ᵥ (x - P *ᵥ x) = 0 := by
    intro x
    set y := x - P *ᵥ x
    have hPy : P *ᵥ y = 0 := by
      change P *ᵥ (x - P *ᵥ x) = 0
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP_idem, sub_self]
    have hLy : graphLaplacian G *ᵥ y = 0 := (hP_ker y).mpr hPy
    have hLS_psd := inducedLaplacian_posSemidef G S
    have h_LS_nn : 0 ≤ star y ⬝ᵥ (L_S *ᵥ y) := hLS_psd.dotProduct_mulVec_nonneg y
    have h_diff_nn : 0 ≤ star y ⬝ᵥ ((graphLaplacian G - L_S) *ᵥ y) :=
      (inducedLaplacian_le_graphLaplacian G S).dotProduct_mulVec_nonneg y
    rw [Matrix.sub_mulVec, hLy, zero_sub, dotProduct_neg] at h_diff_nn
    exact (hLS_psd.dotProduct_mulVec_zero_iff y).mp
      (le_antisymm (neg_nonneg.mp h_diff_nn) h_LS_nn)
  have hLP : L_S * P = L_S := by
    have key : ∀ v, (L_S * P) *ᵥ v = L_S *ᵥ v := by
      intro v
      rw [← Matrix.mulVec_mulVec]
      have hk := hmv v
      rw [Matrix.mulVec_sub] at hk
      exact (sub_eq_zero.mp hk).symm
    ext i j
    have := congr_fun (key (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
               mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
               Finset.mem_univ, ite_true] at this
    exact this
  have hLS_sym : L_S.IsHermitian := (inducedLaplacian_posSemidef G S).isHermitian
  have hPL : P * L_S = L_S := by
    have h := congr_arg Matrix.conjTranspose hLP
    rw [Matrix.conjTranspose_mul] at h
    rwa [hP_herm.eq, hLS_sym.eq] at h
  rw [Matrix.mul_assoc, hLP]; exact hPL

lemma normalized_mono_psd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Lhalf_pinv : Matrix V V ℝ) (hpinv_herm : Lhalf_pinv.IsHermitian)
    (S : Finset V) :
    (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv).PosSemidef := by
  rw [show Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv =
    Lhalf_pinvᴴ * inducedLaplacian G S * Lhalf_pinv from by rw [hpinv_herm.eq]]
  exact (inducedLaplacian_posSemidef G S).conjTranspose_mul_mul_same Lhalf_pinv

lemma normalized_laplacian_eq_proj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    Lhalf_pinv * graphLaplacian G * Lhalf_pinv = Lhalf * Lhalf_pinv := by
  rw [← hLhalf_sq]
  calc Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv
      = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv) := by
        simp only [Matrix.mul_assoc]
    _ = (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) := by rw [← hMP4]
    _ = Lhalf * Lhalf_pinv := hMP3

lemma proj_le_one
    (P : Matrix V V ℝ)
    (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) :
    ((1 : Matrix V V ℝ) - P).PosSemidef := by
  have hQ_herm : ((1 : Matrix V V ℝ) - P).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm.eq]
  have hQ_idem : ((1 : Matrix V V ℝ) - P) * ((1 : Matrix V V ℝ) - P) =
      (1 : Matrix V V ℝ) - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP_idem, sub_self, sub_zero]
  rw [show (1 : Matrix V V ℝ) - P = ((1 : Matrix V V ℝ) - P)ᴴ * ((1 : Matrix V V ℝ) - P) from
      by rw [hQ_herm.eq, hQ_idem]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma inducedLaplacian_mono
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) (hST : S ⊆ T) :
    (inducedLaplacian G T - inducedLaplacian G S).PosSemidef := by
  rw [inducedLaplacian_eq_lapMatrix, inducedLaplacian_eq_lapMatrix]
  exact lapMatrix_loewner_mono (inducedSubgraph_mono G hST)

omit [Fintype V] in
lemma psd_sub_sum_le {r : ℕ} (M : Fin r → Matrix V V ℝ) (u : ℝ)
    (hM_psd : ∀ γ, (M γ).PosSemidef)
    (h_total : (u • (1 : Matrix V V ℝ) - ∑ γ : Fin r, M γ).PosSemidef) :
    ∀ γ : Fin r, (u • (1 : Matrix V V ℝ) - M γ).PosSemidef := by
  intro γ
  have h_split : u • (1 : Matrix V V ℝ) - M γ =
      (u • (1 : Matrix V V ℝ) - ∑ γ' : Fin r, M γ') +
      ∑ γ' ∈ Finset.univ.erase γ, M γ' := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ)]; abel
  rw [h_split]
  exact h_total.add (Finset.sum_induction _ (fun (A : Matrix V V ℝ) => A.PosSemidef)
    (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun γ' _ => hM_psd γ'))

end Problem6

end
