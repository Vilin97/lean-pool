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
1. `inducedLaplacian_le_graphLaplacian`: L_S <= L (Loewner)
2. `hermitian_mulVec_zero_of_sq_zero`: kernel transfer
3. `pinv_pullback_eq`: pseudo-inverse pullback identity
4. `inducedLaplacian_posSemidef`, `normalized_mono_psd`

## Main theorems

- `Problem6.inducedLaplacian_posSemidef`: induced Laplacian PSD
- `Problem6.inducedLaplacian_le_graphLaplacian`: Loewner bound
- `Problem6.hermitian_mulVec_zero_of_sq_zero`: kernel transfer
- `Problem6.pinv_pullback_eq`: pseudo-inverse pullback
- `Problem6.normalized_laplacian_eq_proj`: projection identity
- `Problem6.proj_le_one`: projection bounded by identity
- `Problem6.normalized_mono_psd`: normalized monochromatic PSD
- `Problem6.inducedLaplacian_mono`: monotonicity in subsets
- `Problem6.psd_sub_sum_le`: PSD extraction from sum bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced Laplacian of any subset is PSD. -/
lemma inducedLaplacian_posSemidef
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (inducedLaplacian G S).PosSemidef := by
  rw [inducedLaplacian_eq_lapMatrix]
  exact SimpleGraph.posSemidef_lapMatrix ℝ (inducedSubgraph G S)

/-! ### Loewner bound: induced Laplacian ≤ graph Laplacian -/

/-- The induced Laplacian of any subset is dominated by the graph Laplacian:
    (graphLaplacian G - inducedLaplacian G S).PosSemidef. -/
lemma inducedLaplacian_le_graphLaplacian
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (graphLaplacian G - inducedLaplacian G S).PosSemidef := by
  rw [graphLaplacian_eq_lapMatrix, inducedLaplacian_eq_lapMatrix]
  exact lapMatrix_loewner_mono (inducedSubgraph_le G S)

/-! ### Kernel transfer: ker(Lhalf²) = ker(Lhalf) for Hermitian matrices -/

omit [DecidableEq V] in
/-- For a Hermitian matrix Lhalf over ℝ, if Lhalf * Lhalf * x = 0 then Lhalf * x = 0.
    Proof: ‖Lhalf x‖² = xᵀ Lhalf² x = xᵀ 0 = 0. -/
lemma hermitian_mulVec_zero_of_sq_zero
    (Lhalf : Matrix V V ℝ) (hLhalf_herm : Lhalf.IsHermitian) (x : V → ℝ)
    (hx : (Lhalf * Lhalf) *ᵥ x = 0) :
    Lhalf *ᵥ x = 0 := by
  -- ‖Lhalf x‖² = ∑ i, ((Lhalf x) i)² = 0 implies Lhalf x = 0
  -- Key: ∑ i, ((Lhalf x) i)² = (Lhalf x)^T (Lhalf x) = x^T Lhalf^T Lhalf x
  --   = x^T Lhalf² x = x^T 0 = 0 (using Lhalf^T = Lhalf since Hermitian over ℝ)
  suffices h_zero : ∀ i, (Lhalf *ᵥ x) i = 0 by ext i; exact h_zero i
  intro i
  -- Compute the squared norm
  have h_sq_sum : ∑ j, (Lhalf *ᵥ x) j * (Lhalf *ᵥ x) j = 0 := by
    -- Key: ‖Lhalf x‖² = (Lhalf x) ⬝ (Lhalf x) = x ⬝ (Lhalf² x) = x ⬝ 0 = 0
    change (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = 0
    -- Since Lhalf is Hermitian, (Lhalf*x) ⬝ (Lhalf*x) = x ⬝ (Lhalf² x)
    have h2 : (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = x ⬝ᵥ ((Lhalf * Lhalf) *ᵥ x) := by
      -- Rewrite Lhalf * Lhalf = Lhalfᴴ * Lhalf (Hermiticity)
      -- Then (Lhalfᴴ * Lhalf) *ᵥ x = Lhalfᴴ *ᵥ (Lhalf *ᵥ x) [← mulVec_mulVec]
      -- Then x ⬝ᵥ (Lhalfᴴ *ᵥ y) = (x ᵥ* Lhalfᴴ) ⬝ᵥ y [dotProduct_mulVec]
      -- Then x v* LhalfH = star (Lhalf *v star x) = Lhalf *v x
      rw [show Lhalf * Lhalf = Lhalfᴴ * Lhalf from by rw [hLhalf_herm.eq]]
      simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
      simp [star_trivial]
    rw [h2, hx, dotProduct_zero]
  -- From ∑ ((Lhalf x) j)² = 0 and each term ≥ 0, each term = 0
  have h_nn : ∀ j, 0 ≤ (Lhalf *ᵥ x) j * (Lhalf *ᵥ x) j :=
    fun j => mul_self_nonneg _
  exact mul_self_eq_zero.mp
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nn j) |>.mp h_sq_sum i (Finset.mem_univ i))

/-! ### Pseudo-inverse pullback identity -/

/-- Given Lhalf (Hermitian, Lhalf² = L) and Lhalf_pinv (its Moore-Penrose pseudo-inverse),
    the pullback identity holds:
    Lhalf * (Lhalf_pinv * L_S * Lhalf_pinv) * Lhalf = inducedLaplacian G S. -/
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
  -- Rewrite LHS as P * L_S * P using associativity and MP4
  have h_lhs : Lhalf * (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv) * Lhalf =
      P * inducedLaplacian G S * P := by
    rw [hP_def]
    calc Lhalf * (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv) * Lhalf
        = (Lhalf * Lhalf_pinv) * inducedLaplacian G S * (Lhalf_pinv * Lhalf) := by
          simp only [Matrix.mul_assoc]
      _ = P * inducedLaplacian G S * P := by rw [hP_def, ← hMP4]
  rw [h_lhs]
  -- P is Hermitian
  have hP_herm : P.IsHermitian := by
    change Pᴴ = P
    rw [hP_def, Matrix.conjTranspose_mul, hpinv_herm.eq, hLhalf_herm.eq, ← hMP4]
  -- P is idempotent
  have hP_idem : P * P = P := hMP3
  -- ker(L) = ker(P)
  have hP_ker : ∀ x : V → ℝ, graphLaplacian G *ᵥ x = 0 ↔ P *ᵥ x = 0 := by
    -- Key intermediate fact: Lhalf * P = Lhalf
    -- P = Lhalf_pinv * Lhalf (by hMP4), so:
    -- Lhalf * P = Lhalf * (Lhalf_pinv * Lhalf) = (Lhalf * Lhalf_pinv) * Lhalf = P * Lhalf = Lhalf
    have hLP_half : Lhalf * P = Lhalf := by
      calc Lhalf * P = Lhalf * (Lhalf_pinv * Lhalf) := by rw [hMP4]
        _ = (Lhalf * Lhalf_pinv) * Lhalf := by rw [Matrix.mul_assoc]
        _ = P * Lhalf := rfl
        _ = Lhalf := hMP1
    intro x; constructor
    · -- Forward: L *ᵥ x = 0 → Lhalf *ᵥ x = 0 → P *ᵥ x = 0
      intro hLx
      have hLhalf_x : Lhalf *ᵥ x = 0 :=
        hermitian_mulVec_zero_of_sq_zero Lhalf hLhalf_herm x (by rw [hLhalf_sq]; exact hLx)
      -- P = Lhalf_pinv * Lhalf, so P *ᵥ x = Lhalf_pinv *ᵥ (Lhalf *ᵥ x) = 0
      rw [show P = Lhalf_pinv * Lhalf from hMP4, ← Matrix.mulVec_mulVec,
          hLhalf_x, Matrix.mulVec_zero]
    · -- Backward: P *ᵥ x = 0 → Lhalf *ᵥ x = 0 → L *ᵥ x = 0
      intro hPx
      -- Lhalf *ᵥ x = (Lhalf * P) *ᵥ x = Lhalf *ᵥ (P *ᵥ x) = 0
      have hLhalf_x : Lhalf *ᵥ x = 0 := by
        calc Lhalf *ᵥ x = (Lhalf * P) *ᵥ x := by rw [hLP_half]
          _ = Lhalf *ᵥ (P *ᵥ x) := by rw [← Matrix.mulVec_mulVec]
          _ = Lhalf *ᵥ 0 := by rw [hPx]
          _ = 0 := Matrix.mulVec_zero Lhalf
      -- L *ᵥ x = (Lhalf * Lhalf) *ᵥ x = Lhalf *ᵥ (Lhalf *ᵥ x) = 0
      rw [← hLhalf_sq, ← Matrix.mulVec_mulVec, hLhalf_x, Matrix.mulVec_zero]
  -- Apply the projection absorption argument (same as proj_absorbs_inducedLaplacian)
  set L_S := inducedLaplacian G S with hLS_def
  -- Key: L_S * (x - Px) = 0 for all x
  have hmv : ∀ x : V → ℝ, L_S *ᵥ (x - P *ᵥ x) = 0 := by
    intro x
    set y := x - P *ᵥ x
    -- Step 1: P *ᵥ y = 0 (by idempotence of P)
    have hPy : P *ᵥ y = 0 := by
      change P *ᵥ (x - P *ᵥ x) = 0
      rw [Matrix.mulVec_sub]
      -- Goal: P *ᵥ x - P *ᵥ (P *ᵥ x) = 0
      -- P *ᵥ (P *ᵥ x) = (P * P) *ᵥ x = P *ᵥ x
      rw [Matrix.mulVec_mulVec, hP_idem, sub_self]
    -- Step 2: graphLaplacian G *ᵥ y = 0 (by hP_ker backward)
    have hLy : graphLaplacian G *ᵥ y = 0 := (hP_ker y).mpr hPy
    -- Step 3: y ⬝ᵥ (L_S *ᵥ y) = 0 by PSD sandwich
    -- From inducedLaplacian_posSemidef: star y ⬝ᵥ (L_S *ᵥ y) ≥ 0
    have hLS_psd := inducedLaplacian_posSemidef G S
    have hL_LS_psd := inducedLaplacian_le_graphLaplacian G S
    have h_LS_nn : 0 ≤ star y ⬝ᵥ (L_S *ᵥ y) := hLS_psd.dotProduct_mulVec_nonneg y
    -- From (L - L_S).PosSemidef: star y ⬝ᵥ ((L - L_S) *ᵥ y) ≥ 0
    have h_diff_nn : 0 ≤ star y ⬝ᵥ ((graphLaplacian G - L_S) *ᵥ y) :=
      hL_LS_psd.dotProduct_mulVec_nonneg y
    -- (L - L_S) *ᵥ y = L *ᵥ y - L_S *ᵥ y = 0 - L_S *ᵥ y = -(L_S *ᵥ y)
    rw [Matrix.sub_mulVec, hLy, zero_sub] at h_diff_nn
    -- star y ⬝ᵥ (-(L_S *ᵥ y)) = -(star y ⬝ᵥ (L_S *ᵥ y)) ≥ 0
    rw [dotProduct_neg] at h_diff_nn
    -- So star y ⬝ᵥ (L_S *ᵥ y) ≤ 0 and ≥ 0, hence = 0
    -- Step 4: By dotProduct_mulVec_zero_iff (PSD zero characterization): L_S *ᵥ y = 0
    exact (hLS_psd.dotProduct_mulVec_zero_iff y).mp
      (le_antisymm (neg_nonneg.mp h_diff_nn) h_LS_nn)
  -- L_S * P = L_S
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
  -- L_S is Hermitian
  have hLS_sym : L_S.IsHermitian := (inducedLaplacian_posSemidef G S).isHermitian
  -- P * L_S = L_S (transpose of L_S * P = L_S)
  have hPL : P * L_S = L_S := by
    have h := congr_arg Matrix.conjTranspose hLP
    rw [Matrix.conjTranspose_mul] at h
    rwa [hP_herm.eq, hLS_sym.eq] at h
  -- Combine: P * L_S * P = L_S * P = L_S
  rw [Matrix.mul_assoc, hLP]; exact hPL

/-! ### Normalized monochromatic matrix -/

/-- Normalized monochromatic matrix is PSD (conjugation of PSD by Hermitian). -/
lemma normalized_mono_psd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Lhalf_pinv : Matrix V V ℝ) (hpinv_herm : Lhalf_pinv.IsHermitian)
    (S : Finset V) :
    (Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv).PosSemidef := by
  rw [show Lhalf_pinv * inducedLaplacian G S * Lhalf_pinv =
    Lhalf_pinvᴴ * inducedLaplacian G S * Lhalf_pinv from by rw [hpinv_herm.eq]]
  exact (inducedLaplacian_posSemidef G S).conjTranspose_mul_mul_same Lhalf_pinv

/-! ### Normalized projection sum: Lhalf_pinv * L * Lhalf_pinv = P -/

/-- The normalized graph Laplacian equals the projection P = Lhalf * Lhalf_pinv.
    Proof: Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv)
    = P * P = P (using MP4 for commutativity, MP3 for idempotence). -/
lemma normalized_laplacian_eq_proj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    Lhalf_pinv * graphLaplacian G * Lhalf_pinv = Lhalf * Lhalf_pinv := by
  rw [← hLhalf_sq]
  -- Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv
  -- = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv)   [by mul_assoc]
  -- = P * P = P  [by MP4 and MP3]
  calc Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv
      = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv) := by
        simp only [Matrix.mul_assoc]
    _ = (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) := by rw [← hMP4]
    _ = Lhalf * Lhalf_pinv := hMP3

/-- P ≤ I in Loewner order (since P is an orthogonal projection).
    Proof: (I - P) is PSD because (I - P) = (I - P)^2 for idempotent Hermitian P,
    and X^2 is PSD for any Hermitian X. -/
lemma proj_le_one
    (P : Matrix V V ℝ)
    (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) :
    ((1 : Matrix V V ℝ) - P).PosSemidef := by
  -- (I - P)^2 = I - 2P + P^2 = I - 2P + P = I - P
  -- So I - P = (I - P)^T * (I - P) is PSD
  have hQ_herm : ((1 : Matrix V V ℝ) - P).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hP_herm.eq]
  have hQ_idem : ((1 : Matrix V V ℝ) - P) * ((1 : Matrix V V ℝ) - P) =
      (1 : Matrix V V ℝ) - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP_idem, sub_self, sub_zero]
  rw [show (1 : Matrix V V ℝ) - P =
    ((1 : Matrix V V ℝ) - P)ᴴ * ((1 : Matrix V V ℝ) - P) from by
      rw [hQ_herm.eq, hQ_idem]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### Monotonicity and extraction for the BSS coloring -/

/-- Monotonicity of induced Laplacians: if S ⊆ T then L_S ≤ L_T in Loewner order. -/
lemma inducedLaplacian_mono
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) (hST : S ⊆ T) :
    (inducedLaplacian G T - inducedLaplacian G S).PosSemidef := by
  rw [inducedLaplacian_eq_lapMatrix, inducedLaplacian_eq_lapMatrix]
  exact lapMatrix_loewner_mono (inducedSubgraph_mono G hST)

omit [Fintype V] in
/-- PSD extraction: if the total sum ∑_γ M_γ is bounded by u·I and each M_γ is PSD,
    then each individual M_γ is bounded by u·I.
    Proof: u·I - M_γ = (u·I - ∑ M_γ') + ∑_{γ'≠γ} M_γ' = PSD + PSD. -/
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
