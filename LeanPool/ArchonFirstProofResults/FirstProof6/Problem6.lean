/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.DynamicColoring
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary.OneSidedBarrier

/-!
# Problem 6: Large epsilon-light vertex subsets -- Main Proof

This file contains the main theorem and its supporting lemmas.
All auxiliary infrastructure is in `Problem6Aux.lean`.

## Main theorems

- `Problem6.exists_eps_light_subset`: for every simple graph G
  and `epsilon in (0,1]`, there exists an epsilon-light subset S
  with `|S| >= epsilon/256 * |V|`
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### BSS coloring infrastructure

The BSS framework follows the informal proof's dynamic approach:
1. Spectral setup: Lhalf with Lhalf² = L (via spectral theorem)
2. Normalized edge Laplacians A_e = Lhalf_pinv * L_e * Lhalf_pinv
3. Coloring with one-sided barrier tracking monochromatic matrix M_t
4. Pullback: M_k ≤ u_k·I → each color class ε-light (via eps_light_of_loewner_bound) -/

/-- **Sub-lemma 1 (Spectral setup)**: For any graph G, there exists a Hermitian matrix
    Lhalf with Lhalf * Lhalf = graphLaplacian G (the PSD square root), constructed
    via the spectral theorem. This is Step 1 of the informal proof.
    The spectral decomposition L = U * diag(λ) * U* gives
    Lhalf = U * diag(√λ) * U*, which satisfies Lhalf² = L and IsHermitian. -/
lemma spectral_sqrt_exists
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (Lhalf : Matrix V V ℝ),
      Lhalf.IsHermitian ∧
      Lhalf * Lhalf = graphLaplacian G := by
  -- Use the spectral theorem for the PSD Hermitian graph Laplacian.
  -- L = U * diag(ev) * U* => Lhalf = U * diag(√ev) * U*
  set L := graphLaplacian G with hL_def
  have hL_psd := graphLaplacian_posSemidef G
  have hL_herm := graphLaplacian_isHermitian G
  set U := (hL_herm.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set ev := hL_herm.eigenvalues with hev_def
  have hUU : (U : Matrix V V ℝ) * (star U : Matrix V V ℝ) = 1 :=
    Unitary.coe_mul_star_self hL_herm.eigenvectorUnitary
  have hUstarU : (star U : Matrix V V ℝ) * (U : Matrix V V ℝ) = 1 :=
    Unitary.coe_star_mul_self hL_herm.eigenvectorUnitary
  have hev_nn : ∀ i, 0 ≤ ev i := hL_psd.eigenvalues_nonneg
  set sqrtEv : V → ℝ := fun i => Real.sqrt (ev i) with hsqrtEv_def
  set Lhalf := (U : Matrix V V ℝ) * diagonal sqrtEv * (star U : Matrix V V ℝ) with hLhalf_def
  have hL_eq : L = (U : Matrix V V ℝ) * diagonal ev * (star U : Matrix V V ℝ) := by
    have hspec := hL_herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at hspec
    rw [hL_def]; exact hspec
  refine ⟨Lhalf, ?_, ?_⟩
  · -- Lhalf is Hermitian
    change Lhalfᴴ = Lhalf
    rw [hLhalf_def]
    have h_diag_herm : (diagonal sqrtEv)ᴴ = diagonal sqrtEv := by
      ext i j; simp only [conjTranspose_apply, diagonal, Matrix.of_apply, star_trivial]
      split_ifs with h1 h2 h2
      · rw [h1]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    calc (U * diagonal sqrtEv * star U)ᴴ
        = (star U)ᴴ * (diagonal sqrtEv)ᴴ * Uᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = U * diagonal sqrtEv * star U := by
          simp only [star_eq_conjTranspose, conjTranspose_conjTranspose, h_diag_herm]
  · -- Lhalf * Lhalf = L
    rw [hLhalf_def, hL_eq]
    have h1 : (U : Matrix V V ℝ) * diagonal sqrtEv * (star U : Matrix V V ℝ) *
              ((U : Matrix V V ℝ) * diagonal sqrtEv * (star U : Matrix V V ℝ)) =
              (U : Matrix V V ℝ) * diagonal sqrtEv *
              ((star U : Matrix V V ℝ) * (U : Matrix V V ℝ)) *
              diagonal sqrtEv * (star U : Matrix V V ℝ) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hUstarU, Matrix.mul_one]
    have h_sq : diagonal sqrtEv * diagonal sqrtEv = diagonal ev := by
      rw [diagonal_mul_diagonal]
      congr 1; ext i
      rw [hsqrtEv_def, ← Real.sqrt_mul (hev_nn i), Real.sqrt_mul_self (hev_nn i)]
    rw [show (U : Matrix V V ℝ) * diagonal sqrtEv * diagonal sqrtEv * (star U : Matrix V V ℝ) =
        (U : Matrix V V ℝ) * (diagonal sqrtEv * diagonal sqrtEv) * (star U : Matrix V V ℝ) by
      simp only [Matrix.mul_assoc]]
    rw [h_sq]

/-- Product of unitary-diagonal-conjugate matrices:
    (U * D(f) * U★) * (U * D(g) * U★) = U * D(f·g) * U★.
    Used for spectral calculus (computing products via eigenvalue multiplication). -/
lemma unitary_diag_mul
    (U : Matrix V V ℝ) (hstarU : (star U : Matrix V V ℝ) * U = 1)
    (f g : V → ℝ) :
    (U * diagonal f * (star U : Matrix V V ℝ)) *
    (U * diagonal g * (star U : Matrix V V ℝ)) =
    U * diagonal (f * g) * (star U : Matrix V V ℝ) := by
  have h1 : (U * diagonal f * (star U : Matrix V V ℝ)) *
             (U * diagonal g * (star U : Matrix V V ℝ)) =
      U * diagonal f * ((star U : Matrix V V ℝ) * U) *
      diagonal g * (star U : Matrix V V ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, hstarU, Matrix.mul_one,
      show U * diagonal f * diagonal g * (star U : Matrix V V ℝ) =
           U * (diagonal f * diagonal g) * (star U : Matrix V V ℝ) by
        simp only [Matrix.mul_assoc]]
  congr 1; congr 1
  exact diagonal_mul_diagonal f g

omit [DecidableEq V] in
/-- For a Hermitian matrix M, there exists a Hermitian pseudo-inverse M_pinv satisfying
    the Moore-Penrose conditions:
    (1) M * M_pinv * M = M
    (2) M_pinv * M * M_pinv = M_pinv
    (3) M * M_pinv is idempotent (a projection)
    Constructed via spectral decomposition: if M = U * diag(λ) * U★,
    then M_pinv = U * diag(λ⁻¹) * U★ where λ⁻¹(i) = 0 if λ(i) = 0. -/
lemma hermitian_pseudo_inverse_exists
    (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    ∃ (M_pinv : Matrix V V ℝ),
      M_pinv.IsHermitian ∧
      M * M_pinv * M = M ∧
      M_pinv * M * M_pinv = M_pinv ∧
      (M * M_pinv) * (M * M_pinv) = M * M_pinv ∧
      M * M_pinv = M_pinv * M := by
  classical
  set U := (hM.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set ev := hM.eigenvalues with hev_def
  have hUstarU : (star U : Matrix V V ℝ) * U = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hM_eq : M = U * diagonal ev * (star U : Matrix V V ℝ) := by
    have hspec := hM.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at hspec
    exact hspec
  -- Pseudo-inverse eigenvalues: invert nonzero, keep zero
  set pinvEv : V → ℝ := fun i => if ev i = 0 then 0 else (ev i)⁻¹ with hpinvEv_def
  refine ⟨U * diagonal pinvEv * (star U : Matrix V V ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · -- M_pinv is Hermitian: U * diag(real) * U★ is Hermitian for real diagonal
    change (U * diagonal pinvEv * (star U : Matrix V V ℝ))ᴴ =
         U * diagonal pinvEv * (star U : Matrix V V ℝ)
    have h_diag : (diagonal pinvEv)ᴴ = diagonal pinvEv := by
      ext i j; simp only [conjTranspose_apply, diagonal, Matrix.of_apply, star_trivial]
      split_ifs with h1 h2 h2
      · rw [h1]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    calc (U * diagonal pinvEv * (star U : Matrix V V ℝ))ᴴ
        = (star U : Matrix V V ℝ)ᴴ * (diagonal pinvEv)ᴴ * Uᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = U * diagonal pinvEv * (star U : Matrix V V ℝ) := by
          simp only [star_eq_conjTranspose, conjTranspose_conjTranspose, h_diag]
  · -- (1) M * M_pinv * M = M via eigenvalue identity ev * pinvEv * ev = ev
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU (ev * pinvEv) ev]
    suffices h : ev * pinvEv * ev = ev by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  · -- (2) M_pinv * M * M_pinv = M_pinv via eigenvalue identity pinvEv * ev * pinvEv = pinvEv
    rw [hM_eq, unitary_diag_mul U hUstarU pinvEv ev,
        unitary_diag_mul U hUstarU (pinvEv * ev) pinvEv]
    suffices h : pinvEv * ev * pinvEv = pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [inv_mul_cancel₀ h, one_mul]
  · -- (3) M * M_pinv is idempotent via (ev * pinvEv)² = ev * pinvEv
    have hprod : M * (U * diagonal pinvEv * (star U : Matrix V V ℝ)) =
        U * diagonal (ev * pinvEv) * (star U : Matrix V V ℝ) := by
      rw [hM_eq]; exact unitary_diag_mul U hUstarU ev pinvEv
    rw [hprod, unitary_diag_mul U hUstarU (ev * pinvEv) (ev * pinvEv)]
    suffices h : ev * pinvEv * (ev * pinvEv) = ev * pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h]; simp
  · -- (4) Commutativity: M * M_pinv = M_pinv * M (diagonal multiplication commutes)
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU pinvEv ev]
    congr 1; congr 1; ext i; simp [mul_comm]

/-! #### Dynamic BSS coloring (Steps 1–5 combined)
The informal proof (Steps 3–5) uses a **dynamic** coloring process:
  1. Per-edge matrices: A_e := L^{-1/2} L_e L^{-1/2} with ∑_e A_e = I on range(L)
  2. Track M_t := ∑_{monochromatic edges at time t} A_e (DYNAMIC, depends on current coloring)
  3. At time t: color vertex v with γ, increment M_{t+1} = M_t + B_v^γ where
     B_v^γ = ∑_{u ∈ T, col(u)=γ, uv∈E} A_{uv}
  4. BSS barrier (Lemma 6.1) maintains M_t ≺ u_t·I at each step
  5. After k = n/4 steps: M_k = ∑_a L^{-1/2} L_{S_a} L^{-1/2} (by construction)
  6. Since M_k ≺ u_k·I ≺ ε·I, each color class S_a is ε-light
The proof is decomposed into:
  (A) `dynamic_barrier_coloring`: The core BSS dynamic coloring induction that
      produces a PartialColoring with per-color barrier bounds on normalized monochromatic sums.
  (B) `bss_dynamic_coloring`: Combines (A) with `pinv_pullback_eq` and
      `eps_light_of_loewner_bound` to convert barrier bounds to ε-lightness. -/

/-- Off-diagonal entry equality for the cross-edge decomposition:
    for i ≠ j, (graphLaplacian G - DS) i j = (graphLaplacian G_same) i j. -/
lemma cross_edge_off_diagonal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (pc : PartialColoring V r)
    (S : Fin r → Finset V)
    (hS : S = fun γ => pc.colored.filter (fun w => pc.color w = γ))
    (G_same : SimpleGraph V) [DecidableRel G_same.Adj]
    (hG_same : ∀ a b, G_same.Adj a b ↔ (G.Adj a b ∧ (a ∈ pc.colored ↔ b ∈ pc.colored)))
    (DS : Matrix V V ℝ)
    (hDS : DS = ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
      (inducedLaplacian G (S γ ∪ {v}) - inducedLaplacian G (S γ)))
    (i j : V) (hij : i ≠ j) :
    (graphLaplacian G - DS) i j = (graphLaplacian G_same) i j := by
  -- Helper: off-diagonal entry of graphLaplacian
  have gl_off : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (a b : V), a ≠ b →
      graphLaplacian H a b = if H.Adj a b then -1 else 0 := by
    intro H _ a b hab; simp only [graphLaplacian, Matrix.of_apply, hab, ↓reduceIte]
  -- Helper: off-diagonal entry of inducedLaplacian
  have il_off : ∀ (T : Finset V) (a b : V), a ≠ b →
      inducedLaplacian G T a b = if G.Adj a b ∧ a ∈ T ∧ b ∈ T then -1 else 0 := by
    intro T a b hab; simp only [inducedLaplacian, Matrix.of_apply, hab, ↓reduceIte]
  simp only [Matrix.sub_apply, gl_off G i j hij, gl_off G_same i j hij]
  rw [hDS]; simp only [Matrix.sum_apply, Matrix.sub_apply, il_off _ i j hij]
  by_cases hadj : G.Adj i j
  · -- G.Adj i j
    rw [if_pos hadj]
    by_cases hcross : ¬(i ∈ pc.colored ↔ j ∈ pc.colored)
    · -- Cross-edge: G_same has no edge, double sum = -1
      rw [if_neg (show ¬G_same.Adj i j from fun h => hcross ((hG_same i j).mp h).2)]
      -- Base sets don't contain both endpoints (cross-edge)
      have h_base : ∀ (γ : Fin r), ¬(G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ) := by
        intro γ ⟨_, hi, hj⟩
        rw [hS] at hi hj; simp only [Finset.mem_filter] at hi hj
        exact hcross ⟨fun _ => hj.1, fun _ => hi.1⟩
      simp_rw [if_neg (h_base _), sub_zero]
      have h_cases : (i ∈ pc.colored ∧ j ∉ pc.colored) ∨
          (i ∉ pc.colored ∧ j ∈ pc.colored) := by
        by_cases hi : i ∈ pc.colored
        · exact Or.inl ⟨hi, fun hj => hcross ⟨fun _ => hj, fun _ => hi⟩⟩
        · exact Or.inr ⟨hi, by_contra fun hj =>
            hcross ⟨fun h => absurd h hi,
                    fun h => absurd h hj⟩⟩
      -- Goal: -1 - ∑ v, ∑ γ, (if ... then -1 else 0) = 0
      suffices h_sum :
          ∑ v ∈ Finset.univ.filter (· ∉ pc.colored),
          ∑ γ : Fin r,
          (if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧
              j ∈ (S γ ∪ {v})
            then (-1 : ℝ) else 0) = -1 by
        linarith
      rcases h_cases with ⟨hic, hnjc⟩ | ⟨hnic, hjc⟩
      · -- i ∈ colored, j ∉ colored: only (v=j, γ=color i) contributes
        rw [Finset.sum_eq_single_of_mem j
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnjc⟩)]
        · rw [Finset.sum_eq_single_of_mem (pc.color i) (Finset.mem_univ _)]
          · rw [if_pos]
            refine ⟨hadj,
              Finset.mem_union_left _ ?_,
              Finset.mem_union_right _
                (Finset.mem_singleton_self _)⟩
            rw [hS]; exact Finset.mem_filter.mpr ⟨hic, rfl⟩
          · intro γ _ hne; rw [if_neg]; intro ⟨_, hi_mem, _⟩
            simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hi_mem
            exact hi_mem.elim (fun ⟨_, h⟩ => hne h.symm) (fun h => hnjc (h ▸ hic))
        · intro v _ hne
          apply Finset.sum_eq_zero; intro γ _; rw [if_neg]; intro ⟨_, _, hj_mem⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hj_mem
          exact hj_mem.elim (fun ⟨h, _⟩ => hnjc h) (fun h => hne h.symm)
      · -- i ∉ colored, j ∈ colored: only (v=i, γ=color j) contributes
        rw [Finset.sum_eq_single_of_mem i
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnic⟩)]
        · rw [Finset.sum_eq_single_of_mem (pc.color j) (Finset.mem_univ _)]
          · rw [if_pos]
            refine ⟨hadj,
              Finset.mem_union_right _
                (Finset.mem_singleton_self _),
              Finset.mem_union_left _ ?_⟩
            rw [hS]; exact Finset.mem_filter.mpr ⟨hjc, rfl⟩
          · intro γ _ hne; rw [if_neg]; intro ⟨_, _, hj_mem⟩
            simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hj_mem
            exact hj_mem.elim (fun ⟨_, h⟩ => hne h.symm) (fun h => hnic (h ▸ hjc))
        · intro v _ hne
          apply Finset.sum_eq_zero; intro γ _; rw [if_neg]; intro ⟨_, hi_mem, _⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at hi_mem
          exact hi_mem.elim (fun ⟨h, _⟩ => hnic h) (fun h => hne h.symm)
    · -- Same-status edge: G_same has edge, double sum = 0
      have hcross' : i ∈ pc.colored ↔ j ∈ pc.colored := not_not.mp hcross
      rw [if_pos ((hG_same i j).mpr ⟨hadj, hcross'⟩)]
      -- Goal: -1 - ∑ ... = -1, need ∑ ... = 0
      suffices h_sum :
          ∑ v ∈ Finset.univ.filter (· ∉ pc.colored),
          ∑ γ : Fin r,
          ((if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧
               j ∈ (S γ ∪ {v})
             then (-1 : ℝ) else 0) -
           (if G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ then (-1 : ℝ) else 0)) = 0 by
        linarith
      apply Finset.sum_eq_zero; intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      apply Finset.sum_eq_zero; intro γ _
      have h_iff : (G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧ j ∈ (S γ ∪ {v})) ↔
          (G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ) := by
        constructor
        · intro ⟨h1, h2, h3⟩
          simp only [hS, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton] at h2 h3
          refine ⟨h1, ?_, ?_⟩
          · rcases h2 with h2 | rfl
            · rw [hS]; exact Finset.mem_filter.mpr h2
            · rcases h3 with ⟨hjc, _⟩ | rfl
              · exact absurd (hcross'.mpr hjc) hv
              · exact absurd rfl hij
          · rcases h3 with h3 | rfl
            · rw [hS]; exact Finset.mem_filter.mpr h3
            · rcases h2 with ⟨hic, _⟩ | rfl
              · exact absurd (hcross'.mp hic) hv
              · exact absurd rfl.symm hij
        · intro ⟨h1, h2, h3⟩
          exact ⟨h1, Finset.mem_union_left _ h2, Finset.mem_union_left _ h3⟩
      simp only [h_iff, sub_self]
  · -- not G.Adj i j: L = 0, all terms vanish
    rw [if_neg hadj, if_neg (show ¬G_same.Adj i j from
      fun h => hadj ((hG_same i j).mp h).1)]
    -- Goal: 0 - ∑ ... = 0, need ∑ ... = 0
    suffices h_sum : ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
        ((if G.Adj i j ∧ i ∈ (S γ ∪ {v}) ∧ j ∈ (S γ ∪ {v}) then (-1 : ℝ) else 0) -
         (if G.Adj i j ∧ i ∈ S γ ∧ j ∈ S γ then (-1 : ℝ) else 0)) = 0 by
      linarith
    apply Finset.sum_eq_zero; intro v _
    apply Finset.sum_eq_zero; intro γ _
    have h_neg : ∀ P, ¬(G.Adj i j ∧ P) := fun _ h => hadj h.1
    simp only [if_neg (h_neg _), sub_self]

omit [DecidableEq V] in
/-- Diagonal entry derivation for the cross-edge decomposition:
    derives diagonal from row sums and off-diagonal matching. -/
lemma cross_edge_diagonal
    (L DS R : Matrix V V ℝ)
    (h_off_diag : ∀ (a b : V), a ≠ b → (L - DS) a b = R a b)
    (h_row_LHS : ∀ a, ∑ b, (L - DS) a b = 0)
    (h_row_RHS : ∀ a, ∑ b, R a b = 0)
    (i : V) :
    (L - DS) i i = R i i := by
  classical
  have h1 := h_row_LHS i
  have h2 := h_row_RHS i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1 h2
  have h3 : ∑ j ∈ Finset.univ.erase i, (L - DS) i j =
      ∑ j ∈ Finset.univ.erase i, R i j :=
    Finset.sum_congr rfl fun j hj =>
      h_off_diag i j (Finset.ne_of_mem_erase hj).symm
  linarith

/-- The cross-edge sum decomposition is PSD: the difference between the graph Laplacian and
    the double sum ∑_{v uncolored} ∑_γ (L_{S_γ ∪ {v}} - L_{S_γ}) is PSD,
    equaling the Laplacian of the "same-status" subgraph (edges where both endpoints
    have the same colored/uncolored status). -/
lemma cross_edge_sum_le_graphLaplacian
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (pc : PartialColoring V r) :
    (graphLaplacian G -
      ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
        (inducedLaplacian G (pc.colored.filter (fun w => pc.color w = γ) ∪ {v}) -
         inducedLaplacian G (pc.colored.filter (fun w => pc.color w = γ)))).PosSemidef := by
  -- Strategy: L - double_sum = graphLaplacian G_same where G_same keeps edges
  -- with both endpoints having the same colored/uncolored status. Then PSD.
  let G_same : SimpleGraph V :=
    ⟨fun v w => G.Adj v w ∧ (v ∈ pc.colored ↔ w ∈ pc.colored),
     fun a b ⟨h, hiff⟩ => ⟨G.symm h, hiff.symm⟩,
     ⟨fun v ⟨h, _⟩ => G.loopless.irrefl v h⟩⟩
  haveI : DecidableRel G_same.Adj := inferInstance
  let S : Fin r → Finset V := fun γ => pc.colored.filter (fun w => pc.color w = γ)
  suffices h_eq : graphLaplacian G -
      ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
        (inducedLaplacian G (S γ ∪ {v}) - inducedLaplacian G (S γ)) =
      graphLaplacian G_same by
    rw [h_eq]; exact graphLaplacian_posSemidef G_same
  -- Abbreviate the double sum matrix
  set DS := ∑ v ∈ Finset.univ.filter (· ∉ pc.colored), ∑ γ : Fin r,
    (inducedLaplacian G (S γ ∪ {v}) - inducedLaplacian G (S γ)) with DS_def
  -- Helper: graphLaplacian row sum = 0
  have laplacian_row_sum : ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (a : V),
      ∑ b, graphLaplacian H a b = 0 := by
    intro H _ a
    simp only [graphLaplacian, Matrix.of_apply]
    rw [Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    have hfilt_eq : Finset.univ.filter (fun x => a = x) = {a} := by ext x; simp [eq_comm]
    rw [hfilt_eq, Finset.sum_singleton]
    simp only [Finset.sum_const]
    have : (Finset.univ.filter (fun x => ¬a = x)).filter (H.Adj a) =
        Finset.univ.filter (H.Adj a) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun hab => H.loopless.irrefl a (hab ▸ h), h⟩⟩
    rw [this]; simp [nsmul_eq_mul]
  -- Helper: inducedLaplacian row sum = 0
  have il_row_sum : ∀ (T : Finset V) (a : V), ∑ b, inducedLaplacian G T a b = 0 := by
    intro T a
    simp only [inducedLaplacian, Matrix.of_apply]
    rw [Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    have hfilt_eq : Finset.univ.filter (fun x => a = x) = {a} := by ext x; simp [eq_comm]
    rw [hfilt_eq, Finset.sum_singleton]
    -- Reconcile filter orders:
    -- (a ∈ T ∧ k ∈ T ∧ G.Adj a k) vs (G.Adj a k ∧ a ∈ T ∧ k ∈ T)
    have h_filt : Finset.univ.filter (fun k => a ∈ T ∧ k ∈ T ∧ G.Adj a k) =
        Finset.univ.filter (fun k => G.Adj a k ∧ a ∈ T ∧ k ∈ T) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    rw [h_filt]
    simp only [Finset.sum_const]
    have : (Finset.univ.filter (fun x => ¬a = x)).filter
        (fun k => G.Adj a k ∧ a ∈ T ∧ k ∈ T) =
        Finset.univ.filter (fun k => G.Adj a k ∧ a ∈ T ∧ k ∈ T) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨_, h⟩ => h, fun ⟨h, _, _⟩ =>
        ⟨fun hab => G.loopless.irrefl a (hab ▸ h),
         h, ‹_›, ‹_›⟩⟩
    rw [this]; simp [nsmul_eq_mul]
  -- Off-diagonal equality via cross_edge_off_diagonal
  have hG_same : ∀ a b, G_same.Adj a b ↔
      (G.Adj a b ∧ (a ∈ pc.colored ↔ b ∈ pc.colored)) :=
    fun a b => Iff.rfl
  have h_off_diag : ∀ (a b : V), a ≠ b →
      (graphLaplacian G - DS) a b = (graphLaplacian G_same) a b := by
    intro a b hab
    exact cross_edge_off_diagonal G r pc S rfl G_same hG_same DS DS_def a b hab
  -- Row sums = 0 for both sides
  have h_row_RHS : ∀ a, ∑ b, (graphLaplacian G_same) a b = 0 := laplacian_row_sum G_same
  have h_row_LHS : ∀ a, ∑ b, (graphLaplacian G - DS) a b = 0 := by
    intro a
    simp only [Matrix.sub_apply]
    rw [Finset.sum_sub_distrib, laplacian_row_sum G a, zero_sub, neg_eq_zero]
    -- DS row sum = 0: push application inside, swap sums, use inducedLaplacian row sum
    simp only [DS, Matrix.sum_apply, Matrix.sub_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro v _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro γ _
    rw [Finset.sum_sub_distrib, il_row_sum, il_row_sum, sub_self]
  -- Entry-by-entry equality from off-diagonal + row sums
  ext i j
  by_cases hij : i = j
  · subst hij; exact cross_edge_diagonal _ DS _ h_off_diag h_row_LHS h_row_RHS i
  · exact h_off_diag i j hij

/-- Base case of BSS induction: empty coloring, M_0 = 0, Φ_{ε/2}(0) = 2n/ε. -/
lemma total_barrier_bound_base
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hr_pos : 0 < r)
    (Lhalf_pinv : Matrix V V ℝ)
    (h_lap_le1 : ∀ T : Finset V, T.card ≤ 1 → inducedLaplacian G T = 0) :
    ∃ pc : PartialColoring V r,
      pc.colored.card = 0 ∧
      ((ε / 2 + (0 : ℝ) * (ε / (Fintype.card V : ℝ))) • (1 : Matrix V V ℝ) -
        ∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv).PosDef ∧
      barrierPotential (ε / 2 + (0 : ℝ) * (ε / (Fintype.card V : ℝ)))
        (∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv) ≤ 2 * (Fintype.card V : ℝ) / ε := by
  have h_sum_zero : ∑ γ : Fin r,
      Lhalf_pinv * inducedLaplacian G
        ((∅ : Finset V).filter (fun v =>
          (fun (_ : V) => (⟨0, hr_pos⟩ : Fin r)) v = γ)) *
        Lhalf_pinv = 0 := by
    apply Finset.sum_eq_zero; intro γ _
    simp only [Finset.filter_empty]
    rw [h_lap_le1 _ (by simp), Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨⟨∅, fun _ => ⟨0, hr_pos⟩⟩, by simp, ?_, ?_⟩
  · -- PosDef: (ε/2 · I - 0).PosDef
    simp only [zero_mul, add_zero, h_sum_zero, sub_zero]
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal (fun _ => by linarith)
  · -- Potential bound: Φ_{ε/2}(0) = 2n/ε
    simp only [zero_mul, add_zero, h_sum_zero]
    unfold barrierPotential
    rw [sub_zero]
    have h_inv : ((ε / 2) • (1 : Matrix V V ℝ))⁻¹ =
        (2 / ε) • (1 : Matrix V V ℝ) :=
      Matrix.inv_eq_right_inv (by rw [smul_mul_smul_comm, one_mul,
        show ε / 2 * (2 / ε) = 1 from by field_simp, one_smul])
    rw [h_inv, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      div_mul_eq_mul_div]

/-- Step F-G of `good_pair_exists`: the sum of the cross-edge contributions over uncolored
vertices and colors is bounded above by `I` in the Loewner order. -/
private lemma good_pair_sum_B_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (pc_t : PartialColoring V r) (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian) (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    ((1 : Matrix V V ℝ) -
      ∑ v ∈ Finset.univ.filter (· ∉ pc_t.colored), ∑ γ : Fin r,
        Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv).PosSemidef := by
  set uncolored := Finset.univ.filter (· ∉ pc_t.colored) with h_uncol_def
  -- Factor through the cross-edge Loewner bound
  have h_cross := cross_edge_sum_le_graphLaplacian G r pc_t
  -- Normalize: Lhalf_pinv * ∑ ΔL * Lhalf_pinv ≤ Lhalf_pinv * L * Lhalf_pinv = P
  have h_normalized : (Lhalf_pinv * graphLaplacian G * Lhalf_pinv -
      ∑ v ∈ uncolored, ∑ γ : Fin r,
        Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv).PosSemidef := by
    -- Factor out Lhalf_pinv: Lp * (L - ∑ΔL) * Lp is PSD since (L - ∑ΔL) is PSD
    have h_factor : Lhalf_pinv * graphLaplacian G * Lhalf_pinv -
        ∑ v ∈ uncolored, ∑ γ : Fin r,
          Lhalf_pinv * (inducedLaplacian G
            (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
            inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
          Lhalf_pinv =
        Lhalf_pinvᴴ * (graphLaplacian G -
          ∑ v ∈ uncolored, ∑ γ : Fin r,
            (inducedLaplacian G
              (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
             inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ)))) *
        Lhalf_pinv := by
      rw [hpinv_herm.eq]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul,
        Matrix.mul_assoc]
    rw [h_factor]
    exact h_cross.conjTranspose_mul_mul_same Lhalf_pinv
  -- P = Lhalf_pinv * L * Lhalf_pinv = Lhalf * Lhalf_pinv (projection)
  have hP_eq : Lhalf_pinv * graphLaplacian G * Lhalf_pinv = Lhalf * Lhalf_pinv :=
    normalized_laplacian_eq_proj G Lhalf Lhalf_pinv hLhalf_sq hMP3 hMP4
  -- P is Hermitian and idempotent
  have hP_herm : (Lhalf * Lhalf_pinv).IsHermitian := by
    change (Lhalf * Lhalf_pinv)ᴴ = Lhalf * Lhalf_pinv
    rw [Matrix.conjTranspose_mul, hpinv_herm.eq, hLhalf_herm.eq, ← hMP4]
  -- I - P is PSD
  have hI_sub_P := proj_le_one (Lhalf * Lhalf_pinv) hP_herm hMP3
  -- (I - ∑ B) = (I - P) + (P - ∑ B) = PSD + PSD
  have h_eq : (1 : Matrix V V ℝ) -
      ∑ v ∈ uncolored, ∑ γ : Fin r,
        Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv =
      ((1 : Matrix V V ℝ) - Lhalf_pinv * graphLaplacian G * Lhalf_pinv) +
      (Lhalf_pinv * graphLaplacian G * Lhalf_pinv -
        ∑ v ∈ uncolored, ∑ γ : Fin r,
          Lhalf_pinv * (inducedLaplacian G
            (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
            inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
          Lhalf_pinv) := by abel
  rw [h_eq, hP_eq]
  rw [hP_eq] at h_normalized
  exact hI_sub_P.add h_normalized

/-- Step K of `good_pair_exists`: from the no-good-pair assumption, every uncolored vertex and
color incurs cost at least `1`. -/
private lemma good_pair_cost_ge_one (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (pc_t : PartialColoring V r) (Lhalf_pinv U : Matrix V V ℝ) (gap : ℝ) (hgap_pos : 0 < gap)
    (hU_pd : U.PosDef) (hU_sq_psd : (U * U).PosSemidef)
    (hB_psd_of : ∀ v γ, (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv).PosSemidef)
    (h_no_good_pair : ∀ (v₀ : V), v₀ ∉ pc_t.colored → ∀ (γ₀ : Fin r),
      ¬((Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ₀) ∪ {v₀}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ₀))) *
        Lhalf_pinv * U).trace < 1 ∧
        ((Lhalf_pinv * (inducedLaplacian G
            (pc_t.colored.filter (fun w => pc_t.color w = γ₀) ∪ {v₀}) -
            inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ₀))) *
          Lhalf_pinv * U).trace +
          (Lhalf_pinv * (inducedLaplacian G
            (pc_t.colored.filter (fun w => pc_t.color w = γ₀) ∪ {v₀}) -
            inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ₀))) *
          Lhalf_pinv * U * U).trace / gap ≤ 1))) :
    ∀ v ∈ Finset.univ.filter (· ∉ pc_t.colored), ∀ γ : Fin r,
      1 ≤ (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U).trace +
      (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U * U).trace / gap := by
  intro v hv γ
  have hv_uncol : v ∉ pc_t.colored := (Finset.mem_filter.mp hv).2
  set ΔL_vγ := inducedLaplacian G
    (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
    inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ)) with hΔL_vγ_def
  set B_vγ := Lhalf_pinv * ΔL_vγ * Lhalf_pinv with hB_vγ_def
  have hBU2_div_nn : 0 ≤ (B_vγ * U * U).trace / gap := by
    apply div_nonneg
    · rw [Matrix.mul_assoc]
      exact trace_mul_nonneg_of_posSemidef _ (U * U) (hB_psd_of v γ) hU_sq_psd
    · exact le_of_lt hgap_pos
  have hBU_nn : 0 ≤ (B_vγ * U).trace :=
    trace_mul_nonneg_of_posSemidef _ U (hB_psd_of v γ) hU_pd.posSemidef
  -- From h_no_good_pair: ¬(trBU < 1 ∧ cost ≤ 1)
  have h_neg := h_no_good_pair v hv_uncol γ
  by_cases hlt : (B_vγ * U).trace < 1
  · by_contra h_le; push Not at h_le
    exact h_neg ⟨hlt, le_of_lt h_le⟩
  · push Not at hlt; linarith

/-- BSS averaging: ∃ good (v₀, γ₀) pair with barrier conditions.
    Core by_contra argument of the BSS dynamic coloring. -/
lemma good_pair_exists [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (hn : 4 ≤ Fintype.card V)
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf)
    (pc_t : PartialColoring V r)
    (t : ℕ) (ht : t + 1 ≤ Fintype.card V / 4)
    (hcard_t : pc_t.colored.card = t)
    (hpd_t : ((ε / 2 + (t : ℝ) * (ε / (Fintype.card V : ℝ))) • (1 : Matrix V V ℝ) -
      ∑ γ : Fin r,
        Lhalf_pinv * inducedLaplacian G
          (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
          Lhalf_pinv).PosDef)
    (hphi_t : barrierPotential (ε / 2 + (t : ℝ) * (ε / (Fintype.card V : ℝ)))
      (∑ γ : Fin r,
        Lhalf_pinv * inducedLaplacian G
          (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
          Lhalf_pinv) ≤ 2 * (Fintype.card V : ℝ) / ε) :
    let M_t := ∑ γ : Fin r, Lhalf_pinv *
      inducedLaplacian G (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
      Lhalf_pinv
    let u_t := ε / 2 + (t : ℝ) * (ε / (Fintype.card V : ℝ))
    let u' := ε / 2 + ((t : ℝ) + 1) * (ε / (Fintype.card V : ℝ))
    let U := (u' • (1 : Matrix V V ℝ) - M_t)⁻¹
    ∃ (v₀ : V) (_ : v₀ ∉ pc_t.colored) (γ₀ : Fin r),
      let S_γ₀ := pc_t.colored.filter (fun v => pc_t.color v = γ₀)
      let B := Lhalf_pinv * (inducedLaplacian G (S_γ₀ ∪ {v₀}) -
        inducedLaplacian G S_γ₀) * Lhalf_pinv
      (B * U).trace < 1 ∧
      ((B * U).trace + (B * U * U).trace /
        (barrierPotential u_t M_t - barrierPotential u' M_t) ≤ 1) := by
  intro M_t u_t u' U
  set n := Fintype.card V with hn_def
  have hr_pos : 0 < r := by rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hδ_pos : (0 : ℝ) < ε / (n : ℝ) := div_pos hε hn_pos
  have hu_lt_u' : u_t < u' := by change ε / 2 + (t : ℝ) * (ε / (n : ℝ)) <
      ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ)); linarith
  -- (u'·I - M_t).PosDef by barrier_shift_posDef
  have hpd' : (u' • (1 : Matrix V V ℝ) - M_t).PosDef :=
    barrier_shift_posDef M_t u_t u' hu_lt_u' hpd_t
  -- U = (u'·I - M_t)⁻¹ is PD
  have hU_pd : U.PosDef := hpd'.inv
  -- Find an uncolored vertex
  have ht_lt_n : t < n := by omega
  have h_exists_uncolored : ∃ v₀ : V, v₀ ∉ pc_t.colored := by
    by_contra hall; push Not at hall
    have : Finset.univ ⊆ pc_t.colored := fun x _ => hall x
    have := Finset.card_le_card this
    rw [Finset.card_univ, ← hn_def, hcard_t] at this; omega
  -- Step A: Define the set of uncolored vertices
  set uncolored := Finset.univ.filter (· ∉ pc_t.colored) with h_uncol_def
  have h_uncol_card : uncolored.card = n - t := by
    have h1 : uncolored = Finset.univ \ pc_t.colored := by
      rw [h_uncol_def]; ext v; simp [Finset.mem_sdiff, Finset.mem_filter]
    rw [h1]
    have hsub : pc_t.colored ⊆ Finset.univ := Finset.subset_univ _
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, hcard_t]
  -- Step B: m = n - t ≥ 3n/4 (since t < k = n/4)
  set m := n - t with hm_def
  have hm_pos : 0 < m := by omega
  have hm_large : 4 * m ≥ 3 * n := by omega
  -- Step C: gap > 0
  set gap := barrierPotential u_t M_t - barrierPotential u' M_t with hgap_def
  have hgap_pos : 0 < gap := barrier_gap_pos M_t u_t u' hu_lt_u' hpd_t
  -- Step D: gap ≥ (ε/n) * tr(U²)
  have hU_sq_psd : (U * U).PosSemidef := by
    rw [show U * U = Uᴴ * U from by rw [hU_pd.isHermitian]]
    exact Matrix.posSemidef_conjTranspose_mul_self U
  have hgap_bound : gap ≥ (u' - u_t) * (U * U).trace :=
    barrier_potential_decrease M_t u_t u' hu_lt_u' hpd_t
  have hu_diff : u' - u_t = ε / (n : ℝ) := by
    change ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ)) - (ε / 2 + (t : ℝ) * (ε / (n : ℝ))) =
      ε / (n : ℝ); ring
  -- Step E: tr(U) ≤ 2n/ε (barrier potential monotonicity)
  have htrU_eq : U.trace = barrierPotential u' M_t := by
    unfold barrierPotential; rfl
  have hphi_u'_le : barrierPotential u' M_t ≤ barrierPotential u_t M_t :=
    le_of_lt (sub_pos.mp hgap_pos)
  have htrU_bound : U.trace ≤ 2 * (n : ℝ) / ε := by
    rw [htrU_eq]; linarith
  -- Step F-G: ∑_{v∉colored} ∑_γ B_{v,γ} ≤ I in Loewner order
  have h_sum_B_le_I : ((1 : Matrix V V ℝ) -
      ∑ v ∈ uncolored, ∑ γ : Fin r,
        Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv).PosSemidef :=
    good_pair_sum_B_le_one G r pc_t Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP3 hMP4
  -- Step H: By contradiction — assume no good pair exists
  by_contra h_no_good_pair
  simp only [not_exists] at h_no_good_pair
  -- Helper: B_{v,γ} is PSD for any v, γ
  have hB_psd_of : ∀ v γ, (Lhalf_pinv * (inducedLaplacian G
      (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
      inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
    Lhalf_pinv).PosSemidef := by
    intro v γ
    rw [show Lhalf_pinv * _ * Lhalf_pinv =
      Lhalf_pinvᴴ * _ * Lhalf_pinv from by rw [hpinv_herm.eq]]
    exact (inducedLaplacian_mono G _ _ Finset.subset_union_left).conjTranspose_mul_mul_same _
  -- Abbreviate the sum of B matrices (same as in h_sum_B_le_I)
  set sumB := ∑ v ∈ uncolored, ∑ γ : Fin r,
    Lhalf_pinv * (inducedLaplacian G
      (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
      inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
    Lhalf_pinv with h_sumB_def
  -- Step I: tr(sumB * U) ≤ tr(U) and tr(sumB * U²) ≤ tr(U²)
  have h_sumBU_le : (sumB * U).trace ≤ U.trace := by
    have h := trace_mul_le_of_loewner sumB (1 : Matrix V V ℝ) U h_sum_B_le_I hU_pd.posSemidef
    rwa [one_mul] at h
  have h_sumBUU_le : (sumB * (U * U)).trace ≤ (U * U).trace := by
    have h := trace_mul_le_of_loewner sumB (1 : Matrix V V ℝ) (U * U) h_sum_B_le_I hU_sq_psd
    rwa [one_mul] at h
  -- Step J: Express sum of individual traces in terms of sumB
  have h_sum_trBU : ∑ v ∈ uncolored, ∑ γ : Fin r,
      (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U).trace = (sumB * U).trace := by
    symm; rw [h_sumB_def, Finset.sum_mul, Matrix.trace_sum]
    congr 1; ext1 v; rw [Finset.sum_mul, Matrix.trace_sum]
  have h_sum_trBUU : ∑ v ∈ uncolored, ∑ γ : Fin r,
      (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U * U).trace = (sumB * (U * U)).trace := by
    symm; rw [h_sumB_def, Finset.sum_mul, Matrix.trace_sum]
    congr 1; ext1 v; rw [Finset.sum_mul, Matrix.trace_sum]
    congr 1; ext1 γ; simp only [Matrix.mul_assoc]
  -- Step K: For each uncolored v and color γ, cost ≥ 1
  have h_cost_ge_1 : ∀ v ∈ uncolored, ∀ γ : Fin r,
      1 ≤ (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U).trace +
      (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U * U).trace / gap :=
    good_pair_cost_ge_one G r pc_t Lhalf_pinv U gap hgap_pos hU_pd hU_sq_psd hB_psd_of
      h_no_good_pair
  -- Step L: Sum of costs ≥ m * r
  have h_sum_ge : (m : ℝ) * (r : ℝ) ≤
      ∑ v ∈ uncolored, ∑ γ : Fin r,
        ((Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv * U).trace +
        (Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv * U * U).trace / gap) := by
    calc (m : ℝ) * (r : ℝ) = (uncolored.card : ℝ) * (r : ℝ) := by rw [h_uncol_card]
      _ = ∑ _ ∈ uncolored, ∑ _ : Fin r, (1 : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.smul_one_eq_cast]; ring
      _ ≤ _ := by gcongr with v hv γ _; exact h_cost_ge_1 v hv γ
  -- Step M: ∑(trBU + trBU2/gap) = ∑trBU + (∑trBU2)/gap ≤ tr(U) + tr(U²)/gap
  have h_sum_le : ∑ v ∈ uncolored, ∑ γ : Fin r,
      ((Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U).trace +
      (Lhalf_pinv * (inducedLaplacian G
        (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
        inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
      Lhalf_pinv * U * U).trace / gap) ≤
      U.trace + (U * U).trace / gap := by
    -- Split: ∑(a + b/c) = ∑a + (∑b)/c
    have h_split : ∀ (f g : V → Fin r → ℝ) (c : ℝ),
      ∑ v ∈ uncolored, ∑ γ : Fin r, (f v γ + g v γ / c) =
      (∑ v ∈ uncolored, ∑ γ : Fin r, f v γ) +
      (∑ v ∈ uncolored, ∑ γ : Fin r, g v γ) / c := by
      intro f g c
      simp_rw [Finset.sum_add_distrib]
      congr 1; rw [Finset.sum_div]; congr 1; ext1 v; rw [Finset.sum_div]
    rw [h_split]
    have h_nn : 0 ≤ (∑ v ∈ uncolored, ∑ γ : Fin r,
        (Lhalf_pinv * (inducedLaplacian G
          (pc_t.colored.filter (fun w => pc_t.color w = γ) ∪ {v}) -
          inducedLaplacian G (pc_t.colored.filter (fun w => pc_t.color w = γ))) *
        Lhalf_pinv * U * U).trace) := by
      apply Finset.sum_nonneg; intro v _; apply Finset.sum_nonneg; intro γ _
      rw [Matrix.mul_assoc]
      exact trace_mul_nonneg_of_posSemidef _ (U * U) (hB_psd_of v γ) hU_sq_psd
    gcongr
    · rw [h_sum_trBU]; exact h_sumBU_le
    · rw [h_sum_trBUU]; exact h_sumBUU_le
  -- Step N: tr(U²)/gap ≤ n/ε
  have htrU2_over_gap : (U * U).trace / gap ≤ (n : ℝ) / ε := by
    have h1 : gap ≥ (ε / (n : ℝ)) * (U * U).trace := by
      calc gap ≥ (u' - u_t) * (U * U).trace := hgap_bound
        _ = (ε / (n : ℝ)) * (U * U).trace := by rw [hu_diff]
    have htrU2_nn : 0 ≤ (U * U).trace := hU_sq_psd.trace_nonneg
    rw [div_le_div_iff₀ hgap_pos hε]
    -- Goal: (U * U).trace * ε ≤ ↑n * gap
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have h2 : (n : ℝ) * gap ≥ (n : ℝ) * ((ε / (n : ℝ)) * (U * U).trace) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hn_pos)
    have h3 : (n : ℝ) * ((ε / (n : ℝ)) * (U * U).trace) = ε * (U * U).trace := by
      field_simp
    linarith
  -- Step P: Total bound: ∑ cost ≤ tr(U) + tr(U²)/gap ≤ 3n/ε
  have h_total_le : U.trace + (U * U).trace / gap ≤ 3 * (n : ℝ) / ε := by
    have h3 : 2 * (n : ℝ) / ε + (n : ℝ) / ε = 3 * (n : ℝ) / ε := by ring
    linarith [htrU_bound, htrU2_over_gap]
  -- Step Q: 3n/ε < m*r (number of pairs is large)
  have h_mr_bound : 3 * (n : ℝ) / ε < (m : ℝ) * (r : ℝ) := by
    have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hr' : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_pos
    have hm_ge : 3 * (n : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hm_large
    have h_εr : (16 : ℝ) ≤ ε * (r : ℝ) := by
      rw [hr_def]
      calc (16 : ℝ) = ε * (16 / ε) := by field_simp
        _ ≤ ε * ↑(Nat.ceil (16 / ε)) := by
            gcongr; exact_mod_cast Nat.le_ceil (16 / ε)
    -- Multiply both sides by ε: need 3n < m*r*ε
    rw [div_lt_iff₀ hε]
    have hn_pos_nat : 4 ≤ n := hn
    have hn_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos_nat
    calc 3 * (n : ℝ) = 3 * (n : ℝ) * 1 := by ring
      _ < 3 * (n : ℝ) * (ε * (r : ℝ) / 4) := by
          gcongr
          linarith
      _ = (3 * (n : ℝ) / 4) * (ε * (r : ℝ)) := by ring
      _ ≤ (m : ℝ) * (ε * (r : ℝ)) := by nlinarith
      _ = (m : ℝ) * (r : ℝ) * ε := by ring
  -- Contradiction: m*r ≤ ∑ cost ≤ tr(U) + tr(U²)/gap ≤ 3n/ε < m*r
  linarith

/-- BSS induction step: extend coloring by one vertex using good_pair_exists. -/
lemma total_barrier_bound_step [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (hn : 4 ≤ Fintype.card V)
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf)
    (t : ℕ) (ht : t + 1 ≤ Fintype.card V / 4)
    (pc_t : PartialColoring V r) (hcard_t : pc_t.colored.card = t)
    (hpd_t : ((ε / 2 + (t : ℝ) * (ε / (Fintype.card V : ℝ))) • (1 : Matrix V V ℝ) -
      ∑ γ : Fin r,
        Lhalf_pinv * inducedLaplacian G
          (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
          Lhalf_pinv).PosDef)
    (hphi_t : barrierPotential (ε / 2 + (t : ℝ) * (ε / (Fintype.card V : ℝ)))
      (∑ γ : Fin r,
        Lhalf_pinv * inducedLaplacian G
          (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
          Lhalf_pinv) ≤ 2 * (Fintype.card V : ℝ) / ε) :
    ∃ pc : PartialColoring V r,
      pc.colored.card = t + 1 ∧
      ((ε / 2 + ((t : ℝ) + 1) * (ε / (Fintype.card V : ℝ))) • (1 : Matrix V V ℝ) -
        ∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv).PosDef ∧
      barrierPotential (ε / 2 + ((t : ℝ) + 1) * (ε / (Fintype.card V : ℝ)))
        (∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G
            (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv) ≤ 2 * (Fintype.card V : ℝ) / ε := by
  set n := Fintype.card V with hn_def
  set M_t := ∑ γ : Fin r, Lhalf_pinv *
    inducedLaplacian G (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
    Lhalf_pinv with hM_t_def
  set u_t := ε / 2 + (t : ℝ) * (ε / (n : ℝ)) with hu_t_def
  set u' := ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ)) with hu'_def
  have hr_pos : 0 < r := by rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hδ_pos : (0 : ℝ) < ε / (n : ℝ) := div_pos hε hn_pos
  have hu_lt_u' : u_t < u' := by rw [hu_t_def, hu'_def]; linarith
  -- (u'·I - M_t).PosDef by barrier_shift_posDef
  have hpd' : (u' • (1 : Matrix V V ℝ) - M_t).PosDef :=
    barrier_shift_posDef M_t u_t u' hu_lt_u' hpd_t
  -- U = (u'·I - M_t)⁻¹ is PD
  set U := (u' • (1 : Matrix V V ℝ) - M_t)⁻¹ with hU_def
  have hU_pd : U.PosDef := hpd'.inv
  -- Get good pair from good_pair_exists
  obtain ⟨v₀', hv₀', γ₀, htrBU_lt, hbarrier_cond⟩ :=
    good_pair_exists G ε hε r hr_def hn
      Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP3 hMP4
      pc_t t ht hcard_t hpd_t hphi_t
  set S_γ₀ := pc_t.colored.filter (fun v => pc_t.color v = γ₀) with hS_γ₀_def
  set ΔL := inducedLaplacian G (S_γ₀ ∪ {v₀'}) -
    inducedLaplacian G S_γ₀ with hΔL_def
  set B := Lhalf_pinv * ΔL * Lhalf_pinv with hB_def
  -- B is PSD (ΔL is PSD by inducedLaplacian_mono, conjugation preserves PSD)
  have hΔL_psd : ΔL.PosSemidef :=
    inducedLaplacian_mono G S_γ₀ (S_γ₀ ∪ {v₀'}) Finset.subset_union_left
  have hB_psd : B.PosSemidef := by
    rw [hB_def, show Lhalf_pinv * ΔL * Lhalf_pinv =
      Lhalf_pinvᴴ * ΔL * Lhalf_pinv from by rw [hpinv_herm.eq]]
    exact hΔL_psd.conjTranspose_mul_mul_same Lhalf_pinv
  -- PosDef: (u'·I - (M_t + B)).PosDef by inv_sub_posDef_of_trace_lt_one
  have hpd_new : (u' • (1 : Matrix V V ℝ) - (M_t + B)).PosDef := by
    have h_eq : u' • (1 : Matrix V V ℝ) - (M_t + B) = U⁻¹ - B := by
      rw [hU_def, Matrix.nonsing_inv_nonsing_inv]
      · simp [sub_sub]
      · exact (Matrix.isUnit_iff_isUnit_det _).mp hpd'.isUnit
    rw [h_eq]
    exact inv_sub_posDef_of_trace_lt_one U B hU_pd hB_psd htrBU_lt
  -- Potential: Φ_{u'}(M_t + B) ≤ Φ_{u_t}(M_t) ≤ 2n/ε by one_sided_barrier
  have hphi_new : barrierPotential u' (M_t + B) ≤ 2 * (n : ℝ) / ε := by
    calc barrierPotential u' (M_t + B)
        ≤ barrierPotential u_t M_t :=
          one_sided_barrier M_t B u_t u' hu_lt_u' hpd_t hB_psd hbarrier_cond
      _ ≤ 2 * (n : ℝ) / ε := hphi_t
  -- === Construct the new partial coloring ===
  set color' : V → Fin r := fun v =>
    if v = v₀' then γ₀ else pc_t.color v with hcolor'_def
  set colored' := pc_t.colored ∪ {v₀'} with hcolored'_def
  refine ⟨⟨colored', color'⟩, ?_, ?_⟩
  · -- Card: |colored'| = t + 1
    rw [hcolored'_def, Finset.card_union_of_disjoint
      (Finset.disjoint_singleton_right.mpr hv₀')]
    simp [hcard_t]
  · -- PosDef + Potential: show the new sum = M_t + B, then apply hpd_new/hphi_new
    -- Helper: color' agrees with pc_t.color on old vertices
    have hcolor'_old : ∀ w ∈ pc_t.colored, color' w = pc_t.color w := by
      intro w hw
      simp [hcolor'_def, show w ≠ v₀' from fun h => hv₀' (h ▸ hw)]
    have hcolor'_v₀ : color' v₀' = γ₀ := by simp [hcolor'_def]
    -- Filter for γ₀: (old filter for γ₀) ∪ {v₀'}
    have h_filter_γ₀ : colored'.filter (fun v => color' v = γ₀) =
        S_γ₀ ∪ {v₀'} := by
      ext w; simp only [Finset.mem_filter, Finset.mem_union,
        Finset.mem_singleton, hcolored'_def, hS_γ₀_def]
      constructor
      · intro ⟨hw_mem, hw_col⟩
        rcases hw_mem with hw_old | hw_new
        · left; exact ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
        · right; exact hw_new
      · intro hw
        rcases hw with ⟨hw_old, hw_col⟩ | hw_eq
        · exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
        · exact ⟨Or.inr hw_eq, show color' w = γ₀ from hw_eq ▸ hcolor'_v₀⟩
    -- Filter for γ ≠ γ₀: unchanged
    have h_filter_other : ∀ γ : Fin r, γ ≠ γ₀ →
        colored'.filter (fun v => color' v = γ) =
        pc_t.colored.filter (fun v => pc_t.color v = γ) := by
      intro γ hγ; ext w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
        hcolored'_def]
      constructor
      · intro ⟨hw_mem, hw_col⟩
        rcases hw_mem with hw_old | hw_new
        · exact ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
        · exfalso; rw [hw_new, hcolor'_v₀] at hw_col; exact hγ hw_col.symm
      · intro ⟨hw_old, hw_col⟩
        exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
    -- Key sum identity: new sum = M_t + B
    have h_sum_eq : ∑ γ : Fin r, Lhalf_pinv *
        inducedLaplacian G (colored'.filter (fun v => color' v = γ)) *
        Lhalf_pinv = M_t + B := by
      -- Rewrite each summand using filter equalities
      have h_congr : ∀ γ ∈ Finset.univ, Lhalf_pinv *
          inducedLaplacian G (colored'.filter (fun v => color' v = γ)) *
          Lhalf_pinv =
        Lhalf_pinv * inducedLaplacian G
          (if γ = γ₀ then S_γ₀ ∪ {v₀'}
           else pc_t.colored.filter (fun v => pc_t.color v = γ)) *
          Lhalf_pinv := by
        intro γ _
        split_ifs with h
        · rw [h, h_filter_γ₀]
        · rw [h_filter_other γ h]
      rw [Finset.sum_congr rfl h_congr]
      -- Split sum into γ₀ and rest
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ₀)]
      -- For γ ≠ γ₀ in the erase set, the if is false
      have h_rest : ∀ γ ∈ Finset.univ.erase γ₀,
          Lhalf_pinv * inducedLaplacian G
            (if γ = γ₀ then S_γ₀ ∪ {v₀'}
             else pc_t.colored.filter (fun v => pc_t.color v = γ)) *
            Lhalf_pinv =
          Lhalf_pinv * inducedLaplacian G
            (pc_t.colored.filter (fun v => pc_t.color v = γ)) *
            Lhalf_pinv := by
        intro γ hγ
        rw [if_neg (Finset.ne_of_mem_erase hγ)]
      rw [Finset.sum_congr rfl h_rest]
      -- Now LHS = L_new_γ₀ + ∑_{γ≠γ₀} old = M_t + B
      -- Reduce the if True
      simp only [if_true]
      rw [hB_def, hΔL_def, hM_t_def,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ γ₀)]
      -- Goal: L_new + rest = (L_old + rest) + Lp * ΔL * Lp
      have h_new_split : Lhalf_pinv * inducedLaplacian G (S_γ₀ ∪ {v₀'}) * Lhalf_pinv =
          Lhalf_pinv * inducedLaplacian G S_γ₀ * Lhalf_pinv +
          Lhalf_pinv *
            (inducedLaplacian G (S_γ₀ ∪ {v₀'}) -
             inducedLaplacian G S_γ₀) *
            Lhalf_pinv := by
        simp [Matrix.mul_sub, Matrix.sub_mul]
      rw [h_new_split]; abel
    dsimp only
    rw [h_sum_eq]
    exact ⟨hpd_new, hphi_new⟩

/-- **Total barrier bound (Steps 3-4 of informal proof, core BSS)**: Given the spectral
    setup, there exists a partial coloring of k = n/4 vertices with r = ⌈16/ε⌉ colors
    such that the TOTAL monochromatic normalized sum ∑_γ M_γ ≤ u_k · I.
    The per-color bounds then follow from `psd_sub_sum_le` (extraction lemma).
    The proof constructs the coloring step by step using `one_sided_barrier`:
    1. Track M_t = ∑_γ M_t^γ (total monochromatic matrix, eq. 38)
    2. At step t, for each (v,γ) ∈ R × [r], the increment B_v^γ increases M_t^γ
    3. Averaging: ∑_{v,γ} B_v^γ ≤ P ≤ I (sum of cross-edge contributions)
    4. By `trace_mul_le_of_loewner` + `barrier_potential_decrease` + averaging:
       average barrier cost < 1, so some (v,γ) satisfies the barrier condition (eq. 35)
    5. Apply `one_sided_barrier` to propagate M_t ≺ u_t·I → M_{t+1} ≺ u_{t+1}·I
    6. After k steps: (u_k·I - M_k).PosDef implies (u_k·I - ∑_γ M_k^γ).PosSemidef -/
lemma total_barrier_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (_hMP1 : Lhalf * Lhalf_pinv * Lhalf = Lhalf)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    let r := Nat.ceil (16 / ε)
    let k := Fintype.card V / 4
    let n := Fintype.card V
    let u_k := ε / 2 + (k : ℝ) * (ε / (n : ℝ))
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      (u_k • (1 : Matrix V V ℝ) -
        ∑ γ : Fin r,
          Lhalf_pinv * inducedLaplacian G (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv).PosSemidef := by
  set r := Nat.ceil (16 / ε) with hr_def
  set k := Fintype.card V / 4 with hk_def
  set n := Fintype.card V with hn_def
  have hr_pos : 0 < r := Nat.ceil_pos.mpr (by positivity)
  have hu_pos : 0 < ε / 2 + (k : ℝ) * (ε / (n : ℝ)) := by positivity
  -- Helper: inducedLaplacian of a set with ≤ 1 element is zero
  have h_lap_le1 : ∀ T : Finset V, T.card ≤ 1 → inducedLaplacian G T = 0 := by
    intro T hT; ext i j
    simp only [inducedLaplacian, Matrix.of_apply, Matrix.zero_apply]
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte, Nat.cast_eq_zero]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _ ⟨hiT, hmT, hadj⟩
      have him : i = m := (Finset.card_le_one.mp hT) i hiT m hmT
      subst him; exact absurd hadj (G.loopless.irrefl i)
    · simp only [hij, ↓reduceIte]
      rw [if_neg]; push Not
      intro _ hiT hjT; exact hij ((Finset.card_le_one.mp hT) i hiT j hjT)
  -- Step 1: Get a subset S ⊆ V with |S| = k
  have hk_le_n : k ≤ Fintype.card V := Nat.div_le_self _ 4
  obtain ⟨S, _, hS_card⟩ := Finset.exists_subset_card_eq (α := V)
    (show k ≤ Finset.univ.card from by rw [Finset.card_univ]; exact hk_le_n)
  -- Step 2: Construct coloring with injective color assignment (k ≤ r case)
  by_cases hkr : k ≤ r
  · -- === Case k ≤ r: injective coloring, M_total = 0 ===
    have hemb : Nonempty (↥S ↪ Fin r) := by
      rw [Function.Embedding.nonempty_iff_card_le]
      simp [Fintype.card_coe, hS_card, Fintype.card_fin, hkr]
    obtain ⟨emb⟩ := hemb
    refine ⟨⟨S, fun v =>
      if h : v ∈ S then emb ⟨v, h⟩
      else ⟨0, hr_pos⟩⟩, hS_card, ?_⟩
    suffices h_sum_zero : ∑ γ : Fin r,
        Lhalf_pinv * inducedLaplacian G
          (S.filter (fun v => (if h : v ∈ S then emb ⟨v, h⟩ else ⟨0, hr_pos⟩) = γ)) *
          Lhalf_pinv = 0 by
      rw [h_sum_zero, sub_zero]
      exact Matrix.PosSemidef.one.smul (le_of_lt hu_pos)
    apply Finset.sum_eq_zero; intro γ _
    have h_class_le1 :
        (S.filter (fun v =>
          (if h : v ∈ S then emb ⟨v, h⟩
           else ⟨0, hr_pos⟩) = γ)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      have ha_eq := ha.2; rw [dif_pos ha.1] at ha_eq
      have hb_eq := hb.2; rw [dif_pos hb.1] at hb_eq
      exact congrArg Subtype.val (emb.injective (ha_eq.trans hb_eq.symm))
    rw [h_lap_le1 _ h_class_le1, Matrix.mul_zero, Matrix.zero_mul]
  · -- === Case k > r: BSS dynamic barrier construction ===
    push Not at hkr
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    suffices h_ind : ∀ t, t ≤ k →
        ∃ pc : PartialColoring V r,
          pc.colored.card = t ∧
          ((ε / 2 + (t : ℝ) * (ε / (n : ℝ))) • (1 : Matrix V V ℝ) -
            ∑ γ : Fin r,
              Lhalf_pinv * inducedLaplacian G
                (pc.colored.filter (fun v => pc.color v = γ)) *
                Lhalf_pinv).PosDef ∧
          barrierPotential (ε / 2 + (t : ℝ) * (ε / (n : ℝ)))
            (∑ γ : Fin r,
              Lhalf_pinv * inducedLaplacian G
                (pc.colored.filter (fun v => pc.color v = γ)) *
                Lhalf_pinv) ≤ 2 * (n : ℝ) / ε by
      obtain ⟨pc, hcard, hpd, _⟩ := h_ind k le_rfl
      exact ⟨pc, hcard, hpd.posSemidef⟩
    intro t
    induction t with
    | zero =>
      intro _
      simp only [Nat.cast_zero, hn_def]
      exact total_barrier_bound_base G ε hε r hr_pos Lhalf_pinv h_lap_le1
    | succ t ih =>
      intro ht
      obtain ⟨pc_t, hcard_t, hpd_t, hphi_t⟩ := ih (by omega)
      simp only [Nat.cast_succ, hn_def] at hpd_t hphi_t ht hn ⊢
      exact total_barrier_bound_step G ε hε r hr_def hn
        Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP3 hMP4
        t ht pc_t hcard_t hpd_t hphi_t

/-- **Dynamic barrier coloring (Steps 3-4 of informal proof)**: Given the spectral setup
    (Lhalf, Lhalf_pinv satisfying Moore-Penrose conditions), there exists a partial coloring
    of k = n/4 vertices with r = ⌈16/ε⌉ colors such that each color class γ has its
    normalized monochromatic matrix bounded: Lhalf_pinv * L_{S_γ} * Lhalf_pinv ≼ u_k · I.
    Proof: Apply `total_barrier_bound` for the total sum bound ∑_γ M_γ ≤ u_k·I,
    then `psd_sub_sum_le` to extract per-color bounds (since each M_γ is PSD). -/
lemma dynamic_barrier_coloring
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hpinv_herm : Lhalf_pinv.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP1 : Lhalf * Lhalf_pinv * Lhalf = Lhalf)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    let r := Nat.ceil (16 / ε)
    let k := Fintype.card V / 4
    let n := Fintype.card V
    let u_k := ε / 2 + (k : ℝ) * (ε / (n : ℝ))
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      ∀ γ : Fin r,
        (u_k • (1 : Matrix V V ℝ) -
          Lhalf_pinv * inducedLaplacian G (pc.colored.filter (fun v => pc.color v = γ)) *
            Lhalf_pinv).PosSemidef := by
  -- Step 1: Get total barrier bound from BSS construction
  obtain ⟨pc, hcard, h_total⟩ := total_barrier_bound G ε hε hε1 hn
    Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP1 hMP3 hMP4
  -- Step 2: Extract per-color bounds using psd_sub_sum_le
  exact ⟨pc, hcard, psd_sub_sum_le
    (fun γ => Lhalf_pinv * inducedLaplacian G (pc.colored.filter (fun v => pc.color v = γ)) *
      Lhalf_pinv)
    _
    (fun γ => normalized_mono_psd G Lhalf_pinv hpinv_herm _)
    h_total⟩

/-- **Dynamic BSS coloring result (Steps 1–5 of informal proof)**: Given the spectral
    setup (Lhalf with Lhalf² = L), there exists a partial coloring of k = n/4 vertices
    with r = ⌈16/ε⌉ colors such that each color class is ε-light.
    Proof: Obtain Lhalf_pinv from `hermitian_pseudo_inverse_exists`, apply
    `dynamic_barrier_coloring` for the barrier bound, then use `pinv_pullback_eq`
    and `eps_light_of_loewner_bound` to convert the barrier bound to ε-lightness. -/
lemma bss_dynamic_coloring
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G) :
    let r := Nat.ceil (16 / ε)
    let k := Fintype.card V / 4
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      ∀ γ : Fin r, IsEpsLight G ε (pc.colored.filter (fun v => pc.color v = γ)) := by
  -- Step 1: Get the Moore-Penrose pseudo-inverse of Lhalf
  obtain ⟨Lhalf_pinv, hpinv_herm, hMP1, _, hMP3, hMP4⟩ :=
    hermitian_pseudo_inverse_exists Lhalf hLhalf_herm
  -- Step 2: Get the coloring with per-color barrier bounds
  obtain ⟨pc, hcard, hbarrier⟩ := dynamic_barrier_coloring G ε hε hε1 hn
    Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP1 hMP3 hMP4
  -- Step 3: u_k ≤ ε (by barrier_parameter_bound)
  have ⟨hu_le, _⟩ := barrier_parameter_bound ε hε (Fintype.card V) hn
  have hu_k_le_eps : ε / 2 + ↑(Fintype.card V / 4) * (ε / ↑(Fintype.card V)) ≤ ε := by
    linarith
  -- Step 4: For each color γ, convert barrier bound to ε-lightness
  refine ⟨pc, hcard, fun γ => ?_⟩
  set S_γ := pc.colored.filter (fun v => pc.color v = γ) with hSγ_def
  set M_γ := Lhalf_pinv * inducedLaplacian G S_γ * Lhalf_pinv with hMγ_def
  -- 4a: Lhalf * M_γ * Lhalf = inducedLaplacian G S_γ (by pinv_pullback_eq)
  have hpullback : Lhalf * M_γ * Lhalf = inducedLaplacian G S_γ :=
    pinv_pullback_eq G S_γ Lhalf Lhalf_pinv hLhalf_herm hpinv_herm hLhalf_sq hMP1 hMP3 hMP4
  -- 4b: M_γ ≼ u_k · I (from the barrier coloring)
  have hM_bound := hbarrier γ
  -- 4c: Apply eps_light_of_loewner_bound
  exact eps_light_of_loewner_bound G ε
    (ε / 2 + ↑(Fintype.card V / 4) * (ε / ↑(Fintype.card V)))
    hε hu_k_le_eps S_γ Lhalf hLhalf_herm hLhalf_sq M_γ hM_bound hpullback

/-- The BSS coloring result (correctly stated, dynamic approach).
    There exists a partial coloring of n/4 vertices with r = ⌈16/ε⌉ colors such that
    each color class is ε-light.
    This captures Steps 1–5 of the informal proof:
    1. `spectral_sqrt_exists`: Construct Lhalf with Lhalf² = L (spectral setup)
    2. `bss_dynamic_coloring`: Dynamic coloring with per-edge tracking -/
lemma bss_coloring_eps_light
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V) :
    let r := Nat.ceil (16 / ε)
    let k := Fintype.card V / 4
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      ∀ γ : Fin r, IsEpsLight G ε (pc.colored.filter (fun v => pc.color v = γ)) := by
  -- Step 1: Spectral setup — construct Lhalf with Lhalf² = L
  obtain ⟨Lhalf, hLhalf_herm, hLhalf_sq⟩ := spectral_sqrt_exists G
  -- Step 2: Dynamic BSS coloring — color k vertices with per-edge tracking
  exact bss_dynamic_coloring G ε hε hε1 hn Lhalf hLhalf_herm hLhalf_sq

/-! ### The coloring induction result -/

/-- The result of the BSS coloring induction: there exists a partial coloring of k vertices
    with r colors such that each color class is ε-light. This packages Steps 1-5 of the
    informal proof, delegating to `bss_coloring_eps_light` which uses:
    1. `spectral_sqrt_exists`: Lhalf with Lhalf² = L
    2. `bss_dynamic_coloring`: Dynamic per-edge coloring with BSS barrier -/
lemma coloring_induction_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V) :
    let n := Fintype.card V
    let r := Nat.ceil (16 / ε)
    let k := n / 4
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      ∀ γ : Fin r, IsEpsLight G ε (pc.colored.filter (fun v => pc.color v = γ)) := by
  exact bss_coloring_eps_light G ε hε hε1 hn

/-! ### Proof of the main theorem -/

/-- For n ≥ 4, the coloring process produces an ε-light set of size ≥ εn/256. -/
lemma eps_light_large_n
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 4 ≤ Fintype.card V) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by
  set n := Fintype.card V with hn_def
  set r := Nat.ceil (16 / ε) with hr_def
  set k := n / 4 with hk_def
  -- Step 1: Get the coloring from the induction
  obtain ⟨pc, hpc_card, hpc_light⟩ := coloring_induction_exists G ε hε hε1 hn
  -- Step 2: r > 0
  have hr_pos : 0 < r := by
    rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
  -- Step 3: By pigeonhole, some color class has size ≥ k/r
  obtain ⟨γ, hγ⟩ := largest_color_class_bound pc hr_pos
  set S := pc.colored.filter (fun v => pc.color v = γ) with hS_def
  -- Step 4: S is ε-light (from the coloring induction)
  have hS_light : IsEpsLight G ε S := hpc_light γ
  -- Step 5: |S| ≥ εn/256
  refine ⟨S, hS_light, ?_⟩
  -- From pigeonhole: |S| * r ≥ k = |pc.colored|, and we need ε/256 * n ≤ |S|
  rw [hpc_card] at hγ
  -- Key: n ≤ 8k (integer division: k = n/4,
  -- so 4k ≥ n-3, 8k ≥ 2n-6 ≥ n for n ≥ 6; check n=4,5)
  have h8k : n ≤ 8 * k := by omega
  -- εr ≤ 32 (r = ⌈16/ε⌉ ≤ 16/ε + 1 and ε ≤ 1,
  -- hence εr ≤ 16 + ε ≤ 17 ≤ 32)
  have h_εr_upper : ε * (r : ℝ) ≤ 32 := by
    rw [hr_def]
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have h16ε_nn : (0 : ℝ) ≤ 16 / ε := by positivity
    calc ε * ↑(Nat.ceil (16 / ε)) ≤ ε * (16 / ε + 1) := by
          gcongr; exact le_of_lt (Nat.ceil_lt_add_one h16ε_nn)
      _ = 16 + ε := by field_simp
      _ ≤ 16 + 1 := by linarith
      _ ≤ 32 := by norm_num
  -- Cast to ℝ
  have hSr : (k : ℝ) ≤ (S.card : ℝ) * (r : ℝ) := by exact_mod_cast hγ
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
  have h8k' : (n : ℝ) ≤ 8 * (k : ℝ) := by exact_mod_cast h8k
  -- Chain: ε/256 * n ≤ ε * (8k) / 256 = εk/32
  -- and 256 * |S| * r ≥ 256 * k, so |S| ≥ k/r ≥ εk/(εr) = k/r
  -- We need: ε * n * r ≤ 256 * k (then ε * n ≤ 256k/r ≤ 256|S|)
  -- ε * n * r ≤ ε * 8k * r = 8 * (εr) * k ≤ 8 * 32 * k = 256k ✓
  -- So: ε/256 * n = ε*n/256 ≤ (256k)/(256r) = k/r ≤ |S|
  -- Let's just provide the key multiplication and use nlinarith
  -- Key fact: 256 * |S| * r ≥ 256 * k ≥ 32 * n ≥ ε * n * r
  -- (using 256k ≥ 256 * n/8 = 32n and εr ≤ 32)
  -- Hence 256 * |S| ≥ ε * n (dividing by r > 0)
  -- Equivalently: ε / 256 * n ≤ |S|
  suffices h : ε * ↑n ≤ 256 * ↑S.card by
    linarith [show ε / 256 * ↑n = ε * ↑n / 256
      by ring]
  -- Proof: ε * n * r ≤ 256 * k ≤ 256 * |S| * r, divide by r
  have hkey : ε * ↑n * ↑r ≤ 256 * ↑S.card * ↑r := by nlinarith [mul_pos hε hr']
  exact le_of_mul_le_mul_right hkey hr'

/-- For 1 ≤ n ≤ 3, a single vertex is ε-light and satisfies the size bound. -/
lemma eps_light_small_n
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : Fintype.card V < 4)
    (hne : 0 < Fintype.card V) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤
      (S.card : ℝ) := by
  -- Take any single vertex v. Then L_{S} = 0 (no edges in a singleton),
  -- so εL - L_S = εL ≽ 0. Also |S| = 1 ≥ ε·n/256 since n ≤ 3 and ε ≤ 1.
  have ⟨v⟩ := Fintype.card_pos_iff.mp hne
  refine ⟨{v}, ?_, ?_⟩
  · -- {v} is ε-light: L_{S} = 0 for singleton, so εL - 0 = εL ≽ 0
    -- since L is PSD and ε > 0.
    have hLS : inducedLaplacian G {v} = 0 := by
      ext i j
      simp only [inducedLaplacian, Matrix.of_apply, Matrix.zero_apply]
      split_ifs with hij h
      · -- diagonal: need filter card = 0 since no edges within singleton
        rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _ ⟨hiv, hkv, hadj⟩
        have hi := Finset.mem_singleton.mp hiv
        have hk := Finset.mem_singleton.mp hkv
        rw [hi, hk] at hadj
        exact absurd hadj (G.loopless.irrefl _)
      · -- off-diagonal with adj and both in {v}: contradicts i ≠ j
        exfalso
        have hi := Finset.mem_singleton.mp h.2.1
        have hj := Finset.mem_singleton.mp h.2.2
        exact hij (hi.trans hj.symm)
      · rfl
    unfold IsEpsLight
    rw [hLS, sub_zero]
    exact (graphLaplacian_posSemidef G).smul hε.le
  · -- Size bound: 1 ≥ ε/256 * n when n ≤ 3 and ε ≤ 1
    simp only [Finset.card_singleton]
    have hn' : (Fintype.card V : ℝ) < 4 := Nat.cast_lt.mpr hn
    nlinarith

/-! ### Main theorem -/

/-- **Main Theorem (Problem 6)**: For every simple graph G on a finite vertex set V
    and every ε ∈ (0, 1], there exists an ε-light subset S with |S| ≥ ε/256 · |V|. -/
theorem exists_eps_light_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∃ S : Finset V, IsEpsLight G ε S ∧
      ε / 256 * (Fintype.card V : ℝ) ≤
      (S.card : ℝ) := by
  by_cases hn0 : Fintype.card V = 0
  · -- n = 0: the empty set works
    refine ⟨∅, ?_, by simp [hn0]⟩
    -- n = 0 means V is empty, so all matrices are trivially PSD
    unfold IsEpsLight
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    have h : ε • graphLaplacian G - inducedLaplacian G ∅ = 0 := by
      ext i _; exact isEmptyElim i
    rw [h]; exact Matrix.PosSemidef.zero
  · push Not at hn0
    have hne : 0 < Fintype.card V := Nat.pos_of_ne_zero hn0
    by_cases hn4 : 4 ≤ Fintype.card V
    · exact eps_light_large_n G ε hε_pos hε_le hn4
    · push Not at hn4
      exact eps_light_small_n G ε hε_pos hε_le hn4 hne
end Problem6

end
