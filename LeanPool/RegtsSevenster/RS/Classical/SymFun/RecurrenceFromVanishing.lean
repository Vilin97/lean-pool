/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums

/-!
# Recurrence from Schur-determinant vanishing

Given a power-sum sequence `t` whose determinant Schur specialisation
vanishes on sufficiently wide single-row extensions, the
complete-homogeneous sequence `newtonHZ t` satisfies a nontrivial
linear recurrence.  This is the algebraic core of the argument that
hook confinement forces a nilpotent trace.

The proof proceeds in three stages:

1. **Determinant vanishing** — the vanishing hypothesis `hvan` yields
   `det = 0` for every matrix of the form
   `(fun i j : Fin (a+1) => newtonHZ t (ρ i + 1 + j))` whenever the
   row-shifts `ρ` take integer values `≥ b − a`. Negative degrees
   evaluate to zero.

2. **Finite rank** — the span of the vectors
   `v ρ := (fun k => newtonHZ t (ρ + 1 + k))` for `ρ ≥ b − a` has
   `finrank ≤ a` (a proper subspace of `Fin (a+1) → ℂ`).

3. **Annihilator extraction** — a nonzero linear functional vanishing
   on that span is converted to the coefficient vector `c` of the
   recurrence.
-/

@[expose] public section

namespace RS

open Finset Matrix Submodule Module

/-! ### Stage 1: determinant vanishing from Schur vanishing -/

/-- For all `d`, adding `d` to the index of a `StrictAnti` function
on `Fin n` drops the value by at least `d`. -/
private lemma strictAnti_drop {n : ℕ} {ρ : Fin n → ℤ}
    (hρ : StrictAnti ρ) :
    ∀ d m (hm : m < n) (hmd : m + d < n),
    ρ ⟨m + d, hmd⟩ + (d : ℤ) ≤ ρ ⟨m, hm⟩ := by
  intro d; induction d with
  | zero => intros; simp
  | succ d ih =>
    intro m hm hmd
    have hmd' : m + d < n := by omega
    have h_ih := ih m hm hmd'
    have h_step := hρ
      (show (⟨m + d, hmd'⟩ : Fin n) < ⟨m + d + 1, hmd⟩ by
        exact Fin.mk_lt_mk.mpr (by omega))
    change ρ ⟨m + d + 1, hmd⟩ + ((d + 1 : ℕ) : ℤ) ≤ ρ ⟨m, hm⟩
    omega

/-- For a `StrictAnti` function `ρ` on `Fin n` valued in `ℤ`, the sum
`ρ j + j` is antitone: the strict decrease of `ρ` dominates the
increase of the index. -/
private lemma antitone_strictAnti_add_val {n : ℕ} {ρ : Fin n → ℤ}
    (hρ : StrictAnti ρ) : Antitone (fun j : Fin n => ρ j + (j : ℤ)) := by
  intro i j hij
  change ρ j + (j.val : ℤ) ≤ ρ i + (i.val : ℤ)
  have him : i.val ≤ j.val := hij
  have hmd_lt : i.val + (j.val - i.val) < n := by omega
  have key := strictAnti_drop hρ (j.val - i.val) i.val i.isLt hmd_lt
  have h_fin_eq : (⟨i.val + (j.val - i.val), hmd_lt⟩ : Fin n) = j := by
    ext; change i.val + (j.val - i.val) = j.val; omega
  suffices h : ρ j + ((j.val - i.val : ℕ) : ℤ) ≤ ρ i by omega
  calc ρ j + ((j.val - i.val : ℕ) : ℤ)
      = ρ ⟨i.val + (j.val - i.val), hmd_lt⟩ +
          ((j.val - i.val : ℕ) : ℤ) := by
          rw [congr_arg ρ h_fin_eq]
    _ ≤ ρ ⟨i.val, i.isLt⟩ := key
    _ = ρ i := rfl

/-- The determinant `det (fun i j => newtonHZ t (ρ i + 1 + j))` vanishes
whenever `ρ : Fin (a+1) → ℤ` is `StrictAnti` with
`ρ ⟨a, _⟩ ≥ b − a` and the Schur-determinant vanishing hypothesis
holds. -/
private lemma det_vanishing_of_strictAnti {t : ℕ → ℂ} {a b : ℕ}
    (hvan : ∀ w : List ℕ, w.SortedGE → (∀ x ∈ w, 0 < x) →
      w.length = a + 1 → b + 1 ≤ w.getD a 0 → schurDet t w = 0)
    {ρ : Fin (a + 1) → ℤ} (hρ : StrictAnti ρ)
    (hρ_lb : (b : ℤ) - a ≤ ρ (Fin.last a)) :
    det (Matrix.of fun i j : Fin (a + 1) =>
      newtonHZ t (ρ i + 1 + (j : ℤ))) = 0 := by
  -- ═══════ Construct the list w ═══════
  set f : Fin (a + 1) → ℕ := fun j => (ρ j + (j : ℤ) + 1).toNat with hf_def
  set w := List.ofFn f with hw_def
  have hw_len : w.length = a + 1 := List.length_ofFn
  have hrow (i : Fin (a + 1)) :
      (b : ℤ) + 1 ≤ ρ i + (i : ℤ) + 1 := by
    have hdrop := antitone_strictAnti_add_val hρ (Fin.le_last i)
    change ρ (Fin.last a) + (a : ℤ) ≤ ρ i + (i : ℤ) at hdrop
    omega
  have hf_cast (i : Fin (a + 1)) :
      (f i : ℤ) = ρ i + (i : ℤ) + 1 := by
    exact Int.toNat_of_nonneg (by have := hrow i; omega)
  -- ═══════ Verify the hypotheses of hvan ═══════
  have hw_sorted : w.SortedGE := by
    rw [hw_def, List.sortedGE_ofFn_iff]
    intro i j hij
    apply Int.toNat_le_toNat
    have hdrop := antitone_strictAnti_add_val hρ hij
    change ρ j + (j : ℤ) ≤ ρ i + (i : ℤ) at hdrop
    omega
  have hw_pos : ∀ x ∈ w, 0 < x := by
    intro x hx
    rw [hw_def, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hrow i
    have := hf_cast i
    omega
  have hw_last : b + 1 ≤ w.getD a 0 := by
    change b + 1 ≤ (List.ofFn f).getD a 0
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega),
      List.getElem_ofFn]
    have := hrow (Fin.last a)
    have := hf_cast (Fin.last a)
    simpa only [Fin.last] using (show b + 1 ≤ f (Fin.last a) by omega)
  -- ═══════ Apply the vanishing hypothesis ═══════
  have hschur := hvan w hw_sorted hw_pos hw_len hw_last
  -- ═══════ Relate schurDet to the target determinant ═══════
  rw [schurDet] at hschur
  set target := Matrix.of fun i j : Fin (a + 1) =>
    newtonHZ t (ρ i + 1 + (j : ℤ))
  set e := finCongr hw_len
  suffices h_eq : (Matrix.of fun i j : Fin w.length =>
      newtonHZ t ((w.get i : ℤ) + (j : ℤ) - (i : ℤ))) =
    target.submatrix e e by
    rw [h_eq, det_submatrix_equiv_self] at hschur; exact hschur
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.of_apply, Matrix.submatrix_apply, target, e,
    finCongr_apply, Fin.cast_mk]
  have hw_get : (w.get ⟨i, hi⟩ : ℕ) = f ⟨i, by omega⟩ :=
    List.getElem_ofFn hi
  have h_cast : (↑(w.get ⟨i, hi⟩) + (j : ℤ) - (i : ℤ)) =
      ρ ⟨i, by omega⟩ + 1 + (j : ℤ) := by
    rw [hw_get, hf_cast]
    change ρ ⟨i, _⟩ + (i : ℤ) + 1 + (j : ℤ) - (i : ℤ) =
      ρ ⟨i, _⟩ + 1 + (j : ℤ)
    ring
  rw [h_cast]

/-! ### Stage 2: linear dependence and finite-rank bound -/

/-- For any function `g : Fin (a+1) → ℤ` with values `≥ b − a`, the
matrix `(fun i j => newtonHZ t (g i + 1 + j))` has determinant zero. -/
private lemma det_vanishing_of_all_ge {t : ℕ → ℂ} {a b : ℕ}
    (hvan : ∀ w : List ℕ, w.SortedGE → (∀ x ∈ w, 0 < x) →
      w.length = a + 1 → b + 1 ≤ w.getD a 0 → schurDet t w = 0)
    (g : Fin (a + 1) → ℤ) (hg : ∀ i, (b : ℤ) - a ≤ g i) :
    det (Matrix.of fun i j : Fin (a + 1) =>
      newtonHZ t (g i + 1 + (j : ℤ))) = 0 := by
  by_cases hInj : Function.Injective g
  · -- ═══════ Injective case: sort g and apply Stage 1 ═══════
    set S := Finset.image g Finset.univ
    have hS_card : S.card = a + 1 :=
      (Finset.card_image_of_injective _ hInj).trans (Finset.card_fin _)
    set e := S.orderIsoOfFin hS_card
    set ρ : Fin (a + 1) → ℤ := fun i => (e (Fin.rev i)).1
    have hρ_anti : StrictAnti ρ := fun i j hij =>
      Subtype.coe_lt_coe.mpr (e.strictMono (Fin.rev_lt_rev.mpr hij))
    have hρ_lb : (b : ℤ) - a ≤ ρ (Fin.last a) := by
      change (b : ℤ) - a ≤ (e (Fin.rev (Fin.last a))).1
      have hrev : Fin.rev ((Fin.last a) : Fin (a + 1)) =
          ⟨0, by omega⟩ := Fin.ext (by simp [Fin.rev])
      rw [hrev]
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (e ⟨0, by omega⟩).2
      rw [← hk]; exact hg k
    have h_det_zero := det_vanishing_of_strictAnti hvan hρ_anti hρ_lb
    -- Build a permutation σ where g (σ_fun i) = ρ i
    have hρ_range : ∀ i, ∃ k, g k = ρ i := by
      intro i
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (e (Fin.rev i)).2
      exact ⟨k, hk⟩
    choose σ_fun hσ using hρ_range
    have hσ_inj : Function.Injective σ_fun := fun i j hij =>
      hρ_anti.injective (by rw [← hσ i, ← hσ j, hij])
    set σ : Equiv.Perm (Fin (a + 1)) :=
      Equiv.ofBijective σ_fun
        ⟨hσ_inj, (Finite.injective_iff_surjective.mp hσ_inj)⟩
    have h_eq : (Matrix.of fun i j : Fin (a + 1) =>
        newtonHZ t (ρ i + 1 + (j : ℤ))) =
      (Matrix.of fun i j : Fin (a + 1) =>
        newtonHZ t (g i + 1 + (j : ℤ))).submatrix σ id := by
      ext i j; simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
      change newtonHZ t (ρ i + 1 + (j : ℤ)) =
        newtonHZ t (g (σ_fun i) + 1 + (j : ℤ))
      rw [hσ]
    rw [h_eq, det_permute, mul_eq_zero,
      or_iff_right (by simp [Units.ne_zero])] at h_det_zero
    exact h_det_zero
  · -- ═══════ Non-injective case: repeated rows ═══════
    simp only [Function.Injective] at hInj
    push Not at hInj
    obtain ⟨i, j, hgij, hne⟩ := hInj
    exact det_zero_of_row_eq hne (by ext k; simp [Matrix.of_apply, hgij])

/-! ### Stage 3: extracting the recurrence -/

-- One elaboration of the span/annihilator assembly
-- over `Fin (a+1) → ℂ` with its instance searches, no proof search.
/-- Schur-determinant vanishing on wide single-row extensions forces
the complete-homogeneous sequence to satisfy a nontrivial linear
recurrence. -/
theorem exists_recurrence_of_schurDet_vanishing {t : ℕ → ℂ} {a b : ℕ}
    (hvan : ∀ w : List ℕ, w.SortedGE → (∀ x ∈ w, 0 < x) →
      w.length = a + 1 → b + 1 ≤ w.getD a 0 → schurDet t w = 0) :
    ∃ c : Fin (a + 1) → ℂ, c ≠ 0 ∧
      ∀ ρ : ℤ, (b : ℤ) - a ≤ ρ →
        ∑ k : Fin (a + 1), c k * newtonHZ t (ρ + 1 + (k : ℤ)) = 0 := by
  -- ═══════ STAGE 2: finite-rank bound ═══════
  set v : ℤ → (Fin (a + 1) → ℂ) :=
    fun ρ k => newtonHZ t (ρ + 1 + (k : ℤ)) with hv_def
  set W := span ℂ (v '' {ρ | (b : ℤ) - a ≤ ρ})
  have h_finrank : finrank ℂ W ≤ a := by
    by_contra h_gt
    push Not at h_gt
    have h_le : finrank ℂ W ≤ a + 1 :=
      (Submodule.finrank_le W).trans (le_of_eq (finrank_fin_fun ℂ))
    have h_eq : finrank ℂ W = a + 1 := le_antisymm h_le (by omega)
    have h_top : W = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [h_eq, finrank_fin_fun ℂ])
    -- Extract a linearly independent subset B ⊆ S spanning W
    obtain ⟨B, hBS, hspan, hLI⟩ := exists_linearIndependent ℂ
      (v '' {ρ | (b : ℤ) - a ≤ ρ})
    have hspanB : span ℂ B = ⊤ := hspan.trans h_top
    have hBfin : B.Finite := hLI.set_finite_of_isNoetherian
    have : Fintype B := hBfin.fintype
    have hBcard : Fintype.card B = a + 1 := by
      have h1 := finrank_span_eq_card hLI
      rw [Subtype.range_coe, hspanB, finrank_top, finrank_fin_fun ℂ]
        at h1
      exact h1.symm
    -- Index B by Fin (a+1)
    set eB : Fin (a + 1) ≃ B :=
      (finCongr hBcard.symm).trans (Fintype.equivFin B).symm
    have hg_LI : LinearIndependent ℂ (Subtype.val ∘ eB) :=
      hLI.comp _ eB.injective
    -- Each basis element is v(ρ_i) for some ρ_i ≥ b-a
    have hg_mem : ∀ i, (eB i).val ∈ v '' {ρ | (b : ℤ) - a ≤ ρ} :=
      fun i => hBS (eB i).2
    choose ρ_vals hρ_ge hρ_eq using
      (fun i => (Set.mem_image _ _ _).mp (hg_mem i))
    -- The matrix M has det = 0 by Stage 2, but LI implies det ≠ 0
    set M := Matrix.of fun i j : Fin (a + 1) =>
      newtonHZ t (ρ_vals i + 1 + (j : ℤ))
    have h_det_zero : M.det = 0 :=
      det_vanishing_of_all_ge hvan _ hρ_ge
    have h_rows_eq : M.row = (Subtype.val ∘ eB) := by
      ext i j; simp only [Matrix.row_apply, M, Matrix.of_apply,
        Function.comp_apply]
      exact congr_fun (hρ_eq i) j
    exact absurd h_det_zero
      ((Matrix.isUnit_iff_isUnit_det M).mp
        (Matrix.linearIndependent_rows_iff_isUnit.mp
          (h_rows_eq ▸ hg_LI))).ne_zero
  -- ═══════ STAGE 3: extract the nonzero annihilator ═══════
  have h_lt_top : W < ⊤ := by
    rw [lt_top_iff_ne_top]; intro heq
    rw [heq, finrank_top, finrank_fin_fun ℂ] at h_finrank; omega
  obtain ⟨φ, hφ_ne, hφ_van⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top h_lt_top inferInstance
  refine ⟨fun k => φ (Pi.single k 1), ?_, ?_⟩
  · -- c ≠ 0: if all φ(eₖ) = 0 then φ = 0
    intro hc; apply hφ_ne
    apply LinearMap.ext; intro x
    have hx : x = ∑ k : Fin (a + 1), x k • Pi.single k (1 : ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun k _ => by
      have hk := congr_fun hc k
      simp only [Pi.zero_apply] at hk
      rw [map_smul, smul_eq_mul, hk, mul_zero]
  · -- The recurrence ∑ k, c k * h(ρ + 1 + k) = 0 for ρ ≥ b - a
    intro ρ hρ
    have hv_mem : v ρ ∈ W := subset_span ⟨ρ, hρ, rfl⟩
    have hφ_zero : φ (v ρ) = 0 := by
      have hmem : φ (v ρ) ∈ W.map φ := by
        rw [Submodule.mem_map]; exact ⟨v ρ, hv_mem, rfl⟩
      rwa [hφ_van, Submodule.mem_bot] at hmem
    have hdecomp : v ρ = ∑ k : Fin (a + 1),
        v ρ k • Pi.single k (1 : ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [show (∑ k, (fun k => φ (Pi.single k 1)) k *
          newtonHZ t (ρ + 1 + (k : ℤ))) = φ (v ρ) from by
      conv_rhs => rw [hdecomp, map_sum]
      congr 1; ext k; rw [map_smul, smul_eq_mul, mul_comm]]
    exact hφ_zero

end RS
