/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Symplectic structure of alternating nondegenerate bilinear forms

For a finite-dimensional complex vector space `V` equipped with an
alternating nondegenerate bilinear form `B`:

* **Symplectic splitting** (`exists_symplectic_splitting`): there
  exist `v, w` with `B v w = 1`, `B w v = −1`, spanning a
  2-dimensional nondegenerate plane `U` whose orthogonal complement
  `U^⊥` inherits an alternating nondegenerate restriction of `B`
  with `finrank ℂ U^⊥ = finrank ℂ V − 2`.

* **Standard basis** (`exists_symplectic_basis`): iterating the
  splitting gives a basis indexed by `Fin (2 * ℓ)` in two blocks —
  the first `ℓ` vectors and their partners — carrying the canonical
  symplectic pairing matrix.  In particular the dimension of `V` is
  even.

The assembly interleaves the plane's basis with the complement's
through `Basis.prod`, `Submodule.prodEquivOfIsCompl` and the
reindexing `symplecticReindexEquiv` on `Fin (2 * ℓ)`.
-/

@[expose] public section

noncomputable section

namespace RS

open LinearMap (BilinForm)
open LinearMap.BilinForm
open Module Submodule FiniteDimensional

/-! ### The symplectic plane -/

/-- Vectors `v, w` with `B v w = 1` and `B` alternating are linearly
independent: a dependence would make `B v w` a multiple of the
self-pairing `B w w`, which is zero. -/
private theorem linearIndependent_pair_of_pairing_one
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {B : BilinForm ℂ V} {v w : V} (hAlt : B.IsAlt) (hBvw : B v w = 1) :
    LinearIndependent ℂ ![v, w] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨fun hw_eq => ?_, fun a ha => ?_⟩
  · rw [hw_eq, map_zero] at hBvw; exact one_ne_zero hBvw.symm
  · have hc : B v w = a • B w w := by rw [← ha]; simp [map_smul]
    rw [hAlt.self_eq_zero, smul_zero] at hc
    rw [hc] at hBvw; exact one_ne_zero hBvw.symm

/-- The range of the pair `![v, w]` is the doubleton `{v, w}`. -/
private theorem range_pair_eq {V : Type*} (v w : V) :
    (Set.range ![v, w] : Set V) = {v, w} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp [Set.mem_insert_iff]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-! ### Disjointness of the symplectic plane and its orthogonal complement -/

/-- Given vectors `v, w` with `B v w = 1` and `B` alternating, the
span `{v, w}` is disjoint from its `B`-orthogonal complement. -/
private theorem disjoint_span_pair_orthogonal
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {B : BilinForm K V} (hAlt : B.IsAlt)
    {v w : V} (hBvw : B v w = 1) :
    Disjoint (span K {v, w}) (orthogonal B (span K {v, w})) := by
  have hRefl : B.IsRefl := hAlt.isRefl
  have hBwv : B w v = -1 := by
    have h := hAlt.neg_eq v w; rw [hBvw] at h; exact h.symm
  rw [Submodule.disjoint_def]
  intro x hxU hxPerp
  rw [mem_orthogonal_iff] at hxPerp
  have hxv := hxPerp v (subset_span (Set.mem_insert v {w}))
  have hxw := hxPerp w (subset_span (Set.mem_insert_iff.mpr (Or.inr rfl)))
  have hBxv : B x v = 0 := hRefl v x hxv
  have hBxw : B x w = 0 := hRefl w x hxw
  rw [mem_span_pair] at hxU
  obtain ⟨a, b, rfl⟩ := hxU
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hAlt.self_eq_zero, hBwv, hBvw, mul_zero, mul_one, mul_neg,
    add_zero, zero_add, neg_eq_zero] at hBxv hBxw
  rw [hBxw, hBxv, zero_smul, zero_smul, zero_add]

/-! ### Symplectic splitting -/

/-- **Symplectic splitting**: given `V` with an alternating nondegenerate
bilinear form `B` and `finrank ℂ V ≥ 1`, there exist vectors `v, w`
spanning a 2-dimensional symplectic plane `U` such that `B v w = 1`,
`B w v = −1`, and the orthogonal complement `U^⊥` carries an
alternating nondegenerate restriction of `B` with
`finrank ℂ U^⊥ = finrank ℂ V − 2`. -/
theorem exists_symplectic_splitting
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {B : BilinForm ℂ V} (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (hPos : 0 < finrank ℂ V) :
    ∃ (v w : V),
      B v w = 1 ∧ B w v = -1 ∧
      let U := span ℂ {v, w}
      (B.restrict U).Nondegenerate ∧
      IsCompl U (orthogonal B U) ∧
      (B.restrict (orthogonal B U)).IsAlt ∧
      (B.restrict (orthogonal B U)).Nondegenerate ∧
      finrank ℂ (orthogonal B U) = finrank ℂ V - 2 := by
  have hRefl : B.IsRefl := hAlt.isRefl
  have hV : Nontrivial V := by rwa [← @Module.finrank_pos_iff ℂ V]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hBv : ∃ w₀, B v w₀ ≠ 0 := by
    by_contra hall; push Not at hall
    exact hv (hND.1 v hall)
  obtain ⟨w₀, hw₀⟩ := hBv
  set w := (B v w₀)⁻¹ • w₀
  have hBvw : B v w = 1 := by simp
    [w, map_smul, smul_eq_mul, inv_mul_cancel₀ hw₀]
  have hBwv : B w v = -1 := by
    have h := hAlt.neg_eq v w; rw [hBvw] at h; exact h.symm
  set U := span ℂ {v, w}
  have hDisj := disjoint_span_pair_orthogonal hAlt hBvw
  have hRestND := nondegenerate_restrict_of_disjoint_orthogonal B hRefl hDisj
  have hCompl := isCompl_orthogonal_of_restrict_nondegenerate hRefl hRestND
  -- finrank U = 2
  have hLI := linearIndependent_pair_of_pairing_one hAlt hBvw
  have hSpanEq := range_pair_eq v w
  have hFinrankU : finrank ℂ U = 2 := by
    rw [show U = span ℂ (Set.range ![v, w]) from by rw [hSpanEq]]
    rw [finrank_span_eq_card hLI]; simp
  have hFinrankSum : finrank ℂ V =
      finrank ℂ U + finrank ℂ (orthogonal B U) := by
    have := finrank_sup_add_finrank_inf_eq U (orthogonal B U)
    rw [hCompl.sup_eq_top, hCompl.inf_eq_bot, finrank_top, finrank_bot] at this
    omega
  have hFinrankPerp : finrank ℂ (orthogonal B U) = finrank ℂ V - 2 := by omega
  have hAltPerp : (B.restrict (orthogonal B U)).IsAlt := fun ⟨x, _⟩ => by
    simp [restrict_apply, hAlt.self_eq_zero]
  have hNDPerp : (B.restrict (orthogonal B U)).Nondegenerate := by
    apply nondegenerate_restrict_of_disjoint_orthogonal B hRefl
    rw [orthogonal_orthogonal hND hRefl U]
    exact hCompl.symm.disjoint
  exact ⟨v, w, hBvw, hBwv, hRestND, hCompl, hAltPerp, hNDPerp, hFinrankPerp⟩

/-! ### Symplectic basis assembly -/

/-- Interleaving reindexing for the symplectic basis assembly: the two
"new" indices (0 and `ℓ' + 1`) map to `Fin 2`, and the remaining
indices thread through `Fin (2 * ℓ')`. -/
private def symplecticReindexEquiv (ℓ' : ℕ) :
    Fin (2 * (ℓ' + 1)) ≃ Fin 2 ⊕ Fin (2 * ℓ') where
  toFun i :=
    if h₁ : i.val = 0 then .inl 0
    else if h₂ : i.val ≤ ℓ' then .inr ⟨i.val - 1, by omega⟩
    else if h₃ : i.val = ℓ' + 1 then .inl 1
    else .inr ⟨i.val - 2, by omega⟩
  invFun
    | .inl k => if k.val = 0 then ⟨0, by omega⟩ else ⟨ℓ' + 1, by omega⟩
    | .inr j => if j.val < ℓ' then ⟨j.val + 1, by omega⟩ else ⟨j.val + 2, by
      omega⟩
  left_inv i := by
    dsimp only []
    split_ifs <;> dsimp only [] <;> split_ifs <;>
      (simp only [Fin.ext_iff]; omega)
  right_inv x := by
    rcases x with k | j
    · dsimp only []
      split_ifs <;> (dsimp only [] at *; try split_ifs) <;>
        first | rfl | (simp only [Sum.inl.injEq, Fin.ext_iff]; omega) | omega
    · dsimp only []
      split_ifs <;> (rw [Fin.val_mk] at *; try split_ifs) <;>
        first | rfl | (simp only [Sum.inr.injEq, Fin.ext_iff]; omega) | omega

/-- **Symplectic standard basis**: a finite-dimensional complex vector
space carrying an alternating nondegenerate bilinear form admits a
basis indexed by `Fin (2 * ℓ)` in two blocks — the first `ℓ` vectors
and their partners — with the canonical symplectic pairing matrix:
`B(eₘ, eₘ₊ℓ) = 1`, `B(eₘ₊ℓ, eₘ) = −1`, and all other pairings
vanish. -/
theorem exists_symplectic_basis {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : BilinForm ℂ V)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate) :
    ∃ (ℓ : ℕ) (_ : finrank ℂ V = 2 * ℓ)
      (f : Basis (Fin (2 * ℓ)) ℂ V),
      ∀ i j : Fin (2 * ℓ),
        B (f i) (f j) =
          if (i : ℕ) + ℓ = j then 1
          else if (j : ℕ) + ℓ = i then -1 else 0 := by
  induction h : finrank ℂ V using Nat.strongRecOn generalizing V with
  | ind n ih =>
  by_cases hn : n = 0
  · -- ═══════ Base case: finrank = 0 ═══════
    exact ⟨0, by omega, Module.finBasisOfFinrankEq ℂ V (by omega), fun i =>
      Fin.elim0 i⟩
  · -- ═══════ Inductive step ═══════
    have hPos : 0 < finrank ℂ V := by omega
    obtain ⟨v, w, hBvw, hBwv, _, hCompl, hAltPerp, hNDPerp, hFinrankPerp⟩ :=
      exists_symplectic_splitting hAlt hND hPos
    set U := span ℂ {v, w}
    -- ═══════ Linear independence and U-basis ═══════
    have hLI := linearIndependent_pair_of_pairing_one hAlt hBvw
    have hSpanEq := range_pair_eq v w
    have hSpanRangeEq : span ℂ (Set.range ![v, w]) = U := congr_arg (span ℂ ·)
      hSpanEq
    set bU : Basis (Fin 2) ℂ ↥U :=
      (Basis.span hLI).map (LinearEquiv.ofEq _ _ hSpanRangeEq) with hbU_def
    have hbU_coe : ∀ i, (bU i : V) = ![v, w] i := fun i => by
      simp [hbU_def, Basis.map_apply]
    -- ═══════ Finrank of U ═══════
    have hFinrankU : finrank ℂ U = 2 := by
      rw [show U = span ℂ (Set.range ![v, w]) from hSpanRangeEq.symm]
      rw [finrank_span_eq_card hLI]; simp
    have hFinrankSum : finrank ℂ V =
        finrank ℂ U + finrank ℂ (orthogonal B U) := by
      have := finrank_sup_add_finrank_inf_eq U (orthogonal B U)
      rw [hCompl.sup_eq_top, hCompl.inf_eq_bot, finrank_top,
        finrank_bot] at this
      omega
    -- ═══════ Inductive hypothesis on the complement ═══════
    have hLt : n - 2 < n := by omega
    obtain ⟨ℓ', hℓ', g, hg⟩ := ih (n - 2) hLt
      (B := B.restrict (orthogonal B U)) hAltPerp hNDPerp (by omega)
    -- ═══════ Basis assembly ═══════
    set bV := (bU.prod g).map (prodEquivOfIsCompl U (orthogonal B U) hCompl)
      with hbV_def
    set e := symplecticReindexEquiv ℓ'
    set f := bV.reindex e.symm with hf_def
    refine ⟨ℓ' + 1, by omega, f, ?_⟩
    -- ═══════ Pairing condition verification ═══════
    have hRefl : B.IsRefl := hAlt.isRefl
    -- Helper: bV applied to the two summands
    have hbV_inl : ∀ k : Fin 2, bV (.inl k) = ↑(bU k) := by
      intro k; simp [hbV_def, Basis.map_apply, coe_prodEquivOfIsCompl']
    have hbV_inr : ∀ k : Fin (2 * ℓ'), bV (.inr k) = ↑(g k) := by
      intro k; simp [hbV_def, Basis.map_apply, coe_prodEquivOfIsCompl']
    -- Helper: B-orthogonality between U and its complement
    have hBUP : ∀ (x : ↥U) (y : ↥(orthogonal B U)), B ↑x ↑y = 0 :=
      fun x y => mem_orthogonal_iff.mp y.prop x x.prop
    have hBPU : ∀ (x : ↥(orthogonal B U)) (y : ↥U), B ↑x ↑y = 0 :=
      fun x y => hRefl.eq_zero (mem_orthogonal_iff.mp x.prop y y.prop)
    -- Helper: restrict ↔ ambient
    have hRestrictPerp : ∀ (x y : ↥(orthogonal B U)),
        B.restrict (orthogonal B U) x y = B ↑x ↑y := fun _ _ => rfl
    -- The main verification: extract index arithmetic from the equiv inverse
    have hinv_inl : ∀ (k : Fin 2),
        (e.symm (.inl k)).val = if k.val = 0 then 0 else ℓ' + 1 := by
      intro k
      simp only [e, symplecticReindexEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
      split_ifs <;> rfl
    have hinv_inr : ∀ (k : Fin (2 * ℓ')),
        (e.symm (.inr k)).val = if k.val < ℓ' then k.val + 1 else k.val + 2 :=
          by
      intro k
      simp only [e, symplecticReindexEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
      split_ifs <;> rfl
    intro i j
    simp only [hf_def, Basis.reindex_apply, Equiv.symm_symm]
    -- Case-split on the image of i and j under the reindexing equivalence
    rcases hei : e i with ki | ki <;> rcases hej : e j with kj | kj
    · -- ═══════ Case 1: both in U-block ═══════
      rw [hbV_inl ki, hbV_inl kj, hbU_coe ki, hbU_coe kj]
      have hival : i.val = if ki.val = 0 then 0 else ℓ' + 1 := by
        have hsymm : e.symm (.inl ki) = i := by
          rw [← hei]; exact e.symm_apply_apply i
        rw [← congr_arg Fin.val hsymm]; exact hinv_inl ki
      have hjval : j.val = if kj.val = 0 then 0 else ℓ' + 1 := by
        have hsymm : e.symm (.inl kj) = j := by
          rw [← hej]; exact e.symm_apply_apply j
        rw [← congr_arg Fin.val hsymm]; exact hinv_inl kj
      have hM : ∀ (k : Fin 2), ![v, w] k = if k.val = 0 then v else w := by
        intro k; fin_cases k <;> rfl
      rw [hM ki, hM kj]
      split_ifs at hival hjval ⊢ <;>
        simp only [hAlt.self_eq_zero, hBvw, hBwv] <;>
        first | rfl | (exfalso; omega)
    · -- ═══════ Case 2: i in U, j in complement ═══════
      rw [hbV_inl ki, hbV_inr kj, hBUP (bU ki) (g kj)]
      have hival : i.val = if ki.val = 0 then 0 else ℓ' + 1 := by
        have hsymm : e.symm (.inl ki) = i := by
          rw [← hei]; exact e.symm_apply_apply i
        rw [← congr_arg Fin.val hsymm]; exact hinv_inl ki
      have hjval : j.val = if kj.val < ℓ' then kj.val + 1 else kj.val + 2 := by
        have hsymm : e.symm (.inr kj) = j := by
          rw [← hej]; exact e.symm_apply_apply j
        rw [← congr_arg Fin.val hsymm]; exact hinv_inr kj
      split_ifs at hival hjval ⊢ <;> first | rfl | (exfalso; omega)
    · -- ═══════ Case 3: i in complement, j in U ═══════
      rw [hbV_inr ki, hbV_inl kj, hBPU (g ki) (bU kj)]
      have hival : i.val = if ki.val < ℓ' then ki.val + 1 else ki.val + 2 := by
        have hsymm : e.symm (.inr ki) = i := by
          rw [← hei]; exact e.symm_apply_apply i
        rw [← congr_arg Fin.val hsymm]; exact hinv_inr ki
      have hjval : j.val = if kj.val = 0 then 0 else ℓ' + 1 := by
        have hsymm : e.symm (.inl kj) = j := by
          rw [← hej]; exact e.symm_apply_apply j
        rw [← congr_arg Fin.val hsymm]; exact hinv_inl kj
      split_ifs at hival hjval ⊢ <;> first | rfl | (exfalso; omega)
    · -- ═══════ Case 4: both in complement ═══════
      rw [hbV_inr ki, hbV_inr kj, ← hRestrictPerp, hg]
      have hival : i.val = if ki.val < ℓ' then ki.val + 1 else ki.val + 2 := by
        have hsymm : e.symm (.inr ki) = i := by
          rw [← hei]; exact e.symm_apply_apply i
        rw [← congr_arg Fin.val hsymm]; exact hinv_inr ki
      have hjval : j.val = if kj.val < ℓ' then kj.val + 1 else kj.val + 2 := by
        have hsymm : e.symm (.inr kj) = j := by
          rw [← hej]; exact e.symm_apply_apply j
        rw [← congr_arg Fin.val hsymm]; exact hinv_inr kj
      split_ifs at hival hjval ⊢ <;> first | rfl | (exfalso; omega)

end RS
