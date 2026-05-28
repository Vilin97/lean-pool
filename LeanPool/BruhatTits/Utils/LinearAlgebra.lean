/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Tactic

open Module

section

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

omit [Module.Free R M] in
lemma Submodule.zero_lt_finrank_of_ne_bot (p : Submodule R M) (hp : p ≠ ⊥) :
    0 < Module.finrank R p := by
  by_contra h
  simp only [not_lt, nonpos_iff_eq_zero, finrank_eq_zero] at h
  contradiction

omit [Module.Free R M] in
lemma Submodule.finrank_lt_finrank_of_ne_top (p : Submodule R M) (hp : p ≠ ⊤) :
    Module.finrank R p < Module.finrank R M := by
  obtain ⟨p', hp'⟩ := ComplementedLattice.exists_isCompl p
  rw [← Submodule.finrank_add_eq_of_isCompl hp']
  simp only [lt_add_iff_pos_right]
  apply Submodule.zero_lt_finrank_of_ne_bot
  intro hbot
  rw [hbot] at hp'
  apply hp
  exact eq_top_of_isCompl_bot hp'

omit [Module.Free R M] in
lemma Submodule.exists_generator_of_finrank_eq_one (p : Submodule R M)
    (h : Module.finrank R p = 1) :
    ∃ (v : M), v ≠ 0 ∧ Submodule.span R {v} = p := by
  have : p ≠ ⊥ := by rw [← p.one_le_finrank_iff, h]
  rw [p.ne_bot_iff] at this
  obtain ⟨v, hvmem, hv⟩ := this
  refine ⟨v, hv, ?_⟩
  have : (⟨v, hvmem⟩ : p) ≠ 0 := by simpa
  rw [finrank_eq_one_iff_of_nonzero (K := R) _ this] at h
  apply le_antisymm
  · rw [Submodule.span_le]
    simpa only [Set.singleton_subset_iff, SetLike.mem_coe, ne_eq, AddSubmonoid.mk_eq_zero]
  · intro x hx
    have hx' : (⟨x, hx⟩ : p) ∈ Submodule.span R {⟨v, hvmem⟩} := by
      rw [h]
      trivial
    rw [Submodule.mem_span_singleton] at hx' ⊢
    simp only [SetLike.mk_smul_mk, Subtype.mk.injEq] at hx'
    assumption

omit [Module.Free R M] in
lemma Submodule.exists_generator_of_finrank_eq_one_basis (b : Basis (Fin 2) R M) (p : Submodule R M)
    (hr : Module.finrank R p = 1)
    (ht : p ≠ Submodule.span R {b 0}) :
    ∃ (a : R), p = Submodule.span R { a • b 0 + b 1 } := by
  obtain ⟨v, hv, hvspan⟩ := p.exists_generator_of_finrank_eq_one hr
  have : v ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  let c : Fin 2 → R := b.repr v
  let β : R := c 1
  have hvr : v = c 0 • b 0 + β • b 1 := by
    rw [b.ext_elem_iff]
    intro i
    match i with
    | 0 => simp [c]
    | 1 => simp [c, β]
  have : β ≠ 0 := by
    intro hβ
    rw [hβ, zero_smul, add_zero] at hvr
    have : c 0 ≠ 0 := by
      intro hc
      rw [hc] at hvr
      simp at hvr
      contradiction
    apply ht
    rw [← hvspan, hvr]
    apply le_antisymm
    · rw [Submodule.span_le]
      simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp
    · rw [Submodule.span_le]
      simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
      have : b 0 = (c 0)⁻¹ • c 0 • b 0 := by
        rw [smul_smul]
        rw [inv_mul_cancel₀ this, one_smul]
      nth_rw 2 [this]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      simp
  use c 0 / β
  rw [← hvspan, hvr]
  apply le_antisymm
  · rw [Submodule.span_le]
    have : c 0 • b 0 + β • b 1 = β • ((c 0 / β) • b 0 + b 1) := by
      rw [smul_add, smul_smul]
      have hscalar : β * (c 0 / β) = c 0 := by field_simp [this]
      rw [hscalar]
    simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
    nth_rw 1 [this]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp
  · rw [Submodule.span_le]
    simp only [Fin.isValue, Set.singleton_subset_iff, SetLike.mem_coe]
    have : (c 0 / β) • b 0 + b 1 = (1 / β) • (c 0 • b 0 + β • b 1) := by
      rw [smul_add, smul_smul, smul_smul]
      have hleft : (1 / β) * c 0 = c 0 / β := by ring
      have hright : (1 / β) * β = 1 := by field_simp [this]
      rw [hleft, hright, one_smul]
    nth_rw 1 [this]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp

end

section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {P Q : Type*} [AddCommGroup P] [AddCommGroup Q] [Module R P] [Module R Q]

open TensorProduct LinearMap

variable (M)

/-- As a module of the quotient ring, left tensoring a module with a quotient of the ring
is the same as quotienting that module by the corresponding submodule. -/
noncomputable def quotTensorEquivQuotSMul' (I : Ideal R) :
    (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M ⧸ (I • ⊤ : Submodule R M) :=
  (quotTensorEquivQuotSMul M I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

variable {R M : Type*} [CommRing R] (I : Ideal R) [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `b` is an `ι`-indexed basis of `M` and Ì` is an ideal of `R`, the quotient
`M ⧸ I M` is `R ⧸ I` isomorphic to `ι → R ⧸ I`. -/
noncomputable def TensorProduct.quotientEquivPiOfBasis (b : Basis ι R M) :
    (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R ⧸ I] (ι → R ⧸ I) :=
  let f := TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) ι
  let g : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M ⧸ I • ⊤ :=
    (quotTensorEquivQuotSMul M I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let h : M ≃ₗ[R] (ι → R) := b.equivFun
  let h' : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] (R ⧸ I) ⊗[R] (ι → R) :=
    AlgebraTensorModule.congr (LinearEquiv.refl (R ⧸ I) (R ⧸ I)) h
  g.symm ≪≫ₗ h' ≪≫ₗ f

variable [StrongRankCondition (R ⧸ I)]

omit [DecidableEq ι] in
/-- If `M` is free, the rank of `M ⧸ IM`as an `R ⧸ I`-module is the rank of `M` as an `R`-module. -/
lemma quotient_finrank_eq (b : Basis ι R M) :
    Module.finrank (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)) = Fintype.card ι := by
  classical
  rw [(TensorProduct.quotientEquivPiOfBasis I b).finrank_eq]
  exact Module.finrank_fintype_fun_eq_card (R ⧸ I)

end

section

/-!
### Order on submodule above a fixed submodule
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance (p : Submodule R M) : OrderTop { p' : Submodule R M // p ≤ p' } where
  top := ⟨⊤, le_top⟩
  le_top _ _ _ := trivial

instance (p : Submodule R M) : OrderBot { p' : Submodule R M // p ≤ p' } where
  bot := ⟨p, le_rfl⟩
  bot_le p' _ hx := p'.property hx

lemma Submodule.quotient_equiv_eq_bot_iff (p : Submodule R M)
    (p' : { p' : Submodule R M // p ≤ p' }) :
    p' = ⊥ ↔ p'.val = p := by
  change p' = ⟨p, le_rfl⟩ ↔ p'.val = p
  apply Subtype.ext_iff

lemma lt_of_ne_top (p : Submodule R M) {p' : Submodule R p}
    (q : { q : Submodule R p // p' ≤ q})
    (h : q ≠ ⊤) : Submodule.map p.subtype q.val < p := by
  apply lt_of_le_of_ne
  · rw [Submodule.map_le_iff_le_comap]
    simp
  · intro hc
    absurd h
    rw [eq_top_iff]
    rintro x -
    simp
    have : x.val ∈ Submodule.map p.subtype q := by
      rw [hc]
      exact x.property
    simpa using this

end

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[simp]
lemma Submodule.comap_subtype_smul (I : Ideal R) (p : Submodule R M) :
    Submodule.comap p.subtype (I • p) = I • ⊤ := by
  ext x
  simp [Submodule.mem_smul_top_iff]

lemma Submodule.map_subtype_smul (I : Ideal R) (p : Submodule R M) :
    Submodule.map p.subtype (I • ⊤) = I • p := by
  rw [← Submodule.comap_subtype_smul, map_comap_eq_self]
  simp only [range_subtype]
  exact smul_le_right

lemma ideal_smul_lt_of_ne_bot {I : Ideal R} (p : Submodule R M)
    (q : { q : Submodule R p // (I • ⊤ : Submodule R p) ≤ q}) (h : q ≠ ⊥) :
    I • p < Submodule.map p.subtype q.val := by
  apply lt_of_le_of_ne
  · intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n hn
      let n' : p := ⟨n, hn⟩
      have : r • n' ∈ q.val := by
        apply q.property
        exact Submodule.smul_mem_smul hr trivial
      use r • n', this
      rfl
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  · intro hc
    apply_fun Submodule.comap p.subtype at hc
    rw [Submodule.comap_map_eq_self (by simp)] at hc
    simp at hc
    absurd h
    rw [Submodule.quotient_equiv_eq_bot_iff]
    exact hc.symm

end

section


@[simp]
lemma Matrix.GeneralLinearGroup.toLin_symm_apply {n : Type*} [DecidableEq n]
    [Fintype n] {R : Type*} [CommRing R] (g : LinearMap.GeneralLinearGroup R (n → R))
    (x : n → R) :
    (Matrix.GeneralLinearGroup.toLin.symm g).val.mulVec x = g.val x := by
  simp [Matrix.GeneralLinearGroup.toLin, LinearMap.toMatrixAlgEquiv']

end
