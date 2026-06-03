/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.MoritaEquivalence
import LeanPool.BrauerGroupNew.Wedderburn
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.LittleWedderburn

/-!
# The Stacks Project tag 074E

This file ports the upstream Wedderburn-Artin uniqueness arguments used by the Brauer group
development.
-/

open CategoryTheory DirectSum

universe u v w

section simple

@[stacks 074E "(1)"]
lemma linearEquiv_of_isSimpleModule_over_simple_ring
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] : Nonempty (M ≃ₗ[A] N) := by
  obtain ⟨n, hn, D, _, _, ⟨iso₁⟩⟩ := WedderburnArtin_algebra_version k A
  have : NeZero n := ⟨hn⟩
  let e₁ := moritaEquivalentToMatrix.{_, _, w} D (Fin n)
  let e₂ : ModuleCat.{w} A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm.toRingEquiv
  let e₃ := e₂.trans e₁.symm
  haveI : IsSimpleModule A (ModuleCat.of A M) := inferInstanceAs <| IsSimpleModule A M
  haveI : IsSimpleModule A (ModuleCat.of A N) := inferInstanceAs <| IsSimpleModule A N
  haveI := IsMoritaEquivalent.division_ring.IsSimpleModule.functor A D e₃ (ModuleCat.of A M)
  haveI := IsMoritaEquivalent.division_ring.IsSimpleModule.functor A D e₃ (ModuleCat.of A N)
  obtain ⟨iso₂⟩ := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule D
    (e₃.functor.obj (ModuleCat.of A M))
  obtain ⟨iso₃⟩ := IsMoritaEquivalent.division_ring.division_ring_exists_unique_isSimpleModule D
    (e₃.functor.obj (ModuleCat.of A N))
  let iso₄ : e₃.functor.obj (ModuleCat.of A M) ≅ e₃.functor.obj (ModuleCat.of A N) :=
    LinearEquiv.toModuleIso <| iso₂ ≪≫ₗ iso₃.symm
  let iso₅ : ModuleCat.of A M ≅ ModuleCat.of A N :=
    e₃.unitIso.app (ModuleCat.of A M) ≪≫ e₃.inverse.mapIso iso₄ ≪≫
      (e₃.unitIso.app (ModuleCat.of A N)).symm
  exact ⟨iso₅.toLinearEquiv⟩

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [FiniteDimensional k A]

lemma directSum_simple_module_over_simple_ring
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (S : Type v) (_ : AddCommGroup S) (_ : Module A S) (_ : IsSimpleModule A S)
      (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  classical
  obtain ⟨n, hn, D, inst1, inst2, ⟨iso₁⟩⟩ := WedderburnArtin_algebra_version k A
  have : NeZero n := ⟨hn⟩
  let e₁ := moritaEquivalentToMatrix D (Fin n)
  let e₂ : ModuleCat A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv iso₁.symm.toRingEquiv
  let e := e₂.trans e₁.symm
  let S := e.inverse.obj (ModuleCat.of D D)
  haveI : IsSimpleModule D (ModuleCat.of D D) := inferInstanceAs <| IsSimpleModule D D
  haveI : IsSimpleModule A S :=
    IsMoritaEquivalent.division_ring.IsSimpleModule.functor _ _ e.symm (ModuleCat.of D D)
  obtain ⟨b, hb⟩ : Module.Free D (e.functor.obj (ModuleCat.of A M)) := inferInstance
  refine ⟨S, inferInstance, inferInstance, inferInstance, b, ⟨?_⟩⟩
  let iso₂ : e.functor.obj (ModuleCat.of A M) ≅ ModuleCat.of D (b →₀ D) := hb.repr.toModuleIso
  let iso₃ : ModuleCat.of A M ≅ e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    e.unitIso.app (ModuleCat.of A M) ≪≫ (e.inverse.mapIso iso₂)
  let iso₄₀ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      ModuleCat.of A (⨁ (i : b), e.inverse.obj (ModuleCat.of D D)) :=
    LinearEquiv.toModuleIso (finsuppLequivDFinsupp _)
  let iso₄₁ :
    ModuleCat.of A (⨁ (i : b), e.inverse.obj (ModuleCat.of D D)) ≅
    ∐ fun i : b ↦ ModuleCat.of A (e.inverse.obj (ModuleCat.of D D)) :=
        Iso.symm (ModuleCat.coprodIsoDirectSum _)
  let iso₄₂ :
    (∐ fun i : b ↦ (e.inverse.obj (ModuleCat.of D D))) ≅
    e.inverse.obj (∐ fun i : b ↦ .of D D) := Limits.PreservesCoproduct.iso _ _ |>.symm
  let iso₄₃ : e.inverse.obj (∐ fun i : b ↦ ModuleCat.of D D) ≅
    e.inverse.obj (ModuleCat.of D (⨁ i : b, D)) :=
    e.inverse.mapIso (ModuleCat.coprodIsoDirectSum _)
  let iso₄₄ : e.inverse.obj (ModuleCat.of D (⨁ i : b, D)) ≅
    e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    e.inverse.mapIso (LinearEquiv.toModuleIso (finsuppLequivDFinsupp _).symm)
  let iso₄ :
      ModuleCat.of A (b →₀ e.inverse.obj (ModuleCat.of D D)) ≅
      e.inverse.obj (ModuleCat.of D (b →₀ D)) :=
    iso₄₀ ≪≫ iso₄₁ ≪≫ iso₄₂ ≪≫ iso₄₃ ≪≫ iso₄₄
  exact iso₃ ≪≫ iso₄.symm |>.toLinearEquiv

lemma directSum_simple_module_over_simple_ring'
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [IsSimpleRing A]
    [FiniteDimensional k A] (M : Type v) [AddCommGroup M] [Module A M]
    (S : Type v) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    ∃ (ι : Type v), Nonempty (M ≃ₗ[A] (ι →₀ S)) := by
  obtain ⟨T, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring k A M
  obtain ⟨iso'⟩ := linearEquiv_of_isSimpleModule_over_simple_ring k A S T
  exact ⟨ι, ⟨iso ≪≫ₗ Finsupp.mapRange.linearEquiv iso'.symm⟩⟩

lemma linearEquiv_iff_finrank_eq_over_simple_ring
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module k M] [Module k N]
    [IsScalarTower k A M] [IsScalarTower k A N]
    [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔
    Module.finrank k M = Module.finrank k N := by
  haveI : FiniteDimensional k M := Module.Finite.trans A M
  haveI : FiniteDimensional k N := Module.Finite.trans A N
  fconstructor
  · rintro ⟨iso⟩
    refine LinearEquiv.finrank_eq { iso with map_smul' := ?_ }
    intros a m
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.map_smul_of_tower,
      LinearEquiv.coe_coe, RingHom.id_apply]
  · intro h
    obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring k A M
    obtain ⟨ι', ⟨iso'⟩⟩ := directSum_simple_module_over_simple_ring' k A N S
    have HS : Nontrivial S := IsSimpleModule.nontrivial A S
    cases isEmpty_or_nonempty ι
    · letI : Unique M := ⟨⟨0⟩, by
        intros a
        apply_fun iso using LinearEquiv.injective _
        apply Subsingleton.elim⟩
      have eq : Module.finrank k M = 0 := by
        rw [Module.finrank_eq_zero_iff]
        exact fun m ↦ ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
      have eq' : Module.finrank k N = 0 := by
        rw [← h, eq]
      haveI : Unique N := ⟨⟨0⟩, by
        rw [Module.finrank_zero_iff] at eq'
        intro n
        exact Subsingleton.elim _ _⟩
      refine ⟨⟨0, 0, fun x ↦ Subsingleton.elim _ _, fun x ↦ Subsingleton.elim _ _⟩⟩
    cases isEmpty_or_nonempty ι'
    · letI : Unique N := ⟨⟨0⟩, by
        intros a
        apply_fun iso' using LinearEquiv.injective _
        apply Subsingleton.elim⟩
      have eq : Module.finrank k N = 0 := by
        rw [Module.finrank_eq_zero_iff]
        exact fun m ↦ ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
      have eq' : Module.finrank k M = 0 := by
        rw [h, eq]
      haveI : Unique M := ⟨⟨0⟩, by
        rw [Module.finrank_zero_iff] at eq'
        intro n
        exact Subsingleton.elim _ _⟩
      exact ⟨⟨0, 0, fun x ↦ Subsingleton.elim _ _, fun x ↦ Subsingleton.elim _ _⟩⟩
    letI := Module.compHom S (Algebra.ofId k A).toRingHom
    let ISO : M ≃ₗ[k] ι →₀ S :=
    { iso with
      map_smul' := by
        intros a m
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply]
        rw [algebra_compatible_smul A]
        change iso (algebraMap k A a • _) = algebraMap k A a • _
        rw [map_smul] }
    have eq := LinearEquiv.finrank_eq ISO
    let ISO' : N ≃ₗ[k] ι' →₀ S :=
    { iso' with
      map_smul' := by
        intros a m
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply]
        rw [algebra_compatible_smul A]
        change iso' (algebraMap k A a • _) = algebraMap k A a • _
        rw [map_smul] }
    have eq' := LinearEquiv.finrank_eq ISO'
    have EQ : Module.finrank k (ι →₀ S) = Module.finrank k (ι' →₀ S) := by
      rw [← eq, h, eq']
    haveI : Module.Finite k (ι →₀ S) := Module.Finite.equiv ISO
    haveI : Module.Finite k (ι' →₀ S) := Module.Finite.equiv ISO'
    haveI : Module.Finite k S := by
      suffices IsNoetherian k S from inferInstance
      rw [IsNoetherian.iff_rank_lt_aleph0]
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_right (Module.rank k S) (Cardinal.mk ι)
        (by rw [Cardinal.mk_ne_zero_iff]; infer_instance)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq
    haveI : Fintype ι := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι).1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq
      have ineq : Module.rank k M < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι) (Module.rank k S)
        (by
          suffices 0 < Module.rank k S by exact Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq
    haveI : Fintype ι' := by
      refine (@Cardinal.lt_aleph0_iff_fintype ι').1 ?_ |>.some
      apply_fun ((↑) : ℕ → Cardinal) at eq'
      rw [Module.finrank_eq_rank, Module.finrank_eq_rank, rank_finsupp] at eq'
      have ineq : Module.rank k N < Cardinal.aleph0 := by
        rw [Module.rank_lt_aleph0_iff]; infer_instance
      rw [eq'] at ineq
      simp only [Cardinal.lift_id] at ineq
      have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι') (Module.rank k S)
        (by
          suffices 0 < Module.rank k S from
            Ne.symm (ne_of_lt this)
          apply rank_pos)
      rw [mul_comm] at ineq2
      exact lt_of_le_of_lt ineq2 ineq
    rw [Module.finrank_finsupp,  Module.finrank_finsupp] at EQ
    simp only [mul_eq_mul_right_iff] at EQ
    replace EQ := EQ.resolve_right
      (by have := Module.finrank_pos (R := k) (M := S); omega)
    rw [Fintype.card_eq] at EQ
    obtain ⟨e⟩ := EQ
    let E : (ι →₀ S) ≃ₗ[A] (ι' →₀ S) :=
      { Finsupp.equivCongrLeft e with
        map_add' := by intros a b; ext; simp
        map_smul' := by intros a b; ext; simp }
    refine ⟨iso ≪≫ₗ E ≪≫ₗ iso'.symm⟩

omit [IsSimpleRing A] [FiniteDimensional k A] in
@[stacks 074E "(3) first part"]
lemma simple_mod_of_wedderburn {n : ℕ} (hn : n ≠ 0)
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
    IsSimpleModule A (Fin n → D) := by
  letI : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : NeZero n := ⟨hn⟩
  let e : ModuleCat.{v} A ≌ ModuleCat (Matrix (Fin n) (Fin n) D) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv wdb.toRingEquiv.symm
  have inst1 : IsSimpleModule (Matrix (Fin n) (Fin n) D) (Fin n → D) := by
    haveI : IsSimpleModule D (ModuleCat.of D D) := inferInstanceAs <| IsSimpleModule D D
    exact IsMoritaEquivalent.division_ring.IsSimpleModule.functor D (Matrix (Fin n) (Fin n) D)
      (moritaEquivalentToMatrix D (Fin n)) (ModuleCat.of D D)
  have := IsMoritaEquivalent.division_ring.IsSimpleModule.functor (Matrix (Fin n) (Fin n) D) A
    e.symm (ModuleCat.of (Matrix (Fin n) (Fin n) D) (Fin n → D))
  exact this

noncomputable section wedderburn

/-- Restricts endomorphisms along a Wedderburn equivalence with a matrix algebra. -/
abbrev endCatEquiv (n : ℕ)
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v)
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)] [IsScalarTower k A (Fin n → D)]
    [SMulCommClass A k (Fin n → D)] :
    Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  .ofAlgHom {
    toFun f := {
      __ := f
      map_smul' := fun a v => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
        rw [show a • v = wdb.symm a • v by simp [smul_def], map_smul, smul_def]
        simp
    }
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' := by intros; ext; simp }
  { toFun f := {
      toFun := f
      map_add' := f.map_add
      map_smul' := fun a b => by
        simp only [smul_def, LinearMapClass.map_smul, RingHom.id_apply]
    }
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' := by intros; ext; simp }
  (by rfl) (by rfl)

omit [IsSimpleRing A] [FiniteDimensional k A] in
private lemma matrixModuleVectorDecomp {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D] (v : Fin n → D) :
    v = ∑ j : Fin n, (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) •
      Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D) := by
  ext t
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single]
  · intro j _ hj
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, hj]
  · intro ht
    simp at ht

omit [IsSimpleRing A] [FiniteDimensional k A] in
private lemma matrixModuleEnd_apply {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D]
    (f : Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D)) (v : Fin n → D) (i : Fin n) :
    f v i = v i * f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0 := by
  let e₀ : Fin n → D := Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)
  let c : D := f e₀ 0
  have hfe₀ (j : Fin n) : f e₀ j = Pi.single (M := fun _ : Fin n => D) (0 : Fin n) c j := by
    by_cases h : j = 0
    · subst h
      simp [c]
    · have hzero : (Matrix.single (0 : Fin n) j (1 : D) :
          Matrix (Fin n) (Fin n) D) • e₀ = 0 := by
        ext t
        by_cases ht : (0 : Fin n) = t
        · subst ht
          simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, e₀, h]
        · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, e₀, ht]
      have hmap := congrFun (f.map_smul (Matrix.single (0 : Fin n) j (1 : D)) e₀) 0
      rw [hzero] at hmap
      simp [Matrix.mulVec, dotProduct, Matrix.single, e₀] at hmap
      simpa [e₀, Pi.single, h, c] using hmap.symm
  have hv := matrixModuleVectorDecomp D v
  calc
    f v i = f (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) • e₀) i := by
      simpa [e₀] using congrArg (fun w => f w i) hv
    _ = (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) • f e₀) i := by
      rw [map_sum]
      refine congrArg (fun w : Fin n → D => w i) ?_
      exact Finset.sum_congr rfl fun j _ => f.map_smul (Matrix.single j 0 (v j)) e₀
    _ = (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) •
          Pi.single (M := fun _ : Fin n => D) (0 : Fin n) c) i := by
      refine congrArg (fun w : Fin n → D => w i) ?_
      apply Finset.sum_congr rfl
      intro j _
      rw [funext hfe₀]
    _ = v i * c := by
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single]
      · intro j _ hj
        simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, hj]
      · intro hi
        simp at hi
    _ = v i * f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0 := rfl

omit [IsSimpleRing A] [FiniteDimensional k A] in
private noncomputable def matrixModuleEndAlgEquivMop {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D]
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)]
    [SMulCommClass (Matrix (Fin n) (Fin n) D) k (Fin n → D)] :
    Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) ≃ₐ[k] Dᵐᵒᵖ where
  toFun f := MulOpposite.op (f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0)
  invFun c :=
  { toFun v := fun i => v i * c.unop
    map_add' := by
      intro v w
      ext i
      simp [add_mul]
    map_smul' := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc] }
  left_inv f := by
    ext v i
    simp [matrixModuleEnd_apply D f v i]
  right_inv c := by
    apply MulOpposite.unop_injective
    simp
  map_mul' f g := by
    apply MulOpposite.unop_injective
    simp [matrixModuleEnd_apply D f (g (Pi.single (0 : Fin n) (1 : D))) 0]
  map_add' f g := by
    apply MulOpposite.unop_injective
    simp
  commutes' a := by
    apply MulOpposite.unop_injective
    simp [Pi.single, Algebra.smul_def]

@[stacks 074E "(3) first part"]
def endSimpleModOfWedderburn (n : ℕ) (hn : n ≠ 0) (D : Type v) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) :
    let _ : Module A (Fin n → D) := .compHom _ wdb.toRingEquiv.toRingHom
    -- these should be in Morita file
    have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
    { smul_assoc a b x := by
        ext i
        exact congrFun (smul_assoc a b x) i }
    letI _ : IsScalarTower k A (Fin n → D) :=
    { smul_assoc a b x := by
        change wdb (a • b) • x = _
        rw [map_smul, Algebra.smul_def, mul_smul]
        rw [algebraMap_smul]
        rfl }
    letI _ : SMulCommClass A k (Fin n → D) :=
      { smul_comm a b x := by
          change wdb a • b • x = b • wdb a • x
          ext i
          exact congrFun (smul_comm (wdb a) b x) i }
    Module.End A (Fin n → D) ≃ₐ[k] Dᵐᵒᵖ := by
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc a b x := by
      ext i
      exact congrFun (smul_assoc a b x) i }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc a b x := by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm a b x := by
        change wdb a • b • x = b • wdb a • x
        ext i
        exact congrFun (smul_comm (wdb a) b x) i }
  have : NeZero n := ⟨hn⟩
  let e₁ : Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
    endCatEquiv k A n D wdb fun _ _ => rfl
  exact e₁.trans (matrixModuleEndAlgEquivMop (k := k) (n := n) D)

end wedderburn

lemma endSimpleModOfWedderburn' (n : ℕ) (hn : n ≠ 0) (D : Type v) [DivisionRing D] [Algebra k D]
    (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D) (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    Nonempty <| Module.End A M ≃ₐ[k] Dᵐᵒᵖ := by
  let e := endSimpleModOfWedderburn k A n hn D wdb
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc a b x := by
      ext i
      exact congrFun (smul_assoc a b x) i }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc a b x := by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm a b x := by
        change wdb a • b • x = b • wdb a • x
        ext i
        exact congrFun (smul_comm (wdb a) b x) i }
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A hn D wdb
  obtain ⟨iso⟩ := linearEquiv_of_isSimpleModule_over_simple_ring k A M (Fin n → D)
  exact ⟨(iso.conjAlgEquiv k).trans e⟩

instance end_simple_mod_finite
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    FiniteDimensional k (Module.End A M) := by
  obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := WedderburnArtin_algebra_version k A
  have : NeZero n := ⟨hn⟩
  obtain ⟨iso⟩ := endSimpleModOfWedderburn' k A n hn D e M
  let E : Dᵐᵒᵖ ≃ₗ[k] D := MulOpposite.opLinearEquiv k |>.symm
  have : Module.Finite k D := by
    haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := e.toLinearEquiv.finiteDimensional
    rw [← Module.rank_lt_aleph0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1
  have : FiniteDimensional k Dᵐᵒᵖ := E.symm.finiteDimensional
  refine iso.symm.toLinearEquiv.finiteDimensional

-- instance (D : Type v) [DivisionRing D] : Module.Finite Dᵐᵒᵖ D := by
--   rw [Module.finite_def]
--   refine ⟨{1}, eq_top_iff.2 fun x _ => ?_⟩
--   simp only [Finset.coe_singleton]
--   rw [show x = (MulOpposite.op x : Dᵐᵒᵖ) • 1 by simp]
--   exact Submodule.smul_mem _ _ <| Submodule.subset_span rfl

instance instAlgebraEndOfIsScalarTowerLeanPool (M : Type v) [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] :
    Algebra k (Module.End (Module.End A M) M) where
  algebraMap := {
    toFun a :=
    { toFun m := a • m
      map_add' := by simp only [smul_add, implies_true]
      map_smul' := by
        simp only [Module.End.smul_def, RingHom.id_apply, LinearMap.map_smul_of_tower,
          implies_true] }
    map_one' := by ext; simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    map_mul' := by
      intros; ext
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearMap.map_smul_of_tower]
      rw [mul_comm, mul_smul]
    map_zero' := by ext; simp
    map_add' := by
      intros; ext
      simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  }
  commutes' := by
    intros r f
    ext m
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    let s : Module.End A M :=
    { toFun x := r • x
      map_add' := by simp
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
        congr 1
        exact Algebra.commutes r a }
    rw [show r • m = s • m by rfl, f.map_smul]
    rfl
  smul r f :=
  { toFun m := f <| r • m
    map_add' := by simp
    map_smul' := by
      intro g m
      simp only [Module.End.smul_def, RingHom.id_apply]
      let s : Module.End A M :=
      { toFun x := r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
      change f (s • g m) = g (f <| s • m)
      rw [f.map_smul, f.map_smul]
      simp only [Module.End.smul_def, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul_of_tower,
        s]
      change r • f (g • m) = _
      rw [f.map_smul]
      simp }
  smul_def' := by
    intro r f
    ext m
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    let s : Module.End A M :=
      { toFun x := r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
    change _ = s • f m
    rw [← f.map_smul]
    rfl

omit [IsSimpleRing A] in
lemma exists_gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] :
    ∃ m : M, m ≠ 0 ∧ ∀ m', ∃ a : A, m' = a • m := by
    have i : Submodule.IsPrincipal (⊤ : Submodule A M) := inferInstance
    refine ⟨i.1.choose, ?_, fun m ↦ by
      classical
      have : m ∈ Submodule.span A {i.1.choose} := by
        rw [← i.1.choose_spec]; trivial
      rw [Submodule.mem_span_singleton] at this
      simpa [Eq.comm]⟩
    intro h
    have := i.1.choose_spec
    rw [h] at this
    simp only [Submodule.span_zero_singleton, top_ne_bot] at this

/-- A chosen nonzero generator for a simple module. -/
noncomputable def gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] : M :=
    (exists_gen A M).choose

omit [IsSimpleRing A] in
lemma gen_ne_zero (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    gen A M ≠ 0 := (exists_gen A M).choose_spec.1

omit [IsSimpleRing A] in
lemma gen_spec (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] (m' : M) :
    ∃ a : A, m' = a • gen A M := (exists_gen A M).choose_spec.2 m'

/-- The left action map into the double centralizer endomorphism algebra. -/
@[simps]
def toEndEnd (M : Type v) [AddCommGroup M] [Module A M] :
    A →ₗ[A] Module.End (Module.End A M) M where
  toFun a :=
  { toFun m := a • m
    map_add' := by simp
    map_smul' := fun f m => (f.map_smul a m).symm }
  map_add' := by intros; ext; simp [add_smul]
  map_smul' := by intros; ext; simp [mul_smul]

omit [IsSimpleRing A] in
@[simp]
lemma toEndEnd_apply (M : Type v) [AddCommGroup M] [Module A M] (a : A) (m : M) :
    toEndEnd A M a m = a • m := rfl

/-- The algebra homomorphism induced by the double centralizer action map. -/
def toEndEndAlgHom (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    A →ₐ[k] Module.End (Module.End A M) M where
  __ := toEndEnd A M
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  commutes' a := by
    ext m
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, toEndEnd_apply, algebraMap_smul]
    rfl

instance (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nontrivial (Module.End (Module.End A M) M) where
  exists_pair_ne := ⟨0, 1, fun eq ↦ gen_ne_zero A M congr($eq (gen A M)).symm⟩

omit [FiniteDimensional k A] in
lemma toEndEnd_injective
    (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Function.Injective (toEndEnd A M) :=
  RingHom.injective (toEndEndAlgHom k A M).toRingHom

/-- A module is balanced when the double centralizer action map is surjective. -/
class IsBalanced (M : Type v) [AddCommGroup M] [Module A M] : Prop where
  surj : Function.Surjective (toEndEnd A M)

instance : IsBalanced A A where
  surj f := by
    refine ⟨f 1, ?_⟩
    ext x
    simp only [toEndEnd_apply, smul_eq_mul]
    let X : Module.End A A := LinearMap.mulRight _ x
    simpa [Module.End.smul_def, LinearMap.coe_mk, AddHom.coe_mk, one_mul, X]
      using (f.map_smul X 1).symm

omit [IsSimpleRing A] in
lemma IsBalanced.congr_aux (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Module A N] (l : M ≃ₗ[A] N) (h : IsBalanced A M) : IsBalanced A N := by
  refine ⟨fun a => ?_⟩
  let a' : Module.End (Module.End A M) M :=
  { toFun m := l.symm <| a (l m)
    map_add' := by simp
    map_smul' := fun x y => by
      simp only [Module.End.smul_def, RingHom.id_apply]
      let L := l.toLinearMap ∘ₗ x ∘ₗ l.symm.toLinearMap
      have := a.map_smul L (l y)
      simp only [Module.End.smul_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply, L] at this
      simp [this] }
  obtain ⟨b, hb⟩ := h.1 a'
  refine ⟨b, ?_⟩
  ext n
  have hb' := congrArg (fun f : Module.End (Module.End A M) M => f (l.symm n)) hb
  simp only [a', toEndEnd_apply_apply] at hb'
  apply_fun l at hb'
  simpa using hb'

omit [IsSimpleRing A] in
lemma IsBalanced.congr {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) : IsBalanced A M ↔ IsBalanced A N := by
  constructor
  · apply IsBalanced.congr_aux; exact l
  · apply IsBalanced.congr_aux; exact l.symm

lemma isBalanced_of_simpleMod (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] : IsBalanced A M := by
  classical
  obtain ⟨ι, ⟨e⟩⟩ := directSum_simple_module_over_simple_ring' k A A M
  haveI b : IsBalanced A (ι →₀ M) := by
    rw [← IsBalanced.congr A e]
    infer_instance
  refine ⟨fun g => ?_⟩
  let G : Module.End (Module.End A (ι →₀ M)) (ι →₀ M) :=
  { toFun v := Finsupp.mapRange g (by simp) v
    map_add' := by intros; ext; simp
    map_smul' := by
      intro f v
      ext i
      simp only [Module.End.smul_def, Finsupp.mapRange_apply, RingHom.id_apply]
      let x (i j : ι) : Module.End A M :=
      { toFun m := f (Finsupp.single i m) j
        map_add' := by simp
        map_smul' := by
          intro a m
          simp only [RingHom.id_apply]
          rw [← Finsupp.smul_single, map_smul]
          rfl }
      have eq (i j k : ι) := g.map_smul (x i j) (v k)
      simp only [Module.End.smul_def, LinearMap.coe_mk, AddHom.coe_mk, x] at eq
      conv_lhs => rw [show v = ∑ i ∈ v.support, Finsupp.single i (v i) by
        ext j
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
          Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not]
        aesop]
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      change ∑ j ∈ _, _ = _
      simp_rw [eq]
      rw [show ∑ x ∈ v.support, (f (Finsupp.single x (g (v x)))) i =
        (∑ x ∈ v.support, f (Finsupp.single x (g (v x)))) i by simp [Finsupp.coe_finsetSum],
        ← map_sum]
      congr
      ext j
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
        Finsupp.mem_support_iff, ne_eq, ite_not, Finsupp.mapRange_apply, ite_eq_right_iff]
      aesop }
  obtain ⟨a, ha⟩ := b.1 G
  refine ⟨a, ?_⟩
  ext m
  haveI : Nonempty ι := by
    refine isEmpty_or_nonempty ι |>.resolve_left ?_
    intro H
    haveI : Subsingleton (ι →₀ M) := inferInstance
    haveI : Subsingleton A := Equiv.subsingleton e.toEquiv
    have eq1 : (1 : A) = 0 := Subsingleton.elim _ _
    have : Nontrivial A := inferInstance
    exact one_ne_zero eq1
  obtain ⟨j⟩ := this
  have := congr($ha (Finsupp.single j m))
  simp only [toEndEnd_apply, Finsupp.smul_single, LinearMap.coe_mk, AddHom.coe_mk,
    Finsupp.mapRange_single, G] at this ⊢
  have := congr($this j)
  simp only [Finsupp.single_eq_same] at this
  exact this

/-- The double centralizer algebra equivalence for a simple module. -/
noncomputable def endEndIso
    (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  AlgEquiv.ofBijective (toEndEndAlgHom k A M) ⟨toEndEnd_injective k A M,
    isBalanced_of_simpleMod k A M |>.1⟩

lemma WedderburnArtin_uniqueness₀
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    Nonempty <| D ≃ₐ[k] D' := by
  let _ : Module A (Fin n → D) := Module.compHom _ wdb.toRingEquiv.toRingHom
  have : IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  { smul_assoc a b x := by
      ext i
      exact congrFun (smul_assoc a b x) i }
  letI _ : IsScalarTower k A (Fin n → D) :=
  { smul_assoc a b x := by
      change wdb (a • b) • x = _
      rw [map_smul, Algebra.smul_def, mul_smul]
      rw [algebraMap_smul]
      rfl }
  letI _ : SMulCommClass A k (Fin n → D) :=
    { smul_comm a b x := by
        change wdb a • b • x = b • wdb a • x
        ext i
        exact congrFun (smul_comm (wdb a) b x) i }
  haveI : IsSimpleModule A (Fin n → D) := simple_mod_of_wedderburn k A (NeZero.ne _) D wdb
  have ⟨iso⟩ := endSimpleModOfWedderburn' k A n (NeZero.ne _) D wdb (Fin n → D)
  have ⟨iso'⟩ := endSimpleModOfWedderburn' k A n' (NeZero.ne _) D' wdb' (Fin n → D)
  exact ⟨AlgEquiv.op.symm (iso.symm.trans iso')⟩

lemma WedderburnArtin_uniqueness₁
    (n n' : ℕ) [NeZero n] [NeZero n']
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    (D' : Type v) [DivisionRing D'] [Algebra k D'] (wdb' : A ≃ₐ[k] Matrix (Fin n') (Fin n') D') :
    n = n' := by
  have ⟨iso⟩ := WedderburnArtin_uniqueness₀ k A n n' D wdb D' wdb'
  let e : Matrix (Fin n) (Fin n) D ≃ₐ[k] Matrix (Fin n') (Fin n') D :=
    wdb.symm.trans (wdb'.trans iso.symm.mapMatrix)
  haveI : Module.Finite k D := by
    haveI inst1 : Module.Finite k (Matrix (Fin n) (Fin n) D) := wdb.toLinearEquiv.finiteDimensional
    rw [← Module.rank_lt_aleph0_iff] at inst1 ⊢
    have eq1 := rank_mul_rank k D (Matrix (Fin n) (Fin n) D)
    simp only [rank_matrix', Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_mul,
      Cardinal.lift_natCast] at eq1
    rw [← eq1, mul_comm] at inst1
    exact lt_of_le_of_lt (Cardinal.le_mul_left (a := Module.rank k D) (b := n * n) (by
      simpa only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, or_self] using NeZero.ne n)) inst1
  have eq1 := Module.finrank_matrix k D (Fin n) (Fin n)
  have eq2 := Module.finrank_matrix k D (Fin n') (Fin n')
  simp only [Fintype.card_fin] at eq1 eq2
  have eq3 : n * n * Module.finrank k D = n' * n' * Module.finrank k D := by
    rw [← eq1, ← eq2]
    exact LinearEquiv.finrank_eq e
  simp only [mul_eq_mul_right_iff] at eq3
  replace eq3 := eq3.resolve_right (fun rid => by
    rw [Module.finrank_zero_iff] at rid
    simpa using rid.elim 0 1)
  simpa [← pow_two] using eq3

end simple
