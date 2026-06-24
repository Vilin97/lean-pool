/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.BrauerGroup
import LeanPool.BrauerGroupNew.LemmasAboutSimpleRing
import LeanPool.BrauerGroupNew.Morita.ChangeOfRings

/-!
# LeanPool.BrauerGroupNew.Azumaya.Basic

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Azumaya.Basic`.
-/

universe u v

open Module TensorProduct

section Field
variable (K : Type u) [Field K]

lemma TensorProduct.flip_mk_injective {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [NoZeroSMulDivisors R N] [Module.Flat R M] (a : N) (ha : a ≠ 0) :
    Function.Injective ((TensorProduct.mk R M N).flip a) := by
  intro x y e
  apply (TensorProduct.rid R M).symm.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := M) (LinearMap.toSpanSingleton R N a)
    (smul_left_injective R ha)
  simpa using e

lemma IsCentral.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Nontrivial B] [Nontrivial C] [Algebra K C] [Algebra K B]
    [FiniteDimensional K B] [hbc : Algebra.IsCentral K (B ⊗[K] C)] :
    Algebra.IsCentral K B := by
  letI : Nontrivial (B ⊗[K] C) := Module.FaithfullyFlat.lTensor_nontrivial _ _ _
  have h := (Subalgebra.equivOfEq (R := K) (A := B ⊗[K] C) _ _ <|
    hbc.center_eq_bot K (B ⊗[K] C)) |>.trans <| Algebra.botEquiv K (B ⊗[K] C)
  have : (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range ≤
    Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
    simp only [AlgHom.mem_range, AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Subtype.exists, exists_prop] at hx
    obtain ⟨b, hb0, hb⟩ := hx
    rw [Subalgebra.mem_center_iff] at hb0 ⊢
    intro bc
    induction bc using TensorProduct.induction_on with
    | zero => simp
    | tmul b' c =>
      subst hb
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      congr 1
      exact hb0 b'
    | add _ _ _ _ => simp_all [add_mul, mul_add]
  have eq: (Algebra.TensorProduct.includeLeft.comp (Subalgebra.center K B).val).range =
      (⊥ : Subalgebra K (B ⊗[K] C)) := by
    refine le_antisymm ?_ <| OrderBot.bot_le _
    rw [← hbc.center_eq_bot]; exact this
  let f : Subalgebra.center K B →ₐ[K] ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range := {
      toFun := fun ⟨b, hb⟩ ↦ ⟨b ⊗ₜ 1, ⟨⟨b, hb⟩, rfl⟩⟩
      map_one' := by simp; rfl
      map_mul' := fun _ _ ↦ by ext : 1; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_tmul]
      commutes' := fun _ ↦ rfl}
  have f_surj : Function.Surjective f := fun ⟨bc, ⟨⟨b, hb⟩, h⟩⟩ ↦ ⟨⟨b, hb⟩, by
    simp only [f, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Subtype.mk.injEq]
    change _ ⊗ₜ _ = _ at h
    simp only [RingHom.coe_coe, Subalgebra.coe_val] at h⊢
    exact h⟩
  have e : ((Algebra.TensorProduct.includeLeft (R := K) (B := C)).comp
    (Subalgebra.center K B).val).range ≃ₐ[K] (Subalgebra.center K B) :=
    (AlgEquiv.ofBijective f
    ⟨fun ⟨b1, hb1⟩ ⟨b2, hb2⟩ h12 ↦ by
      simp only [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Subtype.mk.injEq, f] at h12
      ext
      exact TensorProduct.flip_mk_injective _ one_ne_zero h12,
    f_surj⟩).symm
  have e2 := Subalgebra.equivOfEq _ _ eq |>.trans <| Algebra.botEquiv K _
  have ee: Subalgebra.center K B ≃ₐ[K] K := e.symm.trans e2
  exact ⟨le_of_eq <| Subalgebra.eq_of_le_of_finrank_eq (OrderBot.bot_le _)
    (by rw [ee.toLinearEquiv.finrank_eq, Subalgebra.finrank_bot, Module.finrank_self])|>.symm⟩

variable (A : Type u) [Ring A] [Algebra K A]

lemma Algebra.IsCentral_ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : Algebra.IsCentral K A) :  Algebra.IsCentral K B where
  out x hx := by
    obtain ⟨k, hk⟩ := hA.1 (show e.symm x ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hx ⊢
      exact fun x ↦ by simpa using congr(e.symm $(hx (e x))))
    exact ⟨k, by apply_fun e.symm; rw [← hk]; simp⟩

lemma IsSimpleRing.ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : IsSimpleRing A) : IsSimpleRing B :=
  ⟨OrderIso.isSimpleOrder_iff (TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv)|>.1 hA.1⟩

theorem IsAzumaya_iff_CentralSimple [Nontrivial A] : IsAzumaya K A ↔ FiniteDimensional K A ∧
    Algebra.IsCentral K A ∧ IsSimpleRing A :=
  ⟨fun ⟨bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank K A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨IsAzumaya.toFinite, ⟨by
    have : Algebra.IsCentral K (A ⊗[K] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv K _ _ e.symm <| Algebra.IsCentral.matrix K K
        (Fin (Module.finrank K A))
    exact IsCentral.left_of_tensor K A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank K A)) K
    have sim : IsSimpleRing (A ⊗[K] Aᵐᵒᵖ) := IsSimpleRing.ofAlgEquiv K _ _ e.symm this
    exact IsSimpleRing.left_of_tensor K A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ {
      out := Module.Projective.out
      eq_of_smul_eq_smul {k1} {k2} ha := by
        specialize ha (1 : A)
        rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at ha
        exact FaithfulSMul.algebraMap_injective _ _ ha
      fg_top := fin.1
      bij := bijective_of_dim_eq_of_isCentralSimple K _ _
        (AlgHom.mulLeftRight K A) <| tensorSelfOp.dim_eq _ _
    }⟩

/-- The canonical equivalence `Fin (n * m) ≃ Fin (m * n)` induced by commutativity. -/
def finswap {n m : ℕ} : Fin (n * m) ≃ Fin (m * n) where
  toFun i := ⟨i.1, by rw [mul_comm m n]; exact i.2⟩
  invFun i := ⟨i.1, by rw [mul_comm n m]; exact i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open ModuleCat in
lemma IsMorita_iff_IsBrauer' (R : Type u) [CommRing R] (A B : Type v) [Ring A] [Ring B]
    [IsSimpleRing A] [IsSimpleRing B] [IsArtinianRing A] [IsArtinianRing B] [Algebra R A]
    [Algebra R B] :
    IsMoritaEquivalent R A B ↔ ∃(n m : ℕ), n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <|
    Matrix (Fin n) (Fin n) A ≃ₐ[R] Matrix (Fin m) (Fin m) B) := ⟨fun hAB ↦
  by
    obtain ⟨n, hn, D, _, _, ⟨e⟩⟩ := WedderburnArtin_algebra_version' R A
    obtain ⟨m, hm, E, _, _, ⟨e'⟩⟩ := WedderburnArtin_algebra_version' R B
    letI e1 := MoritaEquivalence.ofAlgEquiv e
    letI e2 := MoritaEquivalence.ofAlgEquiv e'
    have : NeZero m := ⟨hm⟩
    have : NeZero n := ⟨hn⟩
    haveI := MoritaEquivalence.matrix' R D n |>.symm
    have ww := MoritaEquivalence.trans R e1 this |>.symm
    haveI := MoritaEquivalence.matrix' R E m |>.symm
    have ww' := MoritaEquivalence.trans R e2 this
    haveI h := MoritaEquivalence.trans R ww hAB.cond.some
    haveI h' := MoritaEquivalence.trans R h ww'
    have := MoritaEquivalence.algEquivOfDivisionRing R D E h'
    refine ⟨m, n, hm, hn, ⟨e.mapMatrix.trans <| Matrix.compAlgEquiv _ _ _ _ |>.trans <|
      Matrix.reindexAlgEquiv _ _ finProdFinEquiv |>.trans <| this.mapMatrix.trans <|
      Matrix.reindexAlgEquiv _ _ finswap|>.trans <| Matrix.reindexAlgEquiv _ _
      finProdFinEquiv.symm |>.trans <| Matrix.compAlgEquiv _ _ _ _|>.symm.trans
      e'.symm.mapMatrix⟩⟩,
  fun ⟨n, m, hn, hm, ⟨e⟩⟩ ↦
  letI : NeZero n := ⟨hn⟩
  letI : NeZero m := ⟨hm⟩
  ⟨⟨MoritaEquivalence.trans R (MoritaEquivalence.trans R
    (MoritaEquivalence.matrix' R A n) (MoritaEquivalence.ofAlgEquiv e))
      (MoritaEquivalence.matrix' R B m).symm⟩⟩⟩

open ModuleCat in
theorem IsMorita_iff_IsBrauer (A B : CSA.{u, v} K) :
    IsMoritaEquivalent K A B ↔ IsBrauerEquivalent (K := K) A B :=
  haveI : IsArtinianRing A := .of_finite K A
  haveI : IsArtinianRing B := .of_finite K B
  IsMorita_iff_IsBrauer' K A B

end Field

section Matrix

open scoped TensorProduct

variable (R : Type u) [CommRing R]

instance (n : ℕ) [NeZero n] : FaithfulSMul R (Matrix (Fin n) (Fin n) R) where
  eq_of_smul_eq_smul {r1 r2} h12 := by
    specialize h12 (1 : Matrix _ _ _)
    rw [← Matrix.ext_iff] at h12
    specialize h12 ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero _⟩
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h12
    exact h12

open MulOpposite in
/-- The matrix algebra is equivalent to its opposite algebra over the base ring. -/
abbrev matrixAlgEquivMatrixMop (n : ℕ) :
  Matrix (Fin n) (Fin n) R ≃ₐ[R] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
  (AlgEquiv.toOpposite R R).mapMatrix.trans <| AlgEquiv.ofRingEquiv
  (f := matrixEquivMatrixMop n R) <|
  fun r ↦ by
    simp only [matrixEquivMatrixMop_apply, MulOpposite.algebraMap_apply, op_inj]
    ext i j
    simp [Matrix.algebraMap_matrix_apply]
    split_ifs with h1 h2 h3 <;> tauto

/-- The opposite algebra of `R` identifies with the endomorphism algebra of `R` as a module. -/
noncomputable abbrev mopAlgEquivEnd : Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  AlgEquiv.ofRingEquiv (f := mopEquivEnd R) fun r ↦ by
    ext; simp [mopEquivEnd]

/-- The tensor product `R ⊗[R] Rᵐᵒᵖ` identifies with `Module.End R R`. -/
noncomputable abbrev tensorEquivEnd : R ⊗[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  Algebra.TensorProduct.lid R Rᵐᵒᵖ|>.trans <| mopAlgEquivEnd R

lemma equal_mulLeftRight : tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext r
  simp [mopEquivEnd, AlgHom.mulLeftRight_apply]

lemma bij_Rtensor : Function.Bijective (AlgHom.mulLeftRight R R) := by
  rw [← equal_mulLeftRight]
  exact (tensorEquivEnd R).bijective

instance : FaithfulSMul R R where
  eq_of_smul_eq_smul {r1 r2} hr := by
    specialize hr 1
    simp only [smul_eq_mul, mul_one] at hr
    exact hr

theorem IsAzumaya_R : IsAzumaya R R where
  bij := bij_Rtensor R

noncomputable section

open MulOpposite Matrix

/-- An explicit inverse to `AlgHom.mulLeftRight` for matrix algebras. -/
abbrev Mat.inv (n : ℕ) : Module.End R (Matrix (Fin n) (Fin n) R) →ₗ[R]
    Matrix (Fin n) (Fin n) R ⊗[R] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ where
  toFun := fun f ↦ ∑ ⟨⟨i, j⟩, k, l⟩ : (Fin n × Fin n) × Fin n × Fin n,
    f (single j k 1) i l • (single i j 1) ⊗ₜ[R] op (single k l 1)
  map_add' := fun f1 f2 ↦ by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := fun r f ↦ by
    simp [SemigroupAction.mul_smul, Finset.smul_sum]

lemma single.eq (n : ℕ) (i j : Fin n) :
    single i j (1 : R) = of (fun i' j' ↦ if i = i' ∧ j = j' then 1 else 0) := rfl

lemma Mat.inv_toFun1' (n : ℕ) :
    (Mat.inv R n).comp (AlgHom.mulLeftRight R (Matrix (Fin n) (Fin n) R)).toLinearMap = .id :=
  Basis.ext ((Matrix.stdBasis _ _ _).tensorProduct ((Matrix.stdBasis _ _ _).map (opLinearEquiv ..)))
  fun ⟨⟨i0, j0⟩, k0, l0⟩ ↦  by
    simp [stdBasis_eq_single, AlgHom.mulLeftRight_apply,
      single, ite_and, mul_apply, Fintype.sum_prod_type]

lemma Mat.inv_toFun2' (n : ℕ) :
    (AlgHom.mulLeftRight R (Matrix (Fin n) (Fin n) R)).toLinearMap.comp (Mat.inv R n) = .id := by
  ext f : 1
  apply Basis.ext (Matrix.stdBasis _ _ _)
  intro ⟨i, j⟩
  simp only [LinearMap.coe_comp, AlgHom.coe_toLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, map_sum, map_smul, LinearMap.coe_sum, LinearMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, AlgHom.mulLeftRight_apply, unop_op, single_mul_mul_single,
    one_mul, mul_one, smul_single, smul_eq_mul, LinearMap.id_coe, id_eq, stdBasis_eq_single]
  ext k l
  simp [Matrix.sum_apply, single, Fintype.sum_prod_type, ite_and]

lemma Mat.bij (n : ℕ) : Function.Bijective (AlgHom.mulLeftRight R (Matrix (Fin n) (Fin n) R)) :=
  ⟨Function.HasLeftInverse.injective ⟨Mat.inv R n, DFunLike.congr_fun (Mat.inv_toFun1' R n)⟩,
  Function.HasRightInverse.surjective ⟨Mat.inv R n, DFunLike.congr_fun (Mat.inv_toFun2' R n)⟩⟩

end

instance (n : ℕ) [NeZero n] : FaithfulSMul R (Matrix (Fin n) (Fin n) R) where
  eq_of_smul_eq_smul {r1 r2} h := by
    specialize h 1
    rw [← Matrix.ext_iff] at h
    specialize h ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    exact h

end Matrix
