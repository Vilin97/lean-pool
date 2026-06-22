/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import LeanPool.BrauerGroupNew.CentralSimple
import LeanPool.BrauerGroupNew.FieldCat
import LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# LeanPool.BrauerGroupNew.BrauerGroup

Imported Lean Pool material for `LeanPool.BrauerGroupNew.BrauerGroup`.
-/

suppress_compilation
universe u v v₁ v₂ w

variable (K : Type u) [Field K]
variable (A B : Type u) [Ring A] [Ring B] [Algebra K A] [Algebra K B]

open scoped TensorProduct

lemma bijective_of_dim_eq_of_isCentralSimple
    [csa_source : IsSimpleRing A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : Module.finrank K A = Module.finrank K B) :
    Function.Bijective f := by
  obtain hA|hA := subsingleton_or_nontrivial A
  · have eq1 : Module.finrank K A = 0 := by
      rw [finrank_zero_iff_forall_zero]
      intro x
      apply Subsingleton.elim
    rw [eq1] at h
    replace h : Subsingleton B := by
      constructor
      symm at h
      rw [finrank_zero_iff_forall_zero] at h
      intro a b
      rw [h a, h b]
    rw [Function.bijective_iff_existsUnique]
    intro b
    refine ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · have := IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain A |>.1 csa_source
      f.toRingHom
    rcases this with (H|H)
    · refine ⟨H, ?_⟩
      change Function.Surjective f.toLinearMap
      have := f.toLinearMap.finrank_range_add_finrank_ker
      rw [show Module.finrank K (LinearMap.ker f.toLinearMap) = 0 by
        rw [finrank_zero_iff_forall_zero]
        rintro ⟨x, hx⟩
        rw [LinearMap.ker_eq_bot (f := f.toLinearMap) |>.2 H] at hx
        ext
        exact hx, add_zero, h] at this
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      exact this
    · have : (1 : A) ∈ TwoSidedIdeal.ker f.toRingHom := by
        simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, map_one]
        exact Subsingleton.elim _ _
      simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, map_one] at this
      have hmm : Nontrivial B := by
        let e := LinearEquiv.ofFinrankEq _ _ h
        exact Equiv.nontrivial e.symm.toEquiv
      exact one_ne_zero this |>.elim

lemma bijective_of_surj_of_isCentralSimple
    [csa_source : IsSimpleRing A]
    (f : A →ₐ[K] B) [Nontrivial B] (h : Function.Surjective f) :
    Function.Bijective f :=
  ⟨IsSimpleRing.iff_injective_ringHom A |>.1 inferInstance f.toRingHom, h⟩
-- instance tensor_CSA_is_CSA
--     [Algebra.IsCentral K A] [hA : IsSimpleRing A]
--     [Algebra.IsCentral K B] [hB: IsSimpleRing B] :
--     IsSimpleRing (A ⊗[K] B) := inferInstance
  --  is_central := IsCentralSimple.TensorProduct.isCentral K A B hA.is_central hB.is_central
  --  simple := IsCentralSimple.TensorProduct.simple K A B

instance CSA_op_is_CSA [hA : Algebra.IsCentral K A] : Algebra.IsCentral K Aᵐᵒᵖ where
  out z hz:= by
    let z': A := z.unop
    have hz' : ∀ (x : A), x * z' = z' * x := by
      rw [Subalgebra.mem_center_iff] at hz
      intro x; specialize hz (MulOpposite.op x)
      have z'_eq : MulOpposite.op z'= z := rfl
      rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
      have : (MulOpposite.op (z' * x)).unop = z' * x := rfl
      simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
          MulOpposite.unop_op, z']
    obtain ⟨k, hk⟩ := hA.out <| Subalgebra.mem_center_iff.mpr hz'
    exact ⟨k, MulOpposite.unop_inj.mp hk⟩
  -- is_simple := @op_simple A _ hA.is_simple

-- instance [IsSimpleRing A] : IsSimpleRing Aᵐᵒᵖ := @op_simple A _ _

namespace tensorSelfOp

variable [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A]

instance st : IsScalarTower K K (Module.End K A) where
  smul_assoc k₁ k₂ f := DFunLike.ext _ _ fun a ↦ by
    change (k₁ * k₂) • f a = k₁ • (k₂ • f a)
    rw [mul_smul]
/-- The action map from `A ⊗ Aᵐᵒᵖ` to endomorphisms of `A`. -/
def toEnd : A ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  Algebra.TensorProduct.lift
    { toFun a :=
        { toFun x := a * x
          map_add' := mul_add _
          map_smul' := by simp }
      map_one' := by aesop
      map_mul' := by intros; ext; simp [mul_assoc]
      map_zero' := by aesop
      map_add' := by intros; ext; simp [add_mul]
      commutes' k := DFunLike.ext _ _ fun a ↦ show (algebraMap K A) k * a = k • _ from
        (Algebra.smul_def _ _).symm }
    { toFun a :=
        { toFun x := x * a.unop
          map_add' := fun x y => by simp [add_mul]
          map_smul' := by simp }
      map_one' := by aesop
      map_mul' := by intros; ext; simp [mul_assoc]
      map_zero' := by aesop
      map_add' := by intros; ext; simp [mul_add]
      commutes' k := DFunLike.ext _ _ fun a ↦
        show a * (algebraMap K A) k = k • _ by
          rw [Algebra.smul_def, Algebra.commutes]
          rfl }
    fun a a' => show _ = _ from DFunLike.ext _ _ fun x ↦ show a * (x * a'.unop) = a * x * a'.unop
      from mul_assoc _ _ _ |>.symm

-- instance : Algebra.IsCentral K Aᵐᵒᵖ := inferInstance -- CSA_op_is_CSA K A inferInstance
instance : FiniteDimensional K Aᵐᵒᵖ := LinearEquiv.finiteDimensional
  (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ)

instance fin_end : FiniteDimensional K (Module.End K A) :=
  LinearMap.finiteDimensional

omit [Algebra.IsCentral K A] hA in
lemma dim_eq :
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct]
  rw [show Module.finrank K (Module.End K A) =
    Module.finrank K (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) from
    (algEquivMatrix <| Module.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin]
  rw [show Module.finrank K Aᵐᵒᵖ = Module.finrank K A from
    (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]
  simp only [Module.finrank_self, mul_one]

/-- The central simple algebra isomorphism `A ⊗ Aᵐᵒᵖ ≃ End_K(A)`. -/
def equivEnd : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (toEnd K A) <| bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <|
    dim_eq K A

end tensorSelfOp

open tensorSelfOp in
/-- Identifies `A ⊗ Aᵐᵒᵖ` with a full matrix algebra over the base field. -/
def tensorSelfOp
    [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A] :
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K]
    (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) :=
  equivEnd K A |>.trans <| algEquivMatrix <| Module.finBasis _ _

/-- Identifies `Aᵐᵒᵖ ⊗ A` with a full matrix algebra over the base field. -/
def tensorOpSelf
    [Algebra.IsCentral K A] [hA : IsSimpleRing A] [FiniteDimensional K A] :
    Aᵐᵒᵖ ⊗[K] A ≃ₐ[K]
    (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) :=
  (Algebra.TensorProduct.comm _ _ _).trans <| tensorSelfOp _ _

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/

variable {K : Type u} [Field K]

namespace IsBrauerEquivalent

/-- Reindexes matrices over `Fin n × Fin m` as matrices over `Fin (n * m)`. -/
def matrixEqv' (n m : ℕ) (A : Type*) [Ring A] [Algebra K A] :
    (Matrix (Fin n × Fin m) (Fin n × Fin m) A) ≃ₐ[K] Matrix (Fin (n * m)) (Fin (n * m)) A :=
{ Matrix.reindexLinearEquiv K A finProdFinEquiv finProdFinEquiv with
  toFun := Matrix.reindex finProdFinEquiv finProdFinEquiv
  map_mul' := fun m n ↦ by simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  commutes' := fun k ↦ by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finProdFinEquiv_symm_apply,
      Matrix.algebraMap_matrix_apply, Prod.mk.injEq]
    if h : i = j then aesop
    else
    simp only [h, ↓reduceIte, ite_eq_right_iff, and_imp]
    intro h1 h2
    have : i = j := by
      have : (⟨i.divNat, i.modNat⟩ : Fin n × Fin m) = ⟨j.divNat, j.modNat⟩ := Prod.ext h1 h2
      apply_fun finProdFinEquiv at this
      rw [show ⟨i.divNat, i.modNat⟩ = finProdFinEquiv.symm i by rfl,
        show ⟨j.divNat, _⟩ = finProdFinEquiv.symm j by rfl,
        finProdFinEquiv.apply_symm_apply, finProdFinEquiv.apply_symm_apply] at this
      exact this
    tauto
}

lemma iso_to_eqv (A B : CSA K) (h : A ≃ₐ[K] B) : IsBrauerEquivalent A B :=
    ⟨1, 1, one_ne_zero, one_ne_zero, ⟨h.mapMatrix (m := (Fin 1))⟩⟩

theorem Braur_is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  refl := refl
  symm := symm
  trans := trans

end IsBrauerEquivalent

namespace BrauerGroup

/-- The setoid on central simple algebras generated by Brauer equivalence. -/
@[implicit_reducible]
def CSASetoid : Setoid (CSA K) where
  r := IsBrauerEquivalent
  iseqv := IsBrauerEquivalent.Braur_is_eqv

/-- Tensor-product multiplication on representatives of the Brauer group. -/
def mul (A B : CSA K) : CSA K where
  toAlgCat := .of K (A ⊗[K] B)
  fin_dim := Module.Finite.tensorProduct K A B

/-- Finite-dimensionality is preserved by passing to the opposite algebra. -/
theorem isFinDimOfMop (A : Type*) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    FiniteDimensional K Aᵐᵒᵖ := by
  have f:= MulOpposite.opLinearEquiv K (M:= A)
  exact Module.Finite.equiv f
    -- Module.Finite.of_surjective f (LinearEquiv.surjective _)

/-- The opposite algebra representative used for inversion in the Brauer group. -/
def inv (A : CSA K) : CSA K := {
  __ := AlgCat.of K Aᵐᵒᵖ
  fin_dim := isFinDimOfMop A }

/-- The matrix algebra representative of the identity Brauer class. -/
def oneIn (n : ℕ) [hn : NeZero n] : CSA K := ⟨.of K (Matrix (Fin n) (Fin n) K)⟩

/-- The base field representative of the identity Brauer class. -/
def oneIn' : CSA K := ⟨.of K K⟩

/-- Right tensoring by an identity matrix algebra representative. -/
def oneMulIn (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  ⟨.of K (A ⊗[K] (Matrix (Fin n) (Fin n) K))⟩

/-- Left tensoring by an identity matrix algebra representative. -/
def mulOneIn (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  ⟨.of K ((Matrix (Fin n) (Fin n) K) ⊗[K] A)⟩

/-- Transports a central simple algebra structure across an algebra equivalence. -/
def eqvIn (A : CSA K) (A' : Type*) [Ring A'] [Algebra K A'] (e : A ≃ₐ[K] A') : CSA K where
  toAlgCat := .of K A'
  isCentral := AlgEquiv.isCentral e
  isSimple := ⟨TwoSidedIdeal.orderIsoOfRingEquiv e.toRingEquiv.symm |>.isSimpleOrder⟩
  fin_dim := LinearEquiv.finiteDimensional e.toLinearEquiv

/-- The representative obtained by replacing `A ⊗ Mₙ(K)` with `Mₙ(A)`. -/
def matrixA (n : ℕ) [hn : NeZero n] (A : CSA K) : CSA K :=
  eqvIn (oneMulIn n A) (Matrix (Fin n) (Fin n) A) <|
    by unfold oneMulIn; exact matrixEquivTensor _ K A |>.symm

/-- The standard scalar action on `1 × 1` matrices. -/
@[implicit_reducible]
def dim_1 (R : Type*) [Ring R] [Algebra K R] : Algebra K (Matrix (Fin 1) (Fin 1) R) where
  algebraMap.toFun k := Matrix.diagonal fun _ => Algebra.ofId K R k
  algebraMap.map_one' := by simp only [map_one, Matrix.diagonal_one]
  algebraMap.map_mul' := by simp only [map_mul, Matrix.diagonal_mul_diagonal, implies_true]
  algebraMap.map_zero' := by simp only [map_zero, Matrix.diagonal_zero]
  algebraMap.map_add' := by simp only [map_add, Matrix.diagonal_add, implies_true]
  commutes' r m := by ext i j; fin_cases i; fin_cases j; simp only [RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Fin.zero_eta, Fin.isValue, Matrix.diagonal_mul,
    Matrix.mul_diagonal]; exact Algebra.commutes r (m 0 0)
  smul_def' r m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.zero_eta, Fin.isValue,
    Matrix.smul_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.diagonal_mul,
    Algebra.smul_def]; rfl

/-- The algebra equivalence between `1 × 1` matrices and the coefficient algebra. -/
def dimOneIso (R : Type*) [Ring R] [Algebra K R] : (Matrix (Fin 1) (Fin 1) R) ≃ₐ[K] R where
  toFun m := m 0 0
  invFun r := Matrix.diagonal fun _ => r
  left_inv m := by ext i j; fin_cases i; fin_cases j; simp only [Fin.isValue, Fin.zero_eta,
    Matrix.diagonal_apply_eq]
  right_inv r := by simp only [Fin.isValue, Matrix.diagonal_apply_eq]
  map_mul' m n := by
    simp only [Fin.isValue, Matrix.mul_apply]
    exact Fin.sum_univ_one fun i ↦ m 0 i * n i 0
  map_add' m n := by simp only [Fin.isValue, Matrix.add_apply]
  commutes' r := by
    simp only [Fin.isValue, Algebra.algebraMap_eq_smul_one']
    rw [Matrix.smul_apply]; rfl

open IsBrauerEquivalent

theorem eqv_mat (A : CSA K) (n : ℕ) [hn : NeZero n] : IsBrauerEquivalent A (matrixA n A) := by
  refine ⟨n, 1, hn.1, one_ne_zero, ?_⟩
  unfold matrixA oneMulIn eqvIn
  exact ⟨dimOneIso _ |>.symm⟩

/-- The Kronecker product algebra homomorphism on square matrices. -/
def matrixEquivForward (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m K ⊗[K] Matrix n n K →ₐ[K] Matrix (m × n) (m × n) K :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.lift Matrix.kroneckerBilinear)
    (fun _ _ _ _ => Matrix.mul_kronecker_mul _ _ _ _)
    (Matrix.one_kronecker_one (α := K))

open scoped Kronecker in
lemma matrixEquivForward_tmul (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m m K) (N : Matrix n n K) : matrixEquivForward m n (M ⊗ₜ N) = M ⊗ₖ N := rfl

lemma matrixEquivForward_surjective
    (n m : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Function.Surjective <| matrixEquivForward (K := K) m n := by
  intro x
  rw [Matrix.matrix_eq_sum_single x]
  suffices H :
      ∀ (i j : m × n), ∃ a, (matrixEquivForward m n) a = Matrix.single i j (x i j) by
    choose a ha using H
    use ∑ i : m × n, ∑ j : m × n, a i j
    rw [map_sum]
    simp_rw [map_sum]
    simp_rw [ha]
  intro i j
  rw [show Matrix.single i j (x i j) = (x i j) • Matrix.single i j 1 by
    rw [Matrix.smul_single, Algebra.smul_def,  mul_one]
    rfl]
  use (x i j) • ((Matrix.single i.1 j.1 1) ⊗ₜ (Matrix.single i.2 j.2 1))
  rw [_root_.map_smul (f := (matrixEquivForward (K := K) m n)) (x i j)]
  congr 1
  simp only [matrixEquivForward, Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply,
    TensorProduct.lift.tmul]
  ext a b
  erw [Matrix.kroneckerMapBilinear_apply_apply]
  erw [Matrix.kroneckerMap_apply]
  erw [Algebra.coe_lmul_eq_mul]
  rw [LinearMap.mul]
  simp only [LinearMap.mk₂_apply]
  simp only [Matrix.single, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · simp only [not_and, ne_eq] at h3
    refine h3 ?_ ?_ |>.elim <;> ext <;> aesop
  · simp only [not_and] at h2
    refine h2 ?_ ?_ |>.elim <;> aesop
  · rfl
  · simp only [not_and] at h1
    refine h1 ?_ ?_ |>.elim <;> aesop
  · rfl

/-- The tensor product of matrix algebras is a matrix algebra on the product index type. -/
def matrixEqv (m n : ℕ) : (Matrix (Fin m) (Fin m) K) ⊗[K] (Matrix (Fin n) (Fin n) K) ≃ₐ[K]
    Matrix (Fin m × Fin n) (Fin m × Fin n) K :=
  .ofBijective (matrixEquivForward (Fin m) (Fin n)) <| by
    if h : n = 0 ∨ m = 0
    then
      rcases h with h|h <;>
      subst h <;>
      refine ⟨?_, matrixEquivForward_surjective _ _⟩ <;>
      intro x y _ <;>
      apply Subsingleton.elim
    else
    have : Nonempty (Fin n) := ⟨0, by omega⟩
    have : Nonempty (Fin m) := ⟨0, by omega⟩
    apply bijective_of_surj_of_isCentralSimple
    apply matrixEquivForward_surjective

lemma one_mul (n : ℕ) [hn : NeZero n] (A : CSA K) :
    IsBrauerEquivalent A (oneMulIn n A) :=
  ⟨n, 1, hn.1, one_ne_zero, ⟨.symm <| (dimOneIso _).trans <| matrixEquivTensor _ _ _ |>.symm⟩⟩

lemma mul_one (n : ℕ) [hn : NeZero n] (A : CSA K) :
    IsBrauerEquivalent A (mulOneIn n A) :=
  ⟨n, 1, hn.1, one_ne_zero, ⟨.symm <| (dimOneIso _).trans <| .symm <|
    matrixEquivTensor _ _ _ |>.trans <| Algebra.TensorProduct.comm _ _ _⟩⟩

lemma mul_assoc (A B C : CSA K) :
    IsBrauerEquivalent (mul (mul A B) C) (mul A (mul B C)) :=
  IsBrauerEquivalent.iso_to_eqv (K := K) _ _ <| Algebra.TensorProduct.assoc ..

/-- Kronecker-style equivalence for tensor products of matrix algebras over two algebras. -/
def kroneckerMatrixTensor' (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] (n m : ℕ) :
      (Matrix (Fin n) (Fin n) A) ⊗[K] (Matrix (Fin m) (Fin m) B) ≃ₐ[K]
      (Matrix (Fin (n*m)) (Fin (n*m)) (A ⊗[K] B)) :=
  .trans (Algebra.TensorProduct.congr (matrixEquivTensor (Fin n) K A) <|
    matrixEquivTensor (Fin m) K B) <| (Algebra.TensorProduct.tensorTensorTensorComm ..).trans <|
      .trans
    (Algebra.TensorProduct.congr .refl <| (matrixEqv ..).trans <| matrixEqv' ..)
    (matrixEquivTensor ..).symm

theorem eqv_tensor_eqv
    (A B C D : CSA K) (hAB : IsBrauerEquivalent A B) (hCD : IsBrauerEquivalent C D) :
    IsBrauerEquivalent (mul A C) (mul B D) := by
  obtain ⟨n, m, hn, hm, ⟨e1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨e2⟩⟩ := hCD
  exact ⟨n * p, m * q, by simp_all, by simp_all, ⟨
    (kroneckerMatrixTensor' (K := K) A C n p).symm.trans <|
      (Algebra.TensorProduct.congr e1 e2).trans <|
        kroneckerMatrixTensor' (K := K) B D m q⟩⟩

instance Mul : Mul <| BrauerGroup (K := K) :=
  ⟨Quotient.lift₂ (fun A B ↦ Quotient.mk (CSASetoid) <| BrauerGroup.mul A B)
  (by
    simp only [Quotient.eq]
    intro A B C D hAB hCD
    change IsBrauerEquivalent (mul A B) (mul C D)
    exact eqv_tensor_eqv A C B D hAB hCD)⟩

instance One : One (BrauerGroup (K := K)) := ⟨Quotient.mk (CSASetoid) oneIn'⟩

theorem mul_assoc' (A B C : BrauerGroup (K := K)) : A * B * C = A * (B * C) := by
  induction A using Quotient.inductionOn' with | h A
  induction B using Quotient.inductionOn' with | h B
  induction C using Quotient.inductionOn' with | h C
  apply Quotient.sound; exact mul_assoc _ _ _

lemma mul_inv (A : CSA.{u, u} K) : IsBrauerEquivalent (mul A (inv (K := K) A)) oneIn' := by
  unfold mul inv oneIn'
  let n := Module.finrank K A
  have hn : NeZero n := by
    constructor
    by_contra! hn
    simp only [n] at hn
    have := Module.finrank_pos_iff (R := K) (M := A) |>.2 inferInstance
    omega
  have := tensorSelfOp K A
  exact ⟨1, n, one_ne_zero, hn.1, ⟨dimOneIso _|>.trans this⟩⟩

lemma inv_mul (A : CSA.{u, u} K) : IsBrauerEquivalent (mul (inv (K := K) A) A) oneIn' := by
  unfold mul inv oneIn'
  let n := Module.finrank K A
  have hn : NeZero n := by
    constructor
    by_contra! hn
    simp only [n] at hn
    have := Module.finrank_pos_iff (R := K) (M := A) |>.2 inferInstance
    omega
  have := tensorOpSelf K A
  exact ⟨1, n, one_ne_zero, hn.1, ⟨dimOneIso _|>.trans this⟩⟩

variable (K R : Type*) [CommSemiring K] [Semiring R] [Algebra K R] in
open Matrix MulOpposite in
/-- Mn(Rᵒᵖ) ≃ₐ[K] Mₙ(R)ᵒᵖ -/
def matrixEquivMatrixMopAlgebra (n : ℕ) :
    Matrix (Fin n) (Fin n) Rᵐᵒᵖ ≃ₐ[K] (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ where
  toFun M := op (M.transpose.map (fun d => d.unop))
  invFun M := M.unop.transpose.map (fun d => op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective <| by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop
  commutes' k := by
    simp only [MulOpposite.algebraMap_apply, op_inj]; ext i j
    simp only [map_apply, transpose_apply, algebraMap_matrix_apply]
    if h : i = j then simp only [h, ↓reduceIte, MulOpposite.algebraMap_apply, unop_op]
    else simp only [MulOpposite.algebraMap_apply, h, ↓reduceIte, unop_eq_zero_iff, ite_eq_right_iff,
      op_eq_zero_iff]; tauto

lemma inv_eqv (A B : CSA K) (hAB : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (inv (K := K) A) (inv (K := K) B) := by
  unfold inv
  obtain ⟨n, m, hn, hm, ⟨iso⟩⟩ := hAB
  refine ⟨n, m, hn, hm, ⟨(matrixEquivMatrixMopAlgebra _ _ _).trans <|
    (AlgEquiv.op iso).trans (matrixEquivMatrixMopAlgebra _ _ _).symm⟩⟩

instance Inv : Inv (BrauerGroup (K := K)) where
  inv := Quotient.lift (fun A ↦ Quotient.mk (CSASetoid) <| inv A) fun A B hAB ↦ by
    change IsBrauerEquivalent _ _ at hAB
    exact Quotient.sound (inv_eqv (K := K) A B hAB)

theorem mul_left_inv' (A : BrauerGroup (K := K)) : A⁻¹ * A = 1 := by
  induction A using Quotient.inductionOn' with | h A
  change _ = Quotient.mk'' oneIn'
  apply Quotient.sound; exact inv_mul A

theorem one_mul' (A : BrauerGroup (K := K)) : 1 * A = A := by
  induction A using Quotient.inductionOn' with | h A
  change Quotient.mk'' oneIn' * _ = _; apply Quotient.sound
  exact iso_to_eqv _ _ (Algebra.TensorProduct.lid K A)

theorem mul_one' (A : BrauerGroup (K := K)) : A * 1 = A := by
  induction A using Quotient.inductionOn' with | h A
  change _ * Quotient.mk'' oneIn' = _; apply Quotient.sound
  exact iso_to_eqv _ _ (Algebra.TensorProduct.rid K K A)

instance BruaerGroup : Group (BrauerGroup (K := K)) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := mul_left_inv'

lemma Alg_closed_equiv_one [IsAlgClosed K] : ∀(A : CSA K), IsBrauerEquivalent A oneIn' := by
  intro A
  obtain ⟨n, hn, ⟨iso⟩⟩ := simple_eq_matrix_algClosed K A
  exact ⟨1, n, one_ne_zero, hn, ⟨dimOneIso A|>.trans iso⟩⟩

lemma Alg_closed_eq_one [IsAlgClosed K] : ∀(A : BrauerGroup (K := K)), A = 1 := by
  intro A; induction A using Quotient.inductionOn' with | h A
  change _ = Quotient.mk'' oneIn'; apply Quotient.sound
  change IsBrauerEquivalent _ _; exact Alg_closed_equiv_one A

instance instUniqueOfIsAlgClosedLeanPool [IsAlgClosed K] : Unique (BrauerGroup (K := K)) where
  default := 1
  uniq := Alg_closed_eq_one

theorem Alg_closed_Brauer_trivial [IsAlgClosed K] : (⊤ : Subgroup (BrauerGroup K)) =
    (⊥ : Subgroup <| BrauerGroup (K := K)) :=
  Subgroup.ext fun _ ↦ ⟨fun _ ↦ Alg_closed_eq_one _, fun _ ↦ ⟨⟩⟩

end BrauerGroup

namespace BrauerGroupHom

open BrauerGroup
variable {E : Type u} [Field E] [Algebra K E]

namespace someEquivs

variable (A B : Type u) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
variable (m : ℕ)

/-- The linear equivalence underlying compatibility of scalar extension with tensor products. -/
def baseChangeTensorLinear :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₗ[E] E ⊗[K] (A ⊗[K] B) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange K E E (E ⊗[K] A) B ≪≫ₗ
    (Algebra.TensorProduct.assoc K K E E A B).toLinearEquiv

/-- Evaluates the scalar-extension tensor compatibility equivalence on pure tensors. -/
theorem baseChangeTensorLinear_tmul (e e' : E) (a : A) (b : B) :
    baseChangeTensorLinear (K := K) (E := E) A B ((e ⊗ₜ[K] a) ⊗ₜ[E] (e' ⊗ₜ[K] b)) =
      (e * e') ⊗ₜ[K] (a ⊗ₜ[K] b) := by
  simp [baseChangeTensorLinear, Algebra.smul_def, mul_comm]

/-- Scalar extension is compatible with tensor products of algebras. -/
def baseChangeTensorEquiv :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  AlgEquiv.ofLinearEquiv (baseChangeTensorLinear (K := K) (E := E) A B)
    (by simp [baseChangeTensorLinear, Algebra.TensorProduct.one_def])
    (by
      let f := baseChangeTensorLinear (K := K) (E := E) A B
      apply LinearMap.map_mul_of_map_mul_tmul
      intro x1 x2 y1 y2
      change f ((x1 * x2) ⊗ₜ[E] (y1 * y2)) = f (x1 ⊗ₜ[E] y1) * f (x2 ⊗ₜ[E] y2)
      induction x1 using TensorProduct.induction_on with
      | zero =>
        simp only [zero_mul, TensorProduct.zero_tmul, f.map_zero]
      | add x1 x1' hx hx' =>
        simp only [add_mul, TensorProduct.add_tmul, f.map_add, hx, hx', add_mul]
      | tmul e1 a1 =>
      induction x2 using TensorProduct.induction_on with
      | zero =>
        simp only [mul_zero, TensorProduct.zero_tmul, f.map_zero]
      | add x2 x2' hx hx' =>
        simp only [mul_add, TensorProduct.add_tmul, f.map_add, hx, hx', mul_add]
      | tmul e2 a2 =>
      induction y1 using TensorProduct.induction_on with
      | zero =>
        simp only [zero_mul, TensorProduct.tmul_zero, f.map_zero]
      | add y1 y1' hy hy' =>
        simp only [add_mul, TensorProduct.tmul_add, f.map_add, hy, hy', add_mul]
      | tmul e3 b1 =>
      induction y2 using TensorProduct.induction_on with
      | zero =>
        simp only [mul_zero, TensorProduct.tmul_zero, f.map_zero]
      | add y2 y2' hy hy' =>
        simp only [mul_add, TensorProduct.tmul_add, f.map_add, hy, hy', mul_add]
      | tmul e4 b2 =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        rw [show f (((e1 * e2) ⊗ₜ[K] (a1 * a2)) ⊗ₜ[E]
            ((e3 * e4) ⊗ₜ[K] (b1 * b2))) =
            ((e1 * e2) * (e3 * e4)) ⊗ₜ[K] ((a1 * a2) ⊗ₜ[K] (b1 * b2)) from
          baseChangeTensorLinear_tmul (K := K) (E := E) A B (e1 * e2) (e3 * e4)
            (a1 * a2) (b1 * b2)]
        rw [show f ((e1 ⊗ₜ[K] a1) ⊗ₜ[E] (e3 ⊗ₜ[K] b1)) =
            (e1 * e3) ⊗ₜ[K] (a1 ⊗ₜ[K] b1) from
          baseChangeTensorLinear_tmul (K := K) (E := E) A B e1 e3 a1 b1]
        rw [show f ((e2 ⊗ₜ[K] a2) ⊗ₜ[E] (e4 ⊗ₜ[K] b2)) =
            (e2 * e4) ⊗ₜ[K] (a2 ⊗ₜ[K] b2) from
          baseChangeTensorLinear_tmul (K := K) (E := E) A B e2 e4 a2 b2]
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        ring_nf)

/-- If the matrix index is empty, the scalar-extension tensor source is subsingleton. -/
lemma e3Aux3 (hm : m = 0) :
    Subsingleton ((E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K)) := by
  suffices ∀ a : (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K), a = 0 by
    exact ⟨fun a b => by rw [this a, this b]⟩
  subst hm
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | add e a he ha => rw [he, ha, zero_add]
  | tmul e a =>
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add _ _ hx hy => rw [TensorProduct.tmul_add, hx, hy, add_zero]
    | tmul e' mat =>
      rw [show mat = 0 from Subsingleton.elim _ _]
      simp

/-- The algebra homomorphism underlying `e3`. -/
def e3Aux4 :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) →ₐ[E]
      E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  (baseChangeTensorEquiv A (Matrix (Fin m) (Fin m) K)).toAlgHom

/-- The algebra homomorphism underlying `e3` is surjective. -/
lemma e3Aux5 : Function.Surjective (e3Aux4 (K := K) (E := E) A m) :=
  (baseChangeTensorEquiv A (Matrix (Fin m) (Fin m) K)).surjective

/-- Rewrites matrices over a scalar extension as a tensor product with matrices over the
extension. -/
def e1 : Matrix (Fin m) (Fin m) (E ⊗[K] A) ≃ₐ[E] (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E :=
  matrixEquivTensor (Fin m) E (E ⊗[K] A)

/-- Replaces matrices over the extension field by scalar extension of matrices over `K`. -/
def e2 :
    (E ⊗[K] A) ⊗[E] Matrix (Fin m) (Fin m) E ≃ₐ[E]
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) :=
  Algebra.TensorProduct.congr .refl <|
    { __ := matrixEquivTensor (Fin m) K E
      commutes' e := by
        simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          matrixEquivTensor_apply, Fintype.sum_prod_type,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        simp_rw [Matrix.algebraMap_eq_diagonal]
        simp_rw [Matrix.diagonal_apply]
        simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [show
          ∑ x : Fin m, ∑ y : Fin m,
            (if x = y then e else 0) ⊗ₜ[K] Matrix.single x y (1 : K) =
          ∑ x : Fin m, e ⊗ₜ[K] Matrix.single x x 1 by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [show e ⊗ₜ[K] Matrix.single x x (1 : K) =
              (if x = x then e else 0) ⊗ₜ Matrix.single x x (1 : K) by aesop]
            apply Finset.sum_eq_single
            · aesop
            · aesop]
        rw [← TensorProduct.tmul_sum]
        congr 1
        ext i j
        rw [Matrix.sum_apply]
        by_cases h : i = j
        · subst h; simp [Matrix.single]
        · rw [Matrix.one_apply_ne h]
          apply Finset.sum_eq_zero
          intros k
          simp only [Finset.mem_univ, Matrix.single, Matrix.of_apply, ite_eq_right_iff,
            one_ne_zero, imp_false, not_and, forall_const]
          rintro rfl
          exact h }

/-- Reassociates a tensor product after base change along `K → E`. -/
def e3 :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) :=
  baseChangeTensorEquiv A (Matrix (Fin m) (Fin m) K)

/-- Applies the matrix-tensor equivalence inside a scalar extension. -/
def e4 :
    E ⊗[K] (A ⊗[K] Matrix (Fin m) (Fin m) K) ≃ₐ[E]
    E ⊗[K] (Matrix (Fin m) (Fin m) A) :=
  Algebra.TensorProduct.congr AlgEquiv.refl <| (matrixEquivTensor (Fin m) K A).symm

/-- Extends an algebra equivalence by scalars from `K` to `E`. -/
def e5 (e : A ≃ₐ[K] B) : (E ⊗[K] A) ≃ₐ[E] (E ⊗[K] B) :=
  Algebra.TensorProduct.congr AlgEquiv.refl e

/-- The algebra homomorphism underlying scalar-extension compatibility with tensor products. -/
def e6Aux0 : (E ⊗[K] A) ⊗[E] (E ⊗[K] B) →ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift
      { toFun e := e ⊗ₜ[K] (1 ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' e := rfl }
      { toFun a := 1 ⊗ₜ[K] (a ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun _ _ => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
        commutes' k := by
          rw [Algebra.algebraMap_eq_smul_one (R := K) (A := E ⊗[K] (A ⊗[K] B)),
            Algebra.algebraMap_eq_smul_one (R := K) (A := A)]
          rw [TensorProduct.smul_tmul (R := K), TensorProduct.tmul_smul,
            TensorProduct.tmul_smul, Algebra.TensorProduct.one_def,
            Algebra.TensorProduct.one_def] } fun e a =>
            show (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) = (_ ⊗ₜ[K] _) * (_ ⊗ₜ[K] _) by simp)
    (Algebra.TensorProduct.lift
      { toFun e := e ⊗ₜ[K] (1 ⊗ₜ 1)
        map_one' := rfl
        map_mul' := fun e e' => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun e e' => by simp [TensorProduct.add_tmul]
        commutes' e := rfl }
      { toFun b := 1 ⊗ₜ[K] (1 ⊗ₜ b)
        map_one' := rfl
        map_mul' := fun _ _ => by
          simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
        map_zero' := by simp
        map_add' := fun _ _ => by simp [TensorProduct.tmul_add]
        commutes' k := by
          rw [Algebra.algebraMap_eq_smul_one (R := K) (A := E ⊗[K] (A ⊗[K] B)),
            Algebra.algebraMap_eq_smul_one (R := K) (A := B)]
          rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul,
            Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def] }
    fun e b => show (_ ⊗ₜ _) * (_ ⊗ₜ _) = (_ ⊗ₜ _) * (_ ⊗ₜ _) by simp)
      fun x y => show _ = _ by
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero, zero_mul, mul_zero]
        | add x x' hx hx' => simp only [map_add, mul_add, hx, hx', add_mul]
        | tmul e a =>
          simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk]
          induction y using TensorProduct.induction_on with
          | zero => simp only [map_zero, mul_zero, zero_mul]
          | add y y' hy hy' => simp only [map_add, mul_add, hy, hy', add_mul]
          | tmul e' b =>
            simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk, RingHom.coe_mk]
            change (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _)) =
              (_ ⊗ₜ _) * (_ ⊗ₜ _) * ((_ ⊗ₜ _) * (_ ⊗ₜ _))
            simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
            rw [mul_comm]

/-- Scalar extension is compatible with tensor products of algebras. -/
def e6 :
    (E ⊗[K] A) ⊗[E] (E ⊗[K] B) ≃ₐ[E] E ⊗[K] (A ⊗[K] B) :=
  baseChangeTensorEquiv A B

/-- The base field scalar extension `E ⊗[K] K` is equivalent to `E`. -/
def e7 : E ≃ₐ[E] (E ⊗[K] K) := .symm <| Algebra.TensorProduct.rid _ _ _

end someEquivs

section Q_to_C

/-- The Brauer group homomorphism induced by scalar extension from `K` to `E`. -/
abbrev BaseChange : BrauerGroup (K := K) →* BrauerGroup (K := E) where
  toFun :=
    Quotient.map'
    (fun A =>
    { __ := AlgCat.of E (E ⊗[K] A)
      fin_dim := inferInstance }) fun A B ⟨m, n, hm, hn, ⟨e⟩⟩ =>
          ⟨m, n, hm, hn, ⟨(someEquivs.e1 A m).trans <| (someEquivs.e2 A m).trans <|
            (someEquivs.e3 A m).trans <| (someEquivs.e4 A m).trans <| AlgEquiv.symm <|
            (someEquivs.e1 B n).trans <| (someEquivs.e2 B n).trans <|
            (someEquivs.e3 B n).trans <| (someEquivs.e4 B n).trans <| someEquivs.e5 _ _ e.symm⟩⟩
  map_one' := by
    erw [Quotient.eq'']
    exact ⟨1, 1, one_ne_zero, one_ne_zero,
      ⟨(dimOneIso (K := E) (E ⊗[K] K)).trans <|
        (someEquivs.e7 (K := K) (E := E)).symm.trans <|
          (dimOneIso (K := E) E).symm⟩⟩
  map_mul' := by
    intro x y
    induction x using Quotient.inductionOn' with | h A
    induction y using Quotient.inductionOn' with | h B
    simp only [Quotient.map'_mk'']
    erw [Quotient.map'_mk'']
    erw [Quotient.eq'']
    change IsBrauerEquivalent ⟨.of E (E ⊗[K] (A ⊗[K] B))⟩ _
    exact ⟨1, 1, one_ne_zero, one_ne_zero,
      ⟨(dimOneIso _).trans <| .symm <| (dimOneIso _).trans <| someEquivs.e6 A B⟩⟩

/-- The scalar extension homomorphism from the rational Brauer group to the complex Brauer group. -/
abbrev BaseChangeQToC := BaseChange (K := ℚ) (E := ℂ)

lemma BaseChangeQToC_eq_one : BaseChangeQToC = 1 := by
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  ext A; simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply]
  induction A using Quotient.inductionOn' with | h A;
  simp only [Quotient.map'_mk'']; apply Quotient.sound
  exact BrauerGroup.Alg_closed_equiv_one _

instance IsAbelBrauer : CommGroup (BrauerGroup (K := K)) where
  __ := BrauerGroup.BruaerGroup
  mul_comm A B := by
    induction A using Quotient.inductionOn' with | h A
    induction B using Quotient.inductionOn' with | h B
    apply Quotient.sound'
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨.mapMatrix <| Algebra.TensorProduct.comm ..⟩⟩

open CategoryTheory

namespace baseChangeIdem

/-- The linear equivalence comparing two-step and one-step scalar extension. -/
@[simps!]
def Aux (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] (K ⊗[F] A) ≃ₗ[E] (E ⊗[F] A.carrier) :=
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  (TensorProduct.AlgebraTensorModule.assoc F K E E K A).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.AlgebraTensorModule.rid _ _ _) (LinearEquiv.refl _ _)

/-- The algebra equivalence comparing two-step and one-step scalar extension. -/
def Aux' (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] (A : CSA F) :
    E ⊗[K] (K ⊗[F] A) ≃ₐ[E] (E ⊗[F] A.carrier) := by
  have : SMulCommClass F K E :=
    { smul_comm := fun a b c => by
        rw [Algebra.smul_def, Algebra.smul_def, ← _root_.mul_assoc, mul_comm (algebraMap _ _ a),
          Algebra.smul_def, Algebra.smul_def, _root_.mul_assoc] }
  refine .ofLinearEquiv (Aux F K E A) ?_ fun x y ↦ ?_
  · simp [Algebra.TensorProduct.one_def]
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, (baseChangeIdem.Aux F K E A).map_zero, zero_mul]
  | add => simp only [add_mul, (Aux F K E A).map_add, *]
  | tmul =>
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, (baseChangeIdem.Aux F K E A).map_zero, mul_zero]
  | add => simp only [mul_add, (Aux F K E A).map_add, *]
  | tmul =>
  rename_i x1 y1 x2 y2
  simp only [Aux, Algebra.TensorProduct.tmul_mul_tmul, LinearEquiv.trans_apply]
  set f := (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.AlgebraTensorModule.rid K E E) (LinearEquiv.refl F A))
  set g := (TensorProduct.AlgebraTensorModule.assoc F K E E K A.carrier).symm
  change f (g _) = _
  induction y1 using TensorProduct.induction_on with
  | zero =>
    rw [zero_mul, TensorProduct.tmul_zero, g.map_zero, f.map_zero, TensorProduct.tmul_zero,
      g.map_zero, f.map_zero, zero_mul]
  | add => simp only [add_mul, TensorProduct.tmul_add, g.map_add, f.map_add, *]
  | tmul k1 a1 =>
  induction y2 using TensorProduct.induction_on with
  | zero =>
    rw [mul_zero, TensorProduct.tmul_zero, TensorProduct.tmul_zero, g.map_zero, f.map_zero,
      mul_zero]
  | add => simp only [mul_add, TensorProduct.tmul_add, g.map_add, f.map_add, *]
  | tmul k2 a2 =>
  simp only [Algebra.TensorProduct.tmul_mul_tmul, *]
  -- rw [mul_comm]
  simp only [TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    LinearEquiv.refl_apply, Algebra.TensorProduct.tmul_mul_tmul, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, f, g]
  congr 1
  rw [mul_comm k1 k2]
  exact mul_smul k2 k1 (x1 * x2)

end baseChangeIdem

lemma baseChangeIdem (F K E : Type u) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] :
    BrauerGroupHom.BaseChange (K := F) (E := E) =
    (BrauerGroupHom.BaseChange (K := K) (E := E)).comp
    BrauerGroupHom.BaseChange := by
  ext A
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply]
  induction A using Quotient.inductionOn' with | h A
  simp only [Quotient.map'_mk'', Quotient.eq'']
  exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨.mapMatrix <| .symm <| baseChangeIdem.Aux' ..⟩⟩

/-- The Brauer group functor from fields to commutative groups. -/
def Br : FieldCat ⥤ CommGrpCat where
  obj F := .of <| BrauerGroup F
  map {F K} f := CommGrpCat.ofHom <| @BrauerGroupHom.BaseChange F _ K _ (RingHom.toAlgebra f.hom)
  map_id F := by
    ext A
    simp only [CommGrpCat.coe_of]
    induction A using Quotient.inductionOn' with | h A
    simp only [CommGrpCat.hom_ofHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Quotient.map'_mk'', CommGrpCat.hom_id, MonoidHom.id_apply, Quotient.eq]
    change IsBrauerEquivalent _ _
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.mapMatrix <| Algebra.TensorProduct.lid _ _⟩⟩
  map_comp {F K E} f g := by
    simp only [← CommGrpCat.ofHom_comp]
    congr 1
    apply (config := { allowSynthFailures := true }) baseChangeIdem
    letI : Algebra F E := RingHom.toAlgebra (f ≫ g).hom
    letI : Algebra F K := RingHom.toAlgebra f.hom
    letI : Algebra K E := RingHom.toAlgebra g.hom
    exact IsScalarTower.of_algebraMap_smul (R := F) (A := K) (M := E) fun r ↦ congrFun rfl

end Q_to_C

end BrauerGroupHom
