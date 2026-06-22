/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.Basic
import LeanPool.Monlib4.QuantumGraph.Example
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.Submodule
import LeanPool.Monlib4.RepTheory.AutMat
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# LeanPool.Monlib4.QuantumGraph.PiMat

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.PiMat`.
-/

variable {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [Π i, Fintype (p i)] [Π i, DecidableEq (p i)]
  {φ : Π i, Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : Π i, (φ i).IsFaithfulPosMap]

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

/-- Introduce the quantum-set instances for a product of matrix blocks in a proof. -/
syntax "withPiQuantumCtx" "[" term "]" : tactic
macro_rules
 | `(tactic| withPiQuantumCtx[$ψ]) =>
      `(tactic|
        letI := PiMat.isStarAlgebra (ψ := $ψ);
        letI := Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := $ψ);
        letI := Module.Dual.PiNormedAddCommGroup (φ := $ψ);
        letI := (Module.Dual.PiNormedAddCommGroup (φ :=
          $ψ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
        letI := (Module.Dual.PiNormedAddCommGroup (φ := $ψ)).toSeminormedAddCommGroup;
        letI := Module.Dual.pi.InnerProductSpace (φ := $ψ))

/-- Introduce the quantum-set instances for a single matrix algebra in a proof. -/
syntax "withMatrixQuantumCtx" "[" term "]" : tactic
macro_rules
  | `(tactic| withMatrixQuantumCtx[$φ]) =>
      `(tactic|
        letI := Matrix.isStarAlgebra (φ := $φ);
        letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ);
        letI := Module.Dual.NormedAddCommGroup $φ;
        letI := (Module.Dual.NormedAddCommGroup
          $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
        letI := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup;
        letI := Module.Dual.InnerProductSpace (φ := $φ))

private noncomputable abbrev PiMatTensorTo (ι : Type*)
  (p : ι → Type*) [Fintype ι] [DecidableEq ι]
  [Π i, DecidableEq (p i)] [Π i, Fintype (p i)] :
  (PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p) ≃⋆ₐ[ℂ] (i : ι × ι) →
    (Matrix (p i.1) (p i.1) ℂ ⊗[ℂ] Matrix (p i.2) (p i.2) ℂ) :=
StarAlgEquiv.ofAlgEquiv (directSumTensorAlgEquiv ℂ
    (fun i ↦ Matrix (p i) (p i) ℂ) (fun i ↦ Matrix (p i) (p i) ℂ))
  (fun x => x.induction_on
    (by simp only [star_zero, map_zero])
    (fun _ _ => by
      ext
      simp only [Pi.star_apply, TensorProduct.star_tmul,
        directSumTensorAlgEquiv_apply, directSumTensorToFun_apply])
    (fun _ _ h1 h2 => by simp only [star_add, map_add, h1, h2]))

/--
Transpose each matrix block of a `PiMat` as a star-algebra equivalence to the opposite algebra.
-/
@[simps]
noncomputable def PiMat.transposeStarAlgEquiv
  (ι : Type*) (p : ι → Type*) [Π i, Fintype (p i)] :
    PiMat ℂ ι p ≃⋆ₐ[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ where
  toFun x := MulOpposite.op (fun i => (x i)ᵀ)
  invFun x i := (MulOpposite.unop x i)ᵀ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := by
    simp only [Pi.mul_apply, Matrix.transpose_mul]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    -- simp only [MulOpposite.op_inj, Matrix.transpose_smul]
    rfl
  map_star' _ := rfl

/-- Matrix algebra as endomorphisms of Euclidean space, as a star-algebra equivalence. -/
noncomputable abbrev Matrix.toEuclideanStarAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
    (Matrix n n ℂ) ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) :=
  StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofLinearEquiv (Matrix.toEuclideanLin)
      (by
        exact Matrix.toLpLin_one (p := (2 : ENNReal)))
      (fun x y => by
        simp only [Matrix.toLpLin_eq_toLin,
          Matrix.toLin_mul (PiLp.basisFun 2 ℂ n) (PiLp.basisFun 2 ℂ n)]
        rfl))
    (fun _ => by
      simp only [AlgEquiv.ofLinearEquiv_apply, Matrix.toEuclideanLin_eq_toLin_orthonormal,
        LinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose,
        Matrix.toLin_conjTranspose])
theorem Matrix.toEuclideanStarAlgEquiv_coe {n : Type*} [Fintype n] [DecidableEq n] :
  ⇑(Matrix.toEuclideanStarAlgEquiv :
    Matrix n n ℂ ≃⋆ₐ[ℂ] EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =
    Matrix.toEuclideanLin := rfl

/-- Tensor-product equivalence for direct products of matrix algebras. -/
@[simps!]
noncomputable def PiMatTensorProductEquiv
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)] :
    (PiMat ℂ ι₁ p₁) ⊗[ℂ] (PiMat ℂ ι₂ p₂) ≃⋆ₐ[ℂ]
      PiMat ℂ (ι₁ × ι₂) (fun i : ι₁ × ι₂ => p₁ i.1 × p₂ i.2) :=
StarAlgEquiv.ofAlgEquiv
  ((directSumTensorAlgEquiv ℂ _ _).trans
    (AlgEquiv.piCongrRight (fun i => tensorToKronecker)))
  (fun x => by
    ext1
    simp only [Pi.star_apply]
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
    simp only [AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply, directSumTensorAlgEquiv_apply,
      tensorToKronecker_apply]
    simp only [TensorProduct.star_tmul, map_sum, Finset.sum_apply, star_sum,
      directSumTensorToFun_apply, Pi.star_apply, TensorProduct.toKronecker_star])

theorem PiMatTensorProductEquiv_tmul_apply
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) (r : ι₁ × ι₂)
  (a b : p₁ r.1 × p₂ r.2) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) r a b = x r.1 a.1 b.1 * y r.2 a.2 b.2 := by
  simp_rw [PiMatTensorProductEquiv_apply, directSumTensorToFun_apply,
    TensorProduct.toKronecker_apply]
  rfl
open scoped Kronecker
theorem PiMatTensorProductEquiv_tmul
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) = fun r : ι₁ × ι₂ => (x r.1 ⊗ₖ y r.2) := by
  ext; simp only [PiMatTensorProductEquiv_tmul_apply]; rfl

theorem PiMatTensorProductEquiv_tmul_apply'
  {ι₁ ι₂ : Type*} {p₁ : ι₁ → Type*} {p₂ : ι₂ → Type*}
  [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Π i, Fintype (p₁ i)] [Π i, DecidableEq (p₁ i)]
  [Π i, Fintype (p₂ i)] [Π i, DecidableEq (p₂ i)]
  (x : PiMat ℂ ι₁ p₁) (y : PiMat ℂ ι₂ p₂) (r : ι₁ × ι₂)
  (a c : p₁ r.1) (b d : p₂ r.2) :
    (PiMatTensorProductEquiv (x ⊗ₜ[ℂ] y)) r (a, b) (c, d) = x r.1 a c * y r.2 b d :=
PiMatTensorProductEquiv_tmul_apply _ _ _ _ _

open scoped FiniteDimensional in
/-- The forgetful equivalence from continuous endomorphisms to linear endomorphisms,
as a star algebra equivalence. -/
noncomputable def ContinuousLinearMap.toLinearMapStarAlgEquiv {𝕜 B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B] [CompleteSpace B] :
    (B →L[𝕜] B) ≃⋆ₐ[𝕜] (B →ₗ[𝕜] B) :=
StarAlgEquiv.ofAlgEquiv ContinuousLinearMap.toLinearMapAlgEquiv
  (fun _ => by simp only [ContinuousLinearMap.toLinearMapAlgEquiv_apply]; rfl)

/-- Convert each block of a `PiMat` to a Euclidean-space linear map. -/
noncomputable abbrev PiMatToEuclideanLM :
  (PiMat ℂ ι p) ≃⋆ₐ[ℂ] (Π i, EuclideanSpace ℂ (p i) →ₗ[ℂ] EuclideanSpace ℂ (p i)) :=
StarAlgEquiv.piCongrRight (fun _ => Matrix.toEuclideanStarAlgEquiv)

/-- Trace functional on a product of matrix blocks. -/
@[simps!]
noncomputable abbrev PiMat.traceLinearMap :
    (PiMat ℂ ι p) →ₗ[ℂ] ℂ :=
Matrix.traceLinearMap _ _ _ ∘ₗ Matrix.blockDiagonal'AlgHom.toLinearMap

/-- Coalgebra structure on a finite product of matrix blocks. -/
@[reducible]
noncomputable def PiMat.finiteDimensionalHilbertCoalgebraStruct :
    CoalgebraStruct ℂ (PiMat ℂ ι p) := by
  withPiQuantumCtx[φ]
  exact (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ)
    (A := PiMat ℂ ι p)).toCoalgebraStruct

theorem QuantumGraph.PiMat_existsSubmoduleIsProj :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph (PiMat ℂ ι p) f → ∀ t r : ℝ,
        ∃ u : Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)),
          ∀ i : ι × ι, LinearMap.IsProj (u i)
            (PiMatToEuclideanLM (PiMatTensorProductEquiv
              ((StarAlgEquiv.lTensor _
                (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
by
  withPiQuantumCtx[φ]
  intro f hf t r
  let q : Π i : ι × ι, EuclideanSpace ℂ (p i.1 × p i.2) →ₗ[ℂ]
      EuclideanSpace ℂ (p i.1 × p i.2) :=
    PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
      (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f)))
  have : ∀ i, IsIdempotentElem (q i) :=
  by
    rw [← isIdempotentElem_pi_iff (a := q)]
    dsimp [q]
    simp_rw [IsIdempotentElem.mulEquiv]
    simpa [QuantumSet.Psi_apply] using
      (schurIdempotent_iff_Psi_isIdempotentElem (A := PiMat ℂ ι p)
        (B := PiMat ℂ ι p) f t r).mp hf.isIdempotentElem
  simp_rw [← LinearMap.isProj_iff_isIdempotentElem] at this
  exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩


/-- Submodules associated to the block components of a `PiMat` quantum graph. -/
noncomputable def QuantumGraph.PiMatSubmodule :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph (PiMat ℂ ι p) f → ℝ → ℝ →
        Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
by
  withPiQuantumCtx[φ]
  intro f hf t r
  exact Classical.choose (QuantumGraph.PiMat_existsSubmoduleIsProj hf t r)

theorem QuantumGraph.PiMatSubmoduleIsProj :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph (PiMat ℂ ι p) f) → ∀ (t r : ℝ) (i : ι × ι),
        LinearMap.IsProj (hf.PiMatSubmodule t r i)
          (PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
            (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
by
  withPiQuantumCtx[φ]
  intro f hf t r i
  exact Classical.choose_spec (QuantumGraph.PiMat_existsSubmoduleIsProj hf t r) i

theorem QuantumGraph.PiMatSubmoduleIsProj_codRestrict :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph (PiMat ℂ ι p) f) → ∀ (t r : ℝ) (i : ι × ι),
        (Submodule.subtype _).comp (QuantumGraph.PiMatSubmoduleIsProj hf t r i).codRestrict
          = (PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
            (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi t r f))) i) :=
by
  withPiQuantumCtx[φ]
  intros
  rfl

/-- Sum of the dimensions of the block submodules associated to a `PiMat` quantum graph. -/
noncomputable def QuantumGraph.dimOfPiMatSubmodule :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, QuantumGraph _ f → ℕ :=
by
  withPiQuantumCtx[φ]
  intro f hf
  exact ∑ i : ι × ι, Module.finrank ℂ (hf.PiMatSubmodule 0 (1 / 2) i)

theorem PiMat.traceLinearMap_comp_piMatTensorProductEquiv_eq :
  (PiMat.traceLinearMap : (PiMat ℂ (ι × ι) fun i ↦ p i.1 × p i.2) →ₗ[ℂ] ℂ) ∘ₗ
    PiMatTensorProductEquiv.toLinearMap
    = LinearMap.mul' ℂ _ ∘ₗ (TensorProduct.map PiMat.traceLinearMap PiMat.traceLinearMap) :=
by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, StarAlgEquiv.toLinearMap_apply,  PiMatTensorProductEquiv_tmul,
    TensorProduct.map_tmul, LinearMap.mul'_apply,
    AlgHom.toLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.traceLinearMap_apply,
    Matrix.trace_blockDiagonal', Matrix.trace_kronecker,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_product_univ]
  rw [Finset.sum_comm]

lemma PiMat.transposeStarAlgEquiv_symm_is_tracePreserving (x : (PiMat ℂ ι p)ᵐᵒᵖ) :
  PiMat.traceLinearMap ((PiMat.transposeStarAlgEquiv ι p).symm x) =
    PiMat.traceLinearMap (MulOpposite.unop x) :=
rfl

lemma PiMat.traceLinearMap_comp_transposeStarAlgEquiv_symm :
  PiMat.traceLinearMap ∘ₗ (PiMat.transposeStarAlgEquiv ι p).symm.toLinearMap
    = PiMat.traceLinearMap ∘ₗ (unop ℂ (A := PiMat ℂ ι p)).toLinearMap :=
rfl

theorem QuantumGraph.dimOfPiMatSubmodule_eq_trace :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hf : QuantumGraph _ f) →
      QuantumGraph.dimOfPiMatSubmodule hf =
        PiMat.traceLinearMap
          (PiMatTensorProductEquiv
            ((StarAlgEquiv.lTensor _ (PiMat.transposeStarAlgEquiv ι p).symm)
              (QuantumSet.Psi 0 (1 / 2) f))) :=
by
  withPiQuantumCtx[φ]
  intro f hf
  rw [PiMat.traceLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.trace_blockDiagonal', dimOfPiMatSubmodule]
  simp only [Nat.cast_sum, PiMatTensorProductEquiv_apply]
  congr
  ext i
  rw [← LinearMap.IsProj.trace (QuantumGraph.PiMatSubmoduleIsProj hf 0 (1 / 2) i)]
  simp only [StarAlgEquiv.piCongrRight_apply,
    Matrix.toEuclideanStarAlgEquiv_coe,
    PiMatTensorProductEquiv_apply, EuclideanSpace.trace_eq_matrix_trace',
      LinearEquiv.symm_apply_apply]

theorem Coalgebra.counit_mulOpposite {A : Type*}
  [Semiring A] [Algebra ℂ A] [CoalgebraStruct ℂ A] :
  Coalgebra.counit (R := ℂ) (A := Aᵐᵒᵖ) = Coalgebra.counit ∘ₗ (unop ℂ).toLinearMap :=
rfl

theorem StarAlgEquiv.lTensor_toLinearMap {R A B C : Type*}
  [RCLike R] [Ring A] [Ring B] [Ring C] [Algebra R A]
  [Algebra R B] [Algebra R C] [StarAddMonoid A] [StarAddMonoid B]
  [StarAddMonoid C] [StarModule R A] [StarModule R B]
  [StarModule R C] [Module.Finite R A] [Module.Finite R B]
  [Module.Finite R C] (f : A ≃⋆ₐ[R] B) :
  (StarAlgEquiv.lTensor C f).toLinearMap = LinearMap.lTensor C f.toLinearMap :=
rfl

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

-- noncomputable instance MulOppositeCoalgebra {A : Type*} [Semiring A] [Algebra ℂ A]
--   [Coalgebra ℂ A] :
--     Coalgebra ℂ Aᵐᵒᵖ where
--   coassoc := sorry
--   rTensor_counit_comp_comul := sorry
--   lTensor_counit_comp_comul := sorry

-- remove this...
noncomputable instance TensorProduct.instCoalgebraStruct'
  {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
    [Algebra R S] [Module R A] [Module S A] [Module R B] [CoalgebraStruct R B]
    [CoalgebraStruct S A] [IsScalarTower R S A] : CoalgebraStruct S (A ⊗[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map CoalgebraStruct.comul CoalgebraStruct.comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ
    AlgebraTensorModule.map CoalgebraStruct.counit CoalgebraStruct.counit

lemma TensorProduct.instCoalgebraStruct'_counit
  {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
  [Algebra R S] [Module R A] [Module S A] [Module R B] [CoalgebraStruct R B]
  [CoalgebraStruct S A] [IsScalarTower R S A] :
  (TensorProduct.instCoalgebraStruct' : CoalgebraStruct S (A ⊗[R] B)).counit =
    AlgebraTensorModule.rid R S S ∘ₗ
      AlgebraTensorModule.map CoalgebraStruct.counit CoalgebraStruct.counit :=
rfl

-- attribute [local instance] TensorProduct.instCoalgebraStruct'

-- instance :
--   Coalgebra ℂ (PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) :=
-- Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A := PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ)

theorem QuantumGraph.dimOfPiMatSubmodule_eq_trace_counit :
  withPiQuantum[φ]
    (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = PiMat.traceLinearMap →
      ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hf : QuantumGraph _ f) →
        QuantumGraph.dimOfPiMatSubmodule hf =
          (Coalgebra.counit (R := ℂ)) (QuantumSet.Psi 0 (1 / 2) f) :=
by
  withPiQuantumCtx[φ]
  intro hc f hf
  simp only [TensorProduct.instCoalgebraStruct'_counit,
    LinearMap.coe_comp, Function.comp_apply, hc, Coalgebra.counit_mulOpposite]
  rw [QuantumGraph.dimOfPiMatSubmodule_eq_trace]
  simp only [← StarAlgEquiv.toLinearMap_apply, ← LinearMap.comp_apply,
    ← LinearMap.comp_assoc,
    PiMat.traceLinearMap_comp_piMatTensorProductEquiv_eq,
    StarAlgEquiv.lTensor_toLinearMap]
  rw [LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
  simp only [one_div, QuantumSet.Psi_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  congr 1
  ext; simp

-- set_option maxHeartbeats 500000 in
theorem Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one
  {A : Type*} [NormedAddCommGroupOfRing A]
  [InnerProductSpace ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [FiniteDimensional ℂ A] :
  Coalgebra.counit (R := ℂ) (A := A ⊗[ℂ] Aᵐᵒᵖ)
    = (bra ℂ (1 : A ⊗[ℂ] Aᵐᵒᵖ)).toLinearMap :=
by
  -- letI : FiniteDimensional ℂ (A ⊗[ℂ] Aᵐᵒᵖ) := by infer_instance
  -- -- letI
  -- letI := TensorProduct.instNormedAddCommGroupOfRing (R:= ℂ) (A := A) (B := Aᵐᵒᵖ)
  -- exact @Coalgebra.counit_eq_bra_one ℂ (A ⊗[ℂ] Aᵐᵒᵖ)
  --   _ _ _ _ _ _
  apply TensorProduct.ext'
  intro x y
  -- rw [TensorProduct.counit_def]
  simp only [TensorProduct.instCoalgebraStruct'_counit, LinearMap.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.one_def,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, TensorProduct.inner_tmul,
    Coalgebra.inner_eq_counit', Coalgebra.counit_mulOpposite_eq,
    MulOpposite.inner_eq, MulOpposite.unop_one,
    TensorProduct.AlgebraTensorModule.map_tmul]
  simp only [LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul, smul_eq_mul, mul_comm]

lemma QuantumGraph.NumOfEdges_apply {A : Type*} [starAlgebra A] [QuantumSet A]
  (f : A →ₗ[ℂ] A) : NumOfEdges f = inner ℂ 1 (f 1) :=
rfl

-- instance {A : Type*} [NormedAddCommGroupOfRing A] :
--   NormedAddCommGroupOfRing Aᵐᵒᵖ where
-- noncomputable instance {A : Type*} [NormedAddCommGroup A]
--   [InnerProductSpace ℂ A] : InnerProductSpace ℂ Aᵐᵒᵖ where
--   norm_sq_eq_re_inner _ := by
--     simp [MulOpposite.inner_eq, norm_eq_sqrt_re_inner (𝕜 := ℂ)]
--     rw [← RCLike.re_eq_complex_re]
--     exact Real.sq_sqrt (inner_self_nonneg)
--   conj_inner_symm _ _ := inner_conj_symm _ _
--   add_left _ _ _ := inner_add_left _ _ _
--   smul_left x y _ := inner_smul_left _ _ _
-- noncomputable instance {A : Type*} [NormedAddCommGroupOfRing A] [InnerProductSpace ℂ A]
--   [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
--   [FiniteDimensional ℂ A] :
--   NormedAddCommGroupOfRing (A ⊗[ℂ] Aᵐᵒᵖ) where

omit [DecidableEq ι] in
private lemma Coalgebra.counit_piMat_eq_moduleDual_pi :
  letI : DecidableEq ι := Classical.decEq ι
  withPiQuantum[φ]
    ∀ x : PiMat ℂ ι p,
      CoalgebraStruct.counit (R := ℂ) (A := PiMat ℂ ι p) x = Module.Dual.pi φ x := by
  classical
  withPiQuantumCtx[φ]
  intro x
  rw [← congrFun (QuantumSet.inner_eq_counit' (B := PiMat ℂ ι p)) x]
  rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_one, one_mul]

omit [DecidableEq ι] in
private lemma Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one_piMat :
  letI : DecidableEq ι := Classical.decEq ι
  withPiQuantum[φ]
    CoalgebraStruct.counit (R:= ℂ) (A:= PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) =
      ((bra ℂ) (1 : PiMat ℂ ι p ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ)).toLinearMap :=
by
  classical
  withPiQuantumCtx[φ]
  apply TensorProduct.ext'
  intro x y
  simp only [TensorProduct.instCoalgebraStruct'_counit, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.AlgebraTensorModule.map_tmul,
    counit_mulOpposite_eq, TensorProduct.AlgebraTensorModule.rid_tmul, smul_eq_mul,
    mul_comm, Algebra.TensorProduct.one_def, ContinuousLinearMap.toLinearMap_innerSL_apply,
    innerₛₗ_apply_apply, TensorProduct.inner_tmul, MulOpposite.inner_eq,
    MulOpposite.unop_one]
  have hx : Coalgebra.counit x = inner ℂ 1 x :=
    by
      rw [Coalgebra.counit_piMat_eq_moduleDual_pi (φ := φ)]
      rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq (ψ := φ)]
      simp
  have hy : Coalgebra.counit (MulOpposite.unop y) = inner ℂ 1 (MulOpposite.unop y) :=
    by
      rw [Coalgebra.counit_piMat_eq_moduleDual_pi (φ := φ)]
      rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq (ψ := φ)]
      simp
  rw [hx, hy]

theorem QuantumGraph.dimOfPiMatSubmodule_eq_numOfEdges_of_trace_counit :
  withPiQuantum[φ]
    (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = PiMat.traceLinearMap →
      ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hf : QuantumGraph _ f) →
        hf.dimOfPiMatSubmodule = QuantumGraph.NumOfEdges f :=
by
  withPiQuantumCtx[φ]
  intro hc f hf
  rw [QuantumGraph.dimOfPiMatSubmodule_eq_trace_counit hc,
    NumOfEdges_apply, oneInner_map_one_eq_oneInner_Psi_map _ 0 (1/2)]
  simp only [Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one_piMat]
  rfl

  -- rw [Coalgebra.counit_eq_bra_one]
  -- rw [Coalgebra.counit_self_tensor_mulOpposite_eq_bra_one]
  -- rfl

theorem QuantumGraph.dimOfPiMatSubmodule_eq_rank_top_iff :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hf : QuantumGraph _ f) →
      QuantumGraph.dimOfPiMatSubmodule hf =
          ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
        ↔ f = Qam.completeGraph _ _ :=
by
  withPiQuantumCtx[φ]
  intro f hf
  calc
    QuantumGraph.dimOfPiMatSubmodule hf = ∑ i : ι × ι, Fintype.card (p i.1) *
      Fintype.card (p i.2)
      ↔ ∑ i : ι × ι, Module.finrank ℂ ↥(hf.PiMatSubmodule 0 (1 / 2) i)
        = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) := by rfl
    _ ↔ ∀ i, Module.finrank ℂ ↥(hf.PiMatSubmodule 0 (1 / 2) i)
      = Fintype.card (p i.1) * Fintype.card (p i.2) := by
        rw [← Nat.cast_inj (R := ℂ)]
        simp only [Nat.cast_sum]
        rw [eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_zero_iff_of_nonneg]
        · simp_rw [sub_eq_zero, Nat.cast_inj, Finset.mem_univ, true_imp_iff,
            ← Fintype.card_prod, ← finrank_euclideanSpace (𝕜 := ℂ),
            @eq_comm _ _ (Module.finrank ℂ (hf.PiMatSubmodule 0 (1/2) _))]
        · simp only [Finset.mem_univ, sub_nonneg, true_implies, Nat.cast_le]
          intro i
          calc Module.finrank ℂ (↥(hf.PiMatSubmodule 0 (1 / 2) i))
            ≤ Module.finrank ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
                Submodule.finrank_le _
            _ = Fintype.card (p i.1) * Fintype.card (p i.2) := by
              simp only [finrank_euclideanSpace, Fintype.card_prod]
    _ ↔
      ∀ i, hf.PiMatSubmodule 0 (1 / 2) i = (⊤ : Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2))) :=
        by
          simp_rw [← Fintype.card_prod, ← finrank_euclideanSpace (𝕜 := ℂ)]
          constructor
          · intro h i
            exact Submodule.eq_top_of_finrank_eq (h i)
          · intro h i
            rw [h]
            simp only [finrank_top]
    _ ↔
      ∀ i, (PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1/2) f))) i)
      = LinearMap.id := by
        simp_rw [LinearMap.IsProj.codRestrict_eq_dim_iff (hf.PiMatSubmoduleIsProj 0 (1/2) _),
          LinearMap.IsProj.subtype_comp_codRestrict]
    _
      ↔ (PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
    (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1/2) f))))
      = 1 := by
        rw [funext_iff]; exact Iff.rfl
    _ ↔ f = Qam.completeGraph _ _ :=
      by
        rw [eq_comm]
        simp_rw [StarAlgEquiv.eq_apply_iff_symm_eq, map_one]
        rw [← LinearEquiv.symm_apply_eq, QuantumSet.Psi_symm_one, eq_comm]

theorem QuantumGraph.CompleteGraph_dimOfPiMatSubmodule :
  withPiQuantum[φ]
    QuantumGraph.dimOfPiMatSubmodule
      (⟨Qam.Nontracial.CompleteGraph.qam⟩ :
        QuantumGraph _ (Qam.completeGraph (PiMat ℂ ι p) (PiMat ℂ ι p)))
        = ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2) :=
by
  withPiQuantumCtx[φ]
  rw [QuantumGraph.dimOfPiMatSubmodule_eq_rank_top_iff]

open scoped InnerProductSpace
omit [DecidableEq ι] in
theorem Algebra.linearMap_adjoint_eq_dual :
  letI : DecidableEq ι := Classical.decEq ι
  withPiQuantum[φ]
    LinearMap.adjoint (Algebra.linearMap ℂ (PiMat ℂ ι p))
      = Module.Dual.pi φ :=
by
  classical
  withPiQuantumCtx[φ]
  rw [← Module.Dual.pi.IsFaithfulPosMap.adjoint_eq, LinearMap.adjoint_adjoint]

theorem exists_dimOfPiMatSubmodule_ne_inner_one_map_one_of_IsFaithfulState :
  withPiQuantum[φ]
    (Module.Dual.pi φ).IsUnital →
      1 < Module.finrank ℂ (PiMat ℂ ι p) →
        ∃ (A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p)
          (hA : QuantumGraph (PiMat ℂ ι p) A),
          QuantumGraph.NumOfEdges A ≠ QuantumGraph.dimOfPiMatSubmodule hA :=
by
  withPiQuantumCtx[φ]
  intro hφ₂ hB
  use Qam.completeGraph _ _, ⟨Qam.Nontracial.CompleteGraph.qam⟩
  rw [QuantumGraph.CompleteGraph_dimOfPiMatSubmodule, Qam.completeGraph,
    QuantumGraph.NumOfEdges]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_coe,
    rankOne_apply_apply_apply, ne_eq]
  have : ⟪(1 : PiMat ℂ ι p), 1⟫_ℂ = 1 :=
  by
    rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq (ψ := φ)]
    simpa [Module.Dual.IsUnital] using hφ₂
  simp_rw [ne_eq, this, one_smul, this]
  rw [← Nat.cast_one, Nat.cast_inj]
  simp only [Module.finrank_pi_fintype, Module.finrank_matrix, ← pow_two,
    Module.finrank_self, mul_one] at hB
  have :=
    calc ∑ i : ι × ι, Fintype.card (p i.1) * Fintype.card (p i.2)
      = ∑ i : ι, ∑ j : ι, Fintype.card (p i) * Fintype.card (p j) :=
        by simp_rw [Finset.sum_product_univ]
      _ = (∑ i : ι, Fintype.card (p i)) ^ 2 :=
        by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [this, eq_comm, ← one_pow 2, sq_eq_sq₀ (by simp) (by simp)]
  contrapose! hB
  calc ∑ x : ι, Fintype.card (p x) ^ 2 ≤ (∑ i : ι, Fintype.card (p i)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (by simp)
    _ = 1 := by rw [hB, one_pow]

theorem QuantumGraph.Real.PiMat_isOrthogonalProjection :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph.Real (PiMat ℂ ι p) A → ∀ i : ι × ι,
        ContinuousLinearMap.IsOrthogonalProjection
        (LinearMap.toContinuousLinearMap
          (PiMatToEuclideanLM (PiMatTensorProductEquiv ((StarAlgEquiv.lTensor _
          (PiMat.transposeStarAlgEquiv ι p).symm) (QuantumSet.Psi 0 (1 / 2) A))) i)) :=
by
  withPiQuantumCtx[φ]
  intro A hA i
  have this' : k (PiMat ℂ ι p) = 0 := by rfl
  rw [← zero_add (1 / 2 : ℝ)]
  nth_rw 2 [← this']
  simp only [LinearMap.isOrthogonalProjection_iff, IsIdempotentElem,
    ← Pi.mul_apply _ _ i, ← map_mul,
    IsSelfAdjoint, ← Pi.star_apply _ i, ← map_star]
  simp only [(quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).1.eq,
    (quantumGraphReal_iff_Psi_isIdempotentElem_and_isSelfAdjoint.mp hA).2.star_eq, and_self]

/-- Block submodules associated to a real `PiMat` quantum graph. -/
noncomputable def QuantumGraph.Real.PiMatSubmodule :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph.Real (PiMat ℂ ι p) A →
        Π i : ι × ι, Submodule ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) :=
by
  withPiQuantumCtx[φ]
  intro A hA i
  exact Classical.choose
      (orthogonal_projection_iff.mpr
      (And.comm.mp
      (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
        (QuantumGraph.Real.PiMat_isOrthogonalProjection hA i))))

theorem QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) → ∀ i : ι × ι,
        (orthogonalProjection' (hA.PiMatSubmodule i)) =
          (LinearMap.toContinuousLinearMap
          ((PiMatToEuclideanLM (PiMatTensorProductEquiv
          ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm)
          (QuantumSet.Psi 0 (1/2) A))) i))) :=
by
  withPiQuantumCtx[φ]
  intro A hA i
  exact Classical.choose_spec
    (orthogonal_projection_iff.mpr
    (And.comm.mp
    (ContinuousLinearMap.isOrthogonalProjection_iff'.mp
      (QuantumGraph.Real.PiMat_isOrthogonalProjection hA i))))

/-- Orthonormal basis of a block submodule associated to a real `PiMat` quantum graph. -/
noncomputable def QuantumGraph.Real.PiMatOrthonormalBasis :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) → ∀ i : ι × ι,
        OrthonormalBasis (Fin (Module.finrank ℂ (hA.PiMatSubmodule i))) ℂ
          (hA.PiMatSubmodule i) :=
by
  withPiQuantumCtx[φ]
  intro A hA i
  exact stdOrthonormalBasis ℂ (hA.PiMatSubmodule i)

theorem EuclideanSpace.prod_exists_finset {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  ∃ S : Finset ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m),
    x = ∑ s ∈ S, euclideanSpaceTensor' (R := ℂ) (s.1 ⊗ₜ[ℂ] s.2) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ((euclideanSpaceTensor' (R:=ℂ)).symm x)
  use S
  apply_fun (euclideanSpaceTensor' (R:=ℂ)).symm using LinearEquiv.injective _
  simp only [map_sum, LinearIsometryEquiv.symm_apply_apply, hS]

theorem QuantumSet.PiMat_n :
  withPiQuantum[φ]
    n (PiMat ℂ ι p) = ((i : ι) × (p i × p i)) :=
rfl

open Kronecker

@[simp]
theorem Matrix.ite_kronecker {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  (if P then x₁ else 0) ⊗ₖ x₂ = if P then x₁ ⊗ₖ x₂ else 0 :=
by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]
@[simp]
theorem Matrix.dite_kronecker {α n m p q : Type*} [MulZeroClass α]
  (P : Prop) [Decidable P]
  (x₁ : P → Matrix n m α) (x₂ : Matrix p q α) :
  (dite P (fun p => x₁ p) (fun _ => 0)) ⊗ₖ x₂ = dite P (fun p => x₁ p ⊗ₖ x₂) (fun _ => 0) :=
by
  split
  next h => simp_all only
  next h => simp_all only [zero_mul, implies_true, kroneckerMap_zero_left]

@[simp]
theorem Matrix.kronecker_ite {α n m p q : Type*} [MulZeroClass α] (x₁ : Matrix n m α)
  (x₂ : Matrix p q α) (P : Prop) [Decidable P] :
  x₁ ⊗ₖ (if P then x₂ else 0) = if P then x₁ ⊗ₖ x₂ else 0 :=
by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]
@[simp]
theorem Matrix.kronecker_dite {α n m p q : Type*} [MulZeroClass α]
  (x₁ : Matrix n m α) (P : Prop) [Decidable P] (x₂ : P → Matrix p q α) :
  x₁ ⊗ₖ (dite P (fun p => x₂ p) (fun _ => 0)) = dite P (fun p => x₁ ⊗ₖ x₂ p) (fun _ => 0) :=
by
  split
  next h => simp_all only
  next h => simp_all only [mul_zero, implies_true, kroneckerMap_zero_right]

theorem Matrix.vecMulVec_kronecker_vecMulVec {α n m p q : Type*} [CommSemiring α]
    (x : n → α) (y : m → α) (z : p → α) (w : q → α) :
  (vecMulVec x y) ⊗ₖ (vecMulVec z w) =
    vecMulVec (reshape (vecMulVec x z)) (reshape (vecMulVec y w)) :=
by
  ext
  simp only [kroneckerMap_apply, vecMulVec_apply, reshape_apply]
  ring_nf

@[simp]
theorem Matrix.vecMulVec_toEuclideanLin {n m : Type*} [Fintype n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  toEuclideanLin (vecMulVec x y) = rankOne ℂ x (star y) :=
by
  classical
  apply_fun Matrix.toEuclideanLin.symm using LinearEquiv.injective _
  simp only [LinearEquiv.symm_apply_apply]
  convert
    (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ) (x := x) (y := star y)).symm
    using 1
  case e'_2 =>
    ext i j
    simp [vecMulVec_apply, PiLp.star_apply]
  case e'_3 =>
    apply congrArg
    ext z
    simp only [ContinuousLinearMap.coe_coe, rankOne_apply, InnerProductSpace.rankOne_apply]

open Matrix in
theorem EuclideanSpaceTensor_apply_eq_reshape_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y) = reshape (vecMulVec x y) :=
by
  ext1
  simp only [euclideanSpaceTensor'_apply, reshape_apply, vecMulVec_apply]

theorem Matrix.vecMulVec_conj {α n m : Type*} [CommSemiring α] [StarMul α] (x : n → α) (y : m → α) :
  (vecMulVec x y)ᴴᵀ = vecMulVec (star x) (star y) :=
by
  ext
  simp only [conj_apply, vecMulVec_apply, Pi.star_apply, star_mul']

theorem rankOne_euclideanSpaceTensor_eq_toEuclideanLin_vecMulVec {n m : Type*} [Fintype n]
  [DecidableEq n] [Fintype m] [DecidableEq m]
  (x y : EuclideanSpace ℂ n) (z w : EuclideanSpace ℂ m) :
  rankOne ℂ (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z))
    (euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w)) =
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    (Matrix.vecMulVec
      (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
      (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))))) :=
by
  let xz : EuclideanSpace ℂ (n × m) := euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z)
  let yw : EuclideanSpace ℂ (n × m) := euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w)
  have hxz : xz.ofLp = Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp) := by
    exact EuclideanSpaceTensor_apply_eq_reshape_vecMulVec x z
  have hyw : yw.ofLp = Matrix.reshape (Matrix.vecMulVec y.ofLp w.ofLp) := by
    exact EuclideanSpaceTensor_apply_eq_reshape_vecMulVec y w
  have hsyw :
      (star yw).ofLp = Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp)) := by
    change star yw.ofLp = Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))
    rw [hyw]
    ext a
    simp [Matrix.reshape_apply, Matrix.vecMulVec_apply]
  have hss : star (star yw) = yw := by
    ext a
    simp
  calc
    rankOne ℂ (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] z))
        (euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] w))
        = rankOne ℂ xz yw := rfl
    _ = rankOne ℂ xz (star (star yw)) := by rw [hss]
    _ = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.vecMulVec xz (star yw))) :=
      by
      apply ContinuousLinearMap.ext
      intro v
      change (rankOne ℂ xz (star (star yw))) v =
        (Matrix.toEuclideanLin (Matrix.vecMulVec xz (star yw))) v
      rw [Matrix.vecMulVec_toEuclideanLin]
      change (rankOne ℂ xz (star (star yw))) v = (rankOne ℂ xz (star (star yw))) v
      rfl
    _ = LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (Matrix.vecMulVec
          (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
          (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))))) := by
      rw [show Matrix.vecMulVec xz (star yw) = Matrix.vecMulVec
          (Matrix.reshape (Matrix.vecMulVec x.ofLp z.ofLp))
          (Matrix.reshape (Matrix.vecMulVec (star y.ofLp) (star w.ofLp))) by
        rw [← hxz, ← hsyw]
        rfl]

theorem Matrix.includeBlock_apply_block {R k : Type*} [CommSemiring R] [DecidableEq k]
    {s : k → Type*} {i : k} (x : Matrix (s i) (s i) R) (j : k) :
    (Matrix.includeBlock x : PiMat R k s) j =
      dite (i = j) (fun h => Eq.mp (by rw [h]) x) fun _ => 0 := by
  rw [Matrix.includeBlock_apply]

/-- A chosen finite support representation of a tensor. -/
noncomputable def TensorProduct.chooseFinset {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (x : TensorProduct R M N) :
    Finset (M × N) :=
Classical.choose (TensorProduct.exists_finset x)
theorem TensorProduct.chooseFinset_spec {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (x : TensorProduct R M N) :
  x = ∑ s ∈ (TensorProduct.chooseFinset x), s.1 ⊗ₜ s.2 :=
by
  exact Classical.choose_spec (TensorProduct.exists_finset x)

/-- A product-coordinate decomposition of Euclidean space vectors. -/
-- changed from choosing some `Finset (_ × _)` like above to the following
noncomputable def EuclideanSpace.prodChoose {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  (n × m) → ((EuclideanSpace ℂ n) × EuclideanSpace ℂ m) :=
  let p₁ : Module.Basis n ℂ (EuclideanSpace ℂ n) := (EuclideanSpace.basisFun n ℂ).toBasis
  let p₂ : Module.Basis m ℂ (EuclideanSpace ℂ m) := (EuclideanSpace.basisFun m ℂ).toBasis
  let a := fun i : n × m =>
    (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R := ℂ)).symm x)) i • p₁ i.1)
  (fun (i : n × m) => (a i, p₂ i.2))

theorem EuclideanSpace.sum_apply {n : Type*} {𝕜 : Type*} [RCLike 𝕜]
  {ι : Type*} (s : Finset ι)
  (x : ι → EuclideanSpace 𝕜 n) (j : n) :
  (∑ i ∈ s, x i) j = ∑ i ∈ s, (x i j) :=
by
  simp [WithLp.ofLp_sum, Finset.sum_apply]

theorem Module.Basis.tensorProduct_repr_tmul_apply' {R M N ι κ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (b : Module.Basis ι R M) (c : Module.Basis κ R N) (m : M) (n : N) (i : ι × κ) :
  ((b.tensorProduct c).repr (m ⊗ₜ[R] n)) i = (c.repr n) i.2 * (b.repr m) i.1 :=
by
  simpa [smul_eq_mul, mul_comm] using
    Module.Basis.tensorProduct_repr_tmul_apply b c m n i.1 i.2

-- theorem PiLp.ext_iff {p : ENNReal} {ι : Type*} {α : ι → Type*} {x : PiLp p α}
--   {y : PiLp p α} :
--   x = y ↔ (∀ (i : ι), x i = y i) :=
-- by simp [← funext_iff]

theorem EuclideanSpace.prodChoose_spec {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] (x : EuclideanSpace ℂ (n × m)) :
  x = ∑ s : n × m, euclideanSpaceTensor' (R:=ℂ)
    (((EuclideanSpace.prodChoose x s).1) ⊗ₜ ((EuclideanSpace.prodChoose x s).2)) :=
by
  have := TensorProduct.of_basis_eq_span ((euclideanSpaceTensor' (R :=
    ℂ)).symm x) (EuclideanSpace.basisFun n ℂ).toBasis (EuclideanSpace.basisFun m ℂ).toBasis
  apply_fun (euclideanSpaceTensor' (R := ℂ)).symm using LinearIsometryEquiv.injective _
  simp only [map_sum, LinearIsometryEquiv.symm_apply_apply]
  rw [this, ← Finset.sum_product']
  simp only [Finset.univ_product_univ, ← TensorProduct.tmul_smul]
  simp only [← TensorProduct.smul_tmul]
  let p₁ := (EuclideanSpace.basisFun n ℂ).toBasis
  let p₂ := (EuclideanSpace.basisFun m ℂ).toBasis
  let a := fun i : n × m => (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R :=
    ℂ)).symm x)) i • p₁ i.1)
  have ha : ∀ i, a i = (((p₁.tensorProduct p₂).repr ((euclideanSpaceTensor' (R :=
    ℂ)).symm x)) i • p₁ i.1) := fun i => rfl
  simp only [p₁, p₂, ← ha]
  rfl

omit [Fintype ι] in
private theorem PiMat_eq_left_block_miss {a b c : ι} (h : a ≠ b)
    (x : Matrix (p a) (p a) ℂ) (y : Matrix (p c) (p c) ℂ) :
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      (Matrix.kroneckerMap (fun x y : ℂ => x * y)
        ((Matrix.includeBlock x : PiMat ℂ ι p) b) y)) = 0 := by
  rw [Matrix.includeBlock_apply_ne_same _ h]
  simp [Matrix.kroneckerMap_zero_left]

omit [Fintype ι] in
private theorem PiMat_eq_right_block_miss {a b c : ι} (h : a ≠ c)
    (x : Matrix (p b) (p b) ℂ) (y : Matrix (p a) (p a) ℂ) :
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      (Matrix.kroneckerMap (fun x y : ℂ => x * y) x
        (((Matrix.includeBlock y : PiMat ℂ ι p) c)ᵀ))) = 0 := by
  rw [Matrix.includeBlock_apply_ne_same _ h]
  simp [Matrix.transpose_zero, Matrix.kroneckerMap_zero_right]

private theorem PiMat_eq_left_block_miss_sum {b j c : ι} (h : j ≠ b)
    {β : ι → Type*} [∀ k, Fintype (β k)]
    (X : (k : ι) → β k → p j → p k → p j → p k → Matrix (p j) (p j) ℂ)
    (Y : (k : ι) → β k → p j → p k → p j → p k → Matrix (p c) (p c) ℂ) :
    (∑ k, ∑ q, ∑ s1, ∑ s2, ∑ t1, ∑ t2,
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (Matrix.kroneckerMap (fun x y : ℂ => x * y)
          ((Matrix.includeBlock (X k q s1 s2 t1 t2) : PiMat ℂ ι p) b)
          (Y k q s1 s2 t1 t2)))) = 0 := by
  apply Fintype.sum_eq_zero
  intro k
  apply Fintype.sum_eq_zero
  intro q
  apply Fintype.sum_eq_zero
  intro s1
  apply Fintype.sum_eq_zero
  intro s2
  apply Fintype.sum_eq_zero
  intro t1
  apply Fintype.sum_eq_zero
  intro t2
  exact PiMat_eq_left_block_miss h _ _

omit [Fintype ι] in
private theorem PiMat_eq_right_block_miss_sum {b j c : ι} (h : j ≠ c)
    {β : Type*} [Fintype β]
    (X : β → p b → p j → p b → p j → Matrix (p b) (p b) ℂ)
    (Y : β → p b → p j → p b → p j → Matrix (p j) (p j) ℂ) :
    (∑ q, ∑ s1, ∑ s2, ∑ t1, ∑ t2,
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (Matrix.kroneckerMap (fun x y : ℂ => x * y)
          ((Matrix.includeBlock (X q s1 s2 t1 t2) : PiMat ℂ ι p) b)
          ((((1 : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p)
            (Matrix.includeBlock (Y q s1 s2 t1 t2) : PiMat ℂ ι p)) c)ᵀ)))) = 0 := by
  apply Fintype.sum_eq_zero
  intro q
  apply Fintype.sum_eq_zero
  intro s1
  apply Fintype.sum_eq_zero
  intro s2
  apply Fintype.sum_eq_zero
  intro t1
  apply Fintype.sum_eq_zero
  intro t2
  simp only [AlgEquiv.one_apply]
  exact PiMat_eq_right_block_miss h _ _

theorem QuantumGraph.Real.PiMat_eq :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) →
        let S : (i : ι × ι) →
            (j : (Fin (Module.finrank ℂ (hA.PiMatSubmodule i))))
              → (((p i.1) × (p i.2)) →
                (((EuclideanSpace ℂ (p i.1)) × (EuclideanSpace ℂ (p i.2)))))
          := fun i j => EuclideanSpace.prodChoose
            (((hA.PiMatOrthonormalBasis i j : hA.PiMatSubmodule i) :
              EuclideanSpace ℂ (p i.1 × p i.2)))
        A = ∑ i : ι × ι, ∑ j, ∑ s : (p i.1 × p i.2), ∑ l : (p i.1 × p i.2),
          --  in S i j, ∑ p in S i j,
          rankOne ℂ (Matrix.includeBlock
            (Matrix.vecMulVec (S i j s).1 (star (S i j l).1)))
            (modAut (- (1 / 2)) (Matrix.includeBlock
              ((Matrix.vecMulVec (S i j s).2 (star (S i j l).2))ᴴᵀ))) :=
by
  withPiQuantumCtx[φ]
  intro A hA S
  have hS : ∀ (i : ι × ι) j, (hA.PiMatOrthonormalBasis i j)
      = ∑ t, euclideanSpaceTensor' (R:=ℂ) ((S i j t).1 ⊗ₜ[ℂ] (S i j t).2) :=
    fun i j => EuclideanSpace.prodChoose_spec _
  apply_fun (QuantumSet.Psi 0 (1/2)) using LinearEquiv.injective _
  apply_fun
    (StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm).trans
    (PiMatTensorProductEquiv.trans PiMatToEuclideanLM)
  simp only [StarAlgEquiv.trans_apply]
  ext1 i
  apply_fun LinearMap.toContinuousLinearMap using LinearEquiv.injective _
  rw [← QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection hA i,
    OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (hA.PiMatOrthonormalBasis i)]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum,
    QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    StarAlgEquiv.lTensor_tmul,
    PiMatToEuclideanLM]
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply, one_div,
    starAlgebra.modAut_star, Finset.sum_apply, StarAlgEquiv.piCongrRight_apply,
    PiMatTensorProductEquiv_apply, StarAlgEquiv.ofAlgEquiv_coe, AlgEquiv.ofLinearEquiv_apply,
    map_sum, directSumTensorToFun_apply,
    PiMat.transposeStarAlgEquiv_symm_apply,
    MulOpposite.unop_op]
  simp only [TensorProduct.toKronecker_apply]
  simp only [QuantumSet.modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero]
  simp only [Matrix.includeBlock_conjTranspose, Matrix.conj_conjTranspose]
  conv_lhs =>
    rw [Finset.sum_congr rfl (by intro j _; rw [hS i j])]
  conv_rhs =>
    rw [Fintype.sum_eq_single i (fun j hj => by
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : j₁ = i.1
      · subst j₁
        have h₂ : j₂ ≠ i.2 := by
          intro h₂
          apply hj
          ext <;> simp [h₂]
        apply Fintype.sum_eq_zero
        intro q
        apply Fintype.sum_eq_zero
        intro s
        apply Fintype.sum_eq_zero
        intro t
        simp only [AlgEquiv.one_apply]
        exact PiMat_eq_right_block_miss h₂ _ _
      · apply Fintype.sum_eq_zero
        intro q
        apply Fintype.sum_eq_zero
        intro s
        apply Fintype.sum_eq_zero
        intro t
        exact PiMat_eq_left_block_miss h₁ _ _)]
  simp only [AlgEquiv.one_apply, Matrix.includeBlock_apply_same]
  simp only [map_sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply,
    Matrix.transpose_transpose, Matrix.vecMulVec_kronecker_vecMulVec]
  congr 1
  ext1
  rw [Finset.sum_comm]
  simp only [Finset.sum_product_univ,
    rankOne_euclideanSpaceTensor_eq_toEuclideanLin_vecMulVec]

noncomputable section deltaForm
variable {d : ℂ} [Nonempty ι] [hφ₂ : Fact (∀ i, (φ i).matrix⁻¹.trace = d)]
  [Π i, Nontrivial (p i)]

theorem QuantumGraph.trivialGraph :
  withPiQuantum[φ]
    letI : QuantumSetDeltaForm (PiMat ℂ ι p) := PiMat.quantumSetDeltaForm (d := d) (φ := φ)
    QuantumGraph _ (Qam.trivialGraph (PiMat ℂ ι p)) :=
by
  withPiQuantumCtx[φ]
  letI : QuantumSetDeltaForm (PiMat ℂ ι p) := PiMat.quantumSetDeltaForm (d := d) (φ := φ)
  exact ⟨Qam.Nontracial.TrivialGraph.qam⟩

omit [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
theorem PiMat.piAlgEquiv_trace_apply
  (f : (i : ι) → (Matrix (p i) (p i) ℂ ≃ₐ[ℂ] Matrix (p i) (p i) ℂ))
  (x : PiMat ℂ ι p) (a : ι) :
  ((AlgEquiv.piCongrRight f x) a).trace = (x a).trace :=
by
  calc (((AlgEquiv.piCongrRight f) x) a).trace
      = ((f a) (x a)).trace := rfl
    _ = (x a).trace := Matrix.aut_mat_inner_trace_preserving _ _

omit [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
omit [Fintype ι] [DecidableEq ι] in
theorem PiMat.modAut_trace_apply [Finite ι] :
  withPiQuantum[φ]
    ∀ (r : ℝ) (x : PiMat ℂ ι p) (a : ι), (modAut r x a).trace = (x a).trace :=
by
  classical
  letI := Fintype.ofFinite ι
  withPiQuantumCtx[φ]
  intro r x a
  exact PiMat.piAlgEquiv_trace_apply _ _ _

omit [Nonempty ι] [∀ (i : ι), Nontrivial (p i)] in
theorem PiMat.orthonormalBasis_trace :
  withPiQuantum[φ]
    ∀ (a : n (PiMat ℂ ι p)) (i : ι),
      (QuantumSet.onb (A := (PiMat ℂ ι p)) a i).trace =
        if a.1 = i then (hφ a.1).matrixIsPosDef.rpow (-(1 / 2)) a.2.2 a.2.1 else 0 :=
by
  withPiQuantumCtx[φ]
  intro a i
  calc (QuantumSet.onb (A := (PiMat ℂ ι p)) a i).trace
      = ∑ j, QuantumSet.onb (A := PiMat ℂ ι p) a i j j := rfl
    _ = ∑ j, (Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis hφ) a i j j := rfl
    _ = ∑ j, Matrix.includeBlock (Matrix.single a.2.1 a.2.2 1
      * (hφ a.1).matrixIsPosDef.rpow (-(1 / 2))) i j j
      := by simp only [Module.Dual.pi.IsFaithfulPosMap.orthonormalBasis_apply]
    _ = if a.1 = i then (hφ a.1).matrixIsPosDef.rpow (-(1 / 2)) a.2.2 a.2.1 else 0 :=
      by
        split
        next h =>
          subst h
          simp only [Matrix.includeBlock_apply, dif_pos]
          simp only [one_div, eq_mp_eq_cast, cast_eq]
          simp only [← Matrix.trace_iff, Matrix.single_hMul_trace]
        next h =>
          simp_all only [one_div, Matrix.includeBlock_apply]
          simp only [↓reduceDIte, Matrix.zero_apply, Finset.sum_const_zero]

open QuantumSet in
theorem QuantumGraph.trivialGraph_dimOfPiMatSubmodule :
  withPiQuantum[φ]
    letI : QuantumSetDeltaForm (PiMat ℂ ι p) := PiMat.quantumSetDeltaForm (d := d) (φ := φ)
    (QuantumGraph.trivialGraph :
      QuantumGraph _ (Qam.trivialGraph (PiMat ℂ ι p))).dimOfPiMatSubmodule =
        Fintype.card ι :=
by
  withPiQuantumCtx[φ]
  letI : QuantumSetDeltaForm (PiMat ℂ ι p) := PiMat.quantumSetDeltaForm (d := d) (φ := φ)
  rw [← Nat.cast_inj (R := ℂ)]
  rw [QuantumGraph.dimOfPiMatSubmodule_eq_trace, Qam.trivialGraph_eq]
  simp_rw [map_smul]
  rw [← rankOne.sum_orthonormalBasis_eq_id_lm (QuantumSet.onb)]
  simp only [map_sum, Psi_apply, PsiToFun_apply, StarAlgEquiv.lTensor_tmul,
    ]
  simp only [starAlgebra.modAut_zero, AlgEquiv.one_apply, one_div, starAlgebra.modAut_star,
    LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, Matrix.traceLinearMap_apply,
    smul_eq_mul]
  simp only [Matrix.blockDiagonal'AlgHom_apply, Matrix.trace_blockDiagonal']
  simp only [PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  simp only [Matrix.trace_transpose (R:=ℂ),
    PiMat.orthonormalBasis_trace, PiMat.modAut_trace_apply]
  simp only [Pi.star_apply, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    PiMat.orthonormalBasis_trace]
  simp only [ite_mul, zero_mul, star_ite, star_zero, mul_ite, mul_zero]
  simp only [Finset.sum_product_univ, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Matrix.conjTranspose_apply, (Matrix.PosDef.rpow.isPosDef _ _).1.eq]
  calc
    (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x : Σ i, p i × p i,
        (hφ x.1).matrixIsPosDef.rpow (-(1 / 2)) x.2.2 x.2.1
          * (hφ x.1).matrixIsPosDef.rpow (-(1 / 2)) x.2.1 x.2.2
    = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ∑ x_2, (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_2 x_1
        * (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_1 x_2 := by
      simp only [Finset.sum_sigma_univ, Finset.sum_product_univ]
    _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ∑ x_2, (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_1 x_2
        * (hφ x).matrixIsPosDef.rpow (-(1 / 2)) x_2 x_1 := by simp only [mul_comm]
    _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
      ∑ x, ∑ x_1, ((hφ x).matrixIsPosDef.rpow (-(1 / 2)) *
        (hφ x).matrixIsPosDef.rpow (-(1 / 2))) x_1 x_1 := by simp only [← Matrix.mul_apply]
    _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
        ∑ x, (φ x).matrix⁻¹.trace := by
      simp only [Matrix.PosDef.rpow_mul_rpow, Matrix.trace_iff]
      ring_nf
      simp only [Matrix.PosDef.rpow_neg_one_eq_inv_self]
    _ = (QuantumSetDeltaForm.delta (PiMat ℂ ι p))⁻¹ *
    ∑ _ : ι, (QuantumSetDeltaForm.delta (PiMat ℂ ι p)) := by
      simp only [(Fact.out : ∀ i, (φ i).matrix⁻¹.trace = d)]
      rfl
    _ = Fintype.card ι := by
      rw [Finset.sum_const, mul_smul_comm, inv_mul_cancel₀ (ne_of_gt QuantumSetDeltaForm.delta_pos)]
      rw [nsmul_eq_mul, mul_one]
      rfl

end deltaForm

theorem StarAlgEquiv.piCongrRight_symm {R ι : Type*} {A₁ A₂ : ι → Type*}
  [(i : ι) → Add (A₁ i)] [(i : ι) → Add (A₂ i)] [(i : ι) → Mul (A₁ i)] [(i : ι) → Mul (A₂ i)]
  [(i : ι) → Star (A₁ i)] [(i : ι) → Star (A₂ i)] [(i : ι) → SMul R (A₁ i)] [(i : ι) →
    SMul R (A₂ i)]
  (e : (i : ι) → A₁ i ≃⋆ₐ[R] A₂ i) :
  (StarAlgEquiv.piCongrRight e).symm = StarAlgEquiv.piCongrRight (fun i => (e i).symm) :=
rfl

theorem Matrix.k {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [φ.IsFaithfulPosMap] :
  withMatrixQuantum[φ]
    k (Matrix n n ℂ) = 0 :=
rfl

theorem unitary.mul_inv_eq_iff {A : Type*} [Monoid A] [StarMul A] (U : ↥(unitary A))
    (x : A) (y : A) : x * (U⁻¹ : unitary A) = y ↔ x = y * U :=
  by
    rw [unitary.inj_hMul (U : unitary A), mul_assoc]
    rw [← Unitary.star_eq_inv]
    simp only [Unitary.coe_star, SetLike.coe_mem, Unitary.star_mul_self_of_mem, mul_one]

/-- Blockwise inner automorphism of a `PiMat`. -/
noncomputable abbrev piInnerAut (U : (i : ι) → Matrix.unitaryGroup (p i) ℂ) :
  PiMat ℂ ι p ≃⋆ₐ[ℂ] PiMat ℂ ι p :=
(StarAlgEquiv.piCongrRight (fun i => Matrix.innerAutStarAlg (U i)))

omit hφ in
theorem piInnerAut_apply_dualMatrix_iff' {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} :
  piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ ↔
  ∀ i, Matrix.innerAutStarAlg (U i) (φ i).matrix = (φ i).matrix :=
by
  simp only [funext_iff, StarAlgEquiv.piCongrRight_apply,
    Module.Dual.pi.matrixBlock_apply]

omit hφ in
theorem piInnerAut_apply_dualMatrix_iff {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} :
  piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ ↔
    ∀ (a : ι), (U a) * (φ a).matrix = (φ a).matrix * (U a) :=
by
  simp only [piInnerAut_apply_dualMatrix_iff', Matrix.innerAutStarAlg_apply']
  simp_rw [unitary.mul_inv_eq_iff]

example :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p ≃⋆ₐ[ℂ] PiMat ℂ ι p},
      @Isometry (PiMat ℂ ι p) (PiMat ℂ ι p)
          (@EMetricSpace.toPseudoEMetricSpace (PiMat ℂ ι p)
            (@MetricSpace.toEMetricSpace (PiMat ℂ ι p) InnerProductAlgebra.toMetricSpace))
          (@EMetricSpace.toPseudoEMetricSpace (PiMat ℂ ι p)
            (@MetricSpace.toEMetricSpace (PiMat ℂ ι p) InnerProductAlgebra.toMetricSpace))
          f ↔
        LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap :=
by
  withPiQuantumCtx[φ]
  intro f
  exact QuantumSet.starAlgEquiv_isometry_iff_adjoint_eq_symm

theorem innerAutStarAlg_adjoint_eq_symm_of :
  withPiQuantum[φ]
    ∀ {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ},
      piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ →
        LinearMap.adjoint (piInnerAut U).toLinearMap = (piInnerAut U).symm.toLinearMap :=
by
  withPiQuantumCtx[φ]
  intro U hU
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [LinearMap.adjoint_inner_right, StarAlgEquiv.toLinearMap_apply]
  rw [piInnerAut_apply_dualMatrix_iff] at hU
  simp only [Module.Dual.pi.IsFaithfulPosMap.inner_eq' (ψ := φ),
    StarAlgEquiv.piCongrRight_apply (R := ℂ), StarAlgEquiv.piCongrRight_symm,
    Matrix.innerAutStarAlg_apply, Matrix.innerAutStarAlg_symm_apply, Matrix.conjTranspose_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.unitaryGroup.star_coe_eq_coe_star (U i)]
  have hstarU :
      star (U i : Matrix (p i) (p i) ℂ) = (U i : Matrix (p i) (p i) ℂ)ᴴ :=
    rfl
  rw [hstarU, Matrix.conjTranspose_conjTranspose]
  change
    (((φ i).matrix *
          ((U i : Matrix (p i) (p i) ℂ) *
            ((y i)ᴴ * (U i : Matrix (p i) (p i) ℂ)ᴴ)) *
        x i).trace) =
      (((φ i).matrix * (y i)ᴴ *
          ((U i : Matrix (p i) (p i) ℂ)ᴴ * x i * U i)).trace)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [← hU i]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (U i : Matrix (p i) (p i) ℂ)
    ((φ i).matrix * ((y i)ᴴ * ((U i : Matrix (p i) (p i) ℂ)ᴴ * x i)))]
  simp only [Matrix.mul_assoc]

/-- Real quantum graphs on `PiMat` are preserved by blockwise unitary conjugation. -/
theorem QuantumGraph.Real.piMat_conj_unitary :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph.Real (PiMat ℂ ι p) A →
        ∀ {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ},
          piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ →
            QuantumGraph.Real _
              ((piInnerAut U).toLinearMap ∘ₗ A ∘ₗ
                LinearMap.adjoint (piInnerAut U).toLinearMap) :=
by
  withPiQuantumCtx[φ]
  intro A hA U hU
  constructor
  · rw [← StarAlgEquiv.toAlgEquiv_toAlgHom_toLinearMap,
      QuantumSet.schurMul_algHom_comp_algHom_adjoint, hA.1]
  · have hadj := innerAutStarAlg_adjoint_eq_symm_of hU
    simp_rw [hadj]
    change LinearMap.IsReal
      ((piInnerAut U).toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ (piInnerAut U).symm.toAlgEquiv.toLinearMap)
    exact (LinearMap.real_starAlgEquiv_conj_iff A (piInnerAut U)).mpr hA.isReal

/-- A unitary matrix as a linear equivalence of Euclidean space. -/
noncomputable abbrev Matrix.UnitaryGroup.toEuclideanLinearEquiv {n :
    Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) :
    EuclideanSpace ℂ n ≃ₗ[ℂ] EuclideanSpace ℂ n :=
(WithLp.linearEquiv 2 ℂ (n → ℂ)).trans
  ((Matrix.UnitaryGroup.toLinearEquiv A).trans
    (WithLp.linearEquiv 2 ℂ (n → ℂ)).symm)
theorem Matrix.UnitaryGroup.toEuclideanLinearEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (v : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearEquiv A) v =
    WithLp.toLp 2 ((A : Matrix n n ℂ) *ᵥ v.ofLp) :=
rfl

/-- A unitary matrix as a linear isometry equivalence of Euclidean space. -/
noncomputable def Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv {n :
    Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) :
    EuclideanSpace ℂ n ≃ₗᵢ[ℂ] EuclideanSpace ℂ n where
  toLinearEquiv := Matrix.UnitaryGroup.toEuclideanLinearEquiv A
  norm_map' x := by
    change
      ‖((EuclideanSpace.equiv n ℂ).symm ((A : Matrix n n ℂ) *ᵥ x) :
          EuclideanSpace ℂ n)‖ = ‖x‖
    calc
      ‖((EuclideanSpace.equiv n ℂ).symm ((A : Matrix n n ℂ) *ᵥ x) :
          EuclideanSpace ℂ n)‖
        = √ (RCLike.re ((star ((A : Matrix n n ℂ) *ᵥ x)) ⬝ᵥ ((A : Matrix n n ℂ) *ᵥ x))) := ?_
      _ = √ (RCLike.re ((star x) ⬝ᵥ (((star (A : Matrix n n ℂ) * (A : Matrix n n ℂ)) *ᵥ x)))) := ?_
      _ = ‖x‖ := ?_
    · rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), dotProduct_eq_inner]
      rfl
    · rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
      rfl
    · rw [Matrix.UnitaryGroup.star_mul_self A, one_mulVec,
        norm_eq_sqrt_re_inner (𝕜 := ℂ), dotProduct_eq_inner]
      rfl

theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply {n :
    Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A) x =
    WithLp.toLp 2 ((A : Matrix n n ℂ) *ᵥ x.ofLp) :=
rfl
theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_symm_apply {n :
    Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A).symm x =
    WithLp.toLp 2 (((A⁻¹ : unitaryGroup n ℂ) : Matrix n n ℂ) *ᵥ x.ofLp) :=
rfl
theorem Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply' {n :
    Type*} [Fintype n] [DecidableEq n]
  (A : ↥(Matrix.unitaryGroup n ℂ)) (x : EuclideanSpace ℂ n) :
  (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv A).symm x =
    WithLp.toLp 2 ((A : Matrix n n ℂ)ᴴ *ᵥ x.ofLp) :=
rfl

/-- Tensor-product Euclidean isometry induced by a pair of blockwise unitaries. -/
noncomputable abbrev unitaryTensorEuclidean (U : (i : ι) → Matrix.unitaryGroup (p i) ℂ) (i :
    ι × ι) :=
(euclideanSpaceTensor'.symm.trans
    ((LinearIsometryEquiv.TensorProduct.map (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv
      (U i.1))
      (Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv (Matrix.unitaryGroup.conj (U i.2)))).trans
    euclideanSpaceTensor'))

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_apply {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i :
    ι × ι) (x : EuclideanSpace ℂ (p i.1)) (y : EuclideanSpace ℂ (p i.2)) :
  (unitaryTensorEuclidean U i) (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ y))
    = euclideanSpaceTensor' (R := ℂ)
      ((WithLp.toLp 2 ((U i.1 : Matrix _ _ ℂ) *ᵥ x.ofLp)) ⊗ₜ
        WithLp.toLp 2 ((U i.2 : Matrix _ _ ℂ)ᴴᵀ *ᵥ y.ofLp)) :=
by
  rw [unitaryTensorEuclidean, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_apply' {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i :
    ι × ι) (x : EuclideanSpace ℂ (p i.1 × p i.2)) :
  (unitaryTensorEuclidean U i) x
    = ∑ j : p i.1 × p i.2, euclideanSpaceTensor' (R := ℂ)
      ((WithLp.toLp 2 ((U i.1 : Matrix _ _ ℂ) *ᵥ (x.prodChoose j).1.ofLp)) ⊗ₜ[ℂ]
        WithLp.toLp 2 ((U i.2 : Matrix _ _ ℂ)ᴴᵀ *ᵥ (x.prodChoose j).2.ofLp)) :=
by
  simp only [← unitaryTensorEuclidean_apply]
  rw [← map_sum, ← EuclideanSpace.prodChoose_spec]

omit [Fintype ι] [DecidableEq ι] in
theorem unitaryTensorEuclidean_symm_apply {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} (i :
    ι × ι) (x : EuclideanSpace ℂ (p i.1)) (y : EuclideanSpace ℂ (p i.2)) :
  (unitaryTensorEuclidean U i).symm (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ y))
    = euclideanSpaceTensor' (R := ℂ)
      ((WithLp.toLp 2 (((U i.1)ᴴ : Matrix _ _ ℂ) *ᵥ x.ofLp)) ⊗ₜ
        WithLp.toLp 2 (((U i.2)ᵀ : Matrix _ _ ℂ) *ᵥ y.ofLp)) :=
by
  simp_rw [unitaryTensorEuclidean, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simp only [LinearIsometryEquiv.piLpCongrRight_symm, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.TensorProduct.map_symm_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      EmbeddingLike.apply_eq_iff_eq]
  apply congrArg₂ (fun a b => a ⊗ₜ[ℂ] b)
  · exact Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply' (U i.1) x
  · simpa [Matrix.unitaryGroup.conj_coe, Matrix.conj_conjTranspose] using
      Matrix.UnitaryGroup.toEuclideanLinearIsometryEquiv_apply'
        (Matrix.unitaryGroup.conj (U i.2)) y

theorem QuantumGraph.Real.PiMatSubmodule_eq_submodule_iff :
  withPiQuantum[φ]
    ∀ {A B : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) →
        (hB : QuantumGraph.Real (PiMat ℂ ι p) B) →
          (∀ i, hA.PiMatSubmodule i = hB.PiMatSubmodule i) ↔ A = B :=
by
  intro A B hA hB
  simp_rw [Submodule.eq_iff_orthogonalProjection_eq, ← ContinuousLinearMap.coe_inj,
    QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection]
  simp only [StarAlgEquiv.piCongrRight_apply,
    PiMatTensorProductEquiv_apply, StarAlgEquiv.ofAlgEquiv_coe, AlgEquiv.ofLinearEquiv_apply,
    LinearMap.coe_toContinuousLinearMap, EmbeddingLike.apply_eq_iff_eq,
    ← tensorToKronecker_apply, ← directSumTensor_apply]
  simp only [← funext_iff, EmbeddingLike.apply_eq_iff_eq]

theorem Matrix.kronecker_mulVec_euclideanSpaceTensor' {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] (A : Matrix n n ℂ) (B : Matrix m m ℂ) (x : EuclideanSpace ℂ n)
  (y : EuclideanSpace ℂ m) :
  (A ⊗ₖ B) *ᵥ ((WithLp.equiv 2 _) (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)))
    = WithLp.equiv 2 _ (euclideanSpaceTensor' (R := ℂ)
      ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ (WithLp.toLp 2 (B *ᵥ y.ofLp)))) :=
by
  ext a
  simp only [Matrix.mulVec, dotProduct, kroneckerMap_apply, WithLp.equiv]
  calc
    ∑ x_1 : n × m,
    A a.1 x_1.1 * B a.2 x_1.2 * (Equiv.refl (WithLp 2 (n × m →
      ℂ))) (euclideanSpaceTensor' (R:=ℂ) (x ⊗ₜ[ℂ] y)) x_1
      = ∑ x_1, A a.1 x_1.1 * B a.2 x_1.2 * ((euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y)) x_1) := rfl
    _ = ∑ x_1 : n × m, A a.1 x_1.1 * B a.2 x_1.2 * (x x_1.1 * y x_1.2) := by
      simp only [euclideanSpaceTensor'_apply]
    _ = (euclideanSpaceTensor' (R := ℂ)
        ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ[ℂ] (WithLp.toLp 2 (B *ᵥ y.ofLp)))) a := ?_
    _ = (Equiv.refl (WithLp 2 (n × m → ℂ))) (euclideanSpaceTensor' (R := ℂ)
        ((WithLp.toLp 2 (A *ᵥ x.ofLp)) ⊗ₜ[ℂ] (WithLp.toLp 2 (B *ᵥ y.ofLp)))) a := rfl
  rw [euclideanSpaceTensor'_apply]
  simp_rw [mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, Finset.sum_product_univ, mul_assoc]
  congr; ext; congr; ext
  ring_nf

theorem StarAlgEquiv.piCongrRight_apply_includeBlock {ι : Type*}
  {p : ι → Type*} [∀ i, Fintype (p i)] [DecidableEq ι]
  (f : Π i, Matrix (p i) (p i) ℂ ≃⋆ₐ[ℂ] Matrix (p i) (p i) ℂ)
  (i : ι) (x : Matrix (p i) (p i) ℂ) :
  (StarAlgEquiv.piCongrRight (fun a => f a)) (Matrix.includeBlock x)
    = Matrix.includeBlock ((f i) x) :=
by
  ext
  simp only [piCongrRight_apply, Matrix.includeBlock_apply]
  aesop

theorem Matrix.innerAutStarAlg_apply_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x y) = vecMulVec (U *ᵥ x) (Uᴴᵀ *ᵥ y) :=
by
  simp only [innerAutStarAlg_apply, Unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose]
  rw [← Matrix.mulVec_transpose]
  rfl
theorem Matrix.innerAutStarAlg_apply_vecMulVec_star {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec x (star y))
    = vecMulVec (U *ᵥ x) (star (U *ᵥ y)) :=
by
  simp only [innerAutStarAlg_apply, Unitary.coe_star, mul_vecMulVec, vecMulVec_mul,
    star_eq_conjTranspose, star_mulVec]
theorem Matrix.innerAutStarAlg_apply_star_vecMulVec {n 𝕜 : Type*} [Fintype n] [Field 𝕜] [StarRing 𝕜]
  [DecidableEq n] (U : ↥(Matrix.unitaryGroup n 𝕜)) (x y : n → 𝕜) :
  (Matrix.innerAutStarAlg U) (vecMulVec (star x) y)
    = (vecMulVec (Uᴴᵀ *ᵥ x) (star (Uᴴᵀ *ᵥ y)))ᴴᵀ :=
by
  rw [innerAutStarAlg_apply_vecMulVec, vecMulVec_conj, star_star, star_mulVec]
  rw [← vecMul_transpose, conj_conjTranspose]

theorem Matrix.PosSemidef.eq_iff_sq_eq_sq {n : Type*} [Fintype n]
  [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosSemidef) {B : Matrix n n ℂ}
  (hB : B.PosSemidef) :
    A ^ 2 = B ^ 2 ↔ A = B :=
by
  letI : Algebra ℝ ℂ := RCLike.toNormedAlgebra.toAlgebra
  haveI : NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    ContinuousFunctionalCalculus.toNonUnital
  haveI : NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
    Matrix.instNonnegSpectrumClass (n := n) (𝕜 := ℂ)
  simpa [pow_two] using (CFC.mul_self_eq_mul_self_iff A B hA.nonneg hB.nonneg)

omit [Fintype ι] [DecidableEq ι] in
theorem innerAutStarAlg_apply_dualMatrix_eq_iff_eq_sqrt {i : ι}
  (U : Matrix.unitaryGroup (p i) ℂ) :
  (Matrix.innerAutStarAlg U) (φ i).matrix = (φ i).matrix
    ↔ (Matrix.innerAutStarAlg U) ((hφ i).matrixIsPosDef.rpow (1 / 2))
      = (hφ i).matrixIsPosDef.rpow (1 / 2) :=
by
  simp_rw [Matrix.innerAutStarAlg_apply_eq_innerAut_apply]
  rw [← Matrix.PosSemidef.eq_iff_sq_eq_sq (Matrix.posDef_innerAut
      (Matrix.PosDef.rpow.isPosDef _ _) _).posSemidef
      (Matrix.PosDef.rpow.isPosDef _ _).posSemidef,
    Matrix.innerAut.map_pow]
  simp_rw [pow_two, Matrix.PosDef.rpow_mul_rpow, add_halves, Matrix.PosDef.rpow_one_eq_self]

omit [Fintype ι] [DecidableEq ι] in
theorem PiMat.modAut [Finite ι] :
  withPiQuantum[φ]
    ∀ (r : ℝ) (x : PiMat ℂ ι p) (i : ι),
      modAut r x i = sig (hφ i) r (x i) :=
by
  classical
  letI := Fintype.ofFinite ι
  withPiQuantumCtx[φ]
  intro r x i
  rfl

theorem Matrix.counit_eq_dual {n : Type*} [Fintype n] [DecidableEq n]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} [φ.IsFaithfulPosMap] :
  withMatrixQuantum[φ]
    Coalgebra.counit (R := ℂ) (A := Matrix n n ℂ) = φ :=
by
  withMatrixQuantumCtx[φ]
  ext
  simp only [← Coalgebra.inner_eq_counit']
  rw [@Module.Dual.IsFaithfulPosMap.inner_eq, conjTranspose_one, one_mul]

omit [DecidableEq ι] in
theorem PiMat.counit_eq_dual :
  letI : DecidableEq ι := Classical.decEq ι
  withPiQuantum[φ]
    (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) = Module.Dual.pi φ :=
by
  classical
  withPiQuantumCtx[φ]
  apply LinearMap.ext
  intro x
  rw [← congrFun (QuantumSet.inner_eq_counit' (B := PiMat ℂ ι p)) x]
  rw [Module.Dual.pi.IsFaithfulPosMap.inner_eq, star_one, one_mul]

omit [DecidableEq ι] in
theorem modAut_eq_id_iff :
  letI : DecidableEq ι := Classical.decEq ι
  withPiQuantum[φ]
    ∀ r : ℝ,
      (modAut r : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p) = 1
        ↔ r = 0 ∨ Module.Dual.IsTracial
          (Coalgebra.counit (R := ℂ) (A := PiMat ℂ ι p)) :=
by
  classical
  withPiQuantumCtx[φ]
  intro r
  rw [PiMat.counit_eq_dual]
  calc (modAut r : PiMat ℂ ι p ≃ₐ[ℂ] PiMat ℂ ι p) = 1
      ↔ ∀ i, sig (hφ i) r = 1 := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply, funext_iff, PiMat.modAut,
          sig_apply]
        constructor
        · intro h i a
          simpa [Matrix.includeBlock_apply_same] using h (Matrix.includeBlock a) i
        · intro h a i
          exact h i (a i)
    _ ↔ r = 0 ∨ Module.Dual.IsTracial (Module.Dual.pi φ) := by
      simp_rw [sig_eq_id_iff, forall_or_left, Module.Dual.pi_isTracial_iff]

theorem unitary.mul_inj {A : Type*} [Monoid A] [StarMul A] (U : ↥(unitary A)) (x y : A) :
  ↑U * x = ↑U * y ↔ x = y :=
by
  rw [← Unitary.val_toUnits_apply]
  exact (Units.mul_right_inj (Unitary.toUnits U))

omit [Fintype ι] [DecidableEq ι] in
theorem piInnerAut_modAut_commutes_of [Finite ι] :
  withPiQuantum[φ]
    ∀ {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ} {r : ℝ},
      (∀ i, (Matrix.innerAutStarAlg (U i)) ((hφ i).matrixIsPosDef.rpow r)
        = (hφ i).matrixIsPosDef.rpow r) →
        ∀ x, (piInnerAut U) ((modAut (-r)) x) = (modAut (-r)) ((piInnerAut U) x) :=
by
  intro U r h
  simp only [Matrix.innerAutStarAlg_apply', unitary.mul_inv_eq_iff] at h
  intro x
  funext i
  classical
  letI := Fintype.ofFinite ι
  simp only [StarAlgEquiv.piCongrRight_apply, Unitary.conjStarAlgAut_apply]
  rw [PiMat.modAut, PiMat.modAut]
  simp only [piInnerAut, StarAlgEquiv.piCongrRight_apply, Unitary.conjStarAlgAut_apply,
    sig_apply, neg_neg]
  let R := (hφ i).matrixIsPosDef.rpow r
  let Rn := (hφ i).matrixIsPosDef.rpow (-r)
  let Umat : Matrix (p i) (p i) ℂ := U i
  let SU : Matrix (p i) (p i) ℂ := star Umat
  change Umat * (R * x i * Rn) * SU = R * (Umat * x i * SU) * Rn
  have hcomm : Umat * R = R * Umat := by
    simpa [Umat, R] using h i
  have hUR : SU * Umat = 1 := by
    dsimp [SU, Umat]
    exact Matrix.UnitaryGroup.star_mul_self (U i)
  have hRU : Umat * SU = 1 := by
    dsimp [SU, Umat]
    exact Matrix.unitaryGroup.coe_hMul_star_self (U i)
  have hRinv : Rn = R⁻¹ := by
    simp [Rn, R, Matrix.PosDef.rpow_neg_eq_inv_rpow]
  letI := (Matrix.PosDef.rpow.isPosDef (hφ i).matrixIsPosDef r).invertible
  have hcommSU : R * SU = SU * R := by
    calc
      R * SU = (SU * Umat) * (R * SU) := by rw [hUR, one_mul]
      _ = SU * (Umat * R) * SU := by noncomm_ring
      _ = SU * (R * Umat) * SU := by rw [hcomm]
      _ = (SU * R) * (Umat * SU) := by noncomm_ring
      _ = SU * R := by rw [hRU, mul_one]
  have hcommInv : Rn * SU = SU * Rn := by
    rw [hRinv]
    rw [← Matrix.mul_right_inj_of_invertible (A := R)]
    calc
      R * (R⁻¹ * SU) = SU := by
        rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, one_mul]
      _ = (SU * R) * R⁻¹ := by rw [Matrix.mul_inv_cancel_right_of_invertible]
      _ = (R * SU) * R⁻¹ := by rw [hcommSU]
      _ = R * (SU * R⁻¹) := by rw [Matrix.mul_assoc]
  calc
    Umat * (R * x i * Rn) * SU = (Umat * R) * x i * (Rn * SU) := by
      noncomm_ring
    _ = (R * Umat) * x i * (Rn * SU) := by rw [hcomm]
    _ = (R * Umat) * x i * (SU * Rn) := by rw [hcommInv]
    _ = R * (Umat * x i * SU) * Rn := by noncomm_ring

theorem QuantumGraph.Real.PiMat_applyConjInnerAut :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) →
        ∀ {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ},
          piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ →
          let S : (i : ι × ι) →
            (j : (Fin (Module.finrank ℂ (hA.PiMatSubmodule i)))) →
              (((p i.1) × (p i.2)) →
                (((EuclideanSpace ℂ (p i.1)) × (EuclideanSpace ℂ (p i.2)))))
            := fun i j => (hA.PiMatOrthonormalBasis i j : EuclideanSpace ℂ _).prodChoose
          (piInnerAut U).toLinearMap ∘ₗ A ∘ₗ LinearMap.adjoint (piInnerAut U).toLinearMap
            = ∑ i : ι × ι, ∑ j, ∑ s : (p i.1 × p i.2), ∑ l : (p i.1 × p i.2),
            rankOne ℂ (Matrix.includeBlock
              (Matrix.vecMulVec ((U i.1 : Matrix (p i.1) (p i.1) ℂ) *ᵥ (S i j s).1)
                (star ((U i.1 : Matrix (p i.1) (p i.1) ℂ) *ᵥ (S i j l).1))))
              (modAut (- (1 / 2)) (Matrix.includeBlock
                ((Matrix.vecMulVec ((U i.2 : Matrix (p i.2) (p i.2) ℂ)ᴴᵀ *ᵥ (S i j s).2)
                  (star ((U i.2 : Matrix (p i.2) (p i.2) ℂ)ᴴᵀ *ᵥ (S i j l).2)))ᴴᵀ))) :=
by
  withPiQuantumCtx[φ]
  intro A hA U hU S
  simp_rw [piInnerAut_apply_dualMatrix_iff', innerAutStarAlg_apply_dualMatrix_eq_iff_eq_sqrt] at hU
  have hU₂ := piInnerAut_modAut_commutes_of hU
  nth_rw 1 [QuantumGraph.Real.PiMat_eq hA]
  simp only [piInnerAut] at hU₂ ⊢
  simp only [ContinuousLinearMap.toLinearMap_sum, LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, StarAlgEquiv.toLinearMap_apply, hU₂]
  repeat apply Finset.sum_congr rfl; intro _ _
  congr 2
  · rw [StarAlgEquiv.piCongrRight_apply_includeBlock, Matrix.innerAutStarAlg_apply_vecMulVec_star]
  · rw [StarAlgEquiv.piCongrRight_apply_includeBlock, Matrix.vecMulVec_conj, star_star,
    Matrix.innerAutStarAlg_apply_star_vecMulVec]

open QuantumSet in
theorem QuantumGraph.Real.PiMat_conj_unitary_submodule_eq_map :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) →
        ∀ {U : (i : ι) → Matrix.unitaryGroup (p i) ℂ},
          (hU : piInnerAut U (Module.Dual.pi.matrixBlock φ) = Module.Dual.pi.matrixBlock φ) →
            ∀ i : ι × ι,
              QuantumGraph.Real.PiMatSubmodule (hA.piMat_conj_unitary hU) i =
                Submodule.map (unitaryTensorEuclidean U i).toLinearMap (hA.PiMatSubmodule i) :=
by
  withPiQuantumCtx[φ]
  intro A hA U hU i
  rw [Submodule.eq_iff_orthogonalProjection_eq, ← ContinuousLinearMap.coe_inj]
  rw [orthogonalProjection_submoduleMap]
  nth_rw 1 [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne (hA.PiMatOrthonormalBasis i)]
  simp_rw [QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection]
  rw [QuantumGraph.Real.PiMat_applyConjInnerAut hA hU]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, Psi_apply, PsiToFun_apply,
    Finset.sum_apply, StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul, PiMatToEuclideanLM,
      StarAlgEquiv.piCongrRight_apply]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum]
  simp only [modAut_apply_modAut, add_neg_cancel, starAlgebra.modAut_zero, AlgEquiv.one_apply,
    PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  simp only [LinearMap.comp_rankOne, LinearMap.rankOne_comp, LinearIsometryEquiv.linearMap_adjoint,
    LinearIsometryEquiv.symm_symm]
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_toLinearMap,
    LinearMap.coe_toContinuousLinearMap, unitaryTensorEuclidean_apply']
  simp only [Matrix.includeBlock_apply, Matrix.dite_kronecker, Pi.star_apply, star_zero,
    apply_dite, Matrix.transpose_zero,
    map_zero, Matrix.kronecker_zero]
  rw [Fintype.sum_eq_single i]
  · simp only [↓reduceDIte]
    simp only [
      eq_mp_eq_cast, cast_eq,
      Matrix.star_eq_conjTranspose, Matrix.conj_conjTranspose,
      Matrix.transpose_transpose, Matrix.vecMulVec_kronecker_vecMulVec,
      Matrix.toEuclideanStarAlgEquiv_coe]
    congr
    ext
    simp only [rankOne_lm_sum_sum]
    simp only [rankOne_euclideanSpaceTensor_eq_toEuclideanLin_vecMulVec]
    simp only [LinearMap.coe_toContinuousLinearMap]
  · intro x hx
    apply Finset.sum_eq_zero
    intro x_1 _
    apply Finset.sum_eq_zero
    intro x_2 _
    apply Finset.sum_eq_zero
    intro x_3 _
    rcases x with ⟨x₁, x₂⟩
    by_cases h₂ : x₂ = i.2
    · by_cases h₁ : x₁ = i.1
      · exfalso
        apply hx
        ext <;> assumption
      · simp [h₂, h₁]
    · simp [h₂]

theorem orthogonalProjection'_bot {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] :
  orthogonalProjection' (⊥ : Submodule 𝕜 E) = 0 :=
by simp

omit [Fintype ι] [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)] in
lemma LinearMap.proj_apply_includeBlock
  (i j : ι) (x : Matrix (p j) (p j) ℂ) :
  LinearMap.proj (R := ℂ) i (Matrix.includeBlock (i := j) x) =
    if h : j = i then by rw [← h]; exact x else 0 :=
by simp [Matrix.includeBlock_apply]

omit [Fintype ι] in
lemma _root_.PiMat.modAut_includeBlock [Finite ι] :
  withPiQuantum[φ]
    ∀ (r : ℝ) (j : ι) (x : Matrix (p j) (p j) ℂ),
      (modAut r) (Matrix.includeBlock x)
        = (letI : starAlgebra (Matrix (p j) (p j) ℂ) := Matrix.isStarAlgebra (φ := φ j);
          Matrix.includeBlock
            ((modAut r : Matrix (p j) (p j) ℂ ≃ₐ[ℂ] Matrix (p j) (p j) ℂ) x)) :=
by
  classical
  letI := Fintype.ofFinite ι
  withPiQuantumCtx[φ]
  intro r j x
  ext i
  by_cases h : j = i
  · subst i
    simp [Matrix.includeBlock_apply_same, modAut, sig_apply]
  · simp [PiMat.modAut, Matrix.includeBlock_apply_ne_same _ h]

omit [Fintype ι] [DecidableEq ι] in
lemma _root_.PiMat.modAut_proj [Finite ι] :
  withPiQuantum[φ]
    ∀ (r : ℝ) (j : ι) (x : PiMat ℂ ι p),
      (letI : starAlgebra (Matrix (p j) (p j) ℂ) := Matrix.isStarAlgebra (φ := φ j);
        ((modAut r : Matrix (p j) (p j) ℂ ≃ₐ[ℂ] Matrix (p j) (p j) ℂ)
          (LinearMap.proj (R := ℂ) j x)))
        = LinearMap.proj (R := ℂ) j (modAut r x) :=
by
  classical
  letI := Fintype.ofFinite ι
  withPiQuantumCtx[φ]
  intro r j x
  change sig (hφ j) r (x j) = modAut r x j
  rw [PiMat.modAut]

lemma EuclideanSpace.prodChoose_zero_fst
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (i : n × m) :
  ((0 : EuclideanSpace ℂ (n × m)).prodChoose i).1 = 0 :=
by
  simp only [EuclideanSpace.prodChoose, LinearIsometryEquiv.map_zero]
  simp

open scoped Kronecker

theorem QuantumGraph.Real.PiMatSubmodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero :
  withPiQuantum[φ]
    letI : ∀ i, _root_.NormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
      fun i => Module.Dual.NormedAddCommGroup (φ i)
    letI : ∀ i, _root_.TopologicalSpace (Matrix (p i) (p i) ℂ) :=
      fun i => (Module.Dual.NormedAddCommGroup (φ
        i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : ∀ i, _root_.SeminormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
      fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup
    letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (p i) (p i) ℂ) :=
      fun i => Module.Dual.InnerProductSpace (φ := φ i)
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real _ A) → ∀ {i : ι × ι},
        hA.PiMatSubmodule i = ⊥ ↔
          (LinearMap.proj (R := ℂ) i.1 :
              PiMat ℂ ι p →ₗ[ℂ] Mat ℂ (p i.1)) ∘ₗ A ∘ₗ
            LinearMap.adjoint
              (LinearMap.proj (R := ℂ) i.2 :
                PiMat ℂ ι p →ₗ[ℂ] Mat ℂ (p i.2)) = 0 :=
by
  withPiQuantumCtx[φ]
  letI : ∀ i, _root_.starAlgebra (Matrix (p i) (p i) ℂ) :=
    fun i => Matrix.isStarAlgebra (φ := φ i)
  letI : ∀ i, _root_.QuantumSet (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i)
  letI : ∀ i, _root_.NormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.NormedAddCommGroup (φ i)
  letI : ∀ i, _root_.TopologicalSpace (Matrix (p i) (p i) ℂ) :=
    fun i => (Module.Dual.NormedAddCommGroup (φ
      i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : ∀ i, _root_.SeminormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
    fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup
  letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.InnerProductSpace (φ := φ i)
  intro A hA i
  rw [Submodule.eq_iff_orthogonalProjection_eq, orthogonalProjection'_bot,
    QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp only [map_sum, Finset.sum_apply, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul, PiMatToEuclideanLM,
      StarAlgEquiv.piCongrRight_apply]
  rw [← map_sum, LinearEquiv.map_eq_zero_iff,
    ← map_sum, StarAlgEquiv.map_eq_zero_iff]
  simp only [PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  rw [← Function.Injective.eq_iff (QuantumSet.Psi 0 (1/2)).injective,
    ← Function.Injective.eq_iff (AlgEquiv.lTensor _ (Matrix.transposeAlgEquiv _ _
      _).symm).injective,
    ← Function.Injective.eq_iff tensorToKronecker.injective]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, map_sum,
    QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, AlgEquiv.lTensor_tmul,
    Matrix.transposeAlgEquiv_symm_op_apply, PiMat.modAut_proj,
    tensorToKronecker_apply, TensorProduct.toKronecker_apply, map_zero]
  rfl

theorem QuantumGraph.Real.PiMatSubmodule_eq_top_iff_proj_comp_adjoint_proj_eq_rankOne_one_one :
  withPiQuantum[φ]
    letI : ∀ i, _root_.NormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
      fun i => Module.Dual.NormedAddCommGroup (φ i)
    letI : ∀ i, _root_.TopologicalSpace (Matrix (p i) (p i) ℂ) :=
      fun i => (Module.Dual.NormedAddCommGroup (φ
        i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : ∀ i, _root_.SeminormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
      fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup
    letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (p i) (p i) ℂ) :=
      fun i => Module.Dual.InnerProductSpace (φ := φ i)
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hA : QuantumGraph.Real _ A) →
      ∀ {i : ι × ι},
        hA.PiMatSubmodule i = ⊤ ↔
          (LinearMap.proj (R := ℂ) i.1 :
              PiMat ℂ ι p →ₗ[ℂ] Mat ℂ (p i.1)) ∘ₗ A ∘ₗ
            LinearMap.adjoint
              (LinearMap.proj (R := ℂ) i.2 :
                PiMat ℂ ι p →ₗ[ℂ] Mat ℂ (p i.2))
            = (rankOne ℂ (1 : Mat ℂ (p i.1)) (1 : Mat ℂ (p i.2))) :=
by
  withPiQuantumCtx[φ]
  letI : ∀ i, _root_.starAlgebra (Matrix (p i) (p i) ℂ) :=
    fun i => Matrix.isStarAlgebra (φ := φ i)
  letI : ∀ i, _root_.QuantumSet (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i)
  letI : ∀ i, _root_.NormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.NormedAddCommGroup (φ i)
  letI : ∀ i, _root_.TopologicalSpace (Matrix (p i) (p i) ℂ) :=
    fun i => (Module.Dual.NormedAddCommGroup (φ
      i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : ∀ i, _root_.SeminormedAddCommGroup (Matrix (p i) (p i) ℂ) :=
    fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup
  letI : ∀ i, _root_.InnerProductSpace ℂ (Matrix (p i) (p i) ℂ) :=
    fun i => Module.Dual.InnerProductSpace (φ := φ i)
  intro A hA i
  rw [Submodule.eq_iff_orthogonalProjection_eq, orthogonalProjection_of_top,
    QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection]
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne A
  simp only [map_sum, Finset.sum_apply, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    StarAlgEquiv.lTensor_tmul, PiMatTensorProductEquiv_tmul, PiMatToEuclideanLM,
      StarAlgEquiv.piCongrRight_apply]
  rw [← map_sum, ← ContinuousLinearMap.toLinearMapAlgEquiv_symm_apply,
    map_eq_one_iff _ (AlgEquiv.injective _),
    ← map_sum, map_eq_one_iff _ (StarAlgEquiv.injective _)]
  simp only [PiMat.transposeStarAlgEquiv_symm_apply, MulOpposite.unop_op]
  rw [← Function.Injective.eq_iff (QuantumSet.Psi 0 (1/2)).injective,
    ← Function.Injective.eq_iff (AlgEquiv.lTensor _ (Matrix.transposeAlgEquiv _ _
      _).symm).injective,
    ← Function.Injective.eq_iff tensorToKronecker.injective]
  simp only [LinearMap.sum_comp, LinearMap.comp_sum,
    LinearMap.rankOne_comp', LinearMap.comp_rankOne, map_sum,
    QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, AlgEquiv.lTensor_tmul,
    Matrix.transposeAlgEquiv_symm_op_apply, PiMat.modAut_proj,
    tensorToKronecker_apply, TensorProduct.toKronecker_apply, map_one,
    star_one, Matrix.transpose_one, Matrix.one_kronecker_one]
  rfl

theorem Matrix.trace_eq_linearMap_trace
  {n : Type*} [Fintype n] [DecidableEq n]
  (y : Matrix n n ℂ) :
  Matrix.trace y = LinearMap.trace ℂ (EuclideanSpace ℂ n)
    (Matrix.toEuclideanLin y) :=
by
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ n)]
  simp only [Matrix.toLpLin_eq_toLin, LinearMap.toMatrix_toLin]

lemma Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {p : ι → Type*} [∀ i, Fintype (p i)] [∀ i, DecidableEq (p i)]
  (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι) :
  Matrix.trace
    (PiMatTensorProductEquiv
      ((StarAlgEquiv.lTensor (PiMat ℂ ι p) (PiMat.transposeStarAlgEquiv ι p).symm) x) i)
    = Matrix.trace (PiMatTensorProductEquiv (LinearMap.lTensor _ (unop ℂ).toLinearMap x) i) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    StarAlgEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
    PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    PiMat.transposeStarAlgEquiv_symm_apply]
  rfl

lemma Matrix.trace_piMatTensorProductEquiv_lTensor_unop_map_modAut
  :
  withPiQuantum[φ]
    ∀ (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι),
      Matrix.trace
        (PiMatTensorProductEquiv
          (LinearMap.lTensor _ (unop ℂ).toLinearMap
            ((TensorProduct.map (modAut (0 - 1 / 2)).toLinearMap
              (AlgEquiv.op (modAut (0 - 1 / 2))).toLinearMap) x)) i)
      = Matrix.trace
        (PiMatTensorProductEquiv
          (LinearMap.lTensor _ (unop ℂ).toLinearMap x) i) :=
by
  intro x i
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    AlgEquiv.toLinearMap_apply]
  congr 1
  ext
  rw [AlgEquiv.op_apply_apply, LinearEquiv.coe_coe, unop_apply, MulOpposite.unop_op]
  simp_rw [PiMat.modAut_trace_apply]
  rfl

lemma Matrix.trace_piMatTensorProductEquiv_lTensor_unop_tenSwap
  (x : (PiMat ℂ ι p) ⊗[ℂ] (PiMat ℂ ι p)ᵐᵒᵖ) (i : ι × ι) :
  (Matrix.trace
      (PiMatTensorProductEquiv
        ((LinearMap.lTensor (PiMat ℂ ι p) (unop ℂ).toLinearMap) ((tenSwap ℂ) x)) i))
  = Matrix.trace (PiMatTensorProductEquiv
        ((LinearMap.lTensor (PiMat ℂ ι p) (unop ℂ).toLinearMap) x) i.swap) :=
by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  rw [← LinearEquiv.coe_toLinearMap]
  simp_rw [hS, map_sum, Finset.sum_apply, Matrix.trace_sum,
    LinearEquiv.coe_coe, tenSwap_apply,
    LinearMap.lTensor_tmul, PiMatTensorProductEquiv_tmul, Matrix.trace_kronecker,
    LinearEquiv.coe_coe, unop_apply]
  congr 1
  ext
  rw [mul_comm]
  rfl

/-- Build a linear isometry equivalence from a linear equivalence whose adjoint is its inverse. -/
def LinearIsometryEquiv.ofLinearEquiv
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (f : E ≃ₗ[𝕜] F) (hf : LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap) :
    E ≃ₗᵢ[𝕜] F where
  toLinearEquiv := f
  norm_map' := by
    rw [← isometry_iff_norm, isometry_iff_inner]
    intro _ _
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.adjoint_inner_left]
    simp only [hf, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

lemma LinearIsometryEquiv.ofLinearEquiv_apply {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (f : E ≃ₗ[𝕜] F) (hf : LinearMap.adjoint f.toLinearMap = f.symm.toLinearMap) (x : E) :
  (LinearIsometryEquiv.ofLinearEquiv f hf) x = f x :=
rfl

/-- Tensor-product commutativity as a linear isometry equivalence. -/
noncomputable def TensorProduct.commLinearIsometryEquiv
  (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] (F ⊗[𝕜] E) :=
LinearIsometryEquiv.ofLinearEquiv (TensorProduct.comm 𝕜 E F) TensorProduct.comm_adjoint

lemma TensorProduct.commLinearIsometryEquiv_apply
  {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 E]
  [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (x : E) (y : F) :
  (TensorProduct.commLinearIsometryEquiv 𝕜 E F) (x ⊗ₜ y) = y ⊗ₜ x :=
rfl

/-- Commute the factors of Euclidean space indexed by a product. -/
noncomputable def
  EuclideanSpace.tensorComm {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :
  EuclideanSpace ℂ (n × m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (m × n) :=
(euclideanSpaceTensor'.symm.trans (TensorProduct.commLinearIsometryEquiv ℂ _ _)).trans
  (euclideanSpaceTensor')
lemma EuclideanSpace.tensorComm_apply {n m :
    Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
  tensorComm (euclideanSpaceTensor' (R := ℂ) (x ⊗ₜ[ℂ] y))
    = euclideanSpaceTensor' (R := ℂ) (y ⊗ₜ[ℂ] x) :=
by
  simp only [tensorComm]
  rw [LinearIsometryEquiv.trans_apply]
  nth_rw 2 [LinearIsometryEquiv.trans_apply]
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem QuantumGraph.Real.piMat_submodule_finrank_eq_swap_of_adjoint :
  withPiQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph.Real _ f) → LinearMap.adjoint f = f → ∀ i : ι × ι,
        Module.finrank ℂ (hf.PiMatSubmodule i)
          = Module.finrank ℂ (hf.PiMatSubmodule i.swap) :=
by
  withPiQuantumCtx[φ]
  intro f hf hf₂ i
  rw [← Nat.cast_inj (R := ℂ)]
  nth_rw 2 [← Complex.conj_natCast]
  simp_rw [← orthogonalProjection_trace,
    QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection,
    LinearMap.coe_toContinuousLinearMap,
    PiMatToEuclideanLM, StarAlgEquiv.piCongrRight_apply,
    Matrix.toEuclideanStarAlgEquiv_coe,
    ← Matrix.trace_eq_linearMap_trace]
  nth_rw 2 [← hf₂]
  rw [Psi.adjoint_apply]
  simp_rw [Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose,
    Matrix.trace_piMatTensorProductEquiv_lTensor_unop_map_modAut,
    Matrix.trace_piMatTensorProductEquiv_lTensor_unop_tenSwap,
    ← Matrix.trace_piMatTensorProductEquiv_apply_lTensor_transpose,
    map_star, starRingEnd_apply, Matrix.trace_star, Pi.star_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rfl

theorem QuantumGraph.Real.PiMatSubmodule_eq_bot_iff_swap_eq_bot_of_adjoint :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real _ A) → LinearMap.adjoint A = A → ∀ i : ι × ι,
        hA.PiMatSubmodule i = ⊥ ↔ hA.PiMatSubmodule i.swap = ⊥ :=
by
  intro A hA hA₂ i
  simp only [← Submodule.finrank_eq_zero]
  rw [hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂]

lemma Submodule.finrank_eq_iff_eq_top {K V : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {S : Submodule K V} :
  Module.finrank K ↥S = Module.finrank K V ↔ S = ⊤ :=
by
  refine ⟨Submodule.eq_top_of_finrank_eq, ?_⟩
  rintro rfl
  simp only [finrank_top]

theorem QuantumGraph.Real.PiMatSubmodule_eq_top_iff_swap_eq_top_of_adjoint :
  withPiQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real _ A) → LinearMap.adjoint A = A → ∀ i : ι × ι,
        hA.PiMatSubmodule i = ⊤ ↔ hA.PiMatSubmodule i.swap = ⊤ :=
by
  intro A hA hA₂ i
  simp only [← Submodule.finrank_eq_iff_eq_top]
  rw [hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂]
  simp only [Prod.fst_swap, Prod.snd_swap]
  have hdim :
      Module.finrank ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) =
        Module.finrank ℂ (EuclideanSpace ℂ (p i.2 × p i.1)) := by
    rw [finrank_euclideanSpace (𝕜 := ℂ), finrank_euclideanSpace (𝕜 := ℂ),
      Fintype.card_prod, Fintype.card_prod, mul_comm]
  rw [hdim]
  rfl
