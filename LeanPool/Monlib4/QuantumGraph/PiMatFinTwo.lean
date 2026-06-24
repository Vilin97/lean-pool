/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.PiMat
import LeanPool.Monlib4.LinearAlgebra.Ips.Nontracial

/-!
# LeanPool.Monlib4.QuantumGraph.PiMatFinTwo

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.PiMatFinTwo`.
-/

open scoped Functional MatrixOrder ComplexOrder TensorProduct Matrix

/-- Elaborate a product-of-blocks statement with matrix quantum-set instances on each block. -/
syntax "withPiBlockQuantum[" term "] " term : term
macro_rules
  | `(withPiBlockQuantum[$ψ] $p) =>
      `(withPiQuantum[$ψ]
        letI := fun i => Matrix.isStarAlgebra (φ := $ψ i)
        letI := fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := $ψ i)
        letI := fun i => Module.Dual.NormedAddCommGroup ($ψ i)
        letI := fun i => (Module.Dual.NormedAddCommGroup ($ψ
          i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        letI := fun i => (Module.Dual.NormedAddCommGroup ($ψ i)).toSeminormedAddCommGroup
        letI := fun i => Module.Dual.InnerProductSpace (φ := $ψ i)
        $p)

/-- Introduce product and blockwise matrix quantum-set instances in a proof. -/
syntax "withPiBlockQuantumCtx" "[" term "]" : tactic
macro_rules
  | `(tactic| withPiBlockQuantumCtx[$ψ]) =>
      `(tactic|
        withPiQuantumCtx[$ψ];
        letI := fun i => Matrix.isStarAlgebra (φ := $ψ i);
        letI := fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := $ψ i);
        letI := fun i => Module.Dual.NormedAddCommGroup ($ψ i);
        letI := fun i => (Module.Dual.NormedAddCommGroup ($ψ
          i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
        letI := fun i => (Module.Dual.NormedAddCommGroup ($ψ i)).toSeminormedAddCommGroup;
        letI := fun i => Module.Dual.InnerProductSpace (φ := $ψ i))

/-- Elaborate a product-of-blocks statement with blockwise quantum and coalgebra instances. -/
syntax "withPiBlockCoalgebraQuantum[" term "] " term : term
macro_rules
  | `(withPiBlockCoalgebraQuantum[$ψ] $p) =>
      `(withPiBlockQuantum[$ψ]
        letI := PiMat.finiteDimensionalHilbertCoalgebraStruct (φ := $ψ)
        $p)

/-- Introduce product, blockwise quantum, and coalgebra instances in a proof. -/
syntax "withPiBlockCoalgebraQuantumCtx" "[" term "]" : tactic
macro_rules
  | `(tactic| withPiBlockCoalgebraQuantumCtx[$ψ]) =>
      `(tactic|
        withPiBlockQuantumCtx[$ψ];
        letI := PiMat.finiteDimensionalHilbertCoalgebraStruct (φ := $ψ))

/-- The algebra equivalence between a two-block product of matrix algebras and the matching
  `PiMat`. -/
def MatProdAlgEquivPiMat (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
  (Matrix (n' 0) (n' 0) ℂ × Matrix (n' 1) (n' 1) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) n' :=
matrixPiFinTwoAlgEquivProd.symm

/-- Swap the two types in a `Fin 2`-indexed family. -/
abbrev PiFinTwo.swap (n' : Fin 2 → Type*) :
  Fin 2 → Type _ :=
fun i => if i = 0 then (n' 1) else (n' 0)

instance {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] :
  Π i, Fintype ((PiFinTwo.swap n') i) :=
fun i => by
  unfold PiFinTwo.swap
  split_ifs <;> infer_instance
instance {n' : Fin 2 → Type*} [Π i, DecidableEq (n' i)] :
  Π i, DecidableEq ((PiFinTwo.swap n') i) :=
fun i => by
  unfold PiFinTwo.swap
  split_ifs <;> infer_instance

/-- The swapped product-to-`PiMat` equivalence for two matrix blocks. -/
def MatProdAlgEquivPiMatSwap (n' : Fin 2 → Type*) [Π i, Fintype (n' i)] [Π i,
  DecidableEq (n' i)] :
  (Matrix (n' 1) (n' 1) ℂ × Matrix (n' 0) (n' 0) ℂ)
    ≃ₐ[ℂ]
  PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
MatProdAlgEquivPiMat (PiFinTwo.swap n')

/-- Swap the two factors of a product as an algebra equivalence. -/
@[simps]
def Prod.swapAlgEquiv
  (α β : Type*) [Semiring α] [Semiring β] [Algebra ℂ α] [Algebra ℂ β] :
    (α × β) ≃ₐ[ℂ] (β × α) where
  toFun x := x.swap
  invFun x := x.swap
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  commutes' _ := by simp

/-- Swap the two blocks of a `PiMat` indexed by `Fin 2`. -/
def PiMatFinTwoSwapAlgEquiv
  {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)] :
    PiMat ℂ (Fin 2) n' ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
(MatProdAlgEquivPiMat n').symm.trans ((Prod.swapAlgEquiv _ _).trans
  (MatProdAlgEquivPiMatSwap n'))

/-- The constant `Fin 2`-indexed family with value `n`. -/
abbrev PiFinTwoSame (n : Type*) :
  Fin 2 → Type _ :=
fun i => let _ := i; n

instance {n : Type*} [Fintype n] :
  Π i, Fintype ((PiFinTwoSame n) i) :=
fun i => by infer_instance
instance {n : Type*} [DecidableEq n] :
  Π i, DecidableEq ((PiFinTwoSame n) i) :=
fun i => by infer_instance

theorem PiMatFinTwoSwapAlgEquiv_apply {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] [Π i,
  DecidableEq (n' i)]
  (x : Matrix (n' 0) (n' 0) ℂ) (y : Matrix (n' 1) (n' 1) ℂ) :
  PiMatFinTwoSwapAlgEquiv (MatProdAlgEquivPiMat n' (x, y))
    = MatProdAlgEquivPiMat _ (y, x) :=
rfl

lemma PiFinTwoSame_swap {n : Type*} :
  PiFinTwo.swap (PiFinTwoSame n) = PiFinTwoSame n :=
by ext; simp only [ite_self, Fin.isValue]

/-- Swap the two identical matrix blocks of a `PiMat` indexed by `Fin 2`. -/
def PiMatFinTwoSameSwapAlgEquiv
  {n : Type*} [Fintype n] [DecidableEq n] :
    PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n) :=
(MatProdAlgEquivPiMat (PiFinTwoSame n)).symm.trans ((Prod.swapAlgEquiv _ _).trans
  (MatProdAlgEquivPiMat (PiFinTwoSame n)))


theorem PiMatFinTwoSameSwapAlgEquiv_apply {n : Type*} [Fintype n] [DecidableEq n]
  (x : Matrix n n ℂ) (y : Matrix n n ℂ) :
  PiMatFinTwoSameSwapAlgEquiv (MatProdAlgEquivPiMat (PiFinTwoSame n) (x, y))
    = MatProdAlgEquivPiMat _ (y, x) :=
rfl

variable {n : Type*}
  [Fintype n] [DecidableEq n]

theorem AlgEquiv.prodMap_inner_of {K R₁ R₂ : Type*} [CommSemiring K]
  [Semiring R₁] [Semiring R₂] [Algebra K R₁] [Algebra K R₂]
  {f : R₁ ≃ₐ[K] R₁} (hf : f.IsInner) {g : R₂ ≃ₐ[K] R₂} (hg : g.IsInner) :
  (f.prodMap g).IsInner := by
  rw [AlgEquiv.prod_isInner_iff_prodMap]
  obtain ⟨U, hU, rfl⟩ := hf
  obtain ⟨V, hV, rfl⟩ := hg
  exact ⟨U, hU, V, hV, rfl⟩

/-- Invertibility is preserved by the product-to-`PiMat` equivalence in the same-block case. -/
@[reducible]
def MatProdAlgEquivPiMatSameInvertibleOf {U : Matrix n n ℂ × Matrix n n ℂ}
  (hU : Invertible U) :
  Invertible ((MatProdAlgEquivPiMat (PiFinTwoSame n)) U) := by
  use (MatProdAlgEquivPiMat _ ⅟U) <;>
  simp only [← map_mul, invOf_mul_self, mul_invOf_self, map_one]

theorem AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner
  {f : (Matrix n n ℂ × Matrix n n ℂ) ≃ₐ[ℂ] (Matrix n n ℂ × Matrix n n ℂ)}
  (hf : f.IsInner) :
  ((MatProdAlgEquivPiMat (PiFinTwoSame n)).symm.trans
  (f.trans
  (MatProdAlgEquivPiMat (PiFinTwoSame n)))).IsInner := by
  obtain ⟨U, hU, rfl⟩ := hf
  use ((MatProdAlgEquivPiMat _) U), MatProdAlgEquivPiMatSameInvertibleOf hU
  ext1
  simp only [Fin.isValue, MatProdAlgEquivPiMat, symm_symm, trans_apply,
    matrixPiFinTwoAlgEquivProd_apply, Algebra.autInner_apply, map_mul]
  congr
  simp only [PiMat.ext_iff, Fin.forall_fin_two]
  trivial

theorem AlgEquiv.PiMat_finTwo_same
  (f : PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n)) :
  f.IsInner
  ∨
  (∃ (g : PiMat ℂ (Fin 2) (PiFinTwoSame n) ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n))
    (_ : AlgEquiv.IsInner g),
      f = PiMatFinTwoSameSwapAlgEquiv.trans g) := by
  let f' := ((MatProdAlgEquivPiMat _).trans f).trans (MatProdAlgEquivPiMat _).symm
  rcases (AlgEquiv.matrix_prod_aut' f') with (⟨f₁, f₂, hf⟩ | ⟨g₁, g₂, hg⟩)
  · left
    obtain ⟨U, hf₁⟩ := Matrix.aut_mat_inner' f₁
    obtain ⟨V, hf₂⟩ := Matrix.aut_mat_inner' f₂
    have hf₁' : f₁.IsInner := ⟨U, _, hf₁⟩
    have hf₂' : f₂.IsInner := ⟨V, _, hf₂⟩
    have hf' :=
      AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner (AlgEquiv.prodMap_inner_of hf₁' hf₂')
    simp only [Fin.isValue, ← hf] at hf'
    have :
      (MatProdAlgEquivPiMat _).symm.trans
      (f'.trans (MatProdAlgEquivPiMat _)) = f :=
    by ext1; simp [f']
    rw [this] at hf'
    exact hf'
  · right
    obtain ⟨U, hg₁⟩ := Matrix.aut_mat_inner' g₁
    obtain ⟨V, hg₂⟩ := Matrix.aut_mat_inner' g₂
    have hg₁' : g₁.IsInner := ⟨U, _, hg₁⟩
    have hg₂' : g₂.IsInner := ⟨V, _, hg₂⟩
    have hg' :=
      AlgEquiv.toPiMat_finTwo_same_inner_of_matrix_prod_inner (AlgEquiv.prodMap_inner_of hg₁' hg₂')
    use (MatProdAlgEquivPiMat (PiFinTwoSame n)).symm.trans
      ((g₁.prodMap g₂).trans (MatProdAlgEquivPiMat (PiFinTwoSame n))), hg'
    rw [funext_iff] at hg
    simp only [Fin.isValue, AlgEquiv.coe_trans, Function.comp_apply,
      AlgEquiv.prodMap_apply, Prod.swap, Prod.map_apply, f',
      AlgEquiv.symm_apply_eq] at hg
    ext1 x
    specialize hg ((MatProdAlgEquivPiMat _).symm x)
    simp only [AlgEquiv.apply_symm_apply] at hg
    rw [hg]
    rfl

variable {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]

theorem PiMat.trace_eq_linearMap_trace_toEuclideanLM
  (y : (PiMat ℂ (ι × ι) fun i ↦ p i.1 × p i.2)) :
  PiMat.traceLinearMap y
    = ∑ x : ι × ι, LinearMap.trace ℂ (EuclideanSpace ℂ (p x.1 × p x.2))
      (PiMatToEuclideanLM y x) := by
  simp only [StarAlgEquiv.piCongrRight_apply, StarAlgEquiv.ofAlgEquiv_coe,
    AlgEquiv.ofLinearEquiv_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Matrix.traceLinearMap_apply, Matrix.blockDiagonal'AlgHom_apply,
    Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i _
  change Matrix.trace (y i) =
      LinearMap.trace ℂ (EuclideanSpace ℂ (p i.1 × p i.2)) (Matrix.toLpLin 2 2 (y i))
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (p i.1 × p i.2)),
    Matrix.toLpLin_eq_toLin, LinearMap.toMatrix_toLin]

variable {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ (i : ι), (φ i).IsFaithfulPosMap]

theorem QuantumGraph.Real.dimOfPiMatSubmodule_eq
  : withPiBlockQuantum[φ]
    letI : CoalgebraStruct ℂ (PiMat ℂ ι p) :=
      PiMat.finiteDimensionalHilbertCoalgebraStruct (φ := φ)
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hA : QuantumGraph.Real (PiMat ℂ ι p) A) →
      hA.toQuantumGraph.dimOfPiMatSubmodule =
        ∑ i, Module.finrank ℂ (hA.PiMatSubmodule i) := by
  withPiBlockQuantumCtx[φ]
  letI : CoalgebraStruct ℂ (PiMat ℂ ι p) :=
    PiMat.finiteDimensionalHilbertCoalgebraStruct (φ := φ)
  intro A hA
  rw [← Nat.cast_inj (R := ℂ), QuantumGraph.dimOfPiMatSubmodule_eq_trace]
  simp only [Nat.cast_sum, ←
    orthogonalProjection_trace (R := ℂ),
    QuantumGraph.Real.PiMatSubmoduleOrthogonalProjection,
    LinearMap.coe_toContinuousLinearMap]
  rw [← PiMat.trace_eq_linearMap_trace_toEuclideanLM]

variable
  {ψ : Π i : Fin 2, Module.Dual ℂ (Matrix (PiFinTwoSame n i) (PiFinTwoSame n i) ℂ)}
  [hψ : ∀ i, (ψ i).IsFaithfulPosMap]
  {A : withPiBlockQuantum[ψ]
    (PiMat ℂ (Fin 2) (PiFinTwoSame n) →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n))}
  (hA : withPiBlockCoalgebraQuantum[ψ] QuantumGraph.Real _ A)

omit [(i : ι) → DecidableEq (p i)] in
theorem LinearMap.proj_adjoint_apply
  : letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (i : ι) (x : Matrix (p i) (p i) ℂ),
      (LinearMap.adjoint (LinearMap.proj (R := ℂ) i)) x
        = Matrix.includeBlock x := by
  classical
  withPiBlockQuantumCtx[φ]
  intro i x
  apply ext_inner_left ℂ
  intro y
  simp only [LinearMap.adjoint_inner_right, coe_proj, Function.eval]
  rw [Module.Dual.pi.IsFaithfulPosMap.includeBlock_right_inner]

omit [(i : ι) → DecidableEq (p i)] in
theorem LinearMap.proj_adjoint
  : letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (i : ι),
      LinearMap.adjoint (LinearMap.proj (R := ℂ) i)
        = LinearMap.single ℂ (fun r => Mat ℂ (p r)) i := by
  classical
  withPiBlockQuantumCtx[φ]
  intro i
  ext1
  rw [LinearMap.proj_adjoint_apply]
  rfl

omit [(i : ι) → DecidableEq (p i)] in
theorem LinearMap.single_adjoint
  : letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (i : ι),
      LinearMap.adjoint (LinearMap.single ℂ (fun r => Mat ℂ (p r)) i)
        = LinearMap.proj (R := ℂ) i := by
  classical
  withPiBlockQuantumCtx[φ]
  intro i
  rw [← proj_adjoint, adjoint_adjoint]

open scoped Classical in
omit [DecidableEq ι] [(i : ι) → DecidableEq (p i)] in
theorem LinearMap.eq_sum_conj_adjoint_proj_comp_proj
  : letI : DecidableEq ι := Classical.decEq ι
    letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p),
      A = ∑ i : ι × ι,
        LinearMap.adjoint (LinearMap.proj i.1)
          ∘ₗ (LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.2))
          ∘ₗ LinearMap.proj i.2 := by
  classical
  withPiBlockQuantumCtx[φ]
  intro A
  simp_rw [LinearMap.proj_adjoint, Finset.sum_product_univ,
    LinearMap.comp_assoc]
  rw [LinearMap.lrsum_eq_single_proj_lrcomp]

private lemma
  QuantumGraph.Real.PiFinTwoSame_exists_proj_conj_add_of_piMat_submodule_eq_bot
  : withPiBlockCoalgebraQuantum[ψ]
    ∀ (_ : hA.PiMatSubmodule ((1 : Fin 2), (0 : Fin 2)) = ⊥)
      (_ : hA.PiMatSubmodule ((0 : Fin 2), (1 : Fin 2)) = ⊥),
  -- ∃ (f₁ f₂ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ),
    (LinearMap.adjoint
        (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2))
      ∘ₗ ((LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2)) ∘ₗ A
        ∘ₗ LinearMap.adjoint
          (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2)))
      ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2))
    + (LinearMap.adjoint
        (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2))
      ∘ₗ ((LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2)) ∘ₗ A
        ∘ₗ LinearMap.adjoint
          (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2)))
      ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2)) = A := by
  withPiBlockCoalgebraQuantumCtx[ψ]
  intro h₂ h₃
  simp only [Fin.isValue,
    QuantumGraph.Real.PiMatSubmodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero] at h₂ h₃
  simp_all only [PiFinTwoSame]
  nth_rw 3 [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hψ) A]
  simp only [Finset.sum_product_univ, Fin.sum_univ_two,
    Fin.isValue,
    h₂, h₃, LinearMap.zero_comp, LinearMap.comp_zero, zero_add, add_zero]

lemma
  QuantumGraph.Real.piFinTwo_same_piMat_submodule_eq_bot_of_adjoint_and_dim_eq_one
  : withPiBlockCoalgebraQuantum[ψ]
    ∀ (_ : LinearMap.adjoint A = A)
      (_ : hA.toQuantumGraph.dimOfPiMatSubmodule = 1),
    hA.PiMatSubmodule ((1 : Fin 2), (0 : Fin 2)) = ⊥
    ∧ ((Module.finrank ℂ (hA.PiMatSubmodule 0) = 1
      ∧ hA.PiMatSubmodule 1 = ⊥)
      ∨
      (hA.PiMatSubmodule 0 = ⊥
        ∧ Module.finrank ℂ (hA.PiMatSubmodule 1) = 1)) := by
  withPiBlockCoalgebraQuantumCtx[ψ]
  intro hA₂ hd
  simp only [QuantumGraph.Real.dimOfPiMatSubmodule_eq,
    Finset.sum_product_univ, Fin.sum_univ_two,
    Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one] at hd
  simp only [Fin.isValue, Nat.add_eq_one_iff, AddLeftCancelMonoid.add_eq_zero,
    Submodule.finrank_eq_zero] at hd
  simp only [Fin.isValue, hA.PiMatSubmodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂ (0, 1),
    Prod.swap_prod_mk] at hd
  rcases hd with (h | h)
  · obtain ⟨h₁, (h₂ | h₂)⟩ := h
    · exact ⟨h₂.1, Or.inr ⟨h₁.1, h₂.2⟩⟩
    · rw [h₁.2] at h₂
      simp only [finrank_bot, zero_ne_one, false_and] at h₂
  · obtain ⟨(h₁ | h₁), h₂⟩ := h
    · rw [hA.PiMatSubmodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂ (1, 0),
        Prod.swap_prod_mk] at h₂
      rw [h₂.1, finrank_bot] at h₁
      simp only [zero_ne_one, and_false] at h₁
    · exact ⟨h₁.2, Or.inl ⟨h₁.1, h₂.2⟩⟩

lemma Pi.nat_eq_zero_of_sum_eq_one_and_unique_one
  {ι : Type*} [Fintype ι] {f : ι → ℕ}
  (h : ∑ i, f i = 1) {i : ι} (hd : f i = 1)
  {j : ι} (hj : j ≠ i) : f j = 0 := by
  classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i), hd] at h
  simp only [add_eq_left, Finset.sum_eq_zero_iff, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_singleton, true_and] at h
  exact h _ hj

theorem Finset.sum_nat_eq_one_iff_exists_unique_eq_one
  {ι : Type*} [Fintype ι] {f : ι → ℕ}
  (h : ∑ i, f i = 1) :
  (∃! i : ι, f i = 1) := by
  classical
  have this1 : ∀ i : ι, f i ≤ 1 := by
    intro i
    by_contra!
    have :=
    calc 1 = ∑ j, f j := h.symm
      _ = f i
        + ∑ j ∈ Finset.univ \ {i}, f j :=
          by rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ _)]
      _ > 1 + ∑ j ∈ Finset.univ \ {i}, f j := by
          nlinarith
      _ ≥ 1 := by norm_num
    linarith
  have : ∃! i, 1 ≤ f i := by
    apply existsUnique_of_exists_of_unique
    · by_contra!
      simp only [Nat.lt_one_iff] at this
      simp only [this, Finset.sum_const_zero] at h
      norm_num at h
    · intro y₁ y₂ hy hd
      by_contra!
      have :=
      calc
        1 =  ∑ i : ι, f i := h.symm
        _ = f y₁ + f y₂
          + ∑ i ∈ (Finset.univ \ {y₁}) \ {y₂}, f i := by
              have : y₂ ∈ Finset.univ \ {y₁} := by simp [this.symm]
              rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ y₁),
                Finset.sum_eq_add_sum_sdiff_singleton_of_mem this, add_assoc]
        _ ≥ 1 + 1
          + ∑ i ∈ (Finset.univ \ {y₁}) \ {y₂}, f i := by
              apply LE.le.ge
              linarith
        _ ≥ 2 := by norm_num
      linarith
  obtain ⟨i, ⟨hi, hii⟩⟩ := this
  simp_rw [le_antisymm_iff]
  use i
  simpa only [this1, true_and, hi] using hii

theorem QuantumGraph.Real.dimOfPiMatSubmodule_eq_zero_iff_eq_zero
  {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]
  {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap]
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p} (hA : QuantumGraph.Real _ A),
      hA.toQuantumGraph.dimOfPiMatSubmodule = 0 ↔ A = 0 := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro A hA
  simp only [QuantumGraph.Real.dimOfPiMatSubmodule_eq]
  simp_rw [Finset.sum_eq_zero_iff,
    Submodule.finrank_eq_zero,
    QuantumGraph.Real.PiMatSubmodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero]
  constructor
  · intro h
    rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) A]
    simp only [h _ (Finset.mem_univ _), LinearMap.comp_zero, LinearMap.zero_comp,
      Finset.sum_const_zero]
  · rintro rfl
    simp only [LinearMap.zero_comp, LinearMap.comp_zero,
      Finset.mem_univ, imp_self, implies_true]

theorem QuantumGraph.Real.exists_unique_includeMap_of_adjoint_and_dim_ofPiMatSubmodule_eq_one
  {ι : Type*} {p : ι → Type*} [Fintype ι] [DecidableEq ι]
  [(i : ι) → Fintype (p i)] [(i : ι) → DecidableEq (p i)]
  {φ : (i : ι) → Module.Dual ℂ (Matrix (p i) (p i) ℂ)}
  [hφ : ∀ i, (φ i).IsFaithfulPosMap]
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {A : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p}, (hA : QuantumGraph.Real _ A) →
      (hA₂ : LinearMap.adjoint A = A) →
      (hd : hA.toQuantumGraph.dimOfPiMatSubmodule = 1) →
      ∃! i : ι,
        LinearMap.adjoint (LinearMap.proj i)
          ∘ₗ LinearMap.proj i
          ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i) ∘ₗ LinearMap.proj i = A := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro A hA hA₂ hd
  have hA_neZero :=
    (not_iff_not.mpr (hA.dimOfPiMatSubmodule_eq_zero_iff_eq_zero)).mp
    (ne_zero_of_eq_one hd)
  simp only [QuantumGraph.Real.dimOfPiMatSubmodule_eq] at hd
  obtain ⟨i, hi, hii⟩ := Finset.sum_nat_eq_one_iff_exists_unique_eq_one hd
  have this₁ : ∀ j ∈ Finset.univ \ {i},
    Module.finrank ℂ (hA.PiMatSubmodule j) = 0 := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    exact Pi.nat_eq_zero_of_sum_eq_one_and_unique_one hd hi hj
  have this₂ := (hA.piMat_submodule_finrank_eq_swap_of_adjoint hA₂)
  rw [this₂] at hi
  have this₃ := Prod.ext_iff.mp (hii _ hi)
  simp only [Prod.fst_swap, Prod.snd_swap] at this₃
  simp_rw [Submodule.finrank_eq_zero,
    QuantumGraph.Real.PiMatSubmodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero] at this₁
  have : ∑ x ∈ Finset.univ \ {i},
      LinearMap.adjoint (LinearMap.proj x.1) ∘ₗ
        ((LinearMap.proj x.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj x.2))) ∘ₗ LinearMap.proj x.2
      = (0 : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p) := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [this₁ _ hj, LinearMap.comp_zero, LinearMap.zero_comp]
  have hAA : A = LinearMap.adjoint (LinearMap.proj i.1)
    ∘ₗ (LinearMap.proj i.1 ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj i.1))
    ∘ₗ LinearMap.proj i.1 := by
    nth_rw 1 [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) A]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [this, add_zero]
    rw [this₃.1]
  refine ⟨i.1, hAA.symm, fun j hj => ?_⟩
  · by_contra!
    specialize this₁ (j, j)
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Prod.ext_iff, this₃.1, and_self] at this₁
    have :=
    calc (0 : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p)
        = LinearMap.adjoint (LinearMap.proj j) ∘ₗ
          (LinearMap.proj j ∘ₗ A ∘ₗ LinearMap.adjoint (LinearMap.proj j)) ∘ₗ LinearMap.proj j := by
            simp only [this₁ this, LinearMap.comp_zero, LinearMap.zero_comp]
      _ = A := by simp only [LinearMap.comp_assoc, hj]
      _ ≠ 0 := hA_neZero
    simp only [ne_eq, not_true_eq_false] at this

theorem QuantumGraph.Real.piFinTwo_same_exists_matrix_map_eq_map_of_adjoint_and_dim_eq_one
  : withPiBlockCoalgebraQuantum[ψ]
    ∀ (_ : LinearMap.adjoint A = A)
      (_ : hA.toQuantumGraph.dimOfPiMatSubmodule = 1),
  -- (∃ f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
  LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2))
    ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2)
    ∘ₗ A
    ∘ₗ LinearMap.adjoint
      (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2))
    ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (0 : Fin 2) = A
  ∨
    -- ∃ f : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
      LinearMap.adjoint
        (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2))
    ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2)
    ∘ₗ A
    ∘ₗ LinearMap.adjoint
      (LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2))
    ∘ₗ LinearMap.proj (R := ℂ) (φ := fun j => Mat ℂ (PiFinTwoSame n j)) (1 : Fin 2) = A := by
  withPiBlockCoalgebraQuantumCtx[ψ]
  intro hA₂ hd
  obtain ⟨h₁, h⟩ := hA.piFinTwo_same_piMat_submodule_eq_bot_of_adjoint_and_dim_eq_one hA₂ hd
  have h₂ := h₁
  rw [hA.PiMatSubmodule_eq_bot_iff_swap_eq_bot_of_adjoint hA₂,
    Prod.swap_prod_mk] at h₂
  obtain hf := hA.PiFinTwoSame_exists_proj_conj_add_of_piMat_submodule_eq_bot h₁ h₂
  simp only [hA.PiMatSubmodule_eq_bot_iff_proj_comp_adjoint_proj_eq_zero,
    Prod.fst_one, Prod.snd_one, Prod.fst_zero, Prod.snd_zero] at h
  rcases h with (h | h)
  <;>
  simp only [h.1, h.2, LinearMap.comp_zero, LinearMap.zero_comp,
    add_zero, zero_add, LinearMap.comp_assoc] at hf
  · exact Or.inl hf
  · exact Or.inr hf

/-- Projection from a dependent product as an algebra homomorphism. -/
def AlgHom.proj
  (R : Type*) {ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
    (Π i, φ i) →ₐ[R] φ i where
  toFun x := x i
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_one' := by simp
  map_zero' := by simp
  commutes' _ := by simp

theorem AlgHom.proj_apply
  {R ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (x : Π i, φ i) (i : ι) :
  AlgHom.proj R i x = x i :=
rfl

theorem AlgHom.proj_toLinearMap
  {R ι : Type*} [CommSemiring R] {φ : ι → Type*}
  [(i : ι) → Semiring (φ i)] [(i : ι) → Algebra R (φ i)] (i : ι) :
  (AlgHom.proj R i).toLinearMap =
    @LinearMap.proj R ι _ φ _ _ i :=
rfl

/-- Insert one component into a dependent product as a non-unital algebra homomorphism. -/
def NonUnitalAlgHom.single (R : Type*) {ι : Type*} [CommSemiring R]
  [DecidableEq ι]
  (φ : ι → Type*) [(i : ι) → Ring (φ i)]
  [(i : ι) → Module R (φ i)] (i : ι) :
    φ i →ₙₐ[R] (Π i, φ i) where
  toFun x := LinearMap.single R φ i x
  map_add' _ _ := by simp [Pi.single_add]
  map_smul' _ _ := by simp []
  map_mul' _ _ := by simp [Pi.single_mul]
  map_zero' := by simp [Pi.single_zero]

theorem NonUnitalAlgHom.single_apply
  {R ι : Type*} [CommSemiring R] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → Ring (φ i)]
  [(i : ι) → Module R (φ i)] (i : ι) (x : φ i) :
  NonUnitalAlgHom.single R φ i x = Pi.single i x :=
rfl

theorem NonUnitalAlgHom.single_toLinearMap
  {R ι : Type*} [CommSemiring R] [DecidableEq ι]
  {φ : ι → Type*} [(i : ι) → Ring (φ i)]
  [(i : ι) → Module R (φ i)] (i : ι) :
  (LinearMapClass.linearMap (NonUnitalAlgHom.single R φ i) : φ i →ₗ[R] (Π i, φ i)) =
    LinearMap.single R φ i :=
rfl

theorem LinearMap.single_isReal
  {R ι : Type*} [DecidableEq ι] [Semiring R] {φ : ι → Type*}
  [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
  [(i : ι) → StarAddMonoid (φ i)] (i : ι) :
  LinearMap.IsReal (LinearMap.single R φ i) := by
  intro x
  ext j
  by_cases h : j = i
  · subst j
    simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, Pi.single_eq_of_ne h]

theorem LinearMap.proj_isReal
  {R ι : Type*} [Semiring R] {φ : ι → Type*}
  [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
  [(i : ι) → StarAddMonoid (φ i)] (i : ι) :
  LinearMap.IsReal (LinearMap.proj (R := R) (φ := φ) i) :=
by intro; simp

theorem LinearMap.single_comp_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)] [DecidableEq ι] (i : ι)
  (f g : B →ₗ[R] φ i) :
  LinearMap.single R φ i ∘ₗ f = LinearMap.single R φ i ∘ₗ g ↔ f = g := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply, Pi.single_inj]

theorem LinearMap.comp_proj_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)] (i : ι)
  (f g : φ i →ₗ[R] B) :
  f ∘ₗ LinearMap.proj (R := R) i = g ∘ₗ LinearMap.proj (R := R) i ↔ f = g := by
  classical
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.proj_apply]
  refine ⟨fun h x => ?_, fun h _ => h _⟩
  simpa only [Pi.single_eq_same] using h (Pi.single i x)

theorem LinearMap.proj_comp_inj
  {R ι B : Type*} [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)]
  [AddCommMonoid B] [Module R B] [(i : ι) → Module R (φ i)]
  (f g : B →ₗ[R] Π r, φ r) :
  (∀ i, LinearMap.proj (R := R) i ∘ₗ f = LinearMap.proj (R := R) i ∘ₗ g) ↔ f = g := by
  classical
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.proj_apply, funext_iff]
  rw [forall_comm]

theorem NonUnitalAlgHom.id_toLinearMap
  {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] :
  (LinearMapClass.linearMap (NonUnitalAlgHom.id R A) : A →ₗ[R] A) = 1 :=
rfl

theorem QuantumGraph.Real.conj_proj_isReal
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph.Real _ f) → ∀ (i : ι),
      QuantumGraph.Real _
        ((LinearMap.proj (R := ℂ) i) ∘ₗ f ∘ₗ LinearMap.adjoint (LinearMap.proj (R := ℂ) i)) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro f hf i
  simp only [QuantumGraph.real_iff, LinearMap.isReal_iff,
    LinearMap.real_comp]
  simp only [LinearMap.proj_adjoint,
    LinearMap.real_of_isReal (LinearMap.single_isReal (R := ℂ) (ι := ι) (φ := fun r =>
      Mat ℂ (p r)) _),
    LinearMap.real_of_isReal (LinearMap.proj_isReal (R := ℂ) (ι := ι)
      (φ := fun r => Mat ℂ (p r)) _), LinearMap.real_of_isReal hf.2, and_true]
  rw [← LinearMap.proj_adjoint,
    ← AlgHom.proj_toLinearMap]
  simp_rw [QuantumSet.schurMul_algHom_comp_algHom_adjoint, hf.1]

open scoped Classical in
omit [DecidableEq ι] [(i : ι) → DecidableEq (p i)] in
lemma schurMul_proj_adjoint_comp
  {B : Type*} [starAlgebra B] [QuantumSet B]
  : letI : DecidableEq ι := Classical.decEq ι
    letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (i : ι) (f g : B →ₗ[ℂ] Mat ℂ (p i)),
      (LinearMap.adjoint (LinearMap.proj i) ∘ₗ f) •ₛ (LinearMap.adjoint (LinearMap.proj i) ∘ₗ g)
        = LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
          ∘ₗ (f •ₛ g) := by
  classical
  withPiBlockQuantumCtx[φ]
  intro i f g
  simp only [LinearMap.proj_adjoint, ← NonUnitalAlgHom.single_toLinearMap,
    schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  congr 2
  exact Eq.symm (nonUnitalAlgHom_comp_mul (NonUnitalAlgHom.single ℂ (fun r ↦ Mat ℂ (p r)) i))

open scoped Classical in
omit [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (p i)] in
lemma schurMul_proj_comp
  {B : Type*} [starAlgebra B] [QuantumSet B] [Finite ι]
  : letI : DecidableEq ι := Classical.decEq ι
    letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ (f g : B →ₗ[ℂ] PiMat ℂ ι p) (i : ι),
      ((LinearMap.proj i) ∘ₗ f) •ₛ ((LinearMap.proj i) ∘ₗ g)
        = (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
          ∘ₗ (f •ₛ g) := by
  classical
  letI := Fintype.ofFinite ι
  withPiBlockQuantumCtx[φ]
  intro f g i
  simp only [schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  congr 2
  rw [← AlgHom.proj_toLinearMap]
  exact TensorProduct.mapMul'_commute_iff.mpr fun x ↦ congrFun rfl

lemma schurMul_comp_proj
  {B : Type*} [starAlgebra B] [QuantumSet B]
  : withPiBlockCoalgebraQuantum[φ]
    ∀ (i : ι),
      withMatrixQuantum[φ i]
        letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
          Mat ℂ (p i))).toCoalgebraStruct
        ∀ (f g : Mat ℂ (p i) →ₗ[ℂ] B),
          ((f ∘ₗ (LinearMap.proj i)) •ₛ (g ∘ₗ (LinearMap.proj i)))
            = (f •ₛ g) ∘ₗ (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro i
  withMatrixQuantumCtx[φ i]
  letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
    Mat ℂ (p i))).toCoalgebraStruct
  intro f g
  simp only [schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  have hcomul :
      TensorProduct.map
          (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
          (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i) ∘ₗ
        Coalgebra.comul =
      Coalgebra.comul ∘ₗ
        LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i := by
    apply_fun LinearMap.adjoint using LinearEquiv.injective _
    simp only [Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, TensorProduct.map_adjoint]
    rw [LinearMap.proj_adjoint, ← NonUnitalAlgHom.single_toLinearMap]
    have hadj :
        LinearMap.adjoint (Coalgebra.comul :
          PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p) =
          LinearMap.mul' ℂ (PiMat ℂ ι p) :=
      LinearMap.adjoint_adjoint (LinearMap.mul' ℂ (PiMat ℂ ι p))
    rw [hadj]
    exact (nonUnitalAlgHom_comp_mul
      (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i)).symm
  rw [LinearMap.comp_assoc, hcomul, ← LinearMap.comp_assoc]

lemma schurMul_comp_proj_adjoint
  {B : Type*} [starAlgebra B] [QuantumSet B]
  : withPiBlockCoalgebraQuantum[φ]
    ∀ (f g : PiMat ℂ ι p →ₗ[ℂ] B) (i : ι),
      withMatrixQuantum[φ i]
        letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
          Mat ℂ (p i))).toCoalgebraStruct
        (f ∘ₗ LinearMap.adjoint (LinearMap.proj i)) •ₛ (g ∘ₗ LinearMap.adjoint (LinearMap.proj i))
          = (f •ₛ g) ∘ₗ LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i) :=
by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro f g i
  withMatrixQuantumCtx[φ i]
  letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
    Mat ℂ (p i))).toCoalgebraStruct
  simp only [LinearMap.proj_adjoint, ← NonUnitalAlgHom.single_toLinearMap,
    schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  have hcomul :
      TensorProduct.map
          (LinearMapClass.linearMap (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i))
          (LinearMapClass.linearMap (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i)) ∘ₗ
        Coalgebra.comul =
      Coalgebra.comul ∘ₗ
        LinearMapClass.linearMap (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i) := by
    apply_fun LinearMap.adjoint using LinearEquiv.injective _
    simp only [Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, TensorProduct.map_adjoint]
    have hsingle :
        LinearMap.adjoint
            (LinearMapClass.linearMap
              (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i) :
                Mat ℂ (p i) →ₗ[ℂ] PiMat ℂ ι p) =
          LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i := by
      rw [NonUnitalAlgHom.single_toLinearMap, ← LinearMap.proj_adjoint]
      exact LinearMap.adjoint_adjoint _
    have hadjPi :
        LinearMap.adjoint (Coalgebra.comul :
          PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p) =
          LinearMap.mul' ℂ (PiMat ℂ ι p) :=
      LinearMap.adjoint_adjoint (LinearMap.mul' ℂ (PiMat ℂ ι p))
    rw [hsingle]
    simp only [hadjPi]
    rw [← AlgHom.proj_toLinearMap]
    exact TensorProduct.mapMul'_commute_iff.mpr fun x => congrFun rfl
  rw [LinearMap.comp_assoc, hcomul, ← LinearMap.comp_assoc]

theorem QuantumGraph.isReal_iff_conj_proj_adjoint_isReal
  : withPiBlockCoalgebraQuantum[φ]
    ∀ (i : ι),
      withMatrixQuantum[φ i]
        letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
          Mat ℂ (p i))).toCoalgebraStruct
        ∀ (f : Mat ℂ (p i) →ₗ[ℂ] Mat ℂ (p i)),
          QuantumGraph.Real _ f
            ↔
          QuantumGraph.Real (PiMat ℂ ι p)
            (LinearMap.adjoint (LinearMap.proj i) ∘ₗ f ∘ₗ LinearMap.proj i) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro i
  withMatrixQuantumCtx[φ i]
  letI := (Coalgebra.ofFiniteDimensionalHilbertAlgebra (R := ℂ) (A :=
    Mat ℂ (p i))).toCoalgebraStruct
  intro f
  simp only [QuantumGraph.real_iff, LinearMap.isReal_iff, LinearMap.real_comp]
  simp only [← LinearMap.comp_assoc]
  rw [schurMul_comp_proj, schurMul_proj_adjoint_comp, LinearMap.proj_adjoint]
  nth_rw 2 [LinearMap.real_of_isReal (LinearMap.single_isReal i)]
  nth_rw 3 [LinearMap.real_of_isReal (LinearMap.proj_isReal i)]
  rw [LinearMap.comp_proj_inj (R := ℂ) (ι := ι) (φ := fun r => Mat ℂ (p r)) i,
    LinearMap.comp_proj_inj (R := ℂ) (ι := ι) (φ := fun r => Mat ℂ (p r)) i]
  rw [LinearMap.single_comp_inj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i,
    LinearMap.single_comp_inj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i]

theorem QuantumGraph.Real.proj_adjoint_comp_proj_conj_isRealQuantumGraph
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph.Real (PiMat ℂ ι p) f) → ∀ (i : ι × ι),
      QuantumGraph.Real (PiMat ℂ ι p)
        (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i.1)
          ∘ₗ LinearMap.proj i.1
          ∘ₗ f
          ∘ₗ LinearMap.adjoint (LinearMap.proj i.2)
          ∘ₗ LinearMap.proj i.2) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro f hf i
  constructor
  · rw [schurMul_proj_adjoint_comp (hφ := hφ), schurMul_proj_comp (hφ := hφ)]
    simp only [← LinearMap.comp_assoc]
    rw [schurMul_comp_proj, schurMul_comp_proj_adjoint]
    simp only [LinearMap.comp_assoc, hf.1]
  · simp only [LinearMap.isReal_iff, LinearMap.real_comp,
      LinearMap.proj_adjoint, LinearMap.real_of_isReal
        (LinearMap.single_isReal (R := ℂ) (φ := fun r => Mat ℂ (p r)) _),
      LinearMap.real_of_isReal (LinearMap.proj_isReal (R := ℂ) (φ := fun r => Mat ℂ (p r)) _),
      LinearMap.real_of_isReal hf.2]

open scoped Classical in
omit [DecidableEq ι] [(i : ι) → DecidableEq (p i)] in
theorem schurMul_proj_adjoint_comp_of_ne_eq_zero
  {B : Type*} [starAlgebra B] [QuantumSet B]
  : letI : DecidableEq ι := Classical.decEq ι
    letI : ∀ i, DecidableEq (p i) := fun i => Classical.decEq (p i)
    withPiBlockQuantum[φ]
    ∀ {i j : ι} (_ : i ≠ j)
      (f : B →ₗ[ℂ] Mat ℂ (p i))
      (g : B →ₗ[ℂ] Mat ℂ (p j)),
      (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
        ∘ₗ f)
      •ₛ
      (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) j)
        ∘ₗ g)
      = 0 := by
  classical
  withPiBlockQuantumCtx[φ]
  intro i j hij f g
  simp only [schurMul_apply_apply, TensorProduct.map_comp, ← LinearMap.comp_assoc]
  have : LinearMap.mul' ℂ ((i : ι) → Mat ℂ (p i))
    ∘ₗ TensorProduct.map
      (LinearMap.adjoint (LinearMap.proj (R := ℂ) i))
      (LinearMap.adjoint (LinearMap.proj j))
    = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      LinearMap.proj_adjoint_apply, LinearMap.zero_apply]
    exact Matrix.includeBlock_hMul_ne_same hij x y
  simp_rw [this, LinearMap.zero_comp]

theorem schurMul_comp_proj_of_ne_eq_zero
  {B : Type*} [starAlgebra B] [QuantumSet B]
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {i j : ι} (_ : i ≠ j)
      (f : Mat ℂ (p i) →ₗ[ℂ] B)
      (g : Mat ℂ (p j) →ₗ[ℂ] B),
      (f ∘ₗ LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
      •ₛ
      (g ∘ₗ LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) j)
      = 0 := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro i j hij f g
  simp only [schurMul_apply_apply, TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  have hcomul :
      TensorProduct.map
          (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i)
          (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) j) ∘ₗ
        Coalgebra.comul = 0 := by
    apply_fun LinearMap.adjoint using LinearEquiv.injective _
    simp only [map_zero,
      LinearMap.adjoint_comp, TensorProduct.map_adjoint]
    rw [LinearMap.proj_adjoint, LinearMap.proj_adjoint,
      ← NonUnitalAlgHom.single_toLinearMap, ← NonUnitalAlgHom.single_toLinearMap]
    have hadj :
        LinearMap.adjoint (Coalgebra.comul :
          PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p ⊗[ℂ] PiMat ℂ ι p) =
          LinearMap.mul' ℂ (PiMat ℂ ι p) :=
      LinearMap.adjoint_adjoint (LinearMap.mul' ℂ (PiMat ℂ ι p))
    rw [hadj]
    change LinearMap.mul' ℂ ((i : ι) → Mat ℂ (p i)) ∘ₗ
        TensorProduct.map
          (LinearMapClass.linearMap (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) i))
          (LinearMapClass.linearMap (NonUnitalAlgHom.single ℂ (fun r => Mat ℂ (p r)) j)) =
      0
    apply TensorProduct.ext'
    intro x y
    ext k
    by_cases hki : k = i
    · subst k
      simp [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        NonUnitalAlgHom.single_apply, Pi.single_eq_of_ne hij]
    · simp [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        NonUnitalAlgHom.single_apply, Pi.single_eq_of_ne hki]
  rw [LinearMap.comp_assoc, hcomul]
  simp

theorem piMat_isRealQuantumGraph_iff_forall_conj_adjoint_proj_comp_proj
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      QuantumGraph.Real (PiMat ℂ ι p) f
        ↔
      ∀ i : ι × ι, QuantumGraph.Real (PiMat ℂ ι p)
        (LinearMap.adjoint (LinearMap.proj (R := ℂ) (φ := fun r => Mat ℂ (p r)) i.1)
          ∘ₗ LinearMap.proj i.1
          ∘ₗ f
          ∘ₗ LinearMap.adjoint (LinearMap.proj i.2)
          ∘ₗ LinearMap.proj i.2) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro f
  refine ⟨fun h i => h.proj_adjoint_comp_proj_conj_isRealQuantumGraph i, fun h => ?_⟩
  constructor
  · rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) f]
    simp only [map_sum, LinearMap.sum_apply]
    congr
    ext1 i
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [LinearMap.comp_assoc, (h i).1, add_eq_left]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    rw [Prod.eq_iff_fst_eq_snd_eq, not_and_or] at hj
    rcases hj with (h | h)
    · rw [schurMul_proj_adjoint_comp_of_ne_eq_zero h]
    · simp only [← LinearMap.comp_assoc]
      rw [schurMul_comp_proj_of_ne_eq_zero h]
  · simp only [LinearMap.isReal_iff]
    rw [LinearMap.eq_sum_conj_adjoint_proj_comp_proj (hφ := hφ) f]
    simp only [LinearMap.real_sum,
      LinearMap.comp_assoc, LinearMap.real_of_isReal (h _).2]

theorem Pi.single_zero_piFinTwo_same_apply (x : Matrix n n ℂ) :
  (Pi.single 0 x : PiMat ℂ (Fin 2) _) =
  MatProdAlgEquivPiMat (PiFinTwoSame n) (x, 0) := by
  ext1
  simp [MatProdAlgEquivPiMat, Pi.single, Function.update]
  rfl
theorem Pi.single_one_piFinTwo_same_apply (x : Matrix n n ℂ) :
  (Pi.single 1 x : PiMat ℂ (Fin 2) _) =
  MatProdAlgEquivPiMat (PiFinTwoSame n) (0, x) := by
  simp only [funext_iff, Fin.forall_fin_two, MatProdAlgEquivPiMat,
    matrixPiFinTwoAlgEquivProd_symm_apply,
    single_eq_same, dite_true, single_eq_of_ne (zero_ne_one' _),
    one_ne_zero, dite_false]
  exact ⟨rfl, rfl⟩

theorem
  PiMat_finTwo_same_swap_swap (x : PiMat ℂ (Fin 2) (PiFinTwoSame n)) :
  PiMatFinTwoSameSwapAlgEquiv
    (PiMatFinTwoSameSwapAlgEquiv x) = x :=
by simp [PiMatFinTwoSameSwapAlgEquiv]

theorem PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_zero (x : Matrix n n ℂ) :
  PiMatFinTwoSameSwapAlgEquiv (Pi.single 0 x) =
    (Pi.single 1 x : PiMat ℂ (Fin 2) (PiFinTwoSame n)) := by
  simp only [Pi.single_zero_piFinTwo_same_apply,
    PiMatFinTwoSameSwapAlgEquiv_apply, Pi.single_one_piFinTwo_same_apply]

theorem PiMatFinTwoSameSwapAlgEquiv_comp_linearMapSingle_zero :
  PiMatFinTwoSameSwapAlgEquiv.toLinearMap.comp (LinearMap.single ℂ _ 0) =
    (LinearMap.single ℂ _ 1 : _ →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n)) := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply]
  exact PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_zero

theorem PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_one (x : Matrix n n ℂ) :
  PiMatFinTwoSameSwapAlgEquiv (Pi.single 1 x) =
    (Pi.single 0 x : PiMat ℂ (Fin 2) (PiFinTwoSame n)) := by
  rw [← PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_zero,
    PiMat_finTwo_same_swap_swap]

theorem PiMatFinTwoSameSwapAlgEquiv_comp_linearMapSingle_one :
  PiMatFinTwoSameSwapAlgEquiv.toLinearMap ∘ₗ (LinearMap.single ℂ _ 1) =
    (LinearMap.single ℂ _ 0 : _ →ₗ[ℂ] PiMat ℂ (Fin 2) (PiFinTwoSame n)) := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply,
    LinearMap.single_apply]
  exact PiMatFinTwoSameSwapAlgEquiv_apply_piSingle_one

theorem QuantumGraph.Real.schurProjection_proj_conj
  : withPiBlockCoalgebraQuantum[φ]
    ∀ {f : PiMat ℂ ι p →ₗ[ℂ] PiMat ℂ ι p},
      (hf : QuantumGraph.Real _ f) → ∀ (i : ι × ι),
      schurProjection (A := Mat ℂ (p i.2)) (B := Mat ℂ (p i.1))
      ((LinearMap.proj (R := ℂ) i.1) ∘ₗ f
        ∘ₗ (LinearMap.adjoint (LinearMap.proj i.2))) := by
  withPiBlockCoalgebraQuantumCtx[φ]
  intro f hf i
  constructor
  · rw [schurMul_proj_comp (hφ := hφ), schurMul_comp_proj_adjoint (hφ := hφ), hf.1]
  · rw [LinearMap.isReal_iff]
    simp_rw [LinearMap.real_comp, LinearMap.real_of_isReal hf.2, LinearMap.proj_adjoint,
    LinearMap.real_of_isReal (LinearMap.proj_isReal (φ := fun r => Mat ℂ (p r)) _),
    LinearMap.real_of_isReal (LinearMap.single_isReal (φ := fun r => Mat ℂ (p r)) _)]
