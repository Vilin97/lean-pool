/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import LeanPool.Monlib4.QuantumGraph.Nontracial
import LeanPool.Monlib4.QuantumGraph.Iso
import LeanPool.Monlib4.LinearAlgebra.ToMatrixOfEquiv
import LeanPool.Monlib4.LinearAlgebra.Ips.MatIps
import LeanPool.Monlib4.QuantumGraph.QamA
import LeanPool.Monlib4.LinearAlgebra.Matrix.Spectra

/-!
# LeanPool.Monlib4.QuantumGraph.QamAExample

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.QamAExample`.
-/

section

/-!

# Examples of single-edged quantum graph

This file contains examples of single-edged quantum graphs over `M₂(ℂ)`. The main result is
  that all single-edged quantum graphs over `M₂(ℂ)` are isomorphic each other.

-/


open Matrix

open scoped Matrix Kronecker Functional

variable {n : Type _} [Fintype n] [DecidableEq n]

local notation "ℍ" => Matrix n n ℂ

private theorem and_true_iff (p : Prop) : p ∧ True ↔ p :=
  by simp

private theorem true_and_iff (p : Prop) : True ∧ p ↔ p :=
  by simp

private theorem false_and_iff (p : Prop) : False ∧ p ↔ False :=
  by simp

private theorem false_or_iff (p : Prop) : False ∨ p ↔ p :=
  by simp

/-- The trace functional on square matrices. -/
def traceModuleDual {𝕜 n : Type _} [Fintype n] [RCLike 𝕜] : Module.Dual 𝕜 (Matrix n n 𝕜) :=
  traceLinearMap n 𝕜 𝕜

/-- The trace functional is faithful and positive. -/
instance trace_isFaithfulPosMap {n : Type _} [Fintype n] {𝕜 : Type _} [RCLike 𝕜] :
   (traceModuleDual : Module.Dual 𝕜 (Matrix n n 𝕜)).IsFaithfulPosMap :=
  by
  simp_rw [Module.Dual.IsFaithfulPosMap_iff, Module.Dual.IsFaithful, Module.Dual.IsPosMap,
    traceModuleDual, traceLinearMap_apply,
    star_eq_conjTranspose, trace_conjTranspose_hMul_self_nonneg,
    trace_conjTranspose_hMul_self_eq_zero, imp_true_iff, and_true_iff]

theorem traceModuleDual_matrix {n : Type _} [Fintype n] [DecidableEq n] :
    (traceModuleDual : Module.Dual ℂ (Matrix n n ℂ)).matrix = 1 :=
  by
  ext i j
  have :=
    (traceModuleDual : Module.Dual ℂ (Matrix n n ℂ)).apply fun k l =>
      ite (j = k) (ite (i = l) 1 0) 0
  simp only [traceModuleDual, traceLinearMap_apply, trace_iff, mul_apply, mul_ite,
    MulZeroClass.mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
  rw [traceModuleDual, ← this]
  rfl

open scoped BigOperators

open scoped ComplexOrder

private theorem PosDef_one_rpow_eq_trace_matrix_rpow (r : ℝ) :
    (posDefOne : PosDef (1 : Matrix n n ℂ)).rpow r =
      (trace_isFaithfulPosMap :
              (traceModuleDual : Module.Dual ℂ ℍ).IsFaithfulPosMap).matrixIsPosDef.rpow
        r :=
  by
  calc
    (posDefOne : PosDef (1 : Matrix n n ℂ)).rpow r = 1 := posDefOne_rpow n r
    _ =
        (trace_isFaithfulPosMap :
            (traceModuleDual : Module.Dual ℂ ℍ).IsFaithfulPosMap).matrixIsPosDef.rpow r := by
      rw [Matrix.PosDef.rpow_cast _ r traceModuleDual_matrix, posDefOne_rpow]

theorem Matrix.smul_stdBasisMatrix {R α n m : Type _} [DecidableEq n] [DecidableEq m]
    [Zero R] [SMulZeroClass α R] (a : α) (i : n) (j : m) (x : R) :
    a • stdBasisMatrix i j x = stdBasisMatrix i j (a • x) := by
  ext k l
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    simp [stdBasisMatrix, Matrix.single, hki, hlj]

private theorem aux.ug :
    (trace_isFaithfulPosMap :
            (traceModuleDual : Module.Dual ℂ ℍ).IsFaithfulPosMap).toMatrix.symm =
      toLinOfAlgEquiv :=
  by
  rw [AlgEquiv.ext_iff]; intro x
  simp_rw [Module.Dual.IsFaithfulPosMap.toMatrix_symm_apply]
  simp_rw [toLinOfAlgEquiv_eq, rankOneStdBasis, one_smul, LinearMap.ext_iff,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.coe_mk, ContinuousLinearMap.coe_coe,
    rankOne_apply, Module.Dual.IsFaithfulPosMap.inner_coord', ←
    PosDef_one_rpow_eq_trace_matrix_rpow, posDefOne_rpow, Matrix.mul_one, AddHom.coe_mk,
      Matrix.smul_stdBasisMatrix,
    smul_eq_mul, Module.Dual.IsFaithfulPosMap.basis_apply,
    ← PosDef_one_rpow_eq_trace_matrix_rpow,
    posDefOne_rpow,
    Matrix.mul_one, Matrix.smul_stdBasisMatrix, smul_eq_mul, mul_one]
  intro x
  repeat'
    nth_rw 1 [← Finset.sum_product']
    simp_rw [Prod.mk.eta]
    apply Finset.sum_congr rfl
    intro _ _
  rfl

theorem Matrix.stdBasisMatrix.transpose {R n m : Type _} [DecidableEq n] [DecidableEq m]
    [Semiring R] (i : n) (j : m) : (stdBasisMatrix i j (1 : R))ᵀ = stdBasisMatrix j i (1 : R) :=
  by
  ext k l
  simp [transpose_apply, stdBasisMatrix, Matrix.single, and_comm]

open scoped TensorProduct

open scoped ComplexConjugate

private theorem linear_map.rsmul_adjoint {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) (r : ℝ) :
    LinearMap.adjoint ((r : 𝕜) • A) = (r : 𝕜) • LinearMap.adjoint A := by
  simp_rw [← @LinearMap.star_eq_adjoint 𝕜 E, star_smul, RCLike.star_def, RCLike.conj_ofReal]

/-- when a matrix $x$ is non-zero, then for any unitary $U$, we also have $f_U(x)$ is non-zero -/
private noncomputable def inner_aut_inv.of_ne_zero (U : unitaryGroup n ℂ)
    (x : { x : Matrix n n ℂ // x ≠ 0 }) : { x : Matrix n n ℂ // x ≠ 0 } :=
  haveI : innerAut (star U : unitaryGroup n ℂ) x.1 ≠ 0 ↔ x.1 ≠ 0 := by
    simp_rw [ne_eq, innerAut_eq_iff, innerAut_apply_zero]
  (⟨innerAut (star U : unitaryGroup n ℂ) x.1, this.mpr x.property⟩ :
    { x : Matrix n n ℂ // x ≠ 0 })

private theorem inner_aut_inv.of_ne_zero_eq (U : unitaryGroup n ℂ) (x : { x : ℍ // x ≠ 0 }) :
    (inner_aut_inv.of_ne_zero U x).1 = innerAut (star U : unitaryGroup n ℂ) x.1 :=
  rfl

theorem StarAlgEquiv.eq_comp_iff {R E₁ E₂ E₃ : Type _} [_inst_1 : CommSemiring R]
    [_inst_2 : Semiring E₂] [_inst_3 : Semiring E₃] [_inst_4 : AddCommMonoid E₁]
    [_inst_5 : Algebra R E₂] [_inst_6 : Algebra R E₃] [_inst_7 : Module R E₁] [_inst_8 : Star E₂]
    [_inst_9 : Star E₃] (f : E₂ ≃⋆ₐ[R] E₃) (x : E₁ →ₗ[R] E₂) (y : E₁ →ₗ[R] E₃) :
    f.toAlgEquiv.toLinearMap.comp x = y ↔ x = f.symm.toAlgEquiv.toLinearMap.comp y :=
  by
  constructor <;> intro h
  on_goal 1 => rw [← h]
  on_goal 2 => rw [h]
  all_goals
    rw [LinearMap.ext_iff]
    intro a
    simp only [LinearMap.comp_apply, StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.toLinearMap_apply,
      StarAlgEquiv.symm_apply_apply, StarAlgEquiv.apply_symm_apply]

theorem ite_comp {R U V W : Type _} [Semiring R] [AddCommMonoid U] [AddCommMonoid V]
    [AddCommMonoid W] [Module R U] [Module R V] [Module R W] {P : Prop} [Decidable P]
    {x y : W →ₗ[R] U} {f : V →ₗ[R] W} : ite P x y ∘ₗ f = ite P (x ∘ₗ f) (y ∘ₗ f) := by
  split_ifs <;> simp

theorem comp_ite {R U V W : Type _} [Semiring R] [AddCommMonoid U] [AddCommMonoid V]
    [AddCommMonoid W] [Module R U] [Module R V] [Module R W] {P : Prop} [Decidable P]
    {x y : W →ₗ[R] U} {f : U →ₗ[R] V} : f ∘ₗ ite P x y = ite P (f ∘ₗ x) (f ∘ₗ y) := by
  split_ifs <;> simp

theorem StarAlgEquiv.comp_symm_self {R U V : Type _} [CommSemiring R] [Semiring U] [Semiring V]
    [Algebra R U] [Algebra R V] [Star U] [Star V] {f : U ≃⋆ₐ[R] V} :
    f.toAlgEquiv.toLinearMap.comp f.symm.toAlgEquiv.toLinearMap = 1 := by
  rw [StarAlgEquiv.eq_comp_iff, LinearMap.comp_one]

theorem StarAlgEquiv.symm_comp_self {R U V : Type _} [CommSemiring R] [Semiring U] [Semiring V]
    [Algebra R U] [Algebra R V] [Star U] [Star V] {f : U ≃⋆ₐ[R] V} :
    f.symm.toAlgEquiv.toLinearMap.comp f.toAlgEquiv.toLinearMap = 1 := by
  simp only [LinearMap.ext_iff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    StarAlgEquiv.coe_toAlgEquiv, StarAlgEquiv.symm_apply_apply, Module.End.one_apply,
      forall_true_iff]

theorem Qam.iso_preserves_ir_reflexive [Nontrivial n] {φ : Module.Dual ℂ ℍ}
    [hφ : φ.IsFaithfulPosMap] {x y : ℍ →ₗ[ℂ] ℍ} (hxhy : @Qam.Iso n _ _ φ x y)
    (ir_reflexive : Prop) [Decidable ir_reflexive] :
    withMatrixQuantum[φ]
      letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (Qam.reflIdempotent hφ x 1 = ite ir_reflexive 1 0 ↔
        Qam.reflIdempotent hφ y 1 = ite ir_reflexive 1 0) :=
  by
  withMatrixQuantumCtx[φ]
  letI : Coalgebra ℂ ℍ := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  obtain ⟨f, hf, h⟩ := hxhy
  rw [StarAlgEquiv.comp_eq_iff, LinearMap.comp_assoc] at hf
  have := List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _
    _ f) 0 4
  have hisometry : StarAlgEquiv.IsIsometry f := by
    change Isometry f
    rw [isometry_iff_norm]
    exact this.mp h
  let conjugateMap : (ℍ →ₗ[ℂ] ℍ) → ℍ →ₗ[ℂ] ℍ :=
    fun A => f.toLinearMap ∘ₗ A ∘ₗ f.symm.toLinearMap
  have hconj_injective : Function.Injective conjugateMap := by
    intro A B hAB
    ext z i j
    have hz := LinearMap.congr_fun hAB (f z)
    have hmatrix : A z = B z := by
      simpa [conjugateMap, LinearMap.comp_apply] using hz
    exact congrFun (congrFun hmatrix i) j
  have hconj_one : conjugateMap 1 = 1 := by
    ext z
    simp [conjugateMap, LinearMap.comp_apply]
  have hconj_zero : conjugateMap 0 = 0 := by
    ext z
    simp [conjugateMap]
  have hconj_const : conjugateMap (ite ir_reflexive 1 0) = ite ir_reflexive 1 0 := by
    by_cases hir : ir_reflexive <;> simp [hir, hconj_one, hconj_zero]
  have hschur :
      Qam.reflIdempotent hφ (conjugateMap y) 1 =
        conjugateMap (Qam.reflIdempotent hφ y 1) := by
    simpa [conjugateMap, hconj_one] using
      (Qam.reflIdempotent_starAlgEquiv_conj (φ := φ) (f := f) hisometry y 1)
  rw [hf]
  rw [hschur]
  constructor
  · intro hA
    apply hconj_injective
    rw [hconj_const]
    exact hA
  · intro hA
    rw [hA, hconj_const]

/-- a function `f : A → B` is _almost injective_ if for all $x, y \in A$,
  if $f(x)=f(y)$ then there exists some $0\neq\alpha \in \mathbb{C}$ such that
  $x = \alpha y$ (in other words, $x$ and $y$ are co-linear) -/
def Function.IsAlmostInjective {A B : Type _} (f : A → B) [SMul ℂˣ A] : Prop :=
  ∀ x y : A, f x = f y ↔ ∃ α : ℂˣ, x = α • y

open scoped BigOperators ComplexConjugate

private theorem nontracial_basis_apply {Q : ℍ} (hQ : Q.PosDef) (i j k l : n) :
  (Matrix.stdBasisMatrix i j (1 : ℂ) * hQ.rpow (-(1 / 2))) k l
    = ite (i = k) (hQ.rpow (-(1 / 2)) j l) 0 := by
  by_cases hik : i = k
  · subst k
    simp [Matrix.mul_apply, stdBasisMatrix, Matrix.single]
  · simp [Matrix.mul_apply, stdBasisMatrix, Matrix.single, hik]

private theorem prod.eq' {α β : Type _} {p r : α} {q s : β} : (p, q) = (r, s) ↔ p = r ∧ q = s :=
  Prod.eq_iff_fst_eq_snd_eq

theorem Matrix.IsAlmostHermitian.spectrum {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) :
    _root_.spectrum ℂ (toLin' x) = {x_1 : ℂ | ∃ i : n, hx.eigenvalues i = x_1} :=
  by
  nth_rw 1 [Matrix.IsAlmostHermitian.eq_smul_matrix hx]
  nth_rw 1 [(hx.matrix_isHermitian).spectral_theorem'']
  rw [← _root_.map_smul, innerAut.spectrum_eq, ← diagonal_smul, Matrix.spectrum_toLin',
    spectrum_diagonal]
  simp [Set.range, Pi.smul_apply, Function.comp_apply, Matrix.IsAlmostHermitian.eigenvalues]

private theorem matrix.is_almost_hermitian.matrix_IsHermitian.eigenvalues_ne_zero
    {x : { x : ℍ // x ≠ 0 }} (hx : x.1.IsAlmostHermitian) :
    ((@RCLike.ofReal ℂ _) ∘ hx.matrix_isHermitian.eigenvalues : n → ℂ) ≠ 0 :=
  by
  intro hh
  have heig : hx.matrix_isHermitian.eigenvalues = 0 := by
    ext i
    have hi := congrFun hh i
    simp only [Function.comp_apply, Pi.zero_apply] at hi
    exact RCLike.ofReal_inj.mp hi
  have hmatrix_zero : hx.matrix = 0 := (hx.matrix_isHermitian.eigenvalues_eq_zero_iff).mp heig
  have h := hx.eq_smul_matrix
  rw [hmatrix_zero, smul_zero] at h
  exact x.property h

private theorem example_aux {x : { x : Matrix (Fin 2) (Fin 2) ℂ // x ≠ 0 }}
    (hx : (x.val : Matrix (Fin 2) (Fin 2) ℂ).IsAlmostHermitian)
    (hh : (hx.matrix_isHermitian.eigenvalues 0 : ℂ) = -(hx.matrix_isHermitian.eigenvalues 1 : ℂ))
    (i : Fin 2) : (hx.matrix_isHermitian.eigenvalues i : ℂ) ≠ 0 :=
  by
  have h := matrix.is_almost_hermitian.matrix_IsHermitian.eigenvalues_ne_zero hx
  simp only [ne_eq, funext_iff, Function.comp_apply, Pi.zero_apply] at h
  simp only [Complex.ofReal'_eq_isROrC_ofReal] at *
  revert i
  simp_rw [Fin.forall_fin_two, ne_eq, hh, neg_eq_zero, and_self_iff] at h ⊢
  exact h

theorem spectra_fin_two {x : Matrix (Fin 2) (Fin 2) ℂ}
    (hx : (x : Matrix (Fin 2) (Fin 2) ℂ).IsAlmostHermitian) :
    hx.spectra = {(hx.eigenvalues 0 : ℂ), (hx.eigenvalues 1 : ℂ)} :=
  rfl

theorem spectra_fin_two' {x : Matrix (Fin 2) (Fin 2) ℂ}
    (hx : (x : Matrix (Fin 2) (Fin 2) ℂ).IsAlmostHermitian) :
    hx.spectra = [(hx.eigenvalues 0 : ℂ), (hx.eigenvalues 1 : ℂ)] :=
  rfl

theorem spectra_fin_two'' {α : Type _} (a : Fin 2 → α) :
    Multiset.map (a : Fin 2 → α) Finset.univ.val = {a 0, a 1} :=
  rfl

open scoped List
theorem List.coe_inj {α : Type _} (l₁ l₂ : List α) : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Multiset.coe_eq_coe

theorem spectra_fin_two_ext_aux {A : Type _} (α β γ : A) :
    ({α, α} : Multiset A) = {β, γ} ↔ α = β ∧ α = γ :=
  by
  simp only [Multiset.insert_eq_cons]
  constructor
  · intro h
    simp_rw [Multiset.cons_eq_cons, Multiset.singleton_inj, Multiset.singleton_eq_cons_iff] at h
    rcases h with (h1 | ⟨_, cs, ⟨hcs₁, _⟩, ⟨hcs₃, _⟩⟩)
    · exact h1
    · exact ⟨hcs₁, hcs₃.symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem spectra_fin_two_ext {α : Type _} (α₁ α₂ β₁ β₂ : α) :
    ({α₁, α₂} : Multiset α) = {β₁, β₂} ↔ α₁ = β₁ ∧ α₂ = β₂ ∨ α₁ = β₂ ∧ α₂ = β₁ :=
  by
  by_cases H₁ : α₁ = α₂
  · rw [H₁, spectra_fin_two_ext_aux]
    constructor
    · rintro ⟨h1, h2⟩
      left
      exact ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
  by_cases h' : α₁ = β₁
  · simp_rw [h', true_and_iff, Multiset.insert_eq_cons, Multiset.cons_inj_right,
      Multiset.singleton_inj]
    constructor
    · intro hi
      left
      exact hi
    rintro (h | ⟨_, h2⟩)
    · exact h
    · rw [← h', eq_comm] at h2
      contradiction
  simp_rw [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_inj,
    Multiset.singleton_eq_cons_iff, ne_eq, h', false_and_iff, false_or_iff, not_false_iff,
    true_and_iff]
  simp only [exists_eq_right_right, and_true_iff, eq_comm]
  simp_rw [and_comm]

@[reducible, instance]
def Multiset.hasSmul {α : Type _} [SMul ℂ α] : SMul ℂ (Multiset α)
    where smul a s := s.map ((· • ·) a)

theorem Multiset.smul_fin_two {α : Type _} [SMul ℂ α] (a b : α) (c : ℂ) :
    (c • ({a, b} : Multiset α) : Multiset α) = {c • a, c • b} :=
  rfl

omit [Fintype n] [DecidableEq n] in
theorem IsAlmostHermitian.smul_eq {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) (c : ℂ) :
    (hx.smul c).scalar • (hx.smul c).matrix = c • x := by rw [← (hx.smul c).eq_smul_matrix]

theorem spectra_fin_two_ext_of_traceless {α₁ α₂ β₁ β₂ : ℂ} (hα₂ : α₂ ≠ 0) (hβ₂ : β₂ ≠ 0)
    (h₁ : α₁ = -α₂) (h₂ : β₁ = -β₂) : ∃ c : ℂˣ, ({α₁, α₂} : Multiset ℂ) = (c : ℂ) • {β₁, β₂} :=
  by
  simp_rw [h₁, h₂, Multiset.smul_fin_two, smul_neg]
  use Units.mk0 (α₂ * β₂⁻¹) (mul_ne_zero hα₂ (inv_ne_zero hβ₂))
  simp_rw [Units.val_mk0, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hβ₂, mul_one]

theorem Matrix.IsAlmostHermitian.trace {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) :
    x.trace = ∑ i, hx.eigenvalues i :=
  by
  nth_rw 1 [hx.eq_smul_matrix]
  rw [trace_smul, hx.matrix_isHermitian.trace_eq_sum_eigenvalues]
  simp [Matrix.IsAlmostHermitian.eigenvalues, Finset.mul_sum]

/-- The unitary eigenvector matrix chosen for an almost-Hermitian matrix. -/
@[reducible]
noncomputable def Matrix.IsAlmostHermitian.eigenvectorUnitary {x : Matrix n n ℂ}
    (hx : x.IsAlmostHermitian) : unitaryGroup n ℂ :=
hx.matrix_isHermitian.eigenvectorUnitary
/-- The eigenvector matrix chosen for an almost-Hermitian matrix. -/
@[reducible]
noncomputable def Matrix.IsAlmostHermitian.eigenvectorMatrix {x : Matrix n n ℂ}
  (hx : x.IsAlmostHermitian) : Matrix n n ℂ :=
hx.matrix_isHermitian.eigenvectorMatrix

theorem Matrix.IsAlmostHermitian.eigenvectorMatrix_eq {x : Matrix n n ℂ}
    (hx : x.IsAlmostHermitian) : hx.eigenvectorMatrix = hx.matrix_isHermitian.eigenvectorMatrix :=
  rfl
theorem Matrix.IsAlmostHermitian.eigenvectorUnitary_eq {x : Matrix n n ℂ}
  (hx : x.IsAlmostHermitian) :
  ↑hx.eigenvectorUnitary = hx.eigenvectorMatrix :=
rfl

theorem Matrix.IsAlmostHermitian.spectral_theorem' {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) :
    x =
      hx.scalar •
        innerAut hx.eigenvectorUnitary
          (diagonal ((@RCLike.ofReal ℂ _) ∘ hx.matrix_isHermitian.eigenvalues)) :=
  by rw [← Matrix.IsHermitian.spectral_theorem'', ← hx.eq_smul_matrix]

theorem Matrix.IsAlmostHermitian.eigenvalues_eq {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) :
    hx.eigenvalues = hx.scalar • ((@RCLike.ofReal ℂ _) ∘ hx.matrix_isHermitian.eigenvalues :
      n → ℂ) :=
  rfl

theorem Matrix.IsAlmostHermitian.spectral_theorem {x : Matrix n n ℂ} (hx : x.IsAlmostHermitian) :
    x =
      innerAut hx.eigenvectorUnitary (diagonal hx.eigenvalues) :=
  by
  simp_rw [hx.eigenvalues_eq, diagonal_smul, _root_.map_smul]
  exact Matrix.IsAlmostHermitian.spectral_theorem' _

theorem Matrix.IsAlmostHermitian.eigenvalues_eq_zero_iff {x : Matrix n n ℂ}
    (hx : x.IsAlmostHermitian) : hx.eigenvalues = 0 ↔ x = 0 :=
  by
  rw [Matrix.IsAlmostHermitian.eigenvalues_eq]
  conv_rhs => rw [hx.eq_smul_matrix]
  rw [smul_eq_zero, smul_eq_zero]
  have hcomp :
      ((@RCLike.ofReal ℂ _) ∘ hx.matrix_isHermitian.eigenvalues : n → ℂ) = 0 ↔
        hx.matrix_isHermitian.eigenvalues = 0 := by
    constructor
    · intro h
      ext i
      exact RCLike.ofReal_inj.mp (congrFun h i)
    · intro h
      ext i
      simp [h]
  rw [hcomp, hx.matrix_isHermitian.eigenvalues_eq_zero_iff]

private theorem matrix.is_almost_hermitian.eigenvalues_eq_zero_iff_aux
    {x : Matrix (Fin 2) (Fin 2) ℂ} (hx : x.IsAlmostHermitian) :
    hx.eigenvalues 0 = 0 ∧ hx.eigenvalues 1 = 0 ↔ x = 0 :=
  by
  rw [← hx.eigenvalues_eq_zero_iff, funext_iff]
  simp_rw [Fin.forall_fin_two, Pi.zero_apply]

omit [Fintype n] in
theorem Matrix.diagonal_eq_zero_iff {x : n → ℂ} : diagonal x = 0 ↔ x = 0 := by
  simp_rw [← diagonal_zero, diagonal_eq_diagonal_iff, funext_iff, Pi.zero_apply]

theorem Matrix.unitaryGroup.star_mul_cancel_right {U₁ U₂ : unitaryGroup n ℂ} :
  U₁ * star U₂ * U₂ = U₁ :=
by simp only [mul_assoc, Unitary.star_mul_self, mul_one]

theorem qamA.finTwoIso (x y : { x : Matrix (Fin 2) (Fin 2) ℂ // x ≠ 0 })
    : withMatrixQuantum[(traceModuleDual : Module.Dual ℂ (Matrix (Fin 2) (Fin 2) ℂ))]
      letI : Coalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
        Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (hx1 : IsSelfAdjoint (qamA trace_isFaithfulPosMap x)) →
      (hx2 :
        Qam.reflIdempotent trace_isFaithfulPosMap (qamA trace_isFaithfulPosMap x) 1 = 0) →
      (hy1 : IsSelfAdjoint (qamA trace_isFaithfulPosMap y)) →
      (hy2 :
        Qam.reflIdempotent trace_isFaithfulPosMap (qamA trace_isFaithfulPosMap y) 1 = 0) →
      @Qam.Iso (Fin 2) _ _ traceModuleDual (qamA trace_isFaithfulPosMap x)
        (qamA trace_isFaithfulPosMap y) :=
  by
  withMatrixQuantumCtx[(traceModuleDual : Module.Dual ℂ (Matrix (Fin 2) (Fin 2) ℂ))]
  letI : Coalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
    Coalgebra.ofFiniteDimensionalHilbertAlgebra
  intro hx1 hx2 hy1 hy2
  simp_rw [qamA.iso_iff, traceModuleDual_matrix, Commute.one_left, and_true_iff,
    _root_.map_smul]
  rw [exists_comm]
  obtain ⟨Hx, _⟩ := (qamA.is_self_adjoint_iff x).mp hx1
  obtain ⟨Hy, _⟩ := (qamA.is_self_adjoint_iff y).mp hy1
  simp_rw [qamA.is_irreflexive_iff, Hx.trace, Hy.trace, Fin.sum_univ_two,
    add_eq_zero_iff_eq_neg] at hx2 hy2
  rw [Matrix.IsAlmostHermitian.spectral_theorem Hx, Matrix.IsAlmostHermitian.spectral_theorem Hy]
  have HX : diagonal Hx.eigenvalues = of ![![-Hx.eigenvalues 1, 0], ![0, Hx.eigenvalues 1]] :=
    by
    rw [← hx2, ← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, diagonal_apply, of_apply, if_true, one_ne_zero,
      if_false, zero_ne_one, if_false]
    simp only [cons_val_zero, cons_val_one, and_self_iff]
  have HY : diagonal Hy.eigenvalues = of ![![-Hy.eigenvalues 1, 0], ![0, Hy.eigenvalues 1]] :=
    by
    rw [← hy2, ← Matrix.ext_iff]
    simp only [Fin.forall_fin_two, diagonal_apply, of_apply, if_true, one_ne_zero,
      if_false, zero_ne_one, if_false]
    simp only [cons_val_zero, cons_val_one, and_self_iff]
  simp_rw [HY, HX, innerAut_apply_innerAut]
  have hx₁ : Hx.eigenvalues 1 ≠ 0 := by
    intro hx₁
    have : diagonal Hx.eigenvalues = 0 :=
      by
      rw [HX, hx₁, neg_zero, ← Matrix.ext_iff]
      simp_rw [Fin.forall_fin_two]
      simp only [of_apply]
      simp only [cons_val_zero, cons_val_one]
      aesop
    rw [Matrix.diagonal_eq_zero_iff, Matrix.IsAlmostHermitian.eigenvalues_eq_zero_iff] at this
    exact (Subtype.mem x) this
  have hy₁ : Hy.eigenvalues 1 ≠ 0 := by
    intro hy₁
    have : diagonal Hy.eigenvalues = 0 :=
      by
      rw [HY, hy₁, neg_zero, ← Matrix.ext_iff]
      simp_rw [Fin.forall_fin_two]
      simp only [of_apply]
      simp only [cons_val_zero, cons_val_one]
      aesop
    rw [Matrix.diagonal_eq_zero_iff, Matrix.IsAlmostHermitian.eigenvalues_eq_zero_iff] at this
    exact (Subtype.mem y) this
  use Units.mk0 (Hx.eigenvalues 1 * (Hy.eigenvalues 1)⁻¹) (mul_ne_zero hx₁ (inv_ne_zero hy₁))
  use Hx.eigenvectorUnitary * star Hy.eigenvectorUnitary
  -- use ⟨Hx.eigenvectorMatrix, Hx.eigenvectorMatrix_mem_unitaryGroup⟩ * star
  -- (⟨Hy.eigenvectorMatrix, Hy.eigenvectorMatrix_mem_unitaryGroup⟩ : unitaryGroup (Fin 2) ℂ)
  have :
    (Hx.eigenvalues 1 * (Hy.eigenvalues 1)⁻¹) • diagonal Hy.eigenvalues = diagonal Hx.eigenvalues :=
    by
    rw [HX, HY]
    simp only [smul_of, smul_cons, smul_eq_mul, mul_neg, MulZeroClass.mul_zero,
      smul_empty, EmbeddingLike.apply_eq_iff_eq]
    simp only [inv_mul_cancel_right₀ hy₁]
  simp_rw [Matrix.unitaryGroup.star_mul_cancel_right, Units.val_mk0,
    ← _root_.map_smul, ← HY, ← HX, this]

theorem Qam.finTwoIsoOfSingleEdge {A B : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ} :
    withMatrixQuantum[(traceModuleDual : Module.Dual ℂ (Matrix (Fin 2) (Fin 2) ℂ))]
      letI : Coalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
        Coalgebra.ofFiniteDimensionalHilbertAlgebra
      (hx0 : RealQam trace_isFaithfulPosMap A) →
      (hy0 : RealQam trace_isFaithfulPosMap B) →
      (hx : hx0.edges = 1) → (hy : hy0.edges = 1) →
      (hx1 : _root_.IsSelfAdjoint A) →
      (hx2 : Qam.reflIdempotent trace_isFaithfulPosMap A 1 = 0) →
      (hy1 : _root_.IsSelfAdjoint B) →
      (hy2 : Qam.reflIdempotent trace_isFaithfulPosMap B 1 = 0) →
      @Qam.Iso (Fin 2) _ _ traceModuleDual A B :=
  by
  withMatrixQuantumCtx[(traceModuleDual : Module.Dual ℂ (Matrix (Fin 2) (Fin 2) ℂ))]
  letI : Coalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
    Coalgebra.ofFiniteDimensionalHilbertAlgebra
  intro hx0 hy0 hx hy hx1 hx2 hy1 hy2
  rw [RealQam.edges_eq_one_iff] at hx hy
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  exact qamA.finTwoIso x y hx1 hx2 hy1 hy2

end
