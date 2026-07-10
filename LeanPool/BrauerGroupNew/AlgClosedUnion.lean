/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Tensor products over algebraic closures

This file ports auxiliary results about finite intermediate fields inside an algebraic
closure and tensor products over their directed union.
-/

suppress_compilation

open Module TensorProduct

universe u

section

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]

lemma dim_eq : Module.finrank K V = Module.finrank L (L ⊗[K] V) := by
  let b := Module.finBasis K V
  let b' := Algebra.TensorProduct.basis L b
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end

section
variable (K K_bar : Type u) [Field K] [Field K_bar] [Algebra K K_bar] [IsAlgClosure K K_bar]

variable (A : Type u) [AddCommGroup A] [Module K A]

open scoped IntermediateField

/-- The image of scalar extension from an intermediate field tensor product. -/
def intermediateTensor (L : IntermediateField K K_bar) : Submodule K (K_bar ⊗[K] A) :=
  LinearMap.range (LinearMap.rTensor _ (L.val.toLinearMap) : L ⊗[K] A →ₗ[K] K_bar ⊗[K] A)

/-- The same image as `intermediateTensor`, regarded as a module over the intermediate field. -/
def intermediateTensor' (L : IntermediateField K K_bar) : Submodule L (K_bar ⊗[K] A) :=
  LinearMap.range ({LinearMap.rTensor _ (L.val.toLinearMap) with
    map_smul' l x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x a =>
        simp only [smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          _root_.map_mul, IntermediateField.coe_val]; rfl
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] } : L ⊗[K] A →ₗ[L] K_bar ⊗[K] A)
/-- The range-restricted tensor map identifies an intermediate tensor with `L ⊗[K] A`. -/
def intermediateTensorEquiv (L : IntermediateField K K_bar) :
    intermediateTensor K K_bar A L ≃ₗ[K] L ⊗[K] A :=
  .symm <| .ofBijective (LinearMap.rangeRestrict _) ⟨by
    intro x y hxy
    simp only [LinearMap.rangeRestrict, Subtype.ext_iff, LinearMap.codRestrict_apply] at hxy
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (fun x y h => by simpa using h) hxy,
      LinearMap.surjective_rangeRestrict _⟩

omit [IsAlgClosure K K_bar] in
@[simp]
lemma intermediateTensorEquiv_apply_tmul (L : IntermediateField K K_bar)
      (x : L) (a : A) (h : x.1 ⊗ₜ[K] a ∈ intermediateTensor K K_bar A L) :
    intermediateTensorEquiv K K_bar A L ⟨_, h⟩ =
    x ⊗ₜ a := by
  simp only [intermediateTensorEquiv]
  refine Eq.trans (congrArg _ ?_) (LinearEquiv.ofBijective_symm_apply_apply
    (LinearMap.rTensor A L.val.toLinearMap).rangeRestrict (x ⊗ₜ[K] a))
  apply Subtype.ext
  simp only [LinearMap.codRestrict_apply, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, IntermediateField.coe_val]
/-- The `L`-linear version of `intermediateTensorEquiv`. -/
def intermediateTensorEquiv' (L : IntermediateField K K_bar) :
    intermediateTensor' K K_bar A L ≃ₗ[L] L ⊗[K] A where
  toFun := intermediateTensorEquiv K K_bar A L
  map_add' := map_add _
  map_smul' := by
    rintro x ⟨-, ⟨y, rfl⟩⟩
    simp only [RingHom.id_apply]
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, SetLike.mk_smul_mk, smul_zero]
      erw [map_zero]
      rw [smul_zero]
    | tmul y a =>
      change (intermediateTensorEquiv K K_bar A L) ⟨↑(x * y) ⊗ₜ[K] a, _⟩ =
        x • (intermediateTensorEquiv K K_bar A L) ⟨↑y ⊗ₜ[K] a, _⟩
      rw [intermediateTensorEquiv_apply_tmul, intermediateTensorEquiv_apply_tmul]
      rfl
    | add y z hy hz =>
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, SetLike.mk_smul_mk, map_add,
        smul_add] at hy hz ⊢
      convert congr($hy + $hz) using 1
      · rw [← (intermediateTensorEquiv K K_bar A L).map_add]; rfl
      · erw [← smul_add, ← (intermediateTensorEquiv K K_bar A L).map_add]; rfl
  invFun := (intermediateTensorEquiv K K_bar A L).symm
  left_inv := (intermediateTensorEquiv K K_bar A L).left_inv
  right_inv := (intermediateTensorEquiv K K_bar A L).right_inv

omit [IsAlgClosure K K_bar] in
lemma mem_intermediateTensor_iff_mem_intermediateTensor'
    {L : IntermediateField K K_bar} {x : K_bar ⊗[K] A} :
    x ∈ intermediateTensor K K_bar A L ↔ x ∈ intermediateTensor' K K_bar A L := by
  simp only [intermediateTensor, LinearMap.mem_range, intermediateTensor', LinearMap.coe_mk,
    LinearMap.coe_toAddHom]

omit [IsAlgClosure K K_bar] in
lemma intermediateTensor_mono {L1 L2 : IntermediateField K K_bar} (h : L1 ≤ L2) :
    intermediateTensor K K_bar A L1 ≤ intermediateTensor K K_bar A L2 := by
  have e1 : (LinearMap.rTensor _ (L1.val.toLinearMap) : L1 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) =
    (LinearMap.rTensor _ (L2.val.toLinearMap) : L2 ⊗[K] A →ₗ[K] K_bar ⊗[K] A) ∘ₗ
    (LinearMap.rTensor A (L1.inclusion h).toLinearMap : L1 ⊗[K] A →ₗ[K] L2 ⊗[K] A) := by
    rw [← LinearMap.rTensor_comp]; rfl
  delta intermediateTensor
  rw [e1, LinearMap.range_comp, Submodule.map_le_iff_le_comap]
  rintro _ ⟨x, rfl⟩
  simp only [Submodule.mem_comap, LinearMap.mem_range, exists_apply_eq_apply]

/-- Finite-dimensional intermediate fields of the algebraic closure. -/
abbrev SetOfFinite : Set (IntermediateField K K_bar) :=
  {M | FiniteDimensional K M}

omit [IsAlgClosure K K_bar] in
lemma is_direct : DirectedOn (fun x x_1 ↦ x ≤ x_1)
    (Set.range fun (L : SetOfFinite K K_bar) ↦ intermediateTensor K K_bar A L) := by
  rintro _ ⟨⟨L1, (hL1 : FiniteDimensional _ _)⟩, rfl⟩ _ ⟨⟨L2, (hL2 : FiniteDimensional _ _)⟩, rfl⟩
  refine ⟨intermediateTensor K K_bar A (L1 ⊔ L2), ⟨⟨L1 ⊔ L2, show FiniteDimensional _ _ from
    ?_⟩, rfl⟩, ⟨intermediateTensor_mono K K_bar A le_sup_left,
      intermediateTensor_mono K K_bar A le_sup_right⟩⟩
  · apply (config := { allowSynthFailures := true }) IntermediateField.finiteDimensional_sup

omit [IsAlgClosure K K_bar] in
lemma SetOfFinite_nonempty : (Set.range fun (L : SetOfFinite K K_bar) ↦
    intermediateTensor K K_bar A L).Nonempty := by
  refine ⟨intermediateTensor K K_bar A ⊥, ⟨⟨⊥, ?_⟩, rfl⟩⟩
  simp only [SetOfFinite, Set.mem_setOf_eq]
  infer_instance

/-- K_bar ⊗[K] A = union of all finite subextension of K ⊗ A -/
theorem inter_tensor_union :
    ⨆ (L : SetOfFinite K K_bar),
    (intermediateTensor K K_bar A L) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  |zero => simp
  |tmul x a =>
    have fin0: FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional (by
      observe : IsAlgebraic K x
      exact Algebra.IsIntegral.isIntegral x)
    exact Submodule.mem_sSup_of_directed (SetOfFinite_nonempty K K_bar A) (is_direct K K_bar A) |>.2
      ⟨intermediateTensor K K_bar A K⟮x⟯, ⟨⟨⟨K⟮x⟯, fin0⟩, rfl⟩,
        ⟨(⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ ⊗ₜ a), by simp⟩⟩⟩
  |add x y hx hy =>
  apply AddMemClass.add_mem <;> assumption

theorem algclosure_element_in (x : K_bar ⊗[K] A) : ∃(F : IntermediateField K K_bar),
    FiniteDimensional K F ∧ x ∈ intermediateTensor K K_bar A F := by
  have mem : x ∈ (⊤ : Submodule K _) := ⟨⟩
  rw [← inter_tensor_union K K_bar A] at mem
  obtain ⟨_, ⟨⟨L, hL1⟩, rfl⟩, hL⟩ := Submodule.mem_sSup_of_directed (SetOfFinite_nonempty K K_bar A)
    (is_direct K K_bar A)|>.1 mem
  refine ⟨L, ⟨hL1, hL⟩⟩

/-- A finite intermediate field whose tensor image contains a chosen tensor element. -/
def subfieldOf (x : K_bar ⊗[K] A) : IntermediateField K K_bar :=
  algclosure_element_in K K_bar A x|>.choose

instance (x : K_bar ⊗[K] A) : FiniteDimensional K (subfieldOf K K_bar A x) :=
  (algclosure_element_in K K_bar A _).choose_spec.1

theorem mem_subfieldOf (x : K_bar ⊗[K] A) : x ∈ intermediateTensor K K_bar A
    (subfieldOf K K_bar A x) := (algclosure_element_in K K_bar A _).choose_spec.2

theorem mem_subfieldOf' (x : K_bar ⊗[K] A) : x ∈ intermediateTensor' K K_bar A
    (subfieldOf K K_bar A x) := by
  rw [← mem_intermediateTensor_iff_mem_intermediateTensor']
  exact mem_subfieldOf K K_bar A x

end

namespace lemmaTto

variable (n : ℕ) [NeZero n] (k k_bar A : Type u) [Field k] [Field k_bar] [Algebra k k_bar]
  [IsAlgClosure k k_bar] [Ring A] [Algebra k A] [FiniteDimensional k A]
  (iso : k_bar ⊗[k] A ≃ₐ[k_bar] Matrix (Fin n) (Fin n) k_bar)

/-- The basis of `k_bar ⊗[k] A` pulled back from the standard matrix basis. -/
def ee : Basis (Fin n × Fin n) k_bar (k_bar ⊗[k] A) :=
  Basis.map (Matrix.stdBasis k_bar _ _) iso.symm

local notation "e" => ee n k k_bar A iso

omit [NeZero n] [IsAlgClosure k k_bar] [FiniteDimensional k A] in
@[simp]
lemma ee_apply (i : Fin n × Fin n) : iso (e i) = Matrix.stdBasis k_bar (Fin n) (Fin n) i := by
  apply_fun iso.symm
  simp only [AlgEquiv.symm_apply_apply]
  have := Basis.map_apply (Matrix.stdBasis k_bar (Fin n) (Fin n)) iso.symm.toLinearEquiv i
  erw [← this]

/-- The finite intermediate field generated by all basis coordinates. -/
def ℒℒ : IntermediateField k k_bar :=
  ⨆ (i : Fin n × Fin n), subfieldOf k k_bar A (e i)

local notation "ℒ" => ℒℒ n k k_bar A iso

instance : FiniteDimensional k ℒ :=
  IntermediateField.finiteDimensional_iSup_of_finite

/-- Inclusion of the coordinate field of a basis vector into the generated field `ℒ`. -/
def f (i : Fin n × Fin n) : subfieldOf k k_bar A (e i) →ₐ[k] ℒ :=
  subfieldOf k k_bar A (e i)|>.inclusion (le_sSup ⟨i, rfl⟩)

/-- The pulled-back basis vector, regarded in the `ℒ`-linear intermediate tensor submodule. -/
def eHat' (i : Fin n × Fin n) : intermediateTensor' k k_bar A ℒ :=
  ⟨e i, by
    rw [← mem_intermediateTensor_iff_mem_intermediateTensor']
    exact intermediateTensor_mono k k_bar A (le_sSup (by simp)) <| mem_subfieldOf k k_bar A (e i)⟩

local notation "e^'" => eHat' n k k_bar A iso
local notation "k⁻" => k_bar

omit [NeZero n] [FiniteDimensional k A] in
theorem eHat_linear_independent : LinearIndependent ℒ e^' := by
  rw [linearIndependent_iff']
  intro s g h
  have h' : ∑ i ∈ s, algebraMap ℒ k⁻ (g i) • e i = 0 := by
    apply_fun Submodule.subtype _ at h
    rw [map_zero] at h
    convert h using 1
    simp only [map_sum, map_smul, Submodule.coe_subtype, eHat']
    apply Finset.sum_congr rfl
    intro x hx
    rfl
  have H := (linearIndependent_iff'.1 <| e |>.linearIndependent) s (algebraMap ℒ k⁻ ∘ g) h'
  intro i hi
  simpa using H i hi

-- shortcut instance search
instance : Module ℒ (ℒ ⊗[k] A) := TensorProduct.leftModule

instance : FiniteDimensional ℒ (intermediateTensor' k k⁻ A ℒ) :=
    Module.Finite.equiv (intermediateTensorEquiv' k k_bar A ℒ).symm

omit [NeZero n] in
theorem dim_ℒ_eq : Module.finrank ℒ (intermediateTensor' k k⁻ A ℒ) = n^2 := by
    have eq1 := dim_eq k k⁻ A |>.trans iso.toLinearEquiv.finrank_eq
    simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at eq1
    rw [pow_two, ← eq1, dim_eq k ℒ A]
    exact LinearEquiv.finrank_eq (intermediateTensorEquiv' k k_bar A ℒ)

/-- The basis of the intermediate tensor submodule over `ℒ`. -/
def eHat : Basis (Fin n × Fin n) ℒ (intermediateTensor' k k_bar A ℒ) :=
  basisOfLinearIndependentOfCardEqFinrank (eHat_linear_independent n k k_bar A iso) <| by
    simp only [Fintype.card_prod, Fintype.card_fin, dim_ℒ_eq, pow_two]

local notation "e^" => eHat n k k_bar A iso

/-- The restricted linear equivalence over the finite intermediate field `ℒ`. -/
def isoRestrict' : ℒ ⊗[k] A ≃ₗ[ℒ] Matrix (Fin n) (Fin n) ℒ :=
  (intermediateTensorEquiv' k k_bar A ℒ).symm ≪≫ₗ
  Basis.equiv (e^) (Matrix.stdBasis ℒ (Fin n) (Fin n)) (Equiv.refl _)

instance : SMulCommClass k ℒ ℒ := inferInstance

/-- Scalar-extension inclusion from the restricted tensor product into the algebraic closure. -/
def inclusion : ℒ ⊗[k] A →ₐ[ℒ] k⁻ ⊗[k] A :=
  Algebra.TensorProduct.map (Algebra.ofId ℒ k⁻) (AlgHom.id k A)

/-- Entrywise matrix inclusion from `ℒ` to the algebraic closure. -/
def inclusion' : Matrix (Fin n) (Fin n) ℒ →ₐ[ℒ] Matrix (Fin n) (Fin n) k⁻ :=
  AlgHom.mapMatrix (Algebra.ofId ℒ _)

omit [NeZero n] [FiniteDimensional k A] in
lemma inclusion'_injective : Function.Injective (inclusion' n k k_bar A iso) := by
  intro x y h
  ext i j
  rw [← Matrix.ext_iff] at h
  specialize h i j
  simp only [inclusion', Algebra.ofId] at h
  exact h

omit [NeZero n] [FiniteDimensional k A] in
/--
ℒ ⊗_k A ------>  intermidateTensor
  |              /
  | inclusion  /
  v          /
k⁻ ⊗_k A  <-
-/
lemma comm_triangle :
    (intermediateTensor' k k_bar A ℒ).subtype ∘ₗ
    (intermediateTensorEquiv' k k_bar A ℒ).symm.toLinearMap =
    (inclusion n k k_bar A iso).toLinearMap := by
  ext a
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.coe_comp, Submodule.coe_subtype, LinearEquiv.coe_coe, Function.comp_apply, inclusion,
    AlgHom.toLinearMap_apply]
  simp only [intermediateTensorEquiv', intermediateTensorEquiv, LinearEquiv.symm_symm,
    LinearEquiv.coe_symm_mk]
  rfl

/--
intermidateTensor ----> M_n(ℒ)
  | val                 | inclusion'
  v                     v
k⁻ ⊗_k A ----------> M_n(k⁻)
          iso
-/
lemma comm_square' :
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ ∘ₗ
    (intermediateTensor' k k_bar A ℒ).subtype =
    (inclusion' n k k_bar A iso).toLinearMap ∘ₗ
    Basis.equiv (e^) (Matrix.stdBasis ℒ (Fin n) (Fin n)) (Equiv.refl _) := by
  apply Basis.ext (e^)
  intro i
  conv_lhs => simp only [AlgEquiv.toLinearEquiv_toLinearMap, eHat,
    basisOfLinearIndependentOfCardEqFinrank,
    Basis.coe_mk, eHat', LinearMap.coe_comp, LinearMap.coe_restrictScalars, Submodule.coe_subtype,
    Function.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Basis.equiv_apply, Equiv.refl_apply, AlgHom.toLinearMap_apply]
  change iso (e i) = (inclusion' n k k_bar A iso) ((Matrix.stdBasis ℒ (Fin n) (Fin n)) i)
  rw [ee_apply n k k_bar A iso i]
  rw [Matrix.stdBasis_eq_single]
  rw [Matrix.stdBasis_eq_single]
  ext a b
  simp only [inclusion']
  simp only [Algebra.ofId]
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.single]
  change (if i.1 = a ∧ i.2 = b then 1 else 0) =
    algebraMap ℒ k_bar ((if i.1 = a ∧ i.2 = b then 1 else 0) : ℒ)
  simp

/-- This shows the following diagram commutes:
     isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso
-/
lemma comm_square :
    (inclusion' n k k_bar A iso).toLinearMap ∘ₗ
    (isoRestrict' n k k_bar A iso).toLinearMap =
    iso.toLinearEquiv.toLinearMap.restrictScalars ℒ ∘ₗ
    (inclusion n k k_bar A iso).toLinearMap := by
  rw [← comm_triangle n k k_bar A iso, ← LinearMap.comp_assoc, comm_square' n k k_bar A iso]
  rfl

lemma isoRestrict_map_one : isoRestrict' n k k⁻ A iso 1 = 1 := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict 1 = 1
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict 1) = iso (inclusion 1) = 1 = inclusion' 1
  since inclusion' is injective, isoRestrict 1 = 1
  -/
  have eq := congr($(comm_square n k k_bar A iso) 1)
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    change (LinearMap.restrictScalars (@Subtype k_bar fun x ↦ x ∈ ℒ)) iso.toLinearEquiv.toLinearMap
      (inclusion n k k_bar A iso 1)
    erw [show (inclusion n k k_bar A iso 1) = 1 from rfl, map_one iso]
  refine inclusion'_injective n k k_bar A iso (eq.trans ?_)
  rw [_root_.map_one]

lemma isoRestrict_map_mul (x y : ℒ ⊗[k] A) :
    isoRestrict' n k k⁻ A iso (x * y) =
    isoRestrict' n k k⁻ A iso x * isoRestrict' n k k⁻ A iso y := by
  /-
        isoRestrict
  ℒ ⊗_k A -----> M_n(ℒ)
    | inclusion    | inclusion'
    v              v
  k⁻ ⊗_k A -----> M_n(k⁻)
            iso

  Want to show isoRestrict (x * y) = isoRestrict x * isoRestrict y
  inclusion' ∘ isoRestrict = iso ∘ inclusion
  inclusion' (isoRestrict (x * y)) = iso (inclusion (x * y)) = iso (inclusion x) * iso (inclusion y)
    = inclusion' (isoRestrict x) * inclusion' (isoRestrict y)
    = inclusion' (isoRestrict x * isoRestrict y)
  since inclusion' is injective, isoRestrict (x * y) = isoRestrict x * isoRestrict y

  -/
  have eq := congr($(comm_square n k k_bar A iso) (x * y))
  conv_rhs at eq =>
    rw [LinearMap.comp_apply]
    erw [_root_.map_mul (f := inclusion n k k_bar A iso), _root_.map_mul (f := iso)]
  have eq₁ := congr($(comm_square n k k_bar A iso) x)
  have eq₂ := congr($(comm_square n k k_bar A iso) y)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearEquiv_toLinearMap, LinearMap.coe_restrictScalars] at eq₁ eq₂
  apply inclusion'_injective n k k_bar A iso
  calc
    (inclusion' n k k_bar A iso) ((isoRestrict' n k k_bar A iso) (x * y)) =
        iso ((inclusion n k k_bar A iso) x) * iso ((inclusion n k k_bar A iso) y) := by
      change
        ((inclusion' n k k_bar A iso).toLinearMap ∘ₗ ↑(isoRestrict' n k k_bar A iso)) (x * y) =
          iso ((inclusion n k k_bar A iso) x) * iso ((inclusion n k k_bar A iso) y)
      exact eq
    _ = (inclusion' n k k_bar A iso) ((isoRestrict' n k k_bar A iso) x) *
        (inclusion' n k k_bar A iso) ((isoRestrict' n k k_bar A iso) y) := by
      rw [eq₁, eq₂]
      rfl
    _ = (inclusion' n k k_bar A iso)
        ((isoRestrict' n k k_bar A iso) x * (isoRestrict' n k k_bar A iso) y) := by
      rw [_root_.map_mul]

/-- The restricted algebra equivalence over the finite intermediate field `ℒ`. -/
def isoRestrict : ℒ ⊗[k] A ≃ₐ[ℒ] Matrix (Fin n) (Fin n) ℒ :=
  AlgEquiv.ofLinearEquiv (isoRestrict' n k k⁻ A iso)
    (isoRestrict_map_one n k k⁻ A iso) (isoRestrict_map_mul n k k⁻ A iso)

end lemmaTto
