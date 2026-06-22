/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import LeanPool.BrauerGroupNew.ToSecond

/-!
# LeanPool.BrauerGroupNew.IsoSecond

Imported Lean Pool material for `LeanPool.BrauerGroupNew.IsoSecond`.
-/

suppress_compilation

open Module
open scoped TensorProduct

universe u
variable (K F : Type) [Field K] [Field F] [Algebra F K]

namespace mapMulProof

open groupCohomology

variable {α β : Gal(K, F) × Gal(K, F) → Kˣ} [Fact (IsMulCocycle₂ α)] [Fact (IsMulCocycle₂ β)]

local notation "A" => CrossProductAlgebra α
local notation "B" => CrossProductAlgebra β
local notation "C" => CrossProductAlgebra (α * β)

variable {K F}

variable (α β) in
/-- The balancing relations used to form the tensor-product quotient module. -/
def S : Set (A ⊗[F] B) :=
  .range fun ((k, a, b) : K × A × B) ↦ (k • a) ⊗ₜ[F] b - a ⊗ₜ[F] (k • b)

@[simp]
lemma mem_S (x : A ⊗[F] B) :
    x ∈ S α β ↔ ∃ (k : K) (a : A) (b : B), x = (k • a) ⊗ₜ b - a ⊗ₜ (k • b) := by
  simp only [S, Set.mem_range, Prod.exists, eq_comm]

variable (α β) in
/-- The balanced tensor-product module used in the multiplicativity proof. -/
@[reducible] def M := (A ⊗[F] B) ⧸ Submodule.span F (S α β)

/-- Right multiplication by fixed tensor factors descends to the balanced quotient. -/
def AoxFBSmulMAux (a' : A) (b' : B) : M α β →ₗ[F] M α β :=
  Submodule.mapQ (Submodule.span F (S α β)) (Submodule.span F (S α β))
    (TensorProduct.lift
      { toFun a :=
        { toFun b := (a * a') ⊗ₜ (b * b')
          map_add' := by
            intro b1 b2
            simp [add_mul, TensorProduct.tmul_add]
          map_smul' := by
            intro f b; simp }
        map_add' := by
          intro a1 a2
          ext b : 1
          simp [add_mul, TensorProduct.add_tmul]
        map_smul' := by
          intro f a
          ext b : 1
          simp [TensorProduct.smul_tmul] })
    (by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, a, b⟩, rfl⟩
      simp only [Submodule.comap_coe, Set.mem_preimage, map_sub, TensorProduct.lift.tmul,
        LinearMap.coe_mk, AddHom.coe_mk, SetLike.mem_coe]
      refine Submodule.subset_span ⟨⟨k, a * a', b * b'⟩, by simp [smul_mul_assoc]⟩)

/-- The auxiliary right action map as a linear map in the second tensor factor. -/
def AoxFBSmulMAuxAux (a : A) : B →ₗ[F] M α β →ₗ[F] M α β where
  toFun b := AoxFBSmulMAux a b
  map_add' b1 b2 := by
    ext a' b'
    simp [AoxFBSmulMAux, mul_add, TensorProduct.tmul_add]
  map_smul' k b := by
    ext a' b'
    simp [AoxFBSmulMAux, Algebra.mul_smul_comm]

open TensorProduct

/-- The right action of `A ⊗[F] B` on the balanced quotient module. -/
def AoxFBSmulM : A ⊗[F] B →ₗ[F] M α β →ₗ[F] M α β :=
  TensorProduct.lift
  { toFun := AoxFBSmulMAuxAux
    map_add' a1' a2' := by
      ext b' a b
      simp only [AoxFBSmulMAux, mul_add, add_tmul, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, Submodule.Quotient.mk_add, LinearMap.add_apply, AoxFBSmulMAuxAux]
    map_smul' f a' := by
      ext b' a b
      simp only [AoxFBSmulMAux, Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        lift.tmul, RingHom.id_apply, LinearMap.smul_apply, AoxFBSmulMAuxAux]
      rw [← smul_tmul']
      simp only [Submodule.Quotient.mk_smul] }

@[simp]
lemma AoxFBSmulM_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    AoxFBSmulM (a' ⊗ₜ[F] b') (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    (Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) : M α β) := rfl

instance : SMul (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  smul x y := AoxFBSmulM x.unop y

open MulOpposite in
@[simp]
lemma Aox_FB_op_tmul_smul_mk_tmul (a' a : A) (b' b : B) :
    op (a' ⊗ₜ[F] b') • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk ((a * a') ⊗ₜ[F] (b * b')) := rfl

open MulOpposite in
instance : MulAction (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  one_smul := by
    intro x
    rw [show (1 : (A ⊗[F] B)ᵐᵒᵖ) = op 1 from rfl,
      Algebra.TensorProduct.one_def]
    change AoxFBSmulM (1 ⊗ₜ[F] 1) x = LinearMap.id (R := F) x
    refine LinearMap.ext_iff |>.1 ?_ x
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      AoxFBSmulM_op_tmul_smul_mk_tmul, _root_.mul_one, LinearMap.id_comp]
  mul_smul := by
    rintro ⟨x⟩ ⟨y⟩ b
    change AoxFBSmulM (y * x) _ = AoxFBSmulM x (AoxFBSmulM y b)
    rw [← LinearMap.comp_apply]
    refine LinearMap.ext_iff |>.1 ?_ b
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    induction x using TensorProduct.induction_on with
    | tmul xl rl =>
      induction y using TensorProduct.induction_on with
      | tmul yl yr => simp [AoxFBSmulM_op_tmul_smul_mk_tmul, _root_.mul_assoc]
      | add y y' hy hy' => simp_all [add_mul]
      | zero => simp
    | add x x' hx hx' => simp_all [mul_add]
    | zero => simp

instance : DistribMulAction (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  smul_zero x := show AoxFBSmulM _ _ = _ by simp
  smul_add x a b := show AoxFBSmulM _ _ =
    AoxFBSmulM _ _ + AoxFBSmulM _ _ by simp

instance : Module (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  add_smul x y a := show AoxFBSmulM _ _ =
    AoxFBSmulM _ _ + AoxFBSmulM _ _ by simp
  zero_smul x := show AoxFBSmulM _ _ = _ by simp

open CrossProductAlgebra TensorProduct

lemma F_smul_mul_compatible (f : F) (a a' : A) : (f • a) * a' = a * (f • a') := by
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

private lemma finrank_mop_eq (V : Type*) [AddCommGroup V] [Module F V] :
    Module.finrank F Vᵐᵒᵖ = Module.finrank F V :=
  LinearEquiv.finrank_eq
    { toFun := MulOpposite.unop
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      invFun := MulOpposite.op
      left_inv := MulOpposite.unop_op
      right_inv _ := rfl }

variable [FiniteDimensional F K]

/-- The auxiliary left action of the product cross-product algebra on the balanced quotient. -/
def CSmulAux (c : C) : M α β →ₗ[F] M α β :=
  Submodule.mapQ (Submodule.span F (S α β)) (Submodule.span F (S α β))
    (TensorProduct.lift
      { toFun a := {
          toFun b := ∑ σ : Gal(K, F), ((c.1 σ • basis σ) * a) ⊗ₜ (basis σ * b)
          map_add' b b' := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [mul_add, tmul_add]
          map_smul' f b := by
            dsimp only [RingHom.id_apply]
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [smul_tmul', smul_tmul, ← F_smul_mul_compatible]
            simp only [Algebra.smul_mul_assoc, tmul_smul] }
        map_add' a a' := by
          ext b : 1
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp [mul_add, add_tmul]
        map_smul' f a := by
          ext b : 1
          simp only [Algebra.mul_smul_comm, LinearMap.coe_mk, AddHom.coe_mk,
            RingHom.id_apply, LinearMap.smul_apply]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [smul_tmul'] })
  (by
    rw [Submodule.span_le]
    rintro _ ⟨⟨k, a, b⟩, rfl⟩
    simp only [Submodule.comap_coe, Set.mem_preimage, map_sub, lift.tmul,
      LinearMap.coe_mk, AddHom.coe_mk, SetLike.mem_coe]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun σ _ =>
      Submodule.subset_span ⟨⟨σ k, c.1 σ • (basis σ * a), basis σ * b⟩, ?_⟩
    simp only [← smul_mul_assoc, basis_smul_comm]
    congr 2
    apply val_injective
    simp only [val_mul, val_smul, CrossProductAlgebra.basis_val, Finsupp.smul_single, smul_eq_mul,
      _root_.mul_one]
    induction b.val using Finsupp.induction_linear with
    | zero => simp
    | add f g _ _ => simp_all
    | single a b =>
      simp only [mulLinearMap_single_single, Finsupp.smul_single, smul_eq_mul, map_mul]
      congr 1
      field_simp [← _root_.mul_assoc])

lemma CSmulAux_calc (k : K) (σ : Gal(K, F)) (a : A) (b : B) :
    CSmulAux (k • basis σ) (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk (((k • basis σ) * a) ⊗ₜ (basis σ * b)) := by
  delta CSmulAux
  rw [Submodule.mapQ_apply, lift.tmul]
  congr 1
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)]
  swap
  · rintro τ - h
    erw [show (k • CrossProductAlgebra.basis σ).val τ = 0 by
      simp [CrossProductAlgebra.basis, Ne.symm h]]
    simp
  congr 2
  simp [CrossProductAlgebra.basis]

/-- The left action of the product cross-product algebra on the balanced quotient. -/
def CSmul : C →ₗ[F] M α β →ₗ[F] M α β where
  toFun := CSmulAux
  map_add' c c' := by
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.add_apply]
    delta CSmulAux
    rw [Submodule.mapQ_apply, lift.tmul, Submodule.mapQ_apply, lift.tmul,
        Submodule.mapQ_apply, lift.tmul]
    change Submodule.Quotient.mk (∑ _, _) = Submodule.Quotient.mk ((∑ _, _) + (∑ _, _))
    change Submodule.mkQ _ _ = Submodule.mkQ _ _
    rw [map_sum, map_add, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_add, ← add_tmul]
    congr 2
    simp [add_smul, add_mul]
  map_smul' f c := by
    ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, RingHom.id_apply,
      LinearMap.smul_apply]
    delta CSmulAux
    rw [Submodule.mapQ_apply, lift.tmul, Submodule.mapQ_apply, lift.tmul]
    change Submodule.mkQ _ (∑ _, _) = f • Submodule.mkQ _ (∑ _, _)
    rw [← map_smul, Finset.smul_sum]
    simp_rw [smul_tmul']
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp

instance : SMul C (M α β) where
  smul c x := CSmul c x

lemma CSmul_def (c : C) (x : M α β) : c • x = CSmul c x := rfl

lemma CSmul_calc (k : K) (σ : Gal(K, F)) (a : A) (b : B) :
    (k • basis σ : C) • (Submodule.Quotient.mk (a ⊗ₜ[F] b) : M α β) =
    Submodule.Quotient.mk (((k • basis σ) * a) ⊗ₜ (basis σ * b)) :=
  CSmulAux_calc k σ a b

theorem C_mul_smul' (x y : C) (ab : M α β) : (x * y) • ab = x • y • ab := by
  change ((⟨x.val⟩ : C) * ⟨y.val⟩) • ab = (⟨x.val⟩ : C) • (⟨y.val⟩ : C) • ab
  induction x.val using Finsupp.induction_linear with
  | zero => change (0 * _) • _ = 0 • _; change CSmul _ _ = CSmul _ (CSmul _ _); simp
  | add f g h1 h2 =>
    change ((⟨f⟩ + ⟨g⟩ : C) * _) • ab = (⟨f⟩ + ⟨g⟩ : C) • _ • _
    simp only [add_mul]
    change CSmul _ _ = CSmul _ (CSmul _ _) at h1 h2 ⊢
    rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, h1, h2]
  | single σ k1 =>
    induction y.val using Finsupp.induction_linear with
    | zero =>
      change (_ * 0) • _ = _ • 0 • _;
      change CSmul _ _ = CSmul _ (CSmul _ _)
      simp
    | add f g h1 h2 =>
      change CSmul (⟨.single σ k1⟩ * (_ + _) : C) _ = CSmul _ (CSmul (⟨f⟩ + ⟨g⟩ : C) _)
      change CSmul _ _ = CSmul _ (CSmul _ _) at h1 h2
      rw [mul_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, h1, h2, map_add]
    | single τ k2 =>
      induction ab using Submodule.Quotient.induction_on with | H ab =>
      induction ab using TensorProduct.induction_on with
      | zero =>
        change CSmul _ _ = CSmul _ (CSmul _ _)
        simp
      | tmul a b =>
        change CSmul (⟨mulLinearMap _ (.single σ k1) (.single τ k2)⟩ : C) _ = CSmul _ (CSmul _ _)
        simp only [mulLinearMap_single_single, Pi.mul_apply, Units.val_mul]
        rw [← mul_one (k1 * σ k2 * ((α (σ, τ)).1 * (β (σ, τ)).1)), ← smul_eq_mul _ 1,
          ← Finsupp.smul_single, ← CrossProductAlgebra.smul_mk, mk_single_one, ← mul_one k1,
          ← mul_one k2, ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one,
          ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one, ← CSmul_def,
          ← CSmul_def, ← CSmul_def, CSmul_calc, CSmul_calc, CSmul_calc, Submodule.Quotient.eq]
        simp only [smul_eq_mul, _root_.mul_one]
        rw [← _root_.mul_assoc (basis σ) _ b, CrossProductAlgebra.basis_mul_basis σ τ,
          incl_apply, smul_mul_assoc (β (σ, τ)).1, _root_.one_mul, smul_mul_assoc (β (σ, τ)).1,
          ← _root_.mul_assoc (k1 • basis σ), basis_smul_comm, ← mul_smul (σ k2), mul_comm k1,
          smul_mul_assoc (σ k2 * k1), CrossProductAlgebra.basis_mul_basis σ τ]
        simp only [incl_apply, smul_one_mul]
        rw [← mul_smul (σ k2 * k1), mul_comm (α (_, _)).1, ← _root_.mul_assoc,
          mul_comm (σ k2 * k1) (β (_, _)).1, _root_.mul_assoc, mul_smul, smul_mul_assoc]
        exact Submodule.subset_span ⟨⟨(β (σ, τ)).1, (σ k2 * k1 * ↑(α (σ, τ))) • basis (σ * τ) * a,
          basis (σ * τ) * b⟩, rfl⟩
      | add x y h1 h2 =>
        simp only [CSmul_def, Submodule.Quotient.mk_add, map_add] at h1 h2 ⊢
        rw [h1, h2]

instance : MulAction C (M α β) where
  one_smul x := by
    induction x using Quotient.inductionOn' with | h x =>
    change (1 : C) • Submodule.Quotient.mk x = Submodule.Quotient.mk x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      rw [show (1 : C) = ((β (1, 1)).1⁻¹ * (α (1, 1)).1⁻¹) • CrossProductAlgebra.basis 1 by
        apply val_injective; simp [CrossProductAlgebra.basis], CSmul_calc, mul_smul,
        show basis 1 = (⟨.single 1 1⟩ : CrossProductAlgebra α) from rfl,
        show ((α (1, 1)).1)⁻¹ • (⟨.single 1 1⟩ : A) = ⟨(↑(α (1, 1)))⁻¹ • .single 1 1⟩ by
          apply val_injective
          simp only [smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one]
          congr
          change _ = (α (1, 1))⁻¹.1 * 1
          simp,
        Finsupp.smul_single, show (α (1, 1))⁻¹ • 1 = (α (1, 1)).1⁻¹ by
          change (α (1, 1))⁻¹.1 * 1 = _; simp,
        show (⟨.single 1 (α (1, 1)).1⁻¹⟩ : A) = 1 by rfl,
        smul_mul_assoc, _root_.one_mul, Submodule.Quotient.eq]
      refine Submodule.subset_span ⟨⟨(β (1, 1)).1⁻¹, a, basis 1 * b⟩, ?_⟩
      simp [← smul_mul_assoc, show ((β (1, 1)).1)⁻¹ • basis 1 = (1 : B) by
        apply val_injective; simp [CrossProductAlgebra.basis]]
    | add x y hx hy =>
      simp only [Submodule.Quotient.mk_add]
      conv_rhs => rw [← hx, ← hy]
      simp [CSmul_def, map_add]
    | zero =>
      simp [Submodule.Quotient.mk_zero, CSmul_def, map_zero]
  mul_smul := C_mul_smul'

instance : DistribMulAction C (M α β) where
  smul_zero c := show CSmul _ _ = 0 by simp
  smul_add c x y := show CSmul _ _ = CSmul _ _ + CSmul _ _ by simp

instance : Module C (M α β) where
  add_smul c c' x :=
    show CSmul _ _ = CSmul _ _ + CSmul _ _ by
      simp only [map_add, LinearMap.add_apply]
  zero_smul x := show CSmul _ _ = _ by simp

instance : SMulWithZero (A ⊗[F] B)ᵐᵒᵖ (M α β) where
  zero_smul ab := show AoxFBSmulM 0 _ = 0 by simp

open CrossProductAlgebra TensorProduct

open MulOpposite

instance : SMulCommClass (A ⊗[F] B)ᵐᵒᵖ C (M α β) where
  smul_comm := by
    rintro ⟨x⟩ c m
    induction m using Quotient.inductionOn' with | h m =>
    change op x • c • Submodule.Quotient.mk _ = c • op x • Submodule.Quotient.mk _
    induction x using TensorProduct.induction_on with
    | tmul a' b' =>
      induction m using TensorProduct.induction_on with
      | tmul a b =>
        change _ • (⟨c.val⟩ : C) • _ = (⟨c.val⟩ : C) • _ • Submodule.Quotient.mk _
        induction c.val using Finsupp.induction_linear with
        | zero => simp
        | add f g h1 h2 =>
          rw [← mk_add_mk, add_smul, @smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _, add_smul, h1, h2]
        | single σ c =>
          rw [← mul_one c, ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one,
            CSmul_calc, Aox_FB_op_tmul_smul_mk_tmul, Aox_FB_op_tmul_smul_mk_tmul, CSmul_calc,
            _root_.mul_assoc, _root_.mul_assoc]
      | zero => simp
      | add x y hx hy =>
        simp [Submodule.Quotient.mk_add, @smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _,
          @smul_add C (M α β) _ _, hx, hy]
    | add x y hx hy =>
      simp only [op_add, @add_smul (A ⊗[F] B)ᵐᵒᵖ (M α β) _ _, hx, hy, smul_add]
    | zero =>
      simp [op_zero, zero_smul]

/-- The tensor-product action commutes with the cross-product action on `M`. -/
lemma Aox_FB_smul_comm_CSmul (x : (A ⊗[F] B)ᵐᵒᵖ) (c : C) (m : M α β) :
    x • c • m = c • x • m :=
  smul_comm x c m

open CrossProductAlgebra TensorProduct in
instance : IsScalarTower F C (M α β) := .of_algebraMap_smul fun x m ↦ by
  induction m using Submodule.Quotient.induction_on with | H m =>
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y h1 h2 =>
    rw [Submodule.Quotient.mk_add, smul_add, h1, h2, smul_add]
  | tmul a b =>
  rw [Algebra.algebraMap_eq_smul_one, one_def, ← mul_one ((α * β) _).1⁻¹,
  ← smul_eq_mul _ 1, ← Finsupp.smul_single, ← smul_mk, mk_single_one, ← smul_assoc, CSmul_calc]
  simp only [Pi.mul_apply, Units.val_mul, mul_inv_rev, smul_assoc, Algebra.smul_mul_assoc]
  rw [← smul_tmul', Submodule.Quotient.mk_smul]
  congr 1
  change Submodule.Quotient.mk ((_ • basis 1 * ⟨a.val⟩) ⊗ₜ (basis 1 * ⟨b.val⟩)) =
    Submodule.Quotient.mk ((⟨a.val⟩ : A) ⊗ₜ[F] (⟨b.val⟩ : B))
  induction a.val using Finsupp.induction_linear with
  | zero => simp
  | add f g h1 h2 =>
    rw [← mk_add_mk, mul_add, add_tmul, add_tmul, Submodule.Quotient.mk_add, h1, h2,
      Submodule.Quotient.mk_add]
  | single σ k1 =>
  rw [smul_mul_assoc, ← mk_single_one]
  change Submodule.Quotient.mk ((_ • (⟨mulLinearMap _ _ _⟩ : A)) ⊗ₜ _) = _
  simp only [mulLinearMap_single_single, _root_.one_mul, AlgEquiv.one_apply, smul_mk,
    Finsupp.smul_single, smul_eq_mul]
  induction b.val using Finsupp.induction_linear with
  | zero => simp
  | add f g h1 h2 =>
    rw [← mk_add_mk, mul_add, tmul_add, Submodule.Quotient.mk_add, h1, h2, tmul_add,
      Submodule.Quotient.mk_add]
  | single τ k2 =>
  rw [← mk_single_one]
  change Submodule.Quotient.mk (_ ⊗ₜ (⟨mulLinearMap β _ _⟩ : B)) = _
  simp only [mulLinearMap_single_single, _root_.one_mul, AlgEquiv.one_apply, mul_comm k2]
  rw [← smul_eq_mul (β _).1, ← Finsupp.smul_single, ← smul_mk, Submodule.Quotient.eq]
  simp_rw [map_one_fst_of_isMulCocycle₂ Fact.out]
  refine Submodule.subset_span ⟨⟨(β (1, 1)).1⁻¹, ⟨Finsupp.single σ k1⟩,
    (β (1, 1)).1 • ⟨Finsupp.single τ k2⟩⟩, ?_⟩
  simp only [smul_mk, Finsupp.smul_single, smul_eq_mul, isUnit_iff_ne_zero, ne_eq,
    Units.ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_left, sub_left_inj]
  congr 3
  field_simp

open CrossProductAlgebra TensorProduct in
/-- The representation of the opposite tensor product algebra by endomorphisms of `M`. -/
noncomputable def φ0 :
    (A ⊗[F] B)ᵐᵒᵖ →ₐ[F] Module.End C (M α β) where
  toFun x := {
    toFun m := x • m
    map_add' _ _ := by simp [@smul_add (A ⊗[F] B)ᵐᵒᵖ (M α β)]
    map_smul' c y := by
      simp only [RingHom.id_apply]
      rw [smul_comm]
    }
  map_one' := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
  map_mul' x y := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    rw [mul_smul]
  map_zero' := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [zero_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  map_add' x y := by
    refine LinearMap.ext fun _ ↦ ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_smul]
  commutes' f := by
    refine LinearMap.ext fun m ↦ ?_
    simp only [MulOpposite.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply]
    induction m using Submodule.Quotient.induction_on with | H m =>
    induction m using TensorProduct.induction_on with
    | tmul a b =>
      erw [Aox_FB_op_tmul_smul_mk_tmul]
      rw [_root_.mul_one, ← Algebra.commutes, ← Algebra.smul_def, ← smul_tmul',
        Submodule.Quotient.mk_smul]
    | add x y hx hy =>
      simpa using congr($hx + $hy)
    | zero =>
      erw [smul_zero]

open TensorProduct

/-- The map from the balanced quotient to the tensor product over `K`. -/
def MtoAoxKB : M α β →ₗ[F] A ⊗[K] B :=
  Submodule.liftQ _
    (TensorProduct.lift
      { toFun a :=
        { toFun b := a ⊗ₜ b
          map_add' := by simp [tmul_add]
          map_smul' := by simp }
        map_add' := by intros; ext; simp [add_tmul]
        map_smul' := by intros; ext; simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
          LinearMap.smul_apply, smul_tmul'] })
    (by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, a, b⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lift.tmul, LinearMap.coe_mk,
        AddHom.coe_mk, tmul_smul, smul_tmul', sub_self])

/-- The additive map from the tensor product over `K` back to the balanced quotient. -/
def AoxKBToMAux : A ⊗[K] B →+ M α β :=
TensorProduct.liftAddHom
  { toFun a :=
    { toFun b := Submodule.Quotient.mk <| a ⊗ₜ b
      map_zero' := by simp
      map_add' := by simp [tmul_add] }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [add_tmul] } fun k a b => by
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span <| ⟨⟨k, a, b⟩, rfl⟩

/-- The linear map from the tensor product over `K` back to the balanced quotient. -/
def AoxKBToM : A ⊗[K] B →ₗ[F] M α β where
  __ := AoxKBToMAux
  map_smul' := by
    intro f x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      simp only [AoxKBToMAux, smul_tmul', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, RingHom.id_apply]
      rw [← Submodule.Quotient.mk_smul, smul_tmul']
    | add x y hx hy =>
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply, smul_add,
        map_add] at hx hy ⊢
      simp only [hx, hy]
    | zero =>
      simp only [smul_zero, ZeroHom.toFun_eq_coe, map_zero,
        RingHom.id_apply]

/-- The balanced quotient is linearly equivalent to the tensor product over `K`. -/
def AoxKBEquivM : M α β ≃ₗ[F] A ⊗[K] B := .ofLinear MtoAoxKB AoxKBToM
  (by
    ext x
    induction x using TensorProduct.induction_on with
    | tmul a b =>
      simp only [MtoAoxKB, AoxKBToM, AoxKBToMAux, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Submodule.liftQ_apply, lift.tmul, LinearMap.id_coe, id_eq]
    | add x y hx hy =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hx hy
      simp only [LinearMap.coe_comp, Function.comp_apply, map_add, hx, hy, LinearMap.id_coe, id_eq]
    | zero => simp)
  (by
    ext a b
    simp only [AoxKBToM, AoxKBToMAux, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      MtoAoxKB, AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.liftQ_apply, lift.tmul, liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      LinearMap.id_comp])

open Module

lemma M_F_dim [IsGalois F K] : finrank F (M α β) = (finrank F K)^3 := by
  rw [LinearEquiv.finrank_eq AoxKBEquivM,
    show finrank F (A ⊗[K] B) = finrank F K * finrank K (A ⊗[K] B) from
      Eq.symm (finrank_mul_finrank F K (A ⊗[K] B)),
    finrank_tensorProduct, finrank_eq_card_basis CrossProductAlgebra.basis,
    finrank_eq_card_basis CrossProductAlgebra.basis, Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank, pow_three]

instance [IsGalois F K] : FiniteDimensional F C :=
  .of_finrank_eq_succ (n := (finrank F K)^2 - 1) <| by
    rw [CrossProductAlgebra.dim_eq_sq]
    refine Nat.succ_pred_eq_of_pos (pow_two_pos_of_ne_zero ?_) |>.symm
    have : 0 < finrank F K := finrank_pos
    omega

instance [IsGalois F K] : Module.Finite C (M α β) :=
  Module.Finite.right F C (M α β)

open CrossProductAlgebra

variable (α β) in
lemma exists_simple_module_directSum [IsGalois F K] :
  ∃ (S : Type) (_ : AddCommGroup S) (_ : Module C S) (_ : IsSimpleModule C S)
    (ι : Type) (_ : Fintype ι),
    Nonempty (C ≃ₗ[C] ι →₀ S) := by
  obtain ⟨S, _, _, _, ι, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring F C C
  refine ⟨S, inferInstance, inferInstance, inferInstance, ι, ?_, ⟨iso⟩⟩
  haveI infinite : Module.Finite C (ι →₀ S) := Module.Finite.equiv iso
  letI : Module F S := Module.compHom S (algebraMap F C)
  haveI : LinearMap.CompatibleSMul C (ι →₀ S) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    congr 1
    apply val_injective
    simp only [val_smul, smul_eq_mul, val_mul]
    induction x.val using Finsupp.induction_linear with
    | zero => simp
    | add f g _ _ => simp_all [smul_add]
    | single σ c =>
      simp only [Finsupp.smul_single, Algebra.algebraMap_eq_smul_one, val_smul, val_one,
        map_one_fst_of_isMulCocycle₂ Fact.out, Pi.mul_apply, Units.val_mul, mul_inv_rev,
        mulLinearMap_single_single, one_mul, AlgEquiv.one_apply, Algebra.smul_mul_assoc]
      rw [mul_comm _ c, mul_assoc c, ← smul_mul_assoc, ← mul_assoc ((β (1, 1)).1⁻¹ * _),
        mul_assoc (β (1, 1)).1⁻¹, inv_mul_cancel₀ (by simp), _root_.mul_one]
      field_simp
  let iso' : C ≃ₗ[F] (ι →₀ S) := iso.restrictScalars F
  haveI : IsScalarTower F C (ι →₀ S) := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]
  haveI : Module.Finite F (ι →₀ S) := Module.Finite.trans C (ι →₀ S)
  have eq := LinearEquiv.finrank_eq iso'
  -- rw [M_F_dim, pow_three] at eq
  refine (@Cardinal.lt_aleph0_iff_fintype ι).1 ?_ |>.some
  apply_fun ((↑) : ℕ → Cardinal) at eq
  rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp F S ι] at eq
  have ineq : Module.rank F C < Cardinal.aleph0 := by
    rw [rank_lt_aleph0_iff]; infer_instance
  rw [eq] at ineq
  simp only [Cardinal.lift_id] at ineq
  haveI : Nontrivial S := IsSimpleModule.nontrivial C S
  have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ι) (Module.rank F S)
    (by
      suffices 0 < Module.rank F S by exact Ne.symm (ne_of_lt this)
      apply rank_pos)
  rw [mul_comm] at ineq2
  exact lt_of_le_of_lt ineq2 ineq

variable [IsGalois F K]

variable (α β) in
/-- A chosen simple module appearing in the Wedderburn decomposition of `C`. -/
def SimpleMod : Type := exists_simple_module_directSum α β |>.choose

local notation "SM" => SimpleMod α β

instance : AddCommGroup SM := exists_simple_module_directSum _ _ |>.choose_spec.choose

instance : Module C SM := exists_simple_module_directSum _ _ |>.choose_spec.choose_spec.choose

instance : Module F SM := Module.compHom SM (algebraMap F C)

instance : IsSimpleModule C SM := exists_simple_module_directSum _ _
  |>.choose_spec.choose_spec.choose_spec.choose

variable (α β) in
/-- The finite index set for the simple-module decomposition of `C`. -/
def IndexingSet : Type := exists_simple_module_directSum α β
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose

local notation "ι" => IndexingSet α β

instance : Fintype ι := exists_simple_module_directSum α β
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- The decomposition of `C` as a finite direct sum of copies of the simple module. -/
def isoιSM : C ≃ₗ[C] ι →₀ SM := exists_simple_module_directSum α β
  |>.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

instance : Nonempty ι := by by_contra!; exact not_subsingleton C isoιSM.toEquiv.subsingleton

instance : NeZero (Fintype.card ι) := by
  constructor
  simp

/-- The direct-sum decomposition rewritten as functions on the finite index set. -/
def isoιSMPow : C ≃ₗ[C] ι → SM := isoιSM ≪≫ₗ Finsupp.linearEquivFunOnFinite C SM ι

variable (α β) in
/-- The direct-sum decomposition reindexed by `Fin (Fintype.card ι)`. -/
def isoιSMPow' : C ≃ₗ[C] Fin (Fintype.card ι) → SM :=
  isoιSMPow ≪≫ₗ
  { __ := Equiv.arrowCongr (Fintype.equivFinOfCardEq (α := ι) rfl : ι ≃ Fin (Fintype.card ι))
      (Equiv.refl _)
    map_add' := by
      intros v w
      rfl
    map_smul' := by
      intros; rfl }

instance : LinearMap.CompatibleSMul (M α β) (ι →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    congr 1
    simp

instance : IsScalarTower F C SM := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]

instance : Module.Finite C (ι →₀ SM) := .equiv isoιSM
instance : Module.Finite F (ι →₀ SM) := .trans C (ι →₀ SM)

instance : SMulCommClass C F SM where
  smul_comm c f a := by
    change c • algebraMap F C f • a = algebraMap F C f • _
    rw [← mul_smul, ← Algebra.commutes, mul_smul]

/-- Endomorphisms of a finite power are matrix algebras over endomorphisms of the summand. -/
def isoDagger (m : ℕ) :
    Module.End C (Fin m → SM) ≃ₐ[F] Matrix (Fin m) (Fin m) (Module.End C SM) where
  __ := endPowEquivMatrix C SM m
  commutes' f := by
    ext i j x
    simp only [endPowEquivMatrix, endVecAlgEquivMatrixEnd, endVecRingEquivMatrixEnd,
      RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk,
      Equiv.coe_fn_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · simp only [h, algebraMap_end_apply, Pi.smul_apply, Pi.single_eq_same]
    · simp only [algebraMap_end_apply, Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero,
      LinearMap.zero_apply]

/-- The opposite algebra of `C` as endomorphisms of the regular `C`-module. -/
def mopEquivEnd' : Cᵐᵒᵖ ≃ₐ[F] Module.End C C :=
  .ofRingEquiv (f := mopEquivEnd C) fun f ↦ by
  ext x
  simp [mopEquivEnd, Algebra.algebraMap_eq_smul_one]

/-- Transport the regular-module endomorphism algebra across the simple-module decomposition. -/
def CIsoAux : Cᵐᵒᵖ ≃ₐ[F] Module.End C (Fin (Fintype.card ι) → SM) :=
  mopEquivEnd'.trans <| (isoιSMPow' α β).conjAlgEquiv F

/-- The matrix form of the opposite algebra of `C`. -/
def CIsoAux' :
    Cᵐᵒᵖ ≃ₐ[F] Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM) :=
  CIsoAux.trans <| isoDagger _

open MulOpposite

lemma dim_endCSM : (finrank F K)^2 =
  (Fintype.card ι) ^ 2 * finrank F (Module.End C SM) := by
  have eq1 := (CIsoAux' (α := α) (β := β)).toLinearEquiv.finrank_eq
  rw [finrank_mop_eq C, CrossProductAlgebra.dim_eq_sq] at eq1
  rw [eq1, matrixEquivTensor (Fin (Fintype.card ι)) F (Module.End C SM) |>.toLinearEquiv.finrank_eq,
    finrank_tensorProduct, finrank_matrix]
  simp only [Fintype.card_fin, finrank_self, _root_.mul_one, pow_two]
  group

/-- Move the matrix algebra description from the opposite algebra back to `C`. -/
def CIsoAux'' :
    C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM))ᵐᵒᵖ where
  toFun c := op <| CIsoAux' (op c)
  invFun m := (CIsoAux'.symm m.unop).unop
  left_inv c := by simp only [unop_op, AlgEquiv.symm_apply_apply]
  right_inv m := by simp only [op_unop, AlgEquiv.apply_symm_apply]
  map_mul' c c' := by simp [op_mul, map_mul]
  map_add' c c' := by simp [op_add, map_add]
  commutes' f := by simp [Algebra.algebraMap_eq_smul_one]

/-- The final matrix-algebra model for the product cross-product algebra. -/
def CIso : C ≃ₐ[F] (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Module.End C SM)ᵐᵒᵖ) :=
  CIsoAux''.trans (BrauerGroup.matrixEquivMatrixMopAlgebra F (End C SM) (Fintype.card ι)).symm

variable (α β) in
lemma M_directSum : ∃ (ιM : Type) (_ : Fintype ιM), Nonempty (M α β ≃ₗ[C] ιM →₀ SM) := by
  obtain ⟨ιM, ⟨iso⟩⟩ := directSum_simple_module_over_simple_ring' F C (M α β) SM
  refine ⟨ιM, ?_, ⟨iso⟩⟩
  haveI : LinearMap.CompatibleSMul C (ιM →₀ SM) F C := by
    constructor
    intro l f x
    change _ = algebraMap F C f • l x
    rw [← map_smul]
    congr 1
    apply val_injective
    simp [Algebra.algebraMap_eq_smul_one]
  let iso' : M α β ≃ₗ[F] (ιM →₀ SM) := iso.restrictScalars F
  haveI : IsScalarTower F C (ιM →₀ SM) := by
    constructor
    intro f c x
    change _ = algebraMap F C f • _ • x
    rw [Algebra.smul_def, mul_smul]
  haveI : Module.Finite C (ιM →₀ SM) := Module.Finite.equiv iso
  haveI : Module.Finite F (ιM →₀ SM) := Module.Finite.trans C (ιM →₀ SM)
  have eq := LinearEquiv.finrank_eq iso'
  rw [M_F_dim, pow_three] at eq
  refine (@Cardinal.lt_aleph0_iff_fintype ιM).1 ?_ |>.some
  apply_fun ((↑) : ℕ → Cardinal) at eq
  simp only [Nat.cast_mul] at eq
  rw [finrank_eq_rank, finrank_eq_rank, rank_finsupp F SM ιM] at eq
  have ineq : Module.rank F K < Cardinal.aleph0 := by
    rw [Module.rank_lt_aleph0_iff]; infer_instance
  replace ineq : Module.rank F K * (Module.rank F K * Module.rank F K) < Cardinal.aleph0 := by
    apply Cardinal.mul_lt_aleph0
    · assumption
    apply Cardinal.mul_lt_aleph0 <;>
    assumption
  rw [eq] at ineq
  simp only [Cardinal.lift_id] at ineq
  haveI : Nontrivial SM := IsSimpleModule.nontrivial C SM
  have ineq2 := @Cardinal.le_mul_left (Cardinal.mk ιM) (Module.rank F SM)
    (by
      suffices 0 < Module.rank F SM by exact Ne.symm (ne_of_lt this)
      apply rank_pos)
  rw [mul_comm] at ineq2
  exact lt_of_le_of_lt ineq2 ineq

variable (α β) in
/-- The finite index set for the simple-module decomposition of `M`. -/
def IndexingSetM : Type := (M_directSum α β).choose

local notation "ιM" => IndexingSetM α β

instance : Fintype ιM := (M_directSum α β).choose_spec.choose

/-- The decomposition of `M` as a finite direct sum of copies of the simple module. -/
def MIsoDirectSum : M α β ≃ₗ[C] ιM →₀ SM := (M_directSum _ _).choose_spec.choose_spec.some

instance : Module.Finite C SM := by
  rw [Module.finite_def, Submodule.fg_def]
  obtain ⟨a, ha⟩ := IsSimpleModule.instIsPrincipal C (M := SM) ⊤
  exact ⟨{a}, Set.finite_singleton a, ha.symm⟩

instance : Module.Finite F SM := .trans C SM

lemma SM_F_dim : Fintype.card ι * finrank F SM = finrank F K ^ 2 := by
  have eq1 := LinearEquiv.finrank_eq (isoιSMPow' α β |>.restrictScalars F)
  rw [CrossProductAlgebra.dim_eq_sq] at eq1
  have eq2 := rank_fun (η := (Fin (Fintype.card ι))) (M := SM) (R := F)
  rw [Fintype.card_fin, ← finrank_eq_rank F SM,
    show (Fintype.card ι : Cardinal) * (finrank F SM : Cardinal) =
      ((Fintype.card ι * finrank F SM : ℕ) : Cardinal) by simp] at eq2
  have := finrank_eq_of_rank_eq (n := Fintype.card ι * finrank F SM) eq2
  rw [this] at eq1
  exact eq1.symm

instance : Module.Finite C (Fin (Fintype.card ι * finrank F K) → SM) := by
  have := Finsupp.linearEquivFunOnFinite C SM (Fin (Fintype.card ι * finrank F K))
  exact .equiv this

variable (α β) in
lemma MIsoPowAux : Nonempty (M α β ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM) := by
  rw [linearEquiv_iff_finrank_eq_over_simple_ring F C]
  have eq2 := rank_fun (η := (Fin (finrank F K * Fintype.card ι))) (M := SM) (R := F)
  rw [Fintype.card_fin, ← finrank_eq_rank F SM,
    show ((finrank F K * Fintype.card ι : ℕ) : Cardinal) * (finrank F SM : Cardinal) =
      ((finrank F K * Fintype.card ι * finrank F SM : ℕ) : Cardinal) by simp] at eq2
  have := finrank_eq_of_rank_eq eq2
  rw [this, M_F_dim, _root_.mul_assoc, SM_F_dim, pow_three, pow_two]

variable (α β) in
/-- A linear equivalence from `M` to a finite power of the chosen simple module. -/
def MIsoPow : M α β ≃ₗ[C] Fin (finrank F K * Fintype.card ι) → SM := MIsoPowAux _ _ |>.some

variable (α β) in
/-- The same finite-power equivalence over the base field. -/
def MIsoPow' : M α β ≃ₗ[F] Fin (finrank F K * Fintype.card ι) → SM :=
  (MIsoPow α β).restrictScalars F

variable (α β) in
/-- Conjugation by `MIsoPow` identifies endomorphism algebras over `C`. -/
def endCMIso :
    Module.End C (M α β) ≃ₐ[F] Module.End C (Fin (finrank F K * Fintype.card ι) → SM) where
  toFun x := (MIsoPow α β) ∘ₗ x ∘ₗ (MIsoPow α β).symm
  invFun x := (MIsoPow α β).symm ∘ₗ x ∘ₗ (MIsoPow α β)
  left_inv x := by
    simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  right_inv x := by
    simp only [← LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  map_mul' x y := by
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.End.mul_apply,
      LinearEquiv.symm_apply_apply]
  map_add' x y := by
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.add_apply,
      map_add]
  commutes' f := by
    refine DFunLike.ext _ _ fun z ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.algebraMap_end_apply]
    change  (MIsoPow' α β) (f • (MIsoPow' α β).symm z) = _
    rw [map_smul]
    simp [LinearEquiv.apply_symm_apply]

instance : NeZero (finrank F K * Fintype.card ι) := by
  constructor
  simp only [ne_eq, mul_eq_zero, Fintype.card_ne_zero, or_false]
  have : 0 < finrank F K := finrank_pos
  omega

variable (α β) in
/-- The endomorphism algebra of `M` as a matrix algebra over endomorphisms of `SM`. -/
def endCMIso' :
    Module.End C (M α β) ≃ₐ[F]
    Matrix (Fin (finrank F K * Fintype.card ι))
      (Fin (finrank F K * Fintype.card ι)) (Module.End C SM) :=
  endCMIso _ _ |>.trans <| isoDagger _

lemma dim_endCM : finrank F (Module.End C (M α β)) = (finrank F K)^4 := by
  have := (endCMIso' α β).toLinearEquiv.finrank_eq
  rw [this]
  have := matrixEquivTensor (Fin (finrank F K * Fintype.card ι)) F (Module.End C SM)
    |>.toLinearEquiv.finrank_eq
  rw [this, finrank_tensorProduct, finrank_matrix]
  simp only [Fintype.card_fin]
  rw [show finrank F K * Fintype.card ι * (finrank F K * Fintype.card ι) =
    (Fintype.card ι)^2 * (finrank F K)^2 by group]
  rw [finrank_self, _root_.mul_one, ← _root_.mul_assoc, mul_comm _ ((Fintype.card ι)^2),
    ← dim_endCSM, pow_two, pow_succ, pow_three]
  group

open MulOpposite in
/-- The opposite tensor product algebra as endomorphisms of the balanced quotient. -/
def φ1 : (A ⊗[F] B)ᵐᵒᵖ ≃ₐ[F] Module.End C (M α β) :=
  .ofBijective φ0 <| bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <| by
    rw [dim_endCM, finrank_mop_eq (A ⊗[F] B), finrank_tensorProduct, CrossProductAlgebra.dim_eq_sq,
      CrossProductAlgebra.dim_eq_sq, pow_two, pow_succ]
    group

open MulOpposite in
/-- The tensor product algebra as the opposite of the endomorphism algebra of `M`. -/
def φ2 : (A ⊗[F] B) ≃ₐ[F] (Module.End C (M α β))ᵐᵒᵖ where
  toFun a := op <| φ1 (op a)
  invFun g := (φ1.symm g.unop).unop
  left_inv x := by simp
  right_inv x := by simp
  map_mul' := by intros; simp
  map_add' := by intros; simp
  commutes' f := by
    simp only [Algebra.TensorProduct.algebraMap_apply, MulOpposite.algebraMap_apply, op_inj]
    rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul', op_smul, ← (φ0 (α := α) (β := β)).commutes f,
      Algebra.algebraMap_eq_smul_one]
    rfl

/-- The tensor product algebra as an opposite matrix algebra over `End_C(SM)`. -/
def φ3 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM))ᵐᵒᵖ := φ2.trans <| endCMIso' _ _ |>.op

/-- The tensor product algebra as a matrix algebra over the opposite endomorphism algebra. -/
def φ4 :
    (A ⊗[F] B) ≃ₐ[F]
    (Matrix (Fin (finrank F K * Fintype.card ι)) (Fin (finrank F K * Fintype.card ι))
      (Module.End C SM)ᵐᵒᵖ) :=
  φ3.trans ((BrauerGroup.matrixEquivMatrixMopAlgebra F _ _).symm)

lemma isBrauerEquivalent : IsBrauerEquivalent (⟨.of F (A ⊗[F] B)⟩ : CSA F) ⟨.of F C⟩ := by
  let iso1 := CIso (α := α) (β := β) |>.mapMatrix (m := Fin (finrank F K))
  let iso11 := iso1.trans (Matrix.compAlgEquiv _ _ _ _) |>.trans
    (Matrix.reindexAlgEquiv _ _ finProdFinEquiv)
  let iso2 := φ4 (α := α) (β := β)
  let iso3 := iso11.trans iso2.symm
  haveI : NeZero (finrank F K) := ⟨by have : 0 < finrank F K := finrank_pos; omega⟩
  exact ⟨1, finrank F K, one_ne_zero, (NeZero.ne' (finrank F K)).symm,
    ⟨(BrauerGroup.dimOneIso (⟨.of F (A ⊗[F] B)⟩ : CSA F)).trans iso3.symm⟩⟩

end mapMulProof

namespace RelativeBrGroup

variable [FiniteDimensional F K] [IsGalois F K] [DecidableEq Gal(K, F)]

open groupCohomology in
/-- The additive form of the isomorphism between the relative Brauer group and second cohomology. -/
def isoSnd : Additive (RelativeBrGroup K F) ≃+ H2 (galAct F K) :=
  .symm <| .mk' (Additive.ofMul.symm.trans <| equivSnd (F := F) (K := K)).symm fun x y ↦ by
    induction x using H2_induction_on with | h x =>
    induction y using H2_induction_on with | h y =>
    rcases x with ⟨x, hx'⟩
    have hx := isMulCocycle₂_of_mem_cocycles₂ _ hx'
    rcases y with ⟨y, hy'⟩
    have hy := isMulCocycle₂_of_mem_cocycles₂ _ hy'
    simp only [Additive.ofMul_symm_eq, equivSnd, H2π, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, Equiv.symm_trans_apply, Additive.toMul_symm_eq, Equiv.coe_fn_symm_mk]
    apply_fun Additive.toMul
    simp only [toMul_ofMul, toMul_add]
    let L := ModuleCat.Hom.hom (H2Iso (galAct F K)).hom
    let px :=
      (ModuleCat.Hom.hom (π (galAct F K) 2))
        ((ModuleCat.Hom.hom (isoCocycles₂ (galAct F K)).inv) ⟨x, hx'⟩)
    let py :=
      (ModuleCat.Hom.hom (π (galAct F K) 2))
        ((ModuleCat.Hom.hom (isoCocycles₂ (galAct F K)).inv) ⟨y, hy'⟩)
    change fromSnd F K (L (px + py)) = fromSnd F K (L px) * fromSnd F K (L py)
    rw [map_add]
    dsimp only [L, px, py]
    simp only [π_comp_H2Iso_hom_apply,
      CategoryTheory.Iso.inv_hom_id_apply]
    change fromSnd F K (Quotient.mk'' _) =
      fromSnd F K (Quotient.mk'' _) * fromSnd F K (Quotient.mk'' _)
    erw [fromSnd_wd, fromSnd_wd]
    erw [fromSnd_wd]
    simp only [MulMemClass.mk_mul_mk]
    refine Subtype.ext ?_
    change _ = Quotient.mk'' _
    rw [Quotient.eq'']
    change IsBrauerEquivalent _ _
    exact @mapMulProof.isBrauerEquivalent _ _ _ _ _ _ _ ⟨hx⟩ ⟨hy⟩ _ _ |>.symm


end RelativeBrGroup
