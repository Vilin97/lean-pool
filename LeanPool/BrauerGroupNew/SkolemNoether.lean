/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.BrauerGroup
import LeanPool.BrauerGroupNew.ZeroSevenFourE

/-!
# LeanPool.BrauerGroupNew.SkolemNoether

Imported Lean Pool material for `LeanPool.BrauerGroupNew.SkolemNoether`.
-/

suppress_compilation

universe u v w

open MulOpposite
open scoped TensorProduct

variable (K : Type u) [Field K]

/-- Type synonym for viewing an `A`-module through an embedding of `B` into `A`. -/
def moduleInst (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : B →ₐ[K] A) :=
  (fun _ : B →ₐ[K] A => M) f

instance (K A B M : Type u) [Field K] [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] (f : B →ₐ[K] A) [AddCommGroup M] :
    AddCommGroup (moduleInst K A B M f) :=
  inferInstanceAs <| AddCommGroup M

instance instKMod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module A M] (f : B →ₐ[K] A) :
    Module K (moduleInst K A B M f) :=
  Module.compHom M (algebraMap K A)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module A M] (f : B →ₐ[K] A) :
    Module A (moduleInst K A B M f) :=
  inferInstanceAs (Module A M)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module A M] (f : B →ₐ[K] A) :
    IsScalarTower K A (moduleInst K A B M f) :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

/-- The additive action map before tensor-product descent. -/
def smul1AddHom' (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module A M] (f : B →ₐ[K] A) (m : M) :
    B →+ (Module.End A M) →+ M where
  toFun b := {
    toFun l := f b • l m
    map_zero' := by rw [LinearMap.zero_apply, smul_zero]
    map_add' l1 l2 := by rw [LinearMap.add_apply, smul_add]
  }
  map_zero' := by
    ext l
    change f 0 • l m = 0
    simp
  map_add' b1 b2 := by
    ext l
    simp only [map_add, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
    exact Module.add_smul (f b1) (f b2) (l m)

/-- The tensor-product additive action on the transported module. -/
def smul1AddHom (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    M → (B ⊗[K] (Module.End A M)) →+ M := fun m ↦
  TensorProduct.liftAddHom (smul1AddHom' K A B M f m) fun k b l ↦ by
    show f (k • b) • l m = f b • (k • l) m
    rw [map_smul, LinearMap.smul_apply, smul_assoc, smul_comm]

/-- The tensor-product linear action on the transported module. -/
def smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    M → (B ⊗[K] (Module.End A M)) →ₗ[K] (moduleInst K A B M f) :=
  fun m ↦ {
    __ := smul1AddHom K A B M f m
    map_smul' := fun k b ↦ by
      simp only [smul1AddHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      induction b using TensorProduct.induction_on
      · rw [smul_zero, map_zero]
        have h : algebraMap K A k • (0 : M) = 0 := smul_zero _
        exact h.symm
      · rename_i b l
        rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul,
          TensorProduct.liftAddHom_tmul]
        show f (k • b) • l m = algebraMap K A k • (f b • l m)
        rw [map_smul, Algebra.smul_def, mul_smul]
      · rename_i x y hx hy
        rw [smul_add, map_add, map_add, hx, hy]
        exact (smul_add _ _ _).symm
  }

/-- Evaluating the tensor-product action on a pure tensor. -/
lemma smul1_tmul (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A)
    (m : M) (b : B) (l : Module.End A M) :
    smul1 K A B M f m (b ⊗ₜ[K] l) = f b • l m := rfl

/-- Evaluating the tensor-product action on `1 ⊗ₜ F`. -/
lemma smul1_one_tmul (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A)
    (m : M) (F : Module.End A M) : smul1 K A B M f m (1 ⊗ₜ[K] F) = F m := by
  rw [smul1_tmul, map_one, one_smul]

lemma one_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B] [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    ∀ (m : moduleInst K A B M f), smul1 K A B M f m 1 = m := fun (m : M) ↦ by
  rw [Algebra.TensorProduct.one_def, smul1_tmul, map_one, Module.End.one_apply, one_smul]

/-- The tensor-product action of anything on `0` vanishes. -/
lemma smul1_zero_left (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A)
    (r : B ⊗[K] Module.End A M) : smul1 K A B M f (0 : M) r = 0 := by
  induction r using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul b l =>
    rw [smul1_tmul, map_zero, smul_zero]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

lemma smul1_add (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (f : B →ₐ[K] A) :  ∀ (r : (B ⊗[K] (Module.End A M))) (m1 m2 : moduleInst K A B M f),
    smul1 K A B M f (m1 + m2) r = smul1 K A B M f m1 r + smul1 K A B M f m2 r :=
    fun r (m1 m2 : M) ↦ by
  show smul1 K A B M f ((m1 : M) + m2) r = smul1 K A B M f m1 r + smul1 K A B M f m2 r
  induction r using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul b l =>
    rw [smul1_tmul, smul1_tmul, smul1_tmul, map_add, smul_add]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    abel

lemma mul_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B] [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    ∀ (x y : (B ⊗[K] (Module.End A M))) (m : moduleInst K A B M f),
    smul1 K A B M f m (x * y) = smul1 K A B M f (smul1 K A B M f m y) x := fun x y (m : M) ↦ by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, map_zero]
  | tmul b1 l1 =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [mul_zero, map_zero]
      exact (smul1_zero_left K A B M f _).symm
    | tmul b2 l2 =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, smul1_tmul, smul1_tmul, smul1_tmul,
        map_mul, Module.End.mul_apply, map_smul, mul_smul]
    | add y1 y2 hy1 hy2 =>
      rw [mul_add, map_add, hy1, hy2, map_add]
      exact (smul1_add K A B M f (b1 ⊗ₜ[K] l1) _ _).symm
  | add x1 x2 hx1 hx2 => rw [add_mul, map_add, map_add, hx1, hx2]

lemma add_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (f : B →ₐ[K] A) (r s : B ⊗[K] Module.End A M) (x : moduleInst K A B M f) :
    smul1 K A B M f x (r + s) = smul1 K A B M f x r + smul1 K A B M f x s :=
  map_add _ _ _

instance IsMod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    Module (B ⊗[K] (Module.End A M)) (moduleInst K A B M f) where
  smul := fun r m => smul1 K A B M f m r
  one_smul := one_smul1 K A B M f
  mul_smul := mul_smul1 K A B M f
  smul_zero a := smul1_zero_left K A B M f a
  smul_add := smul1_add K A B M f
  add_smul := add_smul1 K A B M f
  zero_smul m := map_zero (smul1 K A B M f m)

instance (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f : B →ₐ[K] A) :
    IsScalarTower K (B ⊗[K] Module.End A M) (moduleInst K A B M f) where
  smul_assoc a x y := by
    induction x with
    | zero =>
      -- simp
      change smul1 K A B M f _ _ = _ • smul1 K A B M f _ _
      rw [map_zero, smul_zero, smul_zero, map_zero]
    | tmul b z =>
      change (smul1 K A B M f _ _) = _ • smul1 K A B M f _ _
      simp
    | add x y hx hy =>
      rw [smul_add, add_smul, hx, hy, add_smul, smul_add]

instance moduleInst_findim (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    [IsSimpleModule A M] (f : B →ₐ[K] A) :
    Module.Finite (B ⊗[K] Module.End A M) (moduleInst K A B M f) := by
  have : Module.Finite A M := ⟨⟨{gen A M}, eq_top_iff.2 fun x _ => by
    obtain ⟨a, rfl⟩ := gen_spec A M x
    apply Submodule.smul_mem
    simp_all⟩⟩
  obtain ⟨s, hs⟩ : Module.Finite K M := Module.Finite.trans A M
  refine ⟨⟨s, eq_top_iff.2 ?_⟩⟩
  rintro x -
  have mem : (x : M) ∈ (Submodule.span K s : Submodule K M) := hs ▸ ⟨⟩
  obtain ⟨c, hc1, rfl⟩ := Submodule.mem_span_set (R := K) (M := M) |>.1 mem
  refine Submodule.sum_mem _ fun k hk => ?_
  simp only
  rw [show (c k • k : moduleInst K A B M f) =
    ((algebraMap K (B ⊗[K] Module.End A M) (c k)) • (show moduleInst K A B M f from k)) by
      simp only [Algebra.TensorProduct.algebraMap_apply]
      change _ = smul1 K A B M f k _
      rw [smul1_tmul, AlgHom.commutes, Module.End.one_apply, algebraMap_smul]]
  refine Submodule.smul_mem _ _ ?_
  simp only
  refine Submodule.subset_span ?_
  exact hc1 hk

instance tensor_is_simple (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [IsSimpleRing B] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M]
    [Algebra.IsCentral K A] [csa_A : IsSimpleRing A] :
    IsSimpleRing (B ⊗[K] Module.End A M) := by
  obtain ⟨n, hn, D, hD1, hD2, ⟨iso⟩⟩ := WedderburnArtin_algebra_version K A
  have : NeZero n := ⟨hn⟩
  obtain ⟨e1⟩ := endSimpleModOfWedderburn' K A n hn D iso M
  haveI := CSA_implies_CSA K A n D _ iso
  haveI : Algebra.IsCentral K (Module.End A M) := e1.symm.isCentral
  classical
  exact @IsCentralSimple.TensorProduct.simple K _ B (Module.End A M) _ _ _ _ _ this _

variable (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B]
    [Algebra K B] [hB : IsSimpleRing B] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A)

-- set_option linter.unusedVariables false in
lemma findimB (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B]
    [Algebra K B] [hB : IsSimpleRing B] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f : B →ₐ[K] A) :
    FiniteDimensional K B := FiniteDimensional.of_injective (K := K) (V₂ := A) f (by
    change Function.Injective f
    have H := IsSimpleRing.injective_ringHom_or_subsingleton_codomain f.toRingHom
    refine H.resolve_right fun rid ↦ ?_
    have : Nontrivial A := inferInstance
    rw [← not_subsingleton_iff_nontrivial] at this
    contradiction)

omit hB in
lemma iso_fg [hB1 : IsSimpleRing B] :
    Nonempty <| moduleInst K A B M f ≃ₗ[B ⊗[K] (Module.End A M)] moduleInst K A B M g := by
  haveI := findimB K A B M f
  rw [linearEquiv_iff_finrank_eq_over_simple_ring K]
  rfl

/--
End_End_A
-/
theorem SkolemNoether (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B]
    [Algebra K B] [hB : IsSimpleRing B] [AddCommGroup M] [Module K M] [Module A M]
    [IsScalarTower K A M] [IsSimpleModule A M] (f g : B →ₐ[K] A) :
    ∃(x : Aˣ), ∀(b : B), g b = x * f b * x⁻¹ := by
  obtain ⟨φ⟩ := iso_fg K A B M f g
  let ISO := endEndIso K A M
  let Φ : Module.End (Module.End A M) M :=
    { toFun m := φ m
      map_add' := fun m n => φ.map_add m n
      map_smul' := by
        intro F (m : M)
        simp only [Module.End.smul_def, RingHom.id_apply]
        have : F m = smul1 K A B M f m (1 ⊗ₜ F) := (smul1_one_tmul K A B M f m F).symm
        rw [this]
        erw [φ.map_smul]
        change smul1 K A B M g _ (1 ⊗ₜ F) = _
        exact smul1_one_tmul K A B M g _ F }
  let Ψ : Module.End (Module.End A M) M :=
    { toFun m := φ.symm m
      map_add' := fun m n => φ.symm.map_add m n
      map_smul' := by
        intro F (m : M)
        simp only [Module.End.smul_def, RingHom.id_apply]
        have h : F m = smul1 K A B M g m (1 ⊗ₜ F) := (smul1_one_tmul K A B M g m F).symm
        rw [h]
        have h2 := φ.symm.map_smul (1 ⊗ₜ F) m
        change φ.symm (smul1 K A B M g _ _) = _ at h2
        rw [h2]
        change smul1 K A B M f _ (1 ⊗ₜ F) = _
        exact smul1_one_tmul K A B M f _ F }
  let a := ISO.symm Φ
  let b := ISO.symm Ψ
  refine ⟨⟨a, b, (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, a, b]
    ext m
    exact φ.apply_symm_apply m), (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, b, a]
    ext m
    exact φ.symm_apply_apply m)⟩, ?_⟩
  intro x
  simp only [Units.inv_mk, a, b]
  apply_fun ISO using AlgEquiv.injective _
  simp only [endEndIso, AlgEquiv.coe_ofBijective, map_mul, AlgEquiv.apply_symm_apply, ISO, Φ, Ψ]
  ext m
  simp only [toEndEndAlgHom, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toEndEnd_apply, Module.End.mul_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  have e1 : smul1 K A B M f (φ.symm m) (x ⊗ₜ[K] LinearMap.id) = f x • φ.symm m :=
    smul1_tmul K A B M f _ x LinearMap.id
  have e2 : smul1 K A B M g (φ (φ.symm m)) (x ⊗ₜ[K] LinearMap.id) = g x • φ (φ.symm m) :=
    smul1_tmul K A B M g _ x LinearMap.id
  have e3 := φ.map_smul (x ⊗ₜ[K] LinearMap.id) (φ.symm m)
  change φ (smul1 K A B M f (φ.symm m) (x ⊗ₜ[K] LinearMap.id)) =
    smul1 K A B M g (φ (φ.symm m)) (x ⊗ₜ[K] LinearMap.id) at e3
  have h : φ (f x • φ.symm m) = g x • φ (φ.symm m) :=
    (congrArg (⇑φ) e1).symm.trans (e3.trans e2)
  exact (h.trans (congrArg (fun z : M => g x • z) (φ.apply_symm_apply m))).symm

theorem SkolemNoether' (K A B : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [Ring B]
    [Algebra K B] [hB : IsSimpleRing B] (f g : B →ₐ[K] A) :
    ∃ (x : Aˣ), ∀(b : B), g b = x * f b * x⁻¹ := by
  obtain ⟨n, hn, S, _, _, ⟨e⟩⟩ := WedderburnArtin_algebra_version K A
  letI := Module.compHom (Fin n → S) e.toRingEquiv.toRingHom
  have : IsSimpleModule A (Fin n → S) := simple_mod_of_wedderburn K A hn S e
  haveI : IsScalarTower K A (Fin n → S) := by
    constructor
    intro a b c
    ext i
    simp only [Pi.smul_apply]
    change ∑ x, e (a • b) i x * c x = a • ∑ x, e b i x * c x
    rw [map_smul]
    simp only [Matrix.smul_apply, Algebra.smul_mul_assoc, Finset.smul_sum]
  exact SkolemNoether K A B (Fin n → S) f g
