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
    [AddCommGroup M] [Module A M] (f : B →ₐ[K] A) (m : moduleInst K A B M f) :
    B →+ (Module.End A M) →+ (moduleInst K A B M f) where
  toFun b := {
    toFun l := f b • l m
    map_zero' := by simp only [LinearMap.zero_apply, smul_zero]; rfl
    map_add' l1 l2 := by rw [LinearMap.add_apply, smul_add]; rfl
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
    (moduleInst K A B M f) → (B ⊗[K] (Module.End A M)) →+ (moduleInst K A B M f) := fun m ↦
  TensorProduct.liftAddHom (smul1AddHom' K A B M f m) fun k b l ↦ by
    simp only [smul1AddHom', AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMapClass.map_smul,
      smul_assoc, LinearMap.smul_apply]
    rw [smul_comm]

/-- The tensor-product linear action on the transported module. -/
def smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    (moduleInst K A B M f) → (B ⊗[K] (Module.End A M)) →ₗ[K] (moduleInst K A B M f) :=
  fun m ↦ {
    __ := smul1AddHom K A B M f m
    map_smul' := fun k b ↦ by
      simp only [smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        RingHom.id_apply]
      induction b using TensorProduct.induction_on
      · simp only [smul_zero, map_zero]
      · rename_i b l
        simp only [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, LinearMapClass.map_smul, smul_assoc]
        congr
        ext k m
        change k • m = algebraMap _ _ k • m
        simp only [algebraMap_smul]
      · rename_i bl1 bl2 hbl1 hbl2
        simp only [smul_add, map_add, hbl1, hbl2]
  }

lemma one_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B] [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    ∀ (m : moduleInst K A B M f), smul1 K A B M f m 1 = m := fun m ↦ by
  simp [smul1, smul1AddHom, smul1AddHom', Algebra.TensorProduct.one_def]

lemma mul_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B] [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    ∀ (x y : (B ⊗[K] (Module.End A M))) (m : moduleInst K A B M f),
    smul1 K A B M f m (x * y) = smul1 K A B M f (smul1 K A B M f m y) x := fun x y m ↦ by
  dsimp [smul1, smul1AddHom, smul1AddHom']
  induction x using TensorProduct.induction_on
  · simp only [zero_mul, map_zero]
  · rename_i b1 l1
    induction y using TensorProduct.induction_on
    · simp only [mul_zero, map_zero, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
      have h0 : l1 0 = 0 := l1.map_zero
      change 0 = f b1 • l1 (0 : M)
      rw [h0, smul_zero]
    · rename_i b2 l2
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, Module.End.mul_apply, LinearMapClass.map_smul]
      simp only [smul_smul]
    · simp_all only [mul_add, map_add, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk]
      symm
      exact (congrArg (fun z => f b1 • z) (l1.map_add _ _)).trans (smul_add (f b1) _ _)
  · simp_all [add_mul]

lemma smul1_add (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (f : B →ₐ[K] A) :  ∀ (r : (B ⊗[K] (Module.End A M))) (m1 m2 : moduleInst K A B M f),
    smul1 K A B M f (m1 + m2) r = smul1 K A B M f m1 r + smul1 K A B M f m2 r := fun r m1 m2 ↦ by
  induction r using TensorProduct.induction_on
  · simp only [map_zero, add_zero]
  · rename_i b l
    simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    have hadd : l (m1 + m2) = l m1 + l m2 := l.map_add m1 m2
    rw [hadd, smul_add]
    rfl
  · rename_i a b ha hb
    simp_all only [smul1, smul1AddHom, smul1AddHom', map_add, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk, ← add_assoc, add_left_inj]
    nth_rw 2 [add_assoc]; nth_rw 4 [add_comm]
    rw [← add_assoc]

lemma add_smul1 (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    [Ring B] [Algebra K B] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
    (f : B →ₐ[K] A) (r s : B ⊗[K] Module.End A M) (x : moduleInst K A B M f) :
    smul1 K A B M f x (r + s) = smul1 K A B M f x r + smul1 K A B M f x s := by
  simp only [smul1, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_add, LinearMap.coe_mk,
    AddHom.coe_mk]

instance IsMod (K A B M : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] (f : B →ₐ[K] A) :
    Module (B ⊗[K] (Module.End A M)) (moduleInst K A B M f) where
  smul := fun r m => smul1 K A B M f m r
  one_smul := one_smul1 K A B M f
  mul_smul := mul_smul1 K A B M f
  smul_zero a := by
    change smul1 K A B M f 0 a = 0
    rw [smul1]
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk]
    induction a using TensorProduct.induction_on
    · simp only [map_zero]
    · rename_i b l
      simp only [smul1AddHom, smul1AddHom', TensorProduct.liftAddHom_tmul,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      have h0 : l 0 = 0 := l.map_zero
      change f b • l (0 : M) = 0
      rw [h0, smul_zero]
    · simp_all [map_add]
  smul_add := smul1_add K A B M f
  add_smul := add_smul1 K A B M f
  zero_smul m := by
    change smul1 K A B M f m 0 = 0
    simp only [smul1, map_zero]

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
    refine Submodule.subset_span ?_
    aesop⟩⟩
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
      simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AlgHom.commutes, algebraMap_smul, Module.End.one_apply]]
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
        intro F (m : moduleInst K A B M f)
        simp only [Module.End.smul_def, RingHom.id_apply]
        have : F m = smul1 K A B M f m (1 ⊗ₜ F) := by
          simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
            AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
            TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul]
        rw [this]
        erw [φ.map_smul]
        change smul1 K A B M _ _ (1 ⊗ₜ F) = _
        simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
          TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul] }
  let Ψ : Module.End (Module.End A M) M :=
    { toFun m := φ.symm m
      map_add' := fun m n => φ.symm.map_add m n
      map_smul' := by
        intro F m
        simp only [Module.End.smul_def, RingHom.id_apply]
        have : F m = smul1 K A B M g m (1 ⊗ₜ F) := by
          simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
            AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
            TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul]
        rw [this]
        have := φ.symm.map_smul (1 ⊗ₜ F) m
        change φ.symm (smul1 K A B M _ _ _) = _ at this
        rw [this]
        change  smul1 K A B M _ _ (1 ⊗ₜ F) = _
        simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe,
          AddMonoidHom.toZeroHom_coe, LinearMap.coe_mk, AddHom.coe_mk,
          TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_one, one_smul] }
  let a := ISO.symm Φ
  let b := ISO.symm Ψ
  refine ⟨⟨a, b, (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, a, b]
    ext m
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      Module.End.one_apply, Φ, Ψ]), (by
    apply_fun ISO using AlgEquiv.injective _
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_one, b, a]
    ext m
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply,
      Module.End.one_apply, Ψ, Φ])⟩, ?_⟩
  intro x
  simp only [Units.inv_mk, a, b]
  apply_fun ISO using AlgEquiv.injective _
  simp only [endEndIso, AlgEquiv.coe_ofBijective, map_mul, AlgEquiv.apply_symm_apply, ISO, Φ, Ψ]
  ext m
  simp only [toEndEndAlgHom, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, toEndEnd_apply, Module.End.mul_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  have := φ.map_smul (x ⊗ₜ LinearMap.id) (φ.symm m)
  change φ (smul1 K A B M _ _ (x ⊗ₜ LinearMap.id)) = _ at this
  simp only [smul1, smul1AddHom, smul1AddHom', ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.liftAddHom_tmul, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, LinearMap.id_coe, id_eq, LinearEquiv.apply_symm_apply] at this
  erw [this]
  change _ = smul1 K A B M _ _ (x ⊗ₜ LinearMap.id)
  simp [smul1, smul1AddHom, smul1AddHom']

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
