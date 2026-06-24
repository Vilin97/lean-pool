/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Geometry.Manifold.Notation
public import LeanPool.LeanModularForms.Modularforms.ForMathlibCusps
public import LeanPool.LeanModularForms.Modularforms.QExpansionLems

/-! # IsCuspForm -/


@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Manifold


noncomputable section Definitions



variable {α ι : Type*}

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

/-- Views a cusp form as a modular form. -/
def ModFormMk (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := f.slash_action_eq'
  holo' := f.holo'
  bdd_at_cusps' := fun hc ↦ bdd_at_cusps f hc

lemma ModForm_mk_inj (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : CuspForm Γ k) (hf : f ≠ 0) :
  ModFormMk _ _ f ≠ 0 := by
  rw [@DFunLike.ne_iff] at *
  obtain ⟨x, hx⟩ := hf
  use x
  simp only [CuspForm.zero_apply, ne_eq, ModFormMk, zero_apply] at *
  exact hx

/-- The linear inclusion of cusp forms into modular forms. -/
def CuspFormToModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspForm Γ k →ₗ[ℂ] ModularForm Γ k
  where
  toFun f := ModFormMk Γ k f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The submodule of modular forms that are cusp forms. -/
def CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Submodule ℂ (ModularForm Γ k) :=
  LinearMap.range (CuspFormToModularForm Γ k)

/-- The linear isomorphism between cusp forms and the cusp-form submodule. -/
def CuspFormIsoCuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :
    CuspForm Γ k ≃ₗ[ℂ] CuspFormSubmodule Γ k := by
  apply LinearEquiv.ofInjective
  rw [@injective_iff_map_eq_zero]
  intro f hf
  rw [CuspFormToModularForm] at hf
  simp only [ModFormMk, LinearMap.coe_mk, AddHom.coe_mk] at hf
  ext z
  simpa using congr_fun (congr_arg (fun x => x.toFun) hf) z

lemma mem_CuspFormSubmodule (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : f ∈ CuspFormSubmodule Γ k) :
    ∃ g : CuspForm Γ k, f = CuspFormToModularForm Γ k g := by
  rw [CuspFormSubmodule, LinearMap.mem_range] at hf
  aesop

instance (priority := 100) CuspFormSubmodule.funLike : FunLike (CuspFormSubmodule Γ k) ℍ ℂ where
  coe f := f.1.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : CuspFormClass (CuspFormSubmodule Γ k) Γ k where
  slash_action_eq f := f.1.slash_action_eq'
  holo f := f.1.holo'
  zero_at_cusps := by
    rintro ⟨_, ⟨g, rfl⟩⟩ c hc
    exact g.zero_at_cusps' hc

/-- The predicate that a modular form lies in the cusp-form submodule. -/
def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  f ∈ CuspFormSubmodule Γ k

/-- Promotes a modular form satisfying `IsCuspForm` to a cusp form. -/
def IsCuspFormToCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : CuspForm Γ k := by
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  exact hf.choose

lemma CuspForm_to_ModularForm_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspFormToCuspForm Γ k f hf).toSlashInvariantForm =
    f.toSlashInvariantForm := by
  rw [IsCuspFormToCuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp only [CuspFormToModularForm, ModFormMk, LinearMap.coe_mk, AddHom.coe_mk] at hg
  exact congr_arg (fun x ↦ x.toSlashInvariantForm) hg

lemma CuspForm_to_ModularForm_Fun_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : (IsCuspFormToCuspForm Γ k f hf).toFun =
    f.toFun := by
  rw [IsCuspFormToCuspForm]
  rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at hf
  have hg := hf.choose_spec
  simp only [CuspFormToModularForm, ModFormMk, LinearMap.coe_mk, AddHom.coe_mk] at hg
  exact congr_arg (fun x ↦ x.toFun) hg

/-- Build a `CuspForm` from a `SlashInvariantForm` that is holomorphic and tends to 0. -/
noncomputable def cuspFormOfSIFTendstoZero {k : ℤ}
    (f_SIF : SlashInvariantForm Γ(1) k)
    (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun)
    (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) : CuspForm Γ(1) k where
  toSlashInvariantForm := f_SIF
  holo' := h_mdiff
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f_SIF.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact h_zero

private lemma isZeroAtImInfty_of_coeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) :
    IsZeroAtImInfty f := by
  rw [qExpansion_coeff] at h
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul] at h
  have := modform_tendto_ndhs_zero f 1
  simp only [Nat.cast_one, h] at this
  have := (this.comp (Function.Periodic.qParam_tendsto (h := 1) Real.zero_lt_one)).comp
    tendsto_coe_atImInfty
  rw [IsZeroAtImInfty, ZeroAtFilter]
  apply this.congr'
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨⊤, univ_mem, fun y _ => ?_⟩
  simp only [comp_apply]
  obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := 1)
    (Ne.symm (zero_ne_one' ℝ)) y
  have := (periodic_comp_ofComplex (h := 1) f (by simp)).int_mul m y
  simp only [comp_apply, ofReal_one, mul_one, ofComplex_apply] at *
  rwa [hm]

/-- Build a `CuspForm` from a modular form whose q-expansion has vanishing constant term. -/
noncomputable def cuspFormOfCoeffZero {k : ℤ}
    (f : ModularForm Γ(1) k)
    (h : (qExpansion 1 f).coeff 0 = 0) : CuspForm Γ(1) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' hc := by
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    rw [f.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩]
    exact isZeroAtImInfty_of_coeffZero f h

lemma IsCuspForm_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0 := by
  constructor
  · intro h
    rw [qExpansion_coeff]
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range] at h
    obtain ⟨g, hg⟩ := h
    have := CuspFormClass.cuspFunction_apply_zero (h := 1) g (by positivity) (by simp)
    simp only [CuspFormToModularForm, ModFormMk, LinearMap.coe_mk, AddHom.coe_mk] at hg
    rw [← hg]
    exact this
  · intro h
    rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range]
    exact ⟨cuspFormOfCoeffZero f h, by ext; rfl⟩

lemma CuspFormSubmodule_mem_iff_coeffZero_eq_zero (k : ℤ) (f : ModularForm Γ(1) k) :
    f ∈ CuspFormSubmodule Γ(1) k ↔ (qExpansion 1 f).coeff 0 = 0 :=
  IsCuspForm_iff_coeffZero_eq_zero k f

