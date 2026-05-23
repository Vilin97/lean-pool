/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.Module

/-!  # Linear Algebra auxiliary lemmas   -/

open Module

lemma Basis.equivFun_symm_eq_repr_symm {M ι R : Type*}
    [Fintype ι] [AddCommMonoid M] [Semiring R] [Module R M] (b : Basis ι R M) (f : ι →₀ R) :
    b.equivFun.symm f = b.repr.symm f := by
  apply b.repr.injective
  ext i
  rw [LinearEquiv.apply_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

lemma Basis.equivFun_symm_eq_repr_symm' {M ι R : Type*} [Fintype ι] [AddCommMonoid M]
    [Semiring R] [Module R M] (b : Basis ι R M) (f : ι → R) :
    b.equivFun.symm f = b.repr.symm (Finsupp.equivFunOnFinite.symm f) := by
  have : f = ((Finsupp.equivFunOnFinite.symm f)) := rfl
  rw [this]
  exact Basis.equivFun_symm_eq_repr_symm b _

noncomputable def basisSpanOfBasis.basis_in_span {K L ι R: Type*} [CommRing R] [CommRing L]
    [Field K] [Algebra R K] [IsFractionRing R K] [Module K L][Algebra R L][IsScalarTower R K L]
    (b : Basis ι K L) (O : Subalgebra R L)
    (h : (O : Set L) = Submodule.span R (Set.range b)) (i : ι) :
    b i ∈ O := by
  rw [← SetLike.mem_coe]
  exact h ▸ Submodule.subset_span (Set.mem_range_self _)

noncomputable def basisSpanOfBasis.linearIndependent {K L ι R: Type*} [CommRing R] [CommRing L]
    [Field K] [Algebra R K] [IsFractionRing R K] [Module K L] [Algebra R L] [IsScalarTower R K L]
    (b : Basis ι K L) (O : Subalgebra R L) (h : (O : Set L) = Submodule.span R (Set.range b)) :
    LinearIndependent R (fun i => (⟨b i, basis_in_span b O h i⟩ : O)) := by
  have : Subtype.val ∘ (fun i => (⟨b i, basis_in_span b O h i⟩ : O)) = b := rfl
  apply LinearIndependent.of_comp (SMulMemClass.subtype O)
  rw [SMulMemClass.coeSubtype, this, LinearIndependent.iff_fractionRing R K]
  · exact b.linearIndependent

noncomputable def basisSpanOfBasis.spans {K L ι R: Type*} [CommRing R] [CommRing L]
    [Field K] [Algebra R K] [IsFractionRing R K] [Module K L][Algebra R L][IsScalarTower R K L]
    (b : Basis ι K L) (O : Subalgebra R L) (h : (O : Set L) = Submodule.span R (Set.range b))  :
    ⊤ ≤ Submodule.span R (Set.range (fun i => (⟨b i, basis_in_span b O h i⟩ : O))) := by
  have : Function.Injective (SMulMemClass.subtype O) := by
    rw [SMulMemClass.coeSubtype]
    exact Subtype.coe_injective
  rw [← Submodule.map_le_map_iff_of_injective this, ← Submodule.span_image]
  have aux : Subtype.val '' (Set.range (fun i => (⟨b i, basis_in_span b O h i⟩ : O))) =
    Set.range (fun i => b i) := by
    rw [← Set.range_comp]
    rfl
  erw [aux, Submodule.map_top]
  intros x hx
  rw [← SetLike.mem_coe , LinearMap.range_coe, SMulMemClass.coeSubtype, Subtype.range_coe_subtype,
      Set.mem_setOf_eq, ← Subalgebra.mem_carrier] at hx
  rw [← SetLike.mem_coe]
  exact h ▸ hx

/-- If `B` is a `K`-basis for `L` and `O` is the `R`-span of `B`, then `B` is an `R`-basis for `O`.  -/
noncomputable def basisSpanOfBasis {K L ι R: Type*} [CommRing R] [CommRing L] [Field K] [Algebra R K]
    [IsFractionRing R K] [Module K L] [Algebra R L] [IsScalarTower R K L]
    (b : Basis ι K L) (O : Subalgebra R L) (h : O.carrier = Submodule.span R (Set.range b)) :
    Basis ι R O :=
  Basis.mk (basisSpanOfBasis.linearIndependent b O h) (basisSpanOfBasis.spans b O h)
