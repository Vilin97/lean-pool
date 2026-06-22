/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Field.Basic

/-!
# LeanPool.VirasoroProject.ToMathlib.LinearAlgebra.Basis.FinsumRepr
-/

lemma smul_support_subset_left {R M ι : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (v : ι → M) (cf : ι → R) :
    (fun i ↦ cf i • v i).support ⊆ cf.support := by
  simp only [Function.support_subset_iff, ne_eq, Function.mem_support]
  intro i
  rw [not_imp_not]
  intro hcf
  simp [hcf]

lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  by_cases h : {i | cfs i • vs i ≠ 0}.Finite
  · let s : Finset ι := h.toFinset
    rw [finsum_eq_finsetSum_of_support_subset (s := s) _ (fun i hi ↦ by simpa [s] using hi)]
    apply Submodule.sum_smul_mem
    exact fun i his ↦ Submodule.mem_span_of_mem (Set.mem_range_self i)
  · suffices junk : ∑ᶠ i, cfs i • vs i = 0 by simp [junk]
    simpa [Function.support] using finsum_mem_eq_zero_of_infinite (s := Set.univ)
      (by simpa [Function.support] using h)

-- TODO: Golf.
lemma finsum_mem_mem_span {ι R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  by_cases h : {i | cfs i • vs i ≠ 0 ∧ i ∈ s}.Finite
  · let t : Finset ι := h.toFinset
    rw [finsum_eq_finsetSum_of_support_subset (s := t) _ ?_]
    · classical
      have aux : ∑ i ∈ t, ∑ᶠ (_ : i ∈ s), cfs i • vs i = ∑ i ∈ t.filter s, cfs i • vs i  := by
        rw [Finset.sum_filter]
        congr 1
        funext i
        by_cases his : i ∈ s <;>
        · simpa [his] using fun con ↦ by contradiction
      rw [aux]
      apply Submodule.sum_smul_mem
      intro i hist
      apply Submodule.mem_span_of_mem <| Set.mem_image_of_mem ..
      simp_all only [ne_eq, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, t]
    · intro i hi
      simp only [ne_eq, Set.Finite.coe_toFinset, Set.mem_setOf_eq, t]
      refine ⟨?_, ?_⟩ <;>
      · by_contra con
        simp [con] at hi
  · suffices junk : ∑ᶠ i ∈ s, cfs i • vs i = 0 by simp [junk]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support, Set.inter_comm,
      Set.setOf_and] using h)

namespace Module.Basis

lemma iSupIndep_submodule_span_of_pairwise_disjoint
    {R M ι κ : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (B : Basis ι R M) (Is : κ → Set ι)
    (Is_disj : Pairwise (fun k₁ k₂ ↦ Disjoint (Is k₁) (Is k₂))) :
    iSupIndep fun k ↦ Submodule.span R (B '' (Is k)) := by
  intro k
  simp only [Disjoint, ne_eq, le_bot_iff, Submodule.eq_bot_iff]
  intro U hUk hU v hv
  have hvk := hUk hv
  have hv' := hU hv
  simp only [Submodule.iSup_span, ← Set.image_iUnion] at hv'
  rw [Basis.mem_span_image] at hvk hv'
  suffices B.repr v = 0 by simpa using this
  suffices (B.repr v).support = ∅ by simpa using this
  apply Finset.eq_empty_of_forall_notMem
  exact iSupIndep_iff_pairwiseDisjoint.mpr Is_disj k hvk hv'

lemma finsum_repr_smul_basis {R M ι : Type*} [Semiring R] [Nontrivial R] [IsCancelMulZero R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (B : Basis ι R M) (v : M) :
    ∑ᶠ i, B.repr v i • B i = v := by
  have obs : (Function.support fun i ↦ B.repr v i • B i).Finite := by
    apply (Finsupp.hasFiniteSupport (B.repr v)).subset
    intro i hi
    simp only [Function.support, ne_eq, smul_eq_zero, not_or, Set.mem_setOf_eq] at hi ⊢
    exact hi.1
  rw [finsum_eq_sum _ obs]
  apply B.repr.injective
  rw [map_sum]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  ext i
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ j_ne_i
    simp [j_ne_i]
  · simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, smul_eq_zero, not_or, not_and,
               not_not, Finsupp.single_eq_same]
    intro hi
    rw [← not_imp_not, not_not] at hi
    exact hi (B.ne_zero i)

lemma repr_finsum {R M ι : Type*} [Semiring R] [Nontrivial R] [IsCancelMulZero R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (B : Basis ι R M) (cf : ι →₀ R) :
    B.repr (∑ᶠ i, cf i • B i) = cf := by
  convert show B.repr (B.repr.symm cf) = cf by simp
  have aux_finite : (Function.support fun i ↦ cf i • B i).Finite := by
    apply (Finsupp.hasFiniteSupport cf).subset
    intro i hi
    simp only [Function.support, ne_eq, smul_eq_zero, not_or, Set.mem_setOf_eq] at hi ⊢
    exact hi.1
  rw [finsum_eq_sum _ aux_finite]
  simp only [Basis.repr_symm_apply, Finsupp.linearCombination, Finsupp.coe_lsum,
             LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum]
  congr
  ext i
  simp [Basis.ne_zero B i]

lemma repr_finsum_mem_eq_ite {R M ι : Type*} [Semiring R] [Nontrivial R] [IsCancelMulZero R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (B : Basis ι R M) (cf : ι →₀ R)
    (I : Set ι) [DecidablePred fun i ↦ i ∈ I] (j : ι) :
    B.repr (∑ᶠ i ∈ I, cf i • B i) j = if j ∈ I then cf j else 0 := by
  let cf'' := I.indicator cf
  let cf' : ι →₀ R := {
    support := (cf.support.finite_toSet.inter_of_left I).toFinset
    toFun := I.indicator cf
    mem_support_toFun i := by simp [and_comm]
  }
  have key := B.repr_finsum cf'
  simp only [Finsupp.ext_iff] at key
  have aux (i : ι) : cf' i = if i ∈ I then cf i else 0 := by simp [cf', Set.indicator]
  rw [← aux j, ← key j]
  congr
  ext i
  by_cases hi : i ∈ I <;> simp [hi, aux i]

/-- The basis on the span of a subset of a basis, indexed by that subset. -/
  noncomputable def basisSubmoduleSpan {R M ι : Type*}
    [Semiring R] [Nontrivial R] [IsCancelMulZero R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (B : Basis ι R M) (I : Set ι) :
    Basis I R (Submodule.span R (B '' I)) :=
  let f : Submodule.span R (B '' I) →ₗ[R] (I →₀ R) := {
    toFun v := Finsupp.subtypeDomain (fun x ↦ x ∈ I) (B.repr v)
    map_add' v₁ v₂ := by simp
    map_smul' r v := by
      simp only [SetLike.val_smul, map_smul, RingHom.id_apply]
      exact Finsupp.ext (congrFun rfl) }
  let g : (I →₀ R) →ₗ[R] Submodule.span R (B '' I) := {
    toFun cf := ⟨∑ᶠ i, cf i • B i, by convert finsum_mem_span (fun (i : I) ↦ B i) cf; aesop⟩
    map_add' cf₁ cf₂ := by
      simp only [Finsupp.coe_add, Pi.add_apply, AddMemClass.mk_add_mk, Subtype.mk.injEq]
      rw [← finsum_add_distrib]
      · simp [add_smul]
      · exact cf₁.hasFiniteSupport.subset <| smul_support_subset_left ..
      · exact cf₂.hasFiniteSupport.subset <| smul_support_subset_left ..
    map_smul' r cf := by
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply, SetLike.mk_smul_mk,
                 Subtype.mk.injEq]
      rw [smul_finsum' r (cf.hasFiniteSupport.subset <| smul_support_subset_left ..)] }
  have fog : f ∘ g = id := by
    funext cf
    ext i
    simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
    classical
    have aux := B.repr_finsum_mem_eq_ite cf.extendDomain I i
    simp only [Finsupp.extendDomain_apply, dite_smul, zero_smul, Subtype.coe_prop, ↓reduceIte,
               ↓reduceDIte, Subtype.coe_eta] at aux
    simp [← aux, ← finsum_set_coe_eq_finsum_mem]
  have gof : g ∘ f = id := by
    funext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Finsupp.subtypeDomain_apply,
               id_eq, g, f]
    ext
    dsimp
    nth_rw 2 [← B.finsum_repr_smul_basis v]
    rw [@finsum_set_coe_eq_finsum_mem ι M _ (fun i ↦ (B.repr v) i • B i) I]
    congr 1
    ext j
    by_cases hj : j ∈ I
    · simp [hj]
    · simp only [hj, finsum_false]
      simp [show B.repr v j = 0
            from Finsupp.notMem_support_iff.mp fun h ↦
              hj ((Basis.mem_span_image ..).mp (Submodule.coe_mem v) h)]
  ⟨{
    toFun := f
    map_add' x y := f.map_add x y
    map_smul' m x := LinearMap.CompatibleSMul.map_smul f m x
    invFun := g
    left_inv := congrFun gof
    right_inv := congrFun fog
  }⟩

-- TODO: To Mathlib?
@[simp] lemma basis_submodule_span_apply {R M ι : Type*}
    [Semiring R] [Nontrivial R] [IsCancelMulZero R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    (B : Basis ι R M) (I : Set ι) (i : I) :
    B.basisSubmoduleSpan I i = B i.val := by
  simp only [Basis.basisSubmoduleSpan, LinearMap.coe_mk, AddHom.coe_mk, Basis.coe_ofRepr,
             LinearEquiv.coe_symm_mk]
  rw [finsum_eq_single _ i (fun j hj ↦ by simp [hj.symm])]
  simp

end Module.Basis
