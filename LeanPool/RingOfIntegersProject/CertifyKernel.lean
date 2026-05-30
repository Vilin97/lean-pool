/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
/-!
# Certify kernel

Lemmas to certify the kernel of a linear map.

## Main definition
- `basisKernelOfLinearIndependentKerIm`: constructs a basis for a linear map giving
  linearly independent vectors `v` that map to zero and vectors `v'` such that `f(v')`
  is linearly independent.
- `basisExtensionKernelOfLinearIndependentKerIm` : extends the above basis to a basis
  of the whole space.

## Main results
- `linearIndependent_of_repr_diag` : a collection of vectors is linearly independent (over a field)
  if, when represented as a matrix, is in echelon form.
- `ker_eq_bot_of_linearMap_to_linearMaps` : a condition certifying that the kernel of a map
  `A →ₗ[R] B →ₗ[R] C` is trivial· -/



variable {A R : Type*} {n : ℕ} [AddCommGroup A]

open Module BigOperators

/-- If `v` is a family of vectors such that when represented with respect to a basis they
  are in echelon form, then they are linearly independent· -/
lemma linearIndependent_of_repr_diag {τ ι : Type*} [CommRing R] [Module R A] (b : Basis ι R A)
    (v : τ → A) [IsDomain R]
    (h : ∀ (i : τ), (∃ (j : ι), b.repr (v i) j ≠ 0 ∧ (∀ (k : τ), k ≠ i → b.repr (v k) j = 0))) :
    LinearIndependent R v := by
  rw [linearIndependent_iff']
  intros s g hg i
  obtain ⟨j, hj⟩ := h i
  replace hg := DFunLike.congr_fun (congr_arg b.repr hg) j
  simp only [map_sum, map_smul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hg
  intro h
  rw [Finset.sum_apply', Finset.sum_eq_single i, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_eq_zero] at hg
  · simp only [hj, or_false] at hg
    exact hg
  · intros k _ hk
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero]
    right
    exact hj.2 k hk
  · simp only [h, not_true, Finsupp.coe_smul, IsEmpty.forall_iff]


/-- Let `v` and `v'` are families of vectors, where `v` is linearly independent
  and the sum of the cardinalities of `v` and `v'`equals the rank of the module·
  If `f` is an `R`-linear map such that `f ∘ v'` is linearly independent and
  `v` is contained in the kernel of `f`, then the elements of `v` form a basis for the kernel of
    `f`· -/
noncomputable def basisKernelOfLinearIndependentKerIm {B : Type*} [DivisionRing R] [Module R A]
    [AddCommGroup B] [Module R B] {τ₁ τ₂ τ₃ : Type*} [Fintype τ₁] [Fintype τ₂] [Fintype τ₃]
    (hc1 : Fintype.card τ₁ + Fintype.card τ₂ = Fintype.card τ₃) (b : Basis τ₃ R A)
    (f : A →ₗ[R] B) (v : τ₁ → A) (v' : τ₂ → A)
    (hlin1 : LinearIndependent R v) (hlin2 : LinearIndependent R (f ∘ v'))
    (hker : ∀ i, f (v i) = 0) :
      Basis τ₁ R (LinearMap.ker f) := by
  have hink : ∀ i, v i ∈ LinearMap.ker f := by
    simp_rw [LinearMap.mem_ker]
    exact hker
  set w := fun i => (⟨v i, hink i⟩ : LinearMap.ker f) with hw
  have hinr : ∀ i, (f ∘ v') i ∈  LinearMap.range f := by
    simp only [Function.comp_apply, LinearMap.mem_range, exists_apply_eq_apply, implies_true]
  set s := fun i => (⟨ (f ∘ v') i, hinr i ⟩ : LinearMap.range f) with hs
  have hlin3 : LinearIndependent R s := by
    have hwd : (LinearMap.range f).subtype ∘ s = f ∘ v' := by
      rw [Submodule.coe_subtype]
      ext i
      simp only [Function.comp_apply]
      rw [hs]
      rfl
    have hlin2' : LinearIndependent R ((LinearMap.range f).subtype ∘ s) := by
      simpa [hwd] using hlin2
    exact ((LinearMap.linearIndependent_iff ((LinearMap.range f).subtype)
      (Submodule.ker_subtype _)).1 hlin2')
  have hwd : (LinearMap.ker f).subtype ∘ w = v := by
    rw [Submodule.coe_subtype]
    ext i
    simp only [Function.comp_apply]
    rw [hw]
  refine Basis.mk (v := w) ?_ ?_
  · have hlin1' : LinearIndependent R ((LinearMap.ker f).subtype ∘ w) := by
      simpa [hwd] using hlin1
    exact ((LinearMap.linearIndependent_iff ((LinearMap.ker f).subtype)
      (Submodule.ker_subtype _)).1 hlin1')
  · haveI : FiniteDimensional R A := Module.Basis.finiteDimensional_of_finite b
    haveI : FiniteDimensional  R (LinearMap.ker f) := FiniteDimensional.finiteDimensional_submodule
      _
    haveI : FiniteDimensional  R (Submodule.span R (Set.range v)) :=
      FiniteDimensional.finiteDimensional_submodule _
    have hspan : Submodule.span R (Set.range v) = LinearMap.ker f := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rwa [Submodule.span_le, Set.range_subset_iff]
      · have hdim := LinearMap.finrank_range_add_finrank_ker f
        rw [Module.finrank_eq_card_basis b] at hdim
        have hr1 : Fintype.card τ₂ ≤ Module.finrank R (LinearMap.range f) := by
          exact hlin3.fintype_card_le_finrank
        rw [finrank_span_eq_card hlin1]
        zify at hdim hr1 ⊢
        linarith
    rintro ⟨x, hxk⟩ _
    have hxkc := hxk
    rw [← hspan, ← hwd] at hxkc
    have : Submodule.span R (Set.range (((LinearMap.ker f).subtype) ∘ w)) =
      Submodule.map ((LinearMap.ker f).subtype) (Submodule.span R (Set.range w)) := by
      rw [LinearMap.map_span]; congr
      refine (Set.range_comp ((LinearMap.ker f).subtype) w)
    rw [this] at hxkc
    obtain ⟨y, hy⟩ := Submodule.mem_map.1 hxkc
    have hyeq : y = ⟨x, hxk⟩ := by
      apply Submodule.injective_subtype
      rw [hy.2, Submodule.coe_subtype, Submodule.coe_mk]
    rw [← hyeq]
    exact hy.1

lemma basisKernelOfLinearIndependentKerImEq_apply {B : Type*} [DivisionRing R] [Module R A]
    [AddCommGroup B] [Module R B] {τ₁ τ₂ τ₃ : Type*} [Fintype τ₁] [Fintype τ₂] [Fintype τ₃]
    (hc1 : Fintype.card τ₁ + Fintype.card τ₂ = Fintype.card τ₃)
    (b : Basis τ₃ R A) (f : A →ₗ[R] B) (v : τ₁ → A) (v' : τ₂ → A)
    (hlin1 : LinearIndependent R v) (hlin2 : LinearIndependent R (f ∘ v'))
    (hker : ∀ i, f (v i) = 0) :
  ∀ i,
  ↑((basisKernelOfLinearIndependentKerIm hc1 b f v v' hlin1 hlin2 hker) i) = v i := by
    intro i
    unfold basisKernelOfLinearIndependentKerIm
    simp only [Basis.coe_mk]


/-- If `v` is a collection of vectors with the same cardinality as a basis,
  and `f` is an `R`-linear map
such that ` f ∘ v` is linearly independent, then the kernel of `f` is trivial· -/
lemma kernel_eq_bot_of_linearIndependent_im {B : Type*} [DivisionRing R] [Module R A]
    [AddCommGroup B] [Module R B] {τ : Type*} [Finite τ] (b : Basis τ R A) (f : A →ₗ[R] B)
    (v' : τ → A)
    (hlin2 : LinearIndependent R (f ∘ v')) :
    LinearMap.ker f = ⊥ := by
  haveI := Fintype.ofFinite τ
  haveI : FiniteDimensional R A := Module.Basis.finiteDimensional_of_finite b
  rw [← Submodule.finrank_eq_zero]
  let v : Fin 0 → A := fun _ => 0
  have hker : ∀ (i : Fin 0), f (v i) = 0 := by simp only [IsEmpty.forall_iff]
  have hba :=  basisKernelOfLinearIndependentKerIm ?_ b f v v' (linearIndependent_empty_type) hlin2
    hker
  · rw [Module.finrank_eq_card_basis hba]
    simp only [Fintype.card_fin]
  simp only [Fintype.card_fin, zero_add]

/-- If `f` is a linear map and the vectors in the collection of `v` form a basis for the kernel of
  `f`,
  then this collection can be extended with `v'` to a basis for the vector space,
  if `f ∘ v'` is linearly independent and the sum of the cardinalities of
  `v` and `v'` equals the dimension of the vector space· -/
noncomputable def basisExtensionKernelOfLinearIndependentKerIm
    {B : Type*} [DivisionRing R] [Module R A] [Nontrivial A] [AddCommGroup B] [Module R B] {τ₁ τ₂
      τ₃ : Type*} [Fintype τ₁] [Fintype τ₂]
    [Fintype τ₃] (hc1 : Fintype.card τ₁ + Fintype.card τ₂ = Fintype.card τ₃) (b : Basis τ₃ R A)
    (f : A →ₗ[R] B) (v : τ₁ → A) (v' : τ₂ → A)
    (hlin1 : LinearIndependent R v) (hlin2 : LinearIndependent R (f ∘ v')) (hker : ∀ i,
      f (v i) = 0) :
    Basis (τ₁ ⊕ τ₂) R A := by
  have hlin : LinearIndependent R (Sum.elim v v') := by
    rw [Fintype.linearIndependent_iff]
    intro g
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Sum.forall]
    intro h
    have h' := h
    apply_fun f at h'
    simp only [map_add, map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply, map_zero] at h'
    simp_rw [hker] at h'
    simp only [smul_zero, Finset.sum_const_zero, zero_add] at h'
    replace hlin2 := (Fintype.linearIndependent_iff.1 hlin2) (g ∘ (@Sum.inr τ₁ τ₂)) h'
    simp_rw [Function.comp_apply]  at hlin2
    simp only [hlin2, Module.zero_smul, Finset.sum_const_zero, add_zero] at h
    replace hlin1 := (Fintype.linearIndependent_iff.1 hlin1) (g ∘ (@Sum.inl τ₁ τ₂)) h
    exact ⟨hlin1, hlin2⟩
  haveI : FiniteDimensional R A := Module.Basis.finiteDimensional_of_finite b
  have hcard : Fintype.card (τ₁ ⊕ τ₂) = Fintype.card τ₃ := by rw [Fintype.card_sum, hc1]
  haveI := Basis.index_nonempty  b
  haveI := Equiv.nonempty (Fintype.equivOfCardEq hcard)
  refine basisOfLinearIndependentOfCardEqFinrank hlin ?_
  rw [Module.finrank_eq_card_basis b]
  exact hcard


lemma basisExtensionKernelOfLinearIndependentKerIm_apply_inl
    {B : Type*} [DivisionRing R] [Module R A] [Nontrivial A] [AddCommGroup B] [Module R B] {τ₁ τ₂
      τ₃ : Type*} [Fintype τ₁] [Fintype τ₂] [Fintype τ₃] (hc1 : Fintype.card τ₁ + Fintype.card τ₂ =
      Fintype.card τ₃)
    (b : Basis τ₃ R A) (f : A →ₗ[R] B) (v : τ₁ → A) (v' : τ₂ → A)
    (hlin1 : LinearIndependent R v) (hlin2 : LinearIndependent R (f ∘ v')) (hker : ∀ i,
      f (v i) = 0) (i : τ₁) :
      (basisExtensionKernelOfLinearIndependentKerIm hc1 b f v v' hlin1 hlin2 hker) (Sum.inl i) =
        v i := by
    unfold basisExtensionKernelOfLinearIndependentKerIm
    erw [Basis.mk_apply]
    rfl

lemma basisExtensionKernelOfLinearIndependentKerIm_apply_inr
    {B : Type*} [DivisionRing R] [Module R A] [Nontrivial A] [AddCommGroup B] [Module R B] {τ₁ τ₂
      τ₃ : Type*} [Fintype τ₁] [Fintype τ₂] [Fintype τ₃] (hc1 : Fintype.card τ₁ + Fintype.card τ₂ =
      Fintype.card τ₃)
    (b : Basis τ₃ R A) (f : A →ₗ[R] B) (v : τ₁ → A) (v' : τ₂ → A)
    (hlin1 : LinearIndependent R v) (hlin2 : LinearIndependent R (f ∘ v')) (hker : ∀ i,
      f (v i) = 0) (j : τ₂) :
      (basisExtensionKernelOfLinearIndependentKerIm hc1 b f v v' hlin1 hlin2 hker) (Sum.inr j) =
        v' j := by
    unfold basisExtensionKernelOfLinearIndependentKerIm
    erw [Basis.mk_apply]
    rfl

/-- If `v` is a family of linear maps such that for every `i` there is an entry in the
matrix representing `v i` such that it's different from `0`, while the same entry is `0`
for all the other `v j's`, then the family `v` is linearly independent· -/
lemma linearIndependent_linearMaps_of_repr_diag {R B : Type*} {τ : Type*} [CommRing R] [IsDomain R]
    [Module R A] [AddCommGroup B] [Module R B] {τ₁ τ₂ : Type*}
    (v : τ → (A →ₗ[R] B)) (b : Basis τ₁ R A) (b' : Basis τ₂ R B)
    (h : ∀ (i : τ), (∃ (j : τ₁) (k : τ₂), b'.repr (v i (b j)) k ≠ 0 ∧
    (∀ (l : τ), l ≠ i → b'.repr (v l (b j)) k = 0))) :
LinearIndependent R v := by
  rw [linearIndependent_iff']
  intros s g hg i hins
  obtain ⟨j, k, hjk1, hjk2⟩ := h i
  replace hg := LinearMap.congr_fun hg (b j)
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hg
  have : b'.repr (∑ x ∈ s, g x • (v x) (b j)) k = 0 := by
    rw [hg]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simp only [map_sum, LinearEquiv.map_smulₛₗ, RingHom.id_apply] at this
  rw [Finset.sum_apply', Finset.sum_eq_single i] at this
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hjk1 this
  · intros l _ hlne
    erw [Finsupp.coe_smul, Pi.smul_apply, hjk2 l hlne, smul_zero]
  · simp only [hins, not_true, Finsupp.coe_smul, IsEmpty.forall_iff]


/-- If `f` is a linear map from `A` to `B →ₗ[R] C `, then its kernel is trivial if there exists
a family of vectors `v` with the same cardinality as the dimension of `A` such that for every `i`
there is an entry in the matrix representation of `f ∘ v i` different from zero and such that
that same entry in `f ∘ v l` is zero for all `l ≠ i`· -/
lemma ker_eq_bot_of_linearMap_to_linearMaps {B C : Type*} [AddCommGroup B] [AddCommGroup C]
 [Field R] [Module R A] [Module R B] [Module R C] {τ₁ τ₂ τ₃ : Type*} [Finite τ₁]
 (f : A →ₗ[R] (B →ₗ[R] C)) (b : Basis τ₁ R A) (b' : Basis τ₂ R B) (b'' : Basis τ₃ R C) (v : τ₁ → A)
 (h : ∀ (i : τ₁), (∃ (j : τ₂) (k : τ₃), b''.repr ((f ∘ v) i (b' j)) k ≠ 0
  ∧ (∀ l, l ≠ i → b''.repr ((f ∘ v) l (b' j)) k = 0))) : LinearMap.ker f = ⊥ :=
  kernel_eq_bot_of_linearIndependent_im b f v (linearIndependent_linearMaps_of_repr_diag (f ∘ v) b'
    b'' h)


lemma linearIndependent_of_linearIndependent_eval {R B : Type*} {τ : Type*} [CommRing R]
    [Module R A] [AddCommGroup B] [Module R B] (v : τ → (A →ₗ[R] B))
  (a : A) (hi : LinearIndependent R (fun i => (v i) a)) :
    LinearIndependent R v := by
  rw [linearIndependent_iff'] at hi ⊢
  intros s g hg i hins
  have := LinearMap.congr_fun hg a
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] at this
  exact hi s g this i hins

lemma linearIndependent_of_linearIndependent_eval_repr {R B : Type*} {τ : Type*} [CommRing R]
    [IsDomain R]
  [Module R A] [AddCommGroup B] [Module R B] (v : τ → (A →ₗ[R] B))
  (a : A) {ι : Type*} (b : Basis ι R B)
  (hi : ∀ (i : τ), (∃ (j : ι), b.repr ((v i) a) j ≠ 0 ∧ (∀ (k : τ),
    k ≠ i → b.repr ((v k) a) j = 0))) :
   LinearIndependent R v :=
   linearIndependent_of_linearIndependent_eval v a
  (linearIndependent_of_repr_diag b ((fun i => (v i) a)) hi)

/-- If `f` is a linear map from `A` to `B →ₗ[R] C `, then its kernel is trivial if there exists
a family of vectors `v` with the same cardinality as the dimension of `A` and an element `β` in `B`
such that the vectors `{(f (vᵢ)) β }ᵢ` are in echelon form. -/
lemma ker_eq_bot_of_linearMap_to_linearMaps_eval {B C : Type*} [AddCommGroup B] [AddCommGroup C]
  [Field R] [Module R A] [Module R B] [Module R C] {τ₁ τ₂ : Type*} [Finite τ₁]
  (f : A →ₗ[R] (B →ₗ[R] C)) (b : Basis τ₁ R A) (b' : Basis τ₂ R C) (v : τ₁ → A)
  (β : B) (hi : ∀ (i : τ₁), (∃ (j : τ₂), b'.repr (((f ∘ v) i) β) j ≠ 0 ∧
    (∀ (k : τ₁), k ≠ i → b'.repr (((f ∘ v) k) β) j = 0))) : LinearMap.ker f = ⊥ := by
refine kernel_eq_bot_of_linearIndependent_im b f v ?_
exact linearIndependent_of_linearIndependent_eval_repr (fun i => (f ∘ v) i) β b' hi
