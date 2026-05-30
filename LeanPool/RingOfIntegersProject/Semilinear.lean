/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola,
Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Operations
/-! # Semilinear

This files includes some results on semilinear maps and bases mapped through them.

## Main results:
- `LinearIndependent.mapₛₗ` : linearly independent vectors mapped through a semilinear map
  remain linearly independent if they are disjoint with the kernel of such map.
- `Basis.comp_semilinear` : the reduction of a bases is a bases for the quotient.
- `basisSubmoduleModOfBasisMod` : For `pO ≤ I ≤ O`, A basis for `I/pI` constructed from `I/pO`. -/

open Module

theorem Submodule.coord_in_ideal_of_ideal_smul_top_mem {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Basis ι R M) (I : Ideal R) (x : M) (h : x ∈ I • (⊤ : Submodule R M)) (i : ι) :
    b.coord i x ∈ I := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intros r hr n _
    rw [LinearMap.map_smul, smul_eq_mul ]
    exact Ideal.mul_mem_right _ I hr
  · intros x y hx hy
    rw [LinearMap.map_add]
    exact Ideal.add_mem I hx hy

variable {ι R S M N : Type _} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module S N] (g : R →+* S) (g' : ZeroHom S R) (hg : Function.RightInverse g' g)
   (f : M →ₛₗ[g] N) (f' : N → M) (hf : Function.RightInverse f' f)

theorem Finsupp.apply_linearCombination' (f : M →ₛₗ[g] N) (v) (l : α →₀ R) :
    f (Finsupp.linearCombination R v l) = Finsupp.linearCombination S (f ∘ v) (l.mapRange g
      (map_zero g)) := by
  refine Finsupp.induction_linear l ?_ ?_ ?_
  · simp (config := { contextual := true })
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, mapRange_add, map_add]
    · apply map_add
  · intro _ _
    simp (config := { contextual := true })

include hg in
/-- If `v` is a linearly independent family of vectors and the kernel of a semilinear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors· See also `LinearIndependent.mapₛₗ'` for a similar statement with a different
condition on the kernel of `f` . -/
theorem LinearIndependent.mapₛₗ {v : ι → M} {f : M →ₛₗ[g] N}
    (hf_inj : Submodule.comap (Finsupp.linearCombination R v) (LinearMap.ker f) ≤ RingHom.ker g •
      ⊤) :
    LinearIndependent S (f ∘ v) := by
  rw [linearIndependent_iff_ker]
  haveI : Inhabited M := ⟨0⟩
  rw [← le_bot_iff, Finsupp.linearCombination_comp]
  intros x hx
  let x' : ι →₀ R := x.mapRange g' (map_zero g')
  have x_eq : x = x'.mapRange g (map_zero g) := by
    ext i
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hg]
  suffices h : ∀ i, x' i ∈ RingHom.ker g by
    rw [Submodule.mem_bot, x_eq]
    ext i
    rw [Finsupp.mapRange_apply, Finsupp.zero_apply, ← RingHom.mem_ker]
    apply h
  rw [x_eq, LinearMap.mem_ker, LinearMap.comp_apply,
      Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain,
        ← Finsupp.apply_linearCombination' g f,
       ← LinearMap.comp_apply, ← LinearMap.mem_ker, LinearMap.ker_comp] at hx
  refine Submodule.smul_induction_on (hf_inj hx) ?_ ?_
  · intros r hr x _ i
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  · intros x y hx hy i
    rw [Finsupp.add_apply]
    exact add_mem (hx i) (hy i)


variable [RingHomSurjective g] in
theorem Submodule.finsupp_mem_smul_top (x : ι →₀ R) (I : Ideal R)
    (h : ∀ i, x i ∈ I) : x ∈ (I • ⊤ : Submodule R (ι →₀ R)) := by
  induction x using Finsupp.induction
  case _ => apply zero_mem
  case _ i b x' hix' _ ih =>
    refine add_mem ?_ (ih ?_)
    · specialize h i
      rw [← Finsupp.smul_single_one]
      have hix'_zero : x' i = 0 := by
        simpa [Finsupp.mem_support_iff] using hix'
      rw [Finsupp.add_apply, hix'_zero, add_zero, Finsupp.single_eq_same] at h
      exact Submodule.smul_mem_smul h mem_top
    · intro j
      by_cases hij : i = j
      · subst hij
        have hzero : x' i = 0 := by
          simpa [Finsupp.mem_support_iff] using hix'
        rw [hzero]
        exact zero_mem I
      · specialize h j
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hij), zero_add] at h

include hg
/-- If `v` is a linearly independent family of vectors that can be extended to a basis,
and `f` is a surjective `g`-semilinear map with kernel contained in `ker g • ⊤`,
then `f ∘ v` is linearly independent· -/
theorem LinearIndependent.mapₛₗ' {τ : Type*} {v : ι → M} (b : Basis τ R M) (φ : ι → τ)
     (phi_inj : φ.Injective) (hext : v = b ∘ φ) {f : M →ₛₗ[g] N}
     (hf_inj : LinearMap.ker f ≤ RingHom.ker g • ⊤) :
    LinearIndependent S (f ∘ v) := by
  have hv : LinearIndependent R v := by
    rw [hext]
    exact LinearIndependent.comp (Basis.linearIndependent b) φ phi_inj
  apply LinearIndependent.mapₛₗ g g' hg
  intros x hx
  apply Submodule.finsupp_mem_smul_top
  intro i
  rw [Submodule.mem_comap] at hx
  replace hx := hf_inj hx
  rw [hext, Finsupp.linearCombination_comp, LinearMap.comp_apply ] at hx
  have := Submodule.coord_in_ideal_of_ideal_smul_top_mem b _ _ hx (φ i)
  rw [LinearMap.map_finsupp_linearCombination] at this
  simp only [Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain] at this
  convert this
  rw [Function.comp_assoc, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ (Finset.Subset.refl x.support), Finset.sum_eq_single i]
  · simp only [Function.comp_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  · intros j _ hjnei
    have hne : φ i ≠ φ j := fun hφ => hjnei (phi_inj hφ).symm
    change x j • (b.repr (b (φ j))) (φ i) = 0
    rw [Basis.repr_self, Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_zero]
  · intro hins
    have hzero : x i = 0 := by
      simpa [Finsupp.mem_support_iff] using hins
    rw [hzero, zero_smul]
  · intros h _
    rw [zero_smul]

/-- If we have a basis on an `R`-module `M`,
and we take the quotient of `R` and `M` by "the same thing" `p`,
then we get an `R/p`-basis of `M/p`· -/
noncomputable def Basis.comp_semilinear {ι R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (g : R →+* S) (g' : ZeroHom S R) (hg : Function.RightInverse g' g) [RingHomSurjective g]
    (f : M →ₛₗ[g] N) (f' : N → M) (hf : Function.RightInverse f' f)
    (b : Basis ι R M)
    (h : LinearMap.ker f ≤ RingHom.ker g • ⊤) : Basis ι S N :=
  Basis.mk (v := f ∘ b) (LinearIndependent.mapₛₗ' g g' hg b (@id ι) (Function.injective_id)
    (Function.comp_id b).symm h)
   (by {rw [top_le_iff, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
    LinearMap.range_eq_top]
        exact hf.surjective })

variable [RingHomSurjective g]
lemma Basis.comp_semilinear_def (b : Basis ι R M)
    (h : LinearMap.ker f ≤ RingHom.ker g • ⊤) (i : ι) :
    (Basis.comp_semilinear g g' hg f f' hf b h) i = f (b i) := by
  erw [Basis.mk_apply]
  rfl

lemma Basis.comp_semilinear_repr
    (b : Basis ι R M)
    (h : LinearMap.ker f ≤ RingHom.ker g • ⊤) (x : M) :
    g ∘ (b.repr x) = (Basis.comp_semilinear g g' hg f f' hf b h).repr (f x) := by
  let v : ι →₀ S := Finsupp.mapRange g (RingHom.map_zero g) (b.repr x)
  have : v = g ∘ (b.repr x) := rfl
  rw [← this, ← Basis.repr_linearCombination (Basis.comp_semilinear g g' hg f f' hf b h) v]
  suffices f x = Finsupp.linearCombination S (comp_semilinear g g' hg f f' hf b h) v by rw [this]
  erw [← Basis.linearCombination_repr b x, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, map_sum]
  simp only [LinearMap.map_smulₛₗ, ← Basis.comp_semilinear_def g g' hg f f' hf b h]
  rw [Basis.ext_elem_iff (Basis.comp_semilinear g g' hg f f' hf b h)]
  intro i
  unfold Finsupp.sum
  simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [   Finset.sum_apply' i]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · rfl
  · intros j _ hjne
    rw [Finsupp.single_eq_of_ne (Ne.symm hjne)]
  · intros hin
    have hzero : v i = 0 := by
      simpa [Finsupp.mem_support_iff] using hin
    rw [Finsupp.single_eq_same, hzero]
  · intros j _ hjne
    rw [Finsupp.single_eq_of_ne (Ne.symm hjne)]
  · intros hin
    have hzero : (b.repr x) i = 0 := by
      simpa [Finsupp.mem_support_iff] using hin
    rw [Finsupp.single_eq_same, hzero, map_zero]

/-- Let `S = R/pR`· Given an `S`-basis for `W = I/pO`,
which extends to an `S`-basis for `N = O/pO`, this constructs a basis for
`J = I/pI` using lifts of the other two bases· -/
noncomputable def basisSubmoduleModOfBasisMod {R S M N J : Type _} {n m : ℕ} {p : R} [CommRing R]
    [Field S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup J] [Nonempty (Fin m ⊕ Fin n)]
    [Module R M] [Module S N] [NoZeroSMulDivisors R M] {g : R →+* S}
    (kergp : RingHom.ker g = Ideal.span {p}) (hpnez : p ≠ 0) (g' : ZeroHom S R)
    (hg : Function.RightInverse g' g) [RingHomSurjective g] (f : M →ₛₗ[g] N)
    (hker1 : LinearMap.ker f ≤ RingHom.ker g • ⊤)
    {I : Submodule R M} (hIle : RingHom.ker g • ⊤ ≤ I) (W : Submodule S N) [Module S J]
    (h : I →ₛₗ[g] J) (h' : J → I) (hh : Function.RightInverse h' h) (hker2 : LinearMap.ker h ≤
      RingHom.ker g • ⊤)
    (hW : W.carrier = f '' I) (b : (Fin m) → M) (b' : (Fin n) → M)
    (b1 : Basis (Fin m) S W) (b2 : Basis (Fin m ⊕ Fin n) S N) (b4 : Basis (Fin (m + n)) R I)
    (heq1 : ∀ i, b1 i = f (b i)) (heq2 : ∀ i, b2 (Sum.inl i) = f (b i))
    (heq3 : ∀ i, b2 (Sum.inr i) = f (b' i))
 : Basis (Fin m ⊕ Fin n) S J := by
  have hginv : ∀ x, g (g' x) = x := fun x => hg x
  have g_eval : g p = 0 := by
    rw [← RingHom.mem_ker, kergp]
    exact Ideal.mem_span_singleton_self p
  have hmem1: ∀ i, b i ∈ I := by
    intro i
    have : f (b i) ∈ f '' I := by
      rw [← hW, ← heq1]
      simp only [AddSubsemigroup.mem_carrier, SetLike.coe_mem]
    obtain ⟨x, hxI, hx⟩ := this
    have hmem : b i - x ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hx, sub_self]
    rw [show b i = (b i - x) + x by exact eq_add_of_sub_eq rfl ]
    refine Submodule.add_mem _ (le_trans hker1 hIle hmem) hxI
  have hmem2: ∀ i,  p • (b' i) ∈ I := by
    intro i
    refine hIle ?_
    rw [kergp, Submodule.ideal_span_singleton_smul]
    use b' i
    simp only [Submodule.top_coe, Set.mem_univ, DistribSMul.toLinearMap_apply, and_self]
  have hauxsmul : ∀ (s : S) (x : I), s • (h x) = h ((g' s) • x) := by
    simp only [LinearMap.map_smulₛₗ, hginv, implies_true]
  set v1 := fun (i : Fin m) => h ⟨b i, hmem1 i⟩ with hv1
  set v2:= fun (j : Fin n) => h ⟨p • b' j, hmem2 j⟩ with hv2
  set v := Sum.elim v1 v2 with hv
  have hi : LinearIndependent S v := by
    rw [Fintype.linearIndependent_iff]
    intros c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [hv, Sum.elim_inl, Sum.elim_inr, hv1, hv2] at hc
    have :=  h.map_smul'
    simp_rw [hauxsmul, ← map_sum,  ← LinearMap.map_add] at hc
    rw [← LinearMap.mem_ker] at hc
    replace hc := hker2 hc
    rw [kergp, Submodule.ideal_span_singleton_smul] at hc
    obtain ⟨⟨t, htmem⟩, _, ht⟩ := hc
    simp only [DistribSMul.toLinearMap_apply, SetLike.mk_smul_mk] at ht
    rw [ ← Subtype.val_inj] at ht
    simp only [AddMemClass.coe_add, AddSubmonoidClass.coe_finset_sum] at ht
    have ht_copy := ht
    apply_fun f at ht
    simp only [LinearMap.map_smulₛₗ, map_add, map_sum, g_eval, zero_smul, smul_zero,
     Finset.sum_const_zero, add_zero, hginv, ← heq1] at ht
    have hcl_z : ∀ x, c (Sum.inl x) = 0 := by
      apply Fintype.linearIndependent_iff.1 (Basis.linearIndependent b1) (fun x => c (Sum.inl x))
      rw [← Subtype.val_inj]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul,
        ZeroMemClass.coe_zero]
      exact ht.symm
    simp_rw [hcl_z] at ht_copy
    simp only [map_zero, zero_smul, Finset.sum_const_zero, zero_add, smul_comm _ p,
      ←Finset.smul_sum ] at ht_copy
    rw [← sub_eq_zero, ← smul_sub] at ht_copy
    replace ht_copy := (eq_zero_or_eq_zero_of_smul_eq_zero ht_copy).resolve_left hpnez
    apply_fun f at ht_copy
    simp only [map_sub, map_sum, LinearMap.map_smulₛₗ, map_zero, hginv, ← heq3 ] at ht_copy
    have hftb1 : f t ∈ W := by
      rw [← SetLike.mem_coe, ← Submodule.mem_carrier, hW]
      use (⟨t, htmem⟩ : I)
      simp only [SetLike.mem_coe, and_true, htmem]
    have htsum := Basis.sum_repr b1 (⟨f t, hftb1⟩)
    rw [ ← Subtype.val_inj] at htsum
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul ] at htsum
    simp_rw [heq1, ← heq2] at htsum
    rw [← htsum] at ht_copy
    have hcr_z : ∀ x, c (Sum.inr x) = 0 := by
      intro x
      apply_fun (Basis.coord b2) (Sum.inr x) at ht_copy
      simp only [map_sub, map_sum, map_smul, Basis.coord_apply, Basis.repr_self, ne_eq,
        reduceCtorEq, not_false_eq_true, Finsupp.single_eq_of_ne, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, zero_sub, map_zero, neg_eq_zero] at ht_copy
      rw [Finset.sum_eq_single x] at ht_copy
      · simp only [Finsupp.single_eq_same, mul_one] at ht_copy
        exact ht_copy
      · intros b _ hbnex
        convert mul_zero (c (Sum.inr b))
        refine Finsupp.single_eq_of_ne ?_
        exact fun h => hbnex (Sum.inr.inj h.symm)
      · simp only [Finset.mem_univ, not_true, Finsupp.single_eq_same, mul_one, IsEmpty.forall_iff]
    intro i
    cases i
    · exact hcl_z _
    · exact hcr_z _
  refine basisOfLinearIndependentOfCardEqFinrank hi ?_
  rw [Module.finrank_eq_card_basis (Basis.comp_semilinear g g' hg h h' hh b4 hker2)]
  simp only [Fintype.card_sum, Fintype.card_fin, add_comm]
