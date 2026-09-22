/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeOver
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeSum
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeAssociatedGradedDomain
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreeScalar
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.DegreePrincipalInitialIdeal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Quotient

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Bases over a subalgebra and the associated graded ring of the degree over it

Let `ν` be a separated multiplicative degree on a commutative ring `R` containing a ring `L` in
degree zero, and let `P` be an `L`-subalgebra of `R`. Suppose given elements `β i ∈ R` of degrees
`γ i` whose initial forms, together with the initial forms of `P`, generate the associated graded
ring freely in the sense of `IsBasisOver`. This is the paper's "basis over `S`": for
`R = K((ℝ^{≤0}))`, `ν = deg`, `P = S` and `β = (c_C)_{C ∈ 𝓒}` it says that `(c_C)_{C ∈ 𝓒}` is a
basis of `K((ℝ^{≤0}))` over `S` with `deg(∑ p_C c_C) = max (deg p_C ⊕ deg C)`.

Then:

* the degree of a `P`-combination `∑ pᵢ βᵢ` is `max (ν(pᵢ) + γᵢ)`, so the `β i` are a `P`-basis
  of `R` (`IsBasisOver.basis`);
* the degree over `P`, `ν_P`, is the largest degree `γ i` of a basis vector occurring in the
  expansion (`IsBasisOver.degreeOver_le_iff_forall_repr`);
* the associated graded ring `gr_{ν_P} R` is free over `P`, which sits in degree zero, on the
  classes `[β] i` of the `β i` in their degrees
  (`IsBasisOver.closure_degreeOverSubalgebraHom_mul_layerClass_eq_top` and
  `IsBasisOver.eq_zero_of_sum_degreeOverSubalgebraHom_mul_layerClass_eq_zero`); consequently every
  additive map `C ⊗ P → gr_{ν_P} R` sending `c i ⊗ p` to `p [β] i`, for a basis `c` of `C`, is
  bijective (`IsBasisOver.bijective_of_tmul`);
* an element `a ∈ P` is prime in `R` whenever `gr_{ν_P} R` is identified with a tensor product
  `C ⊗ P` carrying `1 ⊗ a` to the initial form of `a` for `ν_P`, and `C ⊗ P` and `C ⊗ (P ⧸ (a))`
  are domains (`prime_coe_of_degreeOverGradedRingEquiv`); for the paper, `Θ : (P̂/I) ⊗_K S ≅
  gr_{deg_S} K((ℝ^{≤0}))`.

Freeness rests on one computation: the class of any `t ∈ R` in degree `d` for `ν_P` is the sum
of the terms `pᵢ [β]ᵢ` of its expansion whose degree `γ i` is exactly `d`.
-/

universe u v w x

open scoped TensorProduct

public noncomputable section

namespace MaxAddDegree

variable {R : Type u} {M : Type v} {L : Type w}
variable [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-! ### The basis-over-`P` data -/

section Data

variable [CommRing L] [Algebra L R] [WellFoundedLT M] {ι : Type x}

/-- The hypotheses of the basis-over-`P` theorem: `ν` is separated, the `β i` have degrees `γ i`,
and their initial forms are a basis of the associated graded ring over the initial forms of
`P`. -/
structure IsBasisOver (ν : MaxAddDegree R M) (P : Subalgebra L R)
    (γ : ι → M) (β : ι → R) : Prop where
  separated : ν.IsSeparated
  degree_beta : ∀ i, ν (β i) = γ i
  independent : ∀ (s : Finset ι) (p : ι → P),
    ∑ i ∈ s, ν.initialForm (p i) * ν.initialForm (β i) = 0 →
      ∀ i ∈ s, (p i : R) = 0
  spanning : ∀ (d : M) (g : ν.Component d), ∃ t ∈ Submodule.span P (Set.range β),
    ∃ ht : t ∈ ν.filtrationLE d, ν.componentMk d ⟨t, ht⟩ = g

variable {ν : MaxAddDegree R M} {P : Subalgebra L R} {γ : ι → M} {β : ι → R}

namespace IsBasisOver

omit [WellFoundedLT M] in
/-- Independence follows from independence of the initial forms of the `β i` over any set
containing the initial forms of `P`. -/
theorem independent_of_forall_mem (hν : ν.IsSeparated) (S' : Set ν.AssociatedGraded)
    (hP : ∀ p : P, ν.initialForm (p : R) ∈ S')
    (hind : ∀ (s : Finset ι) (x : ι → ν.AssociatedGraded), (∀ i ∈ s, x i ∈ S') →
      ∑ i ∈ s, x i * ν.initialForm (β i) = 0 → ∀ i ∈ s, x i = 0)
    (s : Finset ι) (p : ι → P)
    (h : ∑ i ∈ s, ν.initialForm (p i) * ν.initialForm (β i) = 0) :
    ∀ i ∈ s, (p i : R) = 0 := fun i hi ↦
  (ν.initialForm_eq_zero_iff_of_isSeparated hν _).mp (hind s (fun i ↦ ν.initialForm (p i))
    (fun i _ ↦ hP (p i)) h i hi)

omit [WellFoundedLT M] in
/-- Spanning follows from the associated graded ring being generated, as an abelian group, by
products of initial forms of `P` with initial forms of the `β i`. -/
theorem spanning_of_forall_exists_sum [ν.IsMultiplicative]
    (hspan : ∀ g : ν.AssociatedGraded, ∃ (κ : Type x) (_ : Fintype κ) (p : κ → P) (idx : κ → ι),
      g = ∑ k, ν.initialForm (p k) * ν.initialForm (β (idx k)))
    (d : M) (g : ν.Component d) :
    ∃ t ∈ Submodule.span P (Set.range β), ∃ ht : t ∈ ν.filtrationLE d,
      ν.componentMk d ⟨t, ht⟩ = g := by
  classical
  obtain ⟨κ, _, p, idx, hg⟩ := hspan (DirectSum.of ν.Component d g)
  set y : κ → R := fun k ↦ (p k : R) * β (idx k) with hy
  have hg' : DirectSum.of ν.Component d g = ∑ k, ν.initialForm (y k) := by
    rw [hg]
    exact Finset.sum_congr rfl fun k _ ↦ (ν.initialForm_mul _ _).symm
  have hcomp : (DirectSum.of ν.Component d g) d = (∑ k, ν.initialForm (y k)) d :=
    congrArg (fun z : ν.AssociatedGraded ↦ z d) hg'
  rw [DirectSum.of_eq_same, DirectSum.sum_apply] at hcomp
  simp only [ν.initialForm_apply] at hcomp
  rw [Finset.sum_dite, Finset.sum_const_zero, add_zero, ← map_sum] at hcomp
  refine ⟨∑ k ∈ Finset.univ.filter (fun k ↦ ν (y k) = (d : WithBot M)), y k, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [hy]
    change (p k) • β (idx k) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨idx k, rfl⟩)
  · exact (ν.filtrationLE d).sum_mem fun k hk ↦
      (ν.mem_filtrationLE_iff _ _).mpr (Finset.mem_filter.mp hk).2.le
  · rw [hcomp]
    congr 1
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only
    exact (Finset.sum_attach _ y).symm

variable (H : IsBasisOver ν P γ β) [ν.IsMultiplicative]
include H

omit [WellFoundedLT M] in
theorem degree_coe_mul_beta (p : P) (i : ι) : ν ((p : R) * β i) = ν p + γ i := by
  rw [ν.map_mul, H.degree_beta]

omit [WellFoundedLT M] in
/-- The degree of a finite `P`-combination of the `β i` is the maximum of the termwise degrees
`ν(p i) + γ i`. -/
theorem degree_finsupp_sum (f : ι →₀ P) :
    ν (f.sum fun i p ↦ (p : R) * β i) = f.support.sup fun i ↦ ν (f i) + γ i := by
  classical
  by_cases hf : f = 0
  · subst hf
    simp
  have hne : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup f.support hne fun i ↦ ν (f i) + γ i
  rw [hsup]
  have hfi₀ : (f i₀ : R) ≠ 0 := fun h ↦ Finsupp.mem_support_iff.mp hi₀ (Subtype.ext h)
  obtain ⟨m₀, hm₀⟩ := WithBot.ne_bot_iff_exists.mp (ν.map_ne_bot_of_ne_zero H.separated hfi₀)
  set d : M := m₀ + γ i₀ with hd
  have hdcoe : ν (f i₀) + (γ i₀ : WithBot M) = (d : WithBot M) := by
    rw [← hm₀, hd, WithBot.coe_add]
  rw [hdcoe]
  -- split the sum into the top-degree terms and the rest
  set top := f.support.filter fun i ↦ ν (f i) + γ i = (d : WithBot M) with htop
  have hsplit : (f.sum fun i p ↦ (p : R) * β i) =
      (∑ i ∈ top, (f i : R) * β i) +
        ∑ i ∈ f.support.filter (fun i ↦ ¬ ν (f i) + γ i = d), (f i : R) * β i := by
    rw [Finsupp.sum, Finset.sum_filter_add_sum_filter_not]
  have hle : ∀ i ∈ f.support, ν (f i) + γ i ≤ (d : WithBot M) := fun i hi ↦ by
    rw [← hdcoe, ← hsup]
    exact Finset.le_sup (f := fun i ↦ ν (f i) + γ i) hi
  have hrest :
      ν (∑ i ∈ f.support.filter (fun i ↦ ¬ ν (f i) + γ i = d), (f i : R) * β i) <
        (d : WithBot M) := by
    refine ν.degree_finsetSum_lt _ _ fun i hi ↦ ?_
    rw [Finset.mem_filter] at hi
    rw [H.degree_coe_mul_beta]
    exact lt_of_le_of_ne (hle i hi.1) hi.2
  have htopmem : ∀ i ∈ top, (f i : R) * β i ∈ ν.filtrationLE d := fun i hi ↦ by
    rw [htop, Finset.mem_filter] at hi
    exact (ν.mem_filtrationLE_iff _ _).mpr (by rw [H.degree_coe_mul_beta, hi.2])
  have htopsum : ∑ i ∈ top, (f i : R) * β i ∈ ν.filtrationLE d :=
    (ν.filtrationLE d).sum_mem htopmem
  have hclass : ν.homogeneousMk d ⟨∑ i ∈ top, (f i : R) * β i, htopsum⟩ ≠ 0 := by
    rw [ν.homogeneousMk_finsetSum top _ htopmem htopsum]
    intro hzero
    have hi₀top : i₀ ∈ top := by
      rw [htop, Finset.mem_filter]
      exact ⟨hi₀, hdcoe⟩
    refine hfi₀ (H.independent top (fun i ↦ f i) ?_ i₀ hi₀top)
    rw [← hzero, ← Finset.sum_attach top]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ν.homogeneousMk_eq_initialForm_of_degree_eq (htopmem i i.2)
      (by rw [H.degree_coe_mul_beta]; exact (Finset.mem_filter.mp i.2).2),
      ν.initialForm_mul]
  have htopdeg : ν (∑ i ∈ top, (f i : R) * β i) = (d : WithBot M) := by
    refine le_antisymm ((ν.mem_filtrationLE_iff _ _).mp htopsum) (not_lt.mp fun hlt ↦ ?_)
    exact hclass (ν.homogeneousMk_eq_zero_of_degree_lt htopsum hlt)
  rw [hsplit, ν.degree_add_eq_of_lt (by rw [htopdeg]; exact hrest), htopdeg]

omit [WellFoundedLT M] in
/-- The `β i` are linearly independent over `P`. -/
theorem linearIndependent : LinearIndependent P β := by
  classical
  rw [LinearIndependent, injective_iff_map_eq_zero]
  intro f hf
  have hsum : (f.sum fun i p ↦ (p : R) * β i) = 0 := by
    rw [← hf, Finsupp.linearCombination_apply]
    exact Finsupp.sum_congr fun i _ ↦ by rw [Algebra.smul_def]; rfl
  have hdeg := H.degree_finsupp_sum f
  rw [hsum, ν.map_zero] at hdeg
  by_contra hne
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hfi : (f i : R) ≠ 0 := fun h ↦ Finsupp.mem_support_iff.mp hi (Subtype.ext h)
  have hle : ν (f i) + γ i ≤ ⊥ := by
    rw [hdeg]
    exact Finset.le_sup (f := fun i ↦ ν (f i) + γ i) hi
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ν.map_ne_bot_of_ne_zero H.separated hfi)
  rw [← hm, ← WithBot.coe_add] at hle
  exact absurd hle (not_le.mpr (WithBot.bot_lt_coe _))

omit [ν.IsMultiplicative] in
/-- The `β i` span `R` over `P`, by well-founded induction on the degree. -/
theorem span_eq_top : Submodule.span P (Set.range β) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  suffices h : ∀ (d : WithBot M) (t : R), ν t = d → t ∈ Submodule.span P (Set.range β) from
    h (ν t) t rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro t ht
    cases d with
    | bot => rw [((isSeparated_iff ν).mp H.separated t).mp ht]; exact Submodule.zero_mem _
    | coe m =>
      have hmem : t ∈ ν.filtrationLE m := (ν.mem_filtrationLE_iff _ _).mpr ht.le
      obtain ⟨t', ht'span, ht'mem, ht'class⟩ := H.spanning m (ν.componentMk m ⟨t, hmem⟩)
      have hdiff : ν (t - t') < (m : WithBot M) := by
        have hsub : ν.componentMk m (⟨t, hmem⟩ - ⟨t', ht'mem⟩) = 0 := by
          rw [map_sub, ht'class, sub_self]
        exact (ν.componentMk_eq_zero_iff m _).mp hsub
      have hrec := ih (ν (t - t')) hdiff (t - t') rfl
      have : t = (t - t') + t' := by ring
      rw [this]
      exact Submodule.add_mem _ hrec ht'span

/-- The basis of `R` over `P` given by the `β i`; for the paper, `(c_C)_{C ∈ 𝓒}` as a basis of
`K((ℝ^{≤0}))` over `S`. -/
def basis : Module.Basis ι P R :=
  Module.Basis.mk H.linearIndependent (by rw [H.span_eq_top])

@[simp]
theorem basis_apply (i : ι) : H.basis i = β i :=
  Module.Basis.mk_apply _ _ i

theorem sum_repr_mul_beta (t : R) :
    (H.basis.repr t).sum (fun i p ↦ (p : R) * β i) = t := by
  conv_rhs => rw [← H.basis.linearCombination_repr t]
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun i _ ↦ by rw [Algebra.smul_def, H.basis_apply]; rfl

end IsBasisOver

/-- A subalgebra `P` whose initial forms generate the associated graded ring as an abelian group
is the whole ring: the case `β = 1` of the basis-over-`P` theorem, proved directly by well-founded
induction on the degree. -/
@[blueprint "lem:initial-forms-generate-subalgebra"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Lifting generation from the associated graded ring")
  (statement := /--
    Let $\nu$ be a separated multiplicative degree on a ring $R$, with
    well-founded value order, and let $P\subseteq R$ be a subalgebra.  If every
    element of $\operatorname{gr}_\nu R$ is a finite sum of initial forms of
    elements of $P$, then $P=R$.
  -/)
  (proof := /--
  Use well-founded induction on $\nu(t)$.  Express the initial form of $t$ as
  a finite sum of initial forms of elements of $P$, and subtract their sum
  $t'\in P$.  Equality of initial forms gives $\nu(t-t')<\nu(t)$, so the
  induction hypothesis puts $t-t'$ in $P$.  Hence $t=(t-t')+t'$ lies in $P$.
  Separatedness handles degree $\bot$.
  -/)]
theorem mem_of_forall_exists_sum_initialForm [ν.IsMultiplicative] (hν : ν.IsSeparated)
    (hspan : ∀ g : ν.AssociatedGraded, ∃ (κ : Type x) (_ : Fintype κ) (p : κ → P),
      g = ∑ k, ν.initialForm (p k))
    (t : R) : t ∈ P := by
  refine ν.mem_of_forall_exists_componentMk_eq hν P.toSubring.toAddSubgroup (fun d g ↦ ?_) t
  obtain ⟨u, hu, hut, hmk⟩ := IsBasisOver.spanning_of_forall_exists_sum (ν := ν) (P := P)
    (β := fun _ : PUnit.{x + 1} ↦ (1 : R))
    (fun g ↦ by
      obtain ⟨κ, _, p, hg⟩ := hspan g
      refine ⟨κ, inferInstance, p, fun _ ↦ PUnit.unit, ?_⟩
      simp only [ν.initialForm_one, mul_one]
      exact hg) d g
  refine ⟨u, ?_, hut, hmk⟩
  rw [Set.range_const, Submodule.mem_span_singleton] at hu
  obtain ⟨a, rfl⟩ := hu
  change (a : R) * 1 ∈ P
  rw [mul_one]
  exact a.2

end Data

/-! ### Scalars on the associated graded ring `gr_{ν_P} R` -/

section Scalars

variable [CommRing L] [Algebra L R] [FaithfulSMul L R] [Nontrivial R] [WellFoundedLT M]
  [Fact (∀ m : M, 0 ≤ m)]
variable (ν : MaxAddDegree R M) (P : Subalgebra L R)

omit [IsOrderedCancelAddMonoid M] [WellFoundedLT M] in
theorem zero_le_of_fact (m : M) : 0 ≤ m := (Fact.out : ∀ m : M, 0 ≤ m) m

omit [Nontrivial R] in
theorem degreeOver_algebraMap_eq_zero' {l : L} (hl : l ≠ 0) :
    ν.degreeOver P (algebraMap L R l) = 0 :=
  ν.degreeOver_algebraMap_eq_zero P (zero_le_of_fact)
    (fun h ↦ hl ((FaithfulSMul.algebraMap_injective L R)
      (h.trans (RingHom.map_zero (algebraMap L R)).symm)))

omit [Nontrivial R] [FaithfulSMul L R] in
theorem degreeOver_coe_eq_zero' {p : P} (hp : p ≠ 0) : ν.degreeOver P (p : R) = 0 :=
  ν.degreeOver_coe_eq_zero P (zero_le_of_fact) fun h ↦ hp (Subtype.ext h)

/-- The scalar homomorphism from `L` to `gr_{ν_P} R`. -/
def degreeOverScalarHom : L →+* (ν.degreeOver P).AssociatedGraded :=
  degreeZeroScalarHom (ν.degreeOver P) (algebraMap L R)
    fun _ hl ↦ ν.degreeOver_algebraMap_eq_zero' P hl

/-- The `L`-algebra structure on `gr_{ν_P} R`. -/
instance degreeOverAlgebra : Algebra L (ν.degreeOver P).AssociatedGraded :=
  (degreeOverScalarHom ν P).toAlgebra

omit [Nontrivial R] in
theorem degreeOver_algebraMap_apply (l : L) (x : (ν.degreeOver P).filtrationLE 0)
    (hx : (x : R) = algebraMap L R l) :
    algebraMap L (ν.degreeOver P).AssociatedGraded l = (ν.degreeOver P).homogeneousMk 0 x :=
  degreeZeroScalarHom_apply _ _ _ l x hx

/-- The homomorphism from `P` to degree zero of `gr_{ν_P} R`; for the paper,
`ψ : S → (gr_{deg_S})_0`. -/
def degreeOverSubalgebraHom : P →+* (ν.degreeOver P).AssociatedGraded :=
  degreeZeroScalarHom (ν.degreeOver P) (algebraMap P R)
    fun _ hp ↦ ν.degreeOver_coe_eq_zero' P hp

omit [Nontrivial R] [FaithfulSMul L R] in
theorem degreeOverSubalgebraHom_apply (p : P) (x : (ν.degreeOver P).filtrationLE 0)
    (hx : (x : R) = p) : degreeOverSubalgebraHom ν P p = (ν.degreeOver P).homogeneousMk 0 x :=
  degreeZeroScalarHom_apply _ _ _ p x hx

omit [Nontrivial R] [Fact (∀ m : M, 0 ≤ m)] [FaithfulSMul L R] in
theorem coe_mem_degreeOver_filtrationLE_zero (p : P) : (p : R) ∈ (ν.degreeOver P).filtrationLE 0 :=
  ((ν.degreeOver P).mem_filtrationLE_iff 0 p).mpr (ν.degreeOver_coe_le_zero P p)

/-- The homomorphism `P → gr_{ν_P} R` as an `L`-algebra homomorphism. -/
def degreeOverSubalgebraAlgHom : P →ₐ[L] (ν.degreeOver P).AssociatedGraded :=
  { degreeOverSubalgebraHom ν P with
    commutes' := fun l ↦ by
      change degreeOverSubalgebraHom ν P (algebraMap L P l) = algebraMap L _ l
      rw [degreeOverSubalgebraHom_apply ν P (algebraMap L P l)
        ⟨algebraMap L R l, (ν.coe_mem_degreeOver_filtrationLE_zero P (algebraMap L P l))⟩ rfl,
        degreeOver_algebraMap_apply ν P l
          ⟨algebraMap L R l, (ν.coe_mem_degreeOver_filtrationLE_zero P (algebraMap L P l))⟩ rfl] }

omit [Nontrivial R] in
theorem degreeOverSubalgebraAlgHom_apply (p : P) :
    degreeOverSubalgebraAlgHom ν P p = degreeOverSubalgebraHom ν P p := (rfl)

end Scalars

/-! ### Freeness of `gr_{ν_P} R` over `P` -/

section Freeness

variable [CommRing L] [Algebra L R] [WellFoundedLT M] [Fact (∀ m : M, 0 ≤ m)]
variable {ι : Type x}
variable {ν : MaxAddDegree R M} {P : Subalgebra L R} {γ : ι → M} {β : ι → R}

namespace IsBasisOver

variable (H : IsBasisOver ν P γ β)
include H

omit [Fact (∀ m : M, 0 ≤ m)] in
theorem degreeOver_coe_mul_beta_le (p : P) (i : ι) :
    ν.degreeOver P ((p : R) * β i) ≤ γ i := by
  refine ((ν.degreeOver P).map_mul_le_add _ _).trans ?_
  calc ν.degreeOver P (p : R) + ν.degreeOver P (β i) ≤ 0 + (γ i : WithBot M) :=
        add_le_add (ν.degreeOver_coe_le_zero P p)
          (ν.degreeOver_le_of_degree_le P (H.degree_beta i).le)
    _ = γ i := zero_add _

omit [Fact (∀ m : M, 0 ≤ m)] in
theorem beta_mem_degreeOver_filtrationLE (i : ι) : β i ∈ (ν.degreeOver P).filtrationLE (γ i) :=
  ((ν.degreeOver P).mem_filtrationLE_iff _ _).mpr
    (ν.degreeOver_le_of_degree_le P (H.degree_beta i).le)

/-- The class `[β] i` of `β i` in degree `γ i` of `gr_{ν_P} R`. -/
def layerClass (i : ι) : (ν.degreeOver P).AssociatedGraded :=
  (ν.degreeOver P).homogeneousMk (γ i) ⟨β i, H.beta_mem_degreeOver_filtrationLE i⟩

omit [Fact (∀ m : M, 0 ≤ m)] in
theorem layerClass_eq (i : ι) :
    H.layerClass i =
      (ν.degreeOver P).homogeneousMk (γ i) ⟨β i, H.beta_mem_degreeOver_filtrationLE i⟩ :=
  (rfl)

/-- The product of the degree-zero class of `p ∈ P` with `[β] i` is the class of `p β i`. -/
theorem degreeOverSubalgebraHom_mul_layerClass (p : P) (i : ι) :
    degreeOverSubalgebraHom ν P p * H.layerClass i =
      (ν.degreeOver P).homogeneousMk (γ i)
        ⟨(p : R) * β i, ((ν.degreeOver P).mem_filtrationLE_iff _ _).mpr
          (H.degreeOver_coe_mul_beta_le p i)⟩ := by
  rw [degreeOverSubalgebraHom_apply ν P p ⟨(p : R), ν.coe_mem_degreeOver_filtrationLE_zero P p⟩ rfl,
    layerClass]
  exact ((ν.degreeOver P).homogeneousMk_mul_of_coe_eq (zero_add _).symm _ _ _ rfl).symm

variable [ν.IsMultiplicative]

/-- The `P`-submodule of elements whose expansion involves only `β i` with `γ i ≤ d`. -/
private def coordSubmodule (d : M) : Submodule P R where
  carrier := {t | ∀ i ∈ (H.basis.repr t).support, γ i ≤ d}
  zero_mem' := by simp
  add_mem' {a b} ha hb i hi := by
    classical
    rw [map_add] at hi
    rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
    · exact ha i h
    · exact hb i h
  smul_mem' p t ht i hi := by
    rw [map_smul] at hi
    exact ht i (Finsupp.support_smul hi)

theorem gamma_le_of_degree_le {t : R} {d : M} (ht : ν t ≤ d) :
    ∀ i ∈ (H.basis.repr t).support, γ i ≤ d := by
  intro i hi
  have hdeg := H.degree_finsupp_sum (H.basis.repr t)
  rw [H.sum_repr_mul_beta] at hdeg
  have hfi : ((H.basis.repr t) i : R) ≠ 0 :=
    fun h ↦ Finsupp.mem_support_iff.mp hi (Subtype.ext h)
  have h1 : ν ((H.basis.repr t) i) + γ i ≤ ν t := by
    rw [hdeg]
    exact Finset.le_sup (f := fun i ↦ ν ((H.basis.repr t) i) + γ i) hi
  have h2 : ((γ i : M) : WithBot M) ≤ ν ((H.basis.repr t) i) + γ i := by
    calc ((γ i : M) : WithBot M) = 0 + (γ i : WithBot M) := (zero_add _).symm
      _ ≤ _ := add_le_add (ν.zero_le_degree H.separated (zero_le_of_fact) hfi) le_rfl
  exact WithBot.coe_le_coe.mp (h2.trans (h1.trans ht))

/-- An element of degree at most `d` lies in `P` provided every `β i` with `γ i ≤ d` does. -/
theorem mem_of_degree_le {t : R} {d : M} (ht : ν t ≤ d)
    (hβ : ∀ i, γ i ≤ d → β i ∈ P) : t ∈ P := by
  rw [← H.sum_repr_mul_beta t, Finsupp.sum]
  exact Subalgebra.sum_mem _ fun i hi ↦ Subalgebra.mul_mem _ (Subtype.mem _)
    (hβ i (H.gamma_le_of_degree_le ht i hi))

/-- The degree over `P` in the basis: `ν_P(t) ≤ d` exactly when every `β i` occurring in the
expansion of `t` has `γ i ≤ d`. -/
theorem degreeOver_le_iff_forall_repr (t : R) (d : M) :
    ν.degreeOver P t ≤ d ↔ ∀ i ∈ (H.basis.repr t).support, γ i ≤ d := by
  rw [ν.degreeOver_le_iff]
  constructor
  · intro ht
    refine ((ν.degreeOverStage_le_iff P (coordSubmodule H d) d).mpr ?_) ht
    intro x hx
    exact H.gamma_le_of_degree_le ((ν.mem_filtrationLE_iff d x).mp hx)
  · intro h
    rw [← H.sum_repr_mul_beta t, Finsupp.sum]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    change ((H.basis.repr t) i) • β i ∈ _
    exact Submodule.smul_mem _ _ (ν.degreeOverStage_mono P (h i hi)
      (ν.mem_degreeOverStage_of_degree_le P (H.degree_beta i).le))

theorem gamma_lt_of_degreeOver_lt {t : R} {d : M} (h : ν.degreeOver P t < d) :
    ∀ i ∈ (H.basis.repr t).support, γ i < d := by
  by_cases ht : t = 0
  · subst ht
    simp
  obtain ⟨m, hm, hmem⟩ := ν.exists_mem_degreeOverStage_of_degreeOver_lt P ht h
  intro i hi
  exact lt_of_le_of_lt ((H.degreeOver_le_iff_forall_repr t m).mp
    ((ν.degreeOver_le_iff P t m).mpr hmem) i hi) hm

/-- The class of `t` in degree `d` for `ν_P` is the sum of the terms `pᵢ [β]ᵢ` of its expansion
with `γ i = d`. -/
theorem homogeneousMk_eq_sum (t : R) (d : M)
    (ht : t ∈ (ν.degreeOver P).filtrationLE d) :
    (ν.degreeOver P).homogeneousMk d ⟨t, ht⟩ =
      ∑ i ∈ (H.basis.repr t).support.filter (fun i ↦ γ i = d),
        degreeOverSubalgebraHom ν P ((H.basis.repr t) i) * H.layerClass i := by
  classical
  set f := H.basis.repr t with hf
  have hγ : ∀ i ∈ f.support, γ i ≤ d :=
    (H.degreeOver_le_iff_forall_repr t d).mp
      (((ν.degreeOver P).mem_filtrationLE_iff _ _).mp ht)
  have hmem : ∀ i ∈ f.support, (f i : R) * β i ∈ (ν.degreeOver P).filtrationLE d :=
    fun i hi ↦
    ((ν.degreeOver P).mem_filtrationLE_iff _ _).mpr
      ((H.degreeOver_coe_mul_beta_le (f i) i).trans (WithBot.coe_le_coe.mpr (hγ i hi)))
  have hsum : ∑ i ∈ f.support, (f i : R) * β i ∈ (ν.degreeOver P).filtrationLE d :=
    ((ν.degreeOver P).filtrationLE d).sum_mem hmem
  have ht' : (⟨t, ht⟩ : (ν.degreeOver P).filtrationLE d) = ⟨_, hsum⟩ := by
    apply Subtype.ext
    change t = ∑ i ∈ f.support, (f i : R) * β i
    rw [← H.sum_repr_mul_beta t, Finsupp.sum]
  rw [ht', (ν.degreeOver P).homogeneousMk_finsetSum f.support _ hmem hsum, Finset.sum_filter]
  rw [← Finset.sum_attach f.support fun i ↦ if γ i = d then
    degreeOverSubalgebraHom ν P (f i) * H.layerClass i else 0]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : γ i = d
  · rw [ite_eq_left h]
    subst h
    rw [H.degreeOverSubalgebraHom_mul_layerClass]
  · rw [ite_eq_right h]
    refine (ν.degreeOver P).homogeneousMk_eq_zero_of_degree_lt (hmem i i.2) ?_
    exact lt_of_le_of_lt (H.degreeOver_coe_mul_beta_le (f i) i)
      (WithBot.coe_lt_coe.mpr (lt_of_le_of_ne (hγ i i.2) h))

/-- The classes `[β] i` generate `gr_{ν_P} R` over `P`: every element is a finite sum of products
`p [β]ᵢ` with `p ∈ P`. -/
theorem closure_degreeOverSubalgebraHom_mul_layerClass_eq_top :
    AddSubmonoid.closure
      (Set.range fun x : P × ι ↦ degreeOverSubalgebraHom ν P x.1 * H.layerClass x.2) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of d g =>
    induction g using componentInductionOn with
    | H x =>
      obtain ⟨t, ht⟩ := x
      rw [← (ν.degreeOver P).homogeneousMk_apply, H.homogeneousMk_eq_sum]
      exact sum_mem fun i _ ↦ AddSubmonoid.subset_closure ⟨(_, i), rfl⟩
  | add u v hu hv => exact add_mem hu hv

/-- The classes `[β] i` are independent over `P`: a vanishing finite combination `∑ pₖ [β]ₖ` has
every coefficient zero. -/
theorem eq_zero_of_sum_degreeOverSubalgebraHom_mul_layerClass_eq_zero (s : Finset ι) (f : ι → P)
    (h : ∑ k ∈ s, degreeOverSubalgebraHom ν P (f k) * H.layerClass k = 0) :
    ∀ k ∈ s, f k = 0 := by
  classical
  have hmem : ∀ k, (f k : R) * β k ∈ (ν.degreeOver P).filtrationLE (γ k) := fun k ↦
    ((ν.degreeOver P).mem_filtrationLE_iff _ _).mpr (H.degreeOver_coe_mul_beta_le (f k) k)
  have himage : ∑ k ∈ s, degreeOverSubalgebraHom ν P (f k) * H.layerClass k =
      ∑ k ∈ s, (ν.degreeOver P).homogeneousMk (γ k) ⟨(f k : R) * β k, hmem k⟩ :=
    Finset.sum_congr rfl fun k _ ↦ H.degreeOverSubalgebraHom_mul_layerClass (f k) k
  intro k₀ hk₀
  have hcomp : (∑ k ∈ s, degreeOverSubalgebraHom ν P (f k) * H.layerClass k) (γ k₀) =
      (0 : (ν.degreeOver P).AssociatedGraded) (γ k₀) := congrArg (fun z ↦ z (γ k₀)) h
  rw [himage, (ν.degreeOver P).homogeneousMk_finsetSum_apply s γ
    (fun k ↦ (f k : R) * β k) hmem (γ k₀), DirectSum.zero_apply,
    (ν.degreeOver P).componentMk_eq_zero_iff] at hcomp
  set t := ∑ k ∈ s.filter (fun k ↦ γ k = γ k₀), (f k : R) * β k with ht
  have hrepr : H.basis.repr t k₀ = f k₀ := by
    have : t = ∑ k ∈ s.filter (fun k ↦ γ k = γ k₀), (f k) • H.basis k := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Algebra.smul_def, H.basis_apply]
      rfl
    rw [this, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single k₀]
    · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro k _ hk
      rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hk.symm,
        smul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨hk₀, rfl⟩ : k₀ ∈ s.filter (fun k ↦ γ k = γ k₀)) h
  by_contra hne
  have hsupp : k₀ ∈ (H.basis.repr t).support := by
    rw [Finsupp.mem_support_iff, hrepr]
    exact hne
  exact lt_irrefl _ (H.gamma_lt_of_degreeOver_lt hcomp k₀ hsupp)

section Bijective

variable {L' : Type*} [CommRing L'] [Algebra L' P] {C : Type*} [CommRing C] [Algebra L' C]
  (c : Module.Basis ι L' C)
  {F : Type*} [FunLike F (C ⊗[L'] P) (ν.degreeOver P).AssociatedGraded]
  [AddMonoidHomClass F (C ⊗[L'] P) (ν.degreeOver P).AssociatedGraded]
  (Θ : F)
  (hΘ : ∀ (i : ι) (p : P), Θ (c i ⊗ₜ[L'] p) = degreeOverSubalgebraHom ν P p * H.layerClass i)
include hΘ

/-- A map `C ⊗ P → gr_{ν_P} R` sending `c i ⊗ p` to `p [β] i` is surjective. -/
theorem surjective_of_tmul : Function.Surjective Θ := by
  intro z
  have hz : z ∈ AddSubmonoid.closure
      (Set.range fun x : P × ι ↦ degreeOverSubalgebraHom ν P x.1 * H.layerClass x.2) := by
    rw [H.closure_degreeOverSubalgebraHom_mul_layerClass_eq_top]
    exact AddSubmonoid.mem_top z
  refine AddSubmonoid.closure_induction (fun y hy ↦ ?_) ⟨0, _root_.map_zero Θ⟩
    (fun _ _ _ _ ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, by rw [map_add, ha, hb]⟩) hz
  obtain ⟨⟨p, i⟩, rfl⟩ := hy
  exact ⟨c i ⊗ₜ[L'] p, hΘ i p⟩

/-- A map `C ⊗ P → gr_{ν_P} R` sending `c i ⊗ p` to `p [β] i` is injective. -/
theorem injective_of_tmul : Function.Injective Θ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  set B := Algebra.TensorProduct.basis P c with hB
  set x' := Algebra.TensorProduct.comm L' C P x with hx'
  set f := B.repr x' with hf
  -- expand `x` in the basis of `P ⊗[L'] C`
  have hexp : x = ∑ k ∈ f.support, c k ⊗ₜ[L'] f k := by
    have h1 : x' = ∑ k ∈ f.support, (f k : P) ⊗ₜ[L'] c k := by
      conv_lhs => rw [← B.linearCombination_repr x', Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 := congrArg (Algebra.TensorProduct.comm L' C P).symm h1
    rw [hx', AlgEquiv.symm_apply_apply, map_sum] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [Algebra.TensorProduct.comm_symm_tmul]
  have hcoord : ∀ k ∈ f.support, f k = 0 := by
    refine H.eq_zero_of_sum_degreeOverSubalgebraHom_mul_layerClass_eq_zero f.support f ?_
    rw [← hx, hexp, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ (hΘ k (f k)).symm
  rw [hexp]
  exact Finset.sum_eq_zero fun k hk ↦ by rw [hcoord k hk, TensorProduct.tmul_zero]

/-- A map `C ⊗ P → gr_{ν_P} R` sending `c i ⊗ p` to `p [β] i` is bijective: `gr_{ν_P} R` is free
over `P` on the classes `[β] i`, and `C ⊗ P` is free over `P` on `c i ⊗ 1`. -/
theorem bijective_of_tmul : Function.Bijective Θ :=
  ⟨H.injective_of_tmul c Θ hΘ, H.surjective_of_tmul c Θ hΘ⟩

end Bijective

end IsBasisOver

end Freeness

/-! ### The prime criterion -/

section Prime

variable [CommRing L] [Algebra L R] [WellFoundedLT M]
variable (ν : MaxAddDegree R M) (P : Subalgebra L R)
variable {L' : Type*} [CommRing L'] [Algebra L' P] {C : Type*} [CommRing C] [Algebra L' C]

/-- The prime criterion: if `C ⊗[L'] P ≃ gr_{ν_P} R` as rings, with `1 ⊗ a ↦ in_{ν_P}(a)` (the
initial form of `a` for `ν_P`), then a non-zero `a ∈ P` is prime in `R` whenever `C ⊗[L'] P` and
`C ⊗[L'] (P ⧸ (a))` are domains. For the paper, `Θ : (P̂/I) ⊗_K S ≅ gr_{deg_S} K((ℝ^{≤0}))`. -/
theorem prime_coe_of_degreeOverGradedRingEquiv
    (Θ : C ⊗[L'] P ≃+* (ν.degreeOver P).AssociatedGraded)
    (hΘ : ∀ a : P, Θ (1 ⊗ₜ[L'] a) = (ν.degreeOver P).initialForm a)
    {a : P} (ha : a ≠ 0) [IsDomain (C ⊗[L'] P)] [IsDomain (C ⊗[L'] (P ⧸ Ideal.span {a}))] :
    Prime (a : R) := by
  classical
  have hψsep : (ν.degreeOver P).IsSeparated := ν.degreeOver_isSeparated P
  have : IsDomain (ν.degreeOver P).AssociatedGraded := Θ.symm.toMulEquiv.isDomain _
  -- the quotient by the initial form is a domain
  have hmap : Ideal.span {(ν.degreeOver P).initialForm (a : R)} =
      (Ideal.span ({1 ⊗ₜ[L'] a} : Set (C ⊗[L'] P))).map
        (Θ : C ⊗[L'] P →+* (ν.degreeOver P).AssociatedGraded) := by
    rw [Ideal.map_span, Set.image_singleton, ← hΘ]
    rfl
  have hmap' : (Ideal.span ({a} : Set P)).map
      (Algebra.TensorProduct.includeRight : P →ₐ[L'] C ⊗[L'] P) =
        Ideal.span ({1 ⊗ₜ[L'] a} : Set (C ⊗[L'] P)) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have : IsDomain ((C ⊗[L'] P) ⧸ Ideal.span ({1 ⊗ₜ[L'] a} : Set (C ⊗[L'] P))) := by
    have e := Algebra.TensorProduct.tensorQuotientEquiv (R := L') L' P C (Ideal.span {a})
    rw [hmap'] at e
    exact e.symm.toMulEquiv.isDomain _
  have : IsDomain ((ν.degreeOver P).AssociatedGraded ⧸
      Ideal.span {(ν.degreeOver P).initialForm (a : R)}) :=
    (Ideal.quotientEquiv _ _ Θ hmap).symm.toMulEquiv.isDomain _
  exact (ν.degreeOver P).prime_of_quotient_span_initialForm_isDomain hψsep
    fun h ↦ ha (Subtype.ext h)

/-- The prime criterion transported along an algebra isomorphism `P₀ ≃ P`: the domain
hypotheses may be verified on any model `P₀` of the subalgebra. -/
theorem prime_coe_of_degreeOverGradedRingEquiv_of_algEquiv
    (Θ : C ⊗[L'] P ≃+* (ν.degreeOver P).AssociatedGraded)
    (hΘ : ∀ a : P, Θ (1 ⊗ₜ[L'] a) = (ν.degreeOver P).initialForm a)
    {P₀ : Type*} [CommRing P₀] [Algebra L' P₀] (e : P₀ ≃ₐ[L'] P)
    {a₀ : P₀} (ha₀ : a₀ ≠ 0) [IsDomain (C ⊗[L'] P₀)]
    [IsDomain (C ⊗[L'] (P₀ ⧸ Ideal.span {a₀}))] : Prime ((e a₀ : P) : R) := by
  have ha : e a₀ ≠ 0 := (map_ne_zero_iff e e.injective).mpr ha₀
  have : IsDomain (C ⊗[L'] P) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L') (A₁ := C)) e).symm.toMulEquiv.isDomain _
  have hmap : Ideal.span {e a₀} = (Ideal.span {a₀}).map (e : P₀ →+* P) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquivAlg (Ideal.span {a₀}) (Ideal.span {e a₀}) e hmap
  have : IsDomain (C ⊗[L'] (P ⧸ Ideal.span {e a₀})) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L') (A₁ := C)) eQ).symm.toMulEquiv.isDomain _
  exact ν.prime_coe_of_degreeOverGradedRingEquiv P Θ hΘ ha

end Prime

end MaxAddDegree
