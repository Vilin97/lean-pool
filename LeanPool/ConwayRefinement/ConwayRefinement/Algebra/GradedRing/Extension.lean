/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.OrdinalGenerators
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Extending a degreewise independent family to a minimal system

Let `(A_β)` be a family of subspaces of a commutative algebra over a field `E`, and put
`D_β = ∑_{i ⊕ j = β, i, j ≠ 0} A_i A_j` (Lean `decomposableAt 𝒜 β`). A family
`x i ∈ A_{wt i}` of positive weights whose members of each weight `β` are linearly independent
modulo `D_β` extends to a minimal system relative to `(A_β)`: in each nonzero weight, extend the
given classes to a basis of `A_β / (A_β ∩ D_β)` and lift the new basis vectors to `A_β`.
-/

universe u v w o

open MvPolynomial Module

public noncomputable section

namespace OrdinalGraded

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal.{o} → Submodule E R) [GradedAlgebra 𝒜]
variable {ι : Type w} {wt : ι → NatOrdinal.{o}} {x : ι → R}

omit [GradedAlgebra 𝒜] in
/-- **Extension to a minimal system.** Elements `x i ∈ A_{wt i}` of positive weight, linearly
independent in each weight `β` modulo `decomposableAt 𝒜 β`, are part of a minimal system
relative to `𝒜`: there are `wt'`, `x'` with `IsMinimalSystem 𝒜 wt' x'` and an injection `e`
satisfying `wt' (e i) = wt i` and `x' (e i) = x i`. -/
@[blueprint "lem:extend-to-minimal-system"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Extension of a degreewise independent family")
  (statement := /--
    Let $E$ be a field, let $R$ be a commutative $E$-algebra, and let
    $(A_\alpha)_{\alpha\in\mathbf{On}}$ be a family of $E$-subspaces of $R$.
    Put
    \[
      D_\beta=\sum_{\substack{i\oplus j=\beta\\i,j\ne0}}A_iA_j.
    \]
    Suppose $w_i\ne0$, $x_i\in A_{w_i}$, and every finitely supported
    combination $\sum_i c_ix_i$ with all $w_i=\beta$ belongs to $D_\beta$
    only when every $c_i$ is zero. Then there are a family $(x'_j)_{j\in I'}$,
    weights $w'_j$, and an injection $e:I\to I'$ such that
    $w'_j\ne0$, $x'_j\in A_{w'_j}$, $w'_{e(i)}=w_i$, and
    $x'_{e(i)}=x_i$. Moreover, the $x'_j$ of weight $\beta$ are independent
    modulo $D_\beta$ for every $\beta$ and span $A_\beta$ modulo $D_\beta$
    whenever $\beta\ne0$.
  -/)
  (proof := /--
  For every $\beta$, pass to $A_\beta/(A_\beta\cap D_\beta)$. Extend the
  prescribed independent classes to a basis and choose lifts in $A_\beta$ for
  the added basis vectors. The union over all nonzero
  weights contains the original family and its classes give the required
  independence and spanning properties weight by weight.
  -/)]
theorem exists_isMinimalSystem_extension (hwt : ∀ i, wt i ≠ 0) (hmem : ∀ i, x i ∈ 𝒜 (wt i))
    (hind : ∀ (β : NatOrdinal) (c : ι →₀ E), (∀ i ∈ c.support, wt i = β) →
      Finsupp.linearCombination E x c ∈ decomposableAt 𝒜 β → c = 0) :
    ∃ (ι' : Type (max v w (o + 1))) (wt' : ι' → NatOrdinal.{o}) (x' : ι' → R) (e : ι → ι'),
      Function.Injective e ∧ (∀ i, wt' (e i) = wt i) ∧ (∀ i, x' (e i) = x i) ∧
        IsMinimalSystem 𝒜 wt' x' := by
  classical
  -- the quotients `A_β / ((A_+)² ∩ A_β)`
  let D : ∀ β : NatOrdinal, Submodule E (𝒜 β) := fun β ↦ (decomposableAt 𝒜 β).comap (𝒜 β).subtype
  let mkV : ∀ β : NatOrdinal, (𝒜 β) →ₗ[E] ((𝒜 β) ⧸ D β) := fun β ↦ (D β).mkQ
  have hmk : ∀ β (z : 𝒜 β), mkV β z = 0 ↔ (z : R) ∈ decomposableAt 𝒜 β := fun β z ↦ by
    change Submodule.Quotient.mk z = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  -- the classes of the given generators of degree `β`
  have hmemβ : ∀ β (i : {i // wt i = β}), x i.1 ∈ 𝒜 β := fun β i ↦ by
    have h := hmem i.1
    rwa [i.2] at h
  let xs : ∀ β : NatOrdinal, {i // wt i = β} → (𝒜 β) ⧸ D β := fun β i ↦ mkV β ⟨x i.1, hmemβ β i⟩
  -- they are linearly independent
  have hli : ∀ β, LinearIndependent E (xs β) := by
    intro β
    rw [linearIndependent_iff']
    intro s g hsum i hi
    set c : ι →₀ E := ∑ j ∈ s, Finsupp.single j.1 (g j) with hcdef
    have hcval : ∀ j ∈ s, c j.1 = g j := by
      intro j hj
      rw [hcdef, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
      · rw [Finsupp.single_eq_same]
      · intro j' _ hj'
        rw [Finsupp.single_apply, ite_eq_right]
        exact fun h ↦ hj' (Subtype.ext h)
      · intro h; exact absurd hj h
    have hcsupp : ∀ j ∈ c.support, wt j = β := by
      intro j hj
      obtain ⟨j', -, hjj'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hj)
      have := Finsupp.support_single_subset hjj'
      rw [Finset.mem_singleton] at this
      rw [this]; exact j'.2
    have hlc : Finsupp.linearCombination E x c = ∑ j ∈ s, g j • x j.1 := by
      rw [hcdef, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ Finsupp.linearCombination_single _ _ _
    have hmem' : Finsupp.linearCombination E x c ∈ decomposableAt 𝒜 β := by
      rw [hlc]
      have h0 : mkV β (∑ j ∈ s, g j • (⟨x j.1, hmemβ β j⟩ : 𝒜 β)) = 0 := by
        rw [map_sum]
        simpa only [map_smul] using hsum
      rw [hmk] at h0
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h0
    have hc0 := hind β c hcsupp hmem'
    rw [← hcval i hi, hc0, Finsupp.zero_apply]
  have hinjxs : ∀ β, Function.Injective (xs β) := fun β ↦ (hli β).injective
  -- the basis extending the classes
  let S : ∀ β : NatOrdinal, Set ((𝒜 β) ⧸ D β) := fun β ↦ Set.range (xs β)
  have hS : ∀ β, LinearIndepOn E id (S β) :=
    fun β ↦ (linearIndepOn_id_range_iff (hinjxs β)).mpr (hli β)
  let bas : ∀ β : NatOrdinal, Basis ((hS β).extend (Set.subset_univ _)) E ((𝒜 β) ⧸ D β) :=
    fun β ↦ Basis.extend (hS β)
  -- the new generators: lifts of the basis vectors outside `S β`
  let J : NatOrdinal → Type v := fun β ↦
    {q : (hS β).extend (Set.subset_univ _) // (q : (𝒜 β) ⧸ D β) ∉ S β}
  have hlift : ∀ β (q : J β), ∃ r : 𝒜 β, mkV β r = q.1.1 :=
    fun β q ↦ Submodule.Quotient.mk_surjective (D β) q.1.1
  choose lift hlift using hlift
  -- the extended system
  let wt' : ι ⊕ (Σ β : {β : NatOrdinal // β ≠ 0}, J β.1) → NatOrdinal :=
    Sum.elim wt fun p ↦ p.1.1
  let x' : ι ⊕ (Σ β : {β : NatOrdinal // β ≠ 0}, J β.1) → R :=
    Sum.elim x fun p ↦ (lift p.1.1 p.2 : R)
  have hmem' : ∀ j, x' j ∈ 𝒜 (wt' j) := by
    rintro (i | ⟨β, q⟩)
    · exact hmem i
    · exact (lift β.1 q).2
  refine ⟨_, wt', x', Sum.inl, Sum.inl_injective, fun i ↦ rfl, fun i ↦ rfl, ?_⟩
  refine { ne_zero := ?_, mem := hmem', independent := ?_, spans := ?_ }
  · rintro (i | ⟨β, q⟩)
    · exact hwt i
    · exact β.2
  · -- independence
    intro β c hc hdec
    -- the classes of the generators of degree `β`
    have hmemβ' : ∀ j : {j // wt' j = β}, x' j.1 ∈ 𝒜 β := fun j ↦ by
      have h := hmem' j.1
      rwa [j.2] at h
    let ψ : {j // wt' j = β} → (𝒜 β) ⧸ D β := fun j ↦ mkV β ⟨x' j.1, hmemβ' j⟩
    have hψinl : ∀ (i : ι) (h : wt' (Sum.inl i) = β), ψ ⟨Sum.inl i, h⟩ = xs β ⟨i, h⟩ :=
      fun i h ↦ rfl
    have hψinr : ∀ (β' : {β : NatOrdinal // β ≠ 0}) (q : J β'.1) (h : wt' (Sum.inr ⟨β', q⟩) = β),
        ψ ⟨Sum.inr ⟨β', q⟩, h⟩ = h ▸ q.1.1 := by
      rintro β' q h
      change β'.1 = β at h
      subst h
      exact hlift β'.1 q
    have hψS : ∀ j, ψ j ∈ (hS β).extend (Set.subset_univ _) := by
      rintro ⟨(i | ⟨β', q⟩), hj⟩
      · rw [hψinl]
        exact (hS β).subset_extend (Set.subset_univ _) ⟨⟨i, hj⟩, rfl⟩
      · rw [hψinr]
        change β'.1 = β at hj
        subst hj
        exact q.1.2
    have hψinj : Function.Injective ψ := by
      rintro ⟨(i | ⟨β', q⟩), hj⟩ ⟨(i' | ⟨β'', q'⟩), hj'⟩ heq
      · rw [hψinl, hψinl] at heq
        have := hinjxs β heq
        exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val this))
      · rw [hψinl, hψinr] at heq
        change β''.1 = β at hj'
        subst hj'
        exact absurd ⟨⟨i, hj⟩, heq⟩ q'.2
      · rw [hψinr, hψinl] at heq
        change β'.1 = β at hj
        subst hj
        exact absurd ⟨⟨i', hj'⟩, heq.symm⟩ q.2
      · rw [hψinr, hψinr] at heq
        change β'.1 = β at hj
        change β''.1 = β at hj'
        obtain ⟨β', hβ'⟩ := β'
        obtain ⟨β'', hβ''⟩ := β''
        change β' = β at hj
        change β'' = β at hj'
        subst hj hj'
        have hq : q = q' := Subtype.ext (Subtype.ext heq)
        subst hq
        rfl
    have hψli : LinearIndependent E ψ := by
      have : ψ = fun j ↦ bas β ⟨ψ j, hψS j⟩ := by
        funext j
        exact (Basis.extend_apply_self (hS β) ⟨ψ j, hψS j⟩).symm
      rw [this]
      exact (bas β).linearIndependent.comp _ fun j j' h ↦ hψinj (congrArg Subtype.val h)
    -- the combination is zero in the quotient
    have hZ : Finsupp.linearCombination E x' c ∈ 𝒜 β := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      refine Submodule.sum_mem _ fun j hj ↦ Submodule.smul_mem _ _ ?_
      rw [← hc j hj]; exact hmem' j
    have hsum : ∑ j ∈ c.support.attach, c j.1 • ψ ⟨j.1, hc j.1 j.2⟩ = 0 := by
      have h1 : (⟨Finsupp.linearCombination E x' c, hZ⟩ : 𝒜 β) =
          ∑ j ∈ c.support.attach, c j.1 • ⟨x' j.1, hmemβ' ⟨j.1, hc j.1 j.2⟩⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        change Finsupp.linearCombination E x' c = ∑ j ∈ c.support.attach, c j.1 • x' j.1
        rw [Finset.sum_attach c.support fun j ↦ c j • x' j, Finsupp.linearCombination_apply,
          Finsupp.sum]
      have h2 := (hmk β ⟨_, hZ⟩).mpr hdec
      rw [h1, map_sum] at h2
      simpa only [map_smul] using h2
    have hall := linearIndependent_iff'.mp hψli
      (c.support.attach.map ⟨fun j ↦ (⟨j.1, hc j.1 j.2⟩ : {j // wt' j = β}),
        fun a b h ↦ Subtype.ext (by simpa using h)⟩) (fun t ↦ c t.1) (by
        rw [Finset.sum_map]
        exact hsum)
    ext j
    by_cases hj : j ∈ c.support
    · exact hall ⟨j, hc j hj⟩ (Finset.mem_map.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩)
    · exact Finsupp.notMem_support_iff.mp hj
  · -- spans
    intro β hβ y hy
    obtain ⟨l, hl⟩ : ∃ l, l = (bas β).repr (mkV β ⟨y, hy⟩) := ⟨_, rfl⟩
    let g : (hS β).extend (Set.subset_univ _) → ι ⊕ (Σ β : {β : NatOrdinal // β ≠ 0}, J β.1) :=
      fun q ↦ if h : (q : (𝒜 β) ⧸ D β) ∈ S β then Sum.inl (Classical.choose (Set.mem_range.mp h)).1
        else Sum.inr ⟨⟨β, hβ⟩, ⟨q, h⟩⟩
    have hg : ∀ q, wt' (g q) = β ∧ ∀ hq, mkV β ⟨x' (g q), hq⟩ = (q : (𝒜 β) ⧸ D β) := by
      intro q
      by_cases h : (q : (𝒜 β) ⧸ D β) ∈ S β
      · have hspec := Classical.choose_spec (Set.mem_range.mp h)
        have hq : g q = Sum.inl (Classical.choose (Set.mem_range.mp h)).1 := dite_eq_left h
        refine ⟨by rw [hq]; exact (Classical.choose (Set.mem_range.mp h)).2, fun hq' ↦ ?_⟩
        rw [← hspec]
        exact congrArg (mkV β) (Subtype.ext (by change x' (g q) = _; rw [hq]; rfl))
      · have hq : g q = Sum.inr ⟨⟨β, hβ⟩, ⟨q, h⟩⟩ := dite_eq_right h
        refine ⟨by rw [hq]; rfl, fun hq' ↦ ?_⟩
        rw [← hlift β ⟨q, h⟩]
        exact congrArg (mkV β) (Subtype.ext (by change x' (g q) = _; rw [hq]; rfl))
    have hmemg : ∀ q, x' (g q) ∈ 𝒜 β := fun q ↦ by
      have h := hmem' (g q)
      rwa [(hg q).1] at h
    refine ⟨Finsupp.mapDomain g l, fun j hj ↦ ?_, ?_⟩
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hj)
      rw [← hq]
      exact (hg q).1
    · have hlc : Finsupp.linearCombination E x' (Finsupp.mapDomain g l) ∈ 𝒜 β := by
        rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
        exact Submodule.sum_mem _ fun q _ ↦ Submodule.smul_mem _ _ (hmemg q)
      rw [← hmk β ⟨y - Finsupp.linearCombination E x' (Finsupp.mapDomain g l), sub_mem hy hlc⟩]
      have h1 : (⟨y - Finsupp.linearCombination E x' (Finsupp.mapDomain g l),
          sub_mem hy hlc⟩ : 𝒜 β) = ⟨y, hy⟩ - ⟨_, hlc⟩ := rfl
      rw [h1, map_sub, sub_eq_zero]
      have h2 : (⟨Finsupp.linearCombination E x' (Finsupp.mapDomain g l), hlc⟩ : 𝒜 β) =
          ∑ q ∈ l.support, l q • ⟨x' (g q), hmemg q⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        change Finsupp.linearCombination E x' (Finsupp.mapDomain g l) =
          ∑ q ∈ l.support, l q • x' (g q)
        rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
        rfl
      rw [h2, map_sum]
      simp only [map_smul]
      conv_lhs => rw [← (bas β).linearCombination_repr (mkV β ⟨y, hy⟩), ← hl,
        Finsupp.linearCombination_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [Basis.extend_apply_self, (hg q).2]

omit [GradedAlgebra 𝒜] in
/-- Every ordinal-graded algebra has a minimal system of homogeneous generators: extend the empty
family. -/
theorem exists_isMinimalSystem :
    ∃ (ι' : Type (max v (o + 1))) (wt' : ι' → NatOrdinal.{o}) (x' : ι' → R),
      IsMinimalSystem 𝒜 wt' x' := by
  obtain ⟨ι', wt', x', -, -, -, -, hmin⟩ := exists_isMinimalSystem_extension 𝒜
    (wt := (Empty.elim : Empty → NatOrdinal.{o})) (x := (Empty.elim : Empty → R))
    (fun i ↦ i.elim) (fun i ↦ i.elim) (fun _ c _ _ ↦ Finsupp.ext fun i ↦ i.elim)
  exact ⟨ι', wt', x', hmin⟩

end OrdinalGraded
