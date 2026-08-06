/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Avoiding321

/-!
# Tableaux

This file relates Hecke factorizations of 321-avoiding ASP permutations to
set-valued Young tableaux defined on the inversion set.

This material is not present in [An extended Demazure product](https://arxiv.org/abs/2206.14227);
it gives an additional formal correspondence between fixed-shift set-valued tableaux and
Hecke factorizations for the 321-avoiding case.
-/

namespace LeanPool.DemazureProduct


namespace Tableaux
open ASP321a

/-! ### Links and two-factor data

A `Link` packages the data needed to split a triangle-free ASP set into two
pieces that behave like the two inversion-set components in a Demazure
factorization. This section proves that such links are equivalent to
two-factor factorizations. -/

section Link

/-- Two box sets are linked if comparable boxes are forced to be equal. -/
def linked (A : Set (ℤ × ℤ)) (B : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B, p ≼ q → p = q

/-- A decomposition of a triangle-free ASP set into two linked pieces,
together with the shifts attached to the two factors. -/
structure Link where
  /-- The first part of the box decomposition. -/
  A : Set (ℤ × ℤ)
  /-- The second part of the box decomposition. -/
  B : Set (ℤ × ℤ)
  /-- The ambient triangle-free ASP set. -/
  S : tfas
  /-- The shift assigned to `A`. -/
  χa : ℤ
  /-- The shift assigned to `B`. -/
  χb : ℤ
  /-- The two pieces cover the ambient set. -/
  union_eq : A ∪ B = S.I
  /-- The pieces are linked in order. -/
  sep : linked A B

/-- Build a link from linked pieces and a triangle-free union. -/
def linkOfSets {A B : Set (ℤ × ℤ)} (sep : linked A B) (tf : set_321a_prop (A ∪ B))
  (χa χb : ℤ) : Link :=
  ⟨A, B, ⟨⟨A ∪ B, tf.asp⟩, tf⟩, χa, χb, rfl, sep⟩

namespace Link
/-- The total shift of a link. -/
def chi (L : Link) : ℤ :=
  L.χa + L.χb

lemma B_subset (L : Link) : L.B ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_right

lemma A_subset (L : Link) : L.A ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_left

lemma mem_A_of_mem_inv_not_mem_B (L : Link) {p : ℤ × ℤ}
  (hpτ : p ∈ L.S.I) (hpB : p ∉ L.B) : p ∈ L.A := by
  rw [← L.union_eq] at hpτ
  simp_all

theorem ext {L₁ L₂ : Link}
    (hA : L₁.A = L₂.A) (hB : L₁.B = L₂.B)
    (hχa : L₁.χa = L₂.χa) (hχb : L₁.χb = L₂.χb) : L₁ = L₂ := by
  have hS : L₁.S = L₂.S := by
    cases hs1 : L₁.S with
    | mk S1 p1 =>
      cases hs2 : L₂.S with
      | mk S2 p2 =>
        have hI : S1.I = S2.I := by
          simpa [hs1, hs2] using (by
            rw [← L₁.union_eq, ← L₂.union_eq, hA, hB] : L₁.S.I = L₂.S.I)
        have hAsp : S1 = S2 := AspSet.ext hI
        simp_all
  cases L₁
  simp_all

lemma B_AspSet_prop (L : Link) :
  AspSet_prop L.B where
  directed := by
    intro u v huv
    exact L.S.directed u v (L.B_subset huv)
  closed := by
    intro u v w huv hvw
    exfalso
    have huvS : ⟨u, v⟩ ∈ L.S.I := L.B_subset huv
    have hvwS : ⟨v, w⟩ ∈ L.S.I := L.B_subset hvw
    rcases L.S.prop_321a.tfree u v w with (huv' | hvw')
    · exact huv' huvS
    · exact hvw' hvwS
  coclosed := by
    intro u v w u_lt_v v_lt_w huv hvw
    by_contra! huw
    have := L.S.coclosed u v w u_lt_v v_lt_w
    have h : ⟨u, v⟩ ∈ L.S.I ∨ ⟨v, w⟩ ∈ L.S.I := by
      by_contra! h'
      exact this h'.1 h'.2 (L.B_subset huw)
    rcases h with (h_uv | h_vw)
    · have huv' : ⟨u, v⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_uv huv
      have : ⟨u, v⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_refl u
        · exact le_of_lt v_lt_w
      have := L.sep ⟨u, v⟩ huv' ⟨u, w⟩ huw this
      simp_all
    · have hvw' : ⟨v, w⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_vw hvw
      have : ⟨v, w⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_of_lt u_lt_v
        · exact le_refl w
      have := L.sep ⟨v, w⟩ hvw' ⟨u, w⟩ huw this
      simp_all
  finiteOutdegree := by
    intro u
    exact (L.S.finiteOutdegree u).subset (by
      intro v hv
      exact L.B_subset hv)
  finiteIndegree := by
    intro v
    exact (L.S.finiteIndegree v).subset (by
      intro u hu
      exact L.B_subset hu)

lemma B_set_321a_prop (L : Link) : set_321a_prop L.B where
  asp := L.B_AspSet_prop
  tfree := by
    intro u v w
    rcases L.S.prop_321a.tfree u v w with (huv | hvw)
    · left
      intro huvB
      exact huv (L.B_subset huvB)
    · right
      intro hvwB
      exact hvw (L.B_subset hvwB)

/-- The abstract ASP set represented by the second piece of a link. -/
def bAspSet (L : Link) : AspSet :=
  ⟨L.B, L.B_AspSet_prop⟩

/-- The ambient ASP permutation of a link. -/
noncomputable def τ (L : Link) : AspPerm :=
  L.S.toAspPerm L.chi

@[simp]
lemma inv_set_τ (L : Link) : invSet L.τ = L.S.I := by
  change invSet (L.S.toAspSet.toAspPerm L.chi) = L.S.toAspSet.I
  exact L.S.toAspSet.invSet_of_toAspPerm L.chi

lemma is_321a_τ (L : Link) : is321a L.τ := by
  rw [is_321a_iff_set_321a_prop L.τ L.τ.bijective]
  change set_321a_prop (invSet (L.S.toAspSet.toAspPerm L.chi).func)
  simpa [Link.τ, AspSet.toAspPerm] using set_321a_prop_of_func L.S L.chi

@[simp]
lemma chi_tau (L : Link) : L.τ.χ = L.chi := by
  simpa [Link.τ] using (L.S.toAspSet.chi_of_toAspPerm L.chi)

/-- The second ASP factor associated to a link. -/
noncomputable def β (L : Link) : AspPerm :=
  L.bAspSet.toAspPerm L.χb

@[simp]
lemma inv_set_β (L : Link) : invSet L.β = L.B := by
  change invSet (L.bAspSet.toAspPerm L.χb) = L.bAspSet.I
  exact L.bAspSet.invSet_of_toAspPerm L.χb

@[simp]
lemma chi_beta (L : Link) : L.β.χ = L.χb := by
  simpa [Link.β] using (L.bAspSet.chi_of_toAspPerm L.χb)

lemma A_AspSet_prop (L : Link) :
  AspSet_prop (L.τ.revMap '' L.A) := by
  let L' : Link := {
    A := L.τ.revMap '' L.B
    B := L.τ.revMap '' L.A
    S := tfasOfPerm (inv_is_321a (L.is_321a_τ))
    χa := -L.χb
    χb := -L.χa
    union_eq := by
      ext ⟨u, v⟩
      change ⟨u, v⟩ ∈ L.τ.revMap '' L.B ∪ L.τ.revMap '' L.A ↔
        ⟨u, v⟩ ∈ invSet (((L.τ)⁻¹).func)
      constructor
      · intro h
        rcases h with (hB | hA)
        · rcases hB with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp only [AspPerm.revMap, Prod.mk.injEq] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ invSet L.τ := by
            simpa [L.inv_set_τ] using L.B_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
        · rcases hA with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp only [AspPerm.revMap, Prod.mk.injEq] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ invSet L.τ := by
            simpa [L.inv_set_τ] using L.A_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      · intro h
        have h' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ invSet L.τ := by
          have hτi :
              ⟨L.τ (L.τ⁻¹ u), L.τ (L.τ⁻¹ v)⟩ ∈ invSet ((L.τ)⁻¹).func := by
            simpa using h
          have := (L.τ.inv_set_inverse (L.τ⁻¹ v) (L.τ⁻¹ u)).mpr hτi
          simpa using this
        have h'' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ L.S.I := by
          simpa [L.inv_set_τ] using h'
        rw [← L.union_eq] at h''
        rcases h'' with (hA | hB)
        · right
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hA, ?_⟩
          simp only [AspPerm.revMap, AspPerm.mul_inv_cancel_eval]
        · left
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hB, ?_⟩
          simp only [AspPerm.revMap, AspPerm.mul_inv_cancel_eval]
    sep := by
      intro p hp q hq hpq
      rcases hp with ⟨⟨u, v⟩, huv, rfl⟩
      rcases hq with ⟨⟨u', v'⟩, hu'v', rfl⟩
      simp only [AspPerm.revMap] at hpq
      have hpτi : ⟨L.τ v, L.τ u⟩ ∈ invSet (((L.τ)⁻¹).func) := by
        have huvτ : ⟨u, v⟩ ∈ invSet L.τ := by
          simpa [L.inv_set_τ] using L.B_subset huv
        exact (L.τ.inv_set_inverse u v).mp huvτ
      have hqτi : ⟨L.τ v', L.τ u'⟩ ∈ invSet (((L.τ)⁻¹).func) := by
        have hu'v'τ : ⟨u', v'⟩ ∈ invSet L.τ := by
          simpa [L.inv_set_τ] using L.A_subset hu'v'
        exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      have hqup : u ≤ u' := by
        have hu_snk : isSnk (L.τ⁻¹) (L.τ u) := snk_of_inv hpτi
        simpa using snk_le (inv_is_321a (L.is_321a_τ)) hu_snk hpq.2
      have hvpv : v' ≤ v := by
        have hv_src : isSrc (L.τ⁻¹) (L.τ v) := src_of_inv hpτi
        simpa using src_ge (inv_is_321a (L.is_321a_τ)) hv_src hpq.1
      have hqp : ⟨u', v'⟩ ≼ ⟨u, v⟩ := by
        exact ⟨hqup, hvpv⟩
      have hEq : (u', v') = (u, v) := L.sep (u', v') hu'v' (u, v) huv hqp
      simpa [AspPerm.revMap] using congrArg L.τ.revMap hEq.symm
    }
  have h' := B_AspSet_prop L'
  simpa [L'] using h'

/-- The abstract ASP set represented by the first piece of a link. -/
def aAspSet (L : Link) : AspSet :=
  ⟨L.τ.revMap '' L.A, A_AspSet_prop L⟩

/-- The first ASP factor associated to a link. -/
noncomputable def α (L : Link) : AspPerm :=
  (L.aAspSet.toAspPerm (-L.χa))⁻¹

@[simp]
lemma inv_set_α (L : Link) : L.A = L.τ.sr L.α '' invSet L.α := by
  have hAinv : invSet (((Link.α L)⁻¹).func) = L.τ.revMap '' L.A := by
    rw [Link.α, inv_inv]
    change invSet (L.aAspSet.toAspPerm (-L.χa)) = L.aAspSet.I
    exact L.aAspSet.invSet_of_toAspPerm (-L.χa)
  ext ⟨u, v⟩
  constructor
  · intro huv
    apply (L.τ.sr_crit L.α u v).mpr
    rw [hAinv]
    exact ⟨⟨u, v⟩, huv, by simp only [AspPerm.revMap]⟩
  · intro huv
    have hrev : ⟨L.τ v, L.τ u⟩ ∈ L.τ.revMap '' L.A := by
      rw [← hAinv]
      exact (L.τ.sr_crit L.α u v).mp huv
    rcases hrev with ⟨⟨u', v'⟩, hu'v', hEq⟩
    simp only [AspPerm.revMap, Prod.mk.injEq] at hEq
    rcases hEq with ⟨hv, hu⟩
    apply L.τ.injective at hv
    apply L.τ.injective at hu
    simpa [hu, hv] using hu'v'

@[simp]
lemma chi_alpha (L : Link) : L.α.χ = L.χa := by
  rw [Link.α, AspPerm.chi_dual]
  have hχ := L.aAspSet.chi_of_toAspPerm (-L.χa)
  linarith

lemma dprod (L : Link) : L.α ⋆ L.β = L.τ := by
  have hτ : L.τ = L.α ⋆ L.β := by
    apply (dprod_eq_iff (τ := L.τ) (α := L.α) (β := L.β) (L.is_321a_τ)).mpr
    constructor
    · rw [L.chi_alpha, L.chi_beta, L.chi_tau, Link.chi]
    constructor
    · simpa [L.inv_set_τ, L.inv_set_α, L.inv_set_β] using L.union_eq.symm
    · intro p hp q hq hpq
      have hp' : p ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hp
      have hq' : q ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hq
      exact L.sep p hp'.1 q hq'.2 hpq
  exact hτ.symm

end Link

variable {τ : AspPerm} (h_321a : is321a τ)
include h_321a

/-- The link associated to a Demazure factorization of a 321-avoiding permutation. -/
noncomputable def linkOfDprod {α β : AspPerm}
  (dprod : α ⋆ β = τ) : Link where
  A := (τ.sr α) '' invSet α
  B := invSet β
  S := tfasOfPerm h_321a
  χa := α.χ
  χb := β.χ
  union_eq := by
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.1.symm
  sep := by
    intro p hp q hq hpq
    have h_L : β ≤L τ := by
      rw [← dprod]
      exact Submodular.lel_of_dprod α β
    have h_R : α ≤R τ := by
      rw [← dprod]
      exact Submodular.ler_of_dprod α β
    have hp' : p ∈ invSet β := by
      exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
        ((AspPerm.sr_subset τ α h_R) hp)
    have hq' : q ∈ (τ.sr α) '' (invSet α) := by
      exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.2 p ⟨hp, hp'⟩ q ⟨hq', hq⟩ hpq

lemma rev_A_eq_inv_inv_of_Link_of_dprod {α β : AspPerm} (dprod : α ⋆ β = τ) :
  τ.revMap '' (linkOfDprod h_321a dprod).A = invSet α⁻¹.func := by
  ext ⟨u, v⟩
  change
    ⟨u, v⟩ ∈ τ.revMap '' (τ.sr α '' invSet α.func) ↔
      ⟨u, v⟩ ∈ invSet α⁻¹.func
  constructor
  · intro h
    rcases h with ⟨⟨u', v'⟩, hu'v', hEq⟩
    have hα : ⟨τ v', τ u'⟩ ∈ invSet α⁻¹.func := (τ.sr_crit α u' v').mp hu'v'
    simp only [AspPerm.revMap, Prod.mk.injEq] at hEq
    simp_all
  · intro huv
    have hsr : ⟨τ⁻¹ v, τ⁻¹ u⟩ ∈ τ.sr α '' invSet α := by
      apply (τ.sr_crit α (τ⁻¹ v) (τ⁻¹ u)).mpr
      simpa using huv
    refine ⟨⟨τ⁻¹ v, τ⁻¹ u⟩, hsr, ?_⟩
    simp only [AspPerm.revMap, AspPerm.mul_inv_cancel_eval]

/-- Links with ambient permutation `τ` are equivalent to Demazure
factorizations `τ = α ⋆ β`. -/
noncomputable def linkEquivDprod :
  {L : Link | L.τ = τ } ≃ {⟨α, β⟩ : AspPerm × AspPerm | α ⋆ β = τ } where
  toFun L := ⟨⟨L.val.α, L.val.β⟩, by
    simp only [AspPerm.ext, Set.mem_setOf_eq]
    rw [L.val.dprod, L.prop]⟩
  invFun x := ⟨linkOfDprod h_321a x.property, by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · have h_inv := (tfasOfPerm h_321a).toAspSet.invSet_of_toAspPerm (α.χ + β.χ)
      change invSet ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)) =
        (tfasOfPerm h_321a).toAspSet.I
      exact h_inv
    · change ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
      have hχ' : ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
        exact (tfasOfPerm h_321a).toAspSet.chi_of_toAspPerm (α.χ + β.χ)
      rw [hχ']
      rw [← h_dprod]
      exact (AspPerm.chi_star α β).symm⟩
  left_inv L := by
    have hdp : L.val.α ⋆ L.val.β = τ := by
      rw [L.val.dprod, L.prop]
    apply Subtype.ext
    apply Link.ext
    · dsimp [linkOfDprod]
      have hsr : τ.sr L.val.α '' invSet L.val.α = L.val.τ.sr L.val.α '' invSet L.val.α := by
        simpa using congrArg (fun t => t.sr L.val.α '' invSet L.val.α) L.prop.symm
      exact hsr.trans L.val.inv_set_α.symm
    · change invSet L.val.β = L.val.B
      exact L.val.inv_set_β
    · change L.val.α.χ = L.val.χa
      exact L.val.chi_alpha
    · change L.val.β.χ = L.val.χb
      exact L.val.chi_beta
  right_inv x := by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    have hτL : (linkOfDprod h_321a h_dprod).τ = τ := by
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · have h_inv := (tfasOfPerm h_321a).toAspSet.invSet_of_toAspPerm (α.χ + β.χ)
        change invSet ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)) =
          (tfasOfPerm h_321a).toAspSet.I
        exact h_inv
      · change ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
        have hχ' : ((tfasOfPerm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
          exact (tfasOfPerm h_321a).toAspSet.chi_of_toAspPerm (α.χ + β.χ)
        rw [hχ']
        rw [← h_dprod]
        exact (AspPerm.chi_star α β).symm
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      let asps := (linkOfDprod h_321a h_dprod).aAspSet
      suffices asps.toAspPerm (-(linkOfDprod h_321a h_dprod).χa) = α⁻¹ by
        calc
          (linkOfDprod h_321a h_dprod).α
              = (asps.toAspPerm (-(linkOfDprod h_321a h_dprod).χa))⁻¹ := by
                  rfl
          _ = (α⁻¹)⁻¹ := by rw [this]
          _ = α := by simp only [inv_inv]
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        change (linkOfDprod h_321a h_dprod).aAspSet.I = invSet α⁻¹.func
        simpa [Link.aAspSet, hτL] using
          rev_A_eq_inv_inv_of_Link_of_dprod (τ := τ) h_321a h_dprod
      · rw [AspSet.chi_of_toAspPerm]
        simp only [linkOfDprod, AspPerm.chi_dual]
    · dsimp
      let asps := (linkOfDprod h_321a h_dprod).bAspSet
      suffices asps.toAspPerm (linkOfDprod h_321a h_dprod).χb = β by
        calc
          (linkOfDprod h_321a h_dprod).β
              = asps.toAspPerm (linkOfDprod h_321a h_dprod).χb := by
                  rfl
          _ = β := this
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        change invSet β.func = invSet β.func
        rfl
      · rw [AspSet.chi_of_toAspPerm]
        simp only [linkOfDprod]

end Link

/-! ### Chains and Hecke factorizations

This section iterates the two-factor link construction to compare Hecke
factorizations of a 321-avoiding ASP permutation with chains of inversion-box
data whose union and total shift recover `τ`. -/

section Chains
variable {τ : AspPerm} (h_321a : is321a τ)
open AspPerm

/-- A Hecke factorization of `τ`, represented as a list of ASP permutations
whose Demazure product is `τ`. -/
def HeckeFactorization (τ : AspPerm) : Type :=
  {P : List AspPerm //
    DProd P = τ}

/-- The union of all box sets in a shifted chain. -/
def boxUnion : List (Set (ℤ × ℤ) × ℤ) → Set (ℤ × ℤ)
  | [] => ∅
  | head :: tail => head.1 ∪ boxUnion tail

/-- The sum of all shifts in a shifted chain. -/
def chiSum : List (Set (ℤ × ℤ) × ℤ) → ℤ
  | [] => 0
  | head :: tail => head.2 + chiSum tail

/-- The predicate that adjacent pieces form a linked shifted chain. -/
def isChain : List (Set (ℤ × ℤ) × ℤ) → Prop
  | [] => True
  | ⟨A,_⟩ :: Q =>
      linked A (boxUnion Q)
      ∧ isChain Q

/-- A chain of box sets with shifts whose union is `invSet τ`, whose total
shift is `τ.χ`, and whose pieces are linked in order. -/
def PChain (τ : AspPerm) : Type :=
  {C : List (Set (ℤ × ℤ) × ℤ) // isChain C ∧ boxUnion C = invSet τ ∧ chiSum C = τ.χ}

/-- Convert a list of ASP permutations to its chain of inversion-box pieces and shifts. -/
noncomputable def lSetOfLPerm : List AspPerm → List (Set (ℤ × ℤ) × ℤ)
  | [] => []
  | α :: L =>
    ((DProd (α :: L)).sr α '' (invSet α), α.χ) :: lSetOfLPerm L

lemma LSet_cons (α : AspPerm) (L : List AspPerm) :
    lSetOfLPerm (α :: L) =
      ((DProd (α :: L)).sr α '' invSet α, α.χ) :: lSetOfLPerm L := by
  rfl

include h_321a

lemma LSet_chiSum (A : HeckeFactorization τ) :
  chiSum (lSetOfLPerm A.val) = τ.χ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp only [lSetOfLPerm, chiSum, ← dprodA, List.foldr_nil, id_chi]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, chiSum, ih']
      linarith

lemma LSet_boxUnion (A : HeckeFactorization τ) :
  boxUnion (lSetOfLPerm A.val) = invSet τ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp only [lSetOfLPerm, boxUnion, ← dprodA, List.foldr_nil, inv_set_id]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_R : α ≤R τ := by
        simp_all
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, boxUnion, ih']
      have := ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.1.symm
      convert this

lemma LSet_isChain (A : HeckeFactorization τ) :
  isChain (lSetOfLPerm A.val) := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp only [lSetOfLPerm, isChain]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      rw [LSet_cons]
      constructor
      · rw [LSet_boxUnion h_321a_β ⟨L, rfl⟩]
        unfold linked
        rw [dprodA]
        intro p hp q hq hpq
        refine ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.2 p ?_ q ?_ hpq
        · suffices p ∈ invSet β by
            exact ⟨hp, this⟩
          exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
            ((AspPerm.sr_subset τ α h_R) hp)
        · suffices q ∈ τ.sr α '' invSet α by
            exact ⟨this, hq⟩
          exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
      · exact ih'

/-- Convert a Hecke factorization to the corresponding shifted chain. -/
noncomputable def pChainOfHf (A : HeckeFactorization τ) : PChain τ :=
  ⟨lSetOfLPerm A.val, LSet_isChain h_321a A, LSet_boxUnion h_321a A, LSet_chiSum h_321a A⟩

omit h_321a in
/-- Reconstruct a list of ASP permutations from a shifted chain. -/
noncomputable def lPermOfChain :
  (C : List (Set (ℤ × ℤ) × ℤ)) → isChain C → set_321a_prop (boxUnion C) → List AspPerm
  | [], _, _ => []
  | ⟨A, χ⟩ :: Q, hC, htfas =>
    let L := linkOfSets hC.1 htfas χ (chiSum Q)
    L.α :: lPermOfChain Q hC.2 (by
      change set_321a_prop L.B
      exact L.B_set_321a_prop)

omit h_321a in
theorem DProd_LPerm_of_Chain :
    (C : List (Set (ℤ × ℤ) × ℤ)) → (hC : isChain C) →
      (htfas : set_321a_prop (boxUnion C)) →
        DProd (lPermOfChain C hC htfas) =
          ((⟨boxUnion C, htfas.asp⟩ : AspSet).toAspPerm (chiSum C))
  | [], _, htfas => by
      simp only [lPermOfChain, DProd, boxUnion, chiSum]
      let asps : AspSet := ⟨∅, htfas.asp⟩
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · change invSet AspPerm.id = invSet (asps.toAspPerm 0)
        rw [inv_set_id]
        exact (asps.invSet_of_toAspPerm 0).symm
      · change AspPerm.id.χ = (asps.toAspPerm 0).χ
        rw [id_chi]
        exact (asps.chi_of_toAspPerm 0).symm
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := linkOfSets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        change set_321a_prop L.B
        exact L.B_set_321a_prop
      have ih := DProd_LPerm_of_Chain Q hC.2 htfasQ
      rw [lPermOfChain, DProd_cons, ih]
      apply AspPerm.ext.mpr
      change (L.α ⋆ L.β).func = L.τ.func
      exact congrArg AspPerm.func L.dprod

/-- Convert a shifted chain back to a Hecke factorization. -/
noncomputable def hfOfPChain (C : PChain τ) : HeckeFactorization τ := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  refine ⟨lPermOfChain C.val C.prop.1 tfas, ?_⟩
  let asps : AspSet := ⟨boxUnion C.val, tfas.asp⟩
  have h_asps : asps.toAspPerm (chiSum C.val) = τ := by
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · rw [asps.invSet_of_toAspPerm (chiSum C.val)]
      exact C.prop.2.1
    · simpa [asps, C.prop.2.2] using (asps.chi_of_toAspPerm (chiSum C.val))
  exact (DProd_LPerm_of_Chain C.val C.prop.1 tfas).trans h_asps

omit h_321a in
lemma LSet_of_LPerm_of_Chain :
  ∀ (C : List (Set (ℤ × ℤ) × ℤ)) (hC : isChain C) (htfas : set_321a_prop (boxUnion C)),
    lSetOfLPerm (lPermOfChain C hC htfas) = C
  | [], _, _ => by
      simp only [lPermOfChain, lSetOfLPerm]
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := linkOfSets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        change set_321a_prop L.B
        exact L.B_set_321a_prop
      have ih := LSet_of_LPerm_of_Chain Q hC.2 htfasQ
      have hβ : DProd (lPermOfChain Q hC.2 htfasQ) = L.β := by
        let asps : AspSet := ⟨boxUnion Q, htfasQ.asp⟩
        apply AspPerm.eq_of_inv_set_eq_of_chi_eq
        · rw [DProd_LPerm_of_Chain Q hC.2 htfasQ]
          rw [L.inv_set_β]
          change invSet ((asps.toAspPerm (chiSum Q)).func) = boxUnion Q
          exact asps.invSet_of_toAspPerm (chiSum Q)
        · rw [DProd_LPerm_of_Chain Q hC.2 htfasQ]
          rw [L.chi_beta]
          change (asps.toAspPerm (chiSum Q)).χ = chiSum Q
          exact asps.chi_of_toAspPerm (chiSum Q)
      have hτ : DProd (L.α :: lPermOfChain Q hC.2 htfasQ) = L.τ := by
        simpa [DProd_cons, hβ] using L.dprod
      have hA : (DProd (L.α :: lPermOfChain Q hC.2 htfasQ)).sr L.α '' invSet L.α = A := by
        have hsr :
            (DProd (L.α :: lPermOfChain Q hC.2 htfasQ)).sr L.α '' invSet L.α
              = L.τ.sr L.α '' invSet L.α := by
          simpa using congrArg (fun t => t.sr L.α '' invSet L.α) hτ
        calc
          (DProd (L.α :: lPermOfChain Q hC.2 htfasQ)).sr L.α '' invSet L.α
              = L.τ.sr L.α '' invSet L.α := hsr
          _ = L.A := L.inv_set_α.symm
          _ = A := by rfl
      rw [lPermOfChain, lSetOfLPerm]
      simp only [List.foldr_cons, Link.chi_alpha, ih, List.cons.injEq, Prod.mk.injEq, and_true]
      constructor
      · exact hA
      · rfl

lemma PChain_of_HF_of_PChain (C : PChain τ) :
  pChainOfHf h_321a (hfOfPChain h_321a C) = C := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  apply Subtype.ext
  simpa [pChainOfHf, hfOfPChain] using
    (LSet_of_LPerm_of_Chain C.val C.prop.1 tfas)

lemma HF_of_PChain_of_HF (A : HeckeFactorization τ) :
  hfOfPChain h_321a (pChainOfHf h_321a A) = A := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      apply Subtype.ext
      rfl
  | cons α T ih =>
      let β := DProd T
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is321a β := is_321a_of_lel h_321a h_L
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, DProd_cons]
      have ih' := ih h_321a_β (by rfl)
      apply Subtype.ext
      have htfas : set_321a_prop (boxUnion (lSetOfLPerm (α :: T))) := by
        rw [LSet_boxUnion h_321a ⟨α :: T, dprodA⟩]
        exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
      change
        lPermOfChain (lSetOfLPerm (α :: T)) (LSet_isChain h_321a ⟨α :: T, dprodA⟩) htfas
          = α :: T
      simp only [LSet_cons, lPermOfChain]
      let Lnk : Link := linkOfSets
        (A := (DProd (α :: T)).sr α '' invSet α)
        (B := boxUnion (lSetOfLPerm T))
        (LSet_isChain h_321a ⟨α :: T, dprodA⟩).1
        htfas α.χ (chiSum (lSetOfLPerm T))
      have htfasT :
          set_321a_prop (boxUnion (lSetOfLPerm T)) := by
        change set_321a_prop Lnk.B
        exact Lnk.B_set_321a_prop
      have hTail :
          lPermOfChain (lSetOfLPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2
            htfasT = T := by
        simpa [pChainOfHf, hfOfPChain] using congrArg Subtype.val ih'
      have hLink : Lnk = linkOfDprod h_321a τ_eq := by
        have hA : Lnk.A = (linkOfDprod h_321a τ_eq).A := by
          change (DProd (α :: T)).sr α '' invSet α = τ.sr α '' invSet α
          simp only [dprodA]
        have hB : Lnk.B = (linkOfDprod h_321a τ_eq).B := by
          change boxUnion (lSetOfLPerm T) = invSet β
          simpa [Lnk, linkOfDprod] using (LSet_boxUnion h_321a_β ⟨T, rfl⟩)
        have hχa : Lnk.χa = (linkOfDprod h_321a τ_eq).χa := by
          rfl
        have hχb : Lnk.χb = (linkOfDprod h_321a τ_eq).χb := by
          change chiSum (lSetOfLPerm T) = β.χ
          simpa [Lnk, linkOfDprod] using (LSet_chiSum h_321a_β ⟨T, rfl⟩)
        exact Link.ext hA hB hχa hχb
      let e := linkEquivDprod (τ := τ) h_321a
      let x : {⟨α', β'⟩ : AspPerm × AspPerm | α' ⋆ β' = τ } := ⟨⟨α, β⟩, τ_eq⟩
      have hα₀ : (linkOfDprod h_321a τ_eq).α = α := by
        simpa [e, x, linkEquivDprod] using
          congrArg Prod.fst (congrArg Subtype.val (e.right_inv x))
      have hα : Lnk.α = α := by
        simp_all
      calc
        Lnk.α :: lPermOfChain (lSetOfLPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT
          = α :: lPermOfChain (lSetOfLPerm T)
              (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT := by
                simp_all
        _ = α :: T := by simp only [hTail]

/-- Hecke factorizations of a 321-avoiding ASP permutation are equivalent to
chains of box sets with shifts. -/
noncomputable def hfEquivPChain :
  HeckeFactorization τ ≃ PChain τ
  where
  toFun := pChainOfHf h_321a
  invFun := hfOfPChain h_321a
  left_inv := HF_of_PChain_of_HF h_321a
  right_inv := PChain_of_HF_of_PChain h_321a

end Chains

/-! ### Set-valued tableaux and label chains

This section recodes chains of box sets by distributing labels `1, ..., n`
among the boxes of `invSet τ`. The order condition on labels is exactly the
chain-separation condition in tableau form. -/

section SetValuedTableaux

/-- The semistandard-style conditions on a set-valued tableau on `invSet τ`:
every box is nonempty, and labels weakly decrease along the order `≼`. -/
structure SetValuedTableau_prop {τ : AspPerm} {n : ℕ}
    (T : ↥(invSet τ) → Finset (Fin n)) : Prop where
  nonempty : ∀ p, (T p).Nonempty
  weak :
    ∀ {p q : ↥(invSet τ)} {i j : Fin n},
      i ∈ T p → j ∈ T q → p.val ≼ q.val → p ≠ q → j ≤ i

/-- A set-valued tableau on `invSet τ` with symbols `1, ..., n`. -/
def SetValuedTableau (τ : AspPerm) (n : ℕ) : Type :=
  {T : ↥(invSet τ) → Finset (Fin n) // SetValuedTableau_prop (τ := τ) T}

/-- The compatibility conditions on a label chain: the labeled box sets cover
`invSet τ`, and earlier labels are separated from later ones. -/
structure LabelChain_prop {τ : AspPerm} {n : ℕ}
    (C : Fin n → Set (ℤ × ℤ)) : Prop where
  cover : ∀ p, p ∈ invSet τ ↔ ∃ i, p ∈ C i
  sep :
    ∀ {i j : Fin n}, i < j → ∀ p ∈ C i, ∀ q ∈ C j, p ≼ q → p = q

/-- A fixed-length chain of subsets of `invSet τ`, indexed by the symbols
`1, ..., n`. -/
def LabelChain (τ : AspPerm) (n : ℕ) : Type :=
  {C : Fin n → Set (ℤ × ℤ) // LabelChain_prop (τ := τ) C}

variable {τ : AspPerm} {n : ℕ}

/-- Convert a tableau to the corresponding family of label sets. -/
def labelChainOfTableau (T : SetValuedTableau τ n) : LabelChain τ n := by
  refine ⟨fun i p => ∃ hp : p ∈ invSet τ, i ∈ T.1 ⟨p, hp⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    constructor
    · intro hp
      rcases T.2.nonempty ⟨p, hp⟩ with ⟨i, hi⟩
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp⟩
      exact hp.1
  · intro i j hij p hp q hq hpq
    by_cases hEq : p = q
    · exact hEq
    · rcases hp with ⟨hpτ, hip⟩
      rcases hq with ⟨hqτ, hjq⟩
      have hneq : (⟨p, hpτ⟩ : ↥(invSet τ)) ≠ ⟨q, hqτ⟩ := by
        simp_all
      exfalso
      exact (not_le_of_gt hij) (T.2.weak hip hjq hpq hneq)

/-- Convert a fixed-length chain of label sets to the corresponding tableau. -/
noncomputable def tableauOfLabelChain (C : LabelChain τ n) :
    SetValuedTableau τ n := by
  classical
  refine ⟨fun p => Finset.univ.filter fun i => p.1 ∈ C.1 i, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    rcases (C.2.cover p.1).mp p.2 with ⟨i, hi⟩
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, hi, and_self]⟩
  · intro p q i j hi hj hpq hneq
    have hpC : p.1 ∈ C.1 i := by simpa using hi
    have hqC : q.1 ∈ C.1 j := by simpa using hj
    by_cases hlt : i < j
    · have hpq_eq : p.1 = q.1 := C.2.sep hlt p.1 hpC q.1 hqC hpq
      exfalso
      apply hneq
      apply Subtype.ext
      exact hpq_eq
    · exact le_of_not_gt hlt

lemma mem_labelChainOfTableau_iff (T : SetValuedTableau τ n)
    (p : ↥(invSet τ)) (i : Fin n) :
    p.1 ∈ (labelChainOfTableau T).1 i ↔ i ∈ T.1 p := by
  constructor
  · rintro ⟨hp, hi⟩
    simp_all
  · intro hi
    exact ⟨p.2, hi⟩

lemma mem_labelChainOfTableau_tableauOfLabelChain_iff (C : LabelChain τ n)
    (p : ℤ × ℤ) (i : Fin n) :
    p ∈ (labelChainOfTableau (tableauOfLabelChain C)).1 i ↔ p ∈ C.1 i := by
  constructor
  · rintro ⟨hp, hi⟩
    simpa [tableauOfLabelChain] using hi
  · intro hp
    have hpτ : p ∈ invSet τ := (C.2.cover p).mpr ⟨i, hp⟩
    exact ⟨hpτ, by simp only [tableauOfLabelChain, Finset.mem_filter,
      Finset.mem_univ, hp, and_self]⟩

/-- The tableau reconstructed from the label-chain of `T` is `T` itself. -/
lemma tableauOfLabelChain_labelChainOfTableau (T : SetValuedTableau τ n) :
    tableauOfLabelChain (labelChainOfTableau T) = T := by
  exact Subtype.ext (by
    funext p
    apply Finset.ext
    intro i
    calc
      i ∈ (tableauOfLabelChain (labelChainOfTableau T)).1 p
        ↔ p.1 ∈ (labelChainOfTableau T).1 i := by
            simp only [tableauOfLabelChain, Finset.mem_filter, Finset.mem_univ, true_and]
      _ ↔ i ∈ T.1 p := mem_labelChainOfTableau_iff T p i)

/-- The label-chain reconstructed from the tableau of `C` is `C` itself. -/
lemma labelChainOfTableau_tableauOfLabelChain (C : LabelChain τ n) :
    labelChainOfTableau (tableauOfLabelChain C) = C := by
  exact Subtype.ext (by
    funext i
    ext p
    exact mem_labelChainOfTableau_tableauOfLabelChain_iff C p i)

/-- Set-valued tableaux on `invSet τ` with labels `1, ..., n` are equivalent
to fixed-length label chains. -/
noncomputable def setValuedTableauEquivLabelChain (τ : AspPerm) (n : ℕ) :
    SetValuedTableau τ n ≃ LabelChain τ n where
  toFun := labelChainOfTableau
  invFun := tableauOfLabelChain
  left_inv := tableauOfLabelChain_labelChainOfTableau
  right_inv := labelChainOfTableau_tableauOfLabelChain

end SetValuedTableaux

/-! ### Prescribed chi data

Fix a list of shifts. This section refines the chain/Hecke-factorization
correspondence by keeping track of the individual `χ`-values of the factors,
yielding a tableau model for factorizations with prescribed `χ`-list. -/

section FixedChi

variable {τ : AspPerm} {n : ℕ}

/-- The list of shifts of the factors in a Hecke factorization, in order. -/
noncomputable def chiList (A : HeckeFactorization τ) : List ℤ :=
  A.val.map AspPerm.χ

/-- The ordered list of shifts in a shifted chain. -/
def chainChiList (C : PChain τ) : List ℤ :=
  C.val.map Prod.snd

/-- Shifted chains of fixed length with prescribed shift list. -/
def FixedChiPChain (τ : AspPerm) (n : ℕ) (χs : Fin n → ℤ) : Type :=
  {C : PChain τ // C.val.length = n ∧ chainChiList C = List.ofFn χs}

/-- The subtype of Hecke factorizations of `τ` of length `n` whose ordered list
of shifts is `List.ofFn χs`. -/
def FixedChiHeckeFactorization (τ : AspPerm) (n : ℕ) (χs : Fin n → ℤ) : Type :=
  {A : HeckeFactorization τ // A.val.length = n ∧ chiList A = List.ofFn χs}

lemma chiSum_eq_sum_map_snd (L : List (Set (ℤ × ℤ) × ℤ)) :
    chiSum L = (L.map Prod.snd).sum := by
  induction L with
  | nil =>
      simp only [chiSum, List.map_nil, List.sum_nil]
  | cons head tail ih =>
      simp only [chiSum, ih, List.map_cons, List.sum_cons]

lemma mem_boxUnion_iff_exists_mem {L : List (Set (ℤ × ℤ) × ℤ)} {p : ℤ × ℤ} :
    p ∈ boxUnion L ↔ ∃ x ∈ L, p ∈ x.1 := by
  induction L with
  | nil =>
      simp only [boxUnion, Set.mem_empty_iff_false, List.not_mem_nil, false_and, exists_const]
  | cons head tail ih =>
      simp only [boxUnion, Set.mem_union, ih, Prod.exists, exists_and_right,
        List.mem_cons, exists_eq_or_imp]

lemma mem_boxUnion_iff_exists_index {L : List (Set (ℤ × ℤ) × ℤ)} {p : ℤ × ℤ} :
    p ∈ boxUnion L ↔ ∃ i, ∃ h : i < L.length, p ∈ (L[i]'h).1 := by
  rw [mem_boxUnion_iff_exists_mem]
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases List.mem_iff_getElem.mp hx with ⟨i, h, rfl⟩
    exact ⟨i, h, hp⟩
  · rintro ⟨i, h, hp⟩
    exact ⟨L[i]'h, List.getElem_mem h, hp⟩

lemma isChain_of_sep_ofFn (A : Fin n → Set (ℤ × ℤ)) (χs : Fin n → ℤ)
    (hsep : ∀ {i j : Fin n}, i < j → ∀ p ∈ A i, ∀ q ∈ A j, p ≼ q → p = q) :
    isChain (List.ofFn fun i => (A i, χs i)) := by
  induction n with
  | zero => simp only [List.ofFn_zero, isChain]
  | succ n ih =>
      have hfun :
          (fun i : Fin (n + 1) => (A i, χs i)) =
            Fin.cons (A 0, χs 0) (fun i : Fin n => (A i.succ, χs i.succ)) := by
        funext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [hfun, List.ofFn_cons]
      constructor
      · intro p hp q hq hpq
        rcases (mem_boxUnion_iff_exists_mem.mp hq) with ⟨x, hx, hqx⟩
        rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
        exact hsep (by simp) p hp q hqx hpq
      · apply ih
        intro i j hij p hp q hq hpq
        exact hsep (by simpa using hij) p hp q hq hpq

lemma eq_of_isChain_getElem {L : List (Set (ℤ × ℤ) × ℤ)} (hChain : isChain L) :
    ∀ {i j : ℕ} (hi : i < L.length) (hj : j < L.length), i < j →
      ∀ p ∈ (L[i]'hi).1, ∀ q ∈ (L[j]'hj).1, p ≼ q → p = q := by
  induction L with
  | nil =>
      simp_all
  | cons head tail ih =>
      intro i j hi hj hij p hp q hq hpq
      rcases hChain with ⟨hLink, hTail⟩
      cases i with
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              have hq' : q ∈ boxUnion tail := by
                rw [mem_boxUnion_iff_exists_index]
                exact ⟨j, Nat.succ_lt_succ_iff.mp hj, hq⟩
              exact hLink p hp q hq' hpq
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              exact ih hTail
                (Nat.succ_lt_succ_iff.mp hi)
                (Nat.succ_lt_succ_iff.mp hj)
                (by omega) p hp q hq hpq

/-- Convert a label chain with prescribed shifts to a shifted chain. -/
noncomputable def pChainOfLabelChain (χs : Fin n → ℤ)
    (hχs : (List.ofFn χs).sum = τ.χ) (C : LabelChain τ n) : PChain τ := by
  refine ⟨List.ofFn fun i => (C.1 i, χs i), ?_⟩
  constructor
  · apply isChain_of_sep_ofFn
    intro i j hij p hp q hq hpq
    exact C.2.sep hij p hp q hq hpq
  constructor
  · ext p
    rw [mem_boxUnion_iff_exists_mem]
    constructor
    · rintro ⟨x, hx, hp⟩
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      exact (C.2.cover p).mpr ⟨i, hp⟩
    · intro hp
      rcases (C.2.cover p).mp hp with ⟨i, hi⟩
      exact ⟨(C.1 i, χs i), List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  · calc
      chiSum (List.ofFn fun i => (C.1 i, χs i))
        = (List.map Prod.snd (List.ofFn fun i => (C.1 i, χs i))).sum := by
            simpa using chiSum_eq_sum_map_snd (List.ofFn fun i => (C.1 i, χs i))
      _ = (List.ofFn χs).sum := by
            rw [List.map_ofFn]
            simp only [Function.comp_def]
      _ = τ.χ := hχs

/-- Convert a label chain to a fixed-shift shifted chain. -/
noncomputable def fixedChiPChainOfLabelChain (χs : Fin n → ℤ)
    (hχs : (List.ofFn χs).sum = τ.χ) (C : LabelChain τ n) :
    FixedChiPChain τ n χs :=
  ⟨pChainOfLabelChain χs hχs C, by
    constructor
    · simp only [pChainOfLabelChain, List.length_ofFn]
    · rw [chainChiList, pChainOfLabelChain, List.map_ofFn]
      simp only [Function.comp_def]⟩

/-- Convert a fixed-shift shifted chain to a label chain. -/
noncomputable def labelChainOfFixedChiPChain {χs : Fin n → ℤ}
    (C : FixedChiPChain τ n χs) :
    LabelChain τ n := by
  have hlen : C.1.val.length = n := C.2.1
  refine ⟨fun i => (C.1.val[i.1]'(by omega)).1, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    constructor
    · intro hp
      rw [← C.1.prop.2.1] at hp
      rcases (mem_boxUnion_iff_exists_index.mp hp) with ⟨i, hi, hp⟩
      exact ⟨⟨i, by omega⟩, by simpa using hp⟩
    · rintro ⟨i, hi⟩
      rw [← C.1.prop.2.1]
      exact mem_boxUnion_iff_exists_index.mpr ⟨i.1, by omega, by simpa using hi⟩
  · intro i j hij p hp q hq hpq
    exact eq_of_isChain_getElem C.1.prop.1
      (by omega) (by omega) hij
      p (by simpa using hp) q (by simpa using hq) hpq

/-- Equivalence between label chains and fixed-shift shifted chains. -/
noncomputable def labelChainEquivFixedChiPChain (χs : Fin n → ℤ)
    (hχs : (List.ofFn χs).sum = τ.χ) :
    LabelChain τ n ≃ FixedChiPChain τ n χs where
  toFun := fixedChiPChainOfLabelChain χs hχs
  invFun := labelChainOfFixedChiPChain
  left_inv C := by
    apply Subtype.ext
    funext i
    ext p
    simp only [labelChainOfFixedChiPChain, fixedChiPChainOfLabelChain,
      pChainOfLabelChain, List.getElem_ofFn, Fin.eta]
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    apply List.ext_getElem
    · calc
        (fixedChiPChainOfLabelChain χs hχs (labelChainOfFixedChiPChain C)).1.val.length = n := by
          simp only [fixedChiPChainOfLabelChain, pChainOfLabelChain, List.length_ofFn]
        _ = C.1.val.length := C.2.1.symm
    · intro i hi1 hi2
      have hχi : (C.1.val[i]'hi2).2 = χs ⟨i, by simpa [C.2.1] using hi2⟩ := by
        have h := congrArg (fun l => l[i]?) C.2.2
        have hi : i < n := by simpa [C.2.1] using hi2
        simpa [chainChiList, hi2, hi] using h
      apply Prod.ext
      · simp only [fixedChiPChainOfLabelChain, pChainOfLabelChain,
          labelChainOfFixedChiPChain, List.getElem_ofFn]
      · simpa [fixedChiPChainOfLabelChain, pChainOfLabelChain,
          labelChainOfFixedChiPChain, List.getElem_ofFn, C.2.1] using hχi.symm

lemma length_LSet_of_LPerm (L : List AspPerm) :
    (lSetOfLPerm L).length = L.length := by
  induction L with
  | nil =>
      simp only [lSetOfLPerm, List.length_nil]
  | cons α tail ih =>
      simp only [lSetOfLPerm, List.foldr_cons, List.length_cons, ih]

lemma chainChiList_LSet_of_LPerm (L : List AspPerm) :
    (lSetOfLPerm L).map Prod.snd = L.map AspPerm.χ := by
  induction L with
  | nil =>
      simp only [lSetOfLPerm, List.map_nil]
  | cons α tail ih =>
      simp only [lSetOfLPerm, List.foldr_cons, List.map_cons, ih]

lemma length_PChain_of_HF (h_321a : is321a τ) (A : HeckeFactorization τ) :
    (pChainOfHf h_321a A).val.length = A.val.length := by
  simpa [pChainOfHf] using length_LSet_of_LPerm A.val

lemma chainChiList_PChain_of_HF (h_321a : is321a τ) (A : HeckeFactorization τ) :
    chainChiList (pChainOfHf h_321a A) = chiList A := by
  simpa [pChainOfHf, chainChiList, chiList] using chainChiList_LSet_of_LPerm A.val



/-- Equivalence between fixed-shift Hecke factorizations and fixed-shift chains. -/
noncomputable def fixedChiHeckeFactorizationEquivFixedChiPChain
    (h_321a : is321a τ) (χs : Fin n → ℤ) :
    FixedChiHeckeFactorization τ n χs ≃ FixedChiPChain τ n χs :=
  Equiv.subtypeEquiv (hfEquivPChain h_321a) (by
    intro A
    change (A.val.length = n ∧ chiList A = List.ofFn χs) ↔
      ((pChainOfHf h_321a A).val.length = n ∧
        chainChiList (pChainOfHf h_321a A) = List.ofFn χs)
    simp only [length_PChain_of_HF h_321a A, chainChiList_PChain_of_HF h_321a A])

/-- A label chain is equivalent to a Hecke factorization with prescribed
ordered shift data. -/
noncomputable def labelChainEquivFixedChiHeckeFactorization
    (h_321a : is321a τ) (χs : Fin n → ℤ)
    (hχs : (List.ofFn χs).sum = τ.χ) :
    LabelChain τ n ≃ FixedChiHeckeFactorization τ n χs :=
  (labelChainEquivFixedChiPChain χs hχs).trans
    (fixedChiHeckeFactorizationEquivFixedChiPChain h_321a χs).symm

/-- Equivalence between set-valued tableaux and fixed-shift Hecke factorizations. -/
noncomputable def setValuedTableauEquivFixedChiHeckeFactorization
    (h_321a : is321a τ) (χs : Fin n → ℤ)
    (hχs : (List.ofFn χs).sum = τ.χ) :
    SetValuedTableau τ n ≃ FixedChiHeckeFactorization τ n χs :=
  (setValuedTableauEquivLabelChain τ n).trans
    (labelChainEquivFixedChiHeckeFactorization h_321a χs hχs)

/-- For a prescribed length-`n` list of shifts summing to `τ.χ`, set-valued
tableaux on `invSet τ` are equivalent to Hecke factorizations of `τ` with
exactly that ordered `χ`-list. -/
noncomputable def setValuedTableauEquivHeckeFactorization
    (h_321a : is321a τ) (χs : List ℤ)
    (h_len : χs.length = n) (h_sum : χs.sum = τ.χ) :
    SetValuedTableau τ n ≃ {A : HeckeFactorization τ // A.val.length = n ∧ chiList A = χs} := by
  let χf : Fin n → ℤ := fun i => χs[i.1]'(by omega)
  have h_ofFn : List.ofFn χf = χs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, h_len]
    · intro i hi1 hi2
      rw [List.getElem_ofFn]
  have h_sum' : (List.ofFn χf).sum = τ.χ := by
    simpa [h_ofFn] using h_sum
  simpa [FixedChiHeckeFactorization, h_ofFn] using
    setValuedTableauEquivFixedChiHeckeFactorization h_321a χf h_sum'

end FixedChi
end Tableaux

end LeanPool.DemazureProduct
