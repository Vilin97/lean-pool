/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

/-!
# Hecke Rings: Multiplication

Shimura's multiplicity `heckeMultiplicity`, the multiplication finsupp `m`, the `Mul` instance
on `𝕋 P ℤ`,
and the `NonUnitalNonAssocSemiring` instance. Proves that `HeckeCoset.one` is the identity element.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G)

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

/-- Two `HeckeCoset` elements are equal iff their `toSet`s are equal. -/
lemma HeckeCoset_ext_toSet {D₁ D₂ : HeckeCoset P}
    (h : HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂) : D₁ = D₂ := by
  revert h
  exact Quotient.ind₂ (motive := fun D₁ D₂ =>
    HeckeCoset.toSet D₁ = HeckeCoset.toSet D₂ → D₁ = D₂) (fun g₁ g₂ h => by
    simp only [HeckeCoset.toSet_mk] at h
    exact Quotient.sound h) D₁ D₂

/-- The stabilizer quotient for the identity double coset is trivial. -/
lemma decompQuot_T_one_eq_top :
    (ConjAct.toConjAct ((HeckeCoset.one P).rep : G) • P.H).subgroupOf P.H =
    ⊤ := by
  have h := HeckeCoset.one_rep_mem_H P; rw [Subgroup.subgroupOf_eq_top]
  intro x hx; rw [← @SetLike.mem_coe]; simp only [Subgroup.coe_pointwise_smul]
  rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h,
    Subgroup.subgroup_mul_singleton (by simp [h])]; exact hx

/-- The decomposition quotient for `HeckeCoset.one` is nonempty. -/
lemma one_in_decompQuot_T_one :
    Nonempty (decompQuot P (HeckeCoset.one P).rep) :=
  ⟨(1 : P.H)⟩

/-- The decomposition quotient for `HeckeCoset.one` is a subsingleton. -/
lemma subsingleton_decompQuot_T_one :
    Subsingleton (decompQuot P (HeckeCoset.one P).rep) := by
  unfold decompQuot; rw [decompQuot_T_one_eq_top]
  exact QuotientGroup.subsingleton_quotient_top

private lemma self_mem_singleton_mul (a : G) : a ∈ {a} * (H : Set G) := by simp

private lemma conjAct_mem_of_leftCoset_eq (d : Δ) (h h' : H)
    (hyp : {(h : G)} * {(d : G)} * (H : Set G) =
      {(h' : G)} * {(d : G)} * (H : Set G)) :
    (h')⁻¹ * h ∈ (ConjAct.toConjAct (d : G) • H).subgroupOf H := by
  have h_mem_lhs : (h : G) * (d : G) ∈ {(h : G)} * {(d : G)} * (H : Set G) := by
    rw [Set.singleton_mul_singleton]
    exact ⟨(h : G) * (d : G), Set.mem_singleton _, 1, H.one_mem, by simp⟩
  rw [hyp, Set.singleton_mul_singleton] at h_mem_lhs
  obtain ⟨_, rfl, k, hk, hkk⟩ := h_mem_lhs
  have hkk' : ↑h' * ↑d * k = ↑h * ↑d := hkk
  have key : (h' : G)⁻¹ * (h : G) = (d : G) * k * (d : G)⁻¹ := by
    apply mul_right_cancel (b := (d : G))
    rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    apply mul_left_cancel (a := (h' : G))
    rw [mul_inv_cancel_left, ← mul_assoc]
    exact hkk'.symm
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rw [inv_inv, key]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]; exact hk

/-- Distinct elements of `decompQuot` give distinct left cosets. -/
lemma decompQuot_coset_diff (g : P.Δ)
    (i j : decompQuot P g) (hij : i ≠ j) :
  {((i.out : G) * (g : G))} * (P.H : Set G) ≠
    {((j.out : G) * (g : G))} * (P.H : Set G) := by
  intro h
  simp_rw [← Set.singleton_mul_singleton] at h
  have := conjAct_mem_of_leftCoset_eq P.H P.Δ g i.out j.out h
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at this
  simp only [Quotient.out_eq'] at this
  exact hij this.symm

/-- Two left cosets that are not disjoint must be equal. -/
lemma leftCoset_eq_of_not_disjoint (f g : G)
    (h : ¬ Disjoint (g • (H : Set G)) (f • H)) :
    {g} * (H : Set G) = {f} * H := by
  simp_rw [← Set.singleton_smul] at *; rw [@not_disjoint_iff] at h
  obtain ⟨a, ha, ha2⟩ := h
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage,
    SetLike.mem_coe] at ha ha2
  refine Set.ext ?intro.intro.h; intro Y
  simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  simp_rw [← @QuotientGroup.eq] at *; rw [← ha] at ha2; rw [ha2]

private lemma singleton_mul_subset_mul (g : G) (T S : Set G) (h : g ∈ S) :
    {g} * T ⊆ S * T := mul_subset_mul_right (singleton_subset_iff.mpr h)

private lemma leftCoset_exists (g : P.Δ) : ∃ (i : decompQuot P g),
    {(g : G)} * (P.H : Set G) =
      {(i.out : G)} * {(g : G)} * P.H := by
  have hc : HeckeCoset.toSet (⟦g⟧ : HeckeCoset P) =
    DoubleCoset.doubleCoset (g : G) P.H P.H := HeckeCoset.toSet_mk g
  rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hc
  have h1 : {(g : G)} * (P.H : Set G) ⊆
      HeckeCoset.toSet (⟦g⟧ : HeckeCoset P) := by
    rw [HeckeCoset.toSet_mk]
    intro i hi
    simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at *
    rw [mem_doubleCoset]
    use 1
    simp only [SetLike.mem_coe, one_mem, one_mul, true_and]
    use (g : G)⁻¹ * i
    simp [hi]
  have hr := hc.le
  have h3 := le_trans h1 hr
  simp only [le_eq_subset] at h3
  have h4 : (g : G) ∈ {(g : G)} * (P.H : Set G) := by
    simp [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  have h45 := h3 h4
  simp only [mem_iUnion] at h45
  obtain ⟨i, hi⟩ := h45
  use i
  rw [smul_eq_singleton_mul] at hi
  have h6 := singleton_mul_subset_mul _ P.H _ hi
  conv at h6 =>
    enter [2]
    rw [mul_assoc, coe_mul_coe]
  rw [Set.singleton_mul_singleton]
  apply leftCoset_eq_of_not_disjoint
  apply Set.Nonempty.not_disjoint
  simp_rw [smul_eq_singleton_mul]
  have := Set.inter_eq_self_of_subset_left h6
  have ht := nonempty_of_mem h4
  rw [← this] at ht
  convert ht

private lemma leftCoset_exists_unique (g : P.Δ) :
    ∃! (i : decompQuot P g),
      {(g : G)} * (P.H : Set G) =
        {(i.out : G) * (g : G)} * P.H := by
  obtain ⟨i, hi⟩ := leftCoset_exists P g
  use i
  rw [Set.singleton_mul_singleton] at hi
  simp only [hi, true_and]
  intro j h
  by_contra c
  have := (decompQuot_coset_diff P g j i c).symm
  aesop

private lemma mul_mem_delta (a : H) (g : Δ)
    (h₀ : H.toSubmonoid ≤ Δ) :
    (a : G) * (g : G) ∈ Δ :=
  Submonoid.mul_mem _ (h₀ a.2) g.2

/-- The map sending a pair of coset representatives `(σ_i, τ_j)` to the double coset
of their product `H(σ_i τ_j)H`. -/
noncomputable def mulMap (g₁ g₂ : P.Δ)
    (i : decompQuot P g₁ × decompQuot P g₂) : HeckeCoset P :=
  ⟦⟨i.1.out * g₁ * (i.2.out * g₂),
    Submonoid.mul_mem _ (mul_mem_delta P.H P.Δ i.1.out g₁ P.h₀)
      (mul_mem_delta P.H P.Δ i.2.out g₂ P.h₀)⟩⟧

/-- Shimura's multiplicity (Proposition 3.2): `heckeMultiplicity(g₁, g₂, d)` counts pairs
`(i,j)` such that `σᵢ τⱼ H = ξ H`. -/
noncomputable def heckeMultiplicity (g₁ g₂ d : P.Δ) : ℤ :=
  Nat.card {⟨i, j⟩ : decompQuot P g₁ × decompQuot P g₂ |
    ({(i.out : G) * (g₁ : G)} : Set G) *
      {(j.out : G) * (g₂ : G)} * P.H =
    {(d : G)} * (P.H : Set G)}

/-- The finite set of double cosets appearing in the product `D1 * D2`. -/
noncomputable def mulSupport (g₁ g₂ : P.Δ) : Finset (HeckeCoset P) :=
  Finset.image (mulMap P g₁ g₂) ⊤

/-- If `σ_i τ_j H = ξ H` then the double coset of `σ_i τ_j` equals
that of `ξ`. -/
lemma doubleCoset_eq_of_rightCoset_eq (g₁ g₂ d : P.Δ)
    (p : decompQuot P g₁ × decompQuot P g₂)
    (heq : ({(p.1.out : G) * (g₁ : G)} : Set G) *
      {(p.2.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    mulMap P g₁ g₂ p = (⟦d⟧ : HeckeCoset P) := by
  unfold mulMap
  rw [HeckeCoset.eq_iff]
  have h_mem : (p.1.out : G) * (g₁ : G) *
      ((p.2.out : G) * (g₂ : G))
      ∈ ({(d : G)} : Set G) * (P.H : Set G) := by
    rw [← heq, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, P.H.one_mem, by simp⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_mem
  simp only [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  dsimp only at hprod ⊢
  rw [← hprod]
  exact DoubleCoset.doubleCoset_mul_right_eq_self P ⟨h, hh⟩ _

private lemma mulMap_T_one_eq (g₁ : P.Δ)
    (i : decompQuot P g₁)
    (j : decompQuot P (HeckeCoset.one P).rep) :
    mulMap P g₁ (HeckeCoset.one P).rep (i, j) = (⟦g₁⟧ : HeckeCoset P) := by
  unfold mulMap
  rw [HeckeCoset.eq_iff]; dsimp only
  rw [mul_assoc, doset_mul_left_eq_self]
  apply DoubleCoset.doubleCoset_mul_right_eq_self P
    ⟨j.out * (HeckeCoset.one P).rep, by
      apply Subgroup.mul_mem _ (by simp) (HeckeCoset.one_rep_mem_H P)⟩

/-- Left multiplication by a singleton set is cancellative. -/
lemma set_singleton_mul_left_cancel (a : G) {S T : Set G}
    (h : ({a} : Set G) * S = ({a} : Set G) * T) : S = T := by
  ext x; constructor
  · intro hx
    have hax : a * x ∈ ({a} : Set G) * T := by
      rw [← h]; exact Set.mul_mem_mul (Set.mem_singleton a) hx
    obtain ⟨b, hb, y, hy, heq⟩ := hax
    rw [Set.mem_singleton_iff.mp hb] at heq; exact mul_left_cancel heq ▸ hy
  · intro hx
    have hax : a * x ∈ ({a} : Set G) * S := by
      rw [h]; exact Set.mul_mem_mul (Set.mem_singleton a) hx
    obtain ⟨b, hb, y, hy, heq⟩ := hax
    rw [Set.mem_singleton_iff.mp hb] at heq; exact mul_left_cancel heq ▸ hy

/-- When the first-component representatives agree, the second-component
    representatives must also agree (by left-cancellation on the common prefix). -/
lemma decompQuot_snd_eq_of_fst_eq (g₁ g₂ d : P.Δ)
    (i : decompQuot P g₁) (j₁ j₂ : decompQuot P g₂)
    (h₁ : ({(i.out : G) * (g₁ : G)} : Set G) *
        {(j₁.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G))
    (h₂ : ({(i.out : G) * (g₁ : G)} : Set G) *
        {(j₂.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    j₁ = j₂ := by
  by_contra hne
  exact decompQuot_coset_diff P g₂ j₁ j₂ hne
    (set_singleton_mul_left_cancel _ (by
      have := h₁.trans h₂.symm; rwa [mul_assoc, mul_assoc] at this))

/-- When `j.out * g₂ ∈ H`, the second factor collapses and
    first-component injectivity follows from coset disjointness. -/
lemma decompQuot_fst_eq_of_snd_mem_H (g₁ g₂ d : P.Δ)
    (i₁ i₂ : decompQuot P g₁) (j : decompQuot P g₂)
    (hj : (j.out : G) * (g₂ : G) ∈ P.H)
    (h₁ : ({(i₁.out : G) * (g₁ : G)} : Set G) *
        {(j.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G))
    (h₂ : ({(i₂.out : G) * (g₁ : G)} : Set G) *
        {(j.out : G) * (g₂ : G)} * P.H =
      {(d : G)} * (P.H : Set G)) :
    i₁ = i₂ := by
  by_contra hne; apply decompQuot_coset_diff P g₁ i₁ i₂ hne
  simp only [mul_assoc, Subgroup.singleton_mul_subgroup hj] at h₁ h₂
  exact h₁.trans h₂.symm

/-- Right multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal
and `0` elsewhere. -/
lemma heckeMultiplicity_mul_one (g₁ d : P.Δ) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦d⟧ ↔
      heckeMultiplicity P g₁ (HeckeCoset.one P).rep d = 1 := by
  constructor
  · intro h
    have hg₁d : dcRel P g₁ d := (HeckeCoset.eq_iff g₁ d).mp h
    simp only [heckeMultiplicity]; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (HeckeCoset.one P).rep) :=
      subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
      simp only [Set.mem_setOf_eq] at h₁ h₂
      exact Subtype.ext (Prod.ext
        (decompQuot_fst_eq_of_snd_mem_H P g₁ (HeckeCoset.one P).rep d i₁ i₂ j₁
          (Subgroup.mul_mem _ (SetLike.coe_mem j₁.out)
            (HeckeCoset.one_rep_mem_H P)) h₁ h₂)
        rfl)
    · -- Use d (the target representative) instead of g₁
      -- d ∈ Hg₁H since dcRel P g₁ d, and g₁ ∈ HdH
      -- So we can find an element of decompQuot P g₁ that maps d into the right coset
      have hd_in_g₁ : (↑d : G) ∈ doubleCoset (↑g₁ : G) P.H P.H :=
        hg₁d ▸ DoubleCoset.mem_doubleCoset_self P.H P.H _
      rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hd_in_g₁
      simp only [Set.mem_iUnion] at hd_in_g₁
      obtain ⟨k, hk⟩ := hd_in_g₁
      rw [smul_eq_singleton_mul] at hk
      obtain ⟨j₀⟩ := one_in_decompQuot_T_one P
      refine ⟨⟨(k, j₀), ?_⟩⟩
      simp only [Set.mem_setOf_eq]
      have hmem : (j₀.out : G) * ((HeckeCoset.one P).rep : G) ∈ P.H :=
        Subgroup.mul_mem _ (SetLike.coe_mem j₀.out) (HeckeCoset.one_rep_mem_H P)
      rw [mul_assoc, Subgroup.singleton_mul_subgroup hmem]
      -- Now goal is {k.out * g₁} * H = {d} * H
      apply (leftCoset_eq_of_not_disjoint (H := P.H) _ _ _).symm
      rw [not_disjoint_iff]
      refine ⟨↑d, Set.mem_smul_set.mpr ⟨1, P.H.one_mem, by simp⟩, ?_⟩
      rw [Set.mem_smul_set]
      rw [singleton_mul] at hk
      simp only [image_mul_left, mem_preimage, SetLike.mem_coe] at hk
      exact ⟨(↑k.out * (↑g₁ : G))⁻¹ * ↑d, hk,
        show (↑k.out * (↑g₁ : G)) * ((↑k.out * ↑g₁)⁻¹ * ↑d) = ↑d by group⟩
  · intro hm; by_contra hne
    have hg₁d_ne : ¬ dcRel P g₁ d := fun h => hne (Quotient.sound h)
    have : heckeMultiplicity P g₁ (HeckeCoset.one P).rep d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero,
        isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      apply hne
      have h1 := doubleCoset_eq_of_rightCoset_eq P g₁ (HeckeCoset.one P).rep d (i, j) heq
      have h2 := mulMap_T_one_eq P g₁ i j
      exact h2.symm.trans h1
    omega

private lemma mulMap_one_T_eq (g₁ : P.Δ)
    (i : decompQuot P (HeckeCoset.one P).rep)
    (j : decompQuot P g₁) :
    mulMap P (HeckeCoset.one P).rep g₁ (i, j) = (⟦g₁⟧ : HeckeCoset P) := by
  unfold mulMap
  rw [HeckeCoset.eq_iff]; dsimp only
  rw [mul_assoc]
  simp_rw [doset_mul_left_eq_self,
    doset_mul_left_eq_self P
      ⟨(HeckeCoset.one P).rep, HeckeCoset.one_rep_mem_H P⟩,
    doset_mul_left_eq_self]

/-- The multiplicity `heckeMultiplicity` is nonzero for double cosets in the
multiplication support. -/
lemma heckeMultiplicity_pos_of_mem_mulSupport (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∈ mulSupport P g₁ g₂) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) ≠ 0 := by
  rw [heckeMultiplicity]; simp only [ne_eq, Nat.cast_eq_zero]
  rw [Nat.card_eq_zero, not_or, not_isEmpty_iff]
  refine ⟨?_, not_infinite_iff_finite.mpr inferInstance⟩
  rw [mulSupport] at hd
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists] at hd
  obtain ⟨i₀, j₀, hmap⟩ := hd
  -- hmap : mulMap P g₁ g₂ (i₀, j₀) = d
  -- So ⟦⟨i₀.out * g₁ * (j₀.out * g₂), _⟩⟧ = d, i.e., same double coset as d
  -- Which means: doubleCoset (i₀.out * g₁ * (j₀.out * g₂)) H H = doubleCoset (rep d) H H
  have hset_eq : DoubleCoset.doubleCoset
      ((↑i₀.out : G) * (↑g₁ : G) * ((↑j₀.out : G) * (↑g₂ : G)))
      (P.H : Set G) (P.H : Set G) =
      DoubleCoset.doubleCoset (HeckeCoset.rep d : G) P.H P.H := by
    have h1 : mulMap P g₁ g₂ (i₀, j₀) = (⟦HeckeCoset.rep d⟧ : HeckeCoset P) :=
      hmap.trans (Quotient.out_eq d).symm
    exact (HeckeCoset.eq_iff _ _).mp h1
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq hset_eq)
  set α := (↑g₁ : G) with hα_def
  set β := (↑g₂ : G) with hβ_def
  set K₁ := (ConjAct.toConjAct α • P.H).subgroupOf P.H
  set i' : decompQuot P g₁ := ⟦⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩⟧
  obtain ⟨κ₁, hκ₁_eq⟩ := QuotientGroup.mk_out_eq_mul K₁
    ⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩
  have hκ₁_conj : α⁻¹ * (κ₁.val : G) * α ∈ P.H := by
    have := κ₁.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  set K₂ := (ConjAct.toConjAct β • P.H).subgroupOf P.H
  set j' : decompQuot P g₂ := ⟦⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
    P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩⟧
  obtain ⟨κ₂, hκ₂_eq⟩ := QuotientGroup.mk_out_eq_mul K₂
    ⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
      P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩
  have hκ₂_conj : β⁻¹ * (κ₂.val : G) * β ∈ P.H := by
    have := κ₂.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  have hi'_coe : (↑i'.out : G) = h₁ * ↑i₀.out * (κ₁.val : G) := by
    have h := hκ₁_eq; apply_fun (↑· : ↥P.H → G) at h
    simp only [Subgroup.coe_mul] at h; exact h
  have hj'_coe : (↑j'.out : G) =
      (α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out * (κ₂.val : G) := by
    have h := hκ₂_eq; apply_fun (↑· : ↥P.H → G) at h
    simp only [Subgroup.coe_mul] at h; exact h
  refine ⟨⟨(i', j'), ?_⟩⟩
  simp only [Set.mem_setOf_eq]
  have hprod_main : (↑i'.out : G) * α * ((↑j'.out : G) * β) =
      (HeckeCoset.rep d : G) * (h₂⁻¹ * (β⁻¹ * (κ₂.val : G) * β)) := by
    rw [hi'_coe, hj'_coe]
    have hprod' : (HeckeCoset.rep d : G) =
      h₁ * (↑i₀.out * α * (↑j₀.out * β)) * h₂ := hprod
    rw [hprod']; group
  rw [Set.singleton_mul_singleton, hprod_main, ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup (P.H.mul_mem (P.H.inv_mem hh₂) hκ₂_conj)]

/-- The multiplicity `heckeMultiplicity` is zero for double cosets outside the
multiplication support. -/
lemma heckeMultiplicity_eq_zero_of_nmem_mulSupport (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∉ mulSupport P g₁ g₂) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero,
    isEmpty_subtype]; left
  rintro ⟨i, j⟩ hij
  apply hd
  rw [mulSupport]
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists]
  exact ⟨i, j, (doubleCoset_eq_of_rightCoset_eq P g₁ g₂ (HeckeCoset.rep d)
    (i, j) hij).trans (show (⟦HeckeCoset.rep d⟧ : HeckeCoset P) = d
      from Quotient.out_eq d)⟩

/-- A multiplicity that is both at most one and positive must equal one. -/
lemma heckeMultiplicity_eq_one_of_le_one_and_pos (g₁ g₂ d : P.Δ)
    (h_le : heckeMultiplicity P g₁ g₂ d ≤ 1)
    (h_pos : 0 < heckeMultiplicity P g₁ g₂ d) :
    heckeMultiplicity P g₁ g₂ d = 1 := by omega

/-- The multiplicity `heckeMultiplicity` is positive for double cosets in the
multiplication support. -/
lemma heckeMultiplicity_pos_of_mem (g₁ g₂ : P.Δ) (d : HeckeCoset P)
    (hd : d ∈ mulSupport P g₁ g₂) :
    0 < heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) := by
  have h_ne := heckeMultiplicity_pos_of_mem_mulSupport P g₁ g₂ d hd
  have : (0 : ℤ) ≤ heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d) := by
    simp only [heckeMultiplicity]; exact Nat.cast_nonneg _
  omega

/-- If `h₁ * g₁ * (h₂ * g₂) ∈ HdH` (with `h₁, h₂ ∈ H`), then `⟦d⟧ ∈ mulSupport g₁ g₂`.
    Avoids manual construction of decomposition quotient elements. -/
lemma mem_mulSupport_of_product_mem (g₁ g₂ d : P.Δ) (h₁ h₂ : P.H)
    (hmem : (h₁ : G) * g₁ * ((h₂ : G) * g₂) ∈
      DoubleCoset.doubleCoset (d : G) P.H P.H) :
    (⟦d⟧ : HeckeCoset P) ∈ mulSupport P g₁ g₂ := by
  rw [mulSupport]; simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  refine ⟨⟦⟨h₁, h₁.2⟩⟧, ⟦⟨h₂, h₂.2⟩⟧, ?_⟩
  -- mulMap returns ⟦⟨i.out * g₁ * (j.out * g₂)⟩⟧; need = ⟦d⟧ (double coset equality)
  unfold mulMap; rw [HeckeCoset.eq_iff]; dsimp only
  obtain ⟨n₁, hn₁⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₁ : G) • P.H).subgroupOf P.H) ⟨(h₁ : G), h₁.2⟩
  obtain ⟨n₂, hn₂⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H) ⟨(h₂ : G), h₂.2⟩
  have hi : ((⟦⟨(h₁ : G), h₁.2⟩⟧ : decompQuot P g₁).out : G) = h₁ * n₁ := by
    have := congr_arg (Subtype.val : P.H → G) hn₁; simpa [Subgroup.coe_mul]
  have hj : ((⟦⟨(h₂ : G), h₂.2⟩⟧ : decompQuot P g₂).out : G) = h₂ * n₂ := by
    have := congr_arg (Subtype.val : P.H → G) hn₂; simpa [Subgroup.coe_mul]
  have hn₁c : (g₁ : G)⁻¹ * ↑n₁ * g₁ ∈ P.H := by
    have := n₁.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this; simpa [ConjAct.ofConjAct_toConjAct]
  have hn₂c : (g₂ : G)⁻¹ * ↑n₂ * g₂ ∈ P.H := by
    have := n₂.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this; simpa [ConjAct.ofConjAct_toConjAct]
  rw [hi, hj]
  -- Goal: H((h₁↑↑n₁)g₁((h₂↑↑n₂)g₂))H = HdH
  -- Use doubleCoset_eq_of_mem: show the product ∈ HdH
  apply HeckeCoset.doubleCoset_eq_of_mem
  -- (h₁n₁)g₁(h₂n₂g₂) = (h₁n₁h₁⁻¹ * a) * d * (b * g₂⁻¹n₂g₂) with both in H
  rw [DoubleCoset.mem_doubleCoset] at hmem; obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨(h₁ : G) * ↑↑n₁ * (h₁ : G)⁻¹ * a,
    P.H.mul_mem (P.H.mul_mem (P.H.mul_mem h₁.2 (SetLike.coe_mem n₁.val)) (P.H.inv_mem h₁.2)) ha,
    b * ((g₂ : G)⁻¹ * ↑↑n₂ * g₂),
    P.H.mul_mem hb hn₂c,
    by
      have key : (↑h₁ * ↑↑n₁ * (↑h₁ : G)⁻¹ * a) * ↑d * (b * ((↑g₂ : G)⁻¹ * ↑↑n₂ * ↑g₂)) =
        (↑h₁ * ↑↑n₁) * (↑g₁ : G) * ((↑h₂ * ↑↑n₂) * ↑g₂) := by
          have h := hab
          calc (↑h₁ * ↑↑n₁ * (↑h₁ : G)⁻¹ * a) * ↑d * (b * ((↑g₂ : G)⁻¹ * ↑↑n₂ * ↑g₂))
              = ↑h₁ * ↑↑n₁ * (↑h₁)⁻¹ * (a * ↑d * b) * ((↑g₂)⁻¹ * ↑↑n₂ * ↑g₂) := by group
            _ = ↑h₁ * ↑↑n₁ * (↑h₁)⁻¹ * (↑h₁ * ↑g₁ * (↑h₂ * ↑g₂)) *
                ((↑g₂)⁻¹ * ↑↑n₂ * ↑g₂) := by rw [h]
            _ = (↑h₁ * ↑↑n₁) * ↑g₁ * ((↑h₂ * ↑↑n₂) * ↑g₂) := by group
      exact key.symm⟩

/-- Left multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal
and `0` elsewhere. -/
lemma heckeMultiplicity_one_mul (g₁ d : P.Δ) :
    (⟦g₁⟧ : HeckeCoset P) = ⟦d⟧ ↔
      heckeMultiplicity P (HeckeCoset.one P).rep g₁ d = 1 := by
  constructor
  · intro h
    have hg₁d : dcRel P g₁ d := (HeckeCoset.eq_iff g₁ d).mp h
    simp only [heckeMultiplicity]; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (HeckeCoset.one P).rep) :=
      subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      exact Subtype.ext (Prod.ext rfl
        (decompQuot_snd_eq_of_fst_eq P (HeckeCoset.one P).rep g₁ d i₁ j₁ j₂ h₁ h₂))
    · -- d ∈ Hg₁H, find j' such that d ∈ {j'.out * g₁} * H
      have hd_in : (↑d : G) ∈ doubleCoset (↑g₁ : G) P.H P.H :=
        hg₁d ▸ DoubleCoset.mem_doubleCoset_self P.H P.H _
      rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hd_in
      simp only [Set.mem_iUnion] at hd_in
      obtain ⟨j', hj'⟩ := hd_in
      rw [smul_eq_singleton_mul] at hj'
      rw [singleton_mul] at hj'
      simp only [image_mul_left, mem_preimage, SetLike.mem_coe] at hj'
      -- hj' : (j'.out * g₁)⁻¹ * d ∈ P.H
      -- Pick j₀ := ⟦⟨h₀⁻¹ * j'.out, _⟩⟧ where h₀ = i₀.out * one.rep ∈ H
      obtain ⟨i₀⟩ := one_in_decompQuot_T_one P
      have h₀_mem : (↑i₀.out : G) * ((HeckeCoset.one P).rep : G) ∈ P.H :=
        Subgroup.mul_mem _ (SetLike.coe_mem i₀.out) (HeckeCoset.one_rep_mem_H P)
      set h₀ := ↑i₀.out * ((HeckeCoset.one P).rep : G) with hh₀_def
      set j₀ : decompQuot P g₁ :=
        ⟦⟨h₀⁻¹ * ↑j'.out, P.H.mul_mem (P.H.inv_mem h₀_mem) j'.out.2⟩⟧
      obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct (↑g₁ : G) • P.H).subgroupOf P.H)
        ⟨h₀⁻¹ * ↑j'.out, P.H.mul_mem (P.H.inv_mem h₀_mem) j'.out.2⟩
      have hn_coe : (j₀.out : G) = h₀⁻¹ * ↑j'.out * (n : G) := by
        have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
        simpa [Subgroup.coe_mul] using this
      have hn_conj : (↑g₁ : G)⁻¹ * (n : G) * ↑g₁ ∈ P.H := by
        have := n.2
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ConjAct.smul_def] at this
        simpa [ConjAct.ofConjAct_toConjAct] using this
      exact ⟨⟨(i₀, j₀), by
        simp only [Set.mem_setOf_eq, Set.singleton_mul_singleton]
        apply (leftCoset_eq_of_not_disjoint (H := P.H) _ _ _).symm
        rw [not_disjoint_iff]
        refine ⟨↑d, Set.mem_smul_set.mpr ⟨1, P.H.one_mem, by simp⟩, ?_⟩
        rw [Set.mem_smul_set]
        refine ⟨(h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d, ?_, by
          change (↑i₀.out * (HeckeCoset.one P).rep * (↑j₀.out * (↑g₁ : G))) *
            ((h₀ * ↑j₀.out * ↑g₁)⁻¹ * ↑d) = ↑d
          simp only [hh₀_def]; group⟩
        change (h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d ∈ P.H
        have key : (h₀ * ↑j₀.out * (↑g₁ : G))⁻¹ * ↑d =
            ((↑g₁ : G)⁻¹ * (↑n : G)⁻¹ * ↑g₁) *
            ((↑j'.out * (↑g₁ : G))⁻¹ * ↑d) := by
          rw [hn_coe]; group
        rw [key]
        exact P.H.mul_mem (by convert P.H.inv_mem hn_conj using 1; group) hj'⟩⟩
  · intro hm; by_contra hne
    have : heckeMultiplicity P (HeckeCoset.one P).rep g₁ d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero,
        isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      apply hne
      have h1 := doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P).rep g₁ d (i, j) heq
      have h2 := mulMap_one_T_eq P g₁ i j
      exact h2.symm.trans h1
    omega

/-- The multiplication finsupp: `m(g₁, g₂)` is the formal sum
`Σ_d heckeMultiplicity(g₁, g₂, d) · d`
encoding the product of two double cosets. -/
noncomputable def m (g₁ g₂ : P.Δ) : (HeckeCoset P) →₀ ℤ :=
  ⟨mulSupport P g₁ g₂,
    fun d => heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d),
    fun a =>
      ⟨heckeMultiplicity_pos_of_mem_mulSupport P g₁ g₂ a,
        fun hm => by
          by_contra hemp
          exact hm (heckeMultiplicity_eq_zero_of_nmem_mulSupport P g₁ g₂ a hemp)⟩⟩

/-- The multiplication on the Hecke ring, defined via the multiplicity function `m`. -/
noncomputable instance (P : HeckePair G) : Mul (𝕋 P ℤ) where
  mul f g := Finsupp.sum f fun D1 b₁ =>
    g.sum fun D2 b₂ =>
      b₁ • b₂ • m P (HeckeCoset.rep D1) (HeckeCoset.rep D2)

/-- Multiplication in the Hecke ring unfolds as a double Finsupp sum over multiplicities. -/
lemma mul_def (f g : 𝕋 P ℤ) : f * g = Finsupp.sum f
    (fun D1 b₁ => g.sum fun D2 b₂ =>
      b₁ • b₂ • m P (HeckeCoset.rep D1) (HeckeCoset.rep D2)) := rfl

/-- A basis element of the Hecke ring: `TSingle D b` is the formal sum `b · [D]`. -/
noncomputable abbrev TSingle (a : HeckeCoset P) (b : Z) : 𝕋 P Z :=
  Finsupp.single a b

/-- A basis element of the Hecke module: `HeckeLeftCosetSingle m b` is the formal sum
`b · [m]`. -/
noncomputable abbrev HeckeLeftCosetSingle (a : HeckeLeftCoset P) (b : Z) :
    HeckeModule P Z :=
  Finsupp.single a b

/-- Shimura's notation: `T⦃D⦄` is the basis element `[HgH]` in the Hecke ring,
    corresponding to the double coset `D` with coefficient 1. -/
scoped notation:max "T⦃" D "⦄" => TSingle _ ℤ D (1 : ℤ)

/-- Shimura's notation: `T⦃D, a⦄` is the element `a · [HgH]` in the Hecke ring. -/
scoped notation:max "T⦃" D ", " a "⦄" => TSingle _ ℤ D a

/-- Multiplication of two basis elements in the Hecke ring. -/
lemma mul_singleton_𝕋 (D1 D2 : HeckeCoset P) (a b : ℤ) :
    TSingle P ℤ D1 a * TSingle P ℤ D2 b =
      a • b • m P (HeckeCoset.rep D1) (HeckeCoset.rep D2) := by
  simp_rw [TSingle, mul_def]
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index, m]
  · simp only [zero_smul, smul_zero]
  · ext a; simp only [m, zero_smul, Finsupp.sum_fun_zero, Finsupp.coe_zero,
      Pi.zero_apply]

open Finsupp

/-- If all pairs under `mulMap` land on a single double coset `D_out`, then
`heckeMultiplicity` vanishes on every other coset. -/
lemma heckeMultiplicity_eq_zero_of_mulMap_unique (g₁ g₂ : P.Δ) (D_out A : HeckeCoset P)
    (hA : A ≠ D_out)
    (h : ∀ p : decompQuot P g₁ × decompQuot P g₂,
      mulMap P g₁ g₂ p = D_out) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep A) = 0 :=
  heckeMultiplicity_eq_zero_of_nmem_mulSupport P g₁ g₂ A (by
    rw [mulSupport]; simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
      true_and, Prod.exists, not_exists]
    intro i j heq; exact hA (heq ▸ h (i, j)))

/-- When `heckeMultiplicity` equals one on a single output coset and vanishes elsewhere,
the multiplication finsupp is a singleton. -/
lemma m_eq_single (g₁ g₂ : P.Δ) (D_out : HeckeCoset P)
    (h_one : heckeMultiplicity P g₁ g₂ (HeckeCoset.rep D_out) = 1)
    (h_zero : ∀ A, A ≠ D_out →
      heckeMultiplicity P g₁ g₂ (HeckeCoset.rep A) = 0) :
    m P g₁ g₂ = Finsupp.single D_out 1 := by
  ext A; simp only [m, Finsupp.coe_mk, Finsupp.single_apply]
  split_ifs with h1 <;> [exact h1 ▸ h_one; exact h_zero A (ne_comm.mp h1)]

/-- The off-diagonal multiplicity for right multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_mul_one_eq_zero (g₁ : P.Δ) (A : HeckeCoset P)
    (h : A ≠ (⟦g₁⟧ : HeckeCoset P)) :
    heckeMultiplicity P g₁ (HeckeCoset.one P).rep (HeckeCoset.rep A) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero,
    isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  apply h
  have h1 := doubleCoset_eq_of_rightCoset_eq P g₁ (HeckeCoset.one P).rep
    (HeckeCoset.rep A) (i, j) heq
  have h2 := mulMap_T_one_eq P g₁ i j
  have h3 : A = ⟦HeckeCoset.rep A⟧ := (Quotient.out_eq A).symm
  rw [h3]; exact (h2.symm.trans h1).symm

/-- Right multiplication by `HeckeCoset.one` acts as the identity:
`m(g₁, one.rep) = δ_{⟦g₁⟧}`. -/
lemma m_mul_one_eq_single (g₁ : P.Δ) :
    m P g₁ (HeckeCoset.one P).rep =
      Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 :=
  m_eq_single P g₁ (HeckeCoset.one P).rep (⟦g₁⟧ : HeckeCoset P)
    ((heckeMultiplicity_mul_one P g₁ (HeckeCoset.rep (⟦g₁⟧ : HeckeCoset P))).mp
      (show (⟦g₁⟧ : HeckeCoset P) = ⟦HeckeCoset.rep ⟦g₁⟧⟧
        from (Quotient.out_eq (⟦g₁⟧ : HeckeCoset P)).symm))
    (fun A hA => heckeMultiplicity_mul_one_eq_zero P g₁ A hA)

/-- `TSingle D b * TSingle (HeckeCoset.one P) 1 = TSingle D b`. -/
lemma singleton_one_mul_𝕋 (D2 : HeckeCoset P) (b : ℤ) :
    TSingle P ℤ D2 b * TSingle P ℤ (HeckeCoset.one P) 1 =
      TSingle P ℤ D2 b := by
  revert D2; exact HeckeCoset.ind fun g => by
    rw [mul_singleton_𝕋, m_mul_one_eq_single]
    simp only [TSingle]
    rw [show (⟦HeckeCoset.rep ⟦g⟧⟧ : HeckeCoset P) = ⟦g⟧ from Quotient.out_eq _]
    simp

/-- The off-diagonal multiplicity for left multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_one_mul_eq_zero (g₁ : P.Δ) (A : HeckeCoset P)
    (h : A ≠ (⟦g₁⟧ : HeckeCoset P)) :
    heckeMultiplicity P (HeckeCoset.one P).rep g₁ (HeckeCoset.rep A) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero,
    isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  apply h
  have h1 := doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P).rep g₁
    (HeckeCoset.rep A) (i, j) heq
  have h2 := mulMap_one_T_eq P g₁ i j
  have h3 : A = ⟦HeckeCoset.rep A⟧ := (Quotient.out_eq A).symm
  rw [h3]; exact (h2.symm.trans h1).symm

/-- Left multiplication by `HeckeCoset.one` acts as the identity:
`m(one.rep, g₁) = δ_{⟦g₁⟧}`. -/
lemma m_one_mul_eq_single (g₁ : P.Δ) :
    m P (HeckeCoset.one P).rep g₁ =
      Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 :=
  m_eq_single P (HeckeCoset.one P).rep g₁ (⟦g₁⟧ : HeckeCoset P)
    ((heckeMultiplicity_one_mul P g₁ (HeckeCoset.rep (⟦g₁⟧ : HeckeCoset P))).mp
      (show (⟦g₁⟧ : HeckeCoset P) = ⟦HeckeCoset.rep ⟦g₁⟧⟧
        from (Quotient.out_eq (⟦g₁⟧ : HeckeCoset P)).symm))
    (fun A hA => heckeMultiplicity_one_mul_eq_zero P g₁ A hA)

/-- `TSingle (HeckeCoset.one P) 1 * TSingle D b = TSingle D b`. -/
lemma one_mul_singleton_𝕋 (D2 : HeckeCoset P) (b : ℤ) :
    TSingle P ℤ (HeckeCoset.one P) 1 * TSingle P ℤ D2 b =
      TSingle P ℤ D2 b := by
  revert D2; exact HeckeCoset.ind fun g => by
    rw [mul_singleton_𝕋, m_one_mul_eq_single]
    simp only [TSingle]
    rw [show (⟦HeckeCoset.rep ⟦g⟧⟧ : HeckeCoset P) = ⟦g⟧ from Quotient.out_eq _]
    simp

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance instNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (𝕋 P ℤ) :=
  { (instAddCommGroup𝕋 P ℤ) with
    left_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f)
        (funext₂ fun a₁ b₁ => Finsupp.sum_add_index' ?_ ?_))
        ?_
      · intro a; simp only [zero_smul, smul_zero]
      · intro D1 a b
        simp_rw [← smul_assoc, smul_eq_mul]
        ring_nf
        rw [@add_smul]
      · exact Finsupp.sum_add

    right_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index' ?_ ?_) ?_
      · intro a; change (h.sum fun D2 b₂ ↦ (0 : ℤ) • b₂ • m P a.rep D2.rep) = 0
        simp only [zero_smul, Finsupp.sum_fun_zero]
      · intro D1 a b
        change (h.sum fun D2 b₂ ↦ (a + b) • b₂ • m P D1.rep D2.rep) =
          (h.sum fun D2 b₂ ↦ a • b₂ • m P D1.rep D2.rep) +
          (h.sum fun D2 b₂ ↦ b • b₂ • m P D1.rep D2.rep)
        simp_rw [add_smul]
        exact Finsupp.sum_add
      · rfl

    zero_mul := fun f => by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f)
        (funext₂ fun a₁ b₁ => sum_zero_index)) (sum_fun_zero f) }

end HeckeRing
