/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Module

/-!
# Hecke Rings: Associativity

The `IsScalarTower` instance proving that the module action is compatible with multiplication,
which is equivalent to associativity of multiplication in the Hecke ring. This is Shimura
Proposition 3.4.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- IsScalarTower: `x •_M (y •_M z) = (y * x) •_M z` (Shimura Prop 3.4). -/
private lemma smulOrbit_map_injective (g : P.Δ) (β : P.Δ) :
    Function.Injective (fun i : decompQuot P g =>
      (⟦⟨((β : G) * (i.out : G) * (g : G)),
        delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset : ({(β : G) * (i₁.out : G) *
      (g : G)} : Set G) * (P.H : Set G) =
    {(β : G) * (i₂.out : G) *
      (g : G)} * P.H := Quotient.exact heq
  have hmem : (β : G) * (i₁.out : G) * (g : G) ∈
      ({(β : G) * (i₂.out : G) * (g : G)} : Set G) *
        (P.H : Set G) := by rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (g : G) * k =
      (i₁.out : G) * (g : G) := by
    apply mul_left_cancel (a := (β : G))
    have := hkk; group at this ⊢; exact this
  apply decompQuot_coset_diff P g i₁ i₂ hne
  exact leftCoset_eq_of_not_disjoint (H := P.H) _ _ (by
    rw [@not_disjoint_iff]
    exact ⟨(i₁.out : G) * (g : G),
      ⟨1, P.H.one_mem, mul_one _⟩,
      ⟨k, hk, cancel⟩⟩)

private lemma conjAct_inv_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G)⁻¹ * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hn
  have := P.H.inv_mem hn; convert this using 1; group

private lemma conjAct_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G) * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

private lemma mk_out_coe_eq_mul {g : G} {h : P.H}
    {n : (ConjAct.toConjAct g • P.H).subgroupOf P.H}
    (hn_eq : (⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out = h * n) :
    ((⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out : G) =
      (h : G) * (n : G) := by
  simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn_eq

private lemma decompQuot_eq_of_conjAct_rel (g : P.Δ)
    (i₁ i₂ : decompQuot P g)
    (h : (i₁.out : ↥P.H)⁻¹ * i₂.out ∈
      (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H) :
    i₁ = i₂ := by
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at h
  simp only [Quotient.out_eq'] at h; exact h

private lemma coset_shift_fwd (q a b a' b' g₁ g₂ g_D n₁ n₂ : G)
    (hcond : ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H)
    (ha' : a' = q⁻¹ * a * n₁) (hb' : b' = g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂)
    (hn₂_conj : g₁⁻¹ * n₂ * g₁ ∈ P.H) :
    ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H := by
  subst ha' hb'
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁),
    ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a * g₂ * (b * g₁) ∈ ({q * g_D} : Set G) * ↑P.H := by
    rw [← hcond]; exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, h_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at h_eq; subst h_eq
  refine ⟨h₀ * (g₁⁻¹ * n₂ * g₁), P.H.mul_mem hh₀ hn₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁)
      = q⁻¹ * (a * g₂ * (b * g₁)) * (g₁⁻¹ * n₂ * g₁) := by group
    _ = g_D * (h₀ * (g₁⁻¹ * n₂ * g₁)) := by
        have hprod' : q * g_D * h₀ = a * g₂ * (b * g₁) := hprod
        rw [← hprod']; group

private lemma coset_shift_inv (q a b a' b' g₁ g₂ g_D m₁ m₂ : G)
    (hcond : ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H)
    (ha : a = q * a' * m₁) (hb : b = g₂⁻¹ * m₁⁻¹ * g₂ * b' * m₂)
    (hm₂_conj : g₁⁻¹ * m₂ * g₁ ∈ P.H) :
    ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H := by
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨a * g₂ * (b * g₁), ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a' * g₂ * (b' * g₁) ∈ ({g_D} : Set G) * ↑P.H := by
    rw [← hcond]; exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, hd_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at hd_eq
  refine ⟨h₀ * (g₁⁻¹ * m₂ * g₁), P.H.mul_mem hh₀ hm₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc a * g₂ * (b * g₁)
      = q * (a' * g₂ * (b' * g₁)) * (g₁⁻¹ * m₂ * g₁) := by subst ha hb; group
    _ = q * g_D * (h₀ * (g₁⁻¹ * m₂ * g₁)) := by subst hd_eq; rw [← hprod]; group

/-- Uniform distribution of multiplicities: the count of coset pairs `(i,j)` mapping
to a given left coset `q₀H` within double coset `D` is independent of the choice of `q₀`
(Shimura Proposition 3.4). -/
lemma heckeMultiplicity_uniform (g₂ g₁ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) :
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) *
      {(p.2.out : G) * (g₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * (P.H : Set G)} =
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) *
      {(p.2.out : G) * (g₁ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G)} := by
  set g₁' := (g₁ : G) with hg₁_def
  set g₂' := (g₂ : G) with hg₂_def
  set g_D := (HeckeCoset.rep D : G) with hgD_def
  apply Nat.card_congr
  let get_n : decompQuot P g₂ → (ConjAct.toConjAct g₂' • P.H).subgroupOf P.H := fun i =>
    (QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
      ⟨(q₀.out : G)⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose
  refine Equiv.ofBijective (fun ⟨⟨i, j⟩, (hcond : _ = _)⟩ =>
    let i' : decompQuot P g₂ :=
      ⟦⟨(q₀.out : G)⁻¹ * i.out,
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩⟧
    let n := get_n i
    let hn_conj : g₂'⁻¹ * (n : G)⁻¹ * g₂' ∈ P.H := conjAct_inv_mem_of_subgroupOf P g₂' n
    let h_n : G := g₂'⁻¹ * (n : G)⁻¹ * g₂'
    let j' : decompQuot P g₁ := ⟦⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩⟧
    (⟨⟨i', j'⟩, by
      change ({(i'.out : G) * g₂'} : Set G) * {(j'.out : G) * g₁'} * P.H = {g_D} * P.H
      rw [Set.singleton_mul_singleton]
      have hcond' : ({(i.out : G) * g₂' * ((j.out : G) * g₁')} : Set G) * ↑P.H =
          {(q₀.out : G) * g_D} * ↑P.H := by rw [← Set.singleton_mul_singleton]; exact hcond
      have hn_coe : (i'.out : G) = (q₀.out : G)⁻¹ * (i.out : G) * (n : G) :=
        mk_out_coe_eq_mul P (QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
          ⟨(q₀.out : G)⁻¹ * i.out,
            P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose_spec
      obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
        ⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩
      exact coset_shift_fwd P (q₀.out : G) (i.out : G) (j.out : G) (i'.out : G)
        (j'.out : G) g₁' g₂' g_D (n : G) (n' : G) hcond' hn_coe
        (mk_out_coe_eq_mul P hn'_eq) (conjAct_mem_of_subgroupOf P g₁' n')
    ⟩ : {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * g₂'} : Set G) * {(p.2.out : G) * g₁'} * P.H =
      {g_D} * P.H})) ?_
  constructor
  · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨hi, hj⟩ := heq
    have hi₁₂ : i₁ = i₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hi
      exact decompQuot_eq_of_conjAct_rel P g₂ i₁ i₂
        (by convert hi using 1; ext; simp [Subgroup.coe_mul])
    subst hi₁₂
    have hj₁₂ : j₁ = j₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj
      exact decompQuot_eq_of_conjAct_rel P g₁ j₁ j₂
        (by convert hj using 1; ext; simp [Subgroup.coe_mul]; group)
    subst hj₁₂; rfl
  · intro ⟨⟨i', j'⟩, (hcond'_tgt : _ = _)⟩
    let i₀ : decompQuot P g₂ :=
      ⟦⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩⟧
    let n₀ := get_n i₀
    have hn₀_conj : g₂'⁻¹ * (n₀ : G) * g₂' ∈ P.H := conjAct_mem_of_subgroupOf P g₂' n₀
    let j₀ : decompQuot P g₁ := ⟦⟨g₂'⁻¹ * (n₀ : G) * g₂' * j'.out,
      P.H.mul_mem hn₀_conj j'.out.2⟩⟧
    obtain ⟨m_i, hmi_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
      ⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩
    obtain ⟨m_j, hmj_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
      ⟨g₂'⁻¹ * (n₀ : G) * g₂' * j'.out, P.H.mul_mem hn₀_conj j'.out.2⟩
    have hmi_coe : (i₀.out : G) = (q₀.out : G) * (i'.out : G) * (m_i : G) :=
      mk_out_coe_eq_mul P hmi_eq
    have hmj_coe : (j₀.out : G) = g₂'⁻¹ * (n₀ : G) * g₂' * (j'.out : G) * (m_j : G) :=
      mk_out_coe_eq_mul P hmj_eq
    have h_quot_eq : (⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂) = i' := by
      rw [show i' = ⟦i'.out⟧ from (Quotient.out_eq' i').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h := Quotient.out_eq' i₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h
      convert h using 1; ext; simp [Subgroup.coe_mul]; group
    have h_n₀_mi : (n₀ : G) = (m_i : G)⁻¹ := by
      have hn₀_spec := (QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
        ⟨(q₀.out : G)⁻¹ * i₀.out,
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩).choose_spec
      have hn₀_val : (i'.out : G) = (q₀.out : G)⁻¹ * (i₀.out : G) * (n₀ : G) := by
        have h1 := congr_arg (Subtype.val : ↥P.H → G) hn₀_spec
        simp only [Subgroup.coe_mul] at h1
        rwa [show ((⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂).out : G) =
          (i'.out : G) from by congr 1; simp [h_quot_eq]] at h1
      have h1 : (i'.out : G) = (i'.out : G) * (m_i : G) * (n₀ : G) := by
        conv_lhs => rw [hn₀_val]; rw [hmi_coe]
        group
      have h2 : (m_i : G) * (n₀ : G) = 1 := by
        have := congr_arg ((i'.out : G)⁻¹ * ·) h1
        simp only [inv_mul_cancel] at this; group at this; exact this.symm
      exact eq_inv_of_mul_eq_one_right h2
    have hcond₀ : ({(i₀.out : G) * g₂'} : Set G) * {(j₀.out : G) * g₁'} * P.H =
        {(q₀.out : G) * g_D} * P.H := by
      rw [Set.singleton_mul_singleton]
      exact coset_shift_inv P (q₀.out : G) (i₀.out : G) (j₀.out : G) (i'.out : G)
        (j'.out : G) g₁' g₂' g_D (m_i : G) (m_j : G)
        (by rw [← Set.singleton_mul_singleton]; exact hcond'_tgt)
        hmi_coe (by rw [hmj_coe, h_n₀_mi]) (conjAct_mem_of_subgroupOf P g₁' m_j)
    refine ⟨⟨⟨i₀, j₀⟩, hcond₀⟩, ?_⟩
    apply Subtype.ext; simp only [Prod.mk.injEq]; exact ⟨h_quot_eq, by
      rw [show j' = ⟦j'.out⟧ from (Quotient.out_eq' j').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h_j₀ := Quotient.out_eq' j₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h_j₀
      convert h_j₀ using 1; ext; simp [Subgroup.coe_mul]; group; rfl⟩

private lemma iter_mem_smulOrbit_mulMap (g₂ g₁ : P.Δ) (β : P.Δ)
    (i : decompQuot P g₂) (j : decompQuot P g₁) :
    (⟦⟨(β : G) * i.out * (g₂ : G) *
      j.out * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out β g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) ∈
    smulOrbit P (HeckeCoset.rep (mulMap P g₂ g₁ (i, j))) β := by
  set D := mulMap P g₂ g₁ (i, j) with hD_def
  set g_D := (HeckeCoset.rep D : G) with hgD_def
  set α := (β : G)
  have h_in_doset : (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) ∈
      DoubleCoset.doubleCoset g_D P.H P.H := by
    have h1 := HeckeCoset.toSet_eq_rep D
    rw [← h1]
    change (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) ∈
      HeckeCoset.toSet (mulMap P g₂ g₁ (i, j))
    simp only [mulMap, HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [DoubleCoset.mem_doubleCoset] at h_in_doset
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := h_in_doset
  set r : decompQuot P (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g_D • P.H).subgroupOf P.H) ⟨h₁, hh₁⟩
  have hn_coe : (r.out : G) = h₁ * (n : G) := by
    simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn_eq
  have hn_conj : g_D⁻¹ * (n : G)⁻¹ * g_D ∈ P.H := by
    have hn := n.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at hn
    have hsimp : ConjAct.ofConjAct (ConjAct.toConjAct g_D)⁻¹ = g_D⁻¹ := by
      rw [map_inv, ConjAct.ofConjAct_toConjAct]
    rw [hsimp] at hn
    have := P.H.inv_mem hn; convert this using 1; group
  suffices hsuff : (⟦⟨α * (r.out : G) * g_D,
      delta_mul_mem P.H P.Δ r.out β (HeckeCoset.rep D) P.h₀⟩⟧ :
        HeckeLeftCoset P) =
    (⟦⟨α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out β g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) by
    rw [← hsuff]
    change _ ∈ smulOrbit P (HeckeCoset.rep D) β
    simp only [smulOrbit, Finset.mem_image]
    exact ⟨r, Finset.mem_univ _, rfl⟩
  apply Quotient.sound; change lcRel P _ _; simp only [lcRel]
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨α * h₁ * g_D, ?_, ?_⟩
  · refine ⟨g_D⁻¹ * (n : G)⁻¹ * g_D, hn_conj, ?_⟩
    simp only [smul_eq_mul]; rw [hn_coe]; group
  · refine ⟨h₂⁻¹, P.H.inv_mem hh₂, ?_⟩
    simp only [smul_eq_mul]
    have hprod' : (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) = h₁ * g_D * h₂ := hprod
    calc α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G) * h₂⁻¹
        = α * ((i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G))) * h₂⁻¹ := by group
      _ = α * (h₁ * g_D * h₂) * h₂⁻¹ := by rw [hprod']
      _ = α * h₁ * g_D := by group

private lemma iter_smulOrbit_mem_mulSupport_smulOrbit
    (g₂ g₁ : P.Δ) (β₀ : P.Δ) (j x₀ : HeckeLeftCoset P)
    (hj : j ∈ smulOrbit P g₂ β₀)
    (hx₀ : x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j)) :
    ∃ D, D ∈ mulSupport P g₂ g₁ ∧ x₀ ∈ smulOrbit P (HeckeCoset.rep D) β₀ := by
  set g₂' := (g₂ : G) with hg₂'_def
  set g₁' := (g₁ : G) with hg₁'_def
  set α := (β₀ : G)
  simp only [smulOrbit, Finset.mem_image] at hj hx₀
  obtain ⟨i₀, _, hj_eq⟩ := hj
  obtain ⟨k₀, _, hx₀_eq⟩ := hx₀
  set β := (HeckeLeftCoset.rep j : G)
  have h_rep_mem : g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β ∈ P.H := by
    have h_j_set : HeckeLeftCoset.toSet j =
        ({α * (i₀.out : G) * g₂'} : Set G) * ↑P.H := by rw [← hj_eq]; rfl
    have hβ : β ∈ ({α * (i₀.out : G) * g₂'} : Set G) * ↑P.H := by
      have h_coset : ({β} : Set G) * ↑P.H = ({α * (i₀.out : G) * g₂'} : Set G) * ↑P.H := by
        have h1 : HeckeLeftCoset.toSet j = ({β} : Set G) * ↑P.H := by
          show _ = _
          have := Quotient.out_eq (s := lcSetoid P) j
          rw [← this]; rfl
        rw [← h1, h_j_set]
      have hβ_triv : β ∈ ({β} : Set G) * ↑P.H :=
        ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
      rwa [h_coset] at hβ_triv
    simp only [Set.singleton_mul, Set.mem_image] at hβ
    obtain ⟨h, hh, hβ_eq⟩ := hβ
    have : g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β = h := by
      rw [show β = α * (i₀.out : G) * g₂' * h from hβ_eq.symm]; group
    rw [this]; exact hh
  set k' : decompQuot P g₁ :=
    ⟦⟨g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β * (k₀.out : G),
    P.H.mul_mem h_rep_mem k₀.out.2⟩⟧
  -- Use iter_mem_smulOrbit_mulMap directly with g₂, g₁
  set D' := mulMap P g₂ g₁ (i₀, k')
  have h_target := iter_mem_smulOrbit_mulMap P g₂ g₁ β₀ i₀ k'
  refine ⟨D', Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  -- Show x₀ ∈ smulOrbit P (HeckeCoset.rep D') β₀
  rw [← hx₀_eq]
  obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
    ⟨g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β * (k₀.out : G),
      P.H.mul_mem h_rep_mem k₀.out.2⟩
  have hn'_coe : (k'.out : G) =
      g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β * (k₀.out : G) * (n' : G) := by
    simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn'_eq
  have hn'_conj : g₁'⁻¹ * (n' : G)⁻¹ * g₁' ∈ P.H :=
    conjAct_inv_mem_of_subgroupOf P g₁' n'
  suffices hsuff :
    (⟦⟨β * (k₀.out : G) * g₁',
      delta_mul_mem P.H P.Δ k₀.out (HeckeLeftCoset.rep j) g₁ P.h₀⟩⟧ :
        HeckeLeftCoset P) =
    (⟦⟨α * (i₀.out : G) * g₂' *
      (k'.out : G) * g₁',
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i₀.out β₀ g₂ P.h₀)
        (P.h₀ k'.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) by
    rw [hsuff]; exact h_target
  apply Quotient.sound; change lcRel P _ _; simp only [lcRel]
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨β * (k₀.out : G) * g₁',
    ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  refine ⟨g₁'⁻¹ * (n' : G)⁻¹ * g₁', hn'_conj, ?_⟩
  simp only [smul_eq_mul]
  rw [hn'_coe]; group

open Classical in
private lemma smulOrbit_indicator_eq_sum (g₁ : P.Δ)
    (x₀ : HeckeLeftCoset P) (β : P.Δ) :
    (if x₀ ∈ smulOrbit P g₁ β then (1 : ℤ) else 0) =
    ∑ k : decompQuot P g₁,
      if (⟦⟨(β : G) * (k.out : G) * (g₁ : G),
      delta_mul_mem P.H P.Δ k.out β g₁ P.h₀⟩⟧ :
        HeckeLeftCoset P) = x₀ then 1 else 0 := by
  by_cases hmem : x₀ ∈ smulOrbit P g₁ β
  · rw [if_pos hmem]
    simp only [smulOrbit, Finset.mem_image] at hmem
    obtain ⟨q₀, _, hq₀⟩ := hmem
    rw [Finset.sum_eq_single q₀]
    · simp only [hq₀, ↓reduceIte]
    · intro q _ hne; rw [if_neg]; intro heq
      exact hne (smulOrbit_map_injective P g₁ β (heq.trans hq₀.symm))
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [if_neg hmem]; symm
    exact Finset.sum_eq_zero fun q _ => if_neg fun heq =>
      hmem (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩)

open Classical in
private lemma smulOrbit_count_eq_m' (g₂ g₁ : P.Δ) (D₀ : HeckeCoset P)
    (β₀ : P.Δ) (x₀ : HeckeLeftCoset P)
    (hx₀ : x₀ ∈ smulOrbit P (HeckeCoset.rep D₀) β₀) :
    (∑ j ∈ smulOrbit P g₂ β₀,
      if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j) then (1 : ℤ) else 0) =
    (m P g₂ g₁) D₀ := by
  simp only [smulOrbit, Finset.mem_image] at hx₀
  obtain ⟨q₀, _, hq₀⟩ := hx₀
  -- Step 1: Convert to indexed sum, replacing HeckeLeftCoset.rep with concrete elements
  -- We need: sum over orbit = sum over decompQuot with smulOrbit_rep_mk applied
  have h_lhs_eq :
    ∀ q : decompQuot P g₂,
      smulOrbit P g₁ (HeckeLeftCoset.rep
        (⟦⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P)) =
      smulOrbit P g₁ ⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩ := by
    intro q
    exact smulOrbit_lcRel P g₁
      (Quotient.exact (Quotient.out_eq
        (⟦⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P)))
  set F : HeckeLeftCoset P → ℤ :=
    fun j => if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j) then 1 else 0 with hF_def
  change (∑ j ∈ smulOrbit P g₂ β₀, F j) = (m P g₂ g₁) D₀
  conv_lhs => rw [smulOrbit]; rw [Finset.top_eq_univ]
  have h_inj : Set.InjOn (fun i : decompQuot P g₂ =>
      (⟦⟨(β₀ : G) * (i.out : G) * (g₂ : G),
        delta_mul_mem P.H P.Δ i.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P))
      (Finset.univ : Finset (decompQuot P g₂)) :=
    fun a _ b _ hab => smulOrbit_map_injective P g₂ β₀ hab
  have h_img := Finset.sum_image (f := F) h_inj
  rw [h_img]
  simp only [hF_def, h_lhs_eq]
  -- Step 2: Use smulOrbit_indicator_eq_sum to expand each indicator
  simp_rw [smulOrbit_indicator_eq_sum P g₁ x₀]
  have M_mk_eq_iff : ∀ (a b : P.Δ),
      (⟦a⟧ : HeckeLeftCoset P) = ⟦b⟧ ↔
      ({(a : G)} : Set G) * ↑P.H = {(b : G)} * ↑P.H :=
    fun a b => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  simp_rw [← hq₀, M_mk_eq_iff]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  -- Step 4: Factor out the left coset representative β₀
  have h_iff : ∀ (p : decompQuot P g₂ × decompQuot P g₁),
      ({(β₀ : G) * ↑p.1.out * (g₂ : G) * ↑p.2.out *
        (g₁ : G)} : Set G) * ↑P.H =
        {(β₀ : G) * ↑q₀.out * (HeckeCoset.rep D₀ : G)} * ↑P.H ↔
      ({(↑p.1.out : G) * (g₂ : G)} : Set G) *
        {(↑p.2.out : G) * (g₁ : G)} * ↑P.H =
        {(↑q₀.out : G) * (HeckeCoset.rep D₀ : G)} * ↑P.H := by
    intro p
    constructor
    · intro h
      have hl : ({(β₀ : G) * ↑p.1.out * (g₂ : G) * ↑p.2.out *
          (g₁ : G)} : Set G) =
          ({(β₀ : G)} : Set G) *
          {↑p.1.out * (g₂ : G) * (↑p.2.out * (g₁ : G))} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hr : ({(β₀ : G) * ↑q₀.out * (HeckeCoset.rep D₀ : G)} : Set G) =
          ({(β₀ : G)} : Set G) * {↑q₀.out * (HeckeCoset.rep D₀ : G)} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hset' : ({(β₀ : G)} : Set G) *
          ({↑p.1.out * (g₂ : G) * (↑p.2.out * (g₁ : G))} * ↑P.H) =
          {(β₀ : G)} * ({↑q₀.out * (HeckeCoset.rep D₀ : G)} * ↑P.H) := by
        rw [← mul_assoc, ← hl, ← mul_assoc, ← hr]; exact h
      have h' := set_singleton_mul_left_cancel (β₀ : G) hset'
      rwa [Set.singleton_mul_singleton]
    · intro h
      rw [Set.singleton_mul_singleton] at h
      have hl : ({(β₀ : G) * ↑p.1.out * (g₂ : G) * ↑p.2.out *
          (g₁ : G)} : Set G) =
          ({(β₀ : G)} : Set G) *
          {↑p.1.out * (g₂ : G) * (↑p.2.out * (g₁ : G))} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hr : ({(β₀ : G) * ↑q₀.out * (HeckeCoset.rep D₀ : G)} : Set G) =
          ({(β₀ : G)} : Set G) * {↑q₀.out * (HeckeCoset.rep D₀ : G)} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      calc ({(β₀ : G) * ↑p.1.out * (g₂ : G) * ↑p.2.out *
              (g₁ : G)} : Set G) * ↑P.H
          _ = ({(β₀ : G)} * {↑p.1.out * (g₂ : G) *
              (↑p.2.out * (g₁ : G))}) * ↑P.H := by rw [hl]
          _ = {(β₀ : G)} * ({↑p.1.out * (g₂ : G) *
              (↑p.2.out * (g₁ : G))} * ↑P.H) :=
              mul_assoc ({(β₀ : G)} : Set G) _ _
          _ = {(β₀ : G)} * ({↑q₀.out * (HeckeCoset.rep D₀ : G)} * ↑P.H) :=
              congr_arg _ h
          _ = ({(β₀ : G)} * {↑q₀.out * (HeckeCoset.rep D₀ : G)}) * ↑P.H :=
              (mul_assoc ({(β₀ : G)} : Set G) _ _).symm
          _ = ({(β₀ : G) * ↑q₀.out * (HeckeCoset.rep D₀ : G)} : Set G) * ↑P.H := by rw [hr]
  have h_prop := fun p => propext (h_iff p)
  simp_rw [h_prop]
  -- Step 5: Conclude using the multiplicity definition and uniformity
  rw [show (m P g₂ g₁) D₀ = (heckeMultiplicity P g₂ g₁ (HeckeCoset.rep D₀) : ℤ) from rfl]
  unfold heckeMultiplicity
  norm_cast
  exact heckeMultiplicity_uniform P g₂ g₁ D₀ q₀

private lemma smul_assoc_key (g₁ g₂ : P.Δ) (β₀ : P.Δ) :
    ((m P g₂ g₁).sum fun D b₁ ↦
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D) β₀, Finsupp.single i (b₁ * 1)) =
    (∑ j ∈ smulOrbit P g₂ β₀,
      Finsupp.single j 1).sum
      fun m b₂ ↦ ∑ i ∈ smulOrbit P g₁ (HeckeLeftCoset.rep m),
        Finsupp.single i (1 * b₂) := by
  simp only [mul_one, one_mul]
  ext x₀
  simp only [Finsupp.sum_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_rhs : (∑ j ∈ smulOrbit P g₂ β₀, Finsupp.single j 1).sum
      (fun a₁ b ↦ if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep a₁)
        then b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P g₂ β₀,
        if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j) then 1 else 0 := by
    rw [← Finsupp.sum_finsetSum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rw [h_rhs]
  by_cases h_ex : ∃ D₀ ∈ (m P g₂ g₁).support, x₀ ∈ smulOrbit P (HeckeCoset.rep D₀) β₀
  · obtain ⟨D₀, hD₀, hx₀⟩ := h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P (HeckeCoset.rep a₁) β₀ then b
        else (0 : ℤ)) = (m P g₂ g₁) D₀ := by
      rw [Finsupp.sum]
      rw [Finset.sum_eq_single D₀
        (fun D hD hne => if_neg (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P (HeckeCoset.rep D₀) (HeckeCoset.rep D) β₀
            (by simp only [HeckeCoset.rep, Quotient.out_eq]; exact hne.symm)) hx₀))
        (fun h => absurd hD₀ h)]
      exact if_pos hx₀
    rw [h_lhs]
    exact (smulOrbit_count_eq_m' P g₂ g₁ D₀ β₀ x₀ hx₀).symm
  · push Not at h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P (HeckeCoset.rep a₁) β₀ then b
        else (0 : ℤ)) = 0 := by
      rw [Finsupp.sum]
      exact Finset.sum_eq_zero (fun D hD => if_neg (h_ex D hD))
    rw [h_lhs]
    exact (Finset.sum_eq_zero fun j hj => by
      simp only [ite_eq_right_iff, one_ne_zero]
      intro hmem
      obtain ⟨D, hD, hD_mem⟩ :=
        iter_smulOrbit_mem_mulSupport_smulOrbit
          P g₂ g₁ β₀ j x₀ hj hmem
      exact absurd hD_mem (h_ex D hD)).symm

private lemma smul_assoc_singles (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    (TSingle P ℤ D₂ a₂ * TSingle P ℤ D₁ a₁) •
      (HeckeLeftCosetSingle P ℤ m₀ c₀) =
    TSingle P ℤ D₁ a₁ •
      (TSingle P ℤ D₂ a₂ • HeckeLeftCosetSingle P ℤ m₀ c₀) := by
  rw [mul_singleton_𝕋, single_smul_single]
  simp only [smul_eq_sum, HeckeLeftCosetSingle, TSingle]
  have hsi : ∀ (D : HeckeCoset P) (b : ℤ),
      (Finsupp.single m₀ c₀).sum (fun m b₂ =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * b₂)) =
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀),
        Finsupp.single i (b * c₀) := by
    intro D b
    rw [Finsupp.sum_single_index (by
      simp [mul_zero, Finsupp.single_zero,
        Finset.sum_const_zero])]
  simp_rw [hsi]
  rw [Finsupp.sum_single_index (by simp [zero_mul, Finsupp.single_zero, Finset.sum_const_zero])]
  apply Finsupp.ext; intro x₀
  simp only [Finsupp.sum_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_rhs :
      (∑ j ∈ smulOrbit P (HeckeCoset.rep D₂) (HeckeLeftCoset.rep m₀),
        Finsupp.single j (a₂ * c₀)).sum
      (fun a b ↦ if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep a)
        then a₁ * b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P (HeckeCoset.rep D₂) (HeckeLeftCoset.rep m₀),
        if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep j)
        then a₁ * (a₂ * c₀) else 0 := by
    rw [← Finsupp.sum_finsetSum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*, mul_add])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rw [h_rhs]
  have h_lhs : (a₂ • a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
      (fun D b₁ ↦ if x₀ ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀)
        then b₁ * c₀ else (0 : ℤ)) =
      (m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
      (fun D b₁ ↦
        if x₀ ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀)
        then a₂ * (a₁ * b₁) * c₀
        else (0 : ℤ)) := by
    rw [show a₂ • a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      a₂ • (a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)) from rfl]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
  rw [h_lhs]
  have key := smul_assoc_key P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (HeckeLeftCoset.rep m₀)
  simp only [mul_one, one_mul] at key
  have key_pt := congr_fun (congr_arg DFunLike.coe key) x₀
  simp only [Finsupp.sum_apply, Finsupp.finsetSum_apply, Finsupp.single_apply] at key_pt
  simp_rw [Finset.sum_ite_eq'] at key_pt
  simp_rw [show ∀ (D : HeckeCoset P) (b₁ : ℤ),
      (if x₀ ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀)
        then a₂ * (a₁ * b₁) * c₀ else 0) =
      a₁ * a₂ * c₀ *
        (if x₀ ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀)
          then b₁ else 0) from
    fun D b₁ => by split_ifs <;> ring]
  simp_rw [show ∀ (j : HeckeLeftCoset P),
      (if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep j)
        then a₁ * (a₂ * c₀) else 0) =
      a₁ * a₂ * c₀ *
        (if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep j)
          then 1 else 0) from
    fun j => by split_ifs <;> ring]
  simp_rw [← Finset.mul_sum, ← Finsupp.mul_sum]
  congr 1
  have h_rhs2 :
      (∑ j ∈ smulOrbit P (HeckeCoset.rep D₂) (HeckeLeftCoset.rep m₀),
        Finsupp.single j 1).sum
      (fun a₁ b ↦ if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep a₁)
        then b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P (HeckeCoset.rep D₂) (HeckeLeftCoset.rep m₀),
        if x₀ ∈ smulOrbit P (HeckeCoset.rep D₁) (HeckeLeftCoset.rep j) then 1 else 0 := by
    rw [← Finsupp.sum_finsetSum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rwa [h_rhs2] at key_pt

/-- The module action satisfies the scalar tower property `(x * y) • z = y • (x • z)`,
which is equivalent to associativity of multiplication (Shimura Proposition 3.4). -/
noncomputable instance instIsScalarTower :
    IsScalarTower (𝕋 P ℤ) (𝕋 P ℤ) (HeckeModule P ℤ) where
  smul_assoc x y z := by
    rw [show x • y = y * x from rfl]
    induction x using Finsupp.induction_linear with
    | zero =>
      rw [@mul_zero _ (instNonUnitalNonAssocSemiring P).toMulZeroClass y,
        zero_smul_HeckeModule, zero_smul_HeckeModule]
    | add x₁ x₂ ih₁ ih₂ =>
      rw [(instNonUnitalNonAssocSemiring P).left_distrib y x₁ x₂,
        smul_add_left, ih₁, ih₂, ← smul_add_left]
    | single D₁ a₁ =>
      induction y using Finsupp.induction_linear with
      | zero =>
        rw [@zero_mul _ (instNonUnitalNonAssocSemiring P).toMulZeroClass _,
          zero_smul_HeckeModule, smul_zero_HeckeModule]
      | add y₁ y₂ ih₁ ih₂ =>
        rw [(instNonUnitalNonAssocSemiring P).right_distrib y₁ y₂ (Finsupp.single D₁ a₁),
          smul_add_left, ih₁, ih₂, smul_add_left, smul_add_right]
      | single D₂ a₂ =>
        induction z using Finsupp.induction_linear with
        | zero => simp only [smul_zero_HeckeModule]
        | add z₁ z₂ ih₁ ih₂ =>
          rw [smul_add_right, smul_add_right, ih₁, ih₂, smul_add_right]
        | single m₀ c₀ =>
          exact smul_assoc_singles P D₁ D₂ a₁ a₂ m₀ c₀

end HeckeRing
