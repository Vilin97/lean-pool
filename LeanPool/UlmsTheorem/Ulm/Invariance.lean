/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import LeanPool.UlmsTheorem.PGroups.UlmInvariants

/-!
# Invariance of Ulm data under isomorphism

This module contains the easy direction of Ulm's theorem: isomorphisms preserve
both the Ulm filtration and the classical `P_α / P_{α+1}` quotients, hence the
Ulm invariants.
-/

namespace UlmsTheorem

open Cardinal Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
/-- An isomorphism of abelian groups preserves the Ulm subgroups. -/
lemma ulmSubgroup_map_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    (ulmSubgroup p α (G := G)).map φ.toAddMonoidHom = ulmSubgroup p α (G := H) := by
  induction α using Ordinal.limitRecOn with
  | zero => simp [ulmSubgroup]
  | add_one α ih =>
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ulmSubgroup_add_one] at hx ⊢
      rcases hx with ⟨z, hz, rfl⟩
      refine ⟨φ z, ?_, by simp⟩
      rw [← ih]
      exact ⟨z, hz, rfl⟩
    · rw [ulmSubgroup_add_one]
      rintro ⟨z, hz, hzy⟩
      refine ⟨p • φ.symm z, ?_, ?_⟩
      · rw [ulmSubgroup_add_one]
        refine ⟨φ.symm z, ?_, rfl⟩
        rw [← ih] at hz
        rcases hz with ⟨x, hx, hxz⟩
        have : x = φ.symm z := by
          apply φ.injective
          simpa using hxz
        simpa [this] using hx
      · simp [hzy]
  | limit o ho IH =>
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ ulmSubgroup p o at hx
      rw [mem_ulmSubgroup_limit_iff (G := G) p ho] at hx
      rw [mem_ulmSubgroup_limit_iff (G := H) p ho]
      intro β hβ
      have hxβ : x ∈ ulmSubgroup p β (G := G) := hx β hβ
      have : φ x ∈ (ulmSubgroup p β (G := G)).map φ.toAddMonoidHom := ⟨x, hxβ, rfl⟩
      rw [IH β hβ] at this
      exact this
    · intro hy
      rw [mem_ulmSubgroup_limit_iff (G := H) p ho] at hy
      simp only [AddSubgroup.mem_map]
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [mem_ulmSubgroup_limit_iff (G := G) p ho]
      intro β hβ
      have hyβ : y ∈ ulmSubgroup p β (G := H) := hy β hβ
      rw [← IH β hβ] at hyβ
      rcases hyβ with ⟨x, hx, hxy⟩
      have : x = φ.symm y := by
        apply φ.injective
        simpa using hxy
      change φ.symm y ∈ (ulmSubgroup p β (G := G) : Set G)
      simpa only [this] using hx

omit hp in
/-- An isomorphism preserves the filtered p-socle layers `P_α`. -/
lemma pSocleAt_map_iso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    (pSocleAt p α (G := G)).map φ.toAddMonoidHom = pSocleAt p α (G := H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : p • x = 0 := (mem_pSocleAt p α x).1 hx |>.1
    have hxα : x ∈ ulmSubgroup p α (G := G) := (mem_pSocleAt p α x).1 hx |>.2
    exact (mem_pSocleAt p α (φ x)).2 ⟨by simpa [map_nsmul] using congrArg φ hx0, by
      have : φ x ∈ (ulmSubgroup p α (G := G)).map φ.toAddMonoidHom := ⟨x, hxα, rfl⟩
      rw [ulmSubgroup_map_iso (p := p) φ α] at this
      exact this⟩
  · intro hy
    have hy0 : p • y = 0 := (mem_pSocleAt p α y).1 hy |>.1
    have hyα : y ∈ ulmSubgroup p α (G := H) := (mem_pSocleAt p α y).1 hy |>.2
    refine ⟨φ.symm y, (mem_pSocleAt p α (φ.symm y)).2 ⟨?_, ?_⟩, by simp⟩
    · apply φ.injective
      simpa [map_nsmul] using hy0
    · have hy' : y ∈ (ulmSubgroup p α (G := G)).map φ.toAddMonoidHom := by
        rw [ulmSubgroup_map_iso (p := p) φ α]
        exact hyα
      rcases hy' with ⟨x, hx, hxy⟩
      have : x = φ.symm y := by
        apply φ.injective
        simpa using hxy
      simpa [this] using hx

private noncomputable def pSocleAtIso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) : pSocleAt p α (G := G) ≃+ pSocleAt p α (G := H) where
  toFun x := ⟨φ x, by
    rw [← pSocleAt_map_iso (p := p) φ α]
    exact ⟨x, x.prop, rfl⟩⟩
  invFun y := ⟨φ.symm y, by
    have hy' : (y : H) ∈ (pSocleAt p α (G := G)).map φ.toAddMonoidHom := by
      rw [pSocleAt_map_iso (p := p) φ α]
      exact y.prop
    rcases hy' with ⟨x, hx, hxy⟩
    have : x = φ.symm y := by
      apply φ.injective
      simpa using hxy
    simpa [this] using hx⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

/-- An isomorphism induces an isomorphism on the classical Ulm quotients. -/
noncomputable def ulmQuotientMapIso {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    ulmQuotient p α (G := G) ≃+ ulmQuotient p α (G := H) := by
  let e := pSocleAtIso p φ α
  let Dg : AddSubgroup (pSocleAt p α (G := G)) := pSocleAtSuccSubgroupOf p α
  let Dh : AddSubgroup (pSocleAt p α (G := H)) := pSocleAtSuccSubgroupOf p α
  have hf : Dg ≤ AddSubgroup.comap e.toAddMonoidHom Dh := by
    intro x hx
    change (x : G) ∈ pSocleAt p (Order.succ α) (G := G) at hx
    change (φ (x : G) : H) ∈ pSocleAt p (Order.succ α) (G := H)
    rw [← pSocleAt_map_iso (p := p) φ (Order.succ α)]
    exact ⟨x, hx, rfl⟩
  have hg : Dh ≤ AddSubgroup.comap e.symm.toAddMonoidHom Dg := by
    intro y hy
    change (y : H) ∈ pSocleAt p (Order.succ α) (G := H) at hy
    change (φ.symm (y : H) : G) ∈ pSocleAt p (Order.succ α) (G := G)
    have hy' : (y : H) ∈ (pSocleAt p (Order.succ α) (G := G)).map φ.toAddMonoidHom := by
      rw [pSocleAt_map_iso (p := p) φ (Order.succ α)]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have : x = φ.symm y := by
      apply φ.injective
      simpa using hxy
    simpa [this] using hx
  let f : ulmQuotient p α (G := G) →+ ulmQuotient p α (G := H) :=
    QuotientAddGroup.map Dg Dh e.toAddMonoidHom hf
  let g : ulmQuotient p α (G := H) →+ ulmQuotient p α (G := G) :=
    QuotientAddGroup.map Dh Dg e.symm.toAddMonoidHom hg
  exact f.toAddEquiv g
    (by
      ext q
      refine Quotient.inductionOn q ?_
      intro x
      change g (f (QuotientAddGroup.mk' Dg x)) = QuotientAddGroup.mk' Dg x
      change (QuotientAddGroup.mk' Dg (e.symm (e x))) = QuotientAddGroup.mk' Dg x
      simp)
    (by
      ext q
      refine Quotient.inductionOn q ?_
      intro y
      change f (g (QuotientAddGroup.mk' Dh y)) = QuotientAddGroup.mk' Dh y
      change (QuotientAddGroup.mk' Dh (e (e.symm y))) = QuotientAddGroup.mk' Dh y
      simp)

/-- Isomorphic groups have equal Ulm invariants. -/
theorem ulmInvariant_iso_invariant {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (φ : G ≃+ H) (α : Ordinal) :
    ulmInvariant p α (G := G) = ulmInvariant p α (G := H) := by
  let e := ulmQuotientMapIso p φ α
  have hlin : ∀ (c : ZMod p) (x : ulmQuotient p α (G := G)), e (c • x) = c • e x := by
    intro c x
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
    simp only [Nat.cast_smul_eq_nsmul]
    induction n with
    | zero => simp
    | succ n ih => simp only [succ_nsmul, map_add, ih]
  exact rank_eq_of_equiv_equiv (fun c : ZMod p ↦ c) e (by simp) hlin

end UlmsTheorem
