/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm

/-! # Frobenius Closure Commutation -/

@[expose] public section
universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius-closure commutation

This module promotes commutation with a Frobenius generator to its closed
procyclic subgroup and derives the conjugation identities for the associated
fixed field.
-/

noncomputable
section

open CategoryTheory
open scoped BigOperators

section frobeniusClosureCommutation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Commuting with the chosen generator means commuting with its closed
procyclic closure. -/
theorem frobeniusClosure_commutes_of_commutes_generator (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (c : D.frobeniusClosure K L hLK σ) :
    q * c.1 = c.1 * q := by
  let : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let : T2Space
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
    infer_instance
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let X : Set Q := Set.range (fun _ : Unit => σ.1)
  have hclosure : Subgroup.closure X ≤
      Subgroup.centralizer ({q} : Set Q) := by
    rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hq.symm
  have htop : (Subgroup.closure X).topologicalClosure ≤
      Subgroup.centralizer ({q} : Set Q) :=
    Subgroup.topologicalClosure_minimal _ hclosure
      (Set.isClosed_centralizer (M := Q) ({q} : Set Q))
  have hc : c.1 ∈ (Subgroup.closure X).topologicalClosure := c.2
  exact (Subgroup.mem_centralizer_singleton_iff.mp (htop hc)).symm

/-- If a quotient element commutes with the Frobenius lift, its chosen
representative stabilizes the corresponding fixed field. -/
theorem conjugate_frobeniusFixedField_eq_of_commutes (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ := by
  dsimp only
  let T := D.frobeniusFixedField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [this]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q * QuotientGroup.mk t * q⁻¹ = QuotientGroup.mk t := by
        calc
          q * QuotientGroup.mk t * q⁻¹ =
              (QuotientGroup.mk t * q) * q⁻¹ := by rw [hcomm']
          _ = QuotientGroup.mk t := by simp
      change QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      have hxval : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have hcomm := D.frobeniusClosure_commutes_of_commutes_generator
      K L hLK σ q hq ⟨QuotientGroup.mk t, htClosure⟩
    have hcomm' : q * QuotientGroup.mk t = QuotientGroup.mk t * q := hcomm
    have hyClosure : QuotientGroup.mk yK ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      have hqconj : q⁻¹ * QuotientGroup.mk t * q = QuotientGroup.mk t := by
        calc
          q⁻¹ * QuotientGroup.mk t * q =
              q⁻¹ * (QuotientGroup.mk t * q) := by simp [mul_assoc]
          _ = q⁻¹ * (q * QuotientGroup.mk t) := by rw [hcomm']
          _ = QuotientGroup.mk t := by simp
      have hyval : yK = k⁻¹ * t * k := by
        apply Subtype.ext
        dsimp [yK]
        have htxval : t.1 = x := by simpa using htx
        rw [htxval]
      rw [hyval]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ *
          QuotientGroup.mk t * QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      rw [hkq, hqconj]
      exact htClosure
    refine ⟨yK, hyClosure, ?_⟩
    simp [yK]

end DegreeData

end frobeniusClosureCommutation

end

end ClassFormation
