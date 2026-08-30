/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeanPool.UlmsTheorem.Ulm.Pure

/-!
# Extension lemmas for Ulm's theorem

This file contains the one-generator extension interface used in the hard
direction of Ulm's theorem, formulated against the classical invariants
`dim_{ℤ/pℤ}(P_α / P_{α+1})`.
-/

namespace UlmsTheorem

open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-! ## Kaplansky's finite-stage data -/

-- `IsProper` now lives in `Lib.Ulm.Pure`, next to `ulmHeight`, so that the
-- Section 1 definitions layer can use it without importing this file.

/-- `S_α = S ∩ G_α`. -/
noncomputable def stageAt (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G :=
  S ⊓ ulmSubgroup p α

/-- Kaplansky's `S_α* = S_α ∩ p⁻¹G_{α+2}`. -/
noncomputable def kaplanskyStar (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G where
  carrier := {x | x ∈ S ∧ x ∈ ulmSubgroup p α ∧
    p • x ∈ ulmSubgroup p (Order.succ (Order.succ α))}
  zero_mem' := ⟨S.zero_mem, (ulmSubgroup p α).zero_mem, by
    simp⟩
  add_mem' := by
    rintro x y ⟨hxS, hxα, hpx⟩ ⟨hyS, hyα, hpy⟩
    exact ⟨S.add_mem hxS hyS, (ulmSubgroup p α).add_mem hxα hyα, by
      rw [smul_add]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).add_mem hpx hpy⟩
  neg_mem' := by
    rintro x ⟨hxS, hxα, hpx⟩
    exact ⟨S.neg_mem hxS, (ulmSubgroup p α).neg_mem hxα, by
      rw [smul_neg]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).neg_mem hpx⟩

omit hp in
/-- `S_{α+1}` is contained in `S_α*`. -/
lemma stageAt_succ_le_kaplanskyStar (S : AddSubgroup G) (α : Ordinal) :
    stageAt p S (Order.succ α) ≤ kaplanskyStar p S α := by
  intro x hx
  have hxS : x ∈ S := hx.1
  have hxα1 : x ∈ ulmSubgroup p (Order.succ α) := hx.2
  have hxα : x ∈ ulmSubgroup p α :=
    ulmSubgroup_antitone p (Order.le_succ α) hxα1
  refine ⟨hxS, hxα, ?_⟩
  rw [ulmSubgroup_succ]
  exact ⟨x, hxα1, rfl⟩

/-- `S_{α+1}` viewed as a subgroup of `S_α*`. -/
noncomputable def stageAtSuccInStar (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (kaplanskyStar p S α) :=
  (stageAt p S (Order.succ α)).comap (kaplanskyStar p S α).subtype

/-- The source quotient in Kaplansky's relative-Ulm map. -/
noncomputable def kaplanskyDomainQuotient (S : AddSubgroup G) (α : Ordinal) : Type u :=
  kaplanskyStar p S α ⧸ stageAtSuccInStar p S α

noncomputable instance (S : AddSubgroup G) (α : Ordinal) :
    AddCommGroup (kaplanskyDomainQuotient p S α) := by
  unfold kaplanskyDomainQuotient
  infer_instance

omit hp in
/-- Every class in Kaplansky's source quotient is killed by `p`. -/
lemma kaplanskyDomainQuotient_orderOf_dvd_p
    (S : AddSubgroup G) (α : Ordinal)
    (x : kaplanskyDomainQuotient p S α) :
    p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  change QuotientAddGroup.mk' (stageAtSuccInStar p S α) (p • a) =
    QuotientAddGroup.mk' (stageAtSuccInStar p S α) 0
  apply (QuotientAddGroup.mk'_eq_mk' _).2
  refine ⟨-(p • a), ?_, by simp⟩
  change (-(p • (a : G))) ∈ stageAt p S (Order.succ α)
  refine ⟨S.neg_mem (S.nsmul_mem a.property.1 p), ?_⟩
  apply (ulmSubgroup p (Order.succ α)).neg_mem
  exact ulmSubgroup_antitone p (Order.le_succ (Order.succ α)) a.property.2.2

noncomputable instance kaplanskyDomainQuotientModule
    (S : AddSubgroup G) (α : Ordinal) :
    Module (ZMod p) (kaplanskyDomainQuotient p S α) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := kaplanskyDomainQuotient p S α) ?_
  intro x
  exact kaplanskyDomainQuotient_orderOf_dvd_p p S α x

/-- An additive Kaplansky map is automatically `ZMod p`-linear. -/
noncomputable def kaplanskyLinearMap
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    kaplanskyDomainQuotient p S α →ₗ[ZMod p] ulmQuotient p α (G := G) :=
  U.toZModLinearMap p

/-- The occupied part of the Ulm layer: the range of a Kaplansky map. -/
noncomputable def kaplanskyOccupiedSubmodule
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  LinearMap.range (kaplanskyLinearMap p S α U)

/-- The remaining room in the Ulm layer, after quotienting by the occupied range. -/
abbrev kaplanskyRoomQuotient
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) : Type _ :=
  ulmQuotient p α (G := G) ⧸ kaplanskyOccupiedSubmodule p S α U

/-- The dimension of the unoccupied quotient of the Ulm layer. -/
noncomputable def kaplanskyRoomInvariant
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    Cardinal :=
  Module.rank (ZMod p) (kaplanskyRoomQuotient p S α U)

/-- Rank bookkeeping for Kaplansky's map:
`room + occupied = the ordinary Ulm invariant`. -/
theorem kaplansky_room_equation
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    kaplanskyRoomInvariant p S α U +
        Module.rank (ZMod p) (kaplanskyOccupiedSubmodule p S α U) =
      ulmInvariant p α (G := G) := by
  exact Submodule.rank_quotient_add_rank (kaplanskyOccupiedSubmodule p S α U)

/-- “Not onto means room”: a Kaplansky map fails to be surjective exactly when
its room quotient is nontrivial. -/
theorem kaplansky_not_surjective_iff_room
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    ¬ Function.Surjective U ↔ Nontrivial (kaplanskyRoomQuotient p S α U) := by
  rw [Submodule.Quotient.nontrivial_iff]
  change (¬ Function.Surjective U) ↔
    LinearMap.range (kaplanskyLinearMap p S α U) ≠ ⊤
  rw [ne_eq, LinearMap.range_eq_top]
  rfl

omit hp in
/-- A chosen correction one level higher, with the same `p`-multiple as an
element of `S_α*`.  The eventual quotient class is independent of this choice. -/
lemma exists_kaplanskyCorrection
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    ∃ y : G, y ∈ ulmSubgroup p (Order.succ α) ∧ p • y = p • (x : G) := by
  have hx := x.property.2.2
  rw [ulmSubgroup_succ] at hx
  exact hx

/-- A choice of a one-level-higher correction with the prescribed `p`-multiple. -/
noncomputable def kaplanskyCorrection
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) : G :=
  Classical.choose (exists_kaplanskyCorrection p S α x)

omit hp in
lemma kaplanskyCorrection_mem
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    kaplanskyCorrection p S α x ∈ ulmSubgroup p (Order.succ α) :=
  (Classical.choose_spec (exists_kaplanskyCorrection p S α x)).1

omit hp in
lemma kaplanskyCorrection_smul
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    p • kaplanskyCorrection p S α x = p • (x : G) :=
  (Classical.choose_spec (exists_kaplanskyCorrection p S α x)).2

/-- The order-`p` representative `x-y ∈ P_α` used in Kaplansky's map. -/
noncomputable def kaplanskySocleRep
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    pSocleAt p α (G := G) := by
  refine ⟨(x : G) - kaplanskyCorrection p S α x, ?_⟩
  rw [mem_pSocleAt]
  constructor
  · rw [smul_sub, kaplanskyCorrection_smul]
    simp
  · exact (ulmSubgroup p α).sub_mem x.property.2.1
      (ulmSubgroup_antitone p (Order.le_succ α)
        (kaplanskyCorrection_mem p S α x))

/-- The pre-quotient Kaplansky homomorphism on `S_α*`. -/
noncomputable def kaplanskyPreMap
    (S : AddSubgroup G) (α : Ordinal) :
    kaplanskyStar p S α →+ ulmQuotient p α (G := G) where
  toFun x := (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α x)
  map_zero' := by
    apply (Submodule.Quotient.mk_eq_zero _).2
    change (kaplanskySocleRep p S α 0 : G) ∈
      pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨(kaplanskySocleRep p S α 0).property.1, ?_⟩
    change (0 : G) - kaplanskyCorrection p S α 0 ∈
      ulmSubgroup p (Order.succ α)
    simpa using (ulmSubgroup p (Order.succ α)).neg_mem
      (kaplanskyCorrection_mem p S α 0)
  map_add' x y := by
    rw [← LinearMap.map_add]
    apply (Submodule.Quotient.eq _).2
    change ((kaplanskySocleRep p S α (x + y) -
      (kaplanskySocleRep p S α x + kaplanskySocleRep p S α y) :
        pSocleAt p α (G := G)) : G) ∈
      pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨by
      have h := (kaplanskySocleRep p S α (x + y) -
        (kaplanskySocleRep p S α x + kaplanskySocleRep p S α y)).property
      exact h.1, ?_⟩
    change ((x : G) + y - kaplanskyCorrection p S α (x + y)) -
        (((x : G) - kaplanskyCorrection p S α x) +
          ((y : G) - kaplanskyCorrection p S α y)) ∈
      ulmSubgroup p (Order.succ α)
    have hx := kaplanskyCorrection_mem p S α x
    have hy := kaplanskyCorrection_mem p S α y
    have hxy := kaplanskyCorrection_mem p S α (x + y)
    have hmem :
        kaplanskyCorrection p S α x + kaplanskyCorrection p S α y -
            kaplanskyCorrection p S α (x + y) ∈
          ulmSubgroup p (Order.succ α) :=
      (ulmSubgroup p (Order.succ α)).sub_mem
        ((ulmSubgroup p (Order.succ α)).add_mem hx hy) hxy
    convert hmem using 1
    abel

/-- Kaplansky's canonical linear map `S_α*/S_(α+1) → P_α/P_(α+1)`. -/
noncomputable def kaplanskyMap
    (S : AddSubgroup G) (α : Ordinal) :
    kaplanskyDomainQuotient p S α →+
      ulmQuotient p α (G := G) :=
  QuotientAddGroup.lift (stageAtSuccInStar p S α)
    (kaplanskyPreMap p S α) (by
      intro x hx
      rw [AddMonoidHom.mem_ker]
      apply (Submodule.Quotient.mk_eq_zero _).2
      change (kaplanskySocleRep p S α x : G) ∈
        pSocleAt p (Order.succ α) (G := G)
      rw [mem_pSocleAt]
      refine ⟨(kaplanskySocleRep p S α x).property.1, ?_⟩
      exact (ulmSubgroup p (Order.succ α)).sub_mem hx.2
        (kaplanskyCorrection_mem p S α x))

theorem kaplanskyMap_injective
    (S : AddSubgroup G) (α : Ordinal) :
    Function.Injective (kaplanskyMap p S α) := by
  apply (AddMonoidHom.ker_eq_bot_iff (kaplanskyMap p S α)).1
  ext x
  change (kaplanskyMap p S α) x = 0 ↔ x = 0
  refine Quotient.inductionOn x ?_
  intro a
  constructor
  · intro ha
    simp only [kaplanskyMap] at ha
    have hrep : (kaplanskySocleRep p S α a : G) ∈
        pSocleAt p (Order.succ α) (G := G) := by
      exact (Submodule.Quotient.mk_eq_zero _).1 ha
    apply (QuotientAddGroup.eq_zero_iff _).2
    change (a : G) ∈ stageAt p S (Order.succ α)
    refine ⟨a.property.1, ?_⟩
    have ha :
        (a : G) =
          (kaplanskySocleRep p S α a : G) +
            kaplanskyCorrection p S α a := by
      change (a : G) =
        ((a : G) - kaplanskyCorrection p S α a) +
          kaplanskyCorrection p S α a
      abel
    rw [ha]
    exact (ulmSubgroup p (Order.succ α)).add_mem hrep.2
      (kaplanskyCorrection_mem p S α a)
  · intro ha
    rw [ha]
    exact map_zero (kaplanskyMap p S α)

/-- The canonical Kaplansky map occupies exactly
`((S + G_(α+1)) ∩ P_α) / P_(α+1)` in the ordinary Ulm layer. -/
theorem kaplanskyMap_range
    (S : AddSubgroup G) (α : Ordinal) :
    LinearMap.range (kaplanskyLinearMap p S α (kaplanskyMap p S α)) =
      relativeOccupiedSubmodule p S α := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro a
    change (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α a) ∈
      relativeOccupiedSubmodule p S α
    apply (Submodule.mem_map).2
    refine ⟨kaplanskySocleRep p S α a, ?_, rfl⟩
    change (kaplanskySocleRep p S α a : G) ∈
      pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
    refine ⟨(kaplanskySocleRep p S α a).property, ?_⟩
    change (a : G) - kaplanskyCorrection p S α a ∈
      S ⊔ ulmSubgroup p (Order.succ α)
    simpa [sub_eq_add_neg] using AddSubgroup.add_mem_sup a.property.1
      ((ulmSubgroup p (Order.succ α)).neg_mem
        (kaplanskyCorrection_mem p S α a))
  · intro hz
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).1 hz
    change (v : G) ∈ pSocleAt p α ⊓
      (S ⊔ ulmSubgroup p (Order.succ α)) at hv
    obtain ⟨s, hs, g, hg, hsg⟩ := AddSubgroup.mem_sup.mp hv.2
    have hs_eq : s = (v : G) - g := by
      rw [← hsg]
      abel
    let a : kaplanskyStar p S α := ⟨s, hs, by
      rw [hs_eq]
      exact (ulmSubgroup p α).sub_mem v.property.2
        (ulmSubgroup_antitone p (Order.le_succ α) hg), by
      rw [hs_eq, smul_sub]
      have hvp : p • (v : G) = 0 := v.property.1
      rw [hvp]
      have hpg : p • g ∈ ulmSubgroup p (Order.succ (Order.succ α)) := by
        rw [ulmSubgroup_succ]
        exact ⟨g, hg, rfl⟩
      simpa only [_root_.zero_sub] using
        (ulmSubgroup p (Order.succ (Order.succ α))).neg_mem hpg⟩
    refine ⟨(QuotientAddGroup.mk' (stageAtSuccInStar p S α)) a, ?_⟩
    change (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α a) =
      (ulmDenSubmodule p α).mkQ v
    apply (Submodule.Quotient.eq _).2
    change ((kaplanskySocleRep p S α a - v :
      pSocleAt p α (G := G)) : G) ∈
        pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨(kaplanskySocleRep p S α a - v).property.1, ?_⟩
    have hc := kaplanskyCorrection_mem p S α a
    have hsum :
        -kaplanskyCorrection p S α a - g ∈
          ulmSubgroup p (Order.succ α) :=
      (ulmSubgroup p (Order.succ α)).sub_mem
        ((ulmSubgroup p (Order.succ α)).neg_mem hc) hg
    change (s - kaplanskyCorrection p S α a) - (v : G) ∈
      ulmSubgroup p (Order.succ α)
    rw [← hsg]
    convert hsum using 1
    abel

/-- The relative Ulm quotient is nontrivial exactly when there is a proper
order-`p` representative of exact height `α`. -/
theorem relativeUlmQuotient_nontrivial_iff_proper
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    Nontrivial (relativeUlmQuotient p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by
  constructor
  · intro hroom
    rw [Submodule.Quotient.nontrivial_iff] at hroom
    obtain ⟨v, _, hv⟩ :=
      SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hroom)
    have hv' : (v : G) ∉
        pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α)) := by
      exact hv
    have hvSucc : (v : G) ∉ ulmSubgroup p (Order.succ α) := by
      intro hvs
      exact hv' ⟨v.property, AddSubgroup.mem_sup_right hvs⟩
    refine ⟨v, v.property, hvSucc, ?_⟩
    intro s
    apply ulmHeight_le_of_mem_imp p ((v : G) + s) v
    intro β hvsum
    by_cases hβα : β ≤ α
    · exact ulmSubgroup_antitone p hβα v.property.2
    · have hsucc : Order.succ α ≤ β :=
        Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      have hvsumSucc :
          (v : G) + s ∈ ulmSubgroup p (Order.succ α) :=
        ulmSubgroup_antitone p hsucc hvsum
      exfalso
      apply hv'
      refine ⟨v.property, ?_⟩
      have heq : (v : G) = (-s : G) + ((v : G) + s) := by
        abel
      rw [heq]
      exact AddSubgroup.add_mem_sup (S.neg_mem s.property) hvsumSucc
  · rintro ⟨v, hvP, hvSucc, hvProper⟩
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    let vP : pSocleAt p α (G := G) := ⟨v, hvP⟩
    have hvden : vP ∈ relativeUlmSubmodule p S α := by
      change vP ∈ hillSubmodule p S α
      rw [htop]
      trivial
    change v ∈ pSocleAt p α ⊓
      (S ⊔ ulmSubgroup p (Order.succ α)) at hvden
    obtain ⟨s, hs, g, hg, hsg⟩ := AddSubgroup.mem_sup.mp hvden.2
    have heq : v + -s = g := by
      rw [← hsg]
      abel
    exact (isProper_iff_forall_not_mem_succ p S hvP.2 hvSucc).1 hvProper
      ⟨-s, S.neg_mem hs⟩ (by simpa [heq] using hg)

/-- Canonical form of Kaplansky's range lemma: his specified map is not onto
exactly when there is an exact-height-`α` socle element proper over `S`. -/
theorem kaplanskyMap_not_surjective_iff_proper
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    ¬ Function.Surjective (kaplanskyMap p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by
  rw [kaplansky_not_surjective_iff_room p S α (kaplanskyMap p S α)]
  rw [Submodule.Quotient.nontrivial_iff]
  change LinearMap.range
      (kaplanskyLinearMap p S α (kaplanskyMap p S α)) ≠ ⊤ ↔ _
  rw [kaplanskyMap_range p S α]
  rw [← Submodule.Quotient.nontrivial_iff]
  have hroom :
      Nontrivial (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ↔
        Nontrivial (relativeUlmQuotient p S α) := by
    constructor
    · intro h
      let _ := h
      exact (occupiedQuotientEquivRelative p S α).symm.toEquiv.nontrivial
    · intro h
      let _ := h
      exact (occupiedQuotientEquivRelative p S α).toEquiv.nontrivial
  exact hroom.trans (relativeUlmQuotient_nontrivial_iff_proper p S α)

/-- Kaplansky's range lemma, the central relative ingredient in the one-generator
extension argument.  The map sends a class represented by `x ∈ S_α*` to the class of
`x-y` in `P_α/P_{α+1}`, where `py = px` and `y ∈ G_{α+1}`. -/
lemma kaplansky_range_lemma (S : AddSubgroup G) (α : Ordinal.{0}) :
    ∃ U : kaplanskyDomainQuotient p S α →+
        ulmQuotient p α (G := G),
      Function.Injective U ∧
      (¬ Function.Surjective U ↔
        ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
          v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
          IsProper p S v) := by
  exact ⟨kaplanskyMap p S α, kaplanskyMap_injective p S α,
    kaplanskyMap_not_surjective_iff_proper p S α⟩

/-- A finite height-preserving partial isomorphism, as used in Kaplansky's proof.

The stages are deliberately finite, not finitely generated pure subgroups.  Requiring
purity would make it impossible to cover a nonzero element of `G_ω`. -/
structure UlmStage where
  /-- The finite source subgroup. -/
  A : AddSubgroup G
  /-- The finite target subgroup. -/
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  /-- The partial additive equivalence between the stage subgroups. -/
  e : A ≃+ B
  hφ : IsHeightPresOn p e.toAddMonoidHom

/-- The exact local interface used by Kaplansky target selection at height
`α`.  Only filtration preservation at `α`, `α+1`, and `α+2` enters the
range argument.  Keeping this separate from `UlmStage` lets cutoff-preserving
ACM stages use the same construction below their cutoff. -/
structure UlmStageAt (α : Ordinal.{0}) where
  /-- The finite source subgroup. -/
  A : AddSubgroup G
  /-- The finite target subgroup. -/
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  /-- The partial additive equivalence between the stage subgroups. -/
  e : A ≃+ B
  hφ_at : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p α (G := G) ↔
      (e x : H) ∈ ulmSubgroup p α (G := H))
  hφ_succ : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ α) (G := H))
  hφ_succSucc : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := H))

/-- A globally height-preserving stage supplies the local three-level
interface at every height. -/
def UlmStage.at (s : UlmStage p (G := G) (H := H)) (α : Ordinal.{0}) :
    UlmStageAt p (G := G) (H := H) α where
  A := s.A
  B := s.B
  hAfinite := s.hAfinite
  hBfinite := s.hBfinite
  e := s.e
  hφ_at := fun x ↦ s.hφ x α
  hφ_succ := fun x ↦ s.hφ x (Order.succ α)
  hφ_succSucc := fun x ↦ s.hφ x (Order.succ (Order.succ α))

/-- Reverse a finite partial isomorphism. -/
noncomputable def UlmStage.symm (s : UlmStage p (G := G) (H := H)) :
    UlmStage p (G := H) (H := G) where
  A := s.B
  B := s.A
  hAfinite := s.hBfinite
  hBfinite := s.hAfinite
  e := s.e.symm
  hφ := by
    intro b α
    simpa using (s.hφ (s.e.symm b) α).symm

/-- A height-preserving stage isomorphism identifies Kaplansky's starred
subgroups on the two sides. -/
noncomputable def kaplanskyStarEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyStar p s.A α ≃+ kaplanskyStar p s.B α where
  toFun x := by
    refine ⟨(s.e ⟨(x : G), x.property.1⟩ : H), ?_⟩
    refine ⟨(s.e ⟨(x : G), x.property.1⟩).prop,
      (s.hφ_at ⟨(x : G), x.property.1⟩).mp x.property.2.1, ?_⟩
    have hpxA : p • (x : G) ∈ s.A := s.A.nsmul_mem x.property.1 p
    have hmap :
        p • (s.e ⟨(x : G), x.property.1⟩ : H) =
          (s.e ⟨p • (x : G), hpxA⟩ : H) := by
      exact
        (congrArg Subtype.val
          (map_nsmul s.e p ⟨(x : G), x.property.1⟩)).symm
    rw [hmap]
    exact
      (s.hφ_succSucc ⟨p • (x : G), hpxA⟩).mp x.property.2.2
  invFun y := by
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩ : G), ?_⟩
    have heinv :
        s.e (s.e.symm ⟨(y : H), y.property.1⟩) =
          ⟨(y : H), y.property.1⟩ := s.e.apply_symm_apply _
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩).prop, ?_, ?_⟩
    · apply (s.hφ_at (s.e.symm ⟨(y : H), y.property.1⟩)).mpr
      simpa [heinv] using y.property.2.1
    · have hpxA :
          p • (s.e.symm ⟨(y : H), y.property.1⟩ : G) ∈ s.A :=
        s.A.nsmul_mem (s.e.symm ⟨(y : H), y.property.1⟩).prop p
      apply
        (s.hφ_succSucc
          ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩).mpr
      have hmap :
          (s.e
            ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
            p • (y : H) := by
        calc
          (s.e
              ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
              p • (s.e (s.e.symm ⟨(y : H), y.property.1⟩) : H) := by
                exact congrArg Subtype.val
                  (map_nsmul s.e
                    p (s.e.symm ⟨(y : H), y.property.1⟩))
          _ = p • (y : H) := by
                rw [congrArg Subtype.val heinv]
      simpa [hmap] using y.property.2.2
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simpa using congrArg Subtype.val
      (s.e.map_add ⟨(x : G), x.property.1⟩ ⟨(y : G), y.property.1⟩)

omit hp in
lemma kaplanskyStarEquiv_map_stageAtSucc
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    (stageAtSuccInStar p s.A α).map
        (kaplanskyStarEquiv p s).toAddMonoidHom =
      stageAtSuccInStar p s.B α := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change
      ((kaplanskyStarEquiv p s x : kaplanskyStar p s.B α) : H) ∈
        stageAt p s.B (Order.succ α)
    change (x : G) ∈ stageAt p s.A (Order.succ α) at hx
    refine ⟨(kaplanskyStarEquiv p s x).property.1, ?_⟩
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    exact (s.hφ_succ ⟨(x : G), x.property.1⟩).mp hx.2
  · intro hy
    let x : kaplanskyStar p s.A α :=
      (kaplanskyStarEquiv p s).symm y
    refine ⟨x, ?_, (kaplanskyStarEquiv p s).apply_symm_apply y⟩
    change (x : G) ∈ stageAt p s.A (Order.succ α)
    change (y : H) ∈ stageAt p s.B (Order.succ α) at hy
    refine ⟨x.property.1, ?_⟩
    apply (s.hφ_succ ⟨(x : G), x.property.1⟩).mpr
    have heq :
        (s.e ⟨(x : G), x.property.1⟩ : H) = (y : H) := by
      simp [x, kaplanskyStarEquiv]
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    rw [heq]
    exact hy.2

/-- The stage isomorphism induces an additive equivalence between the finite
source quotients in Kaplansky's range maps. -/
noncomputable def kaplanskyDomainEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyDomainQuotient p s.A α ≃+
      kaplanskyDomainQuotient p s.B α :=
  QuotientAddGroup.congr
    (stageAtSuccInStar p s.A α)
    (stageAtSuccInStar p s.B α)
    (kaplanskyStarEquiv p s)
    (kaplanskyStarEquiv_map_stageAtSucc p s)

/-- Corresponding finite stages give Kaplansky source quotients of equal
`ZMod p`-dimension. -/
theorem kaplanskyDomain_rank_eq
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    Module.rank (ZMod p) (kaplanskyDomainQuotient p s.A α) =
      Module.rank (ZMod p) (kaplanskyDomainQuotient p s.B α) := by
  let E := kaplanskyDomainEquiv p s
  let L :
      kaplanskyDomainQuotient p s.A α →ₗ[ZMod p]
        kaplanskyDomainQuotient p s.B α :=
    E.toAddMonoidHom.toZModLinearMap p
  let LE :
      kaplanskyDomainQuotient p s.A α ≃ₗ[ZMod p]
        kaplanskyDomainQuotient p s.B α :=
    LinearEquiv.ofBijective L E.bijective
  exact LinearEquiv.rank_eq LE

/-- Kaplansky's source quotient is finite-dimensional when the stage itself
is finite. -/
theorem kaplanskyDomain_module_finite
    (S : AddSubgroup G) (hSfinite : Set.Finite (S : Set G))
    (α : Ordinal.{0}) :
    Module.Finite (ZMod p) (kaplanskyDomainQuotient p S α) := by
  have hstar :
      Set.Finite (kaplanskyStar p S α : Set G) :=
    hSfinite.subset (by
      intro x hx
      exact hx.1)
  let _ : Finite (kaplanskyStar p S α) := hstar.to_subtype
  let _ : Finite (kaplanskyDomainQuotient p S α) :=
    Finite.of_surjective
      (QuotientAddGroup.mk' (stageAtSuccInStar p S α))
      (QuotientAddGroup.mk'_surjective _)
  apply Module.Finite.of_fg_top
  rw [← Submodule.span_univ]
  exact Submodule.fg_span Set.finite_univ

/-- Non-surjectivity of Kaplansky's range map transfers across a finite
height-preserving stage when the ordinary Ulm invariants at `α` agree.

Finiteness of the source quotient is essential here: injective endomorphisms
of infinite-dimensional spaces need not be onto. -/
theorem kaplansky_not_surjective_transfer
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hGroom : ¬ Function.Surjective (kaplanskyMap p s.A α)) :
    ¬ Function.Surjective (kaplanskyMap p s.B α) := by
  intro hHsurj
  let DA := kaplanskyDomainQuotient p s.A α
  let DB := kaplanskyDomainQuotient p s.B α
  let PG := ulmQuotient p α (G := G)
  let PH := ulmQuotient p α (G := H)
  let UG : DA →ₗ[ZMod p] PG :=
    kaplanskyLinearMap p s.A α (kaplanskyMap p s.A α)
  let UH : DB →ₗ[ZMod p] PH :=
    kaplanskyLinearMap p s.B α (kaplanskyMap p s.B α)
  let _ : Module.Finite (ZMod p) DA :=
    kaplanskyDomain_module_finite p s.A s.hAfinite α
  let _ : Module.Finite (ZMod p) DB :=
    kaplanskyDomain_module_finite p s.B s.hBfinite α
  have hUHinj : Function.Injective UH :=
    kaplanskyMap_injective p s.B α
  have hUHsurj : Function.Surjective UH := hHsurj
  let EH : DB ≃ₗ[ZMod p] PH :=
    LinearEquiv.ofBijective UH ⟨hUHinj, hUHsurj⟩
  let _ : Module.Finite (ZMod p) PH :=
    Module.Finite.of_surjective UH hUHsurj
  have hrankDA_PH :
      Module.rank (ZMod p) DA = Module.rank (ZMod p) PH := by
    calc
      Module.rank (ZMod p) DA = Module.rank (ZMod p) DB :=
        kaplanskyDomain_rank_eq p s
      _ = Module.rank (ZMod p) PH := LinearEquiv.rank_eq EH
  have hrankDA_PG :
      Module.rank (ZMod p) DA = Module.rank (ZMod p) PG := by
    exact hrankDA_PH.trans hinv.symm
  have hrankPG_nat :
      Module.rank (ZMod p) PG =
        (Module.finrank (ZMod p) DA : Cardinal) := by
    exact hrankDA_PG.symm.trans
      (Module.finrank_eq_rank (R := ZMod p) (M := DA)).symm
  let _ : Module.Finite (ZMod p) PG :=
    Module.finite_of_rank_eq_nat hrankPG_nat
  have hfinPG :
      Module.finrank (ZMod p) PG = Module.finrank (ZMod p) DA :=
    Module.finrank_eq_of_rank_eq hrankPG_nat
  have hUGinj : Function.Injective UG :=
    kaplanskyMap_injective p s.A α
  have hUGsurj : Function.Surjective UG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinPG.symm).mp hUGinj
  exact hGroom hUGsurj

omit hp in
 /-- Trivial extension when the prescribed generator is already in the domain subgroup. -/
lemma extend_by_one_of_mem
    {A : AddSubgroup G}
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, le_rfl, hg, B, hB, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

omit hp in
/-- Trivial finite-stage extension when the prescribed generator is already in
the domain subgroup. -/
lemma extend_by_one_fg_of_mem
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B) (hBfg : B.FG)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B'.FG) (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, hA, hAfg, le_rfl, hg, B, hB, hBfg, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

/-- Adjoin one element to a subgroup by taking the supremum with its cyclic closure. -/
def adjoinElem (A : AddSubgroup G) (g : G) : AddSubgroup G :=
  A ⊔ AddSubgroup.closure ({g} : Set G)

lemma le_adjoinElem (A : AddSubgroup G) (g : G) : A ≤ adjoinElem A g := by
  exact le_sup_left

lemma mem_adjoinElem_right (A : AddSubgroup G) (g : G) :
    g ∈ adjoinElem A g := by
  exact
    (show AddSubgroup.closure ({g} : Set G) ≤ adjoinElem A g from le_sup_right)
      (AddSubgroup.subset_closure (by simp))

lemma adjoinElem_fg {A : AddSubgroup G} (hAfg : A.FG) (g : G) :
    (adjoinElem A g).FG := by
  classical
  unfold adjoinElem
  refine hAfg.sup ?_
  exact (AddSubgroup.fg_iff _).2 ⟨{g}, rfl, Set.finite_singleton g⟩

/-- Adjoining one element to a finite subgroup of a primary group remains finite. -/
lemma adjoinElem_finite
    (hG : IsPrimaryPGroup p G)
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    Set.Finite (adjoinElem A g : Set G) := by
  have hAfg : A.FG :=
    (AddSubgroup.fg_iff A).2 ⟨(A : Set G), by simp, hAfinite⟩
  have hadjfg : (adjoinElem A g).FG := adjoinElem_fg hAfg g
  let _ : AddGroup.FG (adjoinElem A g) :=
    (AddGroup.fg_iff_addSubgroup_fg (adjoinElem A g)).2 hadjfg
  have htors : IsAddTorsion (adjoinElem A g) := by
    intro z
    obtain ⟨n, hn⟩ := hG (z : G)
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨p ^ n, pow_pos hp.out.pos n, ?_⟩
    apply Subtype.ext
    exact hn
  let _ : Finite (adjoinElem A g) :=
    AddCommGroup.finite_of_fg_isAddTorsion (adjoinElem A g) htors
  have hrange :
      Set.range (fun z : adjoinElem A g ↦ (z : G)) =
        (adjoinElem A g : Set G) := by
    ext z
    simp
  rw [← hrange]
  exact Set.finite_range _

lemma adjoinElem_eq_sup_zmultiples (A : AddSubgroup G) (g : G) :
    adjoinElem A g = A ⊔ AddSubgroup.zmultiples g := by
  unfold adjoinElem
  rw [AddSubgroup.zmultiples_eq_closure]

lemma mem_adjoinElem_iff {A : AddSubgroup G} {g x : G} :
    x ∈ adjoinElem A g ↔ ∃ a ∈ A, ∃ n : ℤ, a + n • g = x := by
  rw [adjoinElem_eq_sup_zmultiples]
  constructor
  · intro hx
    rcases (AddSubgroup.mem_sup).1 hx with ⟨a, ha, z, hz, hsum⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hz with ⟨n, rfl⟩
    exact ⟨a, ha, n, hsum⟩
  · rintro ⟨a, ha, n, rfl⟩
    exact AddSubgroup.add_mem_sup ha <| AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩

lemma dvd_of_zsmul_mem_of_not_mem
    {A : AddSubgroup G} {g : G}
    (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    (k : ℤ) (hk : k • g ∈ A) : (↑p : ℤ) ∣ k := by
  let qg : G ⧸ A := QuotientAddGroup.mk g
  have hkq : k • qg = 0 := by
    change QuotientAddGroup.mk (k • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hk
  have hpq : p • qg = 0 := by
    change QuotientAddGroup.mk (p • g) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact hpg_in
  have hq_ne : qg ≠ 0 := by
    intro hq
    apply hg_notin
    rw [QuotientAddGroup.eq_zero_iff] at hq
    exact hq
  have horder_dvd : addOrderOf qg ∣ p := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simpa using hpq
  have horder_eq : addOrderOf qg = p := by
    rw [Nat.dvd_prime hp.1] at horder_dvd
    rcases horder_dvd with horder_one | horder_eq
    · exfalso
      apply hq_ne
      have hzero : (1 : ℕ) • qg = 0 := by
        rw [← horder_one]
        exact addOrderOf_nsmul_eq_zero qg
      simpa using hzero
    · exact horder_eq
  exact horder_eq ▸ addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkq

lemma socle_extend_build_map
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) {h : H}
    (hpg_in : p • g ∈ A)
    (hrel : p • h = (φ ⟨p • g, hpg_in⟩ : H)) :
    ∃ φ' : adjoinElem A g →+ (⊤ : AddSubgroup H),
      (∀ a : A, (φ' ⟨a, le_adjoinElem (A := A) (g := g) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨g, mem_adjoinElem_right (A := A) g⟩ : H) = h := by
  let ψ : A × ℤ →+ adjoinElem A g :=
    { toFun := fun z ↦
        ⟨(z.1 : G) + z.2 • g, (mem_adjoinElem_iff (A := A) (g := g)).2 ⟨z.1, z.1.prop, z.2, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change ((x.1 + y.1 : A) : G) + (x.2 + y.2) • g =
          ((x.1 : G) + x.2 • g) + ((y.1 : G) + y.2 • g)
        rw [add_zsmul]
        change ((x.1 : G) + (y.1 : G)) + (x.2 • g + y.2 • g) =
          ((x.1 : G) + x.2 • g) + ((y.1 : G) + y.2 • g)
        abel }
  have hψ_surj : Function.Surjective ψ := fun x ↦ by
    rcases (mem_adjoinElem_iff (A := A) (g := g) (x := (x : G))).1 x.prop with ⟨a, ha, n, hn⟩
    exact ⟨(⟨a, ha⟩, n), by ext; exact hn⟩
  let χ : A × ℤ →+ H :=
    { toFun := fun z ↦ (φ z.1 : H) + z.2 • h
      map_zero' := by simp
      map_add' := fun x y ↦ by
        change (φ (x.1 + y.1) : H) + (x.2 + y.2) • h =
          ((φ x.1 : H) + x.2 • h) + ((φ y.1 : H) + y.2 • h)
        rw [map_add, add_zsmul]
        change ((φ x.1 : H) + (φ y.1 : H)) + (x.2 • h + y.2 • h) =
          ((φ x.1 : H) + x.2 • h) + ((φ y.1 : H) + y.2 • h)
        abel }
  -- `χ` carries `ψ`'s kernel: a relation forces `p ∣ z.2`, and then `hrel` turns
  -- the `h`-component into the `φ`-image of the `A`-component.
  have hker : ψ.ker ≤ χ.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    have hz0 : ((z.1 : G) + z.2 • g : G) = 0 :=
      congrArg (fun t : adjoinElem A g ↦ (t : G)) hz
    have hzA : z.2 • g ∈ A := by
      rw [show z.2 • g = -((z.1 : A) : G) by
        rw [eq_neg_iff_add_eq_zero]; simpa [add_comm] using hz0]
      exact A.neg_mem z.1.prop
    obtain ⟨k, hk⟩ := dvd_of_zsmul_mem_of_not_mem p hg_notin hpg_in z.2 hzA
    have hzA0 : z.1 + k • ⟨p • g, hpg_in⟩ = 0 :=
      Subtype.ext (by
        simpa [hk, mul_zsmul, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using hz0)
    calc
      χ z = (φ z.1 : H) + ((p : ℤ) * k) • h := by simp [χ, hk]
      _ = (φ z.1 : H) + k • (p • h) := by simp [mul_zsmul, Int.mul_comm]
      _ = (φ z.1 : H) + k • (φ ⟨p • g, hpg_in⟩ : H) := by rw [hrel]
      _ = (φ (z.1 + k • ⟨p • g, hpg_in⟩) : H) := by simp [map_add, map_zsmul]
      _ = 0 := by simp [hzA0]
  let φ0 : adjoinElem A g →+ H := ψ.liftOfSurjective hψ_surj ⟨χ, hker⟩
  have hφ0ψ : ∀ z : A × ℤ, φ0 (ψ z) = χ z := fun z ↦ by simp [φ0]
  refine ⟨φ0.codRestrict ⊤ fun x ↦ by simp, fun a ↦ ?_, ?_⟩
  · have hψa : ψ (a, 0) = ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ := by ext; simp [ψ]
    change φ0 ⟨(a : G), le_adjoinElem (A := A) (g := g) a.prop⟩ = φ a
    rw [← hψa]
    simpa [χ] using hφ0ψ (a, 0)
  · have hψg : ψ (0, 1) = ⟨g, mem_adjoinElem_right (A := A) g⟩ := by ext; simp [ψ]
    change φ0 ⟨g, mem_adjoinElem_right (A := A) g⟩ = h
    rw [← hψg]
    simpa [χ] using hφ0ψ (0, 1)

lemma phi_zsmul_eq_zsmul_h
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    (k : ℤ) (hk : k • g ∈ A) :
    (↑(φ ⟨k • g, hk⟩) : H) = k • h := by
  obtain ⟨m, hm⟩ := dvd_of_zsmul_mem_of_not_mem (p := p) hg_notin hpg_in k hk
  calc
    (↑(φ ⟨k • g, hk⟩) : H)
        = (↑(φ ⟨m • (p • g), by
              simpa [hm, mul_zsmul, Int.mul_comm, Int.mul_left_comm,
                Int.mul_assoc] using hk⟩) : H) := by
            congr 2
            simp [hm, mul_zsmul, Int.mul_comm]
    _ = m • (↑(φ ⟨p • g, hpg_in⟩) : H) := by
          have hmap :
              φ ⟨m • (p • g), by
                exact A.zsmul_mem hpg_in m⟩ = m • φ ⟨p • g, hpg_in⟩ := by
            exact φ.map_zsmul m ⟨p • g, hpg_in⟩
          exact congrArg Subtype.val hmap
    _ = m • (p • h) := by
          rw [← hh_eq]
    _ = k • h := by
          simp [hm, mul_zsmul, Int.mul_comm]

lemma extend_well_defined
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    {a₁ a₂ : G} {n₁ n₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (heq : a₁ + n₁ • g = a₂ + n₂ • g) :
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
  have hrepr' : a₁ - a₂ = n₂ • g - n₁ • g := by
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm, add_left_comm, add_assoc] using heq)
  have hrepr : a₁ - a₂ = (n₂ - n₁) • g := by
    simpa [sub_eq_add_neg, add_zsmul] using hrepr'
  have hkg : (n₂ - n₁) • g ∈ A := by
    rw [← hrepr]
    exact A.sub_mem ha₁ ha₂
  have hphi :
      (φ ⟨(n₂ - n₁) • g, hkg⟩ : H) = (n₂ - n₁) • h := by
    exact phi_zsmul_eq_zsmul_h (p := p) φ hg_notin hpg_in hh_eq (n₂ - n₁) hkg
  have hsub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) = (n₂ - n₁) • h := by
    have hsame :
        (⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : A) = ⟨(n₂ - n₁) • g, hkg⟩ := by
      apply Subtype.ext
      exact hrepr
    simpa [hsame] using hphi
  have hmap_sub :
      (φ ⟨a₁ - a₂, A.sub_mem ha₁ ha₂⟩ : H) =
        (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) := by
    exact congrArg (fun z : B ↦ (z : H)) (φ.map_sub ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
  have hdiff :
      (φ ⟨a₁, ha₁⟩ : H) - (φ ⟨a₂, ha₂⟩ : H) = (n₂ - n₁) • h := by
    exact hmap_sub.symm.trans hsub
  have hsum :
      (φ ⟨a₁, ha₁⟩ : H) = (n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H) := by
    rwa [sub_eq_iff_eq_add] at hdiff
  calc
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = ((n₂ - n₁) • h + (φ ⟨a₂, ha₂⟩ : H)) + n₁ • h := by
      rw [hsum]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁) • h + n₁ • h) := by
      abel
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + ((n₂ - n₁ + n₁) • h) := by
      rw [← add_zsmul]
    _ = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by
      congr 1
      abel

/-- If `x` has exact height `α`, is proper over `A`, and `p • x ∈ A`,
then no coefficient prime to `p` can move a translate of `x` into
`G_(α+1)`.  This is the filtration form of the height calculation used
when Kaplansky says the extended map is still height-preserving. -/
lemma not_mem_succ_add_zsmul_of_proper
    {A : AddSubgroup G} {x : G} {α : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p A x)
    (hpxA : p • x ∈ A)
    (a : A) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    (a : G) + n • x ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  intro hz
  have hcop_nat : Nat.Coprime p n.natAbs := by
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ?_
    intro hdiv
    exact hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hdiv))
  have hcop : n.gcd ↑p = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa [Nat.gcd_comm] using hcop_nat.gcd_eq_one
  have hbez : (1 : ℤ) = n * n.gcdA ↑p + ↑p * n.gcdB ↑p := by
    simpa [hcop] using (Int.gcd_eq_gcd_ab n p)
  let pxA : A := ⟨(p : ℤ) • x, by simpa using hpxA⟩
  let s : A :=
    n.gcdA ↑p • a - n.gcdB ↑p • pxA
  have hxs :
      x + (s : G) = n.gcdA ↑p • ((a : G) + n • x) := by
    change x + (n.gcdA ↑p • (a : G) - n.gcdB ↑p • ((p : ℤ) • x)) =
      n.gcdA ↑p • ((a : G) + n • x)
    rw [smul_add, ← mul_zsmul, ← mul_zsmul]
    have hcoeff :
        (1 : ℤ) - n.gcdB ↑p * p = n.gcdA ↑p * n := by
      have hbez' :
          (1 : ℤ) = n.gcdA ↑p * n + n.gcdB ↑p * p := by
        simpa [Int.mul_comm] using hbez
      omega
    calc
      x + (n.gcdA ↑p • (a : G) - (n.gcdB ↑p * p) • x) =
          n.gcdA ↑p • (a : G) +
            ((1 : ℤ) - n.gcdB ↑p * p) • x := by
              rw [sub_zsmul, one_zsmul]
              abel
      _ = n.gcdA ↑p • (a : G) + (n.gcdA ↑p * n) • x := by
            rw [hcoeff]
  have hxsSucc : x + (s : G) ∈
      ulmSubgroup p (Order.succ α) (G := G) := by
    rw [hxs]
    exact (ulmSubgroup p (Order.succ α)).zsmul_mem hz _
  exact (isProper_iff_forall_not_mem_succ p _ hxα hxSucc).1 hxProper s hxsSucc

/-- The elementwise filtration calculation behind the one-generator
extension.  If `x` and `w` have the same exact height, are proper over the
matched subgroups, and satisfy the same `p`-relation, then corresponding
normal forms `a + n • x` and `φ(a) + n • w` lie in exactly the same Ulm
subgroups. -/
lemma proper_adjoin_rep_mem_iff
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {x : G} {w : H} {α β : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w)
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (a : A) (n : ℤ) :
    ((a : G) + n • x ∈ ulmSubgroup p β (G := G)) ↔
      ((φ a : H) + n • w ∈ ulmSubgroup p β (G := H)) := by
  by_cases hn : (p : ℤ) ∣ n
  · -- On multiples of `p` the representative rewrites inside `A`, where `φ`
    -- preserves height by hypothesis.
    obtain ⟨k, rfl⟩ := hn
    let a' : A := a + k • ⟨p • x, hpxA⟩
    have hxrepr : (a : G) + ((p : ℤ) * k) • x = (a' : G) := by
      change (a : G) + ((p : ℤ) * k) • x = (a : G) + k • (p • x)
      simp [mul_zsmul, Int.mul_comm]
    have hwrepr : (φ a : H) + ((p : ℤ) * k) • w = (φ a' : H) := by
      change (φ a : H) + ((p : ℤ) * k) • w = (φ (a + k • ⟨p • x, hpxA⟩) : H)
      rw [map_add, map_zsmul]
      push_cast
      rw [← hpw]
      simp [mul_zsmul, Int.mul_comm]
    rw [hxrepr, hwrepr]
    exact hφ a' β
  · by_cases hβα : β ≤ α
    · -- Below the exact height both `x` and `w` are already in the filtration,
      -- so the multiple is invisible on each side.
      rw [add_zsmul_mem_iff_of_mem p (ulmSubgroup_antitone p hβα hxα) n,
        add_zsmul_mem_iff_of_mem p (ulmSubgroup_antitone p hβα hwα) n]
      exact hφ a β
    · -- Above it, properness forbids either side from reaching `G_β`.
      have hsuccβ : Order.succ α ≤ β := Order.succ_le_iff.mpr (lt_of_not_ge hβα)
      exact iff_of_false
        (fun hmem ↦ not_mem_succ_add_zsmul_of_proper p hxα hxSucc hxProper hpxA a n hn
          (ulmSubgroup_antitone p hsuccβ hmem))
        (fun hmem ↦ not_mem_succ_add_zsmul_of_proper p hwα hwSucc hwProper
            (by rw [hpw]; exact (φ ⟨p • x, hpxA⟩).prop) (φ a) n hn
          (ulmSubgroup_antitone p hsuccβ hmem))

/-- The quotient-built homomorphism on `A + ⟨x⟩` is height-preserving once
the chosen image `w` satisfies Kaplansky's exact-height and properness
conditions. -/
lemma socle_extend_build_map_heightPres
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {x : G} (hx_notin : x ∉ A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w) :
    ∃ φ' : adjoinElem A x →+ (⊤ : AddSubgroup H),
      (∀ a : A,
        (φ' ⟨a, le_adjoinElem (A := A) (g := x) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨x, mem_adjoinElem_right (A := A) x⟩ : H) = w ∧
      IsHeightPresOn p φ' := by
  obtain ⟨φ', hφA, hφx⟩ :=
    socle_extend_build_map (p := p) φ hx_notin hpxA hpw
  refine ⟨φ', hφA, hφx, ?_⟩
  intro z β
  obtain ⟨a, haA, n, hrepr⟩ :=
    (mem_adjoinElem_iff (A := A) (g := x)).1 z.prop
  let aA : A := ⟨a, haA⟩
  let a' : adjoinElem A x :=
    ⟨a, le_adjoinElem (A := A) (g := x) haA⟩
  let x' : adjoinElem A x :=
    ⟨x, mem_adjoinElem_right (A := A) x⟩
  have hz : z = a' + n • x' := by
    apply Subtype.ext
    simpa [a', x'] using hrepr.symm
  have hmap :
      (φ' z : H) = (φ aA : H) + n • w := by
    rw [hz, map_add, map_zsmul]
    change (φ' a' : H) + n • (φ' x' : H) =
      (φ aA : H) + n • w
    rw [show (φ' a' : H) = φ aA by
      simpa [a', aA] using hφA aA]
    rw [show (φ' x' : H) = w by
      simpa [x'] using hφx]
  change (z : G) ∈ ulmSubgroup p β (G := G) ↔
    (φ' z : H) ∈ ulmSubgroup p β (G := H)
  rw [hmap, hz]
  change ((aA : G) + n • x ∈ ulmSubgroup p β (G := G)) ↔
    ((φ aA : H) + n • w ∈ ulmSubgroup p β (G := H))
  exact
    proper_adjoin_rep_mem_iff p φ hφ hxα hxSucc hwα hwSucc
      hxProper hwProper hpxA hpw aA n

/-- Once the target representative required on page 30 has been found, the
actual finite-stage extension is formal algebra: build the quotient map,
restrict its codomain to its range, and use height preservation for
injectivity. -/
lemma kaplansky_extend_one_of_target
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} (hx_notin : x ∉ s.A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ s.A)
    (hpw : p • w = (s.e ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p s.A x) (hwProper : IsProper p s.B w) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨f, hfA, hfx, hfheight⟩ :=
    socle_extend_build_map_heightPres (p := p)
      s.e.toAddMonoidHom s.hφ hx_notin hpxA hpw
      hxα hxSucc hwα hwSucc hxProper hwProper
  let A' : AddSubgroup G := adjoinElem s.A x
  let raw : A' →+ H := (⊤ : AddSubgroup H).subtype.comp f
  let B' : AddSubgroup H := AddMonoidHom.range raw
  have hf_inj : Function.Injective f := IsHeightPresOn.injective (p := p) hG hfheight
  have hrange_inj : Function.Injective raw.rangeRestrict := fun a b hab ↦
    hf_inj (Subtype.ext (by simpa [raw] using congrArg Subtype.val hab))
  have hA'finite : Set.Finite (A' : Set G) := adjoinElem_finite (p := p) hG.primary s.hAfinite x
  let _ : Finite A' := hA'finite.to_subtype
  let s' : UlmStage p (G := G) (H := H) :=
    { A := A'
      B := B'
      hAfinite := hA'finite
      hBfinite := Set.finite_range raw
      e := AddEquiv.ofBijective raw.rangeRestrict
        ⟨hrange_inj, AddMonoidHom.rangeRestrict_surjective raw⟩
      hφ := fun a β ↦ by
        change ((a : A') : G) ∈ ulmSubgroup p β ↔
          (f a : H) ∈ ulmSubgroup p β
        exact hfheight a β }
  have hAA : s.A ≤ s'.A := le_adjoinElem s.A x
  -- Every old target element is the image of its own preimage, which the
  -- extension still sends where `s.e` did.
  have hBB : s.B ≤ s'.B := fun b hb ↦ by
    let a : s.A := s.e.symm ⟨b, hb⟩
    refine ⟨⟨(a : G), le_adjoinElem (A := s.A) (g := x) a.prop⟩, ?_⟩
    change (f ⟨(a : G), le_adjoinElem (A := s.A) (g := x) a.prop⟩ : H) = b
    rw [hfA a]
    simp [a]
  exact ⟨s', hAA, hBB, mem_adjoinElem_right s.A x, fun a ↦ hfA a⟩

omit hp in
/-- A finite coset has a representative satisfying both of Kaplansky's
normalizations: first maximize the height of the representative, then, among
the proper representatives, maximize the height of its `p`-multiple. -/
lemma exists_kaplanskyNormalized
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    ∃ x : G,
      x - g ∈ A ∧
      IsProper p A x ∧
      ∀ y : G, y - g ∈ A → IsProper p A y →
        ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
  have hAne : (A : Set G).Nonempty := ⟨0, A.zero_mem⟩
  obtain ⟨a₀, ha₀A, ha₀max⟩ :=
    Set.exists_max_image (A : Set G) (fun a ↦ ulmHeight p (g + a))
      hAfinite hAne
  have ha₀proper : IsProper p A (g + a₀) := by
    intro a
    have haa : a₀ + (a : G) ∈ A := A.add_mem ha₀A a.prop
    simpa [add_assoc] using ha₀max (a₀ + (a : G)) haa
  let C : Set G := {a | a ∈ A ∧ IsProper p A (g + a)}
  have hCfinite : C.Finite :=
    hAfinite.subset (by
      intro a ha
      exact ha.1)
  have hCne : C.Nonempty := ⟨a₀, ha₀A, ha₀proper⟩
  obtain ⟨a, haC, hamax⟩ :=
    Set.exists_max_image C (fun a ↦ ulmHeight p (p • (g + a)))
      hCfinite hCne
  refine ⟨g + a, by simpa using haC.1, haC.2, ?_⟩
  intro y hyA hyProper
  have hyrepr : g + (y - g) = y := by abel
  have hyC : y - g ∈ C := by
    refine ⟨hyA, ?_⟩
    simpa [hyrepr] using hyProper
  simpa [hyrepr] using hamax (y - g) hyC

omit hp in
/-- Kaplansky's Case I target construction.

If `p • x` has exact height `α+1`, any height-`α` root of its image is
automatically proper over the target stage.  The proof uses the second
normalization of `x` to rule out a higher translate. -/
lemma exists_kaplanskyTarget_caseI
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x))
    (hcaseI :
      p • x ∉ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by
  have hxHeight : ulmHeight p x = (α : WithTop Ordinal.{0}) :=
    ulmHeight_eq_of_mem_not_mem_succ p x α hxα hxSucc
  -- `x ∈ G_α` puts `p • x` in `G_{α+1}`, so its image has a root `w ∈ H_α`.
  have hzSucc : (s.e ⟨p • x, hpxA⟩ : H) ∈ ulmSubgroup p (Order.succ α) (G := H) :=
    (s.hφ_succ _).mp (by rw [ulmSubgroup_succ]; exact ⟨x, hxα, rfl⟩)
  -- Case I says `p • x ∉ G_{α+2}`, so the root has exact height `α`.
  have hzSuccSucc :
      (s.e ⟨p • x, hpxA⟩ : H) ∉ ulmSubgroup p (Order.succ (Order.succ α)) (G := H) :=
    fun hz ↦ hcaseI ((s.hφ_succSucc _).mpr hz)
  rw [ulmSubgroup_succ] at hzSucc
  obtain ⟨w, hwα, hpw⟩ := hzSucc
  have hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H) := fun hw ↦
    hzSuccSucc (by rw [← hpw, ulmSubgroup_succ]; exact ⟨w, hw, rfl⟩)
  refine ⟨w, hpw, hwα, hwSucc, ?_⟩
  -- Properness of `w`: a target translate `w + t` of height `> α` would pull
  -- back to a translate of `x` whose `p`-multiple beats the maximal height.
  refine (isProper_iff_forall_not_mem_succ p s.B hwα hwSucc).2 fun t hwtSucc ↦ ?_
  have htα : (t : H) ∈ ulmSubgroup p α (G := H) := by
    simpa using (ulmSubgroup p α (G := H)).sub_mem
      (ulmSubgroup_antitone p (Order.le_succ α) hwtSucc) hwα
  let a : s.A := s.e.symm t
  have hea : s.e a = t := by simp [a]
  have haα : (a : G) ∈ ulmSubgroup p α (G := G) :=
    (s.hφ_at a).mpr (by simpa [hea] using htα)
  let y : G := x + (a : G)
  have hyα : y ∈ ulmSubgroup p α (G := G) := (ulmSubgroup p α).add_mem hxα haα
  have hySucc : y ∉ ulmSubgroup p (Order.succ α) (G := G) :=
    (isProper_iff_forall_not_mem_succ p s.A hxα hxSucc).1 hxProper a
  have hyHeight : ulmHeight p y = (α : WithTop Ordinal.{0}) :=
    ulmHeight_eq_of_mem_not_mem_succ p y α hyα hySucc
  have hyProper : IsProper p s.A y := fun b ↦ by
    rw [hyHeight, ← hxHeight]
    simpa [y, add_assoc] using hxProper (a + b)
  have hycoset : y - x ∈ s.A := by simp [y]
  have hpyA : p • y ∈ s.A := by
    simpa [y, smul_add] using s.A.add_mem hpxA (s.A.nsmul_mem a.prop p)
  -- The image of `p • y` is `p • (w + t)`, which lies in `H_{α+2}`.
  have hepy : (s.e ⟨p • y, hpyA⟩ : H) = p • (w + (t : H)) := by
    have hdecomp : (⟨p • y, hpyA⟩ : s.A) = ⟨p • x, hpxA⟩ + p • a :=
      Subtype.ext (by simp [y, smul_add])
    rw [hdecomp, map_add, map_nsmul, hea]
    push_cast
    rw [← hpw, smul_add]
  have hpySuccSucc : p • y ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G) :=
    (s.hφ_succSucc _).mpr <| by
      rw [hepy, ulmSubgroup_succ]
      exact ⟨w + (t : H), hwtSucc, rfl⟩
  -- But `y` is a proper translate of `x`, so maximality caps `h(p • y)` at `α+1`.
  exact absurd
    ((coe_le_ulmHeight_of_mem p (p • y) _ hpySuccSucc).trans
      ((hpxMax y hycoset hyProper).trans
        (ulmHeight_le_of_not_mem_succ p (p • x) (Order.succ α) hcaseI)))
    (not_le_of_gt (WithTop.coe_lt_coe.mpr (Order.lt_succ (Order.succ α))))

/-- Kaplansky's Case II target construction.

When `p • x` lies two levels higher, subtract a higher root to expose a
proper exact-height socle element.  The canonical range lemma and equality of
the ordinary Ulm invariant transfer the resulting room to the target side;
adding that target socle element to a higher root gives the required image. -/
lemma exists_kaplanskyTarget_caseII
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hcaseII :
      p • x ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by
  -- Case II gives `p • x = p • v` with `v ∈ G_{α+1}`, so `q = x - v` is a socle
  -- element of exact height `α`, still proper over the stage.
  obtain ⟨v, hvSucc, hpv⟩ := (ulmSubgroup_succ p (Order.succ α) (G := G)) ▸ hcaseII
  let q : G := x - v
  have hpq : p • q = 0 := by simp [q, smul_sub, hpv]
  have hqα : q ∈ ulmSubgroup p α (G := G) :=
    (ulmSubgroup p α).sub_mem hxα (ulmSubgroup_antitone p (Order.le_succ α) hvSucc)
  have hqSucc : q ∉ ulmSubgroup p (Order.succ α) (G := G) := fun hq ↦ hxSucc <| by
    rw [show x = q + v by simp [q]]
    exact (ulmSubgroup p (Order.succ α)).add_mem hq hvSucc
  have hqProper : IsProper p s.A q :=
    (isProper_iff_forall_not_mem_succ p s.A hqα hqSucc).2 fun a hqa ↦
      (isProper_iff_forall_not_mem_succ p s.A hxα hxSucc).1 hxProper a <| by
        rw [show x + (a : G) = q + (a : G) + v by simp [q]; abel]
        exact (ulmSubgroup p (Order.succ α)).add_mem hqa hvSucc
  -- So the source Kaplansky map misses a class; equal Ulm invariants transfer
  -- that room to the target side, producing a proper socle element `w₀`.
  obtain ⟨w₀, hw₀P, hw₀Succ, hw₀Proper⟩ :=
    (kaplanskyMap_not_surjective_iff_proper p s.B α).1
      (kaplansky_not_surjective_transfer p s hinv
        ((kaplanskyMap_not_surjective_iff_proper p s.A α).2
          ⟨q, (mem_pSocleAt p α q).2 ⟨hpq, hqα⟩, hqSucc, hqProper⟩))
  obtain ⟨hpw₀, hw₀α⟩ := (mem_pSocleAt p α w₀).1 hw₀P
  -- The image of `p • x` lies in `H_{α+2}`, so it is `p • w₂` with `w₂ ∈ H_{α+1}`;
  -- adding the socle element gives a root of exact height `α`.
  obtain ⟨w₂, hw₂Succ, hpw₂⟩ :=
    (ulmSubgroup_succ p (Order.succ α) (G := H)) ▸ (s.hφ_succSucc ⟨p • x, hpxA⟩).mp hcaseII
  let w : H := w₀ + w₂
  have hpw : p • w = (s.e ⟨p • x, hpxA⟩ : H) := by simp [w, smul_add, hpw₀, hpw₂]
  have hwα : w ∈ ulmSubgroup p α (G := H) :=
    (ulmSubgroup p α).add_mem hw₀α (ulmSubgroup_antitone p (Order.le_succ α) hw₂Succ)
  have hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H) := fun hw ↦ hw₀Succ <| by
    rw [show w₀ = w - w₂ by simp [w]]
    exact (ulmSubgroup p (Order.succ α)).sub_mem hw hw₂Succ
  refine ⟨w, hpw, hwα, hwSucc, ?_⟩
  -- `w` and `w₀` differ by `w₂ ∈ H_{α+1}`, so `w` inherits `w₀`'s properness.
  refine (isProper_iff_forall_not_mem_succ p s.B hwα hwSucc).2 fun t hwt ↦
    (isProper_iff_forall_not_mem_succ p s.B hw₀α hw₀Succ).1 hw₀Proper t ?_
  rw [show w₀ + (t : H) = w + (t : H) - w₂ by simp [w]; abel]
  exact (ulmSubgroup p (Order.succ α)).sub_mem hwt hw₂Succ

/-- **Kaplansky's one-step extension from an already normalized element.**

The full `kaplansky_extend_one` theorem below first searches a finite coset for
such an `x`.  Once `x` is given with exact height `α`, properness, and the
maximal-`p x` normalization, target selection uses the ordinary Ulm invariant
only at this single height `α`.  This height-local form is the one needed by
the below-base band of the ACM construction, where invariant equality is known
only below a cutoff. -/
lemma kaplansky_extend_one_of_normalized
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} {α : Ordinal.{0}}
    (hinv : ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hx_notin : x ∉ s.A)
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hpxMax : ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
      ulmHeight p (p • y) ≤ ulmHeight p (p • x)) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  obtain ⟨w, hpw, hwα, hwSucc, hwProper⟩ :
      ∃ w : H,
        p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
        w ∈ ulmSubgroup p α (G := H) ∧
        w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
        IsProper p s.B w := by
    by_cases hcaseII :
        p • x ∈
          ulmSubgroup p (Order.succ (Order.succ α)) (G := G)
    · exact exists_kaplanskyTarget_caseII p (UlmStage.at (p := p) s α) hinv hpxA
        hxα hxSucc hxProper hcaseII
    · exact exists_kaplanskyTarget_caseI p (UlmStage.at (p := p) s α) hpxA
        hxα hxSucc hxProper
        hpxMax hcaseII
  exact kaplansky_extend_one_of_target p hG s hx_notin hpxA hpw
    hxα hxSucc hwα hwSucc hxProper hwProper

/-- Kaplansky's page-30 one-step extension.

The input condition `p • g ∈ A` is the precise one-step hypothesis.  A
normalized representative of the coset `g + A` has an attained exact height;
the two target-selection lemmas above then cover whether its `p`-multiple has
height exactly one higher or lies at least two levels higher. -/
lemma kaplansky_extend_one
    (hG : IsReducedPGroup p G)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G)
    (hpgA : p • g ∈ s.A) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  by_cases hgA : g ∈ s.A
  · exact ⟨s, le_rfl, le_rfl, hgA, fun _ ↦ rfl⟩
  obtain ⟨x, hxgA, hxProper, hpxMax'⟩ :=
    exists_kaplanskyNormalized (p := p) s.hAfinite g
  have hxA : x ∉ s.A := by
    intro hx
    apply hgA
    have : g = x - (x - g) := by abel
    rw [this]
    exact s.A.sub_mem hx hxgA
  have hx0 : x ≠ 0 := by
    intro hx
    apply hxA
    simp [hx]
  have hpxA : p • x ∈ s.A := by
    have hdecomp : p • x = p • g + p • (x - g) := by
      rw [smul_sub]
      abel
    rw [hdecomp]
    exact s.A.add_mem hpgA (s.A.nsmul_mem hxgA p)
  obtain ⟨α, hxα, hxSucc⟩ :=
    exists_ulmHeight_eq_of_ne_zero (p := p) hG hx0
  have hpxMax :
      ∀ y : G, y - x ∈ s.A → IsProper p s.A y →
        ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by
    intro y hyxA hyProper
    apply hpxMax' y
    · have : y - g = (y - x) + (x - g) := by abel
      rw [this]
      exact s.A.add_mem hyxA hxgA
    · exact hyProper
  obtain ⟨s', hAA, hBB, hxs', hext⟩ :=
    kaplansky_extend_one_of_normalized p hG s (hinv α) hxA hpxA
      hxα hxSucc hxProper hpxMax
  refine ⟨s', hAA, hBB, ?_, hext⟩
  have hxgA' : x - g ∈ s'.A := hAA hxgA
  have hgrepr : g = x - (x - g) := by abel
  rw [hgrepr]
  exact s'.A.sub_mem hxs' hxgA'

/-- Kaplansky's finite-stage extension theorem.

Starting from finite subgroups related by a height-preserving isomorphism, extend the
stage to cover a prescribed source element.  This is the iterated conclusion used by
the back-and-forth construction, not the single `px ∈ A` step on page 30: primaryness
first supplies a power of `p` lying in `A`, and the proof then applies the single-step
construction repeatedly.  Only the source group must be reduced in this direction;
the target reducedness hypothesis enters when this theorem is applied symmetrically
for the back step.  At each single step `exists_kaplanskyNormalized` supplies
Kaplansky's two normalizations, and Case II uses the canonical range theorem. -/
lemma kaplansky_extend
    (hG : IsReducedPGroup p G)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by
  have extend_pow :
      ∀ n : ℕ, ∀ t : UlmStage p (G := G) (H := H),
        p ^ n • g ∈ t.A →
        ∃ (t' : UlmStage p (G := G) (H := H))
          (hAA : t.A ≤ t'.A) (_hBB : t.B ≤ t'.B),
          g ∈ t'.A ∧
          ∀ a : t.A, (t'.e ⟨a, hAA a.prop⟩ : H) = t.e a := by
    intro n
    induction n with
    | zero =>
        intro t hpow
        have hgA : g ∈ t.A := by simpa using hpow
        exact ⟨t, le_rfl, le_rfl, hgA, fun _ ↦ rfl⟩
    | succ n ih =>
        intro t hpow
        let y : G := p ^ n • g
        have hpyA : p • y ∈ t.A := by
          simpa [y, pow_succ, mul_smul, Nat.mul_comm] using hpow
        obtain ⟨t₁, hAA₁, hBB₁, hy₁, hext₁⟩ :=
          kaplansky_extend_one p hG hinv t y hpyA
        obtain ⟨t₂, hAA₂, hBB₂, hg₂, hext₂⟩ :=
          ih t₁ hy₁
        let hAA : t.A ≤ t₂.A := hAA₁.trans hAA₂
        let hBB : t.B ≤ t₂.B := hBB₁.trans hBB₂
        refine ⟨t₂, hAA, hBB, hg₂, ?_⟩
        intro a
        calc
          (t₂.e ⟨a, hAA a.prop⟩ : H) =
              t₁.e ⟨a, hAA₁ a.prop⟩ := hext₂ ⟨a, hAA₁ a.prop⟩
          _ = t.e a := hext₁ a
  obtain ⟨n, hn⟩ := hG.primary g
  exact extend_pow n s (by simp [hn])

end UlmsTheorem
