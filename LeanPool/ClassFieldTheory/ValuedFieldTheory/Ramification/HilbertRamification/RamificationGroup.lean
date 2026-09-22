/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

/-! # Ramification Group -/
namespace RamificationTheory

/-!
# Hilbert ramification theory: ramification subgroup source lemmas

This file records the first structural facts about the classical ramification
subgroup `R_w`.  The key point for the later character map
`I_w -> Hom(Delta/Gamma, lambda*)` is that `R_w` is a normal subgroup of
`I_w`, not merely a subgroup.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A decomposition-group automorphism preserves the principal unit group of
the valuation subring it stabilizes. -/
theorem decompositionGroup_mapEquiv_mem_principalUnitGroup
    (A : _root_.ValuationSubring L) (τ : decompositionGroup K A)
    {u : Lˣ} (hu : u ∈ A.principalUnitGroup) :
    Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) u ∈ A.principalUnitGroup := by
  let uA : A.unitGroup := ⟨u, A.principal_units_le_units hu⟩
  let eA : A ≃+* A := MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
  let uA' : A.unitGroup :=
    A.unitGroupMulEquiv.symm
      (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA))
  have huKer :
      A.unitGroupMulEquiv uA ∈
        (Units.map (IsLocalRing.residue A).toMonoidHom).ker :=
    (A.coe_mem_principalUnitGroup_iff (x := uA)).mp hu
  have huRes :
      IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) = 1 := by
    have h :=
      congrArg
        (fun z : (IsLocalRing.ResidueField A)ˣ =>
          (z : IsLocalRing.ResidueField A))
        (MonoidHom.mem_ker.mp huKer)
    simpa using h
  have hresMapped :
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA)) = 1 := by
    ext
    change
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
            (A.unitGroupMulEquiv uA : A)) = 1
    calc
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv (decompositionGroup K A) A τ
            (A.unitGroupMulEquiv uA : A)) =
          τ • IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        rw [← IsLocalRing.ResidueField.residue_smul]
        rfl
      _ = τ • (1 : IsLocalRing.ResidueField A) := by
        rw [huRes]
      _ = 1 := by
        simp
  have huA' :
      (uA' : Lˣ) ∈ A.principalUnitGroup := by
    rw [A.coe_mem_principalUnitGroup_iff (x := uA')]
    rw [MonoidHom.mem_ker]
    simpa [uA'] using hresMapped
  have huA'_coe :
      (uA' : Lˣ) =
        Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) u := by
    ext
    rfl
  rw [← huA'_coe]
  exact huA'

/-- The normality calculation for the ramification subgroup:
the ramification group is normal in inertia. -/
instance ramificationGroup_normal (A : _root_.ValuationSubring L) :
    (ramificationGroup K A).Normal := by
  refine ⟨?_⟩
  intro σ hσ τ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  intro x
  have hquot :
      automorphismUnitQuotient K A
          (((τ * σ * τ⁻¹ : inertiaGroup K A) : decompositionGroup K A)) x =
        Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv)
          (automorphismUnitQuotient K A (σ : decompositionGroup K A)
            (Units.mapEquiv
              ((((τ⁻¹ : inertiaGroup K A) : decompositionGroup K A) :
                L ≃ₐ[K] L).toMulEquiv) x)) := by
    ext
    simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]
  rw [hquot]
  exact decompositionGroup_mapEquiv_mem_principalUnitGroup (K := K) A
    (τ : decompositionGroup K A)
    (hσ (Units.mapEquiv
      ((((τ⁻¹ : inertiaGroup K A) : decompositionGroup K A) :
        L ≃ₐ[K] L).toMulEquiv) x))

/-- The inertia group is canonically equivalent to its image in the ambient
`K`-automorphism group. -/
def inertiaGroupEquivInAut
    (A : _root_.ValuationSubring L) :
    inertiaGroup K A ≃* inertiaGroupInAut K A :=
  (inertiaGroup K A).equivMapOfInjective
    (decompositionGroup K A).subtype
    Subtype.coe_injective

/-- The ramification subgroup, viewed as a subgroup of ambient inertia. -/
abbrev ramificationGroupInInertiaAut
    (A : _root_.ValuationSubring L) :
    Subgroup (inertiaGroupInAut K A) :=
  Subgroup.map (inertiaGroupEquivInAut (K := K) A).toMonoidHom
    (ramificationGroup K A)

/-- States the theorem `mem_ramificationGroupInInertiaAut_iff`. -/
theorem mem_ramificationGroupInInertiaAut_iff
    (A : _root_.ValuationSubring L) (σ : inertiaGroupInAut K A) :
    σ ∈ ramificationGroupInInertiaAut K A ↔
      ∃ τ : ramificationGroup K A,
        inertiaGroupEquivInAut (K := K) A τ = σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : inertiaGroup K A), τ.property, rfl⟩

/-- The ambient copy of `R_w` is normal inside the ambient copy of `I_w`. -/
instance ramificationGroupInInertiaAut_normal
    (A : _root_.ValuationSubring L) :
    (ramificationGroupInInertiaAut K A).Normal := by
  let e := inertiaGroupEquivInAut (K := K) A
  simpa [ramificationGroupInInertiaAut, e] using
    (Subgroup.Normal.map (ramificationGroup_normal (K := K) A)
      e.toMonoidHom e.surjective)

/-- The tame-inertia quotient identification source:
transport the quotient `I_w/R_w` to the corresponding quotient of the ambient
automorphism subgroups. -/
def inertiaGroupQuotientRamificationEquivInertiaAutQuotient
    (A : _root_.ValuationSubring L) :
    inertiaGroup K A ⧸ ramificationGroup K A ≃*
      inertiaGroupInAut K A ⧸ ramificationGroupInInertiaAut K A :=
  QuotientGroup.congr
    (ramificationGroup K A)
    (ramificationGroupInInertiaAut K A)
    (inertiaGroupEquivInAut (K := K) A)
    rfl

/-- States the theorem `inertiaGroupQuotientRamificationEquivInertiaAutQuotient_mk`. -/
theorem inertiaGroupQuotientRamificationEquivInertiaAutQuotient_mk
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    inertiaGroupQuotientRamificationEquivInertiaAutQuotient
        (K := K) A (QuotientGroup.mk' (ramificationGroup K A) σ) =
      QuotientGroup.mk' (ramificationGroupInInertiaAut K A)
        (inertiaGroupEquivInAut (K := K) A σ) :=
  rfl

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
