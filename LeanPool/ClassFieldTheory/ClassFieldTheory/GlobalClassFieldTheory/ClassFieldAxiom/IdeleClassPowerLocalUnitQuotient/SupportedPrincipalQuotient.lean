/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
/-!
# Supported principal ideles and the idele-class quotient

This file identifies supported principal ideles with the corresponding
`S`-unit group and derives the exact-sequence cardinal identities.
-/

@[expose] public section

open scoped NumberField NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- Principal ideles lying in `I_K^{S ∪ T}`, expressed as a subgroup of
the supported idele group. -/
def supportedPrincipalIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  (IdeleGroup.principalSubgroup K).comap
    (IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype

open scoped Classical in
/-- The diagonal map identifies the `(S ∪ T)`-units with the principal
ideles lying in `I_K^{S ∪ T}`. -/
noncomputable def sUnitEquivSupportedPrincipalIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) (S ∪ T) ≃*
      supportedPrincipalIdeleSubgroup (K := K) S T := by
  let f :
      SUnitGroup (K := K) (S ∪ T) →*
        supportedPrincipalIdeleSubgroup (K := K) S T :=
    { toFun := fun x => by
        have hsupp :
            IdeleGroup.principalIdele K (x : Kˣ) ∈
              IdeleGroup.supportedAt
                (K := K)
                (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
          simpa only [Finset.coe_union] using
            (_root_.principalIdele_mem_supportedAt_iff_sUnit
              (L := K) (S ∪ T) (x : Kˣ)).2 x.property
        refine ⟨⟨IdeleGroup.principalIdele K (x : Kˣ), hsupp⟩, ?_⟩
        exact ⟨(x : Kˣ), rfl⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        simp }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply IdeleGroup.principalIdele_injective K
    have h :=
      congrArg
        (fun z :
          supportedPrincipalIdeleSubgroup (K := K) S T =>
            ((z :
                IdeleGroup.supportedAt
                  (K := K)
                  (S ∪ T :
                    Set (HeightOneSpectrum (𝓞 K)))) :
              IdeleGroup K))
        hxy
    exact h
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hsupp :
        IdeleGroup.principalIdele K x ∈
          IdeleGroup.supportedAt
            (K := K)
            (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [hx]
      exact y.1.property
    have hxS : x ∈ SUnitGroup (K := K) (S ∪ T) := by
      apply
        (_root_.principalIdele_mem_supportedAt_iff_sUnit
          (L := K) (S ∪ T) x).1
      simpa only [Finset.coe_union] using hsupp
    refine ⟨⟨x, hxS⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

open scoped Classical in
/-- The supported-principal-idele equivalence has underlying idele equal
to the principal idele of the original `S`-unit. -/
@[simp]
theorem sUnitEquivSupportedPrincipalIdeleSubgroup_coe
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : SUnitGroup (K := K) (S ∪ T)) :
    (((sUnitEquivSupportedPrincipalIdeleSubgroup
          (K := K) S T x :
        supportedPrincipalIdeleSubgroup (K := K) S T) :
      IdeleGroup.supportedAt
        (K := K)
        (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
      IdeleGroup K) =
        IdeleGroup.principalIdele K (x : Kˣ) :=
  rfl

open scoped Classical in
/-- Under the preceding diagonal equivalence, this is the subgroup of
`(S ∪ T)`-units whose principal ideles belong to `h(S,T)`. -/
def sUnitPrincipalIdelePowerSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (SUnitGroup (K := K) (S ∪ T)) :=
  (principalIdelePowerLocalUnitSubgroup (K := K) n S T).comap
    (SUnitGroup (K := K) (S ∪ T)).subtype

open scoped Classical in
/-- The diagonal equivalence carries the principal part of `h(S,T)`
to the intersection of `h(S,T)` with the supported principal ideles. -/
theorem sUnitPrincipalIdelePowerSubgroup_map
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitPrincipalIdelePowerSubgroup (K := K) n S T).map
        (sUnitEquivSupportedPrincipalIdeleSubgroup
          (K := K) S T).toMonoidHom =
      (supportedIdelePowerLocalUnitSubgroup
        (K := K) n S T).subgroupOf
          (supportedPrincipalIdeleSubgroup (K := K) S T) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' :
      IdeleGroup.principalIdele K (y : Kˣ) ∈
        idelePowerLocalUnitSubgroup (K := K) n S T := by
      exact hy
    change
      (((sUnitEquivSupportedPrincipalIdeleSubgroup
            (K := K) S T y :
          supportedPrincipalIdeleSubgroup (K := K) S T) :
        IdeleGroup.supportedAt
          (K := K)
          (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
        IdeleGroup K) ∈
          idelePowerLocalUnitSubgroup (K := K) n S T
    rw [sUnitEquivSupportedPrincipalIdeleSubgroup_coe]
    exact hy'
  · intro hx
    let e :=
      sUnitEquivSupportedPrincipalIdeleSubgroup
        (K := K) S T
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have hx' :
        e (e.symm x) ∈
          (supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T) := by
      rw [e.apply_symm_apply]
      exact hx
    change
      IdeleGroup.principalIdele K ((e.symm x : _) : Kˣ) ∈
        idelePowerLocalUnitSubgroup (K := K) n S T
    have hxIdele :
        (((e (e.symm x) :
              supportedPrincipalIdeleSubgroup (K := K) S T) :
            IdeleGroup.supportedAt
              (K := K)
              (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :
          IdeleGroup K) ∈
            idelePowerLocalUnitSubgroup (K := K) n S T := by
      exact hx'
    rw [sUnitEquivSupportedPrincipalIdeleSubgroup_coe] at hxIdele
    exact hxIdele

open scoped Classical in
/-- The left term in the supported exact sequence, expressed as the
actual quotient of `(S ∪ T)`-units satisfying the principal
`h(S,T)`-condition. -/
noncomputable def
    sUnitPrincipalIdelePowerQuotientEquivSupportedPrincipalQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := K) (S ∪ T) ⧸
        sUnitPrincipalIdelePowerSubgroup (K := K) n S T ≃*
      supportedPrincipalIdeleSubgroup (K := K) S T ⧸
        (supportedIdelePowerLocalUnitSubgroup
          (K := K) n S T).subgroupOf
            (supportedPrincipalIdeleSubgroup (K := K) S T) :=
  QuotientGroup.congr
    (sUnitPrincipalIdelePowerSubgroup (K := K) n S T)
    ((supportedIdelePowerLocalUnitSubgroup
      (K := K) n S T).subgroupOf
        (supportedPrincipalIdeleSubgroup (K := K) S T))
    (sUnitEquivSupportedPrincipalIdeleSubgroup
      (K := K) S T)
    (sUnitPrincipalIdelePowerSubgroup_map
      (K := K) n S T)

open scoped Classical in
/-- Cardinal form of the diagonal identification of the left term in
the supported exact sequence. -/
theorem card_supportedPrincipalQuotient_eq_sUnitPrincipalQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
          (supportedIdelePowerLocalUnitSubgroup
            (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) =
      Nat.card
        (SUnitGroup (K := K) (S ∪ T) ⧸
          sUnitPrincipalIdelePowerSubgroup (K := K) n S T) :=
  Nat.card_congr
    (sUnitPrincipalIdelePowerQuotientEquivSupportedPrincipalQuotient
      (K := K) n S T).symm.toEquiv

open scoped Classical in
/-- The denominator in the supported realization of
`C_K/C_K(S,T)`: it is generated by `h(S,T)` and the principal ideles
which are supported at `S ∪ T`. -/
def supportedIdeleClassPowerDenominator
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))) :=
  supportedIdelePowerLocalUnitSubgroup (K := K) n S T ⊔
    supportedPrincipalIdeleSubgroup (K := K) S T

section SupportedClassQuotient

open scoped Classical in
local instance supportedClassQuotient_isMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] supportedClassQuotient_isMulCommutative

open scoped Classical in
/-- The natural map from supported ideles to
`C_K/C_K(S,T)`. -/
def supportedIdeleToClassPowerQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) →*
      IdeleClassPowerLocalUnitQuotient (K := K) n S T :=
  (QuotientGroup.mk'
      (ideleClassPowerLocalUnitSubgroup (K := K) n S T)).comp
    ((QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)).comp
      (IdeleGroup.supportedAt
        (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).subtype)

open scoped Classical in
/-- The kernel of the supported class-quotient map is precisely the
subgroup generated by `h(S,T)` and the supported principal ideles. -/
theorem supportedIdeleToClassPowerQuotient_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (supportedIdeleToClassPowerQuotient
      (K := K) n S T).ker =
      supportedIdeleClassPowerDenominator (K := K) n S T := by
  let U :=
    IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))
  let H :=
    supportedIdelePowerLocalUnitSubgroup (K := K) n S T
  let P := supportedPrincipalIdeleSubgroup (K := K) S T
  ext x
  rw [MonoidHom.mem_ker]
  change
    QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) (x : IdeleGroup K)) = 1 ↔
      x ∈ H ⊔ P
  constructor
  · intro hx
    have hxClass :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (x : IdeleGroup K) ∈
          ideleClassPowerLocalUnitSubgroup (K := K) n S T :=
      (QuotientGroup.eq_one_iff _).mp hx
    rcases hxClass with ⟨h, hh, heq⟩
    have hhU :
        h ∈ U :=
      idelePowerLocalUnitSubgroup_le_supportedAt
        (K := K) n S T hh
    let hU : U := ⟨h, hhU⟩
    have hpDiv :
        (x : IdeleGroup K) / h ∈
          IdeleGroup.principalSubgroup K := by
      have hpInv :
          h / (x : IdeleGroup K) ∈
            IdeleGroup.principalSubgroup K :=
        (QuotientGroup.eq_iff_div_mem).mp heq
      simpa [div_eq_mul_inv, mul_comm] using
        (IdeleGroup.principalSubgroup K).inv_mem hpInv
    let pU : U := x / hU
    have hpU : pU ∈ P := by
      exact hpDiv
    apply Subgroup.mem_sup.mpr
    refine ⟨hU, hh, pU, hpU, ?_⟩
    simp [pU]
  · intro hx
    apply (QuotientGroup.eq_one_iff _).mpr
    rcases Subgroup.mem_sup.mp hx with
      ⟨h, hh, p, hp, rfl⟩
    have hhClass :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (h : IdeleGroup K) ∈
          ideleClassPowerLocalUnitSubgroup (K := K) n S T := by
      exact ⟨(h : IdeleGroup K), hh, rfl⟩
    have hpOne :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (p : IdeleGroup K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hp
    have hmul :
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            ((h * p : U) : IdeleGroup K) =
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (h : IdeleGroup K) *
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K)
              (p : IdeleGroup K) := by
      simp
    rw [hmul, hpOne]
    exact
      (ideleClassPowerLocalUnitSubgroup (K := K) n S T).mul_mem
        hhClass
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T).one_mem

open scoped Classical in
/-- If `S ∪ T` is sufficiently large, every class modulo `C_K(S,T)`
has a supported representative. -/
theorem supportedIdeleToClassPowerQuotient_surjective
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Function.Surjective
      (supportedIdeleToClassPowerQuotient
        (K := K) n S T) := by
  intro q
  refine q.inductionOn' ?_
  intro c
  refine c.inductionOn' ?_
  intro a
  have ha :
      a ∈
        IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⊔
            IdeleGroup.principalSubgroup K := by
    rw [hLarge]
    exact Subgroup.mem_top a
  rcases Subgroup.mem_sup.mp ha with
    ⟨u, hu, p, hp, hup⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  change
    QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) u) =
      QuotientGroup.mk'
        (ideleClassPowerLocalUnitSubgroup (K := K) n S T)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)
  rw [← hup, map_mul]
  have hpOne :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) p = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hp
  rw [hpOne]
  simp

open scoped Classical in
/-- Supported realization of the idele-class index quotient. -/
noncomputable def
    supportedIdeleClassPowerQuotientEquiv
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    IdeleGroup.supportedAt
          (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⧸
        supportedIdeleClassPowerDenominator (K := K) n S T ≃*
      IdeleClassPowerLocalUnitQuotient (K := K) n S T :=
  (QuotientGroup.quotientMulEquivOfEq
      (supportedIdeleToClassPowerQuotient_ker
        (K := K) n S T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (supportedIdeleToClassPowerQuotient
        (K := K) n S T)
      (supportedIdeleToClassPowerQuotient_surjective
        (K := K) n S T hLarge))

open scoped Classical in
/-- Cardinal form of the supported realization of
`[C_K:C_K(S,T)]`. -/
theorem card_ideleClassPowerLocalUnitQuotient_eq_supported
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
        (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdeleClassPowerDenominator (K := K) n S T) :=
  Nat.card_congr
    (supportedIdeleClassPowerQuotientEquiv
      (K := K) n S T hLarge).symm.toEquiv

end SupportedClassQuotient

open scoped Classical in
/-- The cardinal identity furnished by the supported exact sequence:

`1 → (I_K^{S∪T} ∩ Kˣ)/(h(S,T) ∩ Kˣ)
   → I_K^{S∪T}/h(S,T)
   → I_K^{S∪T}Kˣ/h(S,T)Kˣ → 1`.

The first factor is written intrinsically as the relative index of
`h(S,T)` in the supported principal ideles. -/
theorem card_supportedPrincipalQuotient_mul_card_supportedClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
          (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
            (supportedIdelePowerLocalUnitSubgroup (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) *
        Nat.card
          (IdeleGroup.supportedAt
                (K := K) (S ∪ T :
                  Set (HeightOneSpectrum (𝓞 K))) ⧸
            supportedIdeleClassPowerDenominator (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  let U :=
    IdeleGroup.supportedAt
      (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K)))
  let H :=
    supportedIdelePowerLocalUnitSubgroup (K := K) n S T
  let P := supportedPrincipalIdeleSubgroup (K := K) S T
  change
    (H.subgroupOf P).index * (H ⊔ P).index = H.index
  have h :=
    Subgroup.relIndex_mul_index
      (H := H) (K := H ⊔ P) le_sup_left
  rw [Subgroup.relIndex_sup_left P H] at h
  exact h

open scoped Classical in
/-- The exact-sequence cardinal identity with the right-hand term
identified with the actual idele-class quotient `C_K/C_K(S,T)`. -/
theorem card_supportedPrincipalQuotient_mul_card_ideleClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (supportedPrincipalIdeleSubgroup (K := K) S T ⧸
            (supportedIdelePowerLocalUnitSubgroup (K := K) n S T).subgroupOf
              (supportedPrincipalIdeleSubgroup (K := K) S T)) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  rw [
    card_ideleClassPowerLocalUnitQuotient_eq_supported
      (K := K) n S T hLarge]
  exact
    card_supportedPrincipalQuotient_mul_card_supportedClassQuotient
      (K := K) n S T

open scoped Classical in
/-- The exact-sequence identity in intrinsic `S`-unit notation. -/
theorem card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hLarge :
      IdeleGroup.supportedAt
            (K := K) (S ∪ T : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤) :
    Nat.card
          (SUnitGroup (K := K) (S ∪ T) ⧸
            sUnitPrincipalIdelePowerSubgroup (K := K) n S T) *
        Nat.card
          (IdeleClassPowerLocalUnitQuotient (K := K) n S T) =
      Nat.card
        (IdeleGroup.supportedAt
              (K := K) (S ∪ T :
                Set (HeightOneSpectrum (𝓞 K))) ⧸
          supportedIdelePowerLocalUnitSubgroup (K := K) n S T) := by
  rw [
    ← card_supportedPrincipalQuotient_eq_sUnitPrincipalQuotient
      (K := K) n S T]
  exact
    card_supportedPrincipalQuotient_mul_card_ideleClassQuotient
      (K := K) n S T hLarge


end GlobalClassFieldTheory.ClassFieldAxiom
