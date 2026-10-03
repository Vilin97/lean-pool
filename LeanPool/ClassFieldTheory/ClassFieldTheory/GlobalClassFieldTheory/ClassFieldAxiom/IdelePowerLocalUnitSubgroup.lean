/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
/-!
# Power-local-unit subgroups of the idele group

This module defines the subgroup of ideles that are local powers at selected
places and integral units elsewhere, together with its intersection with
principal ideles and the corresponding subgroup of S-unit powers.
-/

@[expose] public section

open scoped NumberField NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable
section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- Ideles that are local `n`-th powers at the prescribed places and
integral units away from `S ∪ T`. -/
def idelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  (⨅ w : InfinitePlace K,
      ((powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range).comap
        (IdeleGroup.infiniteComponent w)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∈ S),
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range.comap
          (IdeleGroup.finiteComponent v)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∉ S ∪ T),
        (v.adicCompletionIntegers K).units.comap
          (IdeleGroup.finiteComponent v))

open scoped Classical in
/-- Membership in `idelePowerLocalUnitSubgroup` expressed componentwise. -/
theorem mem_idelePowerLocalUnitSubgroup_iff
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ idelePowerLocalUnitSubgroup (K := K) n S T ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          (powMonoidHom (n : ℕ) :
            w.Completionˣ →* w.Completionˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S →
        IdeleGroup.finiteComponent v a ∈
          (powMonoidHom (n : ℕ) :
            (v.adicCompletion K)ˣ →*
              (v.adicCompletion K)ˣ).range) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
        IdeleGroup.finiteComponent v a ∈
          (v.adicCompletionIntegers K).units) := by
  simp only [idelePowerLocalUnitSubgroup, Subgroup.mem_inf,
    Subgroup.mem_iInf, Subgroup.mem_comap, and_assoc]

open scoped Classical in
/-- Field units whose principal ideles lie in the local power-unit
subgroup. -/
def principalIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).comap
    (IdeleGroup.principalIdele K)

open scoped Classical in
/-- The subgroup of field units obtained as `n`-th powers of `U`-units. -/
def sUnitNthPowersInField
    (n : ℕ+)
    (U : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  ((powMonoidHom (n : ℕ) :
      SUnitGroup (K := K) U →*
        SUnitGroup (K := K) U).range).map
    (SUnitGroup (K := K) U).subtype

open scoped Classical in
/-- A field unit is an `n`-th power of an `U`-unit exactly when it is
simultaneously an `U`-unit and an `n`-th power in the field.  The reverse
direction uses the valuation-theoretic saturation of `SUnitGroup`. -/
theorem mem_sUnitNthPowersInField_iff
    (n : ℕ+)
    (U : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) :
    x ∈ sUnitNthPowersInField (K := K) n U ↔
      x ∈ SUnitGroup (K := K) U ∧
        x ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    obtain ⟨z, hz⟩ :=
      (MonoidHom.mem_range
        (G := SUnitGroup (K := K) U)).mp hy
    rw [powMonoidHom_apply] at hz
    subst y
    exact
      (MonoidHom.mem_range
        (G := Kˣ)).mpr ⟨(z : Kˣ), by
          rw [powMonoidHom_apply]
          rfl⟩
  · rintro ⟨hxU, hxPow⟩
    obtain ⟨z, hz⟩ :=
      (MonoidHom.mem_range
        (G := Kˣ)).mp hxPow
    rw [powMonoidHom_apply] at hz
    subst x
    have hzU : z ∈ SUnitGroup (K := K) U :=
      mem_sUnitGroup_of_pow_mem (K := K) U n z hxU
    let zU : SUnitGroup (K := K) U := ⟨z, hzU⟩
    refine ⟨zU ^ (n : ℕ), ?_, ?_⟩
    · exact
        (MonoidHom.mem_range
          (G := SUnitGroup (K := K) U)).mpr
          ⟨zU, by rw [powMonoidHom_apply]⟩
    · simp [zU]

open scoped Classical in
/-- An `n`-th power of an `(S ∪ T)`-unit satisfies all local
power-unit conditions. -/
theorem sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitNthPowersInField (K := K) n (S ∪ T) ≤
      principalIdelePowerLocalUnitSubgroup (K := K) n S T := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx⟩ :=
    (MonoidHom.mem_range
      (G := SUnitGroup (K := K) (S ∪ T))).mp hz
  rw [powMonoidHom_apply] at hx
  subst z
  rw [principalIdelePowerLocalUnitSubgroup,
    Subgroup.mem_comap,
    mem_idelePowerLocalUnitSubgroup_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro w
    apply
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr
    refine
      ⟨IdeleGroup.infiniteComponent w
        (IdeleGroup.principalIdele K (x : Kˣ)), ?_⟩
    simp only [powMonoidHom_apply, map_pow]
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [hxcoe]
  · intro v _
    apply
      (MonoidHom.mem_range
        (G := (v.adicCompletion K)ˣ)).mpr
    refine
      ⟨IdeleGroup.finiteComponent v
        (IdeleGroup.principalIdele K (x : Kˣ)), ?_⟩
    simp only [powMonoidHom_apply, map_pow]
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [hxcoe]
  · intro v hv
    have hxUnit :
        v.valuation K ((x : Kˣ) : K) = 1 :=
      (mem_SUnitGroup_iff (K := K) (S ∪ T) x).mp x.2 v hv
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hxcoe :
        (SUnitGroup (K := K) (S ∪ T)).subtype x = (x : Kˣ) :=
      rfl
    rw [map_pow, hxcoe]
    change
      v.valuation K (((x : Kˣ) : K) ^ (n : ℕ)) = 1
    rw [map_pow, hxUnit, one_pow]

open scoped Classical in
/-- A principal idele satisfying the local power-unit conditions comes
from an `(S ∪ T)`-unit. -/
theorem principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    principalIdelePowerLocalUnitSubgroup (K := K) n S T ≤
      SUnitGroup (K := K) (S ∪ T) := by
  intro y hy
  rw [mem_SUnitGroup_iff]
  intro v hv
  have hAway :=
    ((mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S T
      (IdeleGroup.principalIdele K y)).mp hy).2.2 v hv
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    at hAway
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hAway
  exact hAway

end GlobalClassFieldTheory.ClassFieldAxiom
