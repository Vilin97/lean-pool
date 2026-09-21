/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.Conductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.LocalConductor
/-!
# Narrow finite and local conductor exponents

The narrow finite conductor is the finite component of the conductor in
the all-real-positive convention.  We formulate its local condition
directly inside the idele class group: insert a higher unit at one finite
place and `1` at every other place, then pass to the idele class group.

The proof is constructive.  One inequality follows by restricting any
global defining modulus to one place.  For the reverse inequality, replace
one exponent of a fixed defining modulus by the local minimum and split an
idele into its one-place component and the remaining defining-modulus
component.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- If a global defining modulus exists, then at every finite place some
higher-unit class subgroup is already contained in the given subgroup. -/
theorem exists_localDefiningExponent
    (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℕ,
      RayClass.localHigherUnitClassSubgroup v n ≤ H := by
  let m := Classical.choose h
  refine ⟨m.finitePart v, ?_⟩
  exact
    (RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
      m v).trans (Classical.choose_spec h)

namespace ConductorialSubgroup

/-- The finite local conductor exponent seen by a conductorial subgroup. -/
noncomputable def narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.find (exists_localDefiningExponent H.1 H.2 v)

/-- The finite local conductor exponent has its defining higher-unit
inclusion. -/
theorem narrowFiniteLocalConductorExponent_spec
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    RayClass.localHigherUnitClassSubgroup v
        (H.narrowFiniteLocalConductorExponent v) ≤ H.1 :=
  Nat.find_spec (exists_localDefiningExponent H.1 H.2 v)

/-- Minimality of the finite local conductor exponent. -/
theorem narrowFiniteLocalConductorExponent_le
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ}
    (hn : RayClass.localHigherUnitClassSubgroup v n ≤ H.1) :
    H.narrowFiniteLocalConductorExponent v ≤ n := by
  exact Nat.find_min'
    (exists_localDefiningExponent H.1 H.2 v) hn

/-- The finite local conductor exponent vanishes exactly when the full
finite-place integral-unit class subgroup lies in the subgroup. -/
theorem narrowFiniteLocalConductorExponent_eq_zero_iff
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteLocalConductorExponent v = 0 ↔
      RayClass.localHigherUnitClassSubgroup v 0 ≤ H.1 := by
  constructor
  · intro hzero
    simpa only [hzero] using
      H.narrowFiniteLocalConductorExponent_spec v
  · intro hlocal
    exact Nat.eq_zero_of_le_zero
      (H.narrowFiniteLocalConductorExponent_le v hlocal)

end ConductorialSubgroup

/-- Replacing one finite exponent of a defining modulus, while retaining its
selected real places, again gives a defining modulus. -/
theorem replaceFiniteExponent_definingModulus
    (H : Subgroup (IdeleClassGroup K))
    (m : RayClass.Modulus K)
    (hm : IsDefiningModulus H m)
    (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ)
    (hn : RayClass.localHigherUnitClassSubgroup v n ≤ H) :
    IsDefiningModulus H
      (m.replaceFinitePart (m.finitePart.update v n)) := by
  let m' : RayClass.Modulus K :=
    m.replaceFinitePart (m.finitePart.update v n)
  change IsDefiningModulus H m'
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rw [IsDefiningModulus, RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    have ha' := (RayClass.Modulus.mem_ideleCongruenceSubgroup_iff m' a).1 ha
    let s : IdeleGroup K :=
      IdeleGroup.finitePlaceIdele v (a.2 v)
    let b : IdeleGroup K := a * s⁻¹
    have hav :
        a.2 v ∈ RayClass.localHigherUnitGroup v n := by
      simpa [m', RayClass.Modulus.replaceFinitePart] using ha'.2 v
    have hsH : q s ∈ H := by
      apply hn
      exact ⟨a.2 v, hav, rfl⟩
    have hbCong : b ∈ m.ideleCongruenceSubgroup := by
      rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
      refine ⟨?_, ?_⟩
      · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
        intro w
        have haw :=
          (RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local
            m' a.1).1 ha'.1 w
        have hlocal :
            m'.localInfiniteCongruenceSubgroup w =
              m.localInfiniteCongruenceSubgroup w := by
          simp [m']
        rw [hlocal] at haw
        change IdeleGroup.infiniteComponent w b ∈
          m.localInfiniteCongruenceSubgroup w
        dsimp only [b]
        rw [map_mul, map_inv]
        dsimp only [s]
        rw [IdeleGroup.finitePlaceIdele_infiniteComponent,
          inv_one, mul_one]
        exact haw
      · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
        intro w
        by_cases hw : w = v
        · subst w
          change IdeleGroup.finiteComponent v b ∈
            RayClass.localHigherUnitGroup v (m.finitePart v)
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.finitePlaceIdele_finiteComponent_same,
            IdeleGroup.finiteComponent_apply,
            mul_inv_cancel]
          exact Subgroup.one_mem _
        · have haw := ha'.2 w
          have hupdate : (m'.finitePart w) = m.finitePart w := by
            simp [m', RayClass.Modulus.replaceFinitePart, hw]
          rw [hupdate] at haw
          change IdeleGroup.finiteComponent w b ∈
            RayClass.localHigherUnitGroup w (m.finitePart w)
          dsimp only [b]
          rw [map_mul, map_inv]
          dsimp only [s]
          rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
              v w (a.2 v) hw,
            inv_one, mul_one,
            IdeleGroup.finiteComponent_apply]
          exact haw
    have hbH : q b ∈ H := by
      apply hm
      rw [RayClass.Modulus.congruenceSubgroup]
      exact ⟨b, Subgroup.mem_sup_left hbCong, rfl⟩
    have hab : a = b * s := by
      dsimp [b]
      group
    change q a ∈ H
    rw [hab, map_mul]
    exact H.mul_mem hbH hsH
  · intro a ha
    change q a ∈ H
    have hqa : q a = 1 :=
      (QuotientGroup.eq_one_iff a).2 ha
    rw [hqa]
    exact H.one_mem

namespace ConductorialSubgroup

/-- The narrow finite conductor exponent equals the independently defined
finite local conductor exponent at every finite place. -/
theorem narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductorExponent v =
      H.narrowFiniteLocalConductorExponent v := by
  apply le_antisymm
  · let m := H.chosenDefiningModulus
    have hm : IsDefiningModulus H.1 m :=
      H.chosenDefiningModulus_spec
    have hlocal :
        RayClass.localHigherUnitClassSubgroup v
            (H.narrowFiniteLocalConductorExponent v) ≤ H.1 :=
      H.narrowFiniteLocalConductorExponent_spec v
    have hupdate :
        IsDefiningModulus H.1
          (m.replaceFinitePart
            (m.finitePart.update v
              (H.narrowFiniteLocalConductorExponent v))) :=
      replaceFiniteExponent_definingModulus H.1 m hm v
        (H.narrowFiniteLocalConductorExponent v) hlocal
    have hle :=
      H.narrowFiniteConductorExponent_le hupdate v
    simpa [m, RayClass.Modulus.replaceFinitePart] using hle
  · obtain ⟨m, hm, hmv⟩ :=
      H.narrowFiniteConductorExponent_spec v
    have hlocal :
        RayClass.localHigherUnitClassSubgroup v (m.finitePart v) ≤ H.1 :=
      (RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup
        m v).trans hm
    exact (H.narrowFiniteLocalConductorExponent_le v hlocal).trans_eq hmv

/-- The exponent of the narrow finite conductor at every finite place is
its finite local conductor exponent. -/
theorem narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductor v =
      H.narrowFiniteLocalConductorExponent v := by
  rw [H.narrowFiniteConductor_apply,
    H.narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent v]

/-- A defining modulus can be chosen to agree with the narrow finite
conductor on any prescribed finite set of finite places and with the
fixed bounding modulus away from that set. -/
theorem exists_definingModulus_finitePart_agrees_on_finset
    (H : ConductorialSubgroup K)
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        (∀ v ∈ s, m.finitePart v = H.narrowFiniteConductor v) ∧
        (∀ v ∉ s, m.finitePart v = H.narrowFiniteConductorBoundingModulus v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine
        ⟨H.chosenDefiningModulus,
          H.chosenDefiningModulus_spec, ?_, ?_⟩
      · intro v hv
        simp at hv
      · intro v _hv
        rfl
  | @insert v s hv ih =>
      obtain ⟨m, hm, hmOn, hmOff⟩ := ih
      let m' : RayClass.Modulus K :=
        m.replaceFinitePart
          (m.finitePart.update v (H.narrowFiniteConductor v))
      have hlocal :
          RayClass.localHigherUnitClassSubgroup v
              (H.narrowFiniteConductor v) ≤ H.1 := by
        rw [H.narrowFiniteConductor_apply,
          H.narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent v]
        exact H.narrowFiniteLocalConductorExponent_spec v
      have hm' : IsDefiningModulus H.1 m' :=
        replaceFiniteExponent_definingModulus H.1 m hm v
          (H.narrowFiniteConductor v) hlocal
      refine ⟨m', hm', ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hws
        · simp [m', RayClass.Modulus.replaceFinitePart]
        · by_cases hwv : w = v
          · subst w
            simp [m', RayClass.Modulus.replaceFinitePart]
          · simpa [m', RayClass.Modulus.replaceFinitePart, hwv] using hmOn w hws
      · intro w hw
        have hwv : w ≠ v := by
          intro hwv
          subst w
          exact hw (Finset.mem_insert_self v s)
        have hws : w ∉ s := by
          intro hws
          exact hw (Finset.mem_insert_of_mem hws)
        simpa [m', RayClass.Modulus.replaceFinitePart, hwv] using hmOff w hws

/-- A defining full modulus can be chosen whose finite part is exactly the
narrow finite conductor. -/
theorem exists_definingModulus_finitePart_eq_narrowFiniteConductor
    (H : ConductorialSubgroup K) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        m.finitePart = H.narrowFiniteConductor := by
  classical
  obtain ⟨m, hm, hmOn, hmOff⟩ :=
    H.exists_definingModulus_finitePart_agrees_on_finset
      H.narrowFiniteConductorBoundingModulus.support
  refine ⟨m, hm, ?_⟩
  ext v
  by_cases hv : v ∈ H.narrowFiniteConductorBoundingModulus.support
  · exact hmOn v hv
  · have hbound : H.narrowFiniteConductorBoundingModulus v = 0 := by
      exact Finsupp.notMem_support_iff.mp hv
    have hmzero : m.finitePart v = 0 :=
      (hmOff v hv).trans hbound
    have hfinite_le :
        H.narrowFiniteConductor v ≤
          H.narrowFiniteConductorBoundingModulus v := by
      simpa only [ConductorialSubgroup.narrowFiniteConductorBoundingModulus] using
        H.narrowFiniteConductor_le H.chosenDefiningModulus_spec v
    rw [hbound] at hfinite_le
    have hfinite_zero : H.narrowFiniteConductor v = 0 :=
      Nat.eq_zero_of_le_zero hfinite_le
    exact hmzero.trans hfinite_zero.symm

/-- The narrow finite conductor reverses inclusions of conductorial
subgroups. -/
theorem narrowFiniteConductor_antitone
    (H J : ConductorialSubgroup K)
    (hHJ : H.1 ≤ J.1) :
    J.narrowFiniteConductor ≤ H.narrowFiniteConductor := by
  intro v
  rw [J.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v,
    H.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v]
  apply J.narrowFiniteLocalConductorExponent_le v
  exact (H.narrowFiniteLocalConductorExponent_spec v).trans hHJ

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
