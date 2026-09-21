/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.CyclotomicKummerDescent
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
/-!
# Kummer criteria for openness in the norm topology

Let `H ≤ Kˣ` have finite index `n`, with `n` nonzero in `K`, and suppose
that `K` contains a primitive `n`-th root of unity.  Lagrange's theorem
gives `Kˣⁿ ≤ H`; the maximal Kummer extension constructed above has norm
group exactly `Kˣⁿ`.  Hence `H`, transported to the coefficient
group, is open for the norm topology.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K : Type) [Field K]

/-- Prime-to-characteristic Kummer existence in the norm topology, with
cyclotomic descent carried out inside the fixed separable
closure. -/
theorem finiteIndexSubgroup_isNormOpen_of_natCast_ne_zero
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hnK : (H.index : K) ≠ 0) :
    let A := galoisAmbientUnitsRep K (SeparableClosure K)
    let B := closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K))
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := galoisAmbientUnitsRep K (SeparableClosure K)
  let B := closedFixingSubgroup K (SeparableClosure K)
    (⊥ : IntermediateField K (SeparableClosure K))
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  have hindex : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let n : ℕ+ := ⟨H.index, Nat.pos_of_ne_zero hindex⟩
  have hnK' : ((n : ℕ) : K) ≠ 0 := by simpa [n] using hnK
  obtain ⟨F, hnormF⟩ :=
    exists_finiteGalois_normSubgroup_le_powMonoidHom_range K n hnK'
  let E : IntermediateField K (SeparableClosure K) := F
  let : FiniteDimensional K E := F.finiteDimensional
  let : IsGalois K E := F.isGalois
  let L : FiniteGaloisSubextension B := {
    field := closedFixingSubgroup K (SeparableClosure K) E
    below := fixingSubgroupLeBase K (SeparableClosure K) E
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite
      K (SeparableClosure K) E }
  have hnormLe : additiveNormSubgroup K E ≤ H.toAddSubgroup := by
    intro x hx
    change Additive.toMul x ∈ localNormSubgroup K E at hx
    change Additive.toMul x ∈ H
    apply LocalFieldTheory.powMonoidHom_range_index_le Kˣ H
    exact hnormF hx
  have hmap :
      (L.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K E := by
    simpa [A, B, L, e, FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K (SeparableClosure K) E)
  have hLE :
      L.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    intro x hx
    have hxmap : e.symm x ∈
        (L.normSubgroup A).map e.symm.toAddMonoidHom :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap
    exact ⟨e.symm x, hnormLe hxmap, e.apply_symm_apply x⟩
  exact (normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨L, hLE⟩

/-- In characteristic zero every finite-index subgroup is norm-open. -/
theorem finiteIndexSubgroup_isNormOpen_of_charZero
    [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) [H.FiniteIndex] :
    let A := galoisAmbientUnitsRep K (SeparableClosure K)
    let B := closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K))
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  apply finiteIndexSubgroup_isNormOpen_of_natCast_ne_zero K H
  have hindex : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  exact_mod_cast hindex

/-- Prime-to-characteristic Kummer existence: a finite-index subgroup becomes
norm-open once the corresponding roots of unity are in the base field. -/
theorem finiteIndexSubgroup_isNormOpen_of_primitiveRoots
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hnK : (H.index : K) ≠ 0)
    (hmu : (primitiveRoots H.index K).Nonempty) :
    let A := galoisAmbientUnitsRep K (SeparableClosure K)
    let B := closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K))
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := galoisAmbientUnitsRep K (SeparableClosure K)
  let B := closedFixingSubgroup K (SeparableClosure K)
    (⊥ : IntermediateField K (SeparableClosure K))
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  have hindex : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let n : ℕ+ := ⟨H.index, Nat.pos_of_ne_zero hindex⟩
  let Delta := KummerTheory.maximalKummerSubgroup K n
  let E := kummerRadicalExtension
    (K := K) (Omega := SeparableClosure K) n Delta.1
  have hnK' : ((n : ℕ) : K) ≠ 0 := by simpa [n] using hnK
  have hmu' : (primitiveRoots (n : ℕ) K).Nonempty := by
    simpa [n] using hmu
  let : IsGalois K E :=
    kummerRadicalExtension_isGalois
      (K := K) (Omega := SeparableClosure K) n Delta.1
  let : FiniteDimensional K E :=
    KummerTheory.maximalKummerRadicalExtension_finiteDimensional
      (K := K) (Omega := SeparableClosure K) n hnK' hmu'
  let L : FiniteGaloisSubextension B := {
    field := closedFixingSubgroup K (SeparableClosure K) E
    below := fixingSubgroupLeBase K (SeparableClosure K) E
    normal := inferInstance
    finite := baseFixingExtensionQuotient_finite
      K (SeparableClosure K) E }
  have hnormEq :
      localNormSubgroup K E = (powMonoidHom H.index : Kˣ →* Kˣ).range := by
    simpa [E, Delta, n] using
      (maximalKummerNormSubgroup_eq_powMonoidHom_range
        (K := K) (Omega := SeparableClosure K) n hnK' hmu')
  have hnormLe : additiveNormSubgroup K E ≤ H.toAddSubgroup := by
    intro x hx
    change Additive.toMul x ∈ localNormSubgroup K E at hx
    change Additive.toMul x ∈ H
    rw [hnormEq] at hx
    exact LocalFieldTheory.powMonoidHom_range_index_le Kˣ H hx
  have hmap :
      (L.normSubgroup A).map e.symm.toAddMonoidHom =
        additiveNormSubgroup K E := by
    simpa [A, B, L, e, FiniteGaloisSubextension.normSubgroup] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup
        K (SeparableClosure K) E)
  have hLE :
      L.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    intro x hx
    have hxmap : e.symm x ∈
        (L.normSubgroup A).map e.symm.toAddMonoidHom :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap
    exact ⟨e.symm x, hnormLe hxmap, e.apply_symm_apply x⟩
  exact (normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨L, hLE⟩

end LocalClassFieldTheory

end
