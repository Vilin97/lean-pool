/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Representatives
import LeanPool.LocalComplexGeometry.Nullstellensatz.ZeroSetGerms

/-!
# Representatives of a finite ideal generating family

Noetherianity supplies a chosen finite generating set for every ideal.  This
file chooses analytic representatives of those generators and records the
exact pointwise predicate representing the ideal's local zero-set germ.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- The finite type indexing the chosen generators of an ideal. -/
abbrev IdealGeneratorIndex {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) := idealGeneratorFinset I

/-- Chosen analytic representatives of the chosen generators of an ideal. -/
def idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    IdealGeneratorIndex I → ComplexEuclidean n → ℂ :=
  fun f ↦ HolomorphicGerm.representative (f : HolomorphicGerm n)

theorem analyticAt_idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    AnalyticAt ℂ (idealGeneratorRepresentatives I f) 0 :=
  HolomorphicGerm.analyticAt_representative (f : HolomorphicGerm n)

theorem ofFunction_idealGeneratorRepresentatives {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    HolomorphicGerm.ofFunction (idealGeneratorRepresentatives I f)
        (analyticAt_idealGeneratorRepresentatives I f) =
      (f : HolomorphicGerm n) := by
  apply Subtype.ext
  exact HolomorphicGerm.coe_representative (f : HolomorphicGerm n)

/-- Every member of the chosen generating finset belongs to the ideal it
generates. -/
theorem idealGenerator_mem {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (f : IdealGeneratorIndex I) :
    (f : HolomorphicGerm n) ∈ I := by
  have hle : Ideal.span
      (idealGeneratorFinset I : Set (HolomorphicGerm n)) ≤ I :=
    (span_idealGeneratorFinset I).le
  exact hle (Ideal.subset_span f.property)

/-- Pointwise representative of the ideal zero-set germ furnished by the
chosen finite generating family. -/
def idealGeneratorZeroPredicate {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) (z : ComplexEuclidean n) : Prop :=
  ∀ f : IdealGeneratorIndex I, idealGeneratorRepresentatives I f z = 0

/-- The canonical finite-generator predicate represents the abstract local
zero-set germ of the ideal. -/
theorem idealZeroSetGerm_eq_generatorZeroPredicate {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    idealZeroSetGerm I =
      (idealGeneratorZeroPredicate I : LocalSetGerm n) := by
  calc
    idealZeroSetGerm I = finiteCommonZeroSet (idealGeneratorFinset I) := rfl
    _ = fintypeCommonZeroSet
        (fun f : IdealGeneratorIndex I ↦ (f : HolomorphicGerm n)) :=
      finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype
        (idealGeneratorFinset I)
    _ = fintypeCommonZeroSet
        (fun f : IdealGeneratorIndex I ↦
          HolomorphicGerm.ofFunction (idealGeneratorRepresentatives I f)
            (analyticAt_idealGeneratorRepresentatives I f)) := by
      congr 1
      funext f
      exact (ofFunction_idealGeneratorRepresentatives I f).symm
    _ = (idealGeneratorZeroPredicate I : LocalSetGerm n) := by
      rw [fintypeCommonZeroSet_ofFunction
        (idealGeneratorRepresentatives I)
        (analyticAt_idealGeneratorRepresentatives I)]
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun _ ↦ propext (by
        simp only [idealGeneratorZeroPredicate])

/-- A chosen representative of any ideal member vanishes on the pointwise
finite-generator predicate, on one neighborhood of the origin. -/
theorem eventually_representative_eq_zero_of_mem_ideal
    {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (f : HolomorphicGerm n) (hf : f ∈ I) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z →
        HolomorphicGerm.representative f z = 0 := by
  have hzero : idealZeroSetGerm I ≤ germZeroLocus f :=
    idealZeroSetGerm_le_germZeroLocus_of_mem I hf
  rw [idealZeroSetGerm_eq_generatorZeroPredicate I] at hzero
  have hrep := HolomorphicGerm.coe_representative f
  unfold germZeroLocus at hzero
  rw [← hrep] at hzero
  change
    (idealGeneratorZeroPredicate I : LocalSetGerm n) ≤
      ((fun z ↦ HolomorphicGerm.representative f z = 0) :
        LocalSetGerm n) at hzero
  rw [Filter.Germ.coe_le] at hzero
  exact hzero

/-- Equality modulo an ideal makes chosen representatives equal on that
ideal's local zero set, after shrinking once. -/
theorem eventually_representatives_eq_of_quotient_eq
    {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (f g : HolomorphicGerm n)
    (hfg : Ideal.Quotient.mk I f = Ideal.Quotient.mk I g) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate I z →
        HolomorphicGerm.representative f z =
          HolomorphicGerm.representative g z := by
  have hsub : f - g ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hfg, sub_self]
  have hzero := eventually_representative_eq_zero_of_mem_ideal I (f - g) hsub
  have hrepSub :
      ((HolomorphicGerm.representative (f - g) :
          ComplexEuclidean n → ℂ) : FunctionGerm n) =
        (((fun z ↦ HolomorphicGerm.representative f z -
            HolomorphicGerm.representative g z) :
          ComplexEuclidean n → ℂ) : FunctionGerm n) := by
    calc
      _ = ((f - g : HolomorphicGerm n) : FunctionGerm n) :=
        HolomorphicGerm.coe_representative (f - g)
      _ = (f : FunctionGerm n) - (g : FunctionGerm n) := rfl
      _ = (HolomorphicGerm.representative f : FunctionGerm n) -
          (HolomorphicGerm.representative g : FunctionGerm n) := by
        rw [HolomorphicGerm.coe_representative f,
          HolomorphicGerm.coe_representative g]
      _ = _ := (Filter.Germ.coe_sub _ _).symm
  have hsubeq : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      HolomorphicGerm.representative (f - g) z =
        HolomorphicGerm.representative f z -
          HolomorphicGerm.representative g z :=
    Filter.Germ.coe_eq.mp hrepSub
  filter_upwards [hzero, hsubeq] with z hz hzeq
  intro hZ
  exact sub_eq_zero.mp (hzeq ▸ hz hZ)

end

end LocalComplexGeometry
