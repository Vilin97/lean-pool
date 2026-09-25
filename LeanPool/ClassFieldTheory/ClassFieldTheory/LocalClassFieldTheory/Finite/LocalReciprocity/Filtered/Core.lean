/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Order.Floor.Ring
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Filtration
/-!
# Filtered local reciprocity

The principal-unit filtration transported to a finite Abelian Galois group by
the local Artin map.  Its comparison with upper ramification groups is the
filtered reciprocity theorem; this file first records the Artin side and its
conductor cutoff without assuming that comparison.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalClassFieldTheory LocalFieldTheory RamificationTheory

/-- The image of the `n`-th principal-unit group under finite Abelian local
reciprocity. -/
def artinPrincipalUnitGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) : Subgroup (Gal(L/K)) :=
  (LocalFieldTheory.fieldPrincipalUnits K n).map (abelianLocalArtinMonoidHom K L)

/-- The Artin images of principal units form an antitone filtration. -/
theorem artinPrincipalUnitGroup_antitone
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {m n : ℕ} (hmn : m ≤ n) :
    artinPrincipalUnitGroup K L n ≤ artinPrincipalUnitGroup K L m :=
  Subgroup.map_mono (fieldPrincipalUnits_antitone K hmn)

/-- The Artin image of the `n`-th principal units is trivial exactly from the
conductor exponent onward. -/
theorem artinPrincipalUnitGroup_eq_bot_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) :
    artinPrincipalUnitGroup K L n = ⊥ ↔
      localConductorExponent K L ≤ n := by
  rw [localConductorExponent_le_iff]
  constructor
  · intro h x hx
    rw [← abelianLocalArtinMonoidHom_ker K L, MonoidHom.mem_ker]
    have hmem :
        abelianLocalArtinMonoidHom K L x ∈
          artinPrincipalUnitGroup K L n :=
      ⟨x, hx, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro h
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [← abelianLocalArtinMonoidHom_ker K L] at h
      exact h hx
    · exact bot_le

/-- Before the conductor exponent the Artin image of principal units is
nontrivial, and only then. -/
theorem artinPrincipalUnitGroup_ne_bot_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) :
    artinPrincipalUnitGroup K L n ≠ ⊥ ↔
      n < localConductorExponent K L := by
  simpa only [not_le] using
    not_congr (artinPrincipalUnitGroup_eq_bot_iff K L n)

/-- Restriction along a tower of finite Abelian extensions carries the Artin
image of each principal-unit group onto the corresponding image downstairs. -/
theorem artinPrincipalUnitGroup_map_intermediateFieldRestrict
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (n : ℕ) :
    Subgroup.map
        (intermediateFieldRestrictNormalHom E F hEF)
        (artinPrincipalUnitGroup K F n) =
      artinPrincipalUnitGroup K E n := by
  unfold artinPrincipalUnitGroup
  rw [Subgroup.map_map]
  rw [abelianLocalArtinMonoidHom_restrict K E F hEF]

/-- The real-indexed step filtration obtained by applying local reciprocity
to the principal-unit filtration. -/
def artinPrincipalUnitStepGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) : Subgroup (Gal(L/K)) :=
  natCeilStepFiltration (artinPrincipalUnitGroup K L) t

/-- Restriction along a tower carries the real-indexed Artin principal-unit
step filtration onto the corresponding filtration downstairs. -/
theorem artinPrincipalUnitStepGroup_map_intermediateFieldRestrict
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (t : ℝ) :
    Subgroup.map
        (intermediateFieldRestrictNormalHom E F hEF)
        (artinPrincipalUnitStepGroup K F t) =
      artinPrincipalUnitStepGroup K E t := by
  exact artinPrincipalUnitGroup_map_intermediateFieldRestrict
    K E F hEF ⌈t⌉₊

/-- Filtered reciprocity at nonnegative indices descends through a finite
Abelian tower whenever the chosen upper filtrations are compatible with
restriction.  The index `-1` is outside the principal-unit comparison and is
handled separately in Hasse--Arf. -/
theorem filteredLocalReciprocity_descends
    (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F]
    (upperE : ℝ → Subgroup (Gal(E/K)))
    (upperF : ℝ → Subgroup (Gal(F/K)))
    (hupper : ∀ t,
      Subgroup.map
          (intermediateFieldRestrictNormalHom E F hEF)
          (upperF t) =
        upperE t)
    (hcover : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K F t = upperF t)
    (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K E t = upperE t := by
  rw [← hupper t, ← hcover t ht]
  exact (artinPrincipalUnitStepGroup_map_intermediateFieldRestrict
    K E F hEF t).symm

/-- A jump of the Artin principal-unit step filtration. -/
def IsArtinPrincipalUnitJump
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) : Prop :=
  IsNatCeilStepFiltrationJump (artinPrincipalUnitGroup K L) t

/-- At an integer index, an Artin principal-unit jump is exactly a change
between two consecutive principal-unit images. -/
theorem isArtinPrincipalUnitJump_natCast_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (n : ℕ) :
    IsArtinPrincipalUnitJump K L (n : ℝ) ↔
      artinPrincipalUnitGroup K L n ≠
        artinPrincipalUnitGroup K L (n + 1) := by
  exact isNatCeilStepFiltrationJump_natCast_iff
    (fun _ _ hmn => artinPrincipalUnitGroup_antitone K L hmn) n

/-- Every jump of the Artin principal-unit filtration is an integer.  The
remaining filtered-reciprocity task is to identify this filtration with the
actual upper ramification filtration. -/
theorem isArtinPrincipalUnitJump_integer
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {t : ℝ} (ht : IsArtinPrincipalUnitJump K L t) :
    ∃ n : ℕ, t = n := by
  exact isNatCeilStepFiltrationJump_integer
    (fun _ _ hmn => artinPrincipalUnitGroup_antitone K L hmn) ht

/-- A positive conductor exponent produces a final nontrivial Artin
principal-unit jump one step before the conductor. -/
theorem exists_lastArtinPrincipalUnitJump_of_conductor_pos
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (hcond : 0 < localConductorExponent K L) :
    ∃ n : ℕ,
      localConductorExponent K L = n + 1 ∧
        IsArtinPrincipalUnitJump K L (n : ℝ) := by
  obtain ⟨n, hn⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcond)
  refine ⟨n, hn, ?_⟩
  rw [isArtinPrincipalUnitJump_natCast_iff]
  have hn_ne :
      artinPrincipalUnitGroup K L n ≠ ⊥ := by
    rw [artinPrincipalUnitGroup_ne_bot_iff]
    omega
  have hsucc :
      artinPrincipalUnitGroup K L (n + 1) = ⊥ := by
    rw [artinPrincipalUnitGroup_eq_bot_iff]
    omega
  intro hsame
  apply hn_ne
  rw [hsame, hsucc]

end LocalClassFieldTheory
