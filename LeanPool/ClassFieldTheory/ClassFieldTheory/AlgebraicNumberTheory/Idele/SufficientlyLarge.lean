/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import Mathlib.NumberTheory.NumberField.ClassNumber
/-!
# A sufficiently large finite set of places

Finiteness of the ordinary ideal
class group lets us choose one idele representing each ideal class.  The
union of the (finite) supports of those representatives is a finite set
`S` for which

`I_K = I_K^S Kˣ`.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- A chosen idele representing an ordinary ideal class. -/
def classRepresentative (c : ClassGroup (𝓞 K)) :
    IdeleGroup K :=
  Classical.choose (idealClass_surjective (K := K) c)

@[simp]
private theorem idealClass_classRepresentative
    (c : ClassGroup (𝓞 K)) :
    idealClass (classRepresentative (K := K) c) = c :=
  Classical.choose_spec (idealClass_surjective (K := K) c)

/-- A finite set outside which the chosen representative of `c` is
integral. -/
def classRepresentativeSupport (c : ClassGroup (𝓞 K)) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  Classical.choose
    (exists_finset_supportedAt
      (classRepresentative (K := K) c))

private theorem classRepresentative_mem_support
    (c : ClassGroup (𝓞 K)) :
    classRepresentative (K := K) c ∈
      supportedAt (K := K)
        (classRepresentativeSupport (K := K) c : Set _) :=
  Classical.choose_spec
    (exists_finset_supportedAt
      (classRepresentative (K := K) c))

/-- The union of the supports of one representative of every ordinary
ideal class.  It is finite because the ideal class group is finite. -/
def sufficientlyLargeFiniteSet :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion (classRepresentativeSupport (K := K))

private theorem classRepresentative_mem_sufficientlyLarge
    (c : ClassGroup (𝓞 K)) :
    classRepresentative (K := K) c ∈
      supportedAt (K := K)
        (sufficientlyLargeFiniteSet (K := K) : Set _) := by
  classical
  apply supportedAt_mono
    (S := (classRepresentativeSupport (K := K) c : Set _))
  · intro v hv
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ c, hv⟩
  · exact classRepresentative_mem_support (K := K) c

/-- The ideles supported at `sufficientlyLargeFiniteSet` already map
surjectively to the ordinary ideal class group. -/
theorem idealClass_surjective_on_sufficientlyLarge :
    ∀ c : ClassGroup (𝓞 K),
      ∃ a ∈ supportedAt (K := K)
          (sufficientlyLargeFiniteSet (K := K) : Set _),
        idealClass a = c := by
  intro c
  exact ⟨classRepresentative (K := K) c,
    classRepresentative_mem_sufficientlyLarge (K := K) c,
    idealClass_classRepresentative (K := K) c⟩

/-- For a sufficiently large finite set `S` of
finite places, every idele is the product of an idele integral away from
`S` and a principal idele. -/
theorem supportedAt_sup_principalSubgroup_eq_top :
    supportedAt (K := K)
        (sufficientlyLargeFiniteSet (K := K) : Set _) ⊔
      principalSubgroup K = ⊤ := by
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    (sufficientlyLargeFiniteSet (K := K) : Set _)
  have hintegral :
      integralAtFinitePlaces (K := K) ≤ supportedAt (K := K) S := by
    rw [← supportedAt_empty (K := K)]
    exact supportedAt_mono (K := K) (Set.empty_subset S)
  have hkernel :
      (idealClass (K := K)).ker ≤
        supportedAt (K := K) S ⊔ principalSubgroup K := by
    rw [← ordinaryIdealClassSubgroup_eq_ker (K := K)]
    exact sup_le
      (hintegral.trans le_sup_left)
      le_sup_right
  apply top_unique
  intro a _
  obtain ⟨r, hrS, hr⟩ :=
    idealClass_surjective_on_sufficientlyLarge
      (K := K) (idealClass a)
  have hquot : a * r⁻¹ ∈ (idealClass (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr]
    simp
  have hquot' :
      a * r⁻¹ ∈ supportedAt (K := K) S ⊔ principalSubgroup K :=
    hkernel hquot
  have hr' :
      r ∈ supportedAt (K := K) S ⊔ principalSubgroup K :=
    Subgroup.mem_sup_left hrS
  convert Subgroup.mul_mem _ hquot' hr' using 1
  group

/-- Existential form of the sufficiently-large support theorem. -/
theorem exists_finset_supportedAt_sup_principalSubgroup_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      supportedAt (K := K) (S : Set _) ⊔ principalSubgroup K = ⊤ :=
  ⟨sufficientlyLargeFiniteSet (K := K),
    supportedAt_sup_principalSubgroup_eq_top (K := K)⟩

end IdeleGroup
