/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
public import Mathlib.RingTheory.DedekindDomain.SInteger
/-!
# Ideles and units with finite support

This file formalizes finite-support objects for ideles and units. Since every
archimedean place is always included, a finite set
`S` below records only its finite places.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The finite ideles that are integral units away from `S`. -/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∉ S →
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' _ _ := Submonoid.one_mem _
  mul_mem' ha hb v hv := Submonoid.mul_mem _
    (ha v hv) (hb v hv)
  inv_mem' ha v hv := Subgroup.inv_mem _
    (ha v hv)

@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T := by
  intro a ha v hv
  exact ha v (fun h => hv (hST h))

theorem mem_supportedAt_nonLocalUnits
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K)
      {v | a v ∉ (v.adicCompletionIntegers K).units} := by
  intro v hv
  simpa using hv

/-- Every finite idele is supported at some finite set of finite places. -/
theorem exists_finset_supportedAt (a : FiniteIdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) := by
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | a v ∉ (v.adicCompletionIntegers K).units}
  have hT : T.Finite := Filter.eventually_cofinite.mp a.2
  exact ⟨hT.toFinset, by
    rw [Set.Finite.coe_toFinset]
    exact mem_supportedAt_nonLocalUnits a⟩

/-- The union of the finite-support subgroups is the full finite idele
group. -/
theorem iSup_finset_supportedAt :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 K)),
      supportedAt (K := K) (S : Set _) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨S, ha⟩ := exists_finset_supportedAt a
  exact Subgroup.mem_iSup_of_mem S ha

/-- The everywhere-integral subgroup is the subgroup supported at the empty
set. -/
theorem supportedAt_empty :
    supportedAt (K := K)
      (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      integralSubgroup (K := K) :=
  by
    ext a
    simp only [mem_supportedAt_iff, Set.mem_empty_iff_false,
      not_false_eq_true, forall_const, mem_integralSubgroup_iff]

/-- For a finite set `S`, the `S`-finite-ideles form an open subgroup. -/
theorem isOpen_supportedAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  change IsOpen {a : FiniteIdeleGroup K | ∀ v, v ∉ (S : Set _) →
    a v ∈ (v.adicCompletionIntegers K).units}
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun v => isOpen_finiteLocalUnits K v)

end FiniteIdeleGroup

namespace IdeleGroup

/-- The group `I_K^S`, with all infinite places included and finite
components integral away from `S`. -/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.supportedAt S)

@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a.2 v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T :=
  Subgroup.comap_mono
    (FiniteIdeleGroup.supportedAt_mono hST)

/-- Every idele lies in `I_K^S` for some finite set `S`. -/
theorem exists_finset_supportedAt (a : IdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) :=
  FiniteIdeleGroup.exists_finset_supportedAt a.2

theorem iSup_finset_supportedAt :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 K)),
      supportedAt (K := K) (S : Set _) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨S, ha⟩ := exists_finset_supportedAt a
  exact Subgroup.mem_iSup_of_mem S ha

theorem supportedAt_empty :
    supportedAt (K := K)
      (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      integralAtFinitePlaces (K := K) :=
  by
    ext a
    simp only [mem_supportedAt_iff, Set.mem_empty_iff_false,
      not_false_eq_true, forall_const]
    rfl

theorem isOpen_supportedAt
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) :=
  (FiniteIdeleGroup.isOpen_supportedAt S).preimage continuous_snd

end IdeleGroup

/-- The group of `S`-units of `K`, for a finite set of finite places.
All infinite places are understood to lie in `S`. -/
abbrev SUnitGroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K

@[simp]
theorem mem_SUnitGroup_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ SUnitGroup (K := K) S ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        v.valuation K x = 1 :=
  Iff.rfl
