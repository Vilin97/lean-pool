/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
/-!
# Localization of the relative integral lattice

Away from the finite exceptional set, this module compares the localized
integer lattice with the integral closure and derives coordinatewise
integrality after localization.
-/

@[expose] public section

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Uniform local denominator statement: outside the bad set a
denominator avoiding the prime carries every algebraic integer into
the scaled lattice. -/
theorem exists_notMem_smul_mem_scaledRelativeIntegerLattice
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (x : 𝓞 L) :
    ∃ d : 𝓞 K, d ∉ w.asIdeal ∧
      d • x ∈
        scaledRelativeIntegerLattice
          (K := K) (L := L) :=
  ⟨scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L),
    scaledRelativeIntegerLatticeAnnihilator_not_mem_of_notMem
      (K := K) (L := L) w hw,
    scaledRelativeIntegerLatticeAnnihilator_smul_mem
      (K := K) (L := L) x⟩

/-- The local ring of `K` at a finite place. -/
abbrev RelativeBaseIntegerLocalization
    (w : HeightOneSpectrum (𝓞 K)) :=
  Localization.AtPrime w.asIdeal

/-- The localization of `𝓞 L` above the same finite place of `K`. -/
abbrev RelativeExtensionIntegerLocalization
    (w : HeightOneSpectrum (𝓞 K)) :=
  Localization
    (Algebra.algebraMapSubmonoid
      (𝓞 L) w.asIdeal.primeCompl)

/-- The canonical localization map, regarded as an `𝓞 K`-linear map. -/
noncomputable def relativeIntegerLocalizationLinearMap
    (w : HeightOneSpectrum (𝓞 K)) :
    𝓞 L →ₗ[𝓞 K]
      RelativeExtensionIntegerLocalization
        (K := K) (L := L) w :=
  (IsScalarTower.toAlgHom
    (𝓞 K) (𝓞 L)
    (RelativeExtensionIntegerLocalization
      (K := K) (L := L) w)).toLinearMap

/-- The span of the scaled integral relative basis after localization
at a finite place of `K`. -/
noncomputable def localizedScaledRelativeIntegerLattice
    (w : HeightOneSpectrum (𝓞 K)) :
    Submodule
      (RelativeBaseIntegerLocalization (K := K) w)
      (RelativeExtensionIntegerLocalization
        (K := K) (L := L) w) :=
  Submodule.span
    (RelativeBaseIntegerLocalization (K := K) w)
    (Set.range fun i :
      RelativeAdeleBasisIndex (K := K) (L := L) =>
        algebraMap (𝓞 L)
          (RelativeExtensionIntegerLocalization
            (K := K) (L := L) w)
          (scaledRelativeExtensionInteger
            (K := K) (L := L) i))

/-- Every element of the global scaled lattice maps into its localized
span. -/
theorem relativeIntegerLocalizationLinearMap_mem_localizedLattice
    (w : HeightOneSpectrum (𝓞 K))
    {x : 𝓞 L}
    (hx : x ∈
      scaledRelativeIntegerLattice
        (K := K) (L := L)) :
    relativeIntegerLocalizationLinearMap
        (K := K) (L := L) w x ∈
      localizedScaledRelativeIntegerLattice
        (K := K) (L := L) w := by
  rw [scaledRelativeIntegerLattice] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · rw [map_zero]
    exact
      Submodule.zero_mem
        (localizedScaledRelativeIntegerLattice
          (K := K) (L := L) w)
  · intro y z _ _ hy hz
    simpa using
      (Submodule.add_mem
        (localizedScaledRelativeIntegerLattice
          (K := K) (L := L) w) hy hz)
  · intro a y _ hy
    have hsmul :=
      (localizedScaledRelativeIntegerLattice
        (K := K) (L := L) w).smul_mem
        (algebraMap (𝓞 K)
          (RelativeBaseIntegerLocalization (K := K) w) a) hy
    simpa [relativeIntegerLocalizationLinearMap] using hsmul

/-- Away from the finite bad set, every algebraic integer of `L` maps
into the span of the scaled relative integral basis. -/
theorem algebraMap_mem_localizedScaledRelativeIntegerLattice_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (x : 𝓞 L) :
    algebraMap (𝓞 L)
        (RelativeExtensionIntegerLocalization
          (K := K) (L := L) w) x ∈
      localizedScaledRelativeIntegerLattice
        (K := K) (L := L) w := by
  let d : 𝓞 K :=
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L)
  have hd : d ∉ w.asIdeal := by
    exact
      scaledRelativeIntegerLatticeAnnihilator_not_mem_of_notMem
        (K := K) (L := L) w hw
  let ds : w.asIdeal.primeCompl := ⟨d, hd⟩
  let hdu :
      IsUnit
        (algebraMap (𝓞 K)
          (RelativeBaseIntegerLocalization (K := K) w) d) :=
    IsLocalization.map_units
      (RelativeBaseIntegerLocalization (K := K) w) ds
  let du :
      (RelativeBaseIntegerLocalization (K := K) w)ˣ :=
    hdu.unit
  have hdx :
      d • x ∈
        scaledRelativeIntegerLattice
          (K := K) (L := L) :=
    scaledRelativeIntegerLatticeAnnihilator_smul_mem
      (K := K) (L := L) x
  have hmap :=
    relativeIntegerLocalizationLinearMap_mem_localizedLattice
      (K := K) (L := L) w hdx
  have hdu_spec :
      (du :
        RelativeBaseIntegerLocalization (K := K) w) =
        algebraMap (𝓞 K)
          (RelativeBaseIntegerLocalization (K := K) w) d := by
    exact hdu.unit_spec
  have hmap' :
      (du :
          RelativeBaseIntegerLocalization (K := K) w) •
        algebraMap (𝓞 L)
          (RelativeExtensionIntegerLocalization
            (K := K) (L := L) w) x ∈
        localizedScaledRelativeIntegerLattice
          (K := K) (L := L) w := by
    simpa [relativeIntegerLocalizationLinearMap, hdu_spec] using hmap
  have hinv :=
    (localizedScaledRelativeIntegerLattice
      (K := K) (L := L) w).smul_mem
      (↑(du⁻¹) :
        RelativeBaseIntegerLocalization (K := K) w) hmap'
  simpa [← smul_smul] using hinv

/-- Outside the explicitly constructed finite set of bad places, the
localized scaled lattice is the whole localization of `𝓞 L`. -/
theorem localizedScaledRelativeIntegerLattice_eq_top_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    localizedScaledRelativeIntegerLattice
        (K := K) (L := L) w = ⊤ := by
  apply top_unique
  have htop :
      Submodule.span
          (RelativeBaseIntegerLocalization (K := K) w)
          (algebraMap (𝓞 L)
            (RelativeExtensionIntegerLocalization
              (K := K) (L := L) w) ''
            (Set.univ : Set (𝓞 L))) =
        ⊤ :=
    span_eq_top_localization_localization
      (RelativeBaseIntegerLocalization (K := K) w)
      w.asIdeal.primeCompl
      (RelativeExtensionIntegerLocalization
        (K := K) (L := L) w)
      (by simp)
  rw [← htop]
  refine Submodule.span_le.2 ?_
  rintro y ⟨x, -, rfl⟩
  exact
    algebraMap_mem_localizedScaledRelativeIntegerLattice_of_notMem
      (K := K) (L := L) w hw x
