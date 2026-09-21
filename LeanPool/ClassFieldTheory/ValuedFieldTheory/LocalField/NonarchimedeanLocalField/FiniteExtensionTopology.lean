/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Valuation.Extension
/-!
# The canonical topology on a finite extension of a local field

This file packages the spectral norm topology on a finite extension of a
nonarchimedean local field.  The definitions are deliberately explicit: they
let downstream constructions put several finite extensions in one diagram
while using the same topology on every field.
-/

noncomputable section

namespace LocalFieldTheory

open scoped NNReal ValuativeRel

/-- The normed-field structure canonically associated with the native
topology of a nonarchimedean local field. -/
@[reducible]
noncomputable def localFieldNontriviallyNormedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- The native norm obtained from a nonarchimedean local field is
ultrametric.  This is kept as a named companion to
`localFieldNontriviallyNormedField` so that every use of the spectral norm
starts from the same norm and the same ultrametric structure. -/
theorem localFieldIsUltrametricDist
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField K :=
      localFieldNontriviallyNormedField K
    IsUltrametricDist K := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

/-- A finite extension, equipped with the spectral norm extending the native
topology of its nonarchimedean local base field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact spectralNorm.nontriviallyNormedField K L

/-- A finite extension is complete for its canonical spectral norm. -/
theorem finiteExtensionSpectralCompleteSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    CompleteSpace L := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact spectralNorm.completeSpace K L

/-- A finite extension is locally compact for its canonical spectral norm. -/
theorem finiteExtensionSpectralLocallyCompactSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    LocallyCompactSpace L := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (V : Type) [nV : NontriviallyNormedField V]
        [spaceKV : NormedSpace K V] [FiniteDimensional K V] =>
      LocallyCompactSpace.of_finiteDimensional_of_complete K V)
      L (nV := finiteExtensionSpectralNormedField K L)
      (spaceKV := spectralNorm.normedSpace K L)

/-- The spectral norm on a finite extension of a nonarchimedean local field
is ultrametric. -/
theorem finiteExtensionSpectralIsUltrametricDist
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    IsUltrametricDist L := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (F : Type) [nF : NormedField F]
        (h : IsNonarchimedean (norm : F → ℝ)) =>
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h)
      L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (isNonarchimedean_spectralNorm (K := K) (L := L))

/-- The valuative relation induced by the canonical spectral norm. -/
@[reducible]
noncomputable def finiteExtensionSpectralValuativeRel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    ValuativeRel L := by
  letI hUltra := finiteExtensionSpectralIsUltrametricDist K L
  exact ValuativeRel.ofValuation
    (NormedField.valuation (K := L)
      (hK := (finiteExtensionSpectralNormedField K L).toNormedField))

/-- A finite extension with the spectral norm is again a nonarchimedean
local field. -/
theorem finiteExtensionSpectralIsNonarchimedeanLocalField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    IsNonarchimedeanLocalField L := by
  exact
    (fun (F : Type) [nF : NontriviallyNormedField F] [hUltra : IsUltrametricDist F]
        [hCompact : LocallyCompactSpace F] =>
      letI : Valued F ℝ≥0 := NormedField.toValued
      let vL : Valuation F ℝ≥0 := Valued.v
      letI : ValuativeRel F := ValuativeRel.ofValuation vL
      letI : vL.Compatible := Valuation.Compatible.ofValuation vL
      letI : ValuativeRel.IsNontrivial F :=
        (ValuativeRel.isNontrivial_iff_isNontrivial vL).2
          (inferInstanceAs (NormedField.valuation (K := F)).IsNontrivial)
      letI : IsValuativeTopology F :=
        isValuativeTopology_of_valued_ofValuation F ℝ≥0
      show IsNonarchimedeanLocalField F from
        { toIsValuativeTopology := inferInstance
          toLocallyCompactSpace := hCompact
          toIsNontrivial := inferInstance })
      L (nF := finiteExtensionSpectralNormedField K L)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (hCompact := finiteExtensionSpectralLocallyCompactSpace K L)

/-- The valuative relation coming from the spectral norm is the canonical
extension of the native valuation on the local base field. -/
theorem finiteExtensionSpectralValuation_hasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L) := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  have hL :=
    (fun (F : Type) [nF : NormedField F] [hUltra : IsUltrametricDist F]
        (y : F) =>
      let v : Valuation F ℝ≥0 := NormedField.valuation (K := F)
      letI : ValuativeRel F := ValuativeRel.ofValuation v
      letI : v.Compatible := Valuation.Compatible.ofValuation v
      (Valuation.vle_one_iff (ValuativeRel.valuation F) (x := y)).symm.trans
        (Valuation.vle_one_iff v (x := y)))
      L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (algebraMap K L x)
  refine hL.trans ?_
  change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
    ValuativeRel.valuation K x ≤ 1
  rw [spectralNorm_extends (K := K) (L := L) x]
  exact Valued.toNormedField.norm_le_one_iff
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- If `E/K` and `L/K` carry their canonical `K`-spectral norms in a
tower `K \to E \to L`, then the given `E`-algebra structure on `L` is a
normed algebra.  In particular, inclusion and norm maps in finite towers are
continuous for one topology on each field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedAlgebra
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    NormedAlgebra E L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (F : Type) [nF : NormedField F] [aKF : NormedAlgebra K F]
        [Algebra F L] [IsScalarTower K F L] =>
      spectralNorm.normedAlgebra' (K := K) F L)
      E (nF := (finiteExtensionSpectralNormedField K E).toNormedField)
      (aKF := spectralNorm.normedAlgebra K E)

/-- In a finite tower equipped throughout with the spectral norms over its
local base, the upper spectral valuation extends the intermediate spectral
valuation. -/
theorem finiteExtensionSpectralValuation_hasExtension_of_tower
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel E :=
      finiteExtensionSpectralValuativeRel K E
    letI : ValuativeRel L :=
      finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation E)
      (ValuativeRel.valuation L) := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  have hCompare :=
    (fun (F : Type) [nF : NormedField F] [hUltra : IsUltrametricDist F]
        (y : F) =>
      let v : Valuation F ℝ≥0 := NormedField.valuation (K := F)
      letI : ValuativeRel F := ValuativeRel.ofValuation v
      letI : v.Compatible := Valuation.Compatible.ofValuation v
      (Valuation.vle_one_iff (ValuativeRel.valuation F) (x := y)).symm.trans
        (Valuation.vle_one_iff v (x := y)))
  have hL :=
    hCompare L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (algebraMap E L x)
  have hE :=
    hCompare E (nF := (finiteExtensionSpectralNormedField K E).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K E) x
  refine hL.trans (Iff.trans ?_ hE.symm)
  change spectralNorm K L (algebraMap E L x) ≤ 1 ↔
    spectralNorm K E x ≤ 1
  rw [(spectralNorm.eq_of_tower (K := K) (E := E) (L := L) x).symm]

end LocalFieldTheory
