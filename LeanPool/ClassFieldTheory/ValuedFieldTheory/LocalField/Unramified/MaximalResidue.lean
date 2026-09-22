/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.ResidueEmbedding
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.FiniteSupport
/-!
# The maximal unramified subextension from residue-field data

Finite support in the compositum reduces the value-group equality and the
forward residue-field inclusion to the corresponding finite statements.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section MaximalUnramifiedSubextensionInvariants

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- the maximal-residue theorem, exact value-group equality for the maximal unramified
subextension. -/
theorem maximalUnramifiedSubextension_valueSubgroup_eq
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    exponentialValueSubgroup
        (exponentialValuationRestrict w
          (maximalUnramifiedSubextension v w hExt)) =
      exponentialValueSubgroup v := by
  classical
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  ext r
  constructor
  · rintro ⟨x, hx0, hxval⟩
    obtain ⟨E, hxE, hEunramified⟩ :=
      exists_finiteUnramifiedSubextension_of_mem_maximal
        v w hExt hhens x.property
    let y : E := ⟨((x : T) : L), hxE⟩
    have hy0 : y ≠ 0 := by
      intro hy
      apply hx0
      apply Subtype.ext
      have hyL := congrArg (fun z : E ↦ (z : L)) hy
      simpa [y] using hyL
    have hyr : r ∈ exponentialValueSubgroup
        (exponentialValuationRestrict w E) := by
      refine ⟨y, hy0, ?_⟩
      exact hxval
    rw [finiteUnramifiedSubextension_valueSubgroup_eq
      v w hExt hEunramified] at hyr
    exact hyr
  · rintro ⟨a, ha0, haval⟩
    let x : T := algebraMap K T a
    have hx0 : x ≠ 0 := (map_ne_zero (algebraMap K T)).2 ha0
    refine ⟨x, hx0, ?_⟩
    change w (algebraMap K L a) = (r : WithTop ℝ)
    rw [hExt]
    exact haval

/-- the maximal-residue theorem, the residue field of `T` embeds into the separable
closure of the base residue field in the ambient residue field. -/
theorem maximalUnramifiedSubextension_residue_fieldRange_le_separableClosure
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let VT := LubinTate.Valuations.exponentialValuationSubring wT
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v wT
      (exponentialValuationRestrict_extends v w hExt T)
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v wT
        (exponentialValuationRestrict_extends v w hExt T)
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let kT := IsLocalRing.ResidueField VT
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k kT := (IsLocalRing.ResidueField.map i).toAlgebra
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    (restrictedResidueAlgHomToAmbient v w hExt T).fieldRange ≤
      separableClosure k ell := by
  classical
  simp only
  intro y hy
  rcases hy with ⟨yT, rfl⟩
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let VT := LubinTate.Valuations.exponentialValuationSubring wT
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective yT
  obtain ⟨E, htE, hEunramified⟩ :=
    exists_finiteUnramifiedSubextension_of_mem_maximal
      v w hExt hhens (show ((t : T) : L) ∈ T from (t : T).property)
  let wE := exponentialValuationRestrict w E
  let VE := LubinTate.Valuations.exponentialValuationSubring wE
  let z : VE :=
    ⟨⟨((t : T) : L), htE⟩, by
      change (0 : WithTop ℝ) ≤ w ((t : T) : L)
      exact t.property⟩
  have hz :=
    finiteUnramifiedSubextension_residue_image_mem_separableClosure
      v w hExt hEunramified (IsLocalRing.residue VE z)
  exact hz

end MaximalUnramifiedSubextensionInvariants

end Valuations
end AlgebraicNumberTheory

end
