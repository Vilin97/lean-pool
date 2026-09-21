/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BaseChange
import Mathlib.FieldTheory.SeparableDegree
/-!
# Finite composita of unramified extensions

The finite case of stability under finite composita says that the composite of two finite
unramified extensions is again unramified.  The proof first applies
the unramified base-change theorem to one extension along the other and then uses transitivity
of residue separability and multiplicativity of the field and residue
degrees.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

open DiscreteValuationField.FieldCompositum

section Tower

variable {K M L : Type u}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]

/-- The finite tower step used in the proof of stability under finite composita.

This is the literal the finite unramified-extension definition argument: separability of the residue
extensions is transitive, while both field degrees and residue degrees are
multiplicative in a tower. -/
theorem finiteUnramifiedExtension_trans
    [FiniteDimensional K M]
    [FiniteDimensional M L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation M)
    (u : LubinTate.Valuations.ExponentialValuation L)
    (hKM : ∀ a : K, w (algebraMap K M a) = v a)
    (hML : ∀ a : M, u (algebraMap M L a) = w a)
    (hKL : ∀ a : K, u (algebraMap K L a) = v a)
    (hM : FiniteUnramifiedExtension v w hKM)
    (hL : FiniteUnramifiedExtension w u hML) :
    FiniteUnramifiedExtension v u hKL := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let U := LubinTate.Valuations.exponentialValuationSubring u
  let iVM := unramifiedValuationRingValuationRingMap v w hKM
  let iWU := unramifiedValuationRingValuationRingMap w u hML
  let iVU := unramifiedValuationRingValuationRingMap v u hKL
  let : IsLocalHom iVM :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hKM
  let : IsLocalHom iWU :=
    unramifiedValuationRingValuationRingMap_isLocalHom w u hML
  let : IsLocalHom iVU :=
    unramifiedValuationRingValuationRingMap_isLocalHom v u hKL
  let : Algebra V W := iVM.toAlgebra
  let : Algebra W U := iWU.toAlgebra
  let : Algebra V U := iVU.toAlgebra
  let k := IsLocalRing.ResidueField V
  let m := IsLocalRing.ResidueField W
  let ell := IsLocalRing.ResidueField U
  let f := IsLocalRing.ResidueField.map iVM
  let g := IsLocalRing.ResidueField.map iWU
  let d := IsLocalRing.ResidueField.map iVU
  let : Algebra k m := f.toAlgebra
  let : Algebra m ell := g.toAlgebra
  let : Algebra k ell := d.toAlgebra
  have hi : iVU = iWU.comp iVM := by
    ext x
    change algebraMap K L (x : K) =
      algebraMap M L (algebraMap K M (x : K))
    exact IsScalarTower.algebraMap_apply K M L (x : K)
  have hd : d = g.comp f := by
    dsimp only [d, g, f]
    simpa only [hi] using
      (IsLocalRing.ResidueField.map_comp iVM iWU)
  let residueTower : IsScalarTower k m ell :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change d x = g (f x)
      rw [hd]
      rfl
  let : IsScalarTower k m ell := residueTower
  let kmResidueModule : Module k m := inferInstance
  let mellResidueModule : Module m ell := inferInstance
  let kellResidueModule : Module k ell := inferInstance
  let kmAlgebraModule : Module k m :=
    (inferInstance : Algebra k m).toModule
  let mellAlgebraModule : Module m ell :=
    (inferInstance : Algebra m ell).toModule
  let kellAlgebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  have hkmModule : kmResidueModule = kmAlgebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hmellModule : mellResidueModule = mellAlgebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hkellModule : kellResidueModule = kellAlgebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hMsep : Algebra.IsSeparable k m := by
    exact hM.1
  have hLsep : Algebra.IsSeparable m ell := by
    exact hL.1
  have hsep : Algebra.IsSeparable k ell :=
    Algebra.IsSeparable.trans k m ell
  have hMdegreeResidue :
      Module.finrank K M =
        @Module.finrank k m _ _ kmResidueModule := by
    exact hM.2
  have hLdegreeResidue :
      Module.finrank M L =
        @Module.finrank m ell _ _ mellResidueModule := by
    exact hL.2
  have hMdegreeAlgebra :
      Module.finrank K M =
        @Module.finrank k m _ _ kmAlgebraModule := by
    calc
      Module.finrank K M =
          @Module.finrank k m _ _ kmResidueModule :=
        hMdegreeResidue
      _ = @Module.finrank k m _ _ kmAlgebraModule := by
        rw [hkmModule]
  have hLdegreeAlgebra :
      Module.finrank M L =
        @Module.finrank m ell _ _ mellAlgebraModule := by
    calc
      Module.finrank M L =
          @Module.finrank m ell _ _ mellResidueModule :=
        hLdegreeResidue
      _ = @Module.finrank m ell _ _ mellAlgebraModule := by
        rw [hmellModule]
  have hdegreeResidue :
      Module.finrank K L =
        @Module.finrank k ell _ _ kellResidueModule := by
    calc
      Module.finrank K L =
          Module.finrank K M * Module.finrank M L :=
        (Module.finrank_mul_finrank K M L).symm
      _ = @Module.finrank k m _ _ kmAlgebraModule *
          @Module.finrank m ell _ _ mellAlgebraModule := by
        rw [hMdegreeAlgebra, hLdegreeAlgebra]
      _ = @Module.finrank k ell _ _ kellAlgebraModule :=
        @Module.finrank_mul_finrank k m ell _ _ _
          kmAlgebraModule mellAlgebraModule kellAlgebraModule
          residueTower _ _ _ _
      _ = @Module.finrank k ell _ _ kellResidueModule := by
        rw [hkellModule]
  refine ⟨hsep, ?_⟩
  change Module.finrank K L =
    @Module.finrank k ell _ _ kellResidueModule
  exact hdegreeResidue

end Tower

section FiniteCompositum

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- Finite common-ambient form of stability under composita.

If `L/K` and `K'/K` are finite unramified extensions inside the same
algebraic ambient field, then their actual compositum `L ⊔ K'` is finite
unramified over `K`.  No separate degree or separability hypothesis is used.
-/
theorem finiteUnramifiedExtension_sup
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    [FiniteDimensional K K']
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hL : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L))
    (hK' : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w K')
      (exponentialValuationRestrict_extends v w hExt K')) :
    let wTop := exponentialValuationRestrict w (L ⊔ K')
    let hBaseTop : ∀ a : K,
        wTop (algebraMap K (L ⊔ K' : IntermediateField K Ω) a) =
          v a := exponentialValuationRestrict_extends v w hExt (L ⊔ K')
    letI : FiniteDimensional K (L ⊔ K' : IntermediateField K Ω) :=
      IntermediateField.finiteDimensional_sup L K'
    FiniteUnramifiedExtension v wTop hBaseTop := by
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w (L ⊔ K')
  let hBaseRight : ∀ a : K,
      wRight (algebraMap K K' a) = v a :=
    exponentialValuationRestrict_extends v w hExt K'
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
        wRight a := by
    intro a
    rfl
  let hBaseTop : ∀ a : K,
      wTop (algebraMap K (L ⊔ K' : IntermediateField K Ω) a) =
        v a := exponentialValuationRestrict_extends v w hExt (L ⊔ K')
  let : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.of_finite K K'
  let : FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
    finiteDimensional_sup_over_right_of_left L K'
  let : FiniteDimensional K (L ⊔ K' : IntermediateField K Ω) :=
    IntermediateField.finiteDimensional_sup L K'
  have hTopRight : FiniteUnramifiedExtension wRight wTop hRightTop := by
    exact finiteUnramifiedExtension_commonTop_of_baseChange
      L K' v w hExt hhens hL
  exact finiteUnramifiedExtension_trans
    v wRight wTop hBaseRight hRightTop hBaseTop hK' hTopRight

end FiniteCompositum

end Valuations
end AlgebraicNumberTheory

end
