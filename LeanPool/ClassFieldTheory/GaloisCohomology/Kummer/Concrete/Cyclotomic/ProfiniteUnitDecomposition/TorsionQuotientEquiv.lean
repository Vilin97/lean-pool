/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion
/-!
# Torsion quotients of a profinite-integer product decomposition
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  continuousMulEquivOfCompactToT2 →
    continuousMulEquivOfCompactToT2


open scoped Topology

noncomputable
section

namespace KummerTheory

open ClassFormation

/-- A topological decomposition `G ≃ ℤ̂ × T` with dense torsion in `T`
identifies the quotient of `G` by the closure of its torsion with `ℤ̂`. -/
noncomputable def torsionQuotientEquivOfZHatMulDecomposition
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T)) :
    G ⧸ (CommGroup.torsion G).topologicalClosure ≃ₜ*
      Multiplicative ZHat := by
  let fstHom :
      Multiplicative ZHat × T →*
        Multiplicative ZHat :=
    MonoidHom.fst _ _
  let freePart : G →* Multiplicative ZHat :=
    fstHom.comp E.toMonoidHom
  have hpreTorsion :
      E ⁻¹'
          (CommGroup.torsion
              (Multiplicative ZHat × T) :
            Set (Multiplicative ZHat × T)) =
        (CommGroup.torsion G : Set G) := by
    ext x
    change IsOfFinOrder (E x) ↔ IsOfFinOrder x
    exact Function.Injective.isOfFinOrder_iff
      (f := E.toMonoidHom) E.injective
  have hpreClosure :
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
        closure (CommGroup.torsion G : Set G) := by
    calc
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
          closure
            (E ⁻¹'
              (CommGroup.torsion
                  (Multiplicative ZHat × T) :
                Set (Multiplicative ZHat × T))) :=
        E.toHomeomorph.preimage_closure _
      _ = closure (CommGroup.torsion G : Set G) := by
        rw [hpreTorsion]
  have hkerFst :
      fstHom.ker =
        (CommGroup.torsion
          (Multiplicative ZHat × T)).topologicalClosure := by
    rw [ClassFormation.topologicalClosure_torsion_zHatMul_prod T hT]
    ext x
    rcases x with ⟨x, y⟩
    change x = 1 ↔
      x ∈ (⊥ : Subgroup (Multiplicative ZHat)) ∧
        y ∈ (⊤ : Subgroup T)
    simp
  have hker :
      freePart.ker =
        (CommGroup.torsion G).topologicalClosure := by
    ext x
    change fstHom (E x) = 1 ↔
      x ∈ closure (CommGroup.torsion G : Set G)
    rw [← MonoidHom.mem_ker, hkerFst]
    exact Set.ext_iff.mp hpreClosure x
  have hsurj : Function.Surjective freePart := by
    intro z
    refine ⟨E.symm (z, 1), ?_⟩
    change fstHom (E (E.symm (z, 1))) = z
    rw [E.apply_symm_apply]
    rfl
  let e :
      G ⧸ (CommGroup.torsion G).topologicalClosure ≃*
        Multiplicative ZHat :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        freePart hsurj)
  exact
    continuousMulEquivOfCompactToT2
        e
        (by
          rw [←
            QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
          exact continuous_fst.comp E.continuous_toFun)

end KummerTheory
