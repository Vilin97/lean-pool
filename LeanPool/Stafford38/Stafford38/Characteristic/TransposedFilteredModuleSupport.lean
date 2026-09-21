/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
import LeanPool.Stafford38.Stafford38.Weyl.TranspositionFiltration

/-!
# Transposition of the filtered right quotient and its support

This file turns the concrete order filtration on a right Weyl quotient into
the corresponding filtration of the transposed left module.  On associated
graded modules the transported action is momentum-sign substitution.  The
resulting support is therefore the inverse image of the original support
under `symbolTranspositionEquiv`.

No noncharacteristic restriction theorem or D-module comparison theorem is
used here.
-/

namespace Stafford38.CharacteristicTransposedFilteredModuleSupport

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.EulerSurjectivity
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylTransposition
open Stafford38.WeylTranspositionFiltration

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-! ## The transported filtered quotient -/

/-- The actual right quotient, regarded as a distinct type so that it can
carry the left Weyl action obtained by transposition. -/
structure TransposedFilteredRightQuotient
    (I : RightIdeal (PresentedWeyl k n)) where
  /-- The underlying class in the original right quotient. -/
  toRightQuotient : RightQuotient I

/-- Forget the transported structure. -/
def transposedFilteredRightQuotientEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    TransposedFilteredRightQuotient k I ≃ RightQuotient I where
  toFun := TransposedFilteredRightQuotient.toRightQuotient
  invFun := TransposedFilteredRightQuotient.mk
  left_inv q := by cases q; rfl
  right_inv _ := rfl

instance (I : RightIdeal (PresentedWeyl k n)) : AddCommGroup
    (TransposedFilteredRightQuotient k I) :=
  Equiv.addCommGroup (transposedFilteredRightQuotientEquiv k I)

/-- Additive form of the forgetful equivalence. -/
def transposedFilteredRightQuotientAddEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    TransposedFilteredRightQuotient k I ≃+ RightQuotient I :=
  Equiv.addEquiv (transposedFilteredRightQuotientEquiv k I)

instance (I : RightIdeal (PresentedWeyl k n)) : Module k
    (TransposedFilteredRightQuotient k I) :=
  (transposedFilteredRightQuotientAddEquiv k I).module k

/-- The quotient's right action restricted along Weyl transposition. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    Module (PresentedWeyl k n) (TransposedFilteredRightQuotient k I) :=
  letI : Module (PresentedWeyl k n) (RightQuotient I) :=
    transposedLeftModule k n (RightQuotient I)
  (transposedFilteredRightQuotientAddEquiv k I).module
    (PresentedWeyl k n)

/-- The canonical identification with the filtered `k`-linear quotient. -/
def filteredQuotientToTransposedLinearEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    FilteredRightQuotient k I ≃ₗ[k] TransposedFilteredRightQuotient k I :=
  (filteredRightQuotientEquivRightQuotient k I).trans
    { (transposedFilteredRightQuotientAddEquiv k I).symm with
      map_smul' := by intro c q; rfl }

/-- The transported degree-`N` filtration piece. -/
def transposedQuotientOrderPiece
    (I : RightIdeal (PresentedWeyl k n)) (N : ℕ) :
    Submodule k (TransposedFilteredRightQuotient k I) :=
  (quotientOrderPiece k I N).map
    (filteredQuotientToTransposedLinearEquiv k I).toLinearMap

/-- The transported quotient filtration is increasing. -/
theorem transposedQuotientOrderPiece_mono
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ} (hNM : N ≤ M) :
    transposedQuotientOrderPiece k I N ≤
      transposedQuotientOrderPiece k I M :=
  Submodule.map_mono (Submodule.map_mono
    (presentedWeightPiece_mono k orderWeight hNM))

@[simp]
theorem filteredQuotientToTransposedLinearEquiv_mk
    (I : RightIdeal (PresentedWeyl k n)) (a : PresentedWeyl k n) :
    filteredQuotientToTransposedLinearEquiv k I
        (Submodule.Quotient.mk a) =
      TransposedFilteredRightQuotient.mk (qmk I a) :=
  rfl

@[simp]
theorem transposed_smul_qmk
    (I : RightIdeal (PresentedWeyl k n))
    (a b : PresentedWeyl k n) :
    a • TransposedFilteredRightQuotient.mk (qmk I b) =
      TransposedFilteredRightQuotient.mk
        (qmk I (b * transpose k n a)) := by
  apply (transposedFilteredRightQuotientEquiv k I).injective
  change rightMul I (transpose k n a) (qmk I b) =
    qmk I (b * transpose k n a)
  exact (qmk_right_mul I b (transpose k n a)).symm

/-- The transported filtration is compatible with the transposed left
action: an operator of order at most `M` sends the degree-`N` piece into the
degree-`N+M` piece. -/
theorem smul_mem_transposedQuotientOrderPiece
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ}
    {a : PresentedWeyl k n} (ha : a ∈ orderPiece k n M)
    {q : TransposedFilteredRightQuotient k I}
    (hq : q ∈ transposedQuotientOrderPiece k I N) :
    a • q ∈ transposedQuotientOrderPiece k I (N + M) := by
  rcases hq with ⟨q₀, hq₀, rfl⟩
  rcases hq₀ with ⟨z, hz, rfl⟩
  refine ⟨(Submodule.Quotient.mk
      (z * transpose k n a) : FilteredRightQuotient k I), ?_, ?_⟩
  · exact ⟨z * transpose k n a,
        mul_mem_orderPiece k hz (transpose_mem_orderPiece k ha), rfl⟩
  · exact (transposed_smul_qmk k I a z).symm

/-- Every quotient class occurs in a finite transported order piece. -/
theorem exists_mem_transposedQuotientOrderPiece
    (I : RightIdeal (PresentedWeyl k n))
    (q : TransposedFilteredRightQuotient k I) :
    ∃ N, q ∈ transposedQuotientOrderPiece k I N := by
  rcases q with ⟨q⟩
  refine Submodule.Quotient.induction_on I q ?_
  intro z
  obtain ⟨N, hz⟩ := exists_mem_orderPiece k z
  refine ⟨N, Submodule.mem_map.mpr ⟨Submodule.Quotient.mk z, ?_, rfl⟩⟩
  exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩

/-- Cyclic good-filtration form: every class in degree `N` is obtained by an
operator in `F_N A` acting on the class of one. -/
theorem exists_filtered_smul_one_of_mem
    (I : RightIdeal (PresentedWeyl k n)) {N : ℕ}
    (q : TransposedFilteredRightQuotient k I)
    (hq : q ∈ transposedQuotientOrderPiece k I N) :
    ∃ a : PresentedWeyl k n, a ∈ orderPiece k n N ∧
      q = a • TransposedFilteredRightQuotient.mk (qmk I 1) := by
  rcases hq with ⟨q₀, hq₀, rfl⟩
  rcases hq₀ with ⟨z, hz, rfl⟩
  refine ⟨transpose k n z, transpose_mem_orderPiece k hz, ?_⟩
  change filteredQuotientToTransposedLinearEquiv k I
      (Submodule.Quotient.mk z) =
    transpose k n z • TransposedFilteredRightQuotient.mk (qmk I 1)
  rw [filteredQuotientToTransposedLinearEquiv_mk,
    transposed_smul_qmk, transpose_transpose, one_mul]

/-! ## The transported associated graded module -/

/-- The actual associated graded object with scalar action restricted along
momentum-sign substitution. -/
structure TransposedOrderAssociatedGradedModule
    (I : RightIdeal (PresentedWeyl k n)) where
  /-- The underlying class in the original associated graded module. -/
  toOrderAssociatedGradedModule : OrderAssociatedGradedModule k I

/-- Forget the transported symbol action. -/
def transposedOrderAssociatedGradedEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    TransposedOrderAssociatedGradedModule k I ≃
      OrderAssociatedGradedModule k I where
  toFun := TransposedOrderAssociatedGradedModule.toOrderAssociatedGradedModule
  invFun := TransposedOrderAssociatedGradedModule.mk
  left_inv q := by cases q; rfl
  right_inv _ := rfl

instance (I : RightIdeal (PresentedWeyl k n)) : AddCommGroup
    (TransposedOrderAssociatedGradedModule k I) :=
  Equiv.addCommGroup (transposedOrderAssociatedGradedEquiv k I)

/-- Additive form of the forgetful equivalence. -/
def transposedOrderAssociatedGradedAddEquiv
    (I : RightIdeal (PresentedWeyl k n)) :
    TransposedOrderAssociatedGradedModule k I ≃+
      OrderAssociatedGradedModule k I :=
  Equiv.addEquiv (transposedOrderAssociatedGradedEquiv k I)

/-- Symbol action on the transposed associated graded module. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    Module (SymbolRing k n) (TransposedOrderAssociatedGradedModule k I) :=
  letI : Module (SymbolRing k n) (OrderAssociatedGradedModule k I) :=
    Module.compHom (OrderAssociatedGradedModule k I)
      (symbolTranspositionEquiv k).toRingEquiv.toRingHom
  (transposedOrderAssociatedGradedAddEquiv k I).module (SymbolRing k n)

@[simp]
theorem transposedSymbol_smul
    (I : RightIdeal (PresentedWeyl k n))
    (P : SymbolRing k n) (q : TransposedOrderAssociatedGradedModule k I) :
    (P • q).toOrderAssociatedGradedModule =
      symbolTransposition k P • q.toOrderAssociatedGradedModule :=
  rfl

/-- The associated graded action is the one induced by the filtered
transposed action: on representatives it multiplies on the right by the
transpose of the acting Weyl operator. -/
theorem transposedSymbol_smul_of_mk_eq_transpose_mul
    (I : RightIdeal (PresentedWeyl k n)) {N M : ℕ}
    (z : orderPiece k n N) (a : orderPiece k n M) :
    (presentedPrincipalComponent k orderWeight M a : SymbolRing k n) •
        TransposedOrderAssociatedGradedModule.mk
          (orderAssociatedGradedOf k I N
            (orderPieceToQuotientGraded k I N z)) =
      TransposedOrderAssociatedGradedModule.mk
        (orderAssociatedGradedOf k I (N + M)
          (orderPieceToQuotientGraded k I (N + M)
            ⟨(z : PresentedWeyl k n) * transpose k n a,
              mul_mem_orderPiece k z.property
                (transpose_mem_orderPiece k a.property)⟩)) := by
  apply (transposedOrderAssociatedGradedEquiv k I).injective
  change symbolTransposition k
      (presentedPrincipalComponent k (@orderWeight n) M a) •
        orderAssociatedGradedOf k I N
          (orderPieceToQuotientGraded k I N z) = _
  rw [← principal_transpose_order k a.property]
  exact smul_orderAssociatedGradedOf_mk_eq_of_mul k I z
    ⟨transpose k n a, transpose_mem_orderPiece k a.property⟩

/-- The annihilator of the transported associated graded module is the
inverse image of the original annihilator under symbol transposition. -/
theorem annihilator_transposedOrderAssociatedGradedModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module.annihilator (SymbolRing k n)
        (TransposedOrderAssociatedGradedModule k I) =
      (Module.annihilator (SymbolRing k n)
        (OrderAssociatedGradedModule k I)).comap
          (symbolTranspositionEquiv k).toRingEquiv.toRingHom := by
  ext P
  simp only [Module.mem_annihilator, Ideal.mem_comap]
  constructor <;> intro h q
  · have hq := congrArg
        TransposedOrderAssociatedGradedModule.toOrderAssociatedGradedModule
        (h (TransposedOrderAssociatedGradedModule.mk q))
    exact hq
  · apply (transposedOrderAssociatedGradedEquiv k I).injective
    exact h q.toOrderAssociatedGradedModule

/-- The original actual associated graded quotient is cyclic and therefore
finite over the symbol ring. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    Module.Finite (SymbolRing k n) (OrderAssociatedGradedModule k I) := by
  let g := orderAssociatedGradedGenerator k I
  let f : SymbolRing k n →ₗ[SymbolRing k n]
      OrderAssociatedGradedModule k I :=
    { toFun := fun P => P • g
      map_add' := by intro P Q; exact add_smul P Q g
      map_smul' := by intro P Q; exact mul_smul P Q g }
  apply Module.Finite.of_surjective f
  intro q
  exact exists_smul_orderAssociatedGradedGenerator k I q

/-- The transported associated graded module remains cyclic, hence finite. -/
noncomputable instance (I : RightIdeal (PresentedWeyl k n)) :
    Module.Finite (SymbolRing k n)
      (TransposedOrderAssociatedGradedModule k I) := by
  let g : TransposedOrderAssociatedGradedModule k I :=
    TransposedOrderAssociatedGradedModule.mk
      (orderAssociatedGradedGenerator k I)
  let f : SymbolRing k n →ₗ[SymbolRing k n]
      TransposedOrderAssociatedGradedModule k I :=
    { toFun := fun P => P • g
      map_add' := by intro P Q; exact add_smul P Q g
      map_smul' := by intro P Q; exact mul_smul P Q g }
  apply Module.Finite.of_surjective f
  intro q
  obtain ⟨P, hP⟩ := exists_smul_orderAssociatedGradedGenerator k I
    q.toOrderAssociatedGradedModule
  refine ⟨symbolTransposition k P, ?_⟩
  apply (transposedOrderAssociatedGradedEquiv k I).injective
  change symbolTransposition k (symbolTransposition k P) •
      orderAssociatedGradedGenerator k I = q.toOrderAssociatedGradedModule
  rw [show symbolTransposition k (symbolTransposition k P) = P by
    exact AlgHom.congr_fun (symbolTransposition_comp_self k) P]
  exact hP

/-- Support of the transposed associated graded module. -/
def transposedOrderAssociatedGradedSupport
    (I : RightIdeal (PresentedWeyl k n)) :
    Set (PrimeSpectrum (SymbolRing k n)) :=
  Module.support (SymbolRing k n)
    (TransposedOrderAssociatedGradedModule k I)

/-- Transposition carries associated-graded support by the expected
momentum-sign automorphism of the symbol spectrum. -/
theorem transposedOrderAssociatedGradedSupport_eq_preimage
    (I : RightIdeal (PresentedWeyl k n)) :
    transposedOrderAssociatedGradedSupport k I =
      PrimeSpectrum.comap
        (symbolTranspositionEquiv k).toRingEquiv.toRingHom ⁻¹'
        Module.support (SymbolRing k n)
          (OrderAssociatedGradedModule k I) := by
  rw [transposedOrderAssociatedGradedSupport,
    Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
    annihilator_transposedOrderAssociatedGradedModule]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage,
    PrimeSpectrum.comap_asIdeal, SetLike.coe_subset_coe]
  constructor
  · intro h P hP
    have hP' : symbolTransposition k P ∈
        (Module.annihilator (SymbolRing k n)
          (OrderAssociatedGradedModule k I)).comap
            (symbolTranspositionEquiv k).toRingEquiv.toRingHom := by
      change symbolTransposition k (symbolTransposition k P) ∈
        Module.annihilator (SymbolRing k n)
          (OrderAssociatedGradedModule k I)
      rwa [show symbolTransposition k (symbolTransposition k P) = P by
        exact AlgHom.congr_fun (symbolTransposition_comp_self k) P]
    exact h hP'
  · intro h P hP
    have hP' : symbolTransposition k P ∈
        Module.annihilator (SymbolRing k n)
          (OrderAssociatedGradedModule k I) := hP
    have h' := h hP'
    change symbolTransposition k (symbolTransposition k P) ∈ p.asIdeal at h'
    rwa [show symbolTransposition k (symbolTransposition k P) = P by
      exact AlgHom.congr_fun (symbolTransposition_comp_self k) P] at h'


end

end Stafford38.CharacteristicTransposedFilteredModuleSupport
