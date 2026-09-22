/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Value-group invariants of finite unramified extensions

The first finite step in the unramified base-change theorem is forced already by
  the finite unramified-extension definition
and the fundamental inequality of the fundamental inequality.  The actual quotient of
value groups is finite; degree equality then forces its cardinality to be one,
and hence the source and target value subgroups coincide.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open Module

section FiniteValuedExtensionInvariants

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

omit [Algebra K L] in
/-- Every class of the actual value-group quotient has a representative in
`Lˣ`.  This is the public representative source needed to apply the arbitrary
linear-independence theorem from the fundamental inequality. -/
theorem exponentialValueCoset_units_surjective
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L) :
    Function.Surjective
      (fun x : Lˣ ↦ exponentialValueCoset v w (x : L) x.ne_zero) := by
  intro q
  obtain ⟨gamma, hgamma⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, hx, hvalue⟩ := gamma.property
  refine ⟨Units.mk0 x hx, ?_⟩
  rw [← hgamma]
  unfold exponentialValueCoset
  apply congrArg QuotientAddGroup.mk
  apply Subtype.ext
  simp [hvalue]

/-- For a finite-dimensional valued extension, the actual quotient
`w(Lˣ) / v(Kˣ)` is finite.

The proof is the one-element residue-lift specialization of the fundamental inequality:
representatives of distinct value cosets form a linearly independent family
over `K`, so their indexing type is finite in the finite-dimensional space
`L`. -/
theorem exponentialValueGroupQuotient_finite_of_finiteDimensional
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    Finite (ExponentialValueGroupQuotient v w) := by
  classical
  let Q := ExponentialValueGroupQuotient v w
  have hsur : Function.Surjective
      (fun x : Lˣ ↦ exponentialValueCoset v w (x : L) x.ne_zero) :=
    exponentialValueCoset_units_surjective v w
  let sigma : Q → Lˣ := fun q ↦ Classical.choose (hsur q)
  let pi : Q → L := fun q ↦ (sigma q : L)
  have hpi0 : ∀ q, pi q ≠ 0 := fun q ↦ (sigma q).ne_zero
  have hpiClass : ∀ q,
      exponentialValueCoset v w (pi q) (hpi0 q) = q := by
    intro q
    exact Classical.choose_spec (hsur q)
  have hpiInjective : Function.Injective
      (fun q ↦ exponentialValueCoset v w (pi q) (hpi0 q)) := by
    intro q r hqr
    simpa only [hpiClass] using hqr
  have hpiDistinct : DistinctExponentialValueCosetRepresentatives v w pi :=
    distinctExponentialValueCosetRepresentatives_of_injective
      v w hExt pi hpi0 hpiInjective
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  have honeLI : LinearIndependent (IsLocalRing.ResidueField V)
      (fun _ : Unit ↦ IsLocalRing.residue W (1 : W)) := by
    rw [linearIndependent_unique_iff]
    simp
  have hprodQ : LinearIndependent K
      (fun p : Q × Unit ↦
        (((1 : LubinTate.Valuations.exponentialValuationSubring w) : L) * pi p.1)) :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent_arbitrary
      v w hExt pi hpiDistinct
        (fun _ : Unit ↦ (1 : LubinTate.Valuations.exponentialValuationSubring w)) honeLI
  exact
    (hprodQ.comp (fun q ↦ (q, ())) (by
      intro q r hqr
      exact congrArg Prod.fst hqr)).finite

/-- The value-group ramification index of a finite-dimensional exact valued
extension is positive. -/
theorem exponentialRamificationIndex_pos_of_finiteDimensional
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    0 < exponentialRamificationIndex v w := by
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  let : Nonempty (ExponentialValueGroupQuotient v w) :=
    ⟨QuotientAddGroup.mk (0 : exponentialValueSubgroup w)⟩
  unfold exponentialRamificationIndex
  exact Nat.card_pos

/-- Lifts to the target valuation ring of an arbitrary residue-field basis
are linearly independent over the base field.

This is the one-value-coset specialization of the public arbitrary-index
linear-independence theorem in the fundamental inequality.  No finiteness or
separability hypothesis on `L/K` is used. -/
theorem residueBasisLifts_linearIndependent
    {J : Type*}
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (beta :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := unramifiedValuationRingValuationRingMap v w hExt
      letI : IsLocalHom i :=
        unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      Basis J (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W))
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let W := LubinTate.Valuations.exponentialValuationSubring w
      ∀ j, IsLocalRing.residue W (omega j) = beta j) :
    LinearIndependent K (fun j ↦ (omega j : L)) := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  have homegaLI : LinearIndependent (IsLocalRing.ResidueField V)
      (fun j ↦ IsLocalRing.residue W (omega j)) := by
    rw [show (fun j ↦ IsLocalRing.residue W (omega j)) = beta from
      funext homega]
    exact beta.linearIndependent
  let piOne : Unit → L := fun _ ↦ 1
  have hpiOne : DistinctExponentialValueCosetRepresentatives v w piOne := by
    refine ⟨by intro; simp [piOne], ?_⟩
    intro a b hab
    exact (hab (Subsingleton.elim a b)).elim
  have hprod : LinearIndependent K
      (fun p : Unit × J ↦ (omega p.2 : L) * piOne p.1) :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent_arbitrary
      v w hExt piOne hpiOne omega homegaLI
  have hcomp := hprod.comp (fun j ↦ ((), j)) (by
    intro a b hab
    exact congrArg Prod.snd hab)
  simpa only [Function.comp_def, piOne, mul_one] using hcomp

/-- In every finite-dimensional valued field extension, the actual residue
extension is finite-dimensional.  Its finiteness is produced by lifting a
chosen residue basis and applying the preceding linear-independence theorem. -/
theorem residueExtension_finiteDimensional_of_finiteDimensional
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    letI : Algebra V W := i.toAlgebra
    letI : Algebra (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W) :=
      (IsLocalRing.ResidueField.map i).toAlgebra
    FiniteDimensional (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  let J := Module.Free.ChooseBasisIndex k ell
  let beta : Basis J k ell := Module.Free.chooseBasis k ell
  let omega : J → W := fun j ↦
    Classical.choose (IsLocalRing.residue_surjective (beta j))
  have homega : ∀ j, IsLocalRing.residue W (omega j) = beta j := by
    intro j
    exact Classical.choose_spec (IsLocalRing.residue_surjective (beta j))
  have hli : LinearIndependent K (fun j ↦ (omega j : L)) :=
    residueBasisLifts_linearIndependent v w hExt beta omega homega
  have hfiniteJ : Finite J := hli.finite
  let : Finite J := hfiniteJ
  exact beta.finiteDimensional_of_finite

/-- The residue degree of a finite-dimensional exact valued extension is
positive. -/
theorem exponentialResidueDegree_pos_of_finiteDimensional
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    0 < exponentialResidueDegree v w hExt := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  let : FiniteDimensional (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    residueExtension_finiteDimensional_of_finiteDimensional v w hExt
  change 0 < Module.finrank (IsLocalRing.ResidueField V)
    (IsLocalRing.ResidueField W)
  exact Module.finrank_pos

/-- The value-group ramification index of a finite-dimensional exact valued
extension is at most its field degree. -/
theorem exponentialRamificationIndex_le_finrank
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    exponentialRamificationIndex v w ≤ Module.finrank K L := by
  exact (Nat.le_mul_of_pos_right _
    (exponentialResidueDegree_pos_of_finiteDimensional v w hExt)).trans
      (ramificationInvariants_fundamental_inequality v w hExt)

/-- Under the finite unramified-extension definition, every residue basis has the same
cardinality as the
field degree.  The statement uses `Nat.card`, so no finiteness assumption on
the chosen index type is added to the theorem boundary. -/
theorem finiteUnramifiedExtension_residueBasis_card_eq_finrank
    [FiniteDimensional K L] {J : Type*}
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hUnramified : FiniteUnramifiedExtension v w hExt)
    (beta :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := unramifiedValuationRingValuationRingMap v w hExt
      letI : IsLocalHom i :=
        unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      Basis J (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W))
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let W := LubinTate.Valuations.exponentialValuationSubring w
      ∀ j, IsLocalRing.residue W (omega j) = beta j) :
    Nat.card J = Module.finrank K L := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  have hli : LinearIndependent K (fun j ↦ (omega j : L)) :=
    residueBasisLifts_linearIndependent v w hExt beta omega homega
  have hfiniteJ : Finite J := hli.finite
  let : Finite J := hfiniteJ
  let : Fintype J := Fintype.ofFinite J
  have hresfinite : FiniteDimensional k ell :=
    beta.finiteDimensional_of_finite
  let : FiniteDimensional k ell := hresfinite
  have hdegree :=
    finiteUnramifiedExtension_degree_eq_residueDegree
      v w hExt hUnramified
  change Module.finrank K L = Module.finrank k ell at hdegree
  calc
    Nat.card J = Fintype.card J := Nat.card_eq_fintype_card
    _ = Module.finrank k ell := (Module.finrank_eq_card_basis beta).symm
    _ = Module.finrank K L := hdegree.symm

/-- Valuation-ring lifts of any chosen residue basis form a basis of `L/K`
for a finite unramified extension.  Finiteness and nonemptiness of the index
type are derived internally rather than assumed. -/
theorem exists_basis_eq_residueBasisLifts_of_finiteUnramifiedExtension
    [FiniteDimensional K L] {J : Type*}
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hUnramified : FiniteUnramifiedExtension v w hExt)
    (beta :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := unramifiedValuationRingValuationRingMap v w hExt
      letI : IsLocalHom i :=
        unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      Basis J (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W))
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let W := LubinTate.Valuations.exponentialValuationSubring w
      ∀ j, IsLocalRing.residue W (omega j) = beta j) :
    ∃ b : Basis J K L, ∀ j, b j = (omega j : L) := by
  have hli : LinearIndependent K (fun j ↦ (omega j : L)) :=
    residueBasisLifts_linearIndependent v w hExt beta omega homega
  have hfiniteJ : Finite J := hli.finite
  let : Finite J := hfiniteJ
  let : Fintype J := Fintype.ofFinite J
  have hcardNat : Nat.card J = Module.finrank K L :=
    finiteUnramifiedExtension_residueBasis_card_eq_finrank
      v w hExt hUnramified beta omega homega
  have hcard : Fintype.card J = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardNat
  have hcardpos : 0 < Fintype.card J := by
    rw [hcard]
    exact Module.finrank_pos
  let : Nonempty J := Fintype.card_pos_iff.mp hcardpos
  let b : Basis J K L :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨b, ?_⟩
  intro j
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) j

/-- the finite unramified-extension definition and the fundamental inequality force the actual
ramification index of
a finite unramified extension to be one. -/
theorem exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hUnramified : FiniteUnramifiedExtension v w hExt) :
    exponentialRamificationIndex v w = 1 := by
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  have hfpos : 0 < exponentialResidueDegree v w hExt := by
    rw [← finiteUnramifiedExtension_degree_eq_residueDegree
      v w hExt hUnramified]
    exact Module.finrank_pos
  have hfundamental :
      exponentialRamificationIndex v w * exponentialResidueDegree v w hExt ≤
        Module.finrank K L :=
    ramificationInvariants_fundamental_inequality v w hExt
  have hmul :
      exponentialRamificationIndex v w * exponentialResidueDegree v w hExt ≤
        1 * exponentialResidueDegree v w hExt := by
    simpa [finiteUnramifiedExtension_degree_eq_residueDegree
      v w hExt hUnramified] using hfundamental
  have he_le_one : exponentialRamificationIndex v w ≤ 1 := by
    exact Nat.le_of_mul_le_mul_right hmul hfpos
  have hepos : 0 < exponentialRamificationIndex v w := by
    let : Nonempty (ExponentialValueGroupQuotient v w) :=
      ⟨QuotientAddGroup.mk (0 : exponentialValueSubgroup w)⟩
    rw [exponentialRamificationIndex]
    exact Nat.card_pos
  exact Nat.le_antisymm he_le_one (Nat.succ_le_of_lt hepos)

/-- The value subgroup does not change in a finite unramified extension. -/
theorem exponentialValueSubgroup_eq_of_finiteUnramifiedExtension
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hUnramified : FiniteUnramifiedExtension v w hExt) :
    exponentialValueSubgroup w = exponentialValueSubgroup v := by
  let Gamma := exponentialValueSubgroup w
  let H : AddSubgroup Gamma :=
    (exponentialValueSubgroup v).comap Gamma.subtype
  have hindex : H.index = 1 := by
    have he :=
      exponentialRamificationIndex_eq_one_of_finiteUnramifiedExtension
        v w hExt hUnramified
    rw [AddSubgroup.index_eq_card]
    simpa only [exponentialRamificationIndex, ExponentialValueGroupQuotient, Gamma, H]
      using he
  have hH : H = ⊤ := AddSubgroup.index_eq_one.mp hindex
  apply le_antisymm
  · intro r hr
    let gamma : Gamma := ⟨r, hr⟩
    have hgamma : gamma ∈ H := by
      rw [hH]
      exact Set.mem_univ gamma
    change r ∈ exponentialValueSubgroup v at hgamma
    exact hgamma
  · exact exponentialValueSubgroup_le_of_extends v w hExt

end FiniteValuedExtensionInvariants

end Valuations
end AlgebraicNumberTheory

end
