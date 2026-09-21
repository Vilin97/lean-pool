/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalNormalAxisSupport
import LeanPool.Stafford38.Stafford38.Weyl.PBWMonicBridge
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace Stafford38.Characteristic.NormalSymbolPolynomial

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford38.WeylPBWMonicBridge
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Geometry.ConormalAxisContradiction

noncomputable section
variable {k : Type*} [Field k]

def normalVariableEquiv (n : ℕ) :
    Option {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))} ≃ PhaseVar (n + 1) :=
  Equiv.optionSubtypeNe (Sum.inr (0 : Fin (n + 1)))

def normalSymbolAlgEquiv (n : ℕ) :
    SymbolRing k (n + 1) ≃ₐ[k]
      Polynomial (MvPolynomial
        {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))} k) :=
  (MvPolynomial.renameEquiv k (normalVariableEquiv n).symm).trans
    (MvPolynomial.optionEquivLeft k
      {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))})

def canonicalNormalPolynomial {n N : ℕ} (d : PresentedWeyl k (n + 1)) :
    Polynomial (MvPolynomial
      {v : PhaseVar (n + 1) // v ≠ Sum.inr (0 : Fin (n + 1))} k) :=
  normalSymbolAlgEquiv (k := k) n
    (presentedPrincipalComponent k (@orderWeight (n + 1)) N d)

theorem normalSymbolAlgEquiv_normalVariable (n : ℕ) :
    normalSymbolAlgEquiv (k := k) n
        (MvPolynomial.X (.inr (0 : Fin (n + 1)))) = Polynomial.X := by
  simp [normalSymbolAlgEquiv, normalVariableEquiv]

theorem normalSymbolAlgEquiv_otherVariable (n : ℕ)
    (v : PhaseVar (n + 1)) (hv : v ≠ .inr (0 : Fin (n + 1))) :
    normalSymbolAlgEquiv (k := k) n (MvPolynomial.X v) =
      Polynomial.C (MvPolynomial.X ⟨v, hv⟩) := by
  simp [normalSymbolAlgEquiv, normalVariableEquiv, hv]

theorem optionEquivLeft_monic_of_isHomogeneous
    {S : Type*} [Finite S] (P : MvPolynomial (Option S) k) (N : ℕ)
    (hP : P.IsHomogeneous N)
    (hlead : MvPolynomial.coeff (Finsupp.single none N) P = 1) :
    (MvPolynomial.optionEquivLeft k S P).Monic := by
  classical
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one N
  · rw [MvPolynomial.natDegree_optionEquivLeft]
    exact (MvPolynomial.degreeOf_le_totalDegree P none).trans hP.totalDegree_le
  · ext m
    rw [MvPolynomial.optionEquivLeft_coeff_coeff]
    by_cases hm : m = 0
    · subst m
      simpa using hlead
    · have hzero : MvPolynomial.coeff (m.optionElim N) P = 0 := by
        by_contra hcoeff
        have hcoeffHomogeneous :
            ((MvPolynomial.optionEquivLeft k S P).coeff N).IsHomogeneous 0 := by
          intro e he
          rw [MvPolynomial.optionEquivLeft_coeff_coeff] at he
          have hdegree := hP he
          have hzero : (Finsupp.weight (1 : S → ℕ)) e = 0 := by
            by_contra hne
            have hpos : 0 < (Finsupp.weight (1 : S → ℕ)) e := Nat.pos_of_ne_zero hne
            have hall : N + (Finsupp.weight (1 : S → ℕ)) e = N := by
              rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul] at hdegree
              simpa [Finsupp.weight_apply] using hdegree
            omega
          exact hzero
        have hcoeff' : MvPolynomial.coeff m
            ((MvPolynomial.optionEquivLeft k S P).coeff N) ≠ 0 := by
          rwa [MvPolynomial.optionEquivLeft_coeff_coeff]
        have hdegree := hcoeffHomogeneous hcoeff'
        rw [Finsupp.weight_apply] at hdegree
        apply hm
        ext x
        by_cases hx : x ∈ m.support
        · simpa using (Finset.sum_eq_zero_iff_of_nonneg
              (fun _ _ ↦ Nat.zero_le _)).mp hdegree x hx
        · exact Finsupp.notMem_support_iff.mp hx
      rw [hzero]
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm hm)]

theorem canonicalNormalPolynomial_monic {n N : ℕ}
    {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    (canonicalNormalPolynomial (k := k) (n := n) (N := N) d).Monic := by
  apply optionEquivLeft_monic_of_isHomogeneous
  · exact (canonical_orderPrincipalComponent_isHomogeneous n N hd).rename_isHomogeneous
  · change MvPolynomial.coeff (Finsupp.single none N)
        (MvPolynomial.rename (normalVariableEquiv n).symm
          (presentedPrincipalComponent k orderWeight N d)) = 1
    have hsingle : (Finsupp.single (.inr (0 : Fin (n + 1))) N).mapDomain
        (normalVariableEquiv n).symm = Finsupp.single none N := by
      simp [normalVariableEquiv]
    rw [← hsingle, MvPolynomial.coeff_rename_mapDomain
      (normalVariableEquiv n).symm (normalVariableEquiv n).symm.injective]
    exact canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd


end
end Stafford38.Characteristic.NormalSymbolPolynomial
