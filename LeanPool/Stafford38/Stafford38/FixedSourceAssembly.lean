/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.FixedSourceStatement


/-!
Assembly of the fixed-source reduction from canonical characteristic and Weyl data.
-/

@[expose] public section

namespace Stafford38.FixedSource

open Stafford38
open Stafford38.UniversalAssembly
open Stafford38.CharacteristicCanonicalCertificate
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylSymplectic
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford

noncomputable section
universe u

theorem universalFixedSourceStatement_of_canonicalSupportVanishing
    (hvanish : CanonicalSupportVanishing.{u}) :
    UniversalFixedSourceStatement.{u} := by
  intro k _ _ n d hd
  rcases exists_top_bernstein_piece k hd with ⟨N, hpiece, hprincipal⟩
  have hdegree : bernsteinDegree k d = N :=
    bernsteinDegree_eq_of_piece_of_principal_ne_zero k hpiece hprincipal
  by_cases hNzero : N = 0
  · have hpiece0 : d ∈ bernsteinPiece k (n + 1) 0 := by
      simpa [hNzero] using hpiece
    rcases eq_algebraMap_of_mem_bernsteinPiece_zero k hpiece0 with ⟨c, rfl⟩
    have hc : c ≠ 0 := by
      intro hc
      subst c
      simp at hd
    let ell : PresentedWeyl k (n + 1) := presentedCoordinate k n
    have hell : IsLinearWeylCoordinate k n ell := by
      refine ⟨1, 1, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
      · change freeWeylGenerator (standardForm k (n + 1))
            (.inl (0 : Fin (n + 1))) =
          freeWeylLinearCombination 1
            (freeWeylGenerator (standardForm k (n + 1)))
            (.inl (0 : Fin (n + 1)))
        exact (freeWeylLinearCombination_one (standardForm k (n + 1))
          (.inl (0 : Fin (n + 1)))).symm
    refine ⟨ell, algebraMap k _ c⁻¹, 0, hell, ?_⟩
    simp only [hdegree, hNzero, pow_zero]
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    simp
  · have hN : 0 < N := Nat.pos_of_ne_zero hNzero
    rcases exists_normalized_symplectic_image k
        (.inr ⟨0, Nat.succ_pos n⟩) hpiece (principal_isHomogeneous k d)
        hprincipal hN with
      ⟨M, Ninv, c, hM, hNinv, hMN, hNM, hc, hpiece', haxis⟩
    let e := standardSymplecticAlgEquivOfInverse k M Ninv hM hNinv hMN hNM
    let d' : PresentedWeyl k (n + 1) := normalizedSymplecticImage k M hM c d
    have hd' : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d' := by
      refine ⟨hpiece', ?_⟩
      rw [← coeff_principal_pure_eq_normalForm k]
      rw [← coeff_axisPolynomial k]
      exact haxis
    have hsupp := hvanish k n N d' hN hd'
    rcases exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty
      k n N d' hsupp with ⟨R, S, hcert⟩
    let a : PresentedWeyl k (n + 1) := algebraMap k _ c⁻¹
    have hd'eq : d' = a * e d := by
      simp [d', a, e, normalizedSymplecticImage, Algebra.smul_def,
        standardSymplecticAlgEquivOfInverse]
      all_goals rfl
    have ha_comm : ∀ z : PresentedWeyl k (n + 1), a * z = z * a := by
      intro z
      exact Algebra.commutes c⁻¹ z
    have hchartCert :
        (1 : PresentedWeyl k (n + 1)) = e d * (a * R) +
          (presentedCoordinate k n) ^ N * e d * (a * S) := by
      rw [hcert, hd'eq]
      rw [ha_comm (e d)]
      simp only [mul_assoc]
    let ell : PresentedWeyl k (n + 1) := e.symm (presentedCoordinate k n)
    have hell : IsLinearWeylCoordinate k n ell := by
      refine ⟨M, Ninv, hM, hNinv, hMN, hNM, ?_⟩
      change (standardSymplecticAlgEquivOfInverse k M Ninv hM hNinv hMN hNM).symm
          (freeWeylGenerator (standardForm k (n + 1))
            (.inl (0 : Fin (n + 1)))) =
        freeWeylLinearCombination Ninv
          (freeWeylGenerator (standardForm k (n + 1)))
          (.inl (0 : Fin (n + 1)))
      exact standardSymplecticAlgEquivOfInverse_symm_generator
        k M Ninv hM hNinv hMN hNM (.inl (0 : Fin (n + 1)))
    refine ⟨ell, e.symm (a * R), e.symm (a * S), hell, ?_⟩
    have ht := congrArg e.symm hchartCert
    simpa [ell, hdegree] using ht

/-- Pointwise form of the exact-degree fixed-source theorem. -/
theorem fixedSource_positive
    (hvanish : CanonicalSupportVanishing.{u})
    (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (d : PresentedWeyl k (n + 1)) (hd : d ≠ 0) :
    ∃ ell R S : PresentedWeyl k (n + 1),
      IsLinearWeylCoordinate k n ell ∧
        (1 : PresentedWeyl k (n + 1)) =
          d * R + ell ^ bernsteinDegree k d * d * S :=
  universalFixedSourceStatement_of_canonicalSupportVanishing hvanish k n d hd


end
end Stafford38.FixedSource
