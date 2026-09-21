/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Statement
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalCertificate
import LeanPool.Stafford38.Stafford38.Weyl.MonicNormalization
import LeanPool.Stafford38.Stafford38.Weyl.PBWMonicBridge

/-!
# Final assembly from the canonical support theorem

This file discharges the scalar case, normalized symplectic-chart transport,
and fixed-source certificate transport in the exact universal statement.  Its
single remaining hypothesis is the concrete support-vanishing theorem for the
literal canonical right ideal attached to a normalized PBW-monic operator.
-/

namespace Stafford38.UniversalAssembly

open Stafford38
open Stafford38.CharacteristicCanonicalCertificate
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylSymplectic

noncomputable section

universe u

/-- The one concrete theorem still needed by the final algebraic assembly. -/
def CanonicalSupportVanishing : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N) = ∅

private theorem rankZero_certificate
    (k : Type u) [Field k] (d : PresentedWeyl k 0) (hd : d ≠ 0) :
    ∃ F R S : PresentedWeyl k 0,
      (1 : PresentedWeyl k 0) = d * R + F * d * S := by
  let e := presentedIteratedEquiv k 0
  let c : k := e d
  have hc : c ≠ 0 := by
    intro hczero
    change e d = 0 at hczero
    apply hd
    calc
      d = e.symm (e d) := (e.symm_apply_apply d).symm
      _ = e.symm 0 := congrArg e.symm hczero
      _ = 0 := map_zero e.symm
  refine ⟨0, e.symm (c⁻¹ : k), 0, ?_⟩
  have hmul : c * c⁻¹ = (1 : k) := mul_inv_cancel₀ hc
  have h : d * e.symm (c⁻¹ : k) = 1 := by
    calc d * e.symm (c⁻¹ : k)
        = e.symm c * e.symm (c⁻¹ : k) := by
          congr 1
          exact (e.symm_apply_apply d).symm
      _ = e.symm (c * c⁻¹) := (map_mul e.symm _ _).symm
      _ = e.symm 1 := congrArg e.symm hmul
      _ = 1 := map_one e.symm
  simpa using h.symm

/-- Once canonical support vanishing is proved, the exact theorem exported by
`Stafford38.Statement` follows with no further mathematical hypothesis. -/
theorem universalStatement_of_canonicalSupportVanishing
    (hvanish : CanonicalSupportVanishing.{u}) :
    Stafford38.UniversalStatement.{u} := by
  intro k _ _ n d hd
  cases n with
  | zero =>
      exact rankZero_certificate k d hd
  | succ n =>
      rcases scalar_or_normalized_symplectic_image k (Nat.succ_pos n) hd with
        hscalar | hchart
      · rcases hscalar with ⟨c, hc, rfl⟩
        refine ⟨0, algebraMap k (PresentedWeyl k (n + 1)) c⁻¹, 0, ?_⟩
        simp only [zero_mul, zero_add]
        rw [← map_mul]
        rw [mul_inv_cancel₀ hc, map_one]
        simp
      · rcases hchart with ⟨N, hN, M, Ninv, c, hM, hNinv, hMN, hNM,
          hc, hpiece, haxis⟩
        let e := standardSymplecticAlgEquivOfInverse
          k M Ninv hM hNinv hMN hNM
        let d' : PresentedWeyl k (n + 1) :=
          normalizedSymplecticImage k M hM c d
        have hd' : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d' := by
          refine ⟨hpiece, ?_⟩
          rw [← coeff_principal_pure_eq_normalForm k]
          rw [← coeff_axisPolynomial k]
          exact haxis
        have hsupp := hvanish k n N d' hN hd'
        rcases exists_fixedSource_certificate_of_orderCharacteristicSupport_eq_empty
            k n N d' hsupp with ⟨R, S, hcert⟩
        let a : PresentedWeyl k (n + 1) :=
          algebraMap k (PresentedWeyl k (n + 1)) c⁻¹
        have hd'eq : d' = a * e d := by
          simp [d', a, e, normalizedSymplecticImage, Algebra.smul_def,
            standardSymplecticAlgEquivOfInverse] <;> rfl
        have ha_comm : ∀ z : PresentedWeyl k (n + 1), a * z = z * a := by
          intro z
          exact Algebra.commutes c⁻¹ z
        have hchartCert :
            (1 : PresentedWeyl k (n + 1)) =
              e d * (a * R) +
                (presentedCoordinate k n) ^ N * e d * (a * S) := by
          rw [hcert, hd'eq]
          rw [ha_comm (e d)]
          simp only [mul_assoc]
        refine ⟨e.symm ((presentedCoordinate k n) ^ N),
          e.symm (a * R), e.symm (a * S), ?_⟩
        have htransport := congrArg e.symm hchartCert
        simpa using htransport


end

end Stafford38.UniversalAssembly
