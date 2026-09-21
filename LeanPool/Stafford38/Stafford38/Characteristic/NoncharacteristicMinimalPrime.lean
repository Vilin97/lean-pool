/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import LeanPool.Stafford38.Stafford38.Characteristic.GabberGlobalAssembly
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalNormalAxisSupport

namespace Stafford38.Characteristic.NoncharacteristicMinimalPrime

open Stafford38
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.Characteristic.CanonicalNormalAxisSupport
open Stafford38.Characteristic.GabberGlobalAssembly
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylFiltration
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable {k : Type*} [Field k] [CharZero k] {n N : ℕ}

private def iterPderiv (i : PhaseVar (n + 1)) (r : ℕ)
    (f : SymbolRing k (n + 1)) : SymbolRing k (n + 1) :=
  (MvPolynomial.pderiv i)^[r] f

private theorem iterPderiv_mem_of_involutive
    (P : Ideal (SymbolRing k (n + 1))) (hP : IsInvolutive P)
    (j : Fin (n + 1)) (hx : MvPolynomial.X (.inl j) ∈ P)
    (f : SymbolRing k (n + 1)) (hf : f ∈ P) :
    ∀ r, iterPderiv (.inr j) r f ∈ P := by
  intro r
  induction r with
  | zero => simpa [iterPderiv] using hf
  | succ r ihr =>
      have hb := hP (MvPolynomial.X (.inl j)) hx
        (iterPderiv (.inr j) r f) ihr
      simpa [iterPderiv, Function.iterate_succ_apply', poissonBracket,
        Pi.single_apply] using hb

private theorem iterPderiv_eq_factorial_of_homogeneous
    (i : PhaseVar (n + 1)) (f : SymbolRing k (n + 1))
    (hf : f.IsHomogeneous N)
    (hc : f.coeff (Finsupp.single i N) = 1) :
    iterPderiv i N f = MvPolynomial.C (N.factorial : k) := by
  have hhom : ∀ r, (iterPderiv i r f).IsHomogeneous (N - r) := by
    intro r
    induction r with
    | zero => simpa [iterPderiv] using hf
    | succ r ihr =>
        simpa [iterPderiv, Function.iterate_succ_apply', Nat.sub_sub] using
          (MvPolynomial.IsHomogeneous.pderiv ihr)
  have hcoeff : ∀ r m,
      (iterPderiv i r f).coeff (Finsupp.single i m) =
        f.coeff (Finsupp.single i (m + r)) *
          ((m + r).descFactorial r : k) := by
    intro r
    induction r with
    | zero => intro m; simp [iterPderiv]
    | succ r ihr =>
        intro m
        rw [show iterPderiv i (r + 1) f =
          MvPolynomial.pderiv i (iterPderiv i r f) by
            simp [iterPderiv, Function.iterate_succ_apply']]
        rw [MvPolynomial.coeff_pderiv]
        have hi := ihr (m + 1)
        simp only [Finsupp.single_add] at hi ⊢
        rw [hi]
        have harg :
            ((Finsupp.single i m + Finsupp.single i 1) + Finsupp.single i r) =
              Finsupp.single i (m + (r + 1)) := by
          ext q
          by_cases hq : q = i <;> simp [hq] <;> omega
        rw [harg]
        rw [show m + (r + 1) = m + 1 + r by omega,
          Nat.descFactorial_succ]
        have hnat : m + 1 + r - r = m + 1 := by omega
        rw [hnat]
        simp [Nat.add_assoc, Nat.cast_mul]
        have hcarg :
            Finsupp.single i m + (Finsupp.single i 1 + Finsupp.single i r) =
              Finsupp.single i m + (Finsupp.single i r + Finsupp.single i 1) := by
          ext q
          by_cases hq : q = i <;> simp [hq] <;> omega
        rw [hcarg]
        ring
  have hzero : iterPderiv i N f =
      MvPolynomial.C ((iterPderiv i N f).coeff (0 : PhaseVar (n + 1) →₀ ℕ)) := by
    calc
      iterPderiv i N f = MvPolynomial.homogeneousComponent 0
          (iterPderiv i N f) := by
            simpa only [Nat.sub_self] using
              (MvPolynomial.homogeneousComponent_eq_self (hhom N)).symm
      _ = _ := MvPolynomial.homogeneousComponent_zero _
  rw [hzero]
  have hzeroCoeff :
      (iterPderiv i N f).coeff (0 : PhaseVar (n + 1) →₀ ℕ) =
        (iterPderiv i N f).coeff (Finsupp.single i 0) := by
    congr 1
    ext q
    by_cases hq : q = i <;> simp [hq]
  rw [hzeroCoeff, hcoeff N 0]
  simp [Nat.zero_add, Nat.descFactorial_self, hc]

theorem canonical_minimalPrime_mem_of_normalCoordinate_false
    (d : PresentedWeyl k (n + 1))
    (hN : 0 < N) (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    {P : Ideal (SymbolRing k (n + 1))} (hP : P ∈
      (Module.annihilator (SymbolRing k (n + 1))
        (OrderAssociatedGradedModule k
      (canonicalRightIdeal (presentedCoordinate k n) d N))).minimalPrimes) :
    MvPolynomial.X (.inl (0 : Fin (n + 1))) ∉ P := by
  have hPorder : P ∈ (orderInitialIdeal k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).minimalPrimes := by
    simpa [annihilator_orderAssociatedGradedModule] using hP
  letI : P.IsPrime := hP.1.1
  have hInv : IsInvolutive P := minimalPrime_isInvolutive k
    (canonicalRightIdeal (presentedCoordinate k n) d N) P hP
  intro hx
  let f := presentedPrincipalComponent k orderWeight N d
  have hf : f ∈ P := by
    apply hPorder.1.2
    exact canonical_orderPrincipalComponent_mem_initialIdeal k n N hd
  have hderiv := iterPderiv_mem_of_involutive P hInv
    (0 : Fin (n + 1)) hx f hf N
  have hfac : MvPolynomial.C (N.factorial : k) ∈ P := by
    rw [← iterPderiv_eq_factorial_of_homogeneous
      (.inr (0 : Fin (n + 1))) f
      (canonical_orderPrincipalComponent_isHomogeneous n N hd)
      (canonical_orderPrincipalComponent_pureMomentumCoefficient k n N hd)]
    exact hderiv
  have hfac0 : (N.factorial : k) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero N)
  have hone : (1 : SymbolRing k (n + 1)) ∈ P := by
    have hm := P.mul_mem_left (MvPolynomial.C ((N.factorial : k)⁻¹)) hfac
    rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hfac0] at hm
    simpa using hm
  exact hP.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr hone)

end
end Stafford38.Characteristic.NoncharacteristicMinimalPrime
