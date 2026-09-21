/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.GeneralAsymptoticConormal
import LeanPool.Stafford38.Stafford38.Geometry.GeneralComponentConormalContainment

/-!
# Coisotropic exclusion for arbitrary homogeneous radical ideals

A nonempty fibre-conical coisotropic zero locus contained in a fibre-only
symbol hypersurface transverse to the distinguished axis must meet the
coordinate hyperplane.
-/

namespace Stafford38.Geometry.GeneralCoisotropicExclusion

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.GeneralConormalContainment
open Stafford38.Geometry.GeneralComponentConormalContainment
open Stafford38.Geometry.GeneralAsymptoticConormal
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ProjectiveConormalDirections
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

universe u

theorem exists_zero_base_coordinate
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (J : Ideal (SymbolRing k m)) (hproper : J ≠ ⊤)
    (hrad : J.IsRadical)
    (hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := m)))
    (hpoisson : IsBaseRelativePoisson J)
    (P : MvPolynomial (Fin m) k) (hP : fibreLift P ∈ J)
    (haxis : MvPolynomial.eval
      (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P ≠ 0) :
    ∃ q ∈ MvPolynomial.zeroLocus k J, q (.inl ⟨0, hm⟩) = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  let B := J.comap (baseLift (k := k) (n := m)).toRingHom
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes
    (show B ≠ ⊤ from Ideal.comap_ne_top _ hproper)
  let qprime : PrimeSpectrum (MvPolynomial (Fin m) k) := ⟨Q, hQ.1.1⟩
  have havoid : ∀ y ∈ MvPolynomial.zeroLocus k Q, y ⟨0, hm⟩ ≠ 0 := by
    intro y hy
    have hyB : ∀ f ∈ B, MvPolynomial.eval y f = 0 := by
      intro f hf
      exact hy f (hQ.1.2 hf)
    have hzero : zeroSectionPoint y ∈ MvPolynomial.zeroLocus k J :=
      zeroSection_commonZero_of_isHomogeneous J hhom y hyB
    exact hnone (zeroSectionPoint y) hzero
  have hclosure := coordinate_axis_mem_smooth_fibre_closure hm qprime havoid
  apply haxis
  apply hclosure P
  intro ξ hξ
  obtain ⟨y, hysmooth, hconormal⟩ := hξ
  have hy : y ∈ MvPolynomial.zeroLocus k Q :=
    smoothAffinePoint_mem_zeroLocus Q hysmooth
  have hpoint : Sum.elim y ξ ∈ equationConormalClosure Q := by
    intro f hf
    exact hf (Sum.elim y ξ) ⟨hy, hconormal⟩
  have hJpoint := equationConormalClosure_minimalPrime_subset_zeroLocus
    J hrad hhom hpoisson Q hQ hpoint
  have hzero := hJpoint (fibreLift P) hP
  simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using hzero


end
end Stafford38.Geometry.GeneralCoisotropicExclusion
