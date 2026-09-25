/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import LeanPool.Stafford38.Stafford38.Geometry.GeneralCoisotropicSets
public import LeanPool.Stafford38.Stafford38.Characteristic.PostScalarExtensionPoisson


/-!
# Independent consumer for the set-level coisotropic exclusion

The consumer statements use the exported set theorem as their only geometric
input.  Their interface is paper-facing: closedness and nonemptiness are
hypotheses on `W`, while fibre homogeneity is supplied by `IsFibreConical`
rather than by an explicit homogeneous-ideal hypothesis.  The additional
Poisson import supplies product rules for the independent negative control.
-/

@[expose] public section

namespace Stafford38.Geometry.GeneralCoisotropicSetsTest

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.Geometry.FibreConicalVanishingIdeal
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.GeneralCoisotropicSets
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

universe u

/-- The set-level component theorem exposes the manuscript's conormal
containment directly, without requiring a consumer to reconstruct the
vanishing-ideal dictionary. -/
theorem exported_general_coisotropic_component_conormal_consumer
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ}
    (W : Set (PhaseVar m → k))
    (hclosed : ∃ L : Ideal (SymbolRing k m),
      W = MvPolynomial.zeroLocus k L)
    (hW : IsFibreConical W)
    (hpoisson : ∀ f ∈ MvPolynomial.vanishingIdeal k W,
      ∀ g ∈ MvPolynomial.vanishingIdeal k W,
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k W)
    (P : Ideal (MvPolynomial (Fin m) k))
    (hP : P ∈ ((MvPolynomial.vanishingIdeal k W).comap
      (Stafford38.Geometry.CoisotropicTranslation.baseLift :
        MvPolynomial (Fin m) k →ₐ[k] SymbolRing k m).toRingHom).minimalPrimes) :
    MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (restrictedEquationConormalLocus P {y | SmoothAffinePoint P y})) ⊆ W := by
  exact smoothConormalClosure_minimalPrime_subset_of_isFibreConical
    W hclosed hW hpoisson P hP

/-- The exported arbitrary-set theorem is consumable at exactly its stated
hypotheses, independently of the implementation module. -/
theorem exported_general_coisotropic_set_consumer
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (W : Set (PhaseVar m → k))
    (hnonempty : W.Nonempty)
    (hclosed : ∃ L : Ideal (SymbolRing k m),
      W = MvPolynomial.zeroLocus k L)
    (hW : IsFibreConical W)
    (hpoisson : ∀ f ∈ MvPolynomial.vanishingIdeal k W,
      ∀ g ∈ MvPolynomial.vanishingIdeal k W,
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k W)
    (P : MvPolynomial (Fin m) k)
    (hP : fibreLift P ∈ MvPolynomial.vanishingIdeal k W)
    (haxis : MvPolynomial.eval
      (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P ≠ 0) :
    ∃ q ∈ W, q (.inl ⟨0, hm⟩) = 0 := by
  exact exists_zero_base_coordinate_of_isFibreConical
    hm W hnonempty hclosed hW hpoisson P hP haxis

/-- The exclusion form used by the paper follows immediately and retains the
same arbitrary-set quantifiers. -/
theorem false_of_exported_general_coisotropic_set_avoiding_hyperplane
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (W : Set (PhaseVar m → k))
    (hnonempty : W.Nonempty)
    (hclosed : ∃ L : Ideal (SymbolRing k m),
      W = MvPolynomial.zeroLocus k L)
    (hW : IsFibreConical W)
    (hpoisson : ∀ f ∈ MvPolynomial.vanishingIdeal k W,
      ∀ g ∈ MvPolynomial.vanishingIdeal k W,
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k W)
    (P : MvPolynomial (Fin m) k)
    (hP : fibreLift P ∈ MvPolynomial.vanishingIdeal k W)
    (haxis : MvPolynomial.eval
      (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P ≠ 0)
    (havoid : ∀ q ∈ W, q (.inl ⟨0, hm⟩) ≠ 0) :
    False := by
  obtain ⟨q, hq, hqcoord⟩ := exported_general_coisotropic_set_consumer
    hm W hnonempty hclosed hW hpoisson P hP haxis
  exact havoid q hq hqcoord

/-- The manuscript-facing statement over `ℂ`, with ordinary fibre scaling and
pointwise fibre-polynomial vanishing as its inputs.  The exported theorem is
therefore checked through the definitions used by the paper rather than by
repeating its interface propositions as hypotheses. -/
theorem exact_complex_manuscript_coisotropic_consumer
    {n : ℕ} (hn : 0 < n)
    (W : Set (PhaseVar n → ℂ))
    (hnonempty : W.Nonempty)
    (hclosed : ∃ L : Ideal (SymbolRing ℂ n),
      W = MvPolynomial.zeroLocus ℂ L)
    (hscale : ∀ q ∈ W, ∀ a : ℂ, a ≠ 0 →
      Sum.elim (fun i => q (.inl i)) (fun i => a * q (.inr i)) ∈ W)
    (hbracket : ∀ f ∈ MvPolynomial.vanishingIdeal ℂ W,
      ∀ g ∈ MvPolynomial.vanishingIdeal ℂ W,
      poissonBracket f g ∈ MvPolynomial.vanishingIdeal ℂ W)
    (P : MvPolynomial (Fin n) ℂ)
    (hPpoint : ∀ q ∈ W,
      MvPolynomial.eval (fun i => q (.inr i)) P = 0)
    (haxis : MvPolynomial.eval
      (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) P ≠ 0)
    (havoid : ∀ q ∈ W, q (.inl ⟨0, hn⟩) ≠ 0) :
    False := by
  have hW : IsFibreConical W := hscale
  have hP : fibreLift P ∈ MvPolynomial.vanishingIdeal ℂ W := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro q hq
    have hqP := hPpoint q hq
    simpa [fibreLift, MvPolynomial.eval_rename, Function.comp_def] using hqP
  exact false_of_exported_general_coisotropic_set_avoiding_hyperplane
    hn W hnonempty hclosed hW hbracket P hP haxis havoid

/-! ## A negative control for the coisotropic hypothesis

The zero section in one-dimensional phase space has ideal `(ξ)`.  It is
self-involutive, but it is not stable under bracketing with arbitrary ambient
polynomials because `{ξ, x} = -1`. -/

/-- The ideal of the zero section in the cotangent space of the affine line. -/
def zeroSectionIdealOne (k : Type*) [Field k] : Ideal (SymbolRing k 1) :=
  Ideal.span {MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1)}

theorem zeroSectionIdealOne_isInvolutive
    {k : Type*} [Field k] :
    ∀ f ∈ zeroSectionIdealOne k, ∀ g ∈ zeroSectionIdealOne k,
      poissonBracket f g ∈ zeroSectionIdealOne k := by
  intro f hf g hg
  change f ∈ Ideal.span
    {MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1)} at hf
  change g ∈ Ideal.span
    {MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1)} at hg
  rw [Ideal.mem_span_singleton] at hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  rw [ha, hb]
  let I := zeroSectionIdealOne k
  have hxi : MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1) ∈ I :=
    Ideal.mem_span_singleton_self _
  rw [PostScalarExtensionPoisson.poissonBracket_mul_left]
  apply I.add_mem
  · exact I.mul_mem_right _ hxi
  · apply I.mul_mem_left
    rw [PostScalarExtensionPoisson.poissonBracket_mul_right,
      poissonBracket_self, mul_zero, add_zero]
    exact I.mul_mem_right _ hxi

theorem zeroSectionIdealOne_not_isPoisson
    {k : Type*} [Field k] : ¬ IsPoisson (zeroSectionIdealOne k) := by
  intro hpoisson
  have hxi : MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1) ∈
      zeroSectionIdealOne k :=
    Ideal.mem_span_singleton_self _
  have hbad := hpoisson
    (MvPolynomial.X (Sum.inr (0 : Fin 1) : PhaseVar 1)) hxi
    (MvPolynomial.X (Sum.inl (0 : Fin 1) : PhaseVar 1))
  have hnegone : (-1 : SymbolRing k 1) ∈ zeroSectionIdealOne k := by
    simpa [poissonBracket, Pi.single_apply] using hbad
  rw [zeroSectionIdealOne, Ideal.mem_span_singleton] at hnegone
  rcases hnegone with ⟨a, ha⟩
  have ha0 := congrArg
    (MvPolynomial.eval (fun _ : PhaseVar 1 => (0 : k))) ha
  simp at ha0


end
end Stafford38.Geometry.GeneralCoisotropicSetsTest
