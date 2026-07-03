/-
Copyright (c) 2026 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

import LeanPool.NonisotopicKnots.Submission.ConfigNonComm
import LeanPool.NonisotopicKnots.Submission.Invariant

/-!
# Vieta brick (WORK IN PROGRESS): the coefficient map is an open map

This develops the linchpin reusable brick for the cusp-link route documented in `PLAN.md`:
the elementary-symmetric ("Vieta") coefficient map from ordered triples of complex numbers to
the three coefficients of the monic cubic is a local homeomorphism at injective triples (its
derivative is the Vandermonde matrix, with determinant `∏ (rᵢ − rⱼ) ≠ 0`), hence open there.

This file is NOT imported by `Submission.lean`; it is staged here and will only be wired into the
configured theorem once it is fully `sorry`-free.
-/

namespace Submission.Vieta

open Complex

/-- The configuration space of three ordered distinct points in `ℂ`
(reusing the project's `Submission.ConfigCover.Conf`). -/
abbrev Conf := Submission.ConfigCover.Conf

/-- The full elementary-symmetric coefficient map on all triples (`Fin 3 → ℂ`):
`(r₀,r₁,r₂) ↦ (e₁, e₂, e₃)`. -/
noncomputable def Coeff (r : Fin 3 → ℂ) : ℂ × ℂ × ℂ :=
  (r 0 + r 1 + r 2, r 0 * r 1 + r 0 * r 2 + r 1 * r 2, r 0 * r 1 * r 2)

lemma continuous_Coeff : Continuous Coeff := by
  have h0 : Continuous fun r : Fin 3 → ℂ => r 0 := continuous_apply 0
  have h1 : Continuous fun r : Fin 3 → ℂ => r 1 := continuous_apply 1
  have h2 : Continuous fun r : Fin 3 → ℂ => r 2 := continuous_apply 2
  exact Continuous.prodMk (((h0.add h1).add h2))
    (Continuous.prodMk (((h0.mul h1).add (h0.mul h2)).add (h1.mul h2)) ((h0.mul h1).mul h2))

/-- `Coeff` is smooth (a polynomial map). -/
lemma contDiff_Coeff : ContDiff ℂ (⊤ : ℕ∞) Coeff := by
  have h0 : ContDiff ℂ (⊤ : ℕ∞) fun r : Fin 3 → ℂ => r 0 :=
    (contDiff_apply ℂ ℂ 0)
  have h1 : ContDiff ℂ (⊤ : ℕ∞) fun r : Fin 3 → ℂ => r 1 :=
    (contDiff_apply ℂ ℂ 1)
  have h2 : ContDiff ℂ (⊤ : ℕ∞) fun r : Fin 3 → ℂ => r 2 :=
    (contDiff_apply ℂ ℂ 2)
  exact ContDiff.prodMk (((h0.add h1).add h2))
    (ContDiff.prodMk (((h0.mul h1).add (h0.mul h2)).add (h1.mul h2)) ((h0.mul h1).mul h2))

/-- The `i`-th coordinate projection on `Fin 3 → ℂ` as a continuous linear map. -/
noncomputable def pj (i : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i

/-- The candidate Fréchet derivative of `Coeff` at `r`: the (transpose) Vandermonde linear map. -/
noncomputable def CoeffDeriv (r : Fin 3 → ℂ) : (Fin 3 → ℂ) →L[ℂ] ℂ × ℂ × ℂ :=
  ContinuousLinearMap.prod (pj 0 + pj 1 + pj 2)
    (ContinuousLinearMap.prod
      ((r 1 + r 2) • pj 0 + (r 0 + r 2) • pj 1 + (r 0 + r 1) • pj 2)
      ((r 1 * r 2) • pj 0 + (r 0 * r 2) • pj 1 + (r 0 * r 1) • pj 2))

/-
`Coeff` has the Vandermonde Fréchet derivative `CoeffDeriv r` at every `r`.
-/
lemma hasFDerivAt_Coeff (r : Fin 3 → ℂ) : HasFDerivAt Coeff (CoeffDeriv r) r := by
  unfold CoeffDeriv;
  have h0 : HasFDerivAt (fun r : Fin 3 → ℂ => r 0) (pj 0) r := by
    exact hasFDerivAt_apply _ _
  have h1 : HasFDerivAt (fun r : Fin 3 → ℂ => r 1) (pj 1) r := by
    exact hasFDerivAt_apply _ _
  have h2 : HasFDerivAt (fun r : Fin 3 → ℂ => r 2) (pj 2) r := by
    exact hasFDerivAt_apply _ _;
  convert HasFDerivAt.prodMk ( HasFDerivAt.add ( HasFDerivAt.add h0 h1 ) h2 ) ( HasFDerivAt.prodMk ( HasFDerivAt.add ( HasFDerivAt.add ( HasFDerivAt.mul h0 h1 ) ( HasFDerivAt.mul h0 h2 ) ) ( HasFDerivAt.mul h1 h2 ) ) ( HasFDerivAt.mul ( HasFDerivAt.mul h0 h1 ) h2 ) ) using 1;
  ext ; norm_num ; ring;
  · norm_num [ add_smul, mul_comm ] ; ring;
  · norm_num ; ring

/-
The Vandermonde derivative is injective on the configuration space (its determinant is
`∏_{i<j} (rᵢ − rⱼ) ≠ 0`).
-/
lemma coeffDeriv_injective {r : Fin 3 → ℂ} (hr : Function.Injective r) :
    Function.Injective (CoeffDeriv r) := by
  intro x y hxy;
  simp_all +decide [ CoeffDeriv, funext_iff, Fin.forall_fin_succ ];
  simp_all +decide [ Function.Injective, Fin.forall_fin_succ, pj ];
  grind +splitIndPred

/-- The Vandermonde derivative, packaged as a continuous linear equivalence at injective triples. -/
noncomputable def coeffDerivEquiv {r : Fin 3 → ℂ} (hr : Function.Injective r) :
    (Fin 3 → ℂ) ≃L[ℂ] ℂ × ℂ × ℂ :=
  (LinearEquiv.ofBijective (CoeffDeriv r).toLinearMap
    ⟨coeffDeriv_injective hr, by
      have hfr : Module.finrank ℂ (Fin 3 → ℂ) = Module.finrank ℂ (ℂ × ℂ × ℂ) := by
        simp [Module.finrank_prod]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp
        (coeffDeriv_injective hr)⟩).toContinuousLinearEquivOfContinuous (CoeffDeriv r).continuous

lemma coeffDerivEquiv_coe {r : Fin 3 → ℂ} (hr : Function.Injective r) :
    (coeffDerivEquiv hr : (Fin 3 → ℂ) →L[ℂ] ℂ × ℂ × ℂ) = CoeffDeriv r := rfl

/-
**Key analytic step.** The coefficient map is an open map on the configuration space:
its restriction to the open set of injective triples is open. Equivalently, at every injective
triple the (Vandermonde) derivative is invertible, so `Coeff` is a local homeomorphism there.
-/
theorem isOpenMap_Coeff_on_conf :
    IsOpenMap (fun r : Conf => Coeff r.1) := by
  intro U hU_open
  set V : Set (Fin 3 → ℂ) := Subtype.val '' U
  have hV_open : IsOpen V := by
    rcases hU_open with ⟨ t, ht, rfl ⟩;
    convert ht.inter ( show IsOpen { r : Fin 3 → ℂ | Function.Injective r } from ?_ ) using 1 ; aesop;
    simp +decide [ Function.Injective, Fin.forall_fin_succ ];
    simp +decide only [ne_comm, and_assoc];
    exact isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 1 ) ( continuous_apply 0 ) ) |> IsOpen.inter <| isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 0 ) ( continuous_apply 2 ) ) |> IsOpen.inter <| isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 1 ) ( continuous_apply 0 ) ) |> IsOpen.inter <| isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 1 ) ( continuous_apply 2 ) ) |> IsOpen.inter <| isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 0 ) ( continuous_apply 2 ) ) |> IsOpen.inter <| isOpen_compl_iff.mpr ( isClosed_eq ( continuous_apply 1 ) ( continuous_apply 2 ) )
  have hV_subset : V ⊆ {r : Fin 3 → ℂ | Function.Injective r} := by
    exact Set.image_subset_iff.mpr fun x hx => x.2;
  have h_coeff_open : IsOpen (Coeff '' V) := by
    apply_rules [ isOpen_iff_forall_mem_open.mpr ];
    intro x hx
    obtain ⟨r, hrV, rfl⟩ := hx
    have hr_inj : Function.Injective r := hV_subset hrV
    have h_local_homeomorph : ∃ p : OpenPartialHomeomorph (Fin 3 → ℂ) (ℂ × ℂ × ℂ), p.toFun = Coeff ∧ r ∈ p.source := by
      refine' ⟨ _, _, _ ⟩;
      apply_rules [ ContDiffAt.toOpenPartialHomeomorph ];
      exact contDiff_Coeff.contDiffAt;
      convert hasFDerivAt_Coeff r using 1;
      convert coeffDerivEquiv_coe hr_inj using 1;
      all_goals norm_num [ ContDiffAt.toOpenPartialHomeomorph ];
      grind +suggestions;
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_local_homeomorph;
    refine' ⟨ p '' ( p.source ∩ V ), _, _, _ ⟩;
    · exact fun x hx => by rcases hx with ⟨ y, ⟨ hy₁, hy₂ ⟩, rfl ⟩ ; exact ⟨ y, hy₂, by aesop ⟩ ;
    · exact p.isOpen_image_of_subset_source ( p.open_source.inter hV_open ) ( Set.inter_subset_left );
    · exact ⟨ r, ⟨ hp₂, hrV ⟩, hp₁ ▸ rfl ⟩;
  grind +splitIndPred

/-! ## The Vieta homeomorphism `ConfQuot ≃ₜ DiscComplement`. -/

open Submission.ConfigCover Submission.ConfigNonComm

/-- The coefficient map on the configuration space. -/
noncomputable def coeffConf (r : Conf) : ℂ × ℂ × ℂ := Coeff r.1

lemma continuous_coeffConf : Continuous coeffConf :=
  continuous_Coeff.comp continuous_subtype_val

lemma isOpenMap_coeffConf : IsOpenMap coeffConf := isOpenMap_Coeff_on_conf

/-
`Coeff` is invariant under permuting the three coordinates.
-/
lemma coeff_comp_perm (r : Fin 3 → ℂ) (σ : Equiv.Perm (Fin 3)) :
    Coeff (r ∘ σ) = Coeff r := by
  have he1 : (r ∘ σ) 0 + (r ∘ σ) 1 + (r ∘ σ) 2 = r 0 + r 1 + r 2 := by
    have := Equiv.sum_comp σ r; simpa [Fin.sum_univ_three] using this
  have he3 : (r ∘ σ) 0 * (r ∘ σ) 1 * (r ∘ σ) 2 = r 0 * r 1 * r 2 := by
    have := Equiv.prod_comp σ r; simpa [Fin.prod_univ_three] using this
  have h2 : (r ∘ σ) 0 ^ 2 + (r ∘ σ) 1 ^ 2 + (r ∘ σ) 2 ^ 2 = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
    have := Equiv.sum_comp σ (fun i => r i ^ 2); simpa [Fin.sum_univ_three] using this
  have he2 : (r ∘ σ) 0 * (r ∘ σ) 1 + (r ∘ σ) 0 * (r ∘ σ) 2 + (r ∘ σ) 1 * (r ∘ σ) 2
      = r 0 * r 1 + r 0 * r 2 + r 1 * r 2 := by
    simp only [Function.comp_apply] at he1 h2 ⊢
    linear_combination ((r (σ 0) + r (σ 1) + r (σ 2) + r 0 + r 1 + r 2) / 2) * he1
      + (-1 / 2 : ℂ) * h2
  simp only [Coeff, Prod.mk.injEq]
  exact ⟨he1, he2, he3⟩

/-- `coeffConf` is constant on `S₃`-orbits. -/
lemma coeffConf_smul (σ : Equiv.Perm (Fin 3)) (r : Conf) :
    coeffConf (σ • r) = coeffConf r := by
  show Coeff ((σ • r).1) = Coeff r.1
  have : (σ • r).1 = r.1 ∘ σ.symm := rfl
  rw [this]
  exact coeff_comp_perm r.1 σ.symm

/-
**Vieta uniqueness.** Two injective triples with the same elementary symmetric functions
differ by a permutation of coordinates.
-/
lemma exists_perm_of_coeff_eq {r s : Conf} (h : coeffConf r = coeffConf s) :
    ∃ σ : Equiv.Perm (Fin 3), s = σ • r := by
  -- By Vieta's formulas, if two triples have the same elementary symmetric functions, then they must be permutations of each other.
  simp only [coeffConf, Coeff, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3⟩ := h
  have h_perm : ∀ i : Fin 3, ∃ j : Fin 3, s.val i = r.val j := by
    intro i
    have key : (s.val i - r.val 0) * (s.val i - r.val 1) * (s.val i - r.val 2)
        = (s.val i - s.val 0) * (s.val i - s.val 1) * (s.val i - s.val 2) := by
      linear_combination (-(s.val i) ^ 2) * e1 + (s.val i) * e2 + (-1 : ℂ) * e3
    have hmem : s.val i = s.val 0 ∨ s.val i = s.val 1 ∨ s.val i = s.val 2 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have h_eq : (s.val i - r.val 0) * (s.val i - r.val 1) * (s.val i - r.val 2) = 0 := by
      rw [key]
      rcases hmem with h | h | h <;> rw [h] <;> ring
    rcases mul_eq_zero.mp h_eq with h' | h2
    · rcases mul_eq_zero.mp h' with h0 | h1
      · exact ⟨0, sub_eq_zero.mp h0⟩
      · exact ⟨1, sub_eq_zero.mp h1⟩
    · exact ⟨2, sub_eq_zero.mp h2⟩
  choose f hf using h_perm
  have h_inj : Function.Injective f := fun i j hij => s.2 (by rw [hf i, hf j, hij])
  refine ⟨(Equiv.ofBijective f ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩).symm, ?_⟩
  apply Subtype.ext
  funext i
  exact hf i

/-- The descended coefficient map on the orbit space `ConfQuot`. -/
noncomputable def vlift : ConfQuot → ℂ × ℂ × ℂ :=
  Quotient.lift coeffConf (by
    intro a b hab
    obtain ⟨σ, rfl⟩ := hab
    exact coeffConf_smul σ b)

@[simp] lemma vlift_mk (r : Conf) : vlift (Quotient.mk _ r) = coeffConf r := rfl

lemma continuous_vlift : Continuous vlift :=
  continuous_coeffConf.quotient_lift _

lemma injective_vlift : Function.Injective vlift := by
  intro x y h
  obtain ⟨r, rfl⟩ := Quotient.exists_rep x
  obtain ⟨s, rfl⟩ := Quotient.exists_rep y
  obtain ⟨σ, hσ⟩ := exists_perm_of_coeff_eq h
  apply Quotient.sound
  exact ⟨σ⁻¹, by rw [hσ]; exact inv_smul_smul σ r⟩

lemma isOpenMap_vlift : IsOpenMap vlift := by
  intro W hW
  have himg : vlift '' W = coeffConf '' (Quotient.mk _ ⁻¹' W) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨r, rfl⟩ := Quotient.exists_rep x
      exact ⟨r, hx, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Quotient.mk _ r, hr, rfl⟩
  rw [himg]
  exact isOpenMap_coeffConf _ (hW.preimage continuous_quotient_mk')

/-- The discriminant complement: the image of the coefficient map (an open subset of `ℂ³`). -/
def DiscCompl : Set (ℂ × ℂ × ℂ) := Set.range coeffConf

lemma isOpen_DiscCompl : IsOpen DiscCompl :=
  isOpenMap_coeffConf.isOpen_range

lemma vlift_mem_DiscCompl (x : ConfQuot) : vlift x ∈ DiscCompl := by
  obtain ⟨r, rfl⟩ := Quotient.exists_rep x
  exact ⟨r, rfl⟩

lemma range_vlift : Set.range vlift = DiscCompl := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact vlift_mem_DiscCompl x
  · rintro ⟨r, rfl⟩; exact ⟨Quotient.mk _ r, rfl⟩

/-- The bijection underlying the Vieta homeomorphism. -/
noncomputable def vEquiv : ConfQuot ≃ ↥DiscCompl :=
  Equiv.ofBijective (fun x => ⟨vlift x, vlift_mem_DiscCompl x⟩)
    ⟨fun a b h => injective_vlift (Subtype.ext_iff.mp h), fun y => by
      obtain ⟨x, hx⟩ := (range_vlift.symm ▸ y.2 : y.1 ∈ Set.range vlift)
      exact ⟨x, Subtype.ext hx⟩⟩

lemma continuous_vEquiv : Continuous vEquiv :=
  continuous_vlift.subtype_mk _

lemma isOpenMap_vEquiv : IsOpenMap vEquiv := by
  intro U hU;
  convert isOpenMap_vlift U hU using 1;
  constructor <;> intro h <;> rw [ isOpen_induced_iff ] at *;
  · convert isOpenMap_vlift U hU using 1;
  · grind +locals

/-- **The Vieta homeomorphism.** The orbit space of ordered configurations of three points is
homeomorphic to the discriminant complement of monic cubics. -/
noncomputable def vietaHomeo : ConfQuot ≃ₜ ↥DiscCompl :=
  vEquiv.toHomeomorphOfContinuousOpen continuous_vEquiv isOpenMap_vEquiv

/-- **The discriminant complement has non-abelian fundamental group.**
Transport of `Submission.ConfigNonComm.confQuot_pi1_noncomm` across the Vieta homeomorphism. -/
theorem discCompl_pi1_noncomm :
    ∃ (x : ↥DiscCompl) (a b : FundamentalGroup (↥DiscCompl) x), a * b ≠ b * a := by
  obtain ⟨x, a, b, hab⟩ := Submission.ConfigNonComm.confQuot_pi1_noncomm
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo vietaHomeo x
  refine ⟨vietaHomeo x, ψ a, ψ b, ?_⟩
  intro h
  apply hab
  apply ψ.injective
  rw [map_mul, map_mul, h]

end Submission.Vieta