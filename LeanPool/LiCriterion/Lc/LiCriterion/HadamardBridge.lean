/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import LeanPool.LiCriterion.Lc.LiCriterion.Basic
public import LeanPool.LiCriterion.Hadamard.General

/-!
# The Hadamard bridge for `ξ`

Specializes the general genus-1 Hadamard factorization to `riemannXi`, with multiplicities:
the zero set of `ξ` as a `Hadamard.ZeroSetMultiplicity`, and the resulting `E₁` product.
-/

@[expose] public section

open Complex

namespace LiCriterion

/-- The nontrivial zeros of `riemannXi`, indexed once each and weighted by their analytic order. -/
noncomputable def xiZeroSetMultiplicity : Hadamard.ZeroSetMultiplicity riemannXi where
  Zero := NontrivialZero
  z := fun ρ => ρ.val
  isZero := by
    intro ρ
    exact (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩
  mult := fun ρ => analyticOrderNatAt riemannXi ρ.val
  mult_pos := by
    intro ρ
    have hρ_zero : riemannXi ρ.val = 0 :=
      (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩
    have hxi_analytic : AnalyticOnNhd ℂ riemannXi Set.univ := by
      intro z _
      exact xi_entire.analyticAt z
    have h0_order_ne_top : analyticOrderAt riemannXi 0 ≠ ⊤ := by
      have h0_order_zero : analyticOrderAt riemannXi 0 = 0 := by
        exact (xi_entire.analyticAt 0).analyticOrderAt_eq_zero.2 (by
          unfold riemannXi
          norm_num)
      simp [h0_order_zero]
    have hρ_analytic : AnalyticAt ℂ riemannXi ρ.val := xi_entire.analyticAt ρ.val
    have hρ_order_ne_top : analyticOrderAt riemannXi ρ.val ≠ ⊤ :=
      AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
        (hf := hxi_analytic) (U := Set.univ) (x := 0) (y := ρ.val)
        isPreconnected_univ (by simp) (by simp) h0_order_ne_top
    have hρ_orderAt_ne_zero : analyticOrderAt riemannXi ρ.val ≠ 0 :=
      (hρ_analytic.analyticOrderAt_ne_zero).2 hρ_zero
    have hρ_orderNat_ne_zero : analyticOrderNatAt riemannXi ρ.val ≠ 0 := by
      intro hzero
      exact hρ_orderAt_ne_zero
        (by simpa [hzero] using (Nat.cast_analyticOrderNatAt hρ_order_ne_top).symm)
    exact Nat.pos_of_ne_zero hρ_orderNat_ne_zero

noncomputable instance : Countable xiZeroSetMultiplicity.Zero := by
  simpa [xiZeroSetMultiplicity] using (inferInstance : Countable NontrivialZero)

/-- The honest genus-1 canonical product for `riemannXi`, counted with multiplicity. -/
noncomputable def xiMultiplicityE1Prod (s : ℂ) : ℂ :=
  xiZeroSetMultiplicity.canonicalProductZeroSetMultiplicity s

@[simp] theorem xiMultiplicityE1Prod_eq_xiE1ProdWithMultiplicity (s : ℂ) :
    xiMultiplicityE1Prod s = xiE1ProdWithMultiplicity s := by
  rfl

/-- General Hadamard factorization for `riemannXi`, specialized to order `≤ 1`. -/
theorem xi_hadamard_factorization_with_multiplicity_polynomial
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    ∃ g : Polynomial ℂ,
      g.natDegree ≤ 1 ∧
      ∀ s : ℂ,
        riemannXi s =
          Complex.exp (g.eval s) *
            Hadamard.canonicalProductZeroSetMultiplicityRank xiZeroSetMultiplicity 1 s := by
  have h_zeros_only :
      ∀ s : ℂ,
        riemannXi s = 0 ↔ ∃ ρ : xiZeroSetMultiplicity.Zero, s = xiZeroSetMultiplicity.z ρ := by
    intro s
    simpa [xiZeroSetMultiplicity] using (xi_zeros_are_nontrivial_zeros (s := s))
  have h_inj : Function.Injective xiZeroSetMultiplicity.z := by
    intro ρ ρ' h
    exact Subtype.ext h
  have h_z_ne_zero : ∀ ρ : xiZeroSetMultiplicity.Zero, xiZeroSetMultiplicity.z ρ ≠ 0 := by
    intro ρ
    exact ρ.ne_zero
  have h_mult :
      ∀ ρ : xiZeroSetMultiplicity.Zero,
        analyticOrderNatAt riemannXi (xiZeroSetMultiplicity.z ρ) =
          xiZeroSetMultiplicity.mult ρ := by
    intro ρ
    rfl
  simpa using
    (Hadamard.hadamard_factorization_general
      (f := riemannXi)
      (hf_entire := xi_entire)
      (hf_finite := hfinite)
      (lam := 1)
      (hlam := by positivity)
      (hf_order_le := horder)
      (Z := xiZeroSetMultiplicity)
      (h_zeros_only := h_zeros_only)
      (h_inj := h_inj)
      (h_z_ne_zero := h_z_ne_zero)
      (h_mult := h_mult))

/-- A linear-exponential form of the multiplicity-aware Hadamard factorization for `riemannXi`. -/
theorem xi_hadamard_factorization_with_multiplicity
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    ∃ a b : ℂ, ∀ s : ℂ,
      riemannXi s = Complex.exp (a * s + b) * xiMultiplicityE1Prod s := by
  obtain ⟨g, hgdeg, hgfac⟩ :=
    xi_hadamard_factorization_with_multiplicity_polynomial hfinite horder
  obtain ⟨a, b, hab⟩ := Hadamard.polynomial_eval_eq_linear_of_natDegree_le_one g hgdeg
  refine ⟨a, b, ?_⟩
  intro s
  calc
    riemannXi s
        = Complex.exp (g.eval s) *
            Hadamard.canonicalProductZeroSetMultiplicityRank xiZeroSetMultiplicity 1 s := hgfac s
    _ = Complex.exp (a * s + b) *
          Hadamard.canonicalProductZeroSetMultiplicityRank xiZeroSetMultiplicity 1 s := by
            rw [hab s]
    _ = Complex.exp (a * s + b) * xiMultiplicityE1Prod s := by
          simp [xiMultiplicityE1Prod, Hadamard.canonicalProductZeroSetMultiplicityRank_one]

theorem xi_factorization_prod_with_multiplicity_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    xiFactorizationProdWithMultiplicity := by
  obtain ⟨a, b, hξ⟩ := xi_hadamard_factorization_with_multiplicity hfinite horder
  refine ⟨a, b, ?_⟩
  intro s
  simpa using hξ s

end LiCriterion
