/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
/-!
# maximal-ideal limit from displayed factors

This file carries the displayed `C π` factors from the infinite Hensel
prefixes through the maximal-ideal complete-limit argument.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- each coefficient sequence of the displayed-factor
infinite `g`-approximants is adic Cauchy for the maximal-ideal filtration. -/
theorem henselFactorization_infiniteG_coeff_adicCoeffCauchy_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (i : ℕ) :
    henselFactorizationAdicCoeffCauchy (IsLocalRing.maximalIdeal R)
      (fun N : ℕ =>
        (henselFactorizationHenselIterate π g0
          (henselFactorizationInfinitePCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N).coeff i) := by
  exact henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    (IsLocalRing.maximalIdeal R)
    (Pseq := fun N : ℕ =>
      henselFactorizationHenselIterate π g0
        (henselFactorizationInfinitePCorrOfMemSpan
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N)
    (by
      intro M N hMN i
      exact henselFactorization_infiniteGIter_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd hMN i)
    i

/-- the displayed-factor infinite `g`-approximants have a
bounded polynomial limit obtained from their coefficientwise adic limits. -/
theorem henselFactorization_exists_infiniteG_limitPolynomial_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ G : R[X], G.natDegree ≤ m ∧
      ∀ n i : ℕ,
        (henselFactorizationHenselIterate π g0
            (henselFactorizationInfinitePCorrOfMemSpan
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) n - G).coeff i ∈
          IsLocalRing.maximalIdeal R ^ n := by
  exact
    henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
      (IsLocalRing.maximalIdeal R)
      (N := m)
      (Pseq := fun n : ℕ =>
        henselFactorizationHenselIterate π g0
          (henselFactorizationInfinitePCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (henselFactorization_infiniteGIter_natDegree_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd)
      (fun i =>
        henselFactorization_infiniteG_coeff_adicCoeffCauchy_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd i)

/-- each coefficient sequence of the displayed-factor
infinite `h`-approximants is adic Cauchy for the maximal-ideal filtration. -/
theorem henselFactorization_infiniteH_coeff_adicCoeffCauchy_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (i : ℕ) :
    henselFactorizationAdicCoeffCauchy (IsLocalRing.maximalIdeal R)
      (fun N : ℕ =>
        (henselFactorizationHenselIterate π h0
          (henselFactorizationInfiniteQCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N).coeff i) := by
  exact henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    (IsLocalRing.maximalIdeal R)
    (Pseq := fun N : ℕ =>
      henselFactorizationHenselIterate π h0
        (henselFactorizationInfiniteQCorrOfMemSpan
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N)
    (by
      intro M N hMN i
      exact henselFactorization_infiniteHIter_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd hMN i)
    i

/-- the displayed-factor infinite `h`-approximants have a
bounded polynomial limit obtained from their coefficientwise adic limits. -/
theorem henselFactorization_exists_infiniteH_limitPolynomial_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ H : R[X], H.natDegree ≤ d - m ∧
      ∀ n i : ℕ,
        (henselFactorizationHenselIterate π h0
            (henselFactorizationInfiniteQCorrOfMemSpan
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) n - H).coeff i ∈
          IsLocalRing.maximalIdeal R ^ n := by
  exact
    henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
      (IsLocalRing.maximalIdeal R)
      (N := d - m)
      (Pseq := fun n : ℕ =>
        henselFactorizationHenselIterate π h0
          (henselFactorizationInfiniteQCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          n)
      (henselFactorization_infiniteHIter_natDegree_le_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd)
      (fun i =>
        henselFactorization_infiniteH_coeff_adicCoeffCauchy_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd i)

/-- complete-limit factorization from displayed initial
principal-element errors, without assuming `maximalIdeal ≤ (π)`. -/
theorem henselFactorization_exists_limit_factorization_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hh0map : h0.map (IsLocalRing.residue R) = hbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    ∃ G H : R[X],
      G.natDegree ≤ m ∧ H.natDegree ≤ d - m ∧ f = G * H ∧
        G.map (IsLocalRing.residue R) = gbar ∧
        H.map (IsLocalRing.residue R) = hbar := by
  rcases henselFactorization_exists_infiniteG_limitPolynomial_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd with
    ⟨G, hGdeg, hGlim⟩
  rcases henselFactorization_exists_infiniteH_limitPolynomial_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd with
    ⟨H, hHdeg, hHlim⟩
  have hfactor : f = G * H := by
    apply henselFactorization_limit_factor_eq_of_approximants
      (I := IsLocalRing.maximalIdeal R)
      (Gseq := fun n : ℕ =>
        henselFactorizationHenselIterate π g0
          (henselFactorizationInfinitePCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
          n)
      (Hseq := fun n : ℕ =>
        henselFactorizationHenselIterate π h0
          (henselFactorizationInfiniteQCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
          n)
    · intro n i
      exact (Ideal.pow_le_pow_right (Nat.le_succ n))
        (henselFactorization_infiniteCorr_error_coeff_mem_maximalIdeal_pow_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd n i)
    · exact hGlim
    · exact hHlim
  have hGred : ∀ i : ℕ, (G - g0).coeff i ∈ IsLocalRing.maximalIdeal R :=
    henselFactorization_limit_reduction_of_approx_reduction
      (I := IsLocalRing.maximalIdeal R)
      (Pseq := fun n : ℕ =>
        henselFactorizationHenselIterate π g0
          (henselFactorizationInfinitePCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
          n)
      (P := G) (P0 := g0) hGlim
      (henselFactorization_infiniteGIter_reduction_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
  have hHred : ∀ i : ℕ, (H - h0).coeff i ∈ IsLocalRing.maximalIdeal R :=
    henselFactorization_limit_reduction_of_approx_reduction
      (I := IsLocalRing.maximalIdeal R)
      (Pseq := fun n : ℕ =>
        henselFactorizationHenselIterate π h0
          (henselFactorizationInfiniteQCorrOfMemSpan
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
          n)
      (P := H) (P0 := h0) hHlim
      (henselFactorization_infiniteHIter_reduction_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hfactor0 hbezFactor hmd)
  have hGmap0 :
      G.map (IsLocalRing.residue R) =
        g0.map (IsLocalRing.residue R) :=
    henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal hGred
  have hHmap0 :
      H.map (IsLocalRing.residue R) =
        h0.map (IsLocalRing.residue R) :=
    henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal hHred
  refine ⟨G, H, hGdeg, hHdeg, hfactor, ?_, ?_⟩
  · rw [hGmap0, hg0map]
  · rw [hHmap0, hh0map]


end Valuations
end AlgebraicNumberTheory

end
