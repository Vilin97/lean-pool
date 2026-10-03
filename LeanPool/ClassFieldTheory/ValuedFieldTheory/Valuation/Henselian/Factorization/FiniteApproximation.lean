/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
/-!
# finite Hensel prefixes

This file isolates the reusable one-step extension in the finite
Hensel construction.  Compatible prefixes themselves are assembled once, as
HenselFactorizationFinitePrefixState, in the next layer.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- extend a finite Hensel prefix by one step in the
displayed-factor principal-element form.  The current iterates are automatically
congruent to the initial lifts modulo `(π)`, so the extension uses only
`π ∈ m` and the displayed Bezout-error factor. -/
theorem henselFactorization_extend_finite_prefix_one_step_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d n : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0 : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (pCorr qCorr : ℕ → R[X])
    (hprefix :
      ∀ r : ℕ, r ≤ n →
        ∃ fr : R[X],
          f - henselFactorizationHenselIterate π g0 pCorr r *
              henselFactorizationHenselIterate π h0 qCorr r =
            Polynomial.C (π ^ (r + 1)) * fr)
    {fn : R[X]}
    (hfactor :
      f - henselFactorizationHenselIterate π g0 pCorr n *
          henselFactorizationHenselIterate π h0 qCorr n =
        Polynomial.C (π ^ (n + 1)) * fn)
    (hgDeg : (henselFactorizationHenselIterate π g0 pCorr n).natDegree ≤ m)
    (hhDeg : (henselFactorizationHenselIterate π h0 qCorr n).natDegree ≤ d - m) :
    ∃ p q fnNext : R[X],
      p.natDegree ≤ m ∧ q.natDegree ≤ d - m ∧
        (∀ r : ℕ, r ≤ n →
          ∃ fr : R[X],
            f - henselFactorizationHenselIterate π g0
                  (Function.update pCorr (n + 1) p) r *
                henselFactorizationHenselIterate π h0
                  (Function.update qCorr (n + 1) q) r =
              Polynomial.C (π ^ (r + 1)) * fr) ∧
          f - henselFactorizationHenselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1) *
              henselFactorizationHenselIterate π h0
                (Function.update qCorr (n + 1) q) (n + 1) =
            Polynomial.C (π ^ (n + 2)) * fnNext ∧
            (henselFactorizationHenselIterate π g0
                (Function.update pCorr (n + 1) p) (n + 1)).natDegree ≤ m ∧
              (henselFactorizationHenselIterate π h0
                  (Function.update qCorr (n + 1) q) (n + 1)).natDegree ≤
                d - m ∧
                (∀ i : ℕ,
                  (henselFactorizationHenselIterate π g0
                      (Function.update pCorr (n + 1) p) (n + 1) -
                    g0).coeff i ∈ IsLocalRing.maximalIdeal R) ∧
                  (∀ i : ℕ,
                    (henselFactorizationHenselIterate π h0
                        (Function.update qCorr (n + 1) q) (n + 1) -
                      h0).coeff i ∈ IsLocalRing.maximalIdeal R) := by
  have hπpow : π ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hπne
  have hgSpan :
      ∀ i : ℕ,
        (henselFactorizationHenselIterate π g0 pCorr n - g0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_henselIterate_span_singleton (π := π) g0 pCorr n
  have hhSpan :
      ∀ i : ℕ,
        (henselFactorizationHenselIterate π h0 qCorr n - h0).coeff i ∈
          Ideal.span ({π} : Set R) :=
    henselFactorization_henselIterate_span_singleton (π := π) h0 qCorr n
  rcases henselFactorization_exists_one_step_update_with_degree_bounds_of_mem_span
      (π := π) (n := n + 1) (Nat.succ_pos n) hπpow hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (g := henselFactorizationHenselIterate π g0 pCorr n)
      (h := henselFactorizationHenselIterate π h0 qCorr n)
      (fn := fn) (a := a) (b := b) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hgSpan hhSpan hgDeg hhDeg hg0map hg0nat hgbar_nat hglead
      hh0 hbezFactor hfactor hmd with
    ⟨p, q, fnNext, hpDeg, hqDeg, hgNextDeg, hhNextDeg,
      _hgNextSpan, _hhNextSpan, hgNextRed, hhNextRed, hfactorNextRaw⟩
  have hfactorNext :
      f - (henselFactorizationHenselIterate π g0 pCorr n +
            Polynomial.C (π ^ (n + 1)) * p) *
          (henselFactorizationHenselIterate π h0 qCorr n +
            Polynomial.C (π ^ (n + 1)) * q) =
        Polynomial.C (π ^ (n + 2)) * fnNext := by
    simpa [Nat.add_assoc] using hfactorNextRaw
  refine ⟨p, q, fnNext, hpDeg, hqDeg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases hprefix r hr with ⟨fr, hfr⟩
    exact ⟨fr,
      henselFactorization_henselIterate_update_preserves_factor_of_le
        (π := π) (pCorr := pCorr) (qCorr := qCorr)
        (n := n) (r := r) hr p q fr hfr⟩
  · exact henselFactorization_henselIterate_update_next_factor
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      pCorr qCorr n p q fnNext hfactorNext
  · rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (n := n) (c := p)]
    exact hgNextDeg
  · rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (n := n) (c := q)]
    exact hhNextDeg
  · intro i
    rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (n := n) (c := p)]
    exact hgNextRed i
  · intro i
    rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (n := n) (c := q)]
    exact hhNextRed i

end Valuations
end AlgebraicNumberTheory

end
