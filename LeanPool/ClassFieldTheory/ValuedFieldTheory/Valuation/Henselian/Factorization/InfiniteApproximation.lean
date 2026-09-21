/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
/-!
# compatible Hensel prefixes

This file turns the finite Hensel-prefix construction into a recursive family
of compatible prefixes.  The completion/limit argument is kept for the next
layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the data carried by a finite Hensel prefix at stage `N`.
The fields are exactly the invariants needed to extend the prefix one more
step and later pass to the complete limit. -/
structure HenselFactorizationFinitePrefixState
    {R : Type*} [CommRing R] [IsLocalRing R] (π : R)
    (f g0 h0 : R[X]) (m d N : ℕ) where
  /-- The polynomial corrections for the first factor at each stage. -/
  pCorr : ℕ → R[X]
  /-- The polynomial corrections for the second factor at each stage. -/
  qCorr : ℕ → R[X]
  /-- The residual error polynomial at the current stage. -/
  fErr : R[X]
  /-- Every prefix through the current stage factors the error by the corresponding power of `π`. -/
  prefixFactor :
    ∀ r : ℕ, r ≤ N →
      ∃ fr : R[X],
        f - henselFactorization_henselIterate π g0 pCorr r *
            henselFactorization_henselIterate π h0 qCorr r =
          Polynomial.C (π ^ (r + 1)) * fr
  /-- Each correction for the first factor has degree at most `m`. -/
  pCorrDeg : ∀ r : ℕ, (pCorr r).natDegree ≤ m
  /-- Each correction for the second factor has degree at most `d - m`. -/
  qCorrDeg : ∀ r : ℕ, (qCorr r).natDegree ≤ d - m
  /-- At stage `N`, the factorization error is `π ^ (N + 1)` times `fErr`. -/
  factor :
    f - henselFactorization_henselIterate π g0 pCorr N *
        henselFactorization_henselIterate π h0 qCorr N =
      Polynomial.C (π ^ (N + 1)) * fErr
  /-- The first approximate factor at stage `N` has degree at most `m`. -/
  gDeg : (henselFactorization_henselIterate π g0 pCorr N).natDegree ≤ m
  /-- The second approximate factor at stage `N` has degree at most `d - m`. -/
  hDeg : (henselFactorization_henselIterate π h0 qCorr N).natDegree ≤ d - m
  /-- The first approximate factor remains congruent to `g0` modulo the maximal ideal. -/
  gRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π g0 pCorr N - g0).coeff i ∈
        IsLocalRing.maximalIdeal R
  /-- The second approximate factor remains congruent to `h0` modulo the maximal ideal. -/
  hRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π h0 qCorr N - h0).coeff i ∈
        IsLocalRing.maximalIdeal R

/-- the stage `0` prefix state from a displayed
finite-minimum factor of the initial error. -/
def henselFactorization_initialPrefixState_of_factor
    {R : Type*} [CommRing R] [IsLocalRing R]
    {π : R} {f g0 h0 f1 : R[X]} {m d : ℕ}
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hg0nat : g0.natDegree = m)
    (hh0deg : h0.natDegree ≤ d - m) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d 0 := by
  refine
    { pCorr := fun _ => 0
      qCorr := fun _ => 0
      fErr := f1
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := ?_
      hDeg := ?_
      gRed := ?_
      hRed := ?_ }
  · intro r hr
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    subst r
    exact ⟨f1, by simpa using hfactor0⟩
  · intro r
    simp
  · intro r
    simp
  · simpa using hfactor0
  · simp [hg0nat]
  · simpa using hh0deg
  · intro i
    simp
  · intro i
    simp

/-- Choose an extension of a prefix state by one Hensel correction in the
displayed-factor form. -/
def henselFactorization_chosenNextPrefixState_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d (N + 1) := by
  classical
  let hstep := henselFactorization_extend_finite_prefix_one_step_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
      (gbar := gbar) (m := m) (d := d) (n := N)
      hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
      s.pCorr s.qCorr s.prefixFactor s.factor s.gDeg s.hDeg
  let p := Classical.choose hstep
  have hpstep := Classical.choose_spec hstep
  let q := Classical.choose hpstep
  have hqstep := Classical.choose_spec hpstep
  let fnNext := Classical.choose hqstep
  have hspec := Classical.choose_spec hqstep
  have hpdeg : p.natDegree ≤ m := hspec.1
  have hqdeg : q.natDegree ≤ d - m := hspec.2.1
  have hprefixOld :
      ∀ r : ℕ, r ≤ N →
        ∃ fr : R[X],
          f - henselFactorization_henselIterate π g0
                (Function.update s.pCorr (N + 1) p) r *
              henselFactorization_henselIterate π h0
                (Function.update s.qCorr (N + 1) q) r =
            Polynomial.C (π ^ (r + 1)) * fr := hspec.2.2.1
  have hfactorNext :
      f - henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) *
          henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) =
        Polynomial.C (π ^ (N + 2)) * fnNext := hspec.2.2.2.1
  have hgNextDeg :
      (henselFactorization_henselIterate π g0
        (Function.update s.pCorr (N + 1) p) (N + 1)).natDegree ≤ m :=
    hspec.2.2.2.2.1
  have hhNextDeg :
      (henselFactorization_henselIterate π h0
        (Function.update s.qCorr (N + 1) q) (N + 1)).natDegree ≤ d - m :=
    hspec.2.2.2.2.2.1
  have hgNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) - g0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.1
  have hhNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) - h0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.2
  refine
    { pCorr := Function.update s.pCorr (N + 1) p
      qCorr := Function.update s.qCorr (N + 1) q
      fErr := fnNext
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := hgNextDeg
      hDeg := hhNextDeg
      gRed := hgNextRed
      hRed := hhNextRed }
  · intro r hr
    by_cases htop : r = N + 1
    · subst r
      exact ⟨fnNext, by simpa [Nat.add_assoc] using hfactorNext⟩
    · have hrn : r ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hr htop)
      exact hprefixOld r hrn
  · exact henselFactorization_update_corr_natDegree_le s.pCorrDeg hpdeg
  · exact henselFactorization_update_corr_natDegree_le s.qCorrDeg hqdeg
  · simpa [Nat.add_assoc] using hfactorNext

/-- in the displayed-factor prefix extension the `p`
correction changes only at the newly constructed index. -/
theorem henselFactorization_chosenNextPrefixState_pCorr_of_ne_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N r : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N)
    (hr : r ≠ N + 1) :
    (henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd s).pCorr r =
      s.pCorr r := by
  unfold henselFactorization_chosenNextPrefixState_of_mem_span
  simp [Function.update_of_ne hr]

/-- in the displayed-factor prefix extension the `q`
correction changes only at the newly constructed index. -/
theorem henselFactorization_chosenNextPrefixState_qCorr_of_ne_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N r : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N)
    (hr : r ≠ N + 1) :
    (henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd s).qCorr r =
      s.qCorr r := by
  unfold henselFactorization_chosenNextPrefixState_of_mem_span
  simp [Function.update_of_ne hr]

/-- recursively chosen compatible finite Hensel prefixes in
the displayed-factor displayed-factor form. -/
def henselFactorization_prefixStateSeq_of_mem_span
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
    (hmd : m ≤ d) :
    (N : ℕ) → HenselFactorizationFinitePrefixState π f g0 h0 m d N
  | 0 =>
      henselFactorization_initialPrefixState_of_factor
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (f1 := f1) (m := m) (d := d)
        hfactor0 hg0nat hh0deg
  | N + 1 =>
      henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N)

/-- coherence of the displayed-factor `p`-corrections:
later prefix states agree with earlier ones at every already constructed
index. -/
theorem henselFactorization_prefixStateSeq_pCorr_eq_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).pCorr M =
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd M).pCorr M := by
  intro M N hMN
  induction N generalizing M with
  | zero =>
      have hM0 : M = 0 := Nat.eq_zero_of_le_zero hMN
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hMN htop)
        calc
          (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd (N + 1)).pCorr M =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd N).pCorr M := by
              simpa [henselFactorization_prefixStateSeq_of_mem_span] using
                henselFactorization_chosenNextPrefixState_pCorr_of_ne_of_mem_span
                  (π := π) hπne hπmem
                  (f := f) (g0 := g0) (h0 := h0)
                  (a := a) (b := b) (e := e)
                  (gbar := gbar) (m := m) (d := d) (N := N) (r := M)
                  hf hg0map hg0nat hgbar_nat hglead hh0deg
                  hbezFactor hmd
                  (henselFactorization_prefixStateSeq_of_mem_span
                    (π := π) (f := f) (g0 := g0) (h0 := h0)
                    (a := a) (b := b) (f1 := f1) (e := e)
                    (gbar := gbar) (m := m) (d := d)
                    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
                    hfactor0 hbezFactor hmd N)
                  htop
          _ =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd M).pCorr M := ih hMN'

/-- coherence of the displayed-factor `q`-corrections:
later prefix states agree with earlier ones at every already constructed
index. -/
theorem henselFactorization_prefixStateSeq_qCorr_eq_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).qCorr M =
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd M).qCorr M := by
  intro M N hMN
  induction N generalizing M with
  | zero =>
      have hM0 : M = 0 := Nat.eq_zero_of_le_zero hMN
      subst M
      rfl
  | succ N ih =>
      by_cases htop : M = N + 1
      · subst M
        rfl
      · have hMN' : M ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hMN htop)
        calc
          (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd (N + 1)).qCorr M =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd N).qCorr M := by
              simpa [henselFactorization_prefixStateSeq_of_mem_span] using
                henselFactorization_chosenNextPrefixState_qCorr_of_ne_of_mem_span
                  (π := π) hπne hπmem
                  (f := f) (g0 := g0) (h0 := h0)
                  (a := a) (b := b) (e := e)
                  (gbar := gbar) (m := m) (d := d) (N := N) (r := M)
                  hf hg0map hg0nat hgbar_nat hglead hh0deg
                  hbezFactor hmd
                  (henselFactorization_prefixStateSeq_of_mem_span
                    (π := π) (f := f) (g0 := g0) (h0 := h0)
                    (a := a) (b := b) (f1 := f1) (e := e)
                    (gbar := gbar) (m := m) (d := d)
                    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
                    hfactor0 hbezFactor hmd N)
                  htop
          _ =
            (henselFactorization_prefixStateSeq_of_mem_span
              (π := π) (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd M).qCorr M := ih hMN'

/-- the infinite `p`-correction sequence from the
displayed-factor displayed-factor prefix construction. -/
def henselFactorization_infinitePCorr_of_mem_span
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
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).pCorr n

/-- the infinite `q`-correction sequence from the
displayed-factor displayed-factor prefix construction. -/
def henselFactorization_infiniteQCorr_of_mem_span
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
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).qCorr n

/-- the displayed-factor infinite `p`-corrections retain the
stated degree bound. -/
theorem henselFactorization_infinitePCorr_natDegree_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ n : ℕ,
      (henselFactorization_infinitePCorr_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd n).natDegree ≤ m := by
  intro n
  unfold henselFactorization_infinitePCorr_of_mem_span
  exact
    (henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd n).pCorrDeg n

/-- the displayed-factor infinite `q`-corrections retain the
stated degree bound. -/
theorem henselFactorization_infiniteQCorr_natDegree_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ n : ℕ,
      (henselFactorization_infiniteQCorr_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd n).natDegree ≤ d - m := by
  intro n
  unfold henselFactorization_infiniteQCorr_of_mem_span
  exact
    (henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd n).qCorrDeg n

/-- a displayed-factor finite prefix state's
`p`-correction agrees with the extracted infinite `p`-correction at every
constructed index. -/
theorem henselFactorization_prefixStateSeq_pCorr_eq_infinite_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {r N : ℕ}, r ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).pCorr r =
        henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd r := by
  intro r N hr
  unfold henselFactorization_infinitePCorr_of_mem_span
  exact henselFactorization_prefixStateSeq_pCorr_eq_of_le_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd hr

/-- a displayed-factor finite prefix state's
`q`-correction agrees with the extracted infinite `q`-correction at every
constructed index. -/
theorem henselFactorization_prefixStateSeq_qCorr_eq_infinite_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {r N : ℕ}, r ≤ N →
      (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N).qCorr r =
        henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd r := by
  intro r N hr
  unfold henselFactorization_infiniteQCorr_of_mem_span
  exact henselFactorization_prefixStateSeq_qCorr_eq_of_le_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd hr

/-- every finite displayed-factor factorization invariant
transfers from the coherent prefix states to the extracted infinite correction
sequences. -/
theorem henselFactorization_infiniteCorr_factor_prefix_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      ∃ fN : R[X],
        f - henselFactorization_henselIterate π g0
              (henselFactorization_infinitePCorr_of_mem_span
                (π := π) hπne hπmem
                (f := f) (g0 := g0) (h0 := h0)
                (a := a) (b := b) (f1 := f1) (e := e)
                (gbar := gbar) (m := m) (d := d)
                hf hg0map hg0nat hgbar_nat hglead hh0deg
                hfactor0 hbezFactor hmd) N *
            henselFactorization_henselIterate π h0
              (henselFactorization_infiniteQCorr_of_mem_span
                (π := π) hπne hπmem
                (f := f) (g0 := g0) (h0 := h0)
                (a := a) (b := b) (f1 := f1) (e := e)
                (gbar := gbar) (m := m) (d := d)
                hf hg0map hg0nat hgbar_nat hglead hh0deg
                hfactor0 hbezFactor hmd) N =
          Polynomial.C (π ^ (N + 1)) * fN := by
  intro N
  let S :=
    henselFactorization_prefixStateSeq_of_mem_span
      (π := π) (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd N
  have hp :
      henselFactorization_henselIterate π g0 S.pCorr N =
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N := by
    apply henselFactorization_henselIterate_eq_of_corr_eq_le
    intro k hk
    simpa [S] using
      henselFactorization_prefixStateSeq_pCorr_eq_infinite_of_le_of_mem_span
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd (r := k) (N := N) hk
  have hq :
      henselFactorization_henselIterate π h0 S.qCorr N =
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N := by
    apply henselFactorization_henselIterate_eq_of_corr_eq_le
    intro k hk
    simpa [S] using
      henselFactorization_prefixStateSeq_qCorr_eq_infinite_of_le_of_mem_span
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (a := a) (b := b) (f1 := f1) (e := e)
        (gbar := gbar) (m := m) (d := d)
        hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
        hfactor0 hbezFactor hmd (r := k) (N := N) hk
  exact ⟨S.fErr, by simpa [S, hp, hq] using S.factor⟩

/-- the factorization error of the displayed-factor infinite
approximants is coefficientwise in the corresponding high power of the
maximal ideal. -/
theorem henselFactorization_infiniteCorr_error_coeff_mem_maximalIdeal_pow_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N i : ℕ,
      (f - henselFactorization_henselIterate π g0
            (henselFactorization_infinitePCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) N *
          henselFactorization_henselIterate π h0
            (henselFactorization_infiniteQCorr_of_mem_span
              (π := π) hπne hπmem
              (f := f) (g0 := g0) (h0 := h0)
              (a := a) (b := b) (f1 := f1) (e := e)
              (gbar := gbar) (m := m) (d := d)
              hf hg0map hg0nat hgbar_nat hglead hh0deg
              hfactor0 hbezFactor hmd) N).coeff i ∈
        IsLocalRing.maximalIdeal R ^ (N + 1) := by
  intro N i
  rcases henselFactorization_infiniteCorr_factor_prefix_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd N with
    ⟨fN, hfactor⟩
  exact henselFactorization_coeff_mem_maximalIdeal_pow_of_factor_of_mem
    (π := π) (n := N + 1) hπmem hfactor i

/-- the displayed-factor `g`-approximants keep the construction
degree bound. -/
theorem henselFactorization_infiniteGIter_natDegree_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      (henselFactorization_henselIterate π g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N).natDegree ≤ m := by
  exact henselFactorization_henselIterate_natDegree_le
    (π := π) (F0 := g0)
    (corr := henselFactorization_infinitePCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)
    (M := m)
    (by simp [hg0nat])
    (henselFactorization_infinitePCorr_natDegree_le_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- the displayed-factor `h`-approximants keep the construction
degree bound. -/
theorem henselFactorization_infiniteHIter_natDegree_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N : ℕ,
      (henselFactorization_henselIterate π h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N).natDegree ≤ d - m := by
  exact henselFactorization_henselIterate_natDegree_le
    (π := π) (F0 := h0)
    (corr := henselFactorization_infiniteQCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)
    (M := d - m)
    hh0deg
    (henselFactorization_infiniteQCorr_natDegree_le_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- the displayed-factor infinite `g`-approximants keep the
original residual class of `g0`. -/
theorem henselFactorization_infiniteGIter_reduction_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N i : ℕ,
      (henselFactorization_henselIterate π g0
        (henselFactorization_infinitePCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N - g0).coeff i ∈
        IsLocalRing.maximalIdeal R :=
  henselFactorization_henselIterate_reduction_of_mem
    (π := π) hπmem g0
    (henselFactorization_infinitePCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- the displayed-factor infinite `h`-approximants keep the
original residual class of `h0`. -/
theorem henselFactorization_infiniteHIter_reduction_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ N i : ℕ,
      (henselFactorization_henselIterate π h0
        (henselFactorization_infiniteQCorr_of_mem_span
          (π := π) hπne hπmem
          (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd)
        N - h0).coeff i ∈
        IsLocalRing.maximalIdeal R :=
  henselFactorization_henselIterate_reduction_of_mem
    (π := π) hπmem h0
    (henselFactorization_infiniteQCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- coefficientwise Cauchy estimate for the displayed-factor
infinite `g`-approximants. -/
theorem henselFactorization_infiniteGIter_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N → ∀ i : ℕ,
      (henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N -
        henselFactorization_henselIterate π g0
          (henselFactorization_infinitePCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          M).coeff i ∈
        IsLocalRing.maximalIdeal R ^ (M + 1) :=
  henselFactorization_henselIterate_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem
    (π := π) hπmem g0
    (henselFactorization_infinitePCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)

/-- coefficientwise Cauchy estimate for the displayed-factor
infinite `h`-approximants. -/
theorem henselFactorization_infiniteHIter_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem_span
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
    (hmd : m ≤ d) :
    ∀ {M N : ℕ}, M ≤ N → ∀ i : ℕ,
      (henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          N -
        henselFactorization_henselIterate π h0
          (henselFactorization_infiniteQCorr_of_mem_span
            (π := π) hπne hπmem
            (f := f) (g0 := g0) (h0 := h0)
            (a := a) (b := b) (f1 := f1) (e := e)
            (gbar := gbar) (m := m) (d := d)
            hf hg0map hg0nat hgbar_nat hglead hh0deg
            hfactor0 hbezFactor hmd)
          M).coeff i ∈
        IsLocalRing.maximalIdeal R ^ (M + 1) :=
  henselFactorization_henselIterate_sub_coeff_mem_maximalIdeal_pow_of_le_of_mem
    (π := π) hπmem h0
    (henselFactorization_infiniteQCorr_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0)
      (a := a) (b := b) (f1 := f1) (e := e)
      (gbar := gbar) (m := m) (d := d)
      hf hg0map hg0nat hgbar_nat hglead hh0deg
      hfactor0 hbezFactor hmd)


end Valuations
end AlgebraicNumberTheory

end
