/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.Normalisation

/-!
# The completed Dedekind zeta function, by characterisation  (SP1-FE interface)

Mathlib's `NumberField.dedekindZeta` is the `L`-series only — genuine (an honest convergent
sum) exactly on the half-plane `Re s > 1` and junk elsewhere. The completed zeta
`Λ_K(s) = |Δ_K|^{s/2}·Γℝ(s)^{r₁}·Γℂ(s)^{r₂}·ζ_K(s)` therefore cannot be *defined* through it
on all of `ℂ` without lying in the critical strip.

Instead we **characterise** it, with no placeholder anywhere:

* `completedZetaPrefactor K s = |Δ_K|^{s/2}·γ_K(s)` — genuine (a `cpow` and Gamma factors);
* `IsCompletedDedekindZeta K Λ` — `Λ` agrees with `completedZetaPrefactor · ζ_K` on
  `Re s > 1` **and** `s(s-1)Λ(s)` is entire.

By the identity theorem the two conditions determine `Λ` **uniquely**
(`IsCompletedDedekindZeta.unique`), so quantifying over `Λ` with this predicate *is*
talking about "the" completed Dedekind zeta. Hecke's theorem — the target of SP1-AGE —
is the **existence** statement (construct `Λ` as a Mellin transform of the ideal-class
theta integrals); the functional equation `Λ(1-s) = Λ(s)` is proven of that construction.

This interface is what the GRH predicate (`GRH.lean`) and Theorem 1 consume; nothing here
is a stub.
-/

namespace DedekindResidue

@[expose] public section

open NumberField

/-- The prefactor `|Δ_K|^{s/2} · Γℝ(s)^{r₁} · Γℂ(s)^{r₂}` completing the Dedekind zeta
function. Genuine on all of `ℂ` (a `cpow` of the positive real `|Δ_K|` and the Deligne
Gamma factors of `Normalisation.lean`). -/
noncomputable def completedZetaPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|discr K| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s

/-- **Characterisation of the completed Dedekind zeta function** `Λ_K`:
1. on the half-plane of absolute convergence `Re s > 1` (where mathlib's `dedekindZeta`
   is the honest convergent `L`-series), `Λ` is `|Δ_K|^{s/2}·γ_K(s)·ζ_K(s)`;
2. `s(s-1)·Λ(s)` extends to an entire function — `Λ` is analytic away from (at most
   simple) poles at `s = 0, 1`.

Note the *extends* in 2: a total function `Λ : ℂ → ℂ` carrying genuine poles stores junk
values at `0` and `1`, so `s(s-1)·Λ(s)` literally vanishes there while its analytic
continuation does not; the faithful rendering of "`s(s-1)Λ_K(s)` is entire" is the
existence of an entire `H` agreeing with it away from the two poles.

These two conditions determine `Λ` uniquely away from the poles
(`IsCompletedDedekindZeta.eqOn`): this predicate **is** "the" completed Dedekind zeta,
stated without first constructing the meromorphic continuation. Hecke's theorem
(`exists_isCompletedDedekindZeta`: existence of such a `Λ` via the theta-Mellin
construction) is what makes the predicate inhabited. -/
def IsCompletedDedekindZeta (K : Type*) [Field K] [NumberField K] (Λ : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → Λ s = completedZetaPrefactor K s * dedekindZeta K s)
    ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H
        ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 → H s = s * (s - 1) * Λ s

/-- **Uniqueness.** Any two functions satisfying the completed-zeta characterisation agree
away from the poles `s = 0, 1`: the entire functions `s(s-1)Λᵢ(s)` agree on the open
half-plane `Re s > 1`, hence everywhere by the identity theorem; cancel `s(s-1)`.
(No condition can pin the values *at* `0` and `1` — the genuine `Λ_K` has simple poles
there, so those values are junk by nature.) -/
theorem IsCompletedDedekindZeta.eqOn {K : Type*} [Field K] [NumberField K]
    {Λ₁ Λ₂ : ℂ → ℂ} (h₁ : IsCompletedDedekindZeta K Λ₁)
    (h₂ : IsCompletedDedekindZeta K Λ₂) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Λ₁ s = Λ₂ s := by
  obtain ⟨H₁, hH₁, hH₁eq⟩ := h₁.2
  obtain ⟨H₂, hH₂, hH₂eq⟩ := h₂.2
  have hagree : ∀ s : ℂ, H₁ s = H₂ s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hpre : Set.EqOn H₁ H₂ {s : ℂ | 1 < s.re} := by
      intro s hs
      have hs0' : s ≠ 0 := by
        rintro rfl
        norm_num [Set.mem_setOf_eq, Complex.zero_re] at hs
      have hs1' : s ≠ 1 := by
        rintro rfl
        norm_num [Set.mem_setOf_eq, Complex.one_re] at hs
      rw [hH₁eq s hs0' hs1', hH₂eq s hs0' hs1', h₁.1 s hs, h₂.1 s hs]
    have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num [Complex.ofReal_re]
    have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := H₁) (g := H₂)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hH₁)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hH₂)
      isPreconnected_univ (Set.mem_univ (2 : ℂ))
      (hpre.eventuallyEq_of_mem (hopen.mem_nhds h2mem))
    exact fun s => this (Set.mem_univ s)
  have h : s * (s - 1) * Λ₁ s = s * (s - 1) * Λ₂ s := by
    rw [← hH₁eq s hs0 hs1, ← hH₂eq s hs0 hs1]
    exact hagree s
  have hne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  exact mul_left_cancel₀ hne h

end

end DedekindResidue
