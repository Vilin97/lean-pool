/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.FunctionalEquation

/-!
# The Generalized Riemann Hypothesis for `ζ_K`  — the paper's sole assumption

Belabas–Friedman (arXiv:1305.0035, Theorem 1, audited verbatim): *"Assume GRH, i.e. that
`ζ_K(s) ≠ 0` and `ζ_ℚ(s) ≠ 0` whenever `Re(s) > 1/2`."*

We state this **genuinely, with no placeholder**: the (unique, by
`IsCompletedDedekindZeta.eqOn`) completed zeta `Λ_K` is quantified through its
characterisation, and GRH says it does not vanish on the open half-plane `Re s > 1/2`
away from the pole `s = 1`. Since the completing prefactor `|Δ_K|^{s/2}·γ_K(s)` is
nonvanishing for `Re s > 0` (`gammaFactor_ne_zero_of_re_pos`), this is precisely the
paper's "`ζ_K(s) ≠ 0` for `Re(s) > 1/2`". The `ζ_ℚ` half of the paper's assumption is
mathlib's `RiemannHypothesis`, taken as a separate hypothesis in Theorem 1.

It is always threaded as a **hypothesis argument** — never an `axiom` — so every result
stays axiom-clean. Non-vacuity (the existence of a `Λ` satisfying the characterisation)
is Hecke's theorem, the target of SP1-AGE/FE.
-/

namespace DedekindResidue

@[expose] public section

/-- **GRH for the Dedekind zeta function of `K`** (Belabas–Friedman's form, verbatim:
"`ζ_K(s) ≠ 0` … whenever `Re(s) > 1/2`"): every function satisfying the completed-zeta
characterisation `IsCompletedDedekindZeta K` is nonvanishing on `Re s > 1/2`, away from
the pole `s = 1`. All such functions agree away from `s = 0, 1`
(`IsCompletedDedekindZeta.eqOn`), so this quantification speaks about *the* completed
Dedekind zeta; its zeros there are exactly the zeros of the analytically continued `ζ_K`,
because the completing prefactor is nonvanishing on `Re s > 0`. -/
def GeneralizedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ →
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Λ s ≠ 0

end

end DedekindResidue
