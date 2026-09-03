/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order
public import LeanPool.ZetaZeros.Meta.Attr

/-! # The vocabulary of the main results

Every notion appearing in the statements of the headline theorems: the zero counts, the
Hilbert-space objects of the key proposition, the pair-correlation apparatus, and the two
classical analytic inputs.

These are kept in one module, in the order `Challenge/Basic.lean` repeats them, and should stay
that way. Elaboration lifts a nested proof out of a definition's body into an auxiliary theorem
named after whichever definition in the *module* first needed it, so splitting these across
modules gives them names a single self-contained file cannot reproduce.
-/

@[expose] public section

namespace ZetaZeros

/-- The non-trivial zeros of the Riemann zeta function with imaginary part in `(0, T]`: the
zeros lying in the critical strip `0 < re s < 1`, as a set, so without multiplicity. -/
@[zz_tag "def_nontrivial_zeros"]
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- The multiplicity of `ρ` as a zero of the Riemann zeta function, i.e. its order of
vanishing there. -/
@[zz_tag "def_multiplicity"]
noncomputable def zeroMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]`, counted with multiplicity.
This is `N T` in the source. -/
@[zz_tag "def_N"]
noncomputable def zeroCount (T : ℝ) : ℕ := ∑ᶠ ρ ∈ nontrivialZeros T, zeroMultiplicity ρ

/-- The number of non-trivial zeros with imaginary part in `(0, T]` that are simple and lie on
the critical line `re s = 1/2`. This is `N₀ˢ T` in the source. -/
@[zz_tag "def_N_simple"]
noncomputable def simpleOnLineCount (T : ℝ) : ℕ :=
  {ρ ∈ nontrivialZeros T | ρ.re = 1 / 2 ∧ zeroMultiplicity ρ = 1}.ncard

/-- The number of distinct non-trivial zeros with imaginary part in `(0, T]`. This is `N_d T`
in the source. -/
@[zz_tag "def_N_distinct"]
noncomputable def distinctZeroCount (T : ℝ) : ℕ := (nontrivialZeros T).ncard

/-- The Fourier transform of a compactly supported real function, at a complex argument. -/
@[zz_tag "def_fourier"]
noncomputable def fourierC (f : ℝ → ℝ) (ξ : ℂ) : ℂ :=
  ∫ u : ℝ, (f u : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ξ * (u : ℂ))

/-- `eta` is `lam`-admissible: square-integrable, real-valued, even, supported in
`(-lam, lam)`, and normalised so that its square has Fourier transform `1` at `0`. -/
@[zz_tag "def_admissible"]
structure IsAdmissible (lam : ℝ) (eta : ℝ → ℝ) : Prop where
  /-- `eta` is square-integrable. -/
  memLp : MeasureTheory.MemLp eta 2 MeasureTheory.volume
  /-- `eta` is even. -/
  even : ∀ x, eta (-x) = eta x
  /-- `eta` vanishes off `(-lam, lam)`. -/
  support : ∀ x, lam ≤ |x| → eta x = 0
  /-- `eta` is normalised: its square has Fourier transform `1` at `0`. -/
  fourier_sq_zero : fourierC (eta ^ 2) 0 = 1

/-- The kernel of a test function, `K_eta = fourier transform of eta squared`. -/
@[zz_tag "def_kernel"]
noncomputable def testKernel (eta : ℝ → ℝ) : ℂ → ℂ := fourierC (eta ^ 2)

/-- The support `Z` with multiplicities `m` is conjugation-invariant: every multiplicity is at
least one, and conjugation permutes `Z` preserving multiplicity. -/
@[zz_tag "def_conj_invariant"]
structure IsConjInvariant (Z : Finset ℂ) (m : ℂ → ℕ) : Prop where
  /-- Every point of the support has multiplicity at least one. -/
  one_le : ∀ z ∈ Z, 1 ≤ m z
  /-- Conjugation maps the support to itself. -/
  conj_mem : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z
  /-- Conjugation preserves multiplicity. -/
  mult_conj : ∀ z ∈ Z, m ((starRingEnd ℂ) z) = m z

/-- The simple real part of the support: real points of multiplicity one. -/
@[zz_tag "def_R1"]
noncomputable def simpleRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun x => x.im = 0 ∧ m x = 1

/-- The weight `4 / (4 - z²)` carried by the unconditional pair-correlation formula. -/
@[zz_tag "def_w"]
noncomputable def pairWeight (z : ℂ) : ℂ := 4 / (4 - z ^ 2)

/-- The rescaled difference `i(ρ - ρ') log T / (2π)` of two zeros. -/
@[zz_tag "def_z_rho"]
noncomputable def rescaledDiff (T : ℝ) (ρ ρ' : ℂ) : ℂ :=
  Complex.I * (ρ - ρ') * ((Real.log T / (2 * Real.pi) : ℝ) : ℂ)

/-- The weighted sum of `fourierC f` over ordered pairs of non-trivial zeros with imaginary part
in `(0, T]`, each zero counted with multiplicity. -/
@[zz_tag "def_B_T"]
noncomputable def pairCorrelationSum (f : ℝ → ℝ) (T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, ∑ᶠ ρ' ∈ nontrivialZeros T,
    ((zeroMultiplicity ρ * zeroMultiplicity ρ' : ℕ) : ℂ) *
      fourierC f (rescaledDiff T ρ ρ') * pairWeight (ρ - ρ')

/-- The main term `f 0 + 2 ∫₀¹ α f α` of the pair-correlation formula. -/
@[zz_tag "def_A_functional"]
noncomputable def pairMainTerm (f : ℝ → ℝ) : ℝ := f 0 + 2 * ∫ α in (0:ℝ)..1, α * f α

/-- A test function admissible in the pair-correlation formula: even, integrable, supported in
`[-1, 1]`, and Lipschitz at the origin.

The Lipschitz condition is imposed globally rather than only at `0`. That makes this predicate
*stronger*, hence `PairCorrelation` weaker and safer to assume — and the cited lemma still supplies
it. -/
def IsPairTestFunction (f : ℝ → ℝ) : Prop :=
  (∀ x, f (-x) = f x) ∧ MeasureTheory.Integrable f ∧ (∀ x, 1 < |x| → f x = 0) ∧
    ∃ C : ℝ, ∀ x, |f x - f 0| ≤ C * |x|

/-! ### The two external inputs

The classical analytic results cited rather than proved here: the Riemann--von Mangoldt formula
and the unconditional pair-correlation formula. Each is a `Prop`, carried as a hypothesis, so
every result depending on it names it in its own statement.
-/

/-- **Riemann--von Mangoldt** (`lem_rvm`, external input). `N T ∼ (T / 2π) log T`. -/
@[zz_tag "lem_rvm"]
def RiemannVonMangoldt : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    |(zeroCount T : ℝ) / (T / (2 * Real.pi) * Real.log T) - 1| < ε

/-- **Unconditional pair correlation** (`lem_bgst`, external input). For every admissible test
function the weighted pair-correlation sum is `(T / 2π) log T` times its main term, with an error
`O(1 / √log T)`. Lemma 5 of Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, *An unconditional
Montgomery theorem for pair correlation of zeros of the Riemann zeta-function*, Acta Arith. 214
(2024), 357--376. -/
@[zz_tag "lem_bgst"]
def PairCorrelation : Prop :=
  ∀ f : ℝ → ℝ, IsPairTestFunction f →
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ‖pairCorrelationSum f T / ((T / (2 * Real.pi) * Real.log T : ℝ) : ℂ) -
          ((pairMainTerm f : ℝ) : ℂ)‖ ≤ C / Real.sqrt (Real.log T)

end ZetaZeros
