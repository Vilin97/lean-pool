/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Order.Hom.Basic

/-!
# The finite-arity Erdős–Rado residual (bounded color cardinal, `ω₁` output)

The ER-facing statement that would discharge the Morley–Hanf pure-coloring hypothesis
(`pureColoringHypothesis_of_finiteArityErdosRadoOmega1` in `Conditional/MorleyHanfTransfer.lean`):
for every well-ordered source of size `≥ ℶ_{ω₁}` and every per-arity coloring family with color
types of size `≤ κ`, there is **one** `ω₁`-suborder homogeneous for all arities simultaneously.

**FALSE-SHAPED (statement audit 2026-07-07; external literature check, not formalized here).**
This statement is refutable in ZFC: instantiating `C n := Bool` and restricting the
`ω₁`-suborder to its first `ω` elements gives the partition relation `ℶ_ω₁ → (ω)^{<ω}_2`,
which fails in ZFC — the least `κ` with `κ → (ω)^{<ω}_2` is the Erdős cardinal `κ(ω)`,
inaccessible [Silver; Kanamori, *The Higher Infinite*, 2nd ed., §7, Props. 7.14(b)/7.15(b)],
hence `> ℶ_ω₁` (an inaccessible dominates every `ℶ_α`, `α` below it). The full argument is
recorded on `PureColoringHypothesis` (`Conditional/MorleyHanfTransfer.lean`). The TRUE,
proved supply is the **bounded** finite-arity theorem `finiteArityErdosRadoBounded`
(`Combinatorics/FiniteArityErdosRadoInduction.lean`): one `κ⁺`-suborder homogeneous for all
arities `≤ N`, for every finite `N` — exactly the per-stage approximations the classical
Morley/Hanf template route consumes. This definition is kept as a strength marker and
consumer interface; `morley_hanf_of_finiteArityErdosRado` remains a true implication.

Two design constraints, learned the hard way, dictate the shape:

* **Bounded color cardinal, not `Bool`.** Packing the countably many `Bool` colorings of a fixed
  arity into a single coloring produces a `ℕ → Bool` color — continuum many colors — so a
  `Bool`-only (or `ℵ₀`-color) pair theorem cannot serve the family through packing. The residual
  therefore takes an arbitrary color bound `κ`; the Morley–Hanf discharge uses `κ := ℶ_1`.
* **One output suborder for all arities.** Iterating a single-arity theorem over the countable
  family fails: after one pass the source has shrunk to an `ω₁`-suborder, which is far too small
  to feed the next pass (each pass consumes a `ℶ`-sized source). The homogenization across
  arities must happen inside the (per-arity, finitely iterated) construction, with the countable
  same-arity family packed into one large color.

What per-arity Erdős–Rado actually gives — `(ℶ_n(κ))^+ → (κ^+)^{n+1}_κ`-style homogenization,
with the source `ℶ_{ω₁}` dominating every finite stage — is the bounded theorem: the per-arity
outputs can NOT be intersected/diagonalized along a single `ω₁`-suborder (an ω-schedule of
passes needs an infinite descending sequence of ladder levels, and the audit above shows the
all-arity conclusion is outright refutable). The proved chain lives in
`PairErdosRadoGeneral.lean` (parameterized pair case: `#C ≤ κ`, `#I ≥ (2^κ)⁺` ⇒ a
`κ⁺`-suborder pair-homogeneous), `EndHomogeneousErdosRado.lean` (the end-homogenization
engine), and `FiniteArityErdosRadoInduction.lean` (the induction and the bounded theorem).
-/

universe u

/-! ## The first `ω` elements of `ω₁` -/

/-- The strictly monotone enumeration of the first `ω` elements of `(ω₁).ToType` — how an
`ω₁`-suborder feeds the `ℕ`-sequence consumers (`PureColoringHypothesis`). -/
noncomputable def omegaOneNatEmb : ℕ → (Ordinal.omega.{0} 1).ToType := fun n =>
  Ordinal.ToType.mk
    ⟨(n : Ordinal), (Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one⟩

theorem omegaOneNatEmb_strictMono : StrictMono omegaOneNatEmb := fun n m hnm =>
  Ordinal.ToType.mk.strictMono (Subtype.mk_lt_mk.mpr (by exact_mod_cast hnm))

/-! ## The residual -/

/-- **The finite-arity Erdős–Rado residual with color bound `κ`**: for every well-ordered source
`I` of size `≥ ℶ_{ω₁}` and every family of per-arity colorings `c n : (Fin n ↪o I) → C n` with
`#(C n) ≤ κ`, there is a single `ω₁`-suborder of `I` homogeneous for **all** arities
simultaneously.

This is the exact interface the Morley–Hanf chain consumes at `κ := ℶ_1`
(`pureColoringHypothesis_of_finiteArityErdosRadoOmega1`): the countably many `Bool` colorings of
each arity pack into one color type `{i // arity i = n} → Bool` of size `≤ 2^{ℵ₀} = ℶ_1`. The
color bound must be a parameter — a `Bool`-only statement cannot absorb the packing, and
iterating a one-coloring theorem over the family dies after one pass (the output `ω₁`-suborder
is too small to source the next).

**FALSE-SHAPED** for every `κ ≥ 2` — refutable in ZFC via the Erdős-cardinal argument; see the
module docstring above and `PureColoringHypothesis`. Kept as a strength marker and consumer
interface; the proved supply is the bounded `finiteArityErdosRadoBounded`. -/
def FiniteArityErdosRadoOmega1 (κ : Cardinal.{0}) : Prop :=
  ∀ (I : Type) [LinearOrder I] [WellFoundedLT I],
    Cardinal.mk I ≥ Cardinal.beth (Ordinal.omega 1) →
    ∀ (C : ℕ → Type) (_ : ∀ n, Cardinal.mk (C n) ≤ κ) (c : ∀ n, (Fin n ↪o I) → C n),
    ∃ e : (Ordinal.omega.{0} 1).ToType ↪o I,
      ∀ (n : ℕ) (t t' : Fin n ↪o I),
        (∀ k, t k ∈ Set.range e) → (∀ k, t' k ∈ Set.range e) →
        c n t = c n t'
