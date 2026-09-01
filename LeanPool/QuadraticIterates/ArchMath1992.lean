/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import LeanPool.QuadraticIterates.ArchMath1992.DegreeCriterion
import LeanPool.QuadraticIterates.ArchMath1992.Irreducibility
import LeanPool.QuadraticIterates.ArchMath1992.Iterates
import LeanPool.QuadraticIterates.ArchMath1992.Main
import LeanPool.QuadraticIterates.ArchMath1992.Sequences

/-!
# Galois groups over ℚ of some iterated polynomials

A formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244.

For an integer `a` such that `-a` is not a square, let `f_n` be the `n`-th iterate of
`f = X² + a`, let `K_n` be the splitting field of `f_n` over `ℚ` and `Ω_n` its Galois group,
which always embeds into the `n`-fold iterated wreath product `[C₂]ⁿ`.

## Main definitions

* `QuadraticIterates.iteratedPoly`: the iterates `f_n` of `X² + a`, over any commutative semiring.
* `QuadraticIterates.splittingField`: the splitting field `K_n` of `f_n`, taken inside
  `AlgebraicClosure ℚ`.
* `QuadraticIterates.GaloisGroup`: the Galois group `Ω_n = Gal(f_n/ℚ)`.
* `QuadraticIterates.WreathPower`: the `n`-fold iterated wreath product `[C₂]ⁿ`.
* `QuadraticIterates.EvenPoly`: being an even polynomial, i.e. lying in `R[X²]`.
* `QuadraticIterates.gammaSeq`: the iteration sequence `γ_n` of a polynomial with a sign choice.
* `QuadraticIterates.betaSeq`: its Möbius factors `β_n = ∏_{d ∣ n} γ_d^{μ(n/d)}`.
* `QuadraticIterates.cSeq` and `QuadraticIterates.bSeq`: the paper's `c_n` and `b_n`, namely the
  two above at `g = X² + a`, `ε = -1`.
* `QuadraticIterates.normPoly`: the rescaling `|a|·X² + sign a` of `X² + a`, whose `γ`-sequence
  is `|c_n| / |a|` and hence positive.
* `QuadraticIterates.moebiusFactor`: the rational Möbius product of an integer sequence.
* `QuadraticIterates.TwoIndependent`: `𝔽₂`-linear independence of classes in `ℚ*/(ℚ*)²`.
* `QuadraticIterates.rootShift`: the shifted root `β - a ∈ K_n` of `f_n`.

## Main statements

* `QuadraticIterates.section1_equiv` (Theorem, part 1): `Ω_n ≅ [C₂]ⁿ` iff `c_1, …, c_n` are
  2-independent iff `b_1, …, b_n` are 2-independent, where `c_1 = -a`, `c_{n+1} = c_n² + a =
  f_{n+1}(0)` and `b_n = ∏_{d ∣ n} c_d^{μ(n/d)}`;
* `QuadraticIterates.section1_squarefree` (Theorem, part 2): if none of `|b_2|, …, |b_n|` is a
  square, then `Ω_n ≅ [C₂]ⁿ`;
* `QuadraticIterates.section3_main` (Section 3): if `a > 0` with `a ≡ 1, 2 mod 4`, or `a < 0`,
  `a ≡ 0 mod 4` and `-a` is not a square, then `Ω_n ≅ [C₂]ⁿ` for all `n ≥ 1`;
* `QuadraticIterates.odoni_embedding` (Odoni): `Ω_n` embeds into `[C₂]ⁿ`;
* `QuadraticIterates.degree_criterion` (Lemma 1.6): `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}` is
  not a square in `K_n`;
* `QuadraticIterates.kummer_extension_criterion` (Lemma 1.5): a nonzero rational is a non-square
  in `K_n` iff it extends the 2-independent family `c_1, …, c_n`.

## Notation

`fℚ[a, n]` is local notation for the iterate `f_n` viewed in `ℚ[X]`, that is, for
`(iteratedPoly a n).map (Int.castRingHom ℚ)`.

## Implementation notes

`QuadraticIterates.degree_criterion` (Lemma 1.6) is proved from the hypothesis that `f_n` is
irreducible, which is weaker than the paper's maximality hypothesis
`[K_n : ℚ] = 2 ^ (2 ^ n - 1)`.

All declarations live in the `QuadraticIterates` namespace. The development is split over
`QuadraticIterates/ArchMath1992/`: `Sequences` (the `γ`- and `β`-sequences over general rings and
over `ℤ`), `Iterates` (the polynomials `f_n`, the fields `K_n`, the groups `Ω_n`, the sequences
`c` and `b`), `Irreducibility`, `DegreeCriterion` and `Main`.
-/
