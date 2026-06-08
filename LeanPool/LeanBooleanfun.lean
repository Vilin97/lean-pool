/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import LeanPool.LeanBooleanfun.AuxLemmas
import LeanPool.LeanBooleanfun.ToMathlib
import LeanPool.LeanBooleanfun.Basic
import LeanPool.LeanBooleanfun.BooleanValued
import LeanPool.LeanBooleanfun.Arrow

/-!
# Analysis of Boolean functions in Lean

Source: arxiv:2105.10386, doi:10.1017/CBO9781139814782
Authors: Joris Roos
Status: verified
Main declarations: `LeanPool.LeanBooleanfun.BooleanFun.BV.dictator_of_condorcet_and_unanimous`
Tags: boolean-functions, fourier-analysis, social-choice
MSC: 06E30, 42C10, 91B14
-/

/-!
## Mathematical overview

Following Ryan O'Donnell's book [*Analysis of Boolean functions*](https://arxiv.org/abs/2105.10386),
this project formalizes basic definitions and results in the analysis of real-valued Boolean
functions on the Hamming cube `Fin n → Fin 2`.

The development sets up the Walsh-Fourier transform `fourierTransform` (notation `𝓕`) for
real-valued functions on the Boolean cube, equips the space `BooleanFunc n` with the structure
of an inner product space, and proves that the Walsh characters `walshCharacter` (notation `χ S`)
form an orthonormal basis. From this it derives:

* `walsh_fourier` — every Boolean function admits a Walsh-Fourier expansion.
* `inner_eq_sum_fourier` / `walsh_plancherel` — Plancherel/Parseval theorem for the
  Walsh-Fourier transform.
* `variance_le_totalInfluence` — L² Poincaré inequality bounding variance by total influence.
* `fourier_convolution` — convolution theorem for the Walsh-Fourier transform.

For Boolean-valued functions (i.e. taking values `±1`), the project introduces the typeclass
`BooleanValued` and proves:

* `BV.almost_character` — a Blum–Luby–Rubinfeld linearity testing theorem: a function whose BLR
  acceptance probability is at least `1 - ε` is `ε`-close in Hamming distance to a Walsh character.
* `BV.dictator_of_condorcet_and_unanimous` — a version of Arrow's theorem on 3-candidate
  elections: every unanimous voting rule that always admits a Condorcet winner is a dictatorship,
  proved via Gil Kalai's Fourier-analytic approach.

## Provenance

Imported from <https://github.com/roos-j/lean-booleanfun>; ported from Lean v4.16.0-rc2 to
Lean Pool's v4.30.0-rc2.
-/
