/-
Copyright (c) 2026 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/

import LeanPool.SpecialNumbers.Eulerian
import LeanPool.SpecialNumbers.Euclidian
import LeanPool.SpecialNumbers.Sylvester

/-!
# Special Numbers

Source: url:https://github.com/provables/special-numbers
Authors: Walter Moreira, Joe Stubbs
Status: verified
Main declarations: `SpecialNumbers.sylvester`, `SpecialNumbers.eulerian`, `SpecialNumbers.worpitzky`
Tags: number-theory, combinatorics, integer-sequences
MSC: 11B73, 11B83
-/

/-!
## Mathematical overview

This project formalizes material from Chapter 6 ("Special Numbers") of Knuth,
Graham, and Patashnik's *Concrete Mathematics*, together with closely related
integer sequences. All declarations live in the `SpecialNumbers` namespace.

`Eulerian` defines the Eulerian numbers `SpecialNumbers.eulerian n k` by their
standard triangular recurrence and proves their boundary values. The
combinatorial interpretation (counting permutations of `{1, …, n}` by number of
ascents) is not formalized.

`Euclidian` studies the Euclid numbers `SpecialNumbers.Euclid.euclid`
(`SpecialNumbers.Euclid.euclid_coprime`, `SpecialNumbers.Euclid.euclid_strictMono`)
and derives the explicit floor formula `SpecialNumbers.Euclid.euclid_eq_floor_constant_pow`
in terms of a doubly-exponential constant.

`Sylvester` develops Sylvester's sequence `SpecialNumbers.sylvester` with its
product recurrence, strict monotonicity, pairwise coprimality
(`SpecialNumbers.sylvester_coprime`), and the explicit closed form
`SpecialNumbers.sylvester_eq_floor_constant_pow`.
-/
