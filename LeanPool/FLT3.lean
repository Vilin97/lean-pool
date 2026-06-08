/-
Copyright (c) 2026 Riccardo Brasca and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli
-/
import LeanPool.FLT3.Cyclo
import LeanPool.FLT3.FLT3

/-!
# Fermat's Last Theorem for exponent 3

Source: url:https://github.com/riccardobrasca/FLT3
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli
Status: verified
Main declarations: `FLT3.fermatLastTheoremThree`
Tags: number-theory, fermat-last-theorem, cyclotomic-field
MSC: 11D41
-/

/-!
## Mathematical overview

This project formalizes Fermat's Last Theorem for exponent `3`: for all `a`,
`b`, `c` in `ℕ` with `a ≠ 0`, `b ≠ 0`, `c ≠ 0`, one has `a ^ 3 + b ^ 3 ≠ c ^ 3`,
stated as `FLT3.fermatLastTheoremThree : FermatLastTheoremFor 3`.

The proof works in the cyclotomic ring `ℤ[ζ₃]` (the ring of integers of
`CyclotomicField 3 ℚ`), factoring `a ^ 3 + b ^ 3` over the cube roots of unity
and running a descent argument à la Kummer on the prime `λ = ζ - 1`. `Cyclo`
develops the basic arithmetic of `η` and `λ`, while `FLT3` carries out the
Eisenstein/Kummer descent and assembles the final statement. It was produced at
LFTCM 2024 (Luminy), following Hindry's *Arithmetics* (Theorem 2.6), and has
since been merged into Mathlib; here it is reproduced under the `FLT3` namespace.
The two key descent steps are exposed as
`FLT3.FermatLastTheoremForThreeGen.Solution.by_kummer` and
`FLT3.FermatLastTheoremForThreeGen.Solution.x_eq_unit_mul_cube`.
-/
