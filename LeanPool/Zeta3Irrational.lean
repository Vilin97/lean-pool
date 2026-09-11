/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/
module

public import LeanPool.Zeta3Irrational.Basic
public import LeanPool.Zeta3Irrational.Bound
public import LeanPool.Zeta3Irrational.Chebyshev
public import LeanPool.Zeta3Irrational.Equality
public import LeanPool.Zeta3Irrational.Integral
public import LeanPool.Zeta3Irrational.LegendrePoly
public import LeanPool.Zeta3Irrational.LinearForm
public import LeanPool.Zeta3Irrational.D
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Irrationality of ζ(3)

Source: arxiv:2503.07625, doi:10.1112/blms/11.3.268
Authors: Junqi Liu, Jujian Zhang
Status: verified
Main declarations: `LeanPool.Zeta3Irrational.zeta3_irrational`
Tags: number-theory, analysis, zeta-functions
MSC: 11M06, 11J72
-/

@[expose] public section

/-!
This project formalizes the integral identities and denominator/positivity/
upper-bound estimates used in Beukers' proof of Apéry's theorem for `ζ(3)`.
It completes the final irrationality contradiction using an elementary Chebyshev
estimate for the least common multiple denominator.
-/
