/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import LeanPool.Zeta3Irrational.Basic
import LeanPool.Zeta3Irrational.Bound
import LeanPool.Zeta3Irrational.Chebyshev
import LeanPool.Zeta3Irrational.Equality
import LeanPool.Zeta3Irrational.Integral
import LeanPool.Zeta3Irrational.LegendrePoly
import LeanPool.Zeta3Irrational.LinearForm
import LeanPool.Zeta3Irrational.D

/-!
# Irrationality of ζ(3)

Source: arxiv:2503.07625, doi:10.1112/blms/11.3.268
Authors: Junqi Liu, Jujian Zhang
Status: verified
Main declarations: `LeanPool.Zeta3Irrational.zeta3_irrational`
Tags: number-theory, analysis, zeta-functions
MSC: 11M06, 11J72
-/

/-!
This project formalizes the integral identities and denominator/positivity/
upper-bound estimates used in Beukers' proof of Apéry's theorem for `ζ(3)`.
It completes the final irrationality contradiction using an elementary Chebyshev
estimate for the least common multiple denominator.
-/
