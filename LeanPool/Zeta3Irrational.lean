/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/

import LeanPool.Zeta3Irrational.Basic
import LeanPool.Zeta3Irrational.Bound
import LeanPool.Zeta3Irrational.Equality
import LeanPool.Zeta3Irrational.Integral
import LeanPool.Zeta3Irrational.LegendrePoly
import LeanPool.Zeta3Irrational.LinearForm
import LeanPool.Zeta3Irrational.D

/-!
# Beukers integral estimates for ζ(3)

Source: doi:10.1112/blms/11.3.268
Authors: Junqi Liu, Jujian Zhang
Status: verified
Main declarations: `LeanPool.Zeta3Irrational.linear_int`, `LeanPool.Zeta3Irrational.JJ_upper`
Tags: number-theory, analysis, zeta-functions
MSC: 11M06, 11J72
-/

/-!
This project formalizes the integral identities and denominator/positivity/
upper-bound estimates used in Beukers' proof of Apéry's theorem for `ζ(3)`.
It does not include the final irrationality contradiction.
-/
