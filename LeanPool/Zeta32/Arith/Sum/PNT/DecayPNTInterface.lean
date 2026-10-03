/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.NumberTheory.Chebyshev
import LeanPool.MooreBound.PrimeNumberTheoremAnd.Consequences

/-! the prime number theorem in Chebyshev form, stated with the fully
qualified Mathlib function. The proof reuses the PrimeNumberTheoremAnd
development preserved in LeanPool.MooreBound instead of duplicating its analytic closure. -/

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/DecayPNTInterface.lean
-- The copied PNT closure is replaced by the pooled MooreBound proof.

public section

theorem Zeta32.ArithSum.PNT.theta_isEquivalent_id : Asymptotics.IsEquivalent Filter.atTop
  Chebyshev.theta id :=
  MooreBound.chebyshev_asymptotic

end
