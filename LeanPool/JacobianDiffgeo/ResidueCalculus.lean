/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ResidueCalculus.TaylorCoeff
import LeanPool.JacobianDiffgeo.ResidueCalculus.LaurentCoeff
import LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue
import LeanPool.JacobianDiffgeo.ResidueCalculus.ChangeOfVariables
import LeanPool.JacobianDiffgeo.ResidueCalculus.IntegralBridge
import LeanPool.JacobianDiffgeo.ResidueCalculus.GermFunctionals
import LeanPool.JacobianDiffgeo.ResidueCalculus.MittagLeffler

/-!
# residue-calculus: Laurent coefficients, residues, and the circle-integral bridge (`RS`)

Purely planar (no manifolds, no `Jacobian/Forms` import). API summary
(see `docs/design/residue-calculus.md`):

* **Taylor/Laurent layer**: `RS.taylorCoeffAt g z₀ j` (dslope-iterate Taylor extractor) and
  `RS.laurentCoeffAt f z₀ k` (Laurent coefficient via the order presentation), with congruence
  (`_congr`), ℂ-linearity (`_add`/`_const_mul`/`_fun_sum`), monomials/shift
  (`_zpow_monomial`/`_zpow_mul`), and the analytic/order compatibility bridges
  (`laurentCoeffAt_of_analyticAt`, `laurentCoeffAt_order` vs `meromorphicTrailingCoeffAt`).
* **Principal parts**: `RS.principalPartAt f z₀`, the decomposition
  `MeromorphicAt.exists_principalPart_add_analyticAt` (`f =ᶠ[𝓝[≠]] principalPart + analytic`),
  and its uniqueness (`eq_principalPart_of_eventuallyEq`).
* **Residues**: `RS.resAt f z₀ := laurentCoeffAt f z₀ (-1)`, its algebra, the derivative lemmas
  `MeromorphicAt.resAt_deriv` (= 0) and `MeromorphicAt.resAt_deriv_div` (= order; the argument-
  principle atom), and the Serre-pairing atoms `resAt_tail_mul`/`resAt_analyticAt_mul`/`resAt_mul`
  (Miranda VI.3 shape `Σ c_n a_{−1−n}`).
* **Chart invariance**: `RS.resAt_comp_mul_deriv` — `resAt ((f∘φ)·φ') w₀ = resAt f z₀` for a
  local analytic isomorphism `φ` (`φ w₀ = z₀`, `deriv φ w₀ ≠ 0`); makes `Res_p(ω)` on a surface
  chart-independent. Residue of a raw *function* is NOT chart-invariant — always pair with `φ'`.
* **Integral bridge**: `RS.circleIntegral_eq_two_pi_I_mul_resAt` (`∮_{C(z₀,R)} f = 2πi·resAt f z₀`,
  fixed radius) and its small-radius (`∀ᶠ R in 𝓝[>] 0`) form.
* **Germ/ML packaging**: `RS.meromorphicGermsAt z₀` (ℂ-submodule of meromorphic germs at
  `𝓝[≠] z₀`), `RS.laurentCoeffL`/`RS.resL` as `→ₗ[ℂ]` functionals on it; `RS.PrincipalPartData U`
  (Mittag-Leffler data, Forster §17.1–17.2) with `Realizes`, `ofMeromorphicOn`, and the algebraic
  closure lemmas (`Realizes.add`/`.smul`/`.sub_orderAt_nonneg`, `realizes_zero_iff`).

Routing: this unit is the LOCAL, planar input. `∑ Res = 0` (Stokes) lives in residue-theorem /
planar-stokes-atoms; the residue functional `H¹(Ω) → ℂ` of Serre duality lives in
serre-duality-cech/tails. Neither is built here.
-/
