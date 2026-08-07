/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Meromorphic.Predicates
import LeanPool.JacobianDiffgeo.Meromorphic.CodiscreteBridge
import LeanPool.JacobianDiffgeo.Meromorphic.GermSpace
import LeanPool.JacobianDiffgeo.Meromorphic.OrderEval
import LeanPool.JacobianDiffgeo.Meromorphic.Field
import LeanPool.JacobianDiffgeo.Meromorphic.Divisor
import LeanPool.JacobianDiffgeo.Meromorphic.LinearSystem
import LeanPool.JacobianDiffgeo.Meromorphic.Gluing
import LeanPool.JacobianDiffgeo.Meromorphic.LinSysMulEquiv

/-!
# meromorphic-and-divisors (CC2/CC3): junk-free `ℳ(X)`, divisors, `L(D)` (namespace `RS`)

API summary (see `docs/design/meromorphic-and-divisors.md`):

* **Chart layer** (`Predicates.lean`): `MeromorphicAtX f x` / `MeromorphicOnX f U`, `ordAtX f x`
  (chart-composite order); chart invariance, arithmetic, classification; CC4 compatibility
  `ordAtX_of_contMDiffAt_eq_zero`.
* **Codiscrete bridge** (`CodiscreteBridge.lean`, D2): for **open** `U`, `codiscreteWithin U`
  membership / `=ᶠ` / eventual properties are purely pointwise `𝓝[≠] x` statements
  (`eventuallyEq_codiscreteWithin_iff_of_isOpen` and friends) — meromorphy-free. The meromorphic
  identity dichotomy on a connected surface: `f =ᶠ[codiscrete X] 0` or `∀ x, ordAtX f x ≠ ⊤`.
* **Germ space** (`GermSpace.lean`, D1/D6): `MeroGermOn X U` (a subalgebra of
  `Filter.Germ (codiscreteWithin U) ℂ`; junk-free by construction), `ℳ X := MeroGermOn X univ`.
  `MeroGermOn.mk`/`mk_eq_mk`/`exists_rep`/`ind`, ring/algebra ops via `mk`; `MeroGermOn.restrict`
  as an `AlgHom` (Čech structure maps), with presheaf laws `restrict_restrict`/`restrict_id`.
* **Order and canonical value** (`OrderEval.lean`, D3/D5): `MeroGermOn.ord`/`evalAt` descend from
  `ordAtX` (meromorphy-free congr); `MeroGermOn.holoRepr` is the canonical repaired
  representative — `holoRepr_contMDiffAt` (honestly holomorphic wherever `0 ≤ ord`) and
  `mk_holoRepr` (recovers the class) are the rigidified normal form Čech needs.
* **`Field (ℳ X)`** (`Field.lean`, `[T2Space X] [ConnectedSpace X]`): pointwise `Inv`
  (unconditional), `Mero.ord_eq_top_iff` (dichotomy corollary), field axioms via
  `Mero.mul_inv_cancel`.
* **Divisors** (`Divisor.lean`, CC2/D7): `Divisor X`, `Function.locallyFinsuppWithin.degree`
  (Compat), `MeroGermOn.divisorOn`/`divisor : ℳ X → Divisor X` (total; `divisor 0 = 0` honestly),
  algebra (`divisor_mul/inv/smul`), `divisor_nonneg_iff`, compactness finiteness.
* **`L(D)`** (`LinearSystem.lean`, CC3/D4): `LinSys D`/`l D`, `mem_linSys_iff_eq_zero_or_le_divisor`
  (CC3's frozen shape recovered as a theorem), `linSys_zero_eq_span_one`/`l_zero` (Liouville),
  vanishing lemmas, the conditional `linSys_eq_bot_of_degree_neg`, `LinSysOn`/
  `mem_linSys_iff_forall_restrict` (Čech `H⁰(𝔘, O_D) = L(D)` bookkeeping).
* **Sheaf gluing** (`Gluing.lean`, §6.6): `MeroGermOn.exists_glue`/`glue_unique` — compatible germ
  classes on an open cover glue uniquely, via `holoRepr`'s pointwise rigidity (no coherence lemma
  needed). The Čech `H⁰` engine.
* **Linear equivalence** (`LinSysMulEquiv.lean`, §6.7): `linSysMulEquiv` — multiplication by a
  nonzero class is a `ℂ`-linear equivalence `L(D) ≃ₗ L(D - divisor φ)` (riemann-roch's lattice
  tool).

Every export listed in the design doc §4.1–§4.7 and the six hard proof plans (§6.1–§6.7,
including gluing) is proved; zero sorries.
-/
