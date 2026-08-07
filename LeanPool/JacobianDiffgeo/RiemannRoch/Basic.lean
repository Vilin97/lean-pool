/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality

/-!
# riemann-roch: Riemann–Roch, `l(K) = g`, `deg K = 2g − 2`, the Riemann inequality

Unit: riemann-roch (#28), per `docs/design/serre-duality-tails.md` §9.1 + the `TailDuality` root
docstring's export bank / consumer notes. A thin assembly unit (per the blueprint's own framing):
every proof below is `omega`-level ℤ-arithmetic combining `TailDuality`'s tail-level ledger
(`chiT_eq_chiT_zero_add_degree`, the primary deliverable of the prerequisite pass) with its
Serre-duality export bank (`l_sub_eq_h1T`, `h1T_zero_eq_genus`, `h1T_zero_eq_l_K`) and
`RS.l_zero`. No new mathematics; no reference to `T D`/`pairT`/`chi`'s internals (the interface
`docs/design/serre-duality-tails.md` §9.1 demands).

* `chiT_zero : TailDuality.chiT 0 = 1 - g`.
* **`riemannRoch {ω₀} (h₀) (D) : l D - l(K − D) = deg D + 1 - g`** — the headline theorem.
* `l_K_eq_genus {ω₀} (h₀) : l K = g`.
* `deg_canonical {ω₀} (h₀) : deg K = 2 * g - 2`.
* **`riemann_inequality (D) : deg D + 1 - g ≤ l D`** — the forward-headline seed
  `genus-zero-headline` (#30) consumes.
-/

open scoped ContDiff Manifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-- `χT(0) = 1 - g`, from Liouville (`RS.l_zero`) and the tail-duality genus identification
(`h1T_zero_eq_genus`). -/
theorem chiT_zero : RS.TailDuality.chiT (0 : RS.Divisor X) = 1 - (genus X : ℤ) := by
  unfold RS.TailDuality.chiT
  rw [RS.l_zero, RS.TailDuality.h1T_zero_eq_genus]
  push_cast
  ring

omit [DecidableEq X] in
/-- **Riemann–Roch.** `l(D) − l(K − D) = deg D + 1 − g` for any canonical divisor `K` (seeded by a
nonzero reference form `ω₀`). Proof: the tail ledger `chiT D = chiT 0 + deg D` combined with
Serre duality `l(K − D) = h1T D` and `chiT 0 = 1 - g`; pure ℤ-arithmetic. -/
theorem riemannRoch {ω₀ : RS.MForm X} (h₀ : ω₀ ≠ 0) (D : RS.Divisor X) :
    (RS.l D : ℤ) - (RS.l (RS.canonicalDivisorOf ω₀ - D) : ℤ) =
      D.degree + 1 - (genus X : ℤ) := by
  classical
  have h1 : RS.l (RS.canonicalDivisorOf ω₀ - D) = RS.TailDuality.h1T D :=
    RS.TailDuality.l_sub_eq_h1T h₀ D
  have h2 := RS.TailDuality.chiT_eq_chiT_zero_add_degree D
  have h3 := chiT_zero (X := X)
  rw [h1]
  unfold RS.TailDuality.chiT at h2 h3
  omega

open scoped Classical in
omit [DecidableEq X] in
/-- `l(K) = g` (Riemann–Roch's own dictionary at `D = K`, packaged directly from the tail-duality
export bank). -/
theorem l_K_eq_genus {ω₀ : RS.MForm X} (h₀ : ω₀ ≠ 0) :
    RS.l (RS.canonicalDivisorOf ω₀) = genus X :=
  (RS.TailDuality.h1T_zero_eq_l_K h₀).symm.trans RS.TailDuality.h1T_zero_eq_genus

omit [DecidableEq X] in
/-- `deg K = 2g − 2` (Riemann–Roch applied at `D := K`, then `l K = g`/`l 0 = 1`). -/
theorem deg_canonical {ω₀ : RS.MForm X} (h₀ : ω₀ ≠ 0) :
    (RS.canonicalDivisorOf ω₀).degree = 2 * (genus X : ℤ) - 2 := by
  classical
  have hRR := riemannRoch h₀ (RS.canonicalDivisorOf ω₀)
  rw [sub_self, RS.l_zero, l_K_eq_genus h₀] at hRR
  omega

omit [DecidableEq X] in
/-- **The Riemann inequality**: `deg D + 1 − g ≤ l D`, unconditionally (no reference form needed
— `chiT`'s ledger plus `h1T ≥ 0`). The forward-headline seed `genus-zero-headline` (#30) uses at
`D := single P 1` in genus `0`. -/
theorem riemann_inequality (D : RS.Divisor X) :
    (D.degree + 1 - (genus X : ℤ)) ≤ (RS.l D : ℤ) := by
  classical
  have h2 := RS.TailDuality.chiT_eq_chiT_zero_add_degree D
  have h3 := chiT_zero (X := X)
  have hnn : (0 : ℤ) ≤ (RS.TailDuality.h1T D : ℤ) := Int.natCast_nonneg _
  unfold RS.TailDuality.chiT at h2 h3
  omega

end RS
