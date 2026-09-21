/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnCohomologyRingModel
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnTopClassAlphaPower
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.InducedOnRPCohomology

/-!
# Bridge from RP singular cohomology to the truncated polynomial model

Defines explicit interfaces for maps from the actual mod-two cohomology of `RP n` to the model
`F₂[α]/(αⁿ⁺¹)` and derives nonvanishing and truncation consequences for cup powers. This module is
an intermediate model-comparison API; the final unconditional odd-degree proof uses the direct
cohomology-dimension-vanishing route.
-/

noncomputable section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- The **model-side half of the `RPⁿ` mod-two cohomology ring isomorphism**: a
graded ring homomorphism from the actual singular cohomology of `RPⁿ` to the
algebraic model `F₂[α]/(αⁿ⁺¹)`, carrying a chosen degree-one class to the model
generator `modelAlpha n`.

This is the honest, explicit, single hypothesis to which the top-class
nonvanishing `αⁿ ≠ 0` in `Hⁿ(RPⁿ; F₂)` is reduced. Concretely it bundles:

* a `ZMod 2`-linear map `toFun k : Hᵏ(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` in every degree;
* multiplicativity across degrees for the cup product
 (`toFun (p+q) (a ⌣ b) = toFun p a · toFun q b`);
* unitality (`toFun 0 1 = 1`);
* a chosen degree-one class `alpha ∈ H¹(RPⁿ; F₂)` with `toFun 1 alpha = modelAlpha n`.

Such a homomorphism is exactly what the classical ring isomorphism supplies on the
model side. -/
structure RPnCohomologyToModelHom (n : ℕ) where
  /-- The graded map `Hᵏ(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` in each cohomological degree. -/
  toFun : (k : ℕ) →
    (cohomologyZMod2 (TopCat.of (RP n)) k →ₗ[ZMod 2] RPnCohomologyRingModel n)
  /-- The unit class `1 ∈ H⁰(RPⁿ; F₂)` is sent to `1` in the model ring. -/
  map_one' : toFun 0 (oneZMod2 (TopCat.of (RP n))) = 1
  /-- Multiplicativity across degrees for the cohomology cup product. -/
  map_cup' : ∀ {p q : ℕ} (a : cohomologyZMod2 (TopCat.of (RP n)) p)
      (b : cohomologyZMod2 (TopCat.of (RP n)) q),
      toFun (p + q) (cupZMod2 a b) = toFun p a * toFun q b
  /-- The chosen degree-one cohomology class `α ∈ H¹(RPⁿ; F₂)`. -/
  alpha : cohomologyZMod2 (TopCat.of (RP n)) 1
  /-- `α` is carried to the model generator `modelAlpha n`. -/
  alpha_spec : toFun 1 alpha = modelAlpha n

namespace RPnCohomologyToModelHom

variable {n : ℕ}

/-- The bridge sends the `k`-th cup power of the chosen class `α` to `modelAlpha n ^ k`.
This is the computation that transports the model nonvanishing facts to the actual
cohomology. -/
theorem map_cupPow (Φ : RPnCohomologyToModelHom n) (k : ℕ) :
    Φ.toFun k (cupPowZMod2 Φ.alpha k) = modelAlpha n ^ k := by
  induction k with
  | zero => simpa using Φ.map_one'
  | succ k ih =>
      rw [cupPowZMod2_succ, Φ.map_cup' (cupPowZMod2 Φ.alpha k) Φ.alpha, ih, Φ.alpha_spec,
        pow_succ]

end RPnCohomologyToModelHom

/-- **Conditional sub-truncation nonvanishing, in the actual cohomology.** Given the
bridge `Φ`, the `k`-th cup power of `α` is nonzero in the genuine `Hᵏ(RPⁿ; F₂)` for
every `k ≤ n`. -/
theorem rpAlpha_power_ne_zero {n : ℕ} (Φ : RPnCohomologyToModelHom n) {k : ℕ}
    (hk : k ≤ n) : cupPowZMod2 Φ.alpha k ≠ 0 := by
  intro h
  apply modelAlpha_pow_ne_zero n k hk
  rw [← Φ.map_cupPow k, h, map_zero]

/-- **Conditional top-class nonvanishing, in the actual cohomology** — the
load-bearing `αⁿ ≠ 0` in the genuine `Hⁿ(RPⁿ; F₂)`. -/
theorem rpAlpha_power_top_ne_zero {n : ℕ} (Φ : RPnCohomologyToModelHom n) :
    cupPowZMod2 Φ.alpha n ≠ 0 :=
  rpAlpha_power_ne_zero Φ le_rfl

/-- The **full model-side ring embedding** of the actual `RPⁿ` mod-two cohomology:
a graded ring homomorphism to the model (`RPnCohomologyToModelHom n`) that is, in
addition, **injective in every degree**. This is the genuine "ring-equivalence
hypothesis" the design asks to reduce to: an injective graded ring map to the model
carrying `α` to `modelAlpha n` is exactly the model-side data of the isomorphism
`H^*(RPⁿ; F₂) ≅ F₂[α]/(αⁿ⁺¹)`, and it pins down the relation `αⁿ⁺¹ = 0` as well as
the nonvanishing. -/
structure RPnCohomologyRingModelEmbedding (n : ℕ) extends RPnCohomologyToModelHom n where
  /-- Each graded component `Hᵏ(RPⁿ; F₂) → F₂[α]/(αⁿ⁺¹)` is injective. -/
  injective : ∀ k, Function.Injective (toFun k)

/-- **Conditional truncation relation, in the actual cohomology.** Given the
injective bridge, `αⁿ⁺¹ = 0` in the genuine `Hⁿ⁺¹(RPⁿ; F₂)`. -/
theorem rpAlpha_power_succ_eq_zero {n : ℕ} (e : RPnCohomologyRingModelEmbedding n) :
    cupPowZMod2 e.alpha (n + 1) = 0 := by
  apply e.injective (n + 1)
  rw [e.toRPnCohomologyToModelHom.map_cupPow (n + 1), map_zero, modelAlpha_pow_succ_eq_zero]

/-- **Conditional full power-vanishing characterization, in the actual cohomology.**
Given the injective bridge, the cup power `αᵏ` vanishes in `Hᵏ(RPⁿ; F₂)` exactly at
and beyond the truncation bound: `αᵏ = 0 ↔ n+1 ≤ k`. -/
theorem rpAlpha_power_eq_zero_iff {n : ℕ} (e : RPnCohomologyRingModelEmbedding n) (k : ℕ) :
    cupPowZMod2 e.alpha k = 0 ↔ n + 1 ≤ k := by
  constructor
  · intro h
    by_contra hc
    exact rpAlpha_power_ne_zero e.toRPnCohomologyToModelHom (by omega) h
  · intro h
    apply e.injective k
    rw [e.toRPnCohomologyToModelHom.map_cupPow k, map_zero,
      (modelAlpha_pow_eq_zero_iff n k).2 h]

/-- **Conditional final-theorem package, in the actual cohomology.** Given the
bridge `Φ` and a degree-one class `α = Φ.alpha` fixed by the pullback of a
descended odd self-map `fbar = inducedOnRP f hf`, the top cup power `αⁿ ∈ Hⁿ(RPⁿ; F₂)`
is simultaneously **fixed** by `fbar^*` and **nonzero**. This is exactly the
shape consumed by the final odd-degree comparison: `fbar^*(α) = α` forces
`fbar^*(αⁿ) = αⁿ`, while `αⁿ ≠ 0` makes that identity nontrivial. -/
theorem rpAlpha_power_top_fixed_ne_zero {n : ℕ} (Φ : RPnCohomologyToModelHom n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f)
    (ha : (inducedOnRPPullback f hf 1).hom Φ.alpha = Φ.alpha) :
    (inducedOnRPPullback f hf n).hom (cupPowZMod2 Φ.alpha n) = cupPowZMod2 Φ.alpha n
      ∧ cupPowZMod2 Φ.alpha n ≠ 0 :=
  ⟨inducedOnRP_cohPullback_cupPow_fixed f hf Φ.alpha ha n, rpAlpha_power_top_ne_zero Φ⟩

end SphereOddDegree
