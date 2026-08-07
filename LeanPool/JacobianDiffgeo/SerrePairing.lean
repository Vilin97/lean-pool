/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.SerrePairing.TailSpace
import LeanPool.JacobianDiffgeo.SerrePairing.Pairing
import LeanPool.JacobianDiffgeo.SerrePairing.Duality

/-!
# serre-duality-cech: the Serre pairing at the Čech level (namespace `RS`/`RS.SerrePairing`)

API summary (see `docs/design/serre-duality-cech.md`). **Builds on:** canonical-forms (BUILT) and
residue-calculus (BUILT). Blueprint: "The Serre pairing at the Čech level: the dimension-counting
surjectivity core and the duality bookkeeping consumed by the tail route." Per the design's own
routing decision (§0.1), this unit owns the *pairing formula* and its *injectivity* half; the hard
*surjectivity* half of Serre duality (Miranda VI.3 Lemma 3.4/3.6 and the induction on growing
divisors) is squarely serre-duality-tails' (#26) job and is not attempted here.

## Exports

### `TailSpace.lean`

* `Tail X : Type _ := X →₀ (ℤ →₀ ℂ)` (a `noncomputable abbrev`, not a `def` — this avoids the
  `AddCommGroup`/`Module` instance-search breakage a plain `def` wrapping a nested `Finsupp` would
  cause; the reducible unfolding lets every `Finsupp` instance transport for free): Miranda VI.3's
  *ambient* Laurent-tail space, an arbitrary finite tail of Laurent coefficients at finitely many
  points of `X`, read in each point's own `chartAt`, with **no** exponent restriction at the
  ambient level (`Tail.BoundedBy`/`TailSpace` is the only place a bound enters — hard-coding
  "negative exponents only" would be wrong for divisors `D` with a negative value somewhere).
* `Tail.BoundedBy τ D`/`TailSpace D : Submodule ℂ (Tail X)`: Miranda's `T[D](X)`, tails whose
  exponent at each point `x` is `< -(D x)`.
* `Tail.single p n c`/`Tail.single_boundedBy`: the single-point, single-exponent test tail (the
  injectivity witness's raw material).

### `Pairing.lean` (`RS.MForm`/`RS.SerrePairing` namespaces)

* `pair (θ : MForm X) (τ : Tail X) : ℂ` (Miranda's `Res_θ`, purely algebraic — a finite sum of
  Laurent coefficients of `θ` against `τ`'s exponents, **no integration, no residue functional**,
  built directly from `MForm.laurentCoeffAt` on classes): `pairAt`/`pairTail` are the per-point and
  full assembly via `Finsupp.lsum` (packaging bilinearity for free, no manual `finsum` support-union
  bookkeeping); `pairL : MForm X →ₗ[ℂ] Tail X →ₗ[ℂ] ℂ` is the bundled bilinear form.
* Bilinearity: `pair_add_left`/`pair_smul_left`/`pair_zero_left` (in `θ`), `pair_add_right`/
  `pair_smul_right`/`pair_zero_right` (in `τ`).
* `pair_single (θ) (p) (n) (c) : pair θ (Tail.single p n c) = c * θ.laurentCoeffAt p (-1 - n)` — the
  atom the injectivity core computes with directly.
* `MForm.laurentCoeffAt_add`/`_smul`/`_zero` (Compat: `ℂ`-linearity of `laurentCoeffAt` in the
  class argument, proved via representatives + residue-calculus's linearity kit, since
  canonical-forms does not itself export this).

### `Duality.lean` (`RS.MForm`/`RS.SerrePairing` namespaces, `[T1Space X] [ConnectedSpace X]`)

* **`exists_tail_pair_ne_zero`** (D4, Miranda Thm 3.3's injectivity half / Forster 17.6): a nonzero
  `θ ∈ MForm.OmegaSpace (-D)` pairs nontrivially against *some* `D`-bounded tail — the single-term
  tail at `θ`'s own leading Laurent exponent at any point, "cheap and local" exactly as billed.
* **`finrank_omegaSpace_le`** (D5, the generic dimension-counting interface #26 discharges): given
  *any* finite-dimensional target `H`, a surjective linear map `toH : ↥(TailSpace D) →ₗ[ℂ] H`, and
  a well-definedness hypothesis `hwd` (`pair θ` vanishes on `ker toH` for every `θ ∈ Ω(-D)`), the
  pairing descends to an injective `↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ H`, hence
  `finrank Ω(-D) ≤ finrank H` — i.e. `i(-D) ≤ finrank H`. Pure linear algebra once the two
  hypotheses are supplied; proved here in full, zero dependence on laurent-tails/residue-theorem.
* `MForm.laurentCoeffAt_ord_ne_zero` (Compat): the leading Laurent coefficient of a class at a
  finite-order point is nonzero (lifted from residue-calculus's `laurentCoeffAt_order_ne_zero`).

## The frozen target for #26 (recorded as documentation — NOT a compiled declaration here)

The obligation this unit hands off to serre-duality-tails (its own design's §0, "frozen
reconciliation"), Serre Duality in full:
```
theorem RS.TailDuality.i_neg_eq_h1 [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (D : RS.Divisor X) : RS.MForm.i (-D) = RS.Finiteness.h1 D
```
The `≤` direction is `finrank_omegaSpace_le` instantiated at `H := RS.Cech.H1 D`; the `≥` direction
(Miranda Lemma 3.4/3.6, genuinely new labor) is entirely #26's own. Per serre-duality-tails' own
frozen reconciliation (§0.1 of its design), `finrank_omegaSpace_le` is **not** literally
instantiated there — #26 runs Miranda VI.3 on its own *germ* tail model (`RS.LaurentTail.T D`)
instead, reusing only this unit's *proof pattern* (`resAt_zpow_mul`/`laurentCoeffAt_order_ne_zero`,
spike-verified here) and citing `exists_tail_pair_ne_zero`'s shape directly; `Tail X`/`TailSpace D`/
`pair`/`finrank_omegaSpace_le` remain fully self-contained, adapter-friendly exports regardless.

## Deviations from `docs/design/serre-duality-cech.md` (recorded honestly)

1. **The quotient revision** (`Jacobian/CanonicalForms/Quotient.lean`, landed after this design was
   frozen): `MForm X` is now the QUOTIENT of a raw data carrier `MFormData X` by codiscrete/germ
   agreement, not a raw structure exposing `coeffAt` directly. `pair` is defined directly as the
   finite sum of `MForm.laurentCoeffAt` values (the design's own `pair_eq_finsum_sum` formula) via
   `Finsupp.lsum`, rather than via `resAt` of an explicit representative product + `resAt_tail_mul`
   — the same mathematical content (see `pair_single`'s proof, the one place a representative's
   `resAt_tail_mul` is genuinely exercised, inside `RS.laurentCoeffAt_order_ne_zero`'s proof chain
   via `MForm.laurentCoeffAt_ord_ne_zero`), with strictly less proof debt (bilinearity in `τ` is
   free from `Finsupp.lsum`, no manual `finsum`-over-two-supports bookkeeping).
2. **`MForm.OmegaSpace`'s membership dropped the design's disjunction**: it is now the single
   order-wise condition `∀ x, (-(D x) : WithTop ℤ) ≤ θ.ord x` (no `θ = 0 ∨ ...`), uniform since
   `θ = 0` has `ord = ⊤` everywhere. `exists_tail_pair_ne_zero`/`finrank_omegaSpace_le` use this
   directly.
3. **Hypothesis simplification**: `Duality.lean`'s theorems need only `[T1Space X] [ConnectedSpace
   X]`, not the design's listed `[T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]` —
   `MForm.OmegaSpace` and `Module.finrank` are topology-free, per `CONVENTIONS.md`'s "drop
   hypotheses lemmas don't need, when free to do so".
4. **`finrank_omegaSpace_le`'s proof avoids `Submodule.liftQ`/`LinearMap.quotKerEquivOfSurjective`**
   (the design's primary plan, §5 P2): building `↥(TailSpace D) ⧸ LinearMap.ker toH` was found to
   elaborate extremely slowly (deterministic timeout at `whnf`/`isDefEq` even at 1,000,000
   heartbeats). Root cause, isolated by direct experiment: `↥(TailSpace D)` (a `Submodule` over the
   doubly-nested `Finsupp` carrier `Tail X := X →₀ (ℤ →₀ ℂ)`) has no *findable* `AddCommGroup`/
   `Sub`/`Neg` instance at this pin — `AddSubgroupClass (Submodule ℂ (Tail X)) (Tail X)` itself
   fails to synthesize, even though `Tail X` unwrapped has a perfectly good `AddCommGroup`, and the
   SEMIRING-level `Submodule.add_mem`/`smul_mem` (not `neg_mem`/`sub_mem`) resolve fine. Used
   instead: the design's own documented **risk-3 fallback** (§7) — `Φ`/`resDual` are built directly
   from a chosen section `Function.surjInv` of `toH`, with a congruence lemma
   (`pair_congr_of_toH_eq`) replacing the quotient machinery, and every place a "difference" of
   `↥(TailSpace D)` elements was needed is built as `τ + (-1 : ℂ) • σ` (`+`/`•`, confirmed working)
   rather than `τ - σ` (`Sub`, confirmed broken). Zero mathematical content lost; this is exactly
   the fallback the design pre-registered for this contingency, not an ad-hoc patch. Filed as a
   coordination note for any future consumer building further `Submodule`s over `Tail X`/`TailSpace
   D`: avoid `Submodule.sub_mem`/`neg_mem`/`AddSubgroupClass`/`Sub`/`Neg` on `↥(TailSpace D)`
   directly; use `Submodule.add_mem`/`smul_mem` plus the `(-1 : ℂ) • ·` trick instead.

## Notes for serre-duality-tails (#26), the adapter surface as built

* `Tail X`/`TailSpace D`/`Tail.BoundedBy`/`Tail.single` (`TailSpace.lean`) and `pair`/`pairL`/
  bilinearity/`pair_single` (`Pairing.lean`) are fully self-contained and provable independent of
  laurent-tails, residue-theorem, or cech-cohomology (confirmed: this whole unit builds on
  canonical-forms + residue-calculus only, exactly as its `Builds on:` edge states).
* `exists_tail_pair_ne_zero`'s *proof shape* (`Tail.single p (-1 - k) 1` at the leading exponent
  `k := (θ.ord p).untop₀`, computed via `pair_single` + `MForm.laurentCoeffAt_ord_ne_zero`) is the
  exact pattern #26 reuses against its own `tailGerm`-based test vectors (its design's §0.1 point
  2, confirmed: `RS.Cech.tailGerm` is the literal monomial germ, so the same `resAt_zpow_mul` +
  `laurentCoeffAt_order_ne_zero` computation applies verbatim).
* `finrank_omegaSpace_le`'s statement shape (hypotheses `toH`/`hsurj`/`hwd`, conclusion
  `finrank Ω(-D) ≤ finrank H`) is available as a ready-made `≤`-half instantiable at
  `H := RS.Cech.H1 D` should a future revision want it; #26's own frozen design (§0.1) currently
  gets both inequalities for free from its own `resEquiv` bijectivity instead, so this export is
  offered but not required.
-/
