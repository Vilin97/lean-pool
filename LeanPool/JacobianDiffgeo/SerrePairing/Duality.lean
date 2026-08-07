/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.SerrePairing.Pairing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The injectivity core and the generic dimension inequality (serre-duality-cech, §2 D4–D5)

Unit: serre-duality-cech (`docs/design/serre-duality-cech.md` §2 D4–D5, §4.3).

* `exists_tail_pair_ne_zero` (D4, Miranda Thm 3.3's injectivity half / Forster 17.6): a nonzero
  `Θ ∈ Ω(-D)` pairs nontrivially against the single-term tail witnessing its own leading Laurent
  coefficient at any point where its order is finite.
* `finrank_omegaSpace_le` (D5, the generic dimension-counting interface #26 discharges): given
  any finite-dimensional target `H` and a surjective linear map `toH` from `D`-bounded tails
  whose kernel is annihilated by every `pair Θ` (`Θ ∈ Ω(-D)`), the pairing descends to an
  injective functional-valued map, giving `i(-D) ≤ finrank H`. Pure linear algebra once the two
  hypotheses are supplied.

**Adaptation to the quotient revision.** `MForm.OmegaSpace`/`mem_omegaSpace_iff` (Jacobian/
CanonicalForms/LinearSystems.lean) dropped the design's `Θ = 0 ∨ -D ≤ Θ.divisor` disjunction in
favor of a single order-wise condition `∀ x, (-(D x) : WithTop ℤ) ≤ Θ.ord x` (uniform since
`Θ = 0` has `ord = ⊤` everywhere, `≥` anything for free) — the proof below uses this directly.

**Hypothesis deviation (a simplification, not a correction).** The design's §4.3 listed
`[T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]` for this file; `MForm.OmegaSpace`
is now instance-free and `Module.finrank` needs no topology, so both theorems here need only
`[T1Space X] [ConnectedSpace X]` (for `MForm.ord_ne_top`/`Nonempty X`) — dropped per
`CONVENTIONS.md`'s "drop hypotheses lemmas don't need, when free to do so".
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS
namespace MForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Compat: the leading Laurent coefficient of a meromorphic 1-form at a finite-order point is
nonzero (lifted from residue-calculus's `laurentCoeffAt_order_ne_zero` through a representative;
the residue-calculus atom the whole injectivity core rests on). -/
theorem laurentCoeffAt_ord_ne_zero {Θ : MForm X} {x : X} (h : Θ.ord x ≠ ⊤) :
    Θ.laurentCoeffAt x (Θ.ord x).untop₀ ≠ 0 := by
  obtain ⟨θ, rfl⟩ := MForm.exists_rep Θ
  exact RS.laurentCoeffAt_order_ne_zero (θ.meromorphicAt_coeffAt x) h

end MForm

namespace SerrePairing

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable [T1Space X] [ConnectedSpace X]

/-- **D4** (Miranda Thm 3.3's injectivity half / Forster 17.6): a nonzero `Θ ∈ Ω(-D)` pairs
nontrivially against some `D`-bounded tail — the single-term tail at the leading exponent of
`Θ` at any point, cheap and local. -/
theorem exists_tail_pair_ne_zero {D : RS.Divisor X} {Θ : MForm X}
    (hΘ : Θ ∈ MForm.OmegaSpace (-D)) (hΘ0 : Θ ≠ 0) :
    ∃ τ : Tail X, τ.BoundedBy D ∧ pair Θ τ ≠ 0 := by
  obtain ⟨p⟩ : Nonempty X := inferInstance
  have hp : Θ.ord p ≠ ⊤ := MForm.ord_ne_top hΘ0 p
  set k : ℤ := (Θ.ord p).untop₀ with hk_def
  have hk_eq : ((k : ℤ) : WithTop ℤ) = Θ.ord p := WithTop.coe_untop₀_of_ne_top hp
  have h1 : ((-((-D) p) : ℤ) : WithTop ℤ) ≤ Θ.ord p := hΘ p
  rw [Divisor.neg_apply, neg_neg, ← hk_eq] at h1
  have hDp : D p ≤ k := by exact_mod_cast h1
  refine ⟨Tail.single p (-1 - k) 1, Tail.single_boundedBy (fun _ => by omega), ?_⟩
  rw [pair_single, show (-1 - (-1 - k)) = k from by ring, one_mul]
  exact MForm.laurentCoeffAt_ord_ne_zero hp

/-! ### D5: the generic dimension inequality -/

section FinrankLe

variable {D : RS.Divisor X} {H : Type*} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H]

-- Note: `hwd`/`hsurj`/`toH` are threaded as EXPLICIT arguments throughout this section (rather
-- than section `variable`s) because Lean only auto-includes a section variable in a declaration
-- when it appears in that declaration's stated TYPE, not merely in its tactic proof — `hwd` is
-- only ever used inside proof bodies below, so it must be explicit.

omit [T1Space X] [ConnectedSpace X] [FiniteDimensional ℂ H] in
/-- `pair Θ` is invariant on the fibres of `toH` (a repackaging of `hwd`: since `pair Θ` vanishes
on `ker toH`, it agrees on any two tails with the same `toH`-image). The engine behind `resDual`
below — the design's risk-3 fallback (`docs/design/serre-duality-cech.md` §7): instead of
`Submodule.liftQ`/`LinearMap.quotKerEquivOfSurjective` (which stacks a further quotient on top of
the already-reducible `abbrev Tail X`, and was found to elaborate very slowly / time out), we work
directly with a section `Function.surjInv` of `toH` and this congruence lemma.

**A genuine mathlib-instance gap found and worked around**: `↥(TailSpace D)` has no *findable*
`AddCommGroup`/`Sub`/`Neg` instance at this pin — confirmed by direct experiment that
`AddSubgroupClass (Submodule ℂ (Tail X)) (Tail X)` fails to synthesize (`Tail X`'s doubly-nested
`Finsupp` carrier `X →₀ (ℤ →₀ ℂ)` defeats it), even though `Tail X` itself (unwrapped) has a
perfectly good `AddCommGroup`/`Sub`, and the SEMIRING-level `Submodule.add_mem`/`smul_mem` (not
`neg_mem`/`sub_mem`, which need `Ring`/`AddCommGroup`) resolve fine. So the proof below builds
"`τ - σ`" as `τ + (-1 : ℂ) • σ` (`+`/`•` on `↥(TailSpace D)`, both confirmed working), never
invoking `Sub`/`Neg` on the submodule-subtype itself. -/
theorem pair_congr_of_toH_eq (toH : ↥(TailSpace D) →ₗ[ℂ] H)
    (hwd : ∀ Θ ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair Θ (τ : Tail X) = 0)
    {Θ : MForm X} (hΘ : Θ ∈ MForm.OmegaSpace (-D)) {τ σ : ↥(TailSpace D)} (h : toH τ = toH σ) :
    pair Θ (τ : Tail X) = pair Θ (σ : Tail X) := by
  set negσ : ↥(TailSpace D) := (-1 : ℂ) • σ with hnegσ_def
  set δ : ↥(TailSpace D) := τ + negσ with hδ_def
  have hnegσcoe : (negσ : Tail X) = -(σ : Tail X) := by
    rw [hnegσ_def, Submodule.coe_smul]
    exact neg_one_smul ℂ (σ : Tail X)
  have hδcoe : (δ : Tail X) = (τ : Tail X) - (σ : Tail X) := by
    rw [hδ_def, Submodule.coe_add, hnegσcoe]
    abel
  have hδker : toH δ = 0 := by
    have e1 : toH δ = toH τ + toH negσ := map_add toH τ negσ
    have e2 : toH negσ = (-1 : ℂ) • toH σ := map_smul toH (-1 : ℂ) σ
    rw [e2, neg_one_smul] at e1
    rw [e1, h]
    abel
  have hz := hwd Θ hΘ δ hδker
  rw [hδcoe] at hz
  have hlin : pair Θ ((τ : Tail X) - (σ : Tail X)) = pair Θ (τ : Tail X) - pair Θ (σ : Tail X) :=
    map_sub (pairL Θ) (τ : Tail X) (σ : Tail X)
  rw [hlin] at hz
  exact sub_eq_zero.mp hz

/-- The functional on `H` induced by a class `Θ ∈ Ω(-D)`, via a chosen section `Function.surjInv`
of `toH` (internal plumbing for `finrank_omegaSpace_le`). -/
def resDual (toH : ↥(TailSpace D) →ₗ[ℂ] H)
    (hwd : ∀ Θ ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair Θ (τ : Tail X) = 0)
    (hsurj : Function.Surjective toH) (Θ : ↥(MForm.OmegaSpace (-D))) : Module.Dual ℂ H where
  toFun h := pair Θ.1 ((Function.surjInv hsurj h : ↥(TailSpace D)) : Tail X)
  map_add' h1 h2 := by
    have hc : toH (Function.surjInv hsurj (h1 + h2))
        = toH (Function.surjInv hsurj h1 + Function.surjInv hsurj h2) := by
      rw [Function.surjInv_eq hsurj, map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]
    have hcong := pair_congr_of_toH_eq toH hwd Θ.2 hc
    change pair Θ.1 ((Function.surjInv hsurj (h1 + h2) : ↥(TailSpace D)) : Tail X)
        = pair Θ.1 ((Function.surjInv hsurj h1 : ↥(TailSpace D)) : Tail X)
          + pair Θ.1 ((Function.surjInv hsurj h2 : ↥(TailSpace D)) : Tail X)
    rw [hcong, Submodule.coe_add]
    exact pair_add_right Θ.1 _ _
  map_smul' c h := by
    have hc : toH (Function.surjInv hsurj (c • h)) = toH (c • Function.surjInv hsurj h) := by
      rw [Function.surjInv_eq hsurj, map_smul, Function.surjInv_eq hsurj]
    have hcong := pair_congr_of_toH_eq toH hwd Θ.2 hc
    change pair Θ.1 ((Function.surjInv hsurj (c • h) : ↥(TailSpace D)) : Tail X)
        = (RingHom.id ℂ) c • pair Θ.1 ((Function.surjInv hsurj h : ↥(TailSpace D)) : Tail X)
    rw [hcong, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    exact pair_smul_right Θ.1 c _

omit [T1Space X] [ConnectedSpace X] [FiniteDimensional ℂ H] in
theorem resDual_apply_toH (toH : ↥(TailSpace D) →ₗ[ℂ] H)
    (hwd : ∀ Θ ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair Θ (τ : Tail X) = 0)
    (hsurj : Function.Surjective toH) (Θ : ↥(MForm.OmegaSpace (-D))) (τ : ↥(TailSpace D)) :
    resDual toH hwd hsurj Θ (toH τ) = pair Θ.1 (τ : Tail X) :=
  pair_congr_of_toH_eq toH hwd Θ.2 (Function.surjInv_eq hsurj (toH τ))

/-- **D5** (the interface #26 discharges, generic in the target `H`): given a finite-dimensional
`H` and a surjective linear map `toH` from `D`-bounded tails such that `pair Θ` vanishes on
`ker toH` for every `Θ ∈ Ω(-D)`, the pairing descends to an injective map into `Dual H`, hence
`i(-D) ≤ finrank H`. Pure linear algebra once the two hypotheses are supplied — proved here in
full, no dependency on laurent-tails or residue-theorem's own content. -/
theorem finrank_omegaSpace_le (toH : ↥(TailSpace D) →ₗ[ℂ] H) (hsurj : Function.Surjective toH)
    (hwd : ∀ Θ ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair Θ (τ : Tail X) = 0) :
    Module.finrank ℂ (MForm.OmegaSpace (-D)) ≤ Module.finrank ℂ H := by
  let Φ : ↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ H :=
    { toFun := resDual toH hwd hsurj
      map_add' := fun Θ1 Θ2 => by
        apply LinearMap.ext
        intro h
        obtain ⟨τ, rfl⟩ := hsurj h
        rw [LinearMap.add_apply, resDual_apply_toH, resDual_apply_toH, resDual_apply_toH,
          Submodule.coe_add]
        exact pair_add_left Θ1.1 Θ2.1 (τ : Tail X)
      map_smul' := fun c Θ => by
        apply LinearMap.ext
        intro h
        obtain ⟨τ, rfl⟩ := hsurj h
        rw [RingHom.id_apply, LinearMap.smul_apply, resDual_apply_toH, resDual_apply_toH,
          Submodule.coe_smul, pair_smul_left, smul_eq_mul] }
  have hinj : Function.Injective Φ := by
    intro Θ1 Θ2 heq
    apply Subtype.ext
    by_contra hne
    have hsub0 : Θ1.1 - Θ2.1 ≠ 0 := sub_ne_zero.2 hne
    have hmem : Θ1.1 - Θ2.1 ∈ MForm.OmegaSpace (-D) := Submodule.sub_mem _ Θ1.2 Θ2.2
    obtain ⟨τ0, hτ0bd, hτ0ne⟩ := exists_tail_pair_ne_zero hmem hsub0
    have hτ0mem : τ0 ∈ TailSpace D := hτ0bd
    apply hτ0ne
    have hΦ : resDual toH hwd hsurj Θ1 (toH ⟨τ0, hτ0mem⟩)
        = resDual toH hwd hsurj Θ2 (toH ⟨τ0, hτ0mem⟩) :=
      LinearMap.ext_iff.1 heq (toH ⟨τ0, hτ0mem⟩)
    rw [resDual_apply_toH, resDual_apply_toH] at hΦ
    have hlin : pair (Θ1.1 - Θ2.1) τ0 = pair Θ1.1 τ0 - pair Θ2.1 τ0 := by
      change pairL (Θ1.1 - Θ2.1) τ0 = pairL Θ1.1 τ0 - pairL Θ2.1 τ0
      rw [map_sub, LinearMap.sub_apply]
    rw [hlin, hΦ, sub_self]
  rw [show Module.finrank ℂ (MForm.OmegaSpace (-D)) = Module.finrank ℂ ↥(MForm.OmegaSpace (-D))
    from rfl, ← Subspace.dual_finrank_eq (K := ℂ) (V := H)]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end FinrankLe

end SerrePairing
end RS
