/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# Transport of Stafford certificates

The right-ideal certificate is `1 = e * R + F * e * S`.
This module supplies the generic conditional reduction from monicization and
an exponent hypothesis, together with transport through algebra automorphisms
and nonzero scalars. These conditional interfaces are retained for current
imports; the unconditional theorem is proved in `Stafford38.FoundationClosure`.
-/

namespace Stafford
namespace Reduction

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The commutator `ad Y u = Y * u - u * Y`. -/
def ad (Y u : A) : A := Y * u - u * Y

/-- Stafford 3.8 for a single element, in written operator order. -/
def Stafford38 (e : A) : Prop := ∃ F R S : A, (1 : A) = e * R + F * e * S

/-- The monic right-coefficient presentation `X ^ N + ∑_{i<N} X ^ i * β i`. -/
def monicElt (X : A) (N : ℕ) (β : Fin N → A) : A :=
  X ^ N + ∑ i : Fin N, X ^ (i : ℕ) * β i

/-- `e` is *Weyl-monic* if some Weyl pair presents it monically with all
coefficients commuting with the partner. -/
def WeylMonic (e : A) : Prop :=
  ∃ (X Y : A) (N : ℕ) (β : Fin N → A),
    ad Y X = 1 ∧ (∀ i, Commute Y (β i)) ∧ e = monicElt X N β

/-! ## Transport lemmas -/

/-- Stafford 3.8 transports along any ring automorphism. -/
theorem stafford38_of_ringEquiv (φ : A ≃+* A) {e : A} (h : Stafford38 (φ e)) :
    Stafford38 e := by
  obtain ⟨F, R, S, hFRS⟩ := h
  refine ⟨φ.symm F, φ.symm R, φ.symm S, ?_⟩
  have := congrArg φ.symm hFRS
  simpa using this

/-- Stafford 3.8 transports along scalar multiples (no nonvanishing needed: the
scalar is absorbed into the cofactors `R` and `S`). -/
theorem stafford38_smul (c : k) {e : A} (h : Stafford38 (c • e)) :
    Stafford38 e := by
  obtain ⟨F, R, S, hFRS⟩ := h
  refine ⟨F, c • R, c • S, ?_⟩
  have key : ∀ a b : A, (c • a) * b = a * (c • b) := by
    intro a b
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← Algebra.commutes c a]
  rw [hFRS, key e R]
  congr 1
  calc F * (c • e) * S = F * ((c • e) * S) := by rw [mul_assoc]
    _ = F * (e * (c • S)) := by rw [key e S]
    _ = F * e * (c • S) := by rw [mul_assoc]

/-- A cofactor of the special form `Y ^ s` already witnesses Stafford 3.8. -/
theorem stafford38_of_power {e Y : A} {s : ℕ} {R S : A}
    (h : (1 : A) = e * R + Y ^ s * e * S) : Stafford38 e :=
  ⟨Y ^ s, R, S, h⟩

/-! ## The two hypotheses -/

/-- **Hypothesis M (monicization).**  Every nonzero element is, after an algebra
automorphism and a nonzero scalar, Weyl-monic. -/
def Monicization (k A : Type*) [Field k] [Ring A] [Algebra k A] : Prop :=
  ∀ e : A, e ≠ 0 → ∃ (φ : A ≃ₐ[k] A) (c : k), c ≠ 0 ∧ WeylMonic (c • φ e)

/-- **Hypothesis E (exponent).**  For every Weyl-monic presentation some power of
the Weyl partner is a Stafford cofactor. -/
def ExponentHypothesis (A : Type*) [Ring A] : Prop :=
  ∀ (X Y : A) (N : ℕ) (β : Fin N → A), ad Y X = 1 → (∀ i, Commute Y (β i)) →
    ∃ (s : ℕ) (R S : A),
      (1 : A) = monicElt X N β * R + Y ^ s * monicElt X N β * S

/-! ## The reduction -/

/-- Hypothesis E gives Stafford 3.8 for every Weyl-monic element. -/
theorem stafford38_of_weylMonic (hE : ExponentHypothesis A) {e : A}
    (he : WeylMonic e) : Stafford38 e := by
  obtain ⟨X, Y, N, β, hweyl, hcomm, heq⟩ := he
  obtain ⟨s, R, S, hs⟩ := hE X Y N β hweyl hcomm
  rw [heq]
  exact stafford38_of_power hs

/--
**Stafford 3.8 from the two named hypotheses.**

If every nonzero element monicizes (Hypothesis M) and every Weyl-monic element
admits a cofactor that is a power of the Weyl partner (Hypothesis E), then

    ∀ e ≠ 0, ∃ F R S, 1 = e * R + F * e * S.
-/
theorem stafford38_of_hypotheses
    (hM : Monicization k A) (hE : ExponentHypothesis A) :
    ∀ e : A, e ≠ 0 → Stafford38 e := by
  intro e he
  obtain ⟨φ, c, hc, hmonic⟩ := hM e he
  have h1 : Stafford38 (c • φ e) := stafford38_of_weylMonic hE hmonic
  have h2 : Stafford38 (φ e) := stafford38_smul (k := k) c h1
  exact stafford38_of_ringEquiv (φ : A ≃+* A) h2

end Reduction
end Stafford
