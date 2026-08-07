/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Data.Finsupp.Defs
import LeanPool.JacobianDiffgeo.Meromorphic

/-!
# `Tail X`: free ambient Laurent-tail data, and `TailSpace D` (serre-duality-cech, §2 D1)

Unit: serre-duality-cech (`docs/design/serre-duality-cech.md` §2 D1, §4.1).

Miranda VI.3's *ambient* Laurent-tail space, before any `D`-bound: at finitely many points of `X`,
an arbitrary finite tail of Laurent coefficients (any integer exponents, read in each point's own
`chartAt` — no compatibility/transition data needed, since the pairing (`Pairing.lean`) never
crosses charts). `Tail X` imposes **no** exponent condition at all (finite support only, entirely
free via `Finsupp`); `Tail.BoundedBy`/`TailSpace D` is the only place any bound enters,
parameterized by a divisor `D` (Miranda's `T[D](X)`, top degree `< -(D p)`).

**Deviation from the design** (adaptation, not a correction): `docs/design/serre-duality-cech.md`
declared `Tail X` as a `def` plus manually-registered `AddCommGroup ℂ`/`Module ℂ` instances. The
sibling unit laurent-tails independently discovered that a plain `def` wrapping a `Finsupp`/
`DFinsupp` breaks `DFunLike`/`AddCommGroup`/`Module` instance search
(`Jacobian/LaurentTail/TailSpace.lean`'s own module docstring, confirmed by their spike
`scratch_ltails.lean`); using `abbrev` here sidesteps the issue entirely (reducible unfolding lets
every `Finsupp` instance transport for free), so no manual instances are needed at all.
-/

open scoped ContDiff Manifold

namespace RS.SerrePairing

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Miranda VI.3's *ambient* Laurent-tail space: at finitely many points of `X`, an arbitrary
finite tail of Laurent coefficients (any integer exponents), read in each point's own `chartAt`. -/
noncomputable abbrev Tail (X : Type*)
    : Type _ := X →₀ (ℤ →₀ ℂ)

/-- Miranda's `T[D](X)`-membership condition: the exponent at each point in `τ`'s support is
bounded by `D` (exponent range `< -(D x)`, matching her convention exactly — for `D = 0` this is
"only negative exponents", her own base case). -/
def Tail.BoundedBy (τ : Tail X) (D : RS.Divisor X) : Prop :=
  ∀ x ∈ τ.support, ∀ k ∈ (τ x).support, k < -(D x)

/-- `D`-bounded ambient tails form a submodule (Miranda's `T[D](X)`). -/
def TailSpace (D : RS.Divisor X) : Submodule ℂ (Tail X) where
  carrier := {τ | τ.BoundedBy D}
  zero_mem' := fun x hx => absurd hx (by simp)
  add_mem' {τ σ} hτ hσ := by
    intro x _ k hk
    have hk' : (τ x) k + (σ x) k ≠ 0 := by
      have heq : (τ + σ) x = τ x + σ x := Finsupp.add_apply τ σ x
      have hk2 : ((τ + σ) x) k ≠ 0 := Finsupp.mem_support_iff.1 hk
      rwa [heq] at hk2
    rcases eq_or_ne ((τ x) k) 0 with h1 | h1
    · have h2 : (σ x) k ≠ 0 := fun h2 => hk' (by rw [h1, h2, add_zero])
      have hxσ : x ∈ σ.support :=
        Finsupp.mem_support_iff.2 (fun h0 => h2 (by rw [h0]; simp))
      exact hσ x hxσ k (Finsupp.mem_support_iff.2 h2)
    · have hxτ : x ∈ τ.support :=
        Finsupp.mem_support_iff.2 (fun h0 => h1 (by rw [h0]; simp))
      exact hτ x hxτ k (Finsupp.mem_support_iff.2 h1)
  smul_mem' c {τ} hτ := by
    intro x _ k hk
    have hkc : c * (τ x k) ≠ 0 := by
      have hcs : (c • τ) x = c • (τ x) := Finsupp.smul_apply c τ x
      have hk2 : ((c • τ) x) k ≠ 0 := Finsupp.mem_support_iff.1 hk
      rw [hcs] at hk2
      have hcs2 : (c • τ x) k = c • (τ x k) := Finsupp.smul_apply c (τ x) k
      rwa [hcs2, smul_eq_mul] at hk2
    have hτxk : (τ x) k ≠ 0 := fun h0 => hkc (by rw [h0, mul_zero])
    have hxτ : x ∈ τ.support :=
      Finsupp.mem_support_iff.2 (fun h0 => hτxk (by rw [h0]; simp))
    exact hτ x hxτ k (Finsupp.mem_support_iff.2 hτxk)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [ChartedSpace ℂ X] in
@[simp] theorem mem_tailSpace_iff {τ : Tail X} {D : RS.Divisor X} :
    τ ∈ TailSpace D ↔ τ.BoundedBy D := Iff.rfl

/-- A single-point, single-exponent test tail. -/
noncomputable def Tail.single (p : X) (n : ℤ) (c : ℂ) : Tail X :=
  Finsupp.single p (Finsupp.single n c)

open scoped Classical in
omit [IsManifold 𝓘(ℂ, ℂ) ω X] [ChartedSpace ℂ X] [TopologicalSpace X] in
theorem Tail.single_apply (p : X) (n : ℤ) (c : ℂ) (x : X) :
    Tail.single p n c x = if x = p then Finsupp.single n c else 0 := by
  rw [Tail.single, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [ChartedSpace ℂ X] in
theorem Tail.single_boundedBy {p : X} {n : ℤ} {c : ℂ} {D : RS.Divisor X}
    (h : c ≠ 0 → n < -(D p)) : (Tail.single p n c).BoundedBy D := by
  intro x hx k hk
  rw [Finsupp.mem_support_iff, Tail.single_apply] at hx
  by_cases hxp : x = p
  · subst hxp
    rw [Tail.single_apply, if_pos rfl] at hk
    rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hk
    by_cases hnk : n = k
    · rw [if_pos hnk] at hk
      rw [← hnk]
      exact h hk
    · rw [if_neg hnk] at hk
      exact absurd rfl hk
  · simp [hxp] at hx

end RS.SerrePairing
