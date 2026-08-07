/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality.Pairing
import LeanPool.JacobianDiffgeo.LaurentTail.Comparison
import LeanPool.JacobianDiffgeo.Finiteness

/-!
# `nuPairDual`/Miranda Lemma 3.4: the counting step (serre-duality-tails)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §6 P5, addendum re-basing).

* `instFiniteDimensional_H1Tail`: `H1Tail D` is finite-dimensional for EVERY `D`, via
  `H1Tail.toH1_injective` (unconditional, landed) + `Finiteness.finiteDimensional_H1` (an
  injection into a finite-dimensional space) — the orchestrator addendum's re-basing, NOT via
  the (Serre-circular, out-of-scope) surjectivity of `tailToH1`.
* `h1T`/`h1T_le_h1`: the tail-level `h¹`, bounded above by the Čech `h¹` via the same injection
  (this ONE inequality is all Lemma 3.4's internal arithmetic needs from the Čech side — no
  tail-level six-term ledger is required here).
* `nuPairDual`/`two_l_le_h1T_of_injective`: the pair-map dimension count.
* `exists_mul_functional_eq`: **MIRANDA LEMMA 3.4**.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Finite-dimensionality of `H1Tail D`, via injection into `Cech.H1 D` -/

noncomputable instance instFiniteDimensional_H1Tail (D : RS.Divisor X) :
    FiniteDimensional ℂ (H1Tail D) :=
  FiniteDimensional.of_injective (H1Tail.toH1 D) (H1Tail.toH1_injective D)

/-- The tail-level `h¹`. -/
noncomputable def h1T (D : RS.Divisor X) : ℕ := Module.finrank ℂ (H1Tail D)

/-- `h1T D ≤ h1 D` (Čech), via the injection `H1Tail.toH1` — the ONE fact Lemma 3.4's
arithmetic borrows from the Čech side (no tail-level six-term ledger needed). -/
theorem h1T_le_h1 (D : RS.Divisor X) : h1T D ≤ RS.Finiteness.h1 D :=
  LinearMap.finrank_le_finrank_of_injective (H1Tail.toH1_injective D)

/-! ### `nuPairDual`: the pair map into `Dual (H1Tail (A - C))` -/

/-- Miranda's pair map `(f₁,f₂) ↦ φ₁∘t∘μ_{f₁} − φ₂∘t∘μ_{f₂}`, packaged as a linear map into the
dual of `H1Tail (A - C)` (well-defined: kills `range (alphaL (A-C))` by `nuL_alpha` + the
vanishing hypotheses). -/
noncomputable def nuPairDual (A C : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : RS.Mero X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g : RS.Mero X, φ₂ (alphaL A g) = 0) :
    (↥(RS.LinSys C) × ↥(RS.LinSys C)) →ₗ[ℂ] Module.Dual ℂ (H1Tail (A - C)) where
  toFun fg := Submodule.liftQ (LinearMap.range (alphaL (A - C)))
    (φ₁.comp (nuL A C fg.1) - φ₂.comp (nuL A C fg.2))
    (by
      rintro τ ⟨g, rfl⟩
      change φ₁ (nuL A C fg.1 (alphaL (A - C) g)) - φ₂ (nuL A C fg.2 (alphaL (A - C) g)) = 0
      rw [nuL_alpha, nuL_alpha, hα₁, hα₂, sub_zero])
  map_add' fg fg' := by
    apply LinearMap.ext
    intro x
    obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective (A - C) x
    change (φ₁.comp (nuL A C (fg.1 + fg'.1)) - φ₂.comp (nuL A C (fg.2 + fg'.2))) τ
        = (φ₁.comp (nuL A C fg.1) - φ₂.comp (nuL A C fg.2)) τ
          + (φ₁.comp (nuL A C fg'.1) - φ₂.comp (nuL A C fg'.2)) τ
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
    ring
  map_smul' c fg := by
    apply LinearMap.ext
    intro x
    obtain ⟨τ, rfl⟩ := H1Tail.mk_surjective (A - C) x
    change (φ₁.comp (nuL A C (c • fg.1)) - φ₂.comp (nuL A C (c • fg.2))) τ
        = (RingHom.id ℂ) c • (φ₁.comp (nuL A C fg.1) - φ₂.comp (nuL A C fg.2)) τ
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply, smul_eq_mul]
    ring

theorem nuPairDual_apply (A C : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : RS.Mero X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g : RS.Mero X, φ₂ (alphaL A g) = 0)
    (f₁ f₂ : ↥(RS.LinSys C)) (τ : T (A - C)) :
    nuPairDual A C φ₁ φ₂ hα₁ hα₂ (f₁, f₂) (H1Tail.mk (A - C) τ) =
      φ₁ (nuL A C f₁ τ) - φ₂ (nuL A C f₂ τ) :=
  Submodule.liftQ_apply _ _ τ

theorem two_l_le_h1T_of_injective (A C : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : RS.Mero X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g : RS.Mero X, φ₂ (alphaL A g) = 0)
    (hinj : Function.Injective (nuPairDual A C φ₁ φ₂ hα₁ hα₂)) :
    2 * (RS.l C : ℤ) ≤ (h1T (A - C) : ℤ) := by
  have hle : Module.finrank ℂ (↥(RS.LinSys C) × ↥(RS.LinSys C)) ≤ Module.finrank ℂ
      (H1Tail (A - C)) := by
    rw [show Module.finrank ℂ (H1Tail (A - C)) = Module.finrank ℂ (Module.Dual ℂ (H1Tail (A - C)))
      from (Subspace.dual_finrank_eq).symm]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  have hlC : Module.finrank ℂ (↥(RS.LinSys C)) = RS.l C := rfl
  rw [hlC] at hle
  have : RS.l C + RS.l C ≤ h1T (A - C) := hle
  omega

/-! ### `exists_mul_functional_eq`: MIRANDA LEMMA 3.4 -/

/-- **MIRANDA LEMMA 3.4**: for nonzero functionals on `T A` vanishing on `range (alphaL A)`,
there are `C ≥ 0` and nonzero `f₁ f₂ ∈ L(C)` with `φ₁∘t∘μ_{f₁} = φ₂∘t∘μ_{f₂}` on `T (A - C)`. -/
theorem exists_mul_functional_eq (A : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : RS.Mero X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g : RS.Mero X, φ₂ (alphaL A g) = 0)
    (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) :
    ∃ C : RS.Divisor X, 0 ≤ C ∧ ∃ f₁ f₂ : ↥(RS.LinSys C),
      (f₁ : RS.Mero X) ≠ 0 ∧ (f₂ : RS.Mero X) ≠ 0 ∧
      φ₁ ∘ₗ nuL A C f₁ = φ₂ ∘ₗ nuL A C f₂ := by
  by_contra hcon
  push Not at hcon
  have hinj : ∀ C : RS.Divisor X, 0 ≤ C →
      Function.Injective (nuPairDual A C φ₁ φ₂ hα₁ hα₂) := by
    intro C hC
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    obtain ⟨⟨f₁, f₂⟩, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker] at hmem
    have hfun : φ₁ ∘ₗ nuL A C f₁ = φ₂ ∘ₗ nuL A C f₂ := by
      apply LinearMap.ext
      intro τ
      have hτ := DFunLike.congr_fun hmem (H1Tail.mk (A - C) τ)
      rw [LinearMap.zero_apply, nuPairDual_apply] at hτ
      change φ₁ (nuL A C f₁ τ) = φ₂ (nuL A C f₂ τ)
      rwa [sub_eq_zero] at hτ
    have hf1 : (f₁ : RS.Mero X) ≠ 0 := by
      intro hf1z
      have hf1z' : f₁ = 0 := Subtype.ext hf1z
      rw [hf1z', map_zero, LinearMap.comp_zero] at hfun
      by_cases hf2z : (f₂ : RS.Mero X) = 0
      · exact hne (Prod.ext hf1z' (Subtype.ext hf2z))
      · apply h₂
        apply LinearMap.ext
        intro τ'
        obtain ⟨τ, rfl⟩ := nuL_surjective A C hf2z τ'
        have h3 := DFunLike.congr_fun hfun.symm τ
        simpa using h3
    have hf2 : (f₂ : RS.Mero X) ≠ 0 := by
      intro hf2z
      have hf2z' : f₂ = 0 := Subtype.ext hf2z
      rw [hf2z', map_zero, LinearMap.comp_zero] at hfun
      by_cases hf1z : (f₁ : RS.Mero X) = 0
      · exact hne (Prod.ext (Subtype.ext hf1z) hf2z')
      · apply h₁
        apply LinearMap.ext
        intro τ'
        obtain ⟨τ, rfl⟩ := nuL_surjective A C hf1z τ'
        have h3 := DFunLike.congr_fun hfun τ
        simpa using h3
    exact hcon C hC f₁ f₂ hf1 hf2 hfun
  have harith : ∀ C : RS.Divisor X, 0 ≤ C →
      C.degree ≤ (RS.l A : ℤ) - 3 * RS.Finiteness.chi (0 : RS.Divisor X) - A.degree := by
    intro C hC
    have hAC_le : A - C ≤ A := by
      rw [Function.locallyFinsuppWithin.le_def]
      intro p
      rw [Divisor.sub_apply]
      -- (routed through a divisor-free arithmetic helper: `A p`/`C p` reached via `apply`'s
      -- unification rather than `omega`'s atom detection, which was observed to desync on
      -- syntactically-different-but-defeq terms coming from different lemma applications —
      -- see `TailOps.lean`'s `sub_divisor_le` for the same fix, confirmed by a targeted spike)
      have key : ∀ d : ℤ, 0 ≤ d → A p - d ≤ A p := fun d hd => by omega
      exact key (C p) (Function.locallyFinsuppWithin.le_def.1 hC p)
    have h2l : 2 * (RS.l C : ℤ) ≤ (h1T (A - C) : ℤ) :=
      two_l_le_h1T_of_injective A C φ₁ φ₂ hα₁ hα₂ (hinj C hC)
    have hh1h1T : (h1T (A - C) : ℤ) ≤ (RS.Finiteness.h1 (A - C) : ℤ) := by
      exact_mod_cast h1T_le_h1 (A - C)
    have hchidef : RS.Finiteness.chi (A - C) =
        (RS.l (A - C) : ℤ) - (RS.Finiteness.h1 (A - C) : ℤ) := rfl
    have hchi : RS.Finiteness.chi (A - C) = RS.Finiteness.chi (0 : RS.Divisor X) + (A - C).degree :=
      RS.Finiteness.chi_eq_chi_zero_add_degree (A - C)
    have hlmono : (RS.l (A - C) : ℤ) ≤ (RS.l A : ℤ) := by exact_mod_cast RS.Finiteness.l_mono hAC_le
    have hdeg : (A - C).degree = A.degree - C.degree := by
      rw [sub_eq_add_neg, Function.locallyFinsuppWithin.degree_add,
        Function.locallyFinsuppWithin.degree_neg]
      ring
    have hchi0le : RS.Finiteness.chi (0 : RS.Divisor X) + C.degree ≤ (RS.l C : ℤ) :=
      RS.Finiteness.chi_zero_add_degree_le_l C
    omega
  set n : ℕ := (RS.l A - 3 * RS.Finiteness.chi (0 : RS.Divisor X) - A.degree).toNat + 1 with hn_def
  set P : X := Classical.arbitrary X with hP_def
  set C₀ : RS.Divisor X := Function.locallyFinsuppWithin.single P (n : ℤ) with hC₀_def
  have hC₀nonneg : 0 ≤ C₀ := Function.locallyFinsuppWithin.single_nonneg.2 (by positivity)
  have hC₀deg : C₀.degree = (n : ℤ) := Function.locallyFinsuppWithin.degree_single P (n : ℤ)
  have hbad := harith C₀ hC₀nonneg
  rw [hC₀deg] at hbad
  omega

end RS.TailDuality
