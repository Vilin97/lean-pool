/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Main theorem: the Kalton–Roberts upper bound

This file states and proves the main result of the companion paper:
the Kalton–Roberts constant satisfies `K_KR < 9919/500 = 19.838`.

The proof reduces to two cases (q ≤ q₀ and q ≥ q₀), applies mixed-intersection
constructions and two rounds of expander recombination in each case, and balances
the resulting inequalities to obtain the bounds C₁ and C₂.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Numerical
import LeanPool.KaltonRoberts.Lemmas
import LeanPool.KaltonRoberts.Collections
import LeanPool.KaltonRoberts.Pipeline
import LeanPool.KaltonRoberts.PipelineEps
import LeanPool.KaltonRoberts.EpsilonRecombination

/-!
# Main theorem: the Kalton-Roberts upper bound

The final proof that the Kalton-Roberts constant is less than `9919 / 500`.
-/

namespace KaltonRoberts

open Finset BigOperators

/-! ## Case 1 details -/

/-- **Case 1** of the proof of Theorem 1.1 (`q ≤ q₀`).
Given `M, D'` satisfying the two recombination inequalities from `E₁` and `E₂`:
  `M ≤ A₁ − (1/2) D'`  (Equation (12), from one-sided recombination with E₁)
  `M ≤ 15 + (7/3) D'`  (Equation (13), from one-sided recombination with E₂)
we conclude `M ≤ C₁`.

**Reference**: Case 1 in Section 5 of the companion paper,
Equations (12)–(14). -/
theorem case1_bound (M D' : ℝ) (_hD' : 0 ≤ D')
    (A₁ : ℝ)
    (h1 : M ≤ A₁ - 1 / 2 * D')
    (h2 : M ≤ 15 + 7 / 3 * D') :
    M ≤ (7 / 3 * A₁ + 1 / 2 * 15) / (7 / 3 + 1 / 2) := by
  have h17 : (7 : ℝ) / 3 + 1 / 2 > 0 := by norm_num
  rw [le_div_iff₀ h17]
  nlinarith

/-- In Case 1, the balanced bound equals `C₁`.
**Reference**: Equation (14) in Section 5 of
the companion paper. -/
theorem case1_bound_eq_C₁ :
    let D₁ : ℚ := 6 * q₀ + 4 + τ₁ * (2 * q₀ + 2)
    let A₁ : ℚ := 10 + 3 / 2 * D₁
    (7 / 3 * A₁ + 1 / 2 * 15) / (7 / 3 + 1 / 2) = C₁ :=
  case1_balance

/-! ## Case 2 details -/

/-- **Case 2** of the proof of Theorem 1.1 (`q ≥ q₀`).
Given `M, Y` satisfying the two recombination inequalities from `E₃` and `E₄`:
  `M ≤ A₂ − (2/5) Y`    (Equation (15), from two-sided recombination with E₃)
  `M ≤ 47/3 + (11/6) Y`  (Equation (16), from two-sided recombination with E₄)
we conclude `M ≤ C₂`.

**Reference**: Case 2 in Section 5 of the companion paper,
Equations (15)–(17). -/
theorem case2_bound (M Y : ℝ) (_hY : 0 ≤ Y)
    (A₂ : ℝ)
    (h1 : M ≤ A₂ - 2 / 5 * Y)
    (h2 : M ≤ 47 / 3 + 11 / 6 * Y) :
    M ≤ (11 / 6 * A₂ + 2 / 5 * (47 / 3)) / (11 / 6 + 2 / 5) := by
  have h17 : (11 : ℝ) / 6 + 2 / 5 > 0 := by norm_num
  rw [le_div_iff₀ h17]
  nlinarith

/-- In Case 2, the balanced bound equals `C₂`.
**Reference**: Equation (17) in Section 5 of
the companion paper. -/
theorem case2_bound_eq_C₂ :
    let X₀ : ℚ := 4 * p₀ + 6 + τ₂ * (p₀ + 1)
    let A₂ : ℚ := 47 / 5 + 7 / 5 * X₀
    (11 / 6 * A₂ + 2 / 5 * (47 / 3)) / (11 / 6 + 2 / 5) = C₂ :=
  case2_balance

/-! ## The u-bound (Equation (3)) -/

/-
**Equation (3)** in Section 2. If `f` is `1`-additive, `M = ‖f‖_∞`,
and there exist positive and negative active sets, then `|f(U)| ≤ 1`.

**Reference**: Equation (3) in Section 2 of the companion paper.
-/
theorem u_bound {U : Type*} [DecidableEq U] [Fintype U]
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    (_M : ℝ) (_hM : 0 ≤ _M)
    (hMbound : ∀ S : Finset U, |f S| ≤ _M)
    (P : Finset U) (hP : f P = _M)
    (N : Finset U) (hN : f N = -_M) :
    |f Finset.univ| ≤ 1 := by
  have hP : |f P + f Pᶜ - f Finset.univ| ≤ 1 := by
    convert hf.2 P Pᶜ (Finset.disjoint_right.mpr fun x => by aesop) using 1
    simp +decide [Finset.union_compl]
  have hN : |f N + f Nᶜ - f Finset.univ| ≤ 1 := by
    convert hf.2 N Nᶜ ( disjoint_compl_right ) using 1; aesop;
  grind

/-! ## The finite normalised theorem -/

/-
**Theorem 1.1** (finite normalised form). For every finite type `U` and
every `1`-additive function `f : 2^U → ℝ`, there is an additive signed
measure within `ℓ∞`-distance `C₂` of `f`.

**Reference**: Theorem 1.1 and Section 5 of the companion paper.
-/
lemma exists_additive_approx (U : Type*) [Finite U]
    (f : Finset U → ℝ) (C : ℝ) (hC : distToAdditive f ≤ C) :
    ∃ a : U → ℝ, ∀ S : Finset U, |f S - additiveFunction a S| ≤ C := by
  classical
  let := Fintype.ofFinite U
  have h_exists_a : ∃ a : U → ℝ, ∀ S : Finset U, |f S - additiveFunction a S| ≤ distToAdditive f :=
    by
    by_contra h_contra;
    obtain ⟨a_n, ha_n⟩ : ∃ a_n : ℕ → (U → ℝ), Filter.Tendsto (fun n => ⨆ S : Finset U, |f S -
      additiveFunction (a_n n) S|) Filter.atTop (nhds (distToAdditive f)) := by
      have h_seq : ∀ ε > 0, ∃ a : U → ℝ, ⨆ S : Finset U, |f S - additiveFunction a S| <
        distToAdditive f + ε := by
        exact fun ε εpos => by rcases exists_lt_of_csInf_lt ( show Set.Nonempty { a : ℝ | ∃ a' : U →
          ℝ, ⨆ S : Finset U, |f S - additiveFunction a' S| = a } from ⟨ _, ⟨ 0, rfl ⟩ ⟩ ) (
            lt_add_of_pos_right _ εpos ) with ⟨ a, ⟨ a', rfl ⟩, ha ⟩; exact ⟨ a', ha ⟩;
      choose a ha using fun n : ℕ => h_seq ( 1 / ( n + 1 ) ) ( by positivity );
      refine ⟨a, ?_⟩
      refine tendsto_order.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact Filter.Eventually.of_forall fun n => by
          refine lt_of_lt_of_le hx ?_
          have hbdd : BddBelow (Set.range fun a : U → ℝ =>
              ⨆ S : Finset U, |f S - additiveFunction a S|) := by
            refine ⟨0, ?_⟩
            rintro _ ⟨a, rfl⟩
            exact Real.iSup_nonneg fun _ => abs_nonneg _
          exact ciInf_le hbdd _
      · exact Filter.eventually_atTop.2
          ⟨Nat.ceil ((x - distToAdditive f)⁻¹), fun n hn =>
            lt_of_lt_of_le (ha n) (by
              nlinarith [Nat.ceil_le.1 hn,
                inv_mul_cancel₀ (by linarith : (x - distToAdditive f) ≠ 0),
                one_div_mul_cancel (by linarith : (n : ℝ) + 1 ≠ 0)])⟩
    have h_bounded : ∃ M : ℝ, ∀ n, ∀ S : Finset U, |f S - additiveFunction (a_n n) S| ≤ M := by
      have h_bounded : ∃ M : ℝ, ∀ n, ⨆ S : Finset U, |f S - additiveFunction (a_n n) S| ≤ M := by
        exact ⟨ _, fun n => le_ciSup ( show BddAbove ( Set.range fun n => ⨆ S : Finset U, |f S -
          additiveFunction ( a_n n ) S| ) from ha_n.bddAbove_range ) n ⟩;
      exact ⟨ h_bounded.choose, fun n S => le_trans ( le_ciSup ( Finite.bddAbove_range fun S => |f S
        - additiveFunction ( a_n n ) S| ) S ) ( h_bounded.choose_spec n ) ⟩;
    obtain ⟨a_lim, ha_lim⟩ : ∃ a_lim : U → ℝ, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto
      (fun n => a_n (subseq n)) Filter.atTop (nhds a_lim) := by
      have h_compact : IsCompact (Set.pi Set.univ fun i : U => Set.Icc (-h_bounded.choose - |f {i}|)
        (h_bounded.choose + |f {i}|)) := by
        exact isCompact_univ_pi fun i => CompactIccSpace.isCompact_Icc;
      have h_bounded : ∀ n, ∀ i : U, |a_n n i| ≤ h_bounded.choose + |f {i}| := by
        intro n i
        specialize h_bounded
        have := h_bounded.choose_spec n {i}
        simp_all +decide only [ge_iff_le, additiveFunction, Finset.sum_singleton]
        exact abs_le.mpr
          ⟨by
            cases abs_cases (f {i}) <;> linarith [abs_le.mp this],
            by
            cases abs_cases (f {i}) <;> linarith [abs_le.mp this]⟩
      have := h_compact.isSeqCompact fun n =>
        show a_n n ∈ Set.pi Set.univ fun i =>
            Set.Icc
              (-‹∃ M, ∀ n S, |f S - additiveFunction (a_n n) S| ≤ M›.choose - |f {i}|)
              (‹∃ M, ∀ n S, |f S - additiveFunction (a_n n) S| ≤ M›.choose + |f {i}|) from
          fun i _ =>
            ⟨by linarith [abs_le.mp (h_bounded n i)],
              by linarith [abs_le.mp (h_bounded n i)]⟩
      tauto;
    obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := ha_lim;
    have h_liminf : ∀ S : Finset U, |f S - additiveFunction a_lim S| ≤ distToAdditive f := by
      intro S
      have h_liminf_S : Filter.Tendsto (fun n => |f S - additiveFunction (a_n (subseq n)) S|)
        Filter.atTop (nhds (|f S - additiveFunction a_lim S|)) := by
        exact Filter.Tendsto.abs ( tendsto_const_nhds.sub ( tendsto_finsetSum _ fun i _ =>
          tendsto_pi_nhds.mp hsubseq₂ i ) );
      exact le_of_tendsto_of_tendsto' h_liminf_S ( ha_n.comp hsubseq₁.tendsto_atTop ) fun n =>
        le_ciSup ( Finite.bddAbove_range fun S => |f S - additiveFunction ( a_n ( subseq n ) ) S| )
          S;
    exact h_contra ⟨ a_lim, h_liminf ⟩;
  exact ⟨ h_exists_a.choose, fun S => le_trans ( h_exists_a.choose_spec S ) hC ⟩

/-- **Core distance bound**: `distToAdditive f ≤ C₂`.

The proof depends on the full pipeline:
1. Dual certificate (proved in `DualCert.lean`)
2. Weighted collection construction (proved in `Collections.lean`)
3. Mixed intersection construction (Corollary 3.1)
4. Expander recombination (Lemmas 3.2–3.3)
5. Expander existence via Pippenger entropy (Lemma 4.1)
6. Case analysis and balancing (Section 5)

The theorem `distToAdditive_le_C₂_from_pipeline` in `Pipeline.lean`
makes explicit each missing ingredient as a hypothesis. Here we
instantiate those hypotheses from the concrete theorems. -/
/- The proof follows from `distToAdditive_le_C₂_from_pipeline` in `PipelineEps.lean`
   which uses epsilon recombination + the real-analysis principle
   ∀ ε > 0, x ≤ y + ε ⇒ x ≤ y.

   Pipeline components:
   - `mixed_intersection_weighted` (Corollary 3.1)
   - `mixed_intersection_weighted_surplus` (Corollary 3.1, surplus)
   - `one_sided_recombination_core_eps` (Lemma 3.2, ε-version)
   - `two_sided_recombination_core_eps` (Lemma 3.3, ε-version)
   - `expander_E₁` through `expander_E₄` (Lemma 4.1)
   See `PipelineEps.lean` and `EpsilonRecombination.lean`. -/
lemma distToAdditive_le_C₂ (U : Type*) [DecidableEq U] [Finite U]
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) :
    distToAdditive f ≤ ↑C₂ := by
  let := Fintype.ofFinite U
  exact distToAdditive_le_C₂_from_pipeline f hf
    (exists_additive_approx U f (distToAdditive f) (le_refl _))
    (fun g hg M hM => mixed_intersection_weighted g hg M hM)
    (fun g hg M hM => mixed_intersection_weighted_surplus g hg M hM)
    (fun g hg M hM α_v r_v θ_v hθ hθ1 hexp hr hα C hfreq D hD hdeficit ε hε =>
      one_sided_recombination_core_eps g hg M hM α_v r_v θ_v hθ hθ1 hexp hr hα
        C hfreq D hD hdeficit ε hε)
    (fun g hg M hM α_v r_v θ_v hθ hθ1 hexp hr hα C_def C_sur hfreq_def hfreq_sur
        D S_val hD hS hdeficit hsurplus ε hε =>
      two_sided_recombination_core_eps g hg M hM α_v r_v θ_v hθ hθ1 hexp hr hα
        C_def C_sur hfreq_def hfreq_sur D S_val hD hS hdeficit hsurplus ε hε)
    expander_E₁ expander_E₂ expander_E₃ expander_E₄

theorem finite_KR_bound (U : Type*) [DecidableEq U] [Finite U]
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) :
    ∃ a : U → ℝ, ∀ S : Finset U, |f S - additiveFunction a S| ≤ (C₂ : ℚ) :=
  exists_additive_approx U f ↑C₂ (distToAdditive_le_C₂ U f hf)

/-- The normalized theorem on arbitrary Boolean algebras, obtained from the
finite powerset theorem by the compact reduction. -/
theorem boolean_KR_bound_C₂ (α : Type*) [BooleanAlgebra α]
    (f : α → ℝ) (hf : IsApproxAdditiveBA f 1) :
    ∃ μ : α → ℝ, IsFinitelyAdditiveBA μ ∧ ∀ A : α, |f A - μ A| ≤ (C₂ : ℚ) := by
  have hC : (0 : ℝ) ≤ (C₂ : ℚ) := by
    norm_num [C₂]
  exact finite_reduction (C := (C₂ : ℝ)) hC
    (fun U _ _ f hf => by
      exact_mod_cast finite_KR_bound U f hf)
    α f hf

/-- Theorem 1.1 in its scaled Boolean-algebra form. -/
theorem boolean_KR_bound_C₂_delta (α : Type*) [BooleanAlgebra α]
    (f : α → ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hf : IsApproxAdditiveBA f Δ) :
    ∃ μ : α → ℝ, IsFinitelyAdditiveBA μ ∧
      ∀ A : α, |f A - μ A| ≤ (C₂ : ℝ) * Δ := by
  classical
  by_cases hΔ0 : Δ = 0
  · subst Δ
    refine ⟨f, ?_, ?_⟩
    · constructor
      · exact hf.1
      · intro A B hAB
        have hle : |f A + f B - f (A ⊔ B)| ≤ (0 : ℝ) := hf.2 A B hAB
        have habs : |f A + f B - f (A ⊔ B)| = 0 :=
          le_antisymm hle (abs_nonneg _)
        have hz : f A + f B - f (A ⊔ B) = 0 := abs_eq_zero.mp habs
        linarith
    · simp_all
  · have hΔpos : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm hΔ0)
    let g : α → ℝ := fun A => Δ⁻¹ * f A
    have hg : IsApproxAdditiveBA g 1 := by
      constructor
      · simp [g, hf.1]
      · intro A B hAB
        have h := hf.2 A B hAB
        have hscale :
            |g A + g B - g (A ⊔ B)| =
              Δ⁻¹ * |f A + f B - f (A ⊔ B)| := by
          have hrewrite :
              g A + g B - g (A ⊔ B) =
                Δ⁻¹ * (f A + f B - f (A ⊔ B)) := by
            simp [g]
            ring
          rw [hrewrite, abs_mul, abs_of_pos (inv_pos.mpr hΔpos)]
        rw [hscale]
        calc
          Δ⁻¹ * |f A + f B - f (A ⊔ B)| ≤ Δ⁻¹ * Δ :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hΔ)
          _ = 1 := by field_simp [hΔpos.ne']
    obtain ⟨ν, hνadd, hνclose⟩ := boolean_KR_bound_C₂ α g hg
    let μ : α → ℝ := fun A => Δ * ν A
    refine ⟨μ, ?_, ?_⟩
    · constructor
      · simp [μ, hνadd.1]
      · intro A B hAB
        dsimp [μ]
        rw [hνadd.2 A B hAB]
        ring
    · intro A
      have hclose := hνclose A
      have hrewrite : f A - μ A = Δ * (g A - ν A) := by
        simp [g, μ]
        field_simp [hΔpos.ne']
      rw [hrewrite, abs_mul, abs_of_nonneg hΔ]
      calc
        Δ * |g A - ν A| ≤ Δ * (C₂ : ℝ) :=
          mul_le_mul_of_nonneg_left hclose hΔ
        _ = (C₂ : ℝ) * Δ := by ring

/-- The paper's set-algebra formulation. A set algebra is represented as a
Boolean subalgebra of `Set Ω`. -/
theorem set_algebra_bound_C₂ {Ω : Type*} (F : BooleanSubalgebra (Set Ω))
    (f : F → ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hf : IsApproxAdditiveBA f Δ) :
    ∃ μ : F → ℝ, IsFinitelyAdditiveBA μ ∧
      ∀ A : F, |f A - μ A| ≤ (C₂ : ℝ) * Δ :=
  boolean_KR_bound_C₂_delta F f Δ hΔ hf

/-! ## Main theorem -/

/-- **Theorem 1.1** (Main theorem). The Kalton–Roberts constant satisfies
`K_KR ≤ C₂ = 694198146664396294486127753 / 34994834677886019996000000`.
Consequently, `K_KR < 9919/500 = 19.838`.

**Reference**: Theorem 1.1 in Section 1 of the companion paper. -/
theorem KR_constant_le_C₂ : krConstant ≤ ↑C₂ := by
  apply csInf_le
  · exact ⟨0, fun C ⟨hC, _⟩ => hC⟩
  · refine ⟨?_, fun α _ f hf => ?_⟩
    · have : (0 : ℝ) ≤ (C₂ : ℚ) := by simp [C₂]; norm_num
      exact_mod_cast this
    · exact boolean_KR_bound_C₂ α f hf

/-- **Theorem 1.1**, headline inequality.
**Reference**: second display of Theorem 1.1 in the companion paper. -/
theorem KR_constant_lt : krConstant < 9919 / 500 := by
  calc krConstant ≤ ↑C₂ := KR_constant_le_C₂
    _ < ↑krUpper := by exact_mod_cast C₂_lt_KR_upper
    _ = 9919 / 500 := by simp [krUpper]

end KaltonRoberts
