/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Pipeline: mixed intersections, recombination, and the spine theorem

This file provides the honest mathematical interfaces connecting
weighted collections (from `Collections.lean`) through mixed intersections
and expander recombination to the final distance bound.

**Reference**: Sections 3 and 5 of the companion paper.
-/
import LeanPool.KaltonRoberts.Defs
import LeanPool.KaltonRoberts.Numerical
import LeanPool.KaltonRoberts.Collections
import LeanPool.KaltonRoberts.Lemmas
import LeanPool.KaltonRoberts.Intersections
import LeanPool.KaltonRoberts.Pippenger

/-!
# Pipeline from intersections to the final bound

Interfaces connecting weighted collections through mixed intersections and
expander recombination to the final distance bound.
-/

namespace KaltonRoberts

open Finset BigOperators

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Mixed intersection construction -/

omit [Fintype U] in
/-- **Corollary 3.1** (Mixed intersections, deficit version). -/
theorem mixed_intersection_weighted
    [Finite U]
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (C : WeightedCollection U)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfreq : ∀ i : U, C.itemFreq i ≤ t)
    (D : ℝ) (hD : 0 ≤ D)
    (hdeficit : C.avgDeficit f M ≤ D)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ_mix : ℝ) (hτ : 0 ≤ τ_mix) (hτ1 : τ_mix ≤ 1) :
    ∃ C' : WeightedCollection U,
      (∀ i : U, C'.itemFreq i ≤ (1 - τ_mix) * t ^ ℓ + τ_mix * t ^ (ℓ + 1)) ∧
      C'.avgDeficit f M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ_mix * (D + 2) := by
  let := Fintype.ofFinite U
  exact ⟨C.mixedInter ℓ τ_mix hτ hτ1,
    WeightedCollection.mixedInter_itemFreq_le C ℓ hℓ τ_mix hτ hτ1 t ht ht1 hfreq,
    WeightedCollection.mixedInter_avgDeficit_le C ℓ hℓ τ_mix hτ hτ1
      f hf M hM D hD hdeficit⟩

omit [Fintype U] in
/-- **Corollary 3.1** (Mixed intersections, surplus version). -/
theorem mixed_intersection_weighted_surplus
    [Finite U]
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (C : WeightedCollection U)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfreq : ∀ i : U, C.itemFreq i ≤ t)
    (S_val : ℝ) (hS : 0 ≤ S_val)
    (hsurplus : C.avgSurplus f M ≤ S_val)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (τ_mix : ℝ) (hτ : 0 ≤ τ_mix) (hτ1 : τ_mix ≤ 1) :
    ∃ C' : WeightedCollection U,
      (∀ i : U, C'.itemFreq i ≤ (1 - τ_mix) * t ^ ℓ + τ_mix * t ^ (ℓ + 1)) ∧
      C'.avgSurplus f M ≤ ℓ * S_val + 2 * ((ℓ : ℝ) - 1) + τ_mix * (S_val + 2) := by
  let := Fintype.ofFinite U
  -- Apply the deficit version to g := -f
  have hg : IsApproxAdditive (fun S => -f S) 1 := by
    constructor
    · simp [hf.1]
    · intro A B hAB
      have h := hf.2 A B hAB
      rwa [show -f A + -f B - -f (A ∪ B) = -(f A + f B - f (A ∪ B)) from by ring, abs_neg]
  have hgM : ∀ S : Finset U, |(fun S => -f S) S| ≤ M := fun S => by
    simp_all
  have hg_deficit : C.avgDeficit (fun S => -f S) M ≤ S_val := by
    rw [show C.avgDeficit (fun S => -f S) M = C.avgSurplus f M by
      simp [WeightedCollection.avgDeficit, WeightedCollection.avgSurplus, deficit, surplus]]
    exact hsurplus
  obtain ⟨C', hfreq', hdef'⟩ := mixed_intersection_weighted (fun S => -f S) hg M hgM C t ht ht1
    hfreq S_val hS hg_deficit ℓ hℓ τ_mix hτ hτ1
  refine ⟨C', hfreq', ?_⟩
  have : C'.avgDeficit (fun S => -f S) M = C'.avgSurplus f M := by
    simp [WeightedCollection.avgDeficit, WeightedCollection.avgSurplus, deficit, surplus]
  simp_all

/-! ## Expander existence for the four rows

The Pippenger construction and numerical certificates are in `Pippenger.lean`.
The theorems are re-exported here for use in the spine proof. -/

theorem expander_E₁ : StrongExpandersExist α₁ 4 (1 / 3) :=
  pippenger_required_expanders.1

theorem expander_E₂ : StrongExpandersExist (3009 / 10000) 4 (4 / 7) :=
  pippenger_required_expanders.2.1

theorem expander_E₃ : StrongExpandersExist α₂ 4 (2 / 7) :=
  pippenger_required_expanders.2.2.1

theorem expander_E₄ : StrongExpandersExist (329 / 1250) 5 (5 / 11) :=
  pippenger_required_expanders.2.2.2

/-! ## Normalization helpers -/

omit [Fintype U] in
lemma IsApproxAdditive_sub_additive
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) (a : U → ℝ) :
    IsApproxAdditive (fun S => f S - additiveFunction a S) 1 := by
  refine ⟨?_, fun A B hAB => ?_⟩
  · simp +decide [ hf.1, additiveFunction ]
  · convert hf.2 A B hAB using 1; simp +decide [ additiveFunction, Finset.sum_union hAB ]; ring_nf

omit [DecidableEq U] [Fintype U] in
lemma distToAdditive_sub_additive
    (f : Finset U → ℝ) (a : U → ℝ) :
    distToAdditive (fun S => f S - additiveFunction a S) = distToAdditive f := by
  classical
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun b => ?_
    refine le_trans (ciInf_le
      (⟨0, Set.forall_mem_range.2 fun _ => Real.iSup_nonneg fun _ => abs_nonneg _⟩)
      (fun i => b i - a i)) ?_
    simp +decide [ additiveFunction, Finset.sum_sub_distrib ]
  · refine le_ciInf fun b => ?_
    refine le_trans (ciInf_le
      (⟨0, Set.forall_mem_range.2 fun a => Real.iSup_nonneg fun S => abs_nonneg _⟩)
      (fun i => a i + b i)) (le_of_eq ?_)
    simp +decide [ additiveFunction, Finset.sum_add_distrib, sub_sub ]

/-! ## Negation helpers for the swap-to-small-q step -/

/-- Negated certificate: if cert is a DualCertificate for f with M,
then negating lambda gives a DualCertificate for (-f) with M. -/
noncomputable def DualCertificate.neg
    {f : Finset U → ℝ} {M : ℝ}
    (cert : DualCertificate f M) :
    DualCertificate (fun S => -f S) M where
  lam := fun S => -cert.lam S
  norm_one := by
    simp only [abs_neg]
    exact cert.norm_one
  zero_marginals := by
    intro i; simp only [sum_neg_distrib, neg_eq_zero]; exact cert.zero_marginals i
  pos_support := by
    intro S hS; have := cert.neg_support S (by linarith); linarith
  neg_support := by
    intro S hS; have := cert.pos_support S (by linarith); linarith

lemma DualCertificate.neg_negMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.neg.negMass = cert.posMass := by
  simp [DualCertificate.negMass, DualCertificate.neg, DualCertificate.posMass]

lemma DualCertificate.neg_posMass
    {f : Finset U → ℝ} {M : ℝ} (cert : DualCertificate f M) :
    cert.neg.posMass = cert.negMass := by
  simp [DualCertificate.posMass, DualCertificate.neg, DualCertificate.negMass]

omit [Fintype U] in
lemma IsApproxAdditive_neg (f : Finset U → ℝ) (hf : IsApproxAdditive f 1) :
    IsApproxAdditive (fun S => -f S) 1 := by
  constructor
  · simp [hf.1]
  · intro A B hAB
    rw [show -f A + -f B - -f (A ∪ B) = -(f A + f B - f (A ∪ B)) by ring, abs_neg]
    exact hf.2 A B hAB

omit [DecidableEq U] [Fintype U] in
lemma distToAdditive_neg (f : Finset U → ℝ) :
    distToAdditive (fun S => -f S) = distToAdditive f := by
  classical
  unfold distToAdditive
  have key : ∀ a : U → ℝ, (⨆ S : Finset U, |(fun S => -f S) S - additiveFunction a S|) =
      (⨆ S : Finset U, |f S - additiveFunction (fun i => -a i) S|) := by
    intro a; congr 1; ext S
    simp only [additiveFunction, Finset.sum_neg_distrib]
    rw [sub_neg_eq_add]
    rw [show -f S - ∑ i ∈ S, a i = -(f S + ∑ i ∈ S, a i) by ring, abs_neg]
  have surj : Function.Surjective (fun (a : U → ℝ) (i : U) => -a i) :=
    fun a => ⟨fun i => -a i, by funext i; simp⟩
  conv_lhs => rw [iInf_congr fun a => key a]
  exact (surj.iInf_comp (fun a => ⨆ S : Finset U, |f S - additiveFunction a S|))

/-! ## Case 1 and Case 2 helpers for the spine theorem -/

/-
Helper: the best-approximation property from distToAdditive.
-/
omit [DecidableEq U] [Fintype U] in
lemma best_approx_property [Finite U] (g : Finset U → ℝ) (M : ℝ)
    (_hM_bound : ∀ S : Finset U, |g S| ≤ M)
    (hM_eq : distToAdditive g = M) :
    ∀ a : U → ℝ, ∃ S : Finset U,
      |g S - additiveFunction a S| ≥ M := by
  classical
  let := Fintype.ofFinite U
  -- By definition of infimum, for any a, the supremum of |g S - additiveFunction a S| over all S is
  -- at least M.
  have h_sup_ge_M : ∀ a : U → ℝ, ⨆ S : Finset U, |g S - additiveFunction a S| ≥ M := by
    intro a
    have h_sup_ge_M : M ≤ ⨆ S : Finset U, |g S - additiveFunction a S| := by
      have h_inf :
          M = sInf {x : ℝ | ∃ a : U → ℝ,
            ⨆ S : Finset U, |g S - additiveFunction a S| = x} := by
        exact hM_eq.symm
      exact h_inf.symm ▸
        csInf_le
          ⟨0, by
            rintro x ⟨b, rfl⟩
            exact Real.iSup_nonneg fun _ => abs_nonneg _⟩
          ⟨a, rfl⟩
    exact h_sup_ge_M;
  intro a;
  have h_sup_ge_M : ∃ S : Finset U, ∀ T : Finset U, |g T - additiveFunction a T| ≤ |g S -
    additiveFunction a S| := by
    simpa using Finset.exists_max_image Finset.univ
      (fun S => |g S - additiveFunction a S|)
      ⟨∅, Finset.mem_univ _⟩;
  obtain ⟨ S, hS ⟩ := h_sup_ge_M;
  exact ⟨ S, le_trans ( h_sup_ge_M a ) ( by exact ciSup_le hS ) ⟩

/-! ## Helpers for the spine proofs -/

/-
When M > 0 and a dual certificate exists, both masses are positive.
This follows because if all weights were non-negative (or non-positive),
the zero-marginal property forces all non-empty-set weights to 0,
which means lam(∅) has norm 1, forcing g(∅) = ±M = 0, contradiction.
-/
lemma cert_posMass_pos
    {g : Finset U → ℝ} {M : ℝ} (cert : DualCertificate g M)
    (hg : IsApproxAdditive g 1) (hM : 0 < M)
    (_hM_bound : ∀ S : Finset U, |g S| ≤ M) :
    0 < cert.posMass := by
      -- If posMass = 0, then all lam(S) ≤ 0. By zero_marginals, for each i,
      -- ∑_{S∋i} lam(S) = 0,
      -- with all terms ≤ 0, so each term is 0. So lam(S) = 0 for all nonempty S. Then ∑|lam| =
      -- |lam(∅)| = 1. Since all lam ≤ 0, lam(∅) ≤ 0, so lam(∅) = -1 < 0.
      -- By neg_support, g(∅) = -M.
      -- But g(∅) = 0 (by hg.1), so M = 0, contradicting hM.
      by_contra h_neg
      have h_all_nonpos : ∀ S, cert.lam S ≤ 0 := by
        exact fun S => le_of_not_gt fun hS => h_neg <| lt_of_lt_of_le ( by positivity ) (
          Finset.single_le_sum ( fun x _ => le_max_right ( cert.lam x ) 0 ) ( Finset.mem_univ S ) )
      have h_sum_zero : ∑ S : Finset U, |cert.lam S| = |cert.lam ∅| := by
        have h_sum_zero :
            ∀ i : U, (Finset.univ.filter (fun S => i ∈ S)).sum (fun S => cert.lam S) =
              0 := by
          exact fun i => cert.zero_marginals i;
        have h_lam_zero : ∀ i : U, ∀ S : Finset U, i ∈ S → cert.lam S = 0 := by
          intros i S hiS
          have h_sum_zero_i : ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), cert.lam S = 0 :=
            h_sum_zero i
          have h_lam_zero_i : ∀ S ∈ Finset.univ.filter (fun S => i ∈ S), cert.lam S = 0 := by
            intro T hT
            have hsingle :
                -cert.lam T ≤ ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), -cert.lam S :=
              Finset.single_le_sum (fun x _ => neg_nonneg.mpr (h_all_nonpos x)) hT
            have hle : -cert.lam T ≤ 0 := by
              simpa [Finset.sum_neg_distrib, h_sum_zero_i] using hsingle
            exact le_antisymm (h_all_nonpos T) (neg_nonpos.mp hle)
          exact h_lam_zero_i S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hiS⟩);
        rw [Finset.sum_eq_single ∅] <;>
          simp +contextual only [mem_univ, ne_eq, abs_eq_zero, forall_const,
            not_true_eq_false, false_implies];
        exact fun S hS => h_lam_zero _ _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty hS )
          )
      have h_lam_empty : cert.lam ∅ = -1 := by
        have := cert.norm_one; simp_all +decide [ abs_of_nonpos ];
        linarith
      have h_g_empty : g ∅ = -M := by
        exact cert.neg_support _ ( by linarith )
      have h_contra : M = 0 := by
        linarith [ hg.1 ]
      exact absurd h_contra (by linarith)

lemma cert_negMass_pos
    {g : Finset U → ℝ} {M : ℝ} (cert : DualCertificate g M)
    (hg : IsApproxAdditive g 1) (hM : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M) :
    0 < cert.negMass := by
  simpa [DualCertificate.neg_posMass] using
    cert_posMass_pos (cert.neg) (IsApproxAdditive_neg g hg) hM
      (fun S => by simpa using hM_bound S)

/-
|g(U)| ≤ 1 for a 1-additive function with |g(S)| ≤ M,
given existence of both positive and negative active sets.
-/
lemma g_univ_le_one
    {g : Finset U → ℝ} {M : ℝ} (cert : DualCertificate g M)
    (hg : IsApproxAdditive g 1) (hM : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M) :
    |g Finset.univ| ≤ 1 := by
      -- By assumption, there exist P and N such that g(P) = M and g(N) = -M.
      obtain ⟨P, hP⟩ : ∃ P : Finset U, g P = M := by
        -- Since cert.posMass is positive, there must be at least one set S where cert.lam S is
        -- positive.
        obtain ⟨S, hS⟩ : ∃ S : Finset U, 0 < cert.lam S := by
          exact not_forall_not.mp fun h => by
            have := cert_posMass_pos cert hg hM hM_bound
            simp_all +decide [DualCertificate.posMass]
        exact ⟨ S, cert.pos_support S hS ⟩
      obtain ⟨N, hN⟩ : ∃ N : Finset U, g N = -M := by
        -- By assumption, there exist negative active sets.
        have h_neg_active : ∃ N : Finset U, cert.lam N < 0 := by
          contrapose! hM;
          have := cert.norm_one; simp_all +decide only [ge_iff_le, abs_of_nonneg];
          -- Since $N$ is a negative active set, we have $g(N) = -M$.
          have h_neg_active :
              ∀ i : U, ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), cert.lam S = 0 :=
            by
            exact fun i => cert.zero_marginals i;
          -- Since $N$ is a negative active set, we have $g(N) = -M$. Therefore, $M \leq 0$.
          have h_neg_active : ∀ S : Finset U, S.Nonempty → cert.lam S = 0 := by
            intro S hS_nonempty;
            obtain ⟨i, hi⟩ := hS_nonempty;
            specialize h_neg_active i;
            rw [Finset.sum_eq_zero_iff_of_nonneg] at h_neg_active <;> aesop;
          rw [Finset.sum_eq_single ∅] at this
          · have := cert.pos_support ∅; simp_all +decide
            linarith [ abs_le.mp ( hM_bound ∅ ), hg.1 ];
          · exact fun S _ hS => h_neg_active S ( Finset.nonempty_of_ne_empty hS );
          · simp only [mem_univ, not_true_eq_false, false_implies]
        exact h_neg_active.imp fun N hN => by linarith [ cert.neg_support N hN ];
      -- By assumption, $|g(N) + g(Nᶜ) - g(\text{univ})| \leq 1$ and $|g(P) + g(Pᶜ) -
      -- g(\text{univ})| \leq 1$.
      have h_bound_N : |g N + g Nᶜ - g univ| ≤ 1 := by
        convert hg.2 N Nᶜ ( disjoint_compl_right ) using 1; simp +decide
      have h_bound_P : |g P + g Pᶜ - g univ| ≤ 1 := by
        convert hg.2 P Pᶜ ( disjoint_compl_right ) using 1; aesop;
      exact abs_le.mpr
        ⟨by
          linarith [abs_le.mp h_bound_N, abs_le.mp h_bound_P, abs_le.mp (hM_bound N),
            abs_le.mp (hM_bound Nᶜ), abs_le.mp (hM_bound P), abs_le.mp (hM_bound Pᶜ)],
        by
          linarith [abs_le.mp h_bound_N, abs_le.mp h_bound_P, abs_le.mp (hM_bound N),
            abs_le.mp (hM_bound Nᶜ), abs_le.mp (hM_bound P), abs_le.mp (hM_bound Pᶜ)]⟩

/-
Case 1 of the spine theorem (q ≤ q₀).
Given a dual certificate with q ≤ q₀ ≤ 1/2, using mixed intersection
and two rounds of one-sided recombination, derive M ≤ C₂.
-/
lemma spine_case1
    (g : Finset U → ℝ) (hg : IsApproxAdditive g 1) (M : ℝ) (hM_pos : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M)
    (cert : DualCertificate g M)
    (hq_le : cert.negMass ≤ ↑q₀)
    (hq_half : cert.negMass ≤ 1 / 2)
    -- Pipeline hypotheses (specialized to g and M)
    (hmix : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (D : ℝ) (_ : 0 ≤ D)
      (_ : C.avgDeficit g M ≤ D)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgDeficit g M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2))
    (hrec1 : ∀ (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (C : WeightedCollection U) (_ : ∀ i, C.itemFreq i ≤ (α_v : ℝ))
      (D : ℝ) (_ : 0 ≤ D) (_ : C.avgDeficit g M ≤ D),
      ∃ (C' : WeightedCollection U) (D' : ℝ), 0 ≤ D' ∧
        (∀ i, C'.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'.avgDeficit g M ≤ D' ∧
        (1 - (θ_v : ℝ)) * M ≤ D - (θ_v : ℝ) * D' +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    (hexp1 : StrongExpandersExist α₁ 4 (1 / 3))
    (hexp2 : StrongExpandersExist (3009 / 10000) 4 (4 / 7)) :
    M ≤ ↑C₂ := by
  -- Apply mixed intersection with C₀, t = q, D = q*(1-u), ℓ = 3, τ = (τ₁:ℝ).
  have h_mixed :
      ∃ C₁ : WeightedCollection U,
        (∀ i : U, C₁.itemFreq i ≤
          (1 - τ₁) * cert.negMass ^ 3 + τ₁ * cert.negMass ^ 4) ∧
        C₁.avgDeficit g M ≤
          3 * (cert.negMass * (1 - g Finset.univ)) + 4 +
            τ₁ * (cert.negMass * (1 - g Finset.univ) + 2) := by
    convert hmix ( cert.augPosCollection ) ( cert.negMass ) ( by
      exact cert.negMass_nonneg ) ( by
      exact le_trans hq_le (by simp [q₀]; norm_num) ) ( by
      exact fun i => le_of_eq ( DualCertificate.augPosCollection_itemFreq cert i ) ) ( cert.negMass
        * ( 1 - g Finset.univ ) ) ( by
      exact mul_nonneg (by linarith [cert.negMass_nonneg])
        (by linarith [abs_le.mp (g_univ_le_one cert hg hM_pos hM_bound)])) ( by
      convert DualCertificate.augPosCollection_avgDeficit_le cert hg hM_bound using 1 ) 3 ( by
      norm_num ) ( τ₁ : ℝ ) ( by
      exact_mod_cast τ₁_nonneg ) ( by
      exact_mod_cast τ₁_le_one ) using 1;
    norm_num [ pow_succ ];
  -- Apply hrec1 with α₁, 4, 1/3, hexp1, C₁, D₁.
  obtain ⟨C₂, D', hD'_nonneg, hC₂_freq, hC₂_deficit, hC₂_rec⟩ :=
    hrec1 α₁ 4 (1 / 3) (by norm_num) (by norm_num) hexp1 h_mixed.choose (by
  intro i
  have := h_mixed.choose_spec.left i
  have h_freq_le :
      (1 - τ₁) * cert.negMass ^ 3 + τ₁ * cert.negMass ^ 4 ≤
        (1 - τ₁) * q₀ ^ 3 + τ₁ * q₀ ^ 4 := by
    gcongr;
    · exact sub_nonneg_of_le ( mod_cast τ₁_le_one );
    · exact Finset.sum_nonneg fun _ _ => le_max_right _ _;
    · exact_mod_cast τ₁_nonneg;
    · exact Finset.sum_nonneg fun _ _ => le_max_right _ _;
  exact this.trans
    (h_freq_le.trans (by
      rw [show (α₁ : ℝ) = (1 - τ₁) * q₀ ^ 3 + τ₁ * q₀ ^ 4 by
        exact mod_cast frequency_identity_case1.symm])))
    (3 * (cert.negMass * (1 - g Finset.univ)) + 4 +
      τ₁ * (cert.negMass * (1 - g Finset.univ) + 2)) (by
  have h_negMass_nonneg : 0 ≤ cert.negMass := by
    exact Finset.sum_nonneg fun _ _ => le_max_right _ _;
  have h_g_univ_le_one : |g Finset.univ| ≤ 1 := by
    apply g_univ_le_one cert hg hM_pos hM_bound;
  exact add_nonneg ( add_nonneg ( mul_nonneg zero_le_three ( mul_nonneg h_negMass_nonneg ( by
    linarith [ abs_le.mp h_g_univ_le_one ] ) ) ) zero_le_four ) ( mul_nonneg ( by exact_mod_cast
      τ₁_nonneg ) ( by nlinarith [ abs_le.mp h_g_univ_le_one ] ) )) (by
  exact h_mixed.choose_spec.2);
  -- Apply hrec1 with 3009/10000, 4, 4/7, hexp2, C₂, D'.
  obtain ⟨C₃, D'', hD''_nonneg, hC₃_freq, hC₃_deficit, hC₃_rec⟩ :=
    hrec1 (3009 / 10000) 4 (4 / 7)
      (by norm_num) (by norm_num) hexp2 C₂ (by
  convert hC₂_freq using 1;
  norm_num [ α₁ ]) D' hD'_nonneg hC₂_deficit;
  -- Show that $D₁ \leq 6 * q₀ + 4 + τ₁ * (2 * q₀ + 2)$.
  have hD₁_le : 3 * (cert.negMass * (1 - g Finset.univ)) + 4 + τ₁ * (cert.negMass * (1 - g
    Finset.univ) + 2) ≤ 6 * q₀ + 4 + τ₁ * (2 * q₀ + 2) := by
    have hD₁_le : cert.negMass * (1 - g Finset.univ) ≤ 2 * q₀ := by
      have h_g_univ_le_one : |g Finset.univ| ≤ 1 := by
        apply g_univ_le_one cert hg hM_pos hM_bound;
      nlinarith [ abs_le.mp h_g_univ_le_one, show ( q₀ : ℝ ) ≥ 0 by norm_num [q₀] ];
    nlinarith [ show ( τ₁ : ℝ ) ≥ 0 by exact_mod_cast τ₁_nonneg ];
  norm_num [_root_.KaltonRoberts.C₂] at *
  norm_num [_root_.KaltonRoberts.q₀, _root_.KaltonRoberts.τ₁] at *
  norm_num [_root_.KaltonRoberts.α₁] at *
  linarith

/-
Case 2 of the spine theorem (q₀ < q ≤ 1/2, so p ≤ p₀).
Uses both deficit and surplus augmented collections, mixed intersections,
and two rounds of two-sided recombination.
-/
lemma spine_case2
    (g : Finset U → ℝ) (hg : IsApproxAdditive g 1) (M : ℝ) (hM_pos : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M)
    (cert : DualCertificate g M)
    (hq_gt : ↑q₀ < cert.negMass)
    (hq_half : cert.negMass ≤ 1 / 2)
    -- Pipeline hypotheses (specialized to g and M)
    (hmix : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (D : ℝ) (_ : 0 ≤ D)
      (_ : C.avgDeficit g M ≤ D)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgDeficit g M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2))
    (hmix_sur : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (S_val : ℝ) (_ : 0 ≤ S_val)
      (_ : C.avgSurplus g M ≤ S_val)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgSurplus g M ≤ ℓ * S_val + 2 * ((ℓ : ℝ) - 1) + τ * (S_val + 2))
    (hrec2 : ∀ (C_def C_sur : WeightedCollection U)
      (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (_ : ∀ i, C_def.itemFreq i ≤ (α_v : ℝ))
      (_ : ∀ i, C_sur.itemFreq i ≤ (α_v : ℝ))
      (D S_val : ℝ) (_ : 0 ≤ D) (_ : 0 ≤ S_val)
      (_ : C_def.avgDeficit g M ≤ D)
      (_ : C_sur.avgSurplus g M ≤ S_val),
      ∃ (C'_def C'_sur : WeightedCollection U) (D' S' : ℝ), 0 ≤ D' ∧ 0 ≤ S' ∧
        (∀ i, C'_def.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        (∀ i, C'_sur.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'_def.avgDeficit g M ≤ D' ∧
        C'_sur.avgSurplus g M ≤ S' ∧
        (1 - (θ_v : ℝ)) * M ≤ (D + S_val) / 2 - (θ_v : ℝ) * ((D' + S') / 2) +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    (hexp3 : StrongExpandersExist α₂ 4 (2 / 7))
    (hexp4 : StrongExpandersExist (329 / 1250) 5 (5 / 11)) :
    M ≤ ↑C₂ := by
  -- Apply hmix to the augmented collection to get the deficit.
  obtain ⟨C_def, hC_def⟩ := hmix cert.augPosCollection cert.negMass (by
  grind +suggestions) (by
  linarith) (by
  exact fun i => DualCertificate.augPosCollection_itemFreq cert i |> le_of_eq) (cert.negMass * (1 -
    g Finset.univ)) (by
  exact mul_nonneg ( cert_negMass_pos cert hg hM_pos hM_bound |> le_of_lt ) ( sub_nonneg.2 <|
    le_of_abs_le <| g_univ_le_one cert hg hM_pos hM_bound )) (by
  convert DualCertificate.augPosCollection_avgDeficit_le cert hg hM_bound using 1) 4 (by
  norm_num) 0 (by
  norm_num) (by
  norm_num);
  -- Apply hmix_sur to the augmented collection to get the surplus.
  obtain ⟨C_sur, hC_sur⟩ := hmix_sur cert.augNegCollection cert.posMass (by
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _) (by
  exact cert.posMass_le_one) (by
  exact fun i => DualCertificate.augNegCollection_itemFreq cert i ▸ le_rfl) (cert.posMass * (1 + g
    Finset.univ)) (by
  exact mul_nonneg (le_of_lt (cert_posMass_pos cert hg hM_pos hM_bound))
    (by linarith [abs_le.mp (g_univ_le_one cert hg hM_pos hM_bound)])) (by
  convert DualCertificate.augNegCollection_avgSurplus_le _ _ _ using 1;
  · exact hg;
  · exact hM_bound) 4 (by
  norm_num) τ₂ (by
  exact_mod_cast τ₂_nonneg) (by
  exact_mod_cast τ₂_le_one);
  -- Apply hrec2 to get the two-sided recombination.
  obtain ⟨C'_def, C'_sur, D1, S1, hD1_nn, hS1_nn, hC'_def, hC'_sur, hC'_def_avg, hC'_sur_avg,
    hineq1⟩ := hrec2 C_def C_sur α₂ 4 (2 / 7) (by
  norm_num) (by
  norm_num) hexp3 (by
  intro i
  specialize hC_def
  have hC_def_i : C_def.itemFreq i ≤ cert.negMass ^ 4 := by
    simpa using hC_def.1 i
  have hC_def_i_le : cert.negMass ^ 4 ≤ α₂ := by
    exact le_trans
      (pow_le_pow_left₀
        (by
          linarith [show (0 : ℝ) ≤ cert.negMass by
            exact le_trans (by norm_num [q₀]) hq_gt.le])
        hq_half 4)
      (by norm_num [α₂]);
  exact le_trans hC_def_i hC_def_i_le) (by
  intro i
  have hp_le_p0 : cert.posMass ≤ (↑p₀ : ℝ) := by
    have h1 := cert.posMass_add_negMass
    have h2 : (↑p₀ : ℝ) = 1 - (↑q₀ : ℝ) := by exact_mod_cast p₀_eq
    linarith
  have hp_nn : 0 ≤ cert.posMass := cert.posMass_nonneg
  have h_freq_sur : C_sur.itemFreq i ≤ (1 - τ₂) * p₀^4 + τ₂ * p₀^5 := by
    refine le_trans (hC_sur.1 i) ?_
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_nn hp_le_p0 4)
      linarith [show (τ₂ : ℝ) ≤ 1 from by exact_mod_cast τ₂_le_one]
    · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_nn hp_le_p0 5)
      exact_mod_cast τ₂_nonneg
  exact h_freq_sur.trans
    (by
      rw [show (α₂ : ℝ) = (1 - τ₂) * p₀ ^ 4 + τ₂ * p₀ ^ 5 by
        exact mod_cast frequency_identity_case2.symm]))
    (4 * (cert.negMass * (1 - g Finset.univ)) + 2 * (4 - 1))
    (4 * (cert.posMass * (1 + g Finset.univ)) + 2 * (4 - 1) +
      τ₂ * (cert.posMass * (1 + g Finset.univ) + 2)) (by
  have := g_univ_le_one cert hg hM_pos hM_bound;
  nlinarith [abs_le.mp this,
    show (0 : ℝ) ≤ cert.negMass by
      exact le_of_lt (cert_negMass_pos cert hg hM_pos hM_bound)]) (by
  have h_pos : 0 ≤ cert.posMass := by
    exact Finset.sum_nonneg fun _ _ => le_max_right _ _
  have h_pos_g : -1 ≤ g univ := by
    exact neg_le_of_abs_le ( g_univ_le_one cert hg hM_pos hM_bound )
  have h_pos_g' : g univ ≤ 1 := by
    linarith [ abs_le.mp ( g_univ_le_one cert hg hM_pos hM_bound ) ]
  norm_num at *;
  exact add_nonneg
    (add_nonneg (mul_nonneg zero_le_four (mul_nonneg h_pos (by linarith))) (by norm_num))
    (mul_nonneg (by exact_mod_cast τ₂_nonneg)
      (add_nonneg (mul_nonneg h_pos (by linarith)) (by norm_num)))) (by
  exact hC_def.2.trans ( by norm_num )) (by
  exact hC_sur.2.trans ( by norm_num ));
  -- Apply hrec2 again to get the final recombination.
  obtain ⟨C''_def, C''_sur, D2, S2, hD2_nn, hS2_nn, hC''_def, hC''_sur,
    hC''_def_avg, hC''_sur_avg, hineq2⟩ := hrec2 C'_def C'_sur (329 / 1250) 5 (5 / 11) (by
  norm_num) (by
  norm_num) hexp4 (by
  convert hC'_def using 1;
  norm_num [ α₂ ]) (by
  convert hC'_sur using 1;
  norm_num [ α₂ ]) D1 S1 (by
  exact hD1_nn) (by
  exact hS1_nn) (by
  exact hC'_def_avg) (by
  exact hC'_sur_avg);
  -- Set Y1 = (D1 + S1) / 2 and derive the two bounds for case2_bound
  set Y1 := (D1 + S1) / 2 with hY1_def
  -- From hineq2: (6/11)*M ≤ Y1 - (5/11)*(D2+S2)/2 + 9 - 5/11
  -- Since D2 ≥ 0 and S2 ≥ 0: M ≤ 47/3 + (11/6)*Y1
  have hY1_nn : 0 ≤ Y1 := by linarith
  norm_num [ show cert.posMass = 1 - cert.negMass by linarith [ cert.posMass_add_negMass ] ] at *;
  unfold τ₂ at *;
  unfold C₂ p₀ α₂ at *;
  unfold q₀ at *;
  have := g_univ_le_one cert hg hM_pos hM_bound;
  norm_num [ abs_le ] at *;
  nlinarith [ mul_le_mul_of_nonneg_left hq_half hY1_nn ]

end KaltonRoberts
