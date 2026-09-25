/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.TightSchedule
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpRoundAssembly

/-!
# Near-regular hypergraph nibble

A finite, ceiling-carrying nibble theorem for near-regular uniform hypergraphs.
The module deliberately stops before application-specific graph-transfer assemblies.
-/

@[expose] public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal
/-- **The one-round covering oracle from the sharp round.**  Running the tight-band schedule
`LeanPool.AsymptoticTrianglePacking.Internal.TightParams r β` gives a one-round oracle for every
majority near-regular input with a global degree ceiling and low codegree. -/
theorem roundOracleExistsCeil_holds : RoundOracleExistsCeil := by
  classical
  intro r hr β hβ
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1` is vacuous: more than a `β`-fraction can never be uncovered
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, le_rfl, ?_⟩
    intro V _ _ H d _ _ _ _ _ _
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro H' S _ hlt
    exfalso
    have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨Pm⟩ := exists_tightParams r hr hβ hβ1
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨D₀, hD₀, c₀, hc₀, hround⟩ :=
    sharpRoundHyp_of_two_gamma_le_eps r hr Pm.gam Pm.eps Pm.exc (β / 2) Pm.gam_pos Pm.gam_le
      Pm.eps_le Pm.two_gam_le_eps Pm.exc_pos Pm.exc_le (by linarith) (by linarith)
  -- the parameters of the interface
  obtain ⟨mu, hmudef⟩ : ∃ m : ℝ,
      m = min Pm.wid (min (c₀ * Pm.lomin) (min (1 / (2 * (D₀ + 1))) (1 / 2))) := ⟨_, rfl⟩
  have hD1 : (0 : ℝ) < 2 * (D₀ + 1) := by linarith
  have hmupos : 0 < mu := by
    rw [hmudef]
    exact lt_min Pm.wid_pos (lt_min (mul_pos hc₀ Pm.lomin_pos)
      (lt_min (div_pos one_pos hD1) (by norm_num)))
  have hmu_wid : mu ≤ Pm.wid := by rw [hmudef]; exact min_le_left _ _
  have hmu_c0 : mu ≤ c₀ * Pm.lomin := by
    rw [hmudef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmu_D : mu ≤ 1 / (2 * (D₀ + 1)) := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmu_half : mu ≤ 1 / 2 := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcpos : (0 : ℝ) < Pm.gam / (16 * r) := div_pos Pm.gam_pos (by linarith)
  have hcle : Pm.gam / (16 * r) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [Pm.gam_le]
  refine ⟨mu, hmupos, Pm.eta, Pm.eta_pos, max 1 (D₀ / Pm.lomin),
    lt_of_lt_of_le one_pos (le_max_left _ _), Pm.gam / (16 * r), hcpos, hcle, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_max_left _ _) hd0
  have hDlo : D₀ ≤ d * Pm.lomin := by
    have h := le_trans (le_max_right (1 : ℝ) (D₀ / Pm.lomin)) hd0
    rw [div_le_iff₀ Pm.lomin_pos] at h
    exact h
  have hcodsmall : mu * d ≤ c₀ * (d * Pm.lomin) := by
    linarith only [mul_le_mul_of_nonneg_right hmu_c0 (show (0 : ℝ) ≤ d by linarith only [hd1])]
  -- the vertex count is at least the round's degree threshold
  have hNbig : 0 < (Fintype.card V : ℝ) → D₀ ≤ (Fintype.card V : ℝ) := by
    intro hNpos
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    have hetahalf : Pm.eta ≤ β / 2 := le_trans Pm.sig_init (Pm.sig_le 0 (Nat.zero_le _))
    have hExcnn : (0 : ℝ) ≤ (Exc.card : ℝ) := Nat.cast_nonneg _
    have hExclt : (Exc.card : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Exc := by
      by_contra hcon
      push Not at hcon
      have : Exc = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [this, Finset.card_univ] at hExclt
      exact absurd hExclt (lt_irrefl _)
    have hdeg := (hExcdeg v hv).1
    have hcg := card_ge_of_codegree huni hr1 hcodeg v
    have hdegnn : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
    by_contra hcon
    push Not at hcon
    have hmu_D' : mu * (2 * (D₀ + 1)) ≤ 1 := by
      rw [le_div_iff₀ hD1] at hmu_D
      linarith
    have hstep1 : d / 2 ≤ (degree H v : ℝ) := by nlinarith
    have hr1R : (1 : ℝ) ≤ (r : ℝ) - 1 := by linarith
    have hstep2 : (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hr1R hdegnn]
    have hstep3 : d / 2 ≤ ((Fintype.card V : ℝ) - 1) * (mu * d) := by linarith
    have hstep4 : (1 : ℝ) / 2 ≤ ((Fintype.card V : ℝ) - 1) * mu := by
      have hmul : d * (1 / 2) ≤ d * (((Fintype.card V : ℝ) - 1) * mu) := by
        linarith only [hstep3]
      exact le_of_mul_le_mul_left hmul hd
    nlinarith only [hstep4, hmu_D', hcon, hmupos,
      mul_pos hmupos (show (0 : ℝ) < D₀ - (Fintype.card V : ℝ) by linarith)]
  refine hasRoundOracle_of_scheduled_invariant H hcpos.le hcle Pm.T Pm.decay
    (fun j H' S => (∀ e ∈ H', Disjoint e S) ∧
      ∃ (K : Finset (Finset V)) (E : Finset V), K ⊆ H' ∧ IsUniform K r ∧
        (∀ e ∈ K, Disjoint e S) ∧
        (∀ v : V, (degree K v : ℝ) ≤ d * Pm.hi j) ∧
        (∀ v : V, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ)) ∧
        (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ mu * d) ∧
        (E.card : ℝ) ≤ Pm.sig j * (Fintype.card V : ℝ))
    ?_ (fun j H' S hP => hP.1) ?_
  · -- initialisation
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    refine ⟨fun e _ => Finset.disjoint_empty_right e, H, Exc, Finset.Subset.refl _, huni,
      fun e _ => Finset.disjoint_empty_right e, ?_, ?_, hcodeg, ?_⟩
    · intro v
      have h1 : (1 : ℝ) + mu ≤ Pm.hi 0 := by linarith [Pm.init_hi]
      have := hceil v
      nlinarith
    · intro v _ hvE
      have h1 : Pm.lo 0 ≤ 1 - mu := by linarith [Pm.init_lo]
      have := (hExcdeg v hvE).1
      nlinarith
    · have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      exact le_trans hExc (mul_le_mul_of_nonneg_right Pm.sig_init hNnn)
  · -- one round of the schedule
    rintro j hj H' S ⟨hH'disj, K, E, hKH', huniK, hKdisj, hhi, hlo, hcodK, hE⟩ hlt
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨R', hR'K, hcov, K', E', hK'res, huniK', hK'disj, hhi', hlo', hcodK', hE'⟩ :=
      tight_round_step hr Pm hc₀.le hround hd (mul_nonneg hmupos.le hd.le) hDlo hcodsmall
        (hNbig hNpos) hj huniK hKdisj hhi hlo hcodK hE hlt
    refine ⟨R', Finset.Subset.trans hR'K hKH', ⟨?_, K', E', ?_, huniK', hK'disj, hhi', hlo',
      hcodK', hE'⟩, hcov⟩
    · intro e he
      rw [Finset.disjoint_union_right]
      exact ⟨hH'disj e (Hypergraph.residual_subset H' R' he),
        Hypergraph.residual_disjoint_covered he⟩
    · exact Finset.Subset.trans hK'res (Finset.filter_subset_filter _ hKH')

/-- **`NibbleTheoremMostCeil`, unconditionally.** -/
theorem nibbleTheoremMostCeil_holds : NibbleTheoremMostCeil :=
  nibbleTheoremMostCeil_of_adaptiveOracleCeil
    (adaptiveOracleExistsCeil_of_roundOracleCeil roundOracleExistsCeil_holds)

/-- **`NibbleTheoremMostCeilSized`, unconditionally.**  The size hypothesis
`|V| ≤ K d²` is not needed by the tight-band route, so it is simply discarded. -/
theorem nibbleTheoremMostCeilSized_holds : NibbleTheoremMostCeilSized := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  exact ⟨μ, hμ, η, hη, d₀, hd₀, 1, one_pos,
    fun H d hd hd0 huni hreg hcod hceil _ => hmain H d hd hd0 huni hreg hcod hceil⟩

/-- **`NibbleTheorem`, unconditionally.** -/
theorem nibbleTheorem_holds : NibbleTheorem :=
  nibbleTheoremMostCeil_holds.nibbleTheorem

end LeanPool.AsymptoticTrianglePacking.Internal

