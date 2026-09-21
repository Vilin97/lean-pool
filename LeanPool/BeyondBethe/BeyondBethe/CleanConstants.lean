/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.CleanGain
import Mathlib.Tactic

/-! # Clean Constants -/

open scoped BigOperators Topology

namespace BeyondBethe

/-- The first line of paper (61), with `negMulLog` encoding the convention
`0 log 0 = 0`. -/
noncomputable def cleanCoreFunction (κ ρ : ℝ) : ℝ :=
  (1 - ρ) * Real.log ((2 * (Real.exp (-κ)) ^ 2) / (1 - ρ)) +
    ρ * Real.log (Real.exp (-κ)) - Real.negMulLog ρ - ρ

/-- Separate the core contribution in (61) from its entropy-regularization
loss. -/
theorem cleanGainLowerBound_eq_core_sub_entropy
    {ι : Type*} [Fintype ι]
    {κ τ ρ : ℝ} {α : ι → ℝ} :
    cleanGainLowerBound κ τ ρ α = cleanCoreFunction κ ρ -
      τ * (-(∑ l, α l * Real.log (α l)) + ρ * Real.log 2) := by
  rw [cleanGainLowerBound, cleanCoreFunction, Real.negMulLog_def]
  ring

/-- If the core term is above `log 2 / 2` and the entropy bracket is below
`4 ell`, the paper's choice `tau = xi / (4 ell)` loses less than `xi`. -/
theorem cleanGainLowerBound_gt_of_core_and_entropy
    {ι : Type*} [Fintype ι]
    {κ τ ρ ξ ell : ℝ} {α : ι → ℝ}
    (hξ : 0 < ξ) (hell : 0 < ell)
    (hτ : τ = ξ / (4 * ell))
    (hcore : Real.log 2 / 2 < cleanCoreFunction κ ρ)
    (hentropy : -(∑ l, α l * Real.log (α l)) + ρ * Real.log 2 <
      4 * ell) :
    Real.log 2 / 2 - ξ < cleanGainLowerBound κ τ ρ α := by
  let B := -(∑ l, α l * Real.log (α l)) + ρ * Real.log 2
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hloss : τ * B < ξ := by
    calc
      τ * B < τ * (4 * ell) := mul_lt_mul_of_pos_left hentropy hτpos
      _ = ξ := by rw [hτ]; field_simp
  rw [cleanGainLowerBound_eq_core_sub_entropy]
  dsimp only [B] at hloss
  linarith

/-- The outside entropy in (62) is at most `rho log(n/rho)`.  The subtype
cardinality argument is explicit: outside columns inject into all `n`
columns. -/
theorem outsidePairEntropy_le
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    {r s a b : Fin n}
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b) :
    -(∑ l : OutsideColumn a b,
        pairAlpha X r s l.1 * Real.log (pairAlpha X r s l.1)) ≤
      outsideMassTwo (pairAlpha X r s) a b *
        Real.log (n / outsideMassTwo (pairAlpha X r s) a b) := by
  let ρ := outsideMassTwo (pairAlpha X r s) a b
  let αo : OutsideColumn a b → ℝ := fun l ↦ pairAlpha X r s l.1
  have hne : ¬ IsEmpty (OutsideColumn a b) := by
    intro hempty
    letI : IsEmpty (OutsideColumn a b) := hempty
    have hsum := sum_outsideColumn_eq_outsideMassTwo
      (pairAlpha X r s) a b
    have hzero : (∑ l : OutsideColumn a b, pairAlpha X r s l.1) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      exact isEmptyElim l
    linarith [hsum, hzero]
  letI : Nonempty (OutsideColumn a b) := not_isEmpty_iff.mp hne
  have hsum : ∑ l, αo l = ρ := by
    dsimp only [αo, ρ]
    exact sum_outsideColumn_eq_outsideMassTwo _ _ _
  have hα : ∀ l, 0 ≤ αo l := fun l ↦ pairAlpha_nonneg hX r s l.1
  have hent := shannonEntropy_of_mass_le hα (show 0 < ρ from hρ) hsum
  have hcard : Fintype.card (OutsideColumn a b) ≤ n := by
    simpa using Fintype.card_le_of_injective
      (fun l : OutsideColumn a b ↦ l.1) Subtype.val_injective
  have hcardpos : 0 < (Fintype.card (OutsideColumn a b) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hquot : (Fintype.card (OutsideColumn a b) : ℝ) / ρ ≤ n / ρ := by
    apply div_le_div_of_nonneg_right _ hρ.le
    exact_mod_cast hcard
  have hlog : Real.log ((Fintype.card (OutsideColumn a b) : ℝ) / ρ) ≤
      Real.log (n / ρ) :=
    Real.log_le_log (div_pos hcardpos hρ) hquot
  have hfinal := hent.trans (mul_le_mul_of_nonneg_left hlog hρ.le)
  dsimp only [αo, ρ] at hfinal ⊢
  have heq :
      -(∑ l : OutsideColumn a b,
          pairAlpha X r s l.1 * Real.log (pairAlpha X r s l.1)) =
        shannonEntropy (fun l : OutsideColumn a b ↦ pairAlpha X r s l.1) := by
    rw [shannonEntropy, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [Real.negMulLog_def]
    ring
  rw [heq]
  exact hfinal

/-- A deliberately slack version of the entropy estimate below (61).
The elementary bound `negMulLog rho <= 1-rho` is already enough once
`rho < 1/10`; the sharper `1/e` in the paper is not needed here. -/
theorem outsideEntropyBracket_lt_four_scale
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    {r s a b : Fin n}
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρsmall : outsideMassTwo (pairAlpha X r s) a b < 1 / 10)
    {ell : ℝ} (hell : 1 ≤ ell)
    (hlogn : Real.log n ≤ ell * Real.log 2) :
    -(∑ l : OutsideColumn a b,
        pairAlpha X r s l.1 * Real.log (pairAlpha X r s l.1)) +
        outsideMassTwo (pairAlpha X r s) a b * Real.log 2 <
      4 * ell := by
  let ρ := outsideMassTwo (pairAlpha X r s) a b
  have hent := outsidePairEntropy_le hX hρ
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n from Fin.pos_iff_nonempty.mpr ⟨r⟩)
  have hlogdiv : Real.log ((n : ℝ) / ρ) =
      Real.log n - Real.log ρ := Real.log_div hnpos.ne' hρ.ne'
  have hnml : Real.negMulLog ρ ≤ 1 - ρ :=
    Real.negMulLog_le_one_sub_self hρ.le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hrlog : ρ * Real.log 2 < 1 / 10 := by
    have h := mul_lt_mul_of_pos_right hρsmall hlog2pos
    nlinarith
  have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
  have hmain : ρ * (ell * Real.log 2) < ell / 10 := by
    have h := mul_lt_mul_of_pos_left hrlog hellpos
    nlinarith
  have hfirst :
      -(∑ l : OutsideColumn a b,
          pairAlpha X r s l.1 * Real.log (pairAlpha X r s l.1)) ≤
        ρ * (ell * Real.log 2) + Real.negMulLog ρ := by
    calc
      -(∑ l : OutsideColumn a b,
          pairAlpha X r s l.1 * Real.log (pairAlpha X r s l.1)) ≤
          ρ * Real.log ((n : ℝ) / ρ) := hent
      _ = ρ * Real.log n + Real.negMulLog ρ := by
        rw [hlogdiv, Real.negMulLog_def]
        ring
      _ ≤ ρ * (ell * Real.log 2) + Real.negMulLog ρ := by
        gcongr
  dsimp only [ρ] at hfirst hnml hmain hrlog hρ hρsmall ⊢
  linarith

theorem cleanCoreFunction_continuousAt_zero :
    ContinuousAt (fun p : ℝ × ℝ => cleanCoreFunction p.1 p.2) (0, 0) := by
  unfold cleanCoreFunction
  have hfst : ContinuousAt (fun p : ℝ × ℝ => p.1) (0, 0) := continuousAt_fst
  have hsnd : ContinuousAt (fun p : ℝ × ℝ => p.2) (0, 0) := continuousAt_snd
  have hden : ContinuousAt (fun p : ℝ × ℝ => 1 - p.2) (0, 0) :=
    continuousAt_const.sub hsnd
  have hexp : ContinuousAt (fun p : ℝ × ℝ => Real.exp (-p.1)) (0, 0) :=
    Real.continuous_exp.continuousAt.comp_of_eq hfst.neg rfl
  have hnum : ContinuousAt
      (fun p : ℝ × ℝ => 2 * Real.exp (-p.1) ^ 2) (0, 0) :=
    continuousAt_const.mul (hexp.pow 2)
  have hfrac := hnum.div hden (by norm_num)
  have hlogfrac := hfrac.log (by norm_num)
  have hlogexp := hexp.log (by norm_num)
  have hnml : ContinuousAt (fun p : ℝ × ℝ => Real.negMulLog p.2) (0, 0) :=
    Real.continuous_negMulLog.continuousAt.comp_of_eq hsnd rfl
  convert ((hden.mul hlogfrac).add (hsnd.mul hlogexp)).sub hnml |>.sub hsnd using 1 <;>
    ext p <;> rfl

/-- Uniform continuity at `(kappa,rho)=(0,0)` makes the core contribution
strictly larger than `log 2 / 2` throughout a small rectangle. -/
theorem cleanCore_uniform_rectangle : ∃ ε : ℝ, 0 < ε ∧ ∀ κ ρ : ℝ,
    |κ| < ε → |ρ| < ε → Real.log 2 / 2 < cleanCoreFunction κ ρ := by
  have hcont := cleanCoreFunction_continuousAt_zero
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hval : Real.log 2 / 2 < cleanCoreFunction 0 0 := by
    simp [cleanCoreFunction]
    linarith
  have hevent : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      Real.log 2 / 2 < cleanCoreFunction p.1 p.2 :=
    hcont.eventually (isOpen_Ioi.mem_nhds hval)
  change {p : ℝ × ℝ |
    Real.log 2 / 2 < cleanCoreFunction p.1 p.2} ∈ nhds (0, 0) at hevent
  rw [Metric.mem_nhds_iff] at hevent
  rcases hevent with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, fun κ ρ hκ hρ => ?_⟩
  change (κ, ρ) ∈ {p : ℝ × ℝ |
    Real.log 2 / 2 < cleanCoreFunction p.1 p.2}
  apply hball
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero,
    max_lt_iff]
  exact ⟨hκ, hρ⟩

/-- The upper envelope `bar rho_kappa` from paper (51). -/
noncomputable def leakageEnvelope (κ : ℝ) : ℝ :=
  2 * (Real.exp κ - 1)

/-- A positive rational local-cost threshold for which every admissible
leakage lies in the uniform core rectangle and is below `1/10`. -/
theorem exists_rational_core_cost :
    ∃ κq : ℚ, 0 < κq ∧ leakageEnvelope (κq : ℝ) < 1 / 10 ∧
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ leakageEnvelope (κq : ℝ) →
        Real.log 2 / 2 < cleanCoreFunction (κq : ℝ) ρ := by
  rcases cleanCore_uniform_rectangle with ⟨ε, hε, hcore⟩
  let η : ℝ := min ε (1 / 10)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hbarcont : ContinuousAt leakageEnvelope 0 := by
    unfold leakageEnvelope
    fun_prop
  have hbarzero : leakageEnvelope 0 = 0 := by simp [leakageEnvelope]
  have hevent : ∀ᶠ κ : ℝ in nhds 0,
      -η < leakageEnvelope κ ∧ leakageEnvelope κ < η := by
    exact hbarcont.eventually (show ∀ᶠ y : ℝ in nhds (leakageEnvelope 0),
      -η < y ∧ y < η by
        rw [hbarzero]
        exact isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  change {κ : ℝ |
    -η < leakageEnvelope κ ∧ leakageEnvelope κ < η} ∈ nhds 0 at hevent
  rw [Metric.mem_nhds_iff] at hevent
  rcases hevent with ⟨δ, hδ, hball⟩
  obtain ⟨κq : ℚ, hκqpos, hκqsmall⟩ :=
    exists_rat_btwn (show (0 : ℝ) < min ε δ from lt_min hε hδ)
  have hκcastpos : 0 < (κq : ℝ) := hκqpos
  have hκeps : (κq : ℝ) < ε := hκqsmall.trans_le (min_le_left _ _)
  have hκδ : (κq : ℝ) < δ := hκqsmall.trans_le (min_le_right _ _)
  have hbarinterval : -η < leakageEnvelope (κq : ℝ) ∧
      leakageEnvelope (κq : ℝ) < η := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκcastpos]
    exact hκδ
  refine ⟨κq, ?_, ?_, ?_⟩
  · exact_mod_cast hκcastpos
  · exact hbarinterval.2.trans_le (min_le_right _ _)
  · intro ρ hρ hρbar
    have hρeps : ρ < ε :=
      hρbar.trans_lt (hbarinterval.2.trans_le (min_le_left _ _))
    exact hcore (κq : ℝ) ρ
      (by simpa [abs_of_pos hκcastpos] using hκeps)
      (by simpa [abs_of_nonneg hρ] using hρeps)

/-- The analytic conclusion of the clean-pair lemma, after a clean component
has supplied two distinct rows and two distinct core columns. -/
def CleanPairGainGuarantee (κ₀ ξ₀ γ₀ : ℝ) : Prop :=
  ∀ {n : ℕ} {ell ξ τ : ℝ}
    {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ},
    1 ≤ ell →
    Real.log n ≤ ell * Real.log 2 →
    0 < ξ → ξ ≤ ξ₀ → τ = ξ / (4 * ell) →
    (∀ i j, 0 < A i j) →
    IsDoublyStochastic X →
    (∀ i, IsInteriorProbabilityVector (X i)) →
    (∀ i, 0 < rscale i) → (∀ j, 0 < cscale j) →
    HasMultiplicativeKKT τ A X rscale cscale →
    ∀ {r s a b : Fin n}, r ≠ s → a ≠ b →
      fourCoreTransferCost τ X r s a b ≤ κ₀ →
      γ₀ ≤ Real.log (pairGain A X r s)

/-- Paper Lemma 19: rational absolute constants exist for which every clean
pair of small local transfer cost has a uniform positive logarithmic gain.
The graph-theoretic word "clean" is used earlier in the paper only to supply
the two distinct rows and columns appearing in this analytic statement. -/
theorem exists_rational_cleanPairGain_constants :
    ∃ κ₀ ξ₀ γ₀ : ℚ, 0 < κ₀ ∧ 0 < ξ₀ ∧ 0 < γ₀ ∧
      CleanPairGainGuarantee (κ₀ : ℝ) (ξ₀ : ℝ) (γ₀ : ℝ) := by
  rcases exists_rational_core_cost with
    ⟨κ₀, hκ₀pos, hbarSmall, hcore⟩
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨ξ₀ : ℚ, hξ₀posR, hξ₀small⟩ :=
    exists_rat_btwn (show (0 : ℝ) < Real.log 2 / 4 by positivity)
  have hgapPos : 0 < Real.log 2 / 2 - (ξ₀ : ℝ) := by
    linarith
  obtain ⟨γ₀ : ℚ, hγ₀posR, hγ₀gap⟩ := exists_rat_btwn hgapPos
  refine ⟨κ₀, ξ₀, γ₀, hκ₀pos, ?_, ?_, ?_⟩
  · exact_mod_cast hξ₀posR
  · exact_mod_cast hγ₀posR
  · intro n ell ξ τ A X rscale cscale hell hlogn hξ hξ₀ hτ
      hApos hX hXint hrscale hcscale hKKT r s a b hrs hab hcost
    have hellpos : 0 < ell := lt_of_lt_of_le (by norm_num) hell
    have hτpos : 0 < τ := by rw [hτ]; positivity
    have hκ₀posR : 0 < (κ₀ : ℝ) := by exact_mod_cast hκ₀pos
    let ρ := outsideMassTwo (pairAlpha X r s) a b
    have hρnonneg : 0 ≤ ρ := by
      dsimp only [ρ, outsideMassTwo]
      exact Finset.sum_nonneg fun j _ ↦ pairAlpha_nonneg hX r s j
    by_cases hρzero : ρ = 0
    · have hbarNonneg : 0 ≤ leakageEnvelope (κ₀ : ℝ) := by
        rw [leakageEnvelope]
        have hexp : 1 ≤ Real.exp (κ₀ : ℝ) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr hκ₀posR.le
        linarith
      have hcoreZero := hcore 0 le_rfl hbarNonneg
      have hcoreLog : Real.log 2 / 2 <
          Real.log (2 * (Real.exp (-(κ₀ : ℝ))) ^ 2) := by
        simpa [cleanCoreFunction] using hcoreZero
      have hgain := log_pairGain_ge_core_of_zeroLeakage
        hτpos.le hApos hX hXint hrscale hcscale hKKT hrs hab hcost
        (by simpa only [ρ] using hρzero)
      have hγcore : (γ₀ : ℝ) < Real.log 2 / 2 := by linarith
      exact le_of_lt (hγcore.trans (hcoreLog.trans_le hgain))
    · have hρpos : 0 < ρ := lt_of_le_of_ne hρnonneg (Ne.symm hρzero)
      have hρbar : ρ ≤ leakageEnvelope (κ₀ : ℝ) := by
        dsimp only [ρ, leakageEnvelope]
        exact pairOutsideMass_le_exp hτpos.le hκ₀posR.le hXint hab hcost
      have hρsmall : ρ < 1 / 10 := hρbar.trans_lt hbarSmall
      have hρone : ρ < 1 := hρsmall.trans (by norm_num)
      have hcoreRho := hcore ρ hρnonneg hρbar
      have hentropy := outsideEntropyBracket_lt_four_scale hX hρpos
        hρsmall hell hlogn
      have hclean := cleanGainLowerBound_gt_of_core_and_entropy
        hξ hellpos hτ hcoreRho hentropy
      have hgain := log_pairGain_ge_cleanGainLowerBound_of_positiveLeakage
        hτpos.le hApos hX hXint hrscale hcscale hKKT hrs hab hcost
        hρpos hρone
      have hγlower : (γ₀ : ℝ) < Real.log 2 / 2 - ξ := by
        linarith
      exact le_of_lt (hγlower.trans (hclean.trans_le hgain))

end BeyondBethe
