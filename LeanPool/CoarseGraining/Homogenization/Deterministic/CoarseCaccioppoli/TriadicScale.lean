/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Height

/-! # Triadic Scale -/

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoliRadiusSequence_mem_Icc (n : ℕ) :
    (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n ∧
      coarseCaccioppoliRadiusSequence n ≤ 1 := by
  unfold coarseCaccioppoliRadiusSequence
  constructor
  · have hpos : 0 < 3 * (n + 1 : ℝ) := by positivity
    field_simp [hpos.ne']
    nlinarith
  · have hfrac_nonneg : 0 ≤ 2 / (3 * (n + 1 : ℝ)) := by positivity
    nlinarith

theorem coarseCaccioppoliRadiusSequence_lt_one (n : ℕ) :
    coarseCaccioppoliRadiusSequence n < 1 := by
  unfold coarseCaccioppoliRadiusSequence
  have hfrac_pos : 0 < 2 / (3 * (n + 1 : ℝ)) := by positivity
  linarith

theorem coarseCaccioppoliRadiusSequence_strictMono :
    StrictMono coarseCaccioppoliRadiusSequence := by
  intro m n hmn
  unfold coarseCaccioppoliRadiusSequence
  have hm3 : (0 : ℝ) < 3 * (m + 1 : ℝ) := by positivity
  have hlt3 : 3 * (m + 1 : ℝ) < 3 * (n + 1 : ℝ) := by
    have hlt : (m : ℝ) + 1 < n + 1 := by
      exact_mod_cast Nat.succ_lt_succ hmn
    nlinarith
  have hInv : (3 * (n + 1 : ℝ))⁻¹ < (3 * (m + 1 : ℝ))⁻¹ := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hm3 hlt3)
  have hFrac : 2 / (3 * (n + 1 : ℝ)) < 2 / (3 * (m + 1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_lt_mul_of_pos_left hInv (show (0 : ℝ) < 2 by positivity))
  nlinarith

theorem coarseCaccioppoliRadiusSequence_succ_sub (n : ℕ) :
    coarseCaccioppoliRadiusSequence (n + 1) - coarseCaccioppoliRadiusSequence n =
      2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ)) := by
  unfold coarseCaccioppoliRadiusSequence
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n + 2 : ℝ) := by
    have hstep : (((n + 1 : ℕ) : ℝ) + 1) = ((((n + 1) + 1 : ℕ) : ℝ)) := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_add]
    calc
      (((n + 1 : ℕ) : ℝ) + 1) = ((((n + 1) + 1 : ℕ) : ℝ)) := hstep
      _ = (n + 2 : ℝ) := by
        exact_mod_cast (by omega : (n + 1) + 1 = n + 2)
  rw [hcast]
  calc
    (1 - 2 / (3 * (n + 2 : ℝ))) - (1 - 2 / (3 * (n + 1 : ℝ)))
        = 2 / (3 * (n + 1 : ℝ)) - 2 / (3 * (n + 2 : ℝ)) := by ring
    _ = 2 / (3 * (((n + 1) * (n + 2) : ℕ) : ℝ)) := by
          field_simp
          ring_nf
          norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

theorem coarseCaccioppoliRadiusSequence_gap_pos (n : ℕ) :
    0 < coarseCaccioppoliRadiusSequence (n + 1) - coarseCaccioppoliRadiusSequence n := by
  rw [coarseCaccioppoliRadiusSequence_succ_sub]
  positivity

theorem coarseCaccioppoliRadiusIterationTerm_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ coarseCaccioppoliRadiusIterationTerm β n := by
  unfold coarseCaccioppoliRadiusIterationTerm
  refine mul_nonneg ?_ ?_
  · positivity
  · exact Real.rpow_nonneg (le_of_lt (coarseCaccioppoliRadiusSequence_gap_pos n)) _

theorem coarseCaccioppoliGapInv_nonneg {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ < ρ₂) :
    0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  unfold coarseCaccioppoliGapInv
  exact Real.rpow_nonneg (sub_nonneg.mpr hρ.le) _

@[simp] theorem coarseCaccioppoliGapInv_eq_inv (ρ₁ ρ₂ : ℝ) :
    coarseCaccioppoliGapInv ρ₁ ρ₂ = (ρ₂ - ρ₁)⁻¹ := by
  unfold coarseCaccioppoliGapInv
  simpa using (Real.rpow_neg_one (ρ₂ - ρ₁))

theorem coarseCaccioppoli_gap_le_two_thirds {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (_hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    ρ₂ - ρ₁ ≤ (2 / 3 : ℝ) := by
  linarith

/-- There is always a triadic scale in the note's admissible gap window. -/
theorem exists_coarseCaccioppoliTriadicGapScaleChoice {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ := by
  let gap : ℝ := ρ₂ - ρ₁
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hlt
  have hgap_le : gap ≤ (2 / 3 : ℝ) := by
    dsimp [gap]
    exact coarseCaccioppoli_gap_le_two_thirds hρ₁ hlt hρ₂
  have hA_ge_one : (1 : ℝ) ≤ 27 / gap := by
    rw [le_div_iff₀ hgap_pos]
    nlinarith
  rcases exists_nat_pow_near hA_ge_one (by norm_num : (1 : ℝ) < 3) with
    ⟨n, hn_lower, hn_upper⟩
  refine ⟨n + 1, ?_⟩
  have hpow_pos : 0 < (3 : ℝ) ^ (n + 1) := by positivity
  have hA_pos : 0 < 27 / gap := div_pos (by norm_num) hgap_pos
  have hpow_lower : 27 / gap ≤ (3 : ℝ) ^ (n + 1) :=
    le_of_lt hn_upper
  have hpow_upper : (3 : ℝ) ^ (n + 1) ≤ 81 / gap := by
    calc
      (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
        rw [pow_succ]
        ring
      _ ≤ 3 * (27 / gap) := by
        exact mul_le_mul_of_nonneg_left hn_lower (by norm_num : (0 : ℝ) ≤ 3)
      _ = 81 / gap := by ring
  constructor
  · have hinv :
        1 / (81 / gap) ≤ 1 / ((3 : ℝ) ^ (n + 1)) :=
      one_div_le_one_div_of_le hpow_pos hpow_upper
    have hrewrite :
        1 / (81 / gap) = (1 / 81 : ℝ) * gap := by
      field_simp [hgap_pos.ne']
    simpa [hrewrite, one_div] using hinv
  · have hinv :
        1 / ((3 : ℝ) ^ (n + 1)) ≤ 1 / (27 / gap) :=
      one_div_le_one_div_of_le hA_pos hpow_lower
    have hrewrite :
        1 / (27 / gap) = (1 / 27 : ℝ) * gap := by
      field_simp [hgap_pos.ne']
    simpa [hrewrite, one_div] using hinv

/-- A canonical triadic scale choice for the radius gap.  Outside the Caccioppoli
radius range it is set to `0`; all note-facing uses go through the `_spec`
lemma below. -/
noncomputable def coarseCaccioppoliTriadicGapScale (ρ₁ ρ₂ : ℝ) : ℕ :=
  if h : (1 / 3 : ℝ) ≤ ρ₁ ∧ ρ₁ < ρ₂ ∧ ρ₂ ≤ 1 then
    Classical.choose
      (exists_coarseCaccioppoliTriadicGapScaleChoice h.1 h.2.1 h.2.2)
  else
    0

theorem coarseCaccioppoliTriadicGapScale_spec {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    CoarseCaccioppoliTriadicGapScaleChoice
      (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂) ρ₁ ρ₂ := by
  unfold coarseCaccioppoliTriadicGapScale
  have hvalid : (1 / 3 : ℝ) ≤ ρ₁ ∧ ρ₁ < ρ₂ ∧ ρ₂ ≤ 1 :=
    ⟨hρ₁, hlt, hρ₂⟩
  rw [dif_pos hvalid]
  exact
    Classical.choose_spec
      (exists_coarseCaccioppoliTriadicGapScaleChoice hρ₁ hlt hρ₂)

theorem coarseCaccioppoliGapInv_ge_three_halves {ρ₁ ρ₂ : ℝ}
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    (3 / 2 : ℝ) ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  rw [coarseCaccioppoliGapInv_eq_inv]
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hlt
  have hgap_ne : ρ₂ - ρ₁ ≠ 0 := hgap_pos.ne'
  have hgap_le : ρ₂ - ρ₁ ≤ (2 / 3 : ℝ) :=
    coarseCaccioppoli_gap_le_two_thirds hρ₁ hlt hρ₂
  field_simp [hgap_ne]
  nlinarith

theorem coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
    {k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hρ : ρ₁ < ρ₂) :
    (3 : ℝ) ^ k ≤ 81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hρ
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hpow_ne : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hscaled :
      ((3 : ℝ) ^ k) * ((1 / 81 : ℝ) * (ρ₂ - ρ₁)) ≤ 1 := by
    calc
      ((3 : ℝ) ^ k) * ((1 / 81 : ℝ) * (ρ₂ - ρ₁))
          ≤ ((3 : ℝ) ^ k) * (((3 : ℝ) ^ k)⁻¹) := by
            exact mul_le_mul_of_nonneg_left hchoice.1 hpow_nonneg
      _ = 1 := by rw [mul_inv_cancel₀ hpow_ne]
  have hmain : (3 : ℝ) ^ k * (ρ₂ - ρ₁) ≤ 81 := by
    nlinarith
  have hdiv : (3 : ℝ) ^ k ≤ 81 / (ρ₂ - ρ₁) := by
    exact (le_div_iff₀ hgap_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  simpa [coarseCaccioppoliGapInv_eq_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hdiv

theorem coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice
    {k : ℕ} {ρ₁ ρ₂ : ℝ}
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hρ : ρ₁ < ρ₂) :
    27 * coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ (3 : ℝ) ^ k := by
  have hgap_pos : 0 < ρ₂ - ρ₁ := sub_pos.mpr hρ
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hpow_ne : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hscaled :
      1 ≤ ((3 : ℝ) ^ k) * ((1 / 27 : ℝ) * (ρ₂ - ρ₁)) := by
    calc
      1 = ((3 : ℝ) ^ k) * (((3 : ℝ) ^ k)⁻¹) := by rw [mul_inv_cancel₀ hpow_ne]
      _ ≤ ((3 : ℝ) ^ k) * ((1 / 27 : ℝ) * (ρ₂ - ρ₁)) := by
            exact mul_le_mul_of_nonneg_left hchoice.2 hpow_nonneg
  have hmain : 27 ≤ (3 : ℝ) ^ k * (ρ₂ - ρ₁) := by
    nlinarith
  have hdiv : 27 / (ρ₂ - ρ₁) ≤ (3 : ℝ) ^ k := by
    exact (div_le_iff₀ hgap_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  simpa [coarseCaccioppoliGapInv_eq_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hdiv

/-- A stronger triadic-scale absorption estimate, stated using the note's
auxiliary scale `k`, implies the actual absorption condition appearing in the
boundary coefficient bookkeeping. -/
theorem coarseCaccioppoli_boundary_noteAbsorptionCondition_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C / (s * (1 - s)) * (3 : ℝ) ^ k *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) ≤ (27 / 4 : ℝ)) :
    CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hscale hρ₁ hlt hρ₂ with ⟨k, hkchoice, hkbound⟩
  have hs1 : s < 1 := by
    linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hpow_nonneg :
      0 ≤ C / (s * (1 - s)) *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
    refine mul_nonneg ?_ ?_
    · exact mul_nonneg
        (div_nonneg hC hden_nonneg)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · exact Real.rpow_nonneg htheta_nonneg _
  have hgap_le : coarseCaccioppoliGapInv ρ₁ ρ₂ ≤ ((3 : ℝ) ^ k) / 27 := by
    exact (le_div_iff₀ (show (0 : ℝ) < 27 by norm_num)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (coarseCaccioppoli_mul_gapInv_le_pow_scale_of_triadicGapScaleChoice hkchoice hlt)
  calc
    coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂
        = coarseCaccioppoliGapInv ρ₁ ρ₂ *
            (C / (s * (1 - s)) *
              Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
              Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := by
              unfold coarseCaccioppoliBoundaryAlphaOfHeight
              ring
    _ ≤ ((3 : ℝ) ^ k / 27) *
          (C / (s * (1 - s)) *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hgap_le hpow_nonneg
    _ = (1 / 27 : ℝ) *
          (C / (s * (1 - s)) * (3 : ℝ) ^ k *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := by
              ring
    _ ≤ (1 / 27 : ℝ) * (27 / 4 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hkbound (by norm_num : 0 ≤ (1 / 27 : ℝ))
    _ = (1 / 4 : ℝ) := by norm_num

/-- The note-facing explicit height choice already implies the absorbability
condition in the boundary bookkeeping. -/
theorem coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hheight : CoarseCaccioppoliBoundaryHeightChoice Q a s t C h) :
    CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h := by
  apply coarseCaccioppoli_boundary_noteAbsorptionCondition_of_triadicGapScaleChoice
    Q a s t C h hC hs ht hst
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hheight hρ₁ hlt hρ₂ with ⟨k, hkchoice, -, hkbound⟩
  refine ⟨k, hkchoice, ?_⟩
  exact le_trans hkbound (by norm_num)

/-- The interior note-specific absorption condition currently follows from the
same stronger triadic-scale estimate as the boundary version. -/
theorem coarseCaccioppoli_interior_noteAbsorptionCondition_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C / (s * (1 - s)) * (3 : ℝ) ^ k *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) ≤ (27 / 4 : ℝ)) :
    CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h := by
  exact coarseCaccioppoli_boundary_noteAbsorptionCondition_of_triadicGapScaleChoice
    Q a s t C h hC hs ht hst hscale

/-- The same explicit `h`-choice bookkeeping also discharges the interior
absorption condition. -/
theorem coarseCaccioppoli_interior_noteAbsorptionCondition_of_heightChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hheight : CoarseCaccioppoliInteriorHeightChoice Q a s t C h) :
    CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h := by
  exact coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
    Q a s t C h hC hs ht hst hheight


end

end Homogenization
