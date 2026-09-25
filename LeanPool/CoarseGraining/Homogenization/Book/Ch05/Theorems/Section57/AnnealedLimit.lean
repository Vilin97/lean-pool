/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.QuenchedGammaEllipticity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.AnnealedConvergence
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.ScalarChain
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScaleCompression

/-! # Annealed Limit -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped Topology
open Filter

/-!
# Limiting annealed scalar coefficients

This file starts the Lean surface for the limiting annealed matrix
`\overline{\mathbf A}` used in Section 5.7.  The scalarized upper coefficient
is realized as the infimum of the decreasing `\bar σ_n`, and the starred
coefficient as the supremum of the increasing `\bar σ_{*,n}`.
-/

noncomputable section

/-- Candidate limiting scalar `\bar σ = inf_n \bar σ_n`. -/
noncomputable def barSigmaLimit {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : ℝ :=
  sInf (Set.range fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ))

/-- Candidate limiting starred scalar `\bar σ_* = sup_n \bar σ_{*,n}`. -/
noncomputable def barSigmaStarLimit {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : ℝ :=
  sSup (Set.range fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ))

/-- Limiting scalarized annealed doubled matrix. -/
noncomputable def scalarAnnealedBlockMatrixLimit
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : BlockMat d :=
  Ch02.blockDiag
    (barSigmaLimit hP hStruct • (1 : Mat d))
    ((barSigmaStarLimit hP hStruct)⁻¹ • (1 : Mat d))

namespace GammaSigmaCoarseGrainedEllipticity

variable {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
variable {hP : Ch04.RestrictionLawCarrier P} {hStruct : Ch04.RestrictionStructuralLaw P}

private theorem exponentialDecay_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => Real.rpow (3 : ℝ) (-α * (n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
  have hlinear :
      Tendsto (fun n : ℕ => (-α) * (n : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow (3 : ℝ) x) atBot (𝓝 (0 : ℝ)) :=
    tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num : (1 : ℝ) < 3)
  simpa [mul_comm] using! hpow.comp hlinear

private theorem le_of_forall_le_one_add_mul
    {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ ε > 0, a ≤ (1 + ε) * b) :
    a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  by_cases hb_zero : b = 0
  · have hbound := h 1 (by norm_num : (0 : ℝ) < 1)
    nlinarith [hb_zero]
  · have hb_pos : 0 < b := lt_of_le_of_ne' hb hb_zero
    let ε : ℝ := (a - b) / (2 * b)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact div_pos (sub_pos.mpr hlt) (mul_pos (by norm_num) hb_pos)
    have hbound := h ε hε_pos
    have hmul_eq : (1 + ε) * b = (a + b) / 2 := by
      dsimp [ε]
      field_simp [hb_pos.ne']
      ring
    nlinarith [hbound, hmul_eq]

private theorem barSigma_range_bddBelow
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    BddBelow (Set.range fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
    hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity n).le

private theorem barSigmaStar_range_bddAbove
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    BddAbove (Set.range fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) := by
  refine ⟨hP.barSigmaAtScale hStruct (0 : ℤ), ?_⟩
  rintro x ⟨n, rfl⟩
  have hstar_le_at_n :
      hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
        hP.barSigmaAtScale hStruct (n : ℤ) :=
    Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
      hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity n
  have hb_n_le_b0 :
      hP.barSigmaAtScale hStruct (n : ℤ) ≤
        hP.barSigmaAtScale hStruct (0 : ℤ) :=
    (Section54.Pigeonhole.scalarChain_of_P4 hP hStruct
      hΓ.toQuantitativeCoarseGrainedEllipticity (Nat.zero_le n)).2.2
  exact hstar_le_at_n.trans hb_n_le_b0

theorem barSigmaLimit_le_barSigmaAtScale
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) (m : ℕ) :
    barSigmaLimit hP hStruct ≤ hP.barSigmaAtScale hStruct (m : ℤ) := by
  exact csInf_le hΓ.barSigma_range_bddBelow ⟨m, rfl⟩

theorem barSigmaStarAtScale_le_barSigmaStarLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) (m : ℕ) :
    hP.barSigmaStarAtScale hStruct (m : ℤ) ≤
      barSigmaStarLimit hP hStruct := by
  exact le_csSup hΓ.barSigmaStar_range_bddAbove ⟨m, rfl⟩

theorem barSigmaStarAtScale_le_barSigmaLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) (n : ℕ) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
      barSigmaLimit hP hStruct := by
  refine le_csInf (Set.range_nonempty _) ?_
  rintro y ⟨m, rfl⟩
  by_cases hnm : n ≤ m
  · have hstar_nm :
        hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
          hP.barSigmaStarAtScale hStruct (m : ℤ) :=
      (Section54.Pigeonhole.scalarChain_of_P4 hP hStruct
        hΓ.toQuantitativeCoarseGrainedEllipticity hnm).1
    have hstar_m_b_m :
        hP.barSigmaStarAtScale hStruct (m : ℤ) ≤
          hP.barSigmaAtScale hStruct (m : ℤ) :=
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity m
    exact hstar_nm.trans hstar_m_b_m
  · have hmn : m ≤ n := by omega
    have hstar_n_b_n :
        hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
          hP.barSigmaAtScale hStruct (n : ℤ) :=
      Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity n
    have hb_n_m :
        hP.barSigmaAtScale hStruct (n : ℤ) ≤
          hP.barSigmaAtScale hStruct (m : ℤ) :=
      (Section54.Pigeonhole.scalarChain_of_P4 hP hStruct
        hΓ.toQuantitativeCoarseGrainedEllipticity hmn).2.2
    exact hstar_n_b_n.trans hb_n_m

theorem barSigmaStarLimit_le_barSigmaLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    barSigmaStarLimit hP hStruct ≤ barSigmaLimit hP hStruct := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro x ⟨n, rfl⟩
  exact hΓ.barSigmaStarAtScale_le_barSigmaLimit n

theorem barSigmaStarLimit_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 < barSigmaStarLimit hP hStruct := by
  have h0_pos :
      0 < hP.barSigmaStarAtScale hStruct (0 : ℤ) :=
    Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  exact lt_of_lt_of_le h0_pos
    (hΓ.barSigmaStarAtScale_le_barSigmaStarLimit 0)

theorem barSigmaLimit_pos
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    0 < barSigmaLimit hP hStruct :=
  lt_of_lt_of_le hΓ.barSigmaStarLimit_pos hΓ.barSigmaStarLimit_le_barSigmaLimit

private theorem barSigmaLimit_le_one_add_mul_barSigmaStarLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {ε : ℝ} (hε : 0 < ε) :
    barSigmaLimit hP hStruct ≤
      (1 + ε) * barSigmaStarLimit hP hStruct := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  obtain ⟨C, α, hC_pos, hα_pos, hconv⟩ :=
    Section51.annealedConvergence_homogenizationScale hΓ.params
  let N : ℕ := annealedAlgebraicEntryScale P hP4 C
  have hsmall_event :
      ∀ᶠ n : ℕ in atTop,
        Real.rpow (3 : ℝ) (-α * (n : ℝ)) < ε := by
    exact (exponentialDecay_tendsto_zero hα_pos) (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hsmall_event with ⟨n, hn⟩
  let m : ℕ := N + n
  have htheta :
      thetaAtScale hP hStruct (m : ℤ) ≤
        1 + Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    have hparams : hP4.params = hΓ.params := by
      simp [hP4, GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
        GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos,
        QuantitativeCoarseGrainedEllipticity.params]
    have h := hconv hP hStruct hP4 hparams n
    simpa [N, m] using h
  have htheta_eps : thetaAtScale hP hStruct (m : ℤ) ≤ 1 + ε := by
    have hdecay_le : Real.rpow (3 : ℝ) (-α * (n : ℝ)) ≤ ε :=
      (hn n le_rfl).le
    linarith
  let bm : ℝ := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm : ℝ := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hcm_pos : 0 < cm := by
    simpa [cm, hP4] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have htheta_def : bm * cm⁻¹ ≤ 1 + ε := by
    simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, bm, cm] using htheta_eps
  have hb_le : bm ≤ (1 + ε) * cm := by
    have hmul :=
      mul_le_mul_of_nonneg_right htheta_def hcm_pos.le
    calc
      bm = bm * cm⁻¹ * cm := by
            field_simp [hcm_pos.ne']
      _ ≤ (1 + ε) * cm := hmul
  have honeps_nonneg : 0 ≤ 1 + ε := by linarith
  calc
    barSigmaLimit hP hStruct ≤ bm := by
      simpa [bm, m] using hΓ.barSigmaLimit_le_barSigmaAtScale m
    _ ≤ (1 + ε) * cm := hb_le
    _ ≤ (1 + ε) * barSigmaStarLimit hP hStruct := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [cm, m] using hΓ.barSigmaStarAtScale_le_barSigmaStarLimit m)
        honeps_nonneg

theorem barSigmaLimit_eq_barSigmaStarLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    barSigmaLimit hP hStruct = barSigmaStarLimit hP hStruct := by
  refine le_antisymm ?_ hΓ.barSigmaStarLimit_le_barSigmaLimit
  exact le_of_forall_le_one_add_mul hΓ.barSigmaStarLimit_pos.le
    fun ε hε => hΓ.barSigmaLimit_le_one_add_mul_barSigmaStarLimit hε

/-- The limiting annealed block matrix has the single scalar coefficient
`\bar σ` on the upper block and `\bar σ^{-1}` on the lower block. -/
theorem scalarAnnealedBlockMatrixLimit_eq_blockDiag_barSigmaLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    scalarAnnealedBlockMatrixLimit hP hStruct =
      Ch02.blockDiag
        (barSigmaLimit hP hStruct • (1 : Mat d))
        ((barSigmaLimit hP hStruct)⁻¹ • (1 : Mat d)) := by
  rw [scalarAnnealedBlockMatrixLimit]
  rw [← hΓ.barSigmaLimit_eq_barSigmaStarLimit]

/-- The upper unit-scale scalar is controlled by the limiting scalar times the
initial scalar contrast. -/
theorem barSigmaAtScale_zero_le_thetaAtScale_zero_mul_barSigmaLimit
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    hP.barSigmaAtScale hStruct (0 : ℤ) ≤
      thetaAtScale hP hStruct (0 : ℤ) * barSigmaLimit hP hStruct := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let L := barSigmaLimit hP hStruct
  have hb0_pos : 0 < b0 := by
    simpa [b0] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0_pos : 0 < c0 := by
    simpa [c0] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0_le_L : c0 ≤ L := by
    simpa [c0, L] using hΓ.barSigmaStarAtScale_le_barSigmaLimit 0
  have htheta_nonneg : 0 ≤ b0 * c0⁻¹ :=
    mul_nonneg hb0_pos.le (inv_pos.mpr hc0_pos).le
  calc
    b0 = (b0 * c0⁻¹) * c0 := by field_simp [hc0_pos.ne']
    _ ≤ (b0 * c0⁻¹) * L :=
      mul_le_mul_of_nonneg_left hc0_le_L htheta_nonneg
    _ = thetaAtScale hP hStruct (0 : ℤ) * barSigmaLimit hP hStruct := by
      simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, c0, L]

/-- The limiting inverse upper scalar is controlled by the unit-scale inverse
upper scalar times the initial scalar contrast. -/
theorem barSigmaLimit_inv_le_thetaAtScale_zero_mul_barSigmaAtScale_zero_inv
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    (barSigmaLimit hP hStruct)⁻¹ ≤
      thetaAtScale hP hStruct (0 : ℤ) *
        (hP.barSigmaAtScale hStruct (0 : ℤ))⁻¹ := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let L := barSigmaLimit hP hStruct
  let θ := thetaAtScale hP hStruct (0 : ℤ)
  have hb0_pos : 0 < b0 := by
    simpa [b0] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hL_pos : 0 < L := by
    simpa [L] using hΓ.barSigmaLimit_pos
  have hle : b0 ≤ θ * L := by
    simpa [b0, L, θ] using
      hΓ.barSigmaAtScale_zero_le_thetaAtScale_zero_mul_barSigmaLimit
  rw [← div_eq_mul_inv]
  rw [le_div_iff₀ hb0_pos]
  have hmain : b0 * L⁻¹ ≤ θ := by
    have hmul := mul_le_mul_of_nonneg_right hle (inv_pos.mpr hL_pos).le
    calc
      b0 * L⁻¹ ≤ (θ * L) * L⁻¹ := hmul
      _ = θ := by field_simp [hL_pos.ne']
  simpa [L, θ, mul_comm] using hmain

/-- The unit-scale inverse starred scalar is controlled by the limiting inverse
scalar times the initial scalar contrast. -/
theorem barSigmaStarAtScale_zero_inv_le_thetaAtScale_zero_mul_barSigmaLimit_inv
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ ≤
      thetaAtScale hP hStruct (0 : ℤ) *
        (barSigmaLimit hP hStruct)⁻¹ := by
  let hP4 := hΓ.toQuantitativeCoarseGrainedEllipticity
  let b0 := hP.barSigmaAtScale hStruct (0 : ℤ)
  let c0 := hP.barSigmaStarAtScale hStruct (0 : ℤ)
  let L := barSigmaLimit hP hStruct
  have hb0_pos : 0 < b0 := by
    simpa [b0] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
  have hc0_pos : 0 < c0 := by
    simpa [c0] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 0
  have hL_pos : 0 < L := by
    simpa [L] using hΓ.barSigmaLimit_pos
  have hL_le_b0 : L ≤ b0 := by
    simpa [L, b0] using hΓ.barSigmaLimit_le_barSigmaAtScale 0
  have hinv_nonneg : 0 ≤ c0⁻¹ * L⁻¹ :=
    mul_nonneg (inv_pos.mpr hc0_pos).le (inv_pos.mpr hL_pos).le
  calc
    c0⁻¹ = (c0⁻¹ * L⁻¹) * L := by field_simp [hL_pos.ne']
    _ ≤ (c0⁻¹ * L⁻¹) * b0 :=
      mul_le_mul_of_nonneg_left hL_le_b0 hinv_nonneg
    _ = (b0 * c0⁻¹) * L⁻¹ := by ring
    _ = thetaAtScale hP hStruct (0 : ℤ) *
        (barSigmaLimit hP hStruct)⁻¹ := by
      simp [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, b0, c0, L]

/-- The initial scalar contrast is bounded by the Γσ ellipticity scale supplied
by `(P5)`. -/
theorem thetaAtScale_zero_le_gammaMomentScale_sq
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct) :
    thetaAtScale hP hStruct (0 : ℤ) ≤
      (Ch04.gammaMomentConst hΓ.sigma *
        (hΓ.params.xi : ℝ) ^ hΓ.sigma⁻¹ * hΓ.thetaHat) ^ 2 := by
  have htheta_wide :
      thetaAtScale hP hStruct (0 : ℤ) ≤
        widetildeThetaAtScale P (0 : ℤ)
          hΓ.toQuantitativeCoarseGrainedEllipticity :=
    Section54.OneStepContraction.thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4
      hP hStruct hΓ.toQuantitativeCoarseGrainedEllipticity
  exact htheta_wide.trans hΓ.widetildeThetaAtScale_zero_le_gammaMomentScale_sq

end GammaSigmaCoarseGrainedEllipticity

end

end Section57
end Ch05
end Book
end Homogenization
