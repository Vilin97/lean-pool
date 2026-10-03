/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ShiftCutoff

/-! Statement file: `Ingredients` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- The exact list of ingredients of Section 2.1 (source lines 967-1396). -/
structure Ingredients (β : ℝ) where
  /-- `e.beta.def` (977). -/
  one_lt_beta : 1 < β
  /-- `e.beta.def` (977). -/
  beta_lt : β < 4 / 3
  /-- minimal scale separation, line 1030. -/
  Λ : ℕ
  /-- `Λ ∈ [2^7, ∞)`, line 1030. -/
  two_pow_seven_le : 2 ^ 7 ≤ Λ
  /-- time cutoff `ζ`, line 1226. -/
  zeta : ℝ → ℝ
  /-- `ζ ∈ C_c^∞(ℝ)`, line 1226. -/
  zeta_smooth : ContDiff ℝ (⊤ : ℕ∞) zeta
  zeta_compact : HasCompactSupport zeta
  /-- `ζ` even, line 1226. -/
  zeta_even : ∀ t, zeta (-t) = zeta t
  /-- the constant `C_{e.zetatimecutoff}`, lines 1226, 1235. -/
  Czeta : ℝ
  one_le_Czeta : 1 ≤ Czeta
  /-- `0 ≤ ζ ≤ 1_{[-2/3,2/3]}`, `e.zetatimecutoff` (1229). -/
  zeta_nonneg : ∀ t, 0 ≤ zeta t
  zeta_le_ind : ∀ t, zeta t ≤ indIcc (-(2 / 3)) (2 / 3) t
  /-- `∑_k ζ(· - k) ≡ 1`, `e.zetatimecutoff` (1231). -/
  zeta_partition : ∀ t, ∑' k : ℤ, zeta (t - k) = 1
  /-- `max_{j ≤ N_*} ‖∂_t^j ζ‖_∞ ≤ C`, `e.zetatimecutoff` (1233-1235). -/
  zeta_deriv_le : ∀ j : ℕ, j ≤ Nstar β → ∀ t, |iteratedDeriv j zeta t| ≤ Czeta
  /-- `∫ ζ² = 9/10`, `e.weirdo` (1241). -/
  zeta_sq_integral : ∫ t, zeta t ^ 2 = 9 / 10
  /-- time cutoff `ξ ∈ C^∞(ℝ)`, line 1268. -/
  xi : ℝ → ℝ
  xi_smooth : ContDiff ℝ (⊤ : ℕ∞) xi
  /-- the constant `C_{e.cutoff.xi}`, lines 1268, 1278. -/
  Cxi : ℝ
  one_le_Cxi : 1 ≤ Cxi
  /-- `1_{[-3/4,3/4]} ≤ ξ ≤ 1_{[-5/4,5/4]}`, `e.cutoff.xi` (1271). -/
  ind_le_xi : ∀ t, indIcc (-(3 / 4)) (3 / 4) t ≤ xi t
  xi_le_ind : ∀ t, xi t ≤ indIcc (-(5 / 4)) (5 / 4) t
  /-- `∑_{k ∈ 2ℤ+1} ξ(· - k) ≡ 1`, `e.cutoff.xi` (1273-1274). -/
  xi_partition : ∀ t, ∑' k : {k : ℤ // Odd k}, xi (t - (k : ℤ)) = 1
  /-- `max_{j ≤ N_*} ‖∂_t^j ξ‖_∞ ≤ C`, `e.cutoff.xi` (1276-1278). -/
  xi_deriv_le : ∀ j : ℕ, j ≤ Nstar β → ∀ t, |iteratedDeriv j xi t| ≤ Cxi
  /-- large-scale cutoffs `ζ̂_{m,0}`, `ξ̂_{m,0}`, `m ∈ ℕ₀` (lines 1309-1322). -/
  hatZeta : ℕ → ℝ → ℝ
  /-- Enlarged auxiliary cutoff profile at each spatial scale. -/
  hatXi : ℕ → ℝ → ℝ
  /-- smoothness (implicit, see open questions). -/
  hatZeta_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (hatZeta m)
  hatXi_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (hatXi m)
  /-- the constant `C_{e.zeta.prime.ml.bounds}` (line 1324). -/
  Chat : ℝ
  one_le_Chat : 1 ≤ Chat
  /-- `e.zeta.prime.ml.fitting` (1327-1341), first line, lower bound. -/
  hatZeta_ge : ∀ m, 1 ≤ m → ∀ (l : ℤ) t,
    indIcc ((l - 1 / 2) * tauPP β Λ m + 2 * tauP β Λ m)
      ((l + 1 / 2) * tauPP β Λ m - 2 * tauP β Λ m) t
      ≤ shiftCutoff (hatZeta m) (l * tauPP β Λ m) t
  /-- `e.zeta.prime.ml.fitting`, first line, upper bound. -/
  hatZeta_le : ∀ m, 1 ≤ m → ∀ (l : ℤ) t,
    shiftCutoff (hatZeta m) (l * tauPP β Λ m) t
      ≤ indIcc ((l - 1 / 2) * tauPP β Λ m + tauP β Λ m)
        ((l + 1 / 2) * tauPP β Λ m - tauP β Λ m) t
  /-- `e.zeta.prime.ml.fitting`, second line, lower bound. -/
  hatXi_ge : ∀ m, 1 ≤ m → ∀ (l : ℤ) t,
    indIcc ((l - 1 / 2) * tauPP β Λ m + tauP β Λ m)
      ((l + 1 / 2) * tauPP β Λ m - tauP β Λ m) t
      ≤ shiftCutoff (hatXi m) (l * tauPP β Λ m) t
  /-- `e.zeta.prime.ml.fitting`, second line, upper bound. -/
  hatXi_le : ∀ m, 1 ≤ m → ∀ (l : ℤ) t,
    shiftCutoff (hatXi m) (l * tauPP β Λ m) t
      ≤ indIcc ((l - 1 / 2) * tauPP β Λ m - tauP β Λ m)
        ((l + 1 / 2) * tauPP β Λ m + tauP β Λ m) t
  /-- `e.hatxi.partition` (1346): `∑_l ξ̂_{m,l} = 1`. -/
  hatXi_partition : ∀ m, 1 ≤ m → ∀ t,
    ∑' l : ℤ, shiftCutoff (hatXi m) (l * tauPP β Λ m) t = 1
  /-- `e.zeta.prime.ml.bounds` (1351-1359), for `ζ̂`. -/
  hatZeta_deriv_le : ∀ m, 1 ≤ m → ∀ (l : ℤ) (j : ℕ), j ≤ Nstar β → ∀ t,
    tauP β Λ m ^ j *
      |iteratedDeriv j (shiftCutoff (hatZeta m) (l * tauPP β Λ m)) t| ≤ Chat
  /-- `e.zeta.prime.ml.bounds`, for `ξ̂`. -/
  hatXi_deriv_le : ∀ m, 1 ≤ m → ∀ (l : ℤ) (j : ℕ), j ≤ Nstar β → ∀ t,
    tauP β Λ m ^ j *
      |iteratedDeriv j (shiftCutoff (hatXi m) (l * tauPP β Λ m)) t| ≤ Chat

end AVenhance
