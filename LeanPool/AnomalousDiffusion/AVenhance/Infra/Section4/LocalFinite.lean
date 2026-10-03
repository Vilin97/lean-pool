/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelLipschitz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.TimeAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeqPred

/-! Local finiteness of the cutoff families. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-! ## FILES 11-14: local finiteness of the cutoff families (why every `tsum` below is a finite
sum, no junk value).  INFRA helper + FILE 11-14 [PROVED, characterizations]. -/

/-- INFRA (private helper, `Infra/Ingredients/LatticeNear.lean`). -/
theorem finite_lattice_near {τ : ℝ} (hτ : 0 < τ) (t ρ : ℝ) :
    {l : ℤ | |t - (l : ℝ) * τ| ≤ ρ}.Finite := by
  refine (Set.finite_Icc (⌈(t - ρ) / τ⌉) (⌊(t + ρ) / τ⌋)).subset ?_
  intro l hl
  have h := abs_le.mp (show |t - (l : ℝ) * τ| ≤ ρ from hl)
  constructor
  · apply Int.ceil_le.mpr
    rw [div_le_iff₀ hτ]; linarith [h.2]
  · apply Int.le_floor.mpr
    rw [le_div_iff₀ hτ]; linarith [h.1]

theorem indIcc_eq_zero_of_not_mem {a b t : ℝ} (h : t ∉ Set.Icc a b) : indIcc a b t = 0 := by
  simp [indIcc, h]

theorem indIcc_nonneg' (a b t : ℝ) : 0 ≤ indIcc a b t := by
  by_cases h : t ∈ Set.Icc a b <;> simp [indIcc, h]

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

theorem tau_pos' (m : ℕ) : 0 < tau β I.Λ m :=
  Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)

theorem tauPP_pos' (m : ℕ) : 0 < tauPP β I.Λ m :=
  Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt (by exact_mod_cast I.two_pow_seven_le)

/-- `{k | ξ_{m,k}(t) ≠ 0}` is finite. -/
theorem xiMK_support_finite (m : ℕ) (t : ℝ) : {k : ℤ | I.xiMK m k t ≠ 0}.Finite := by
  refine (finite_lattice_near (I.tau_pos' m) t (5 / 4 * tau β I.Λ m)).subset ?_
  intro k hk
  have hne : I.xiMK m k t ≠ 0 := hk
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have hτ := I.tau_pos' m
  change |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m
  have : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at this
  linarith

/-- `{k | ζ_{m,k}(t) ≠ 0}` is finite. -/
theorem zetaMK_support_finite (m : ℕ) (t : ℝ) : {k : ℤ | I.zetaMK m k t ≠ 0}.Finite := by
  refine (finite_lattice_near (I.tau_pos' m) t (2 / 3 * tau β I.Λ m)).subset ?_
  intro k hk
  have hne : I.zetaMK m k t ≠ 0 := hk
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(2 / 3) : ℝ) (2 / 3) := by
    by_contra hnot
    apply hne
    have h1 := I.zeta_le_ind u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    exact le_antisymm h1 (I.zeta_nonneg u)
  have hτ := I.tau_pos' m
  change |t - (k : ℝ) * tau β I.Λ m| ≤ 2 / 3 * tau β I.Λ m
  have : |u| ≤ 2 / 3 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at this
  linarith

/-- `{l | ζ̂_{m,l}(t) ≠ 0}` is finite. -/
theorem hatZetaML_support_finite {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    {l : ℤ | I.hatZetaML m l t ≠ 0}.Finite := by
  refine (finite_lattice_near (I.tauPP_pos' m) t (1 / 2 * tauPP β I.Λ m)).subset ?_
  intro l hl
  have hne : I.hatZetaML m l t ≠ 0 := hl
  have hle := I.hatZeta_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatZeta m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatZeta_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  have hp : 0 < tauP β I.Λ m := Infra.Cutoff.tauP_pos I.one_lt_beta I.beta_lt
    (by exact_mod_cast I.two_pow_seven_le)
  change |t - (l : ℝ) * tauPP β I.Λ m| ≤ 1 / 2 * tauPP β I.Λ m
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-- `{l | ξ̂_{m,l}(t) ≠ 0}` is finite. -/
theorem hatXiML_support_finite {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    {l : ℤ | I.hatXiML m l t ≠ 0}.Finite := by
  refine (finite_lattice_near (I.tauPP_pos' m) t
    (1 / 2 * tauPP β I.Λ m + tauP β I.Λ m)).subset ?_
  intro l hl
  have hne : I.hatXiML m l t ≠ 0 := hl
  have hle := I.hatXi_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatXi m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatXi_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  change |t - (l : ℝ) * tauPP β I.Λ m| ≤ 1 / 2 * tauPP β I.Λ m + tauP β I.Λ m
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

end Ingredients

end AVenhance
