/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPositivePairingAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ExplicitBounds.MatrixBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.JhatFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Scales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! The flux coefficient input for the positive-time `H_m` source.

The estimates are assembled from the Section 3 `flux - Jhat` remainder,
the zeroth-order bounds on `Jhat - κ I` and `Kmat - κ I`, and the
diffusivity-recursion scale package. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
namespace AVenhance.Infra.Section4
open AVenhance AVenhance.Infra.Section3 AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration

variable {β : ℝ}

/-- The oscillatory part of `Kmat` is bounded by the number of Taylor terms
times the standard `a_m² ε_m⁴/κ` scale. -/
theorem Kmat_sub_kappa_entry_abs_le (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hratio : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m)
    (t : ℝ) (i j : Fin 2) :
    |(I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
      (Nstar β : ℝ) *
        (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  classical
  let D := I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  have hC : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hτ := I.tau_pos' m
  have hε : 0 < epsilon β I.Λ m ^ 2 :=
    pow_pos (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le) 2
  have hq : 0 ≤ 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) := by positivity
  have hq1 : 2 * epsilon β I.Λ m ^ 2 /
      (4 * Real.pi ^ 2 * κ * tau β I.Λ m) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    have hπ : 2 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    calc
      2 * epsilon β I.Λ m ^ 2 ≤ 2 * (κ * tau β I.Λ m) := by gcongr
      _ ≤ (4 * Real.pi ^ 2) * (κ * tau β I.Λ m) :=
        mul_le_mul_of_nonneg_right hπ (mul_nonneg hκ.le hτ.le)
      _ = 4 * Real.pi ^ 2 * κ * tau β I.Λ m := by ring
  have hprod (n : ℕ) :
      ((n.factorial : ℝ) * 2 ^ n *
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
        ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
          (n.factorial : ℝ) *
          (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
          (I.Czeta / tau β I.Λ m ^ n)) =
      D * (2 * epsilon β I.Λ m ^ 2 /
        (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ^ n := by
    have hτ' : tau β I.Λ m ≠ 0 := hτ.ne'
    have hπ' : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hε' : epsilon β I.Λ m ^ 2 ≠ 0 := ne_of_gt hε
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    simp only [div_pow, mul_pow, inv_div]
    dsimp [D]
    field_simp [hκ.ne', hτ', hπ', hε', hn]
    ring
  have hterm (n : ℕ) (hn : n ∈ Finset.range (Nstar β)) :
      |I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| ≤ D := by
    have hn' : n ≤ Nstar β := by simp only [Finset.mem_range] at hn; omega
    rw [abs_mul]
    calc
      |I.LMN κ m n t| * |timeAvgMat (I.jMN κ m n) i j| ≤
          ((n.factorial : ℝ) * 2 ^ n *
            (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 / 2)⁻¹) *
          ((2 * Real.pi ^ 2 * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 2 /
            (n.factorial : ℝ) *
            (epsilon β I.Λ m ^ 2 / (4 * Real.pi ^ 2 * κ)) ^ n) *
            (I.Czeta / tau β I.Λ m ^ n)) := by
        apply mul_le_mul (LMN_abs_le I hm hκ n t)
          (jMN_average_entry_abs_le I m hn' hκ i j) (abs_nonneg _) (by positivity)
      _ = D * (2 * epsilon β I.Λ m ^ 2 /
          (4 * Real.pi ^ 2 * κ * tau β I.Λ m)) ^ n := hprod n
      _ ≤ D := by
        calc
          _ ≤ D * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq hq1) hD
          _ = D := mul_one _
  have hsum :
      (I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j =
        ∑ n ∈ Finset.range (Nstar β),
          I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j := by
    unfold Ingredients.Kmat
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.sum_apply]
    ring
  rw [hsum]
  calc
    |∑ n ∈ Finset.range (Nstar β),
        I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| ≤
        ∑ n ∈ Finset.range (Nstar β),
          |I.LMN κ m n t * timeAvgMat (I.jMN κ m n) i j| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (Nstar β), D := by
      exact Finset.sum_le_sum fun n hn => hterm n hn
    _ = (Nstar β : ℝ) * D := by simp [Finset.sum_const, Finset.card_range]
    _ = _ := by dsimp [D]

/-- `flux-Kmat` is controlled by the sum of the two comparison errors and
the Section 3 `flux-Jhat` remainder. -/
theorem flux_sub_Kmat_entry_abs_le_of_small_ratio (I : Ingredients β)
    {C₀ CJ : ℝ} (hCzeta : I.Czeta ≤ C₀)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    (hratio : epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) ≤ 1)
    (hJbound : ∀ t i j,
      |(I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
        CJ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ))
    (t : ℝ) (i j : Fin 2) :
    |(I.flux κ m t - I.Kmat κ m t) i j| ≤
      (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β +
        CJ + (Nstar β : ℝ) * C₀) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
  have hden : 0 < κ * tau β I.Λ m := mul_pos hκ (I.tau_pos' m)
  have hnum : epsilon β I.Λ m ^ 2 ≤ κ * tau β I.Λ m :=
    by simpa using (div_le_iff₀ hden).mp hratio
  have hK := Kmat_sub_kappa_entry_abs_le I hm hκ hnum t i j
  have hdecomp : I.flux κ m t - I.Kmat κ m t =
      (I.flux κ m t - I.Jhat κ m t) +
        (I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
          (I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply]
    abel
  have hflux := flux_sub_Jhat_entry_abs_le I hm hκ t i j
  have hrate : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by positivity
  have hCzeta_nonneg : 0 ≤ I.Czeta := by linarith [I.one_le_Czeta]
  have hratioNonneg : 0 ≤ epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m) := by positivity
  have hratioPow : (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β ≤ 1 :=
    pow_le_one₀ hratioNonneg hratio
  have hflux' : |(I.flux κ m t - I.Jhat κ m t) i j| ≤
      (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
        (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
    calc
      _ ≤ (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
            (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
            (epsilon β I.Λ m ^ 2 / (κ * tau β I.Λ m)) ^ Nstar β := hflux
      _ ≤ (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
            (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) * 1 := by
          have hcoeff : 0 ≤ (4 * Real.pi ^ 2 * I.Czeta * Nstar β *
              2 ^ Nstar β) * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
            positivity
          exact mul_le_mul_of_nonneg_left hratioPow hcoeff
      _ = _ := by ring
  have hsum := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hdecomp
  rw [hsum]
  calc
    |(I.flux κ m t - I.Jhat κ m t) i j +
        (I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j -
          (I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
        |(I.flux κ m t - I.Jhat κ m t) i j| +
          |(I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| +
            |(I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| := by
      set a₀ := (I.flux κ m t - I.Jhat κ m t) i j
      set b₀ := (I.Jhat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j
      set c₀ := (I.Kmat κ m t - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j
      calc
        |a₀ + b₀ - c₀| ≤ |a₀ + b₀| + |c₀| := abs_sub _ _
        _ ≤ |a₀| + |b₀| + |c₀| := by linarith [abs_add_le a₀ b₀]
    _ ≤ (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) +
        CJ * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) +
        (Nstar β : ℝ) *
          (I.Czeta * a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
      exact add_le_add (add_le_add hflux' (hJbound t i j)) hK
    _ ≤ (4 * Real.pi ^ 2 * I.Czeta * Nstar β * 2 ^ Nstar β +
          CJ + (Nstar β : ℝ) * I.Czeta) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
      exact le_of_eq (by ring)
    _ ≤ (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β +
          CJ + (Nstar β : ℝ) * C₀) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) := by
      have hrate : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ := by positivity
      apply mul_le_mul_of_nonneg_right _ hrate
      have hN : 0 ≤ (Nstar β : ℝ) := by positivity
      gcongr

/-- The scale hypotheses, together with the diffusivity-recursion chain, provide the
small-ratio flux coefficient bound used by the positive-time `H_m` pairing. -/
theorem hm_flux_coefficient_rate_onA7 (β C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C₁ Cflux : ℝ, 0 ≤ Cflux ∧
      OnA7Instances β C₀ C₁
        (fun I _Φ _hΦ κ M _R _θ₀ m _θprev _T =>
          ∀ t : ℝ, ∀ i j : Fin 2,
            |(I.flux (I.kappaSeq κ M m) m t - I.Kmat (I.kappaSeq κ M m) m t) i j| ≤
              Cflux * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
                I.kappaSeq κ M m)) := by
  obtain ⟨Kscale, hKscale, hscales⟩ := LeftToShow.left_to_show_scales β C₀
  obtain ⟨C₁, hthreshold⟩ := iterate_contract_scales β Kscale hKscale
  obtain ⟨CJ, hCJ, hJ⟩ := LeftToShow.Jhat_sub_kappa_entry_abs_le β C₀
  let Cflux : ℝ := 4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β + CJ +
    (Nstar β : ℝ) * C₀
  have hCflux : 0 ≤ Cflux := by dsimp [Cflux]; positivity
  refine ⟨C₁, Cflux, hCflux, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκperm M hM hperm R hR θ₀ hθ₀smooth hθ₀per hθ₀mean hθ₀analytic
    m hm hmM θprev T hθprev hT t i j
  have hstart := hthreshold I hΛ R hR m hm
  have hm2 : 2 ≤ m := hstart.1
  obtain ⟨hκm, hmono, hκprev, hprod, hratio, hcorrection, hepsilon⟩ :=
    hscales I hz hx hh κ hκperm M hM hperm m hm2 hmM
  have heprev : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hsmall : Kscale * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤ 1 := by
    have hpow := hstart.2.2
    have hKpos : 0 < Kscale := lt_of_lt_of_le (by norm_num) hKscale
    have heq : Kscale * (4 * Kscale ^ 3)⁻¹ = (4 * Kscale ^ 2)⁻¹ := by
      field_simp [hKpos.ne']
    have hden : 1 ≤ 4 * Kscale ^ 2 := by nlinarith [sq_nonneg Kscale]
    calc
      Kscale * epsilon β I.Λ (m - 1) ^ (2 * delta β) ≤
          Kscale * (4 * Kscale ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = (4 * Kscale ^ 2)⁻¹ := heq
      _ ≤ 1 := (inv_le_one₀ (by positivity)).2 hden
  have hratioSmall : epsilon β I.Λ m ^ 2 /
      (I.kappaSeq κ M m * tau β I.Λ m) ≤ 1 := by
    exact hratio.trans (hsmall)
  have hκpos : 0 < I.kappaSeq κ M m := hκm
  have hm1 : 1 ≤ m := by omega
  have hJbound := fun s a b => hJ I hz hx hh m hm1
    (I.kappaSeq κ M m) hκpos hratioSmall s a b
  have hraw := flux_sub_Kmat_entry_abs_le_of_small_ratio I hz
    hm1 hκpos hratioSmall hJbound t i j
  have hscaleNonneg : 0 ≤ a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
      I.kappaSeq κ M m := by positivity
  calc
    _ ≤ (4 * Real.pi ^ 2 * C₀ * Nstar β * 2 ^ Nstar β + CJ +
          (Nstar β : ℝ) * C₀) *
          (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
            I.kappaSeq κ M m) := hraw
    _ ≤ Cflux * (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 /
          I.kappaSeq κ M m) := by
      apply mul_le_mul_of_nonneg_right _ hscaleNonneg
      dsimp [Cflux]
      gcongr

end AVenhance.Infra.Section4
