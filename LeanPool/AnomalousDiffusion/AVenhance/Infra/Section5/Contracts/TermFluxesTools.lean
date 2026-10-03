/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityPeriodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite

/-! # Generic tools for the flux contracts

Locally finite `tsum`s of jointly smooth families, the order-shifting spatial gradient on the open
half space, and the local-in-time finiteness of the `ζ_{m,k}` and `ξ̂_{m,l}` cutoff families. -/

@[expose] public section

open Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

/-- The open half space `(0,∞) × ℝ²`. -/
abbrev tfU : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ

/-- A `tsum` over a family whose terms vanish outside a finite set, uniformly for times within one
unit of any given time, is as smooth as its terms. -/
theorem tf_contDiffOn_tsum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {U : Set (ℝ × Vec 2)} (f : ι → ℝ × Vec 2 → F) (P : ι → ℝ → Prop)
    (hact : ∀ t₀ : ℝ, ∃ S : Finset ι, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → P k t)
    (hzero : ∀ k q, P k q.1 → f k q = 0) (hf : ∀ k, ContDiffOn ℝ n (f k) U) :
    ContDiffOn ℝ n (fun q => ∑' k, f k q) U := by
  refine contDiffOn_of_locally_contDiffOn fun p₀ _ => ?_
  obtain ⟨S, hS⟩ := hact p₀.1
  have hopen : IsOpen {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨_, hopen, by simp, ?_⟩
  have hfin : ContDiffOn ℝ n (fun q => ∑ k ∈ S, f k q)
      (U ∩ {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1}) :=
    ContDiffOn.sum fun k _ => (hf k).mono Set.inter_subset_left
  exact hfin.congr fun q hq => tsum_eq_sum fun k hk => hzero k q (hS k hk q.1 hq.2)

/-- Odd-subtype version of local-in-time finiteness. -/
theorem tf_active_odd {P : ℤ → ℝ → Prop}
    (h : ∀ t₀ : ℝ, ∃ S : Finset ℤ, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → P k t) :
    ∀ t₀ : ℝ, ∃ S : Finset {k : ℤ // Odd k}, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → P k.1 t := by
  classical
  intro t₀
  obtain ⟨S, hS⟩ := h t₀
  refine ⟨S.subtype _, fun k hk t ht => hS k.1 ?_ t ht⟩
  intro hmem
  exact hk (Finset.mem_subtype.mpr hmem)

/-- A family on the lattice `kτ` whose members vanish outside `|t - kτ| ≤ ρ` is locally finite in
time. -/
theorem tf_exists_active {τ ρ : ℝ} (hτ : 0 < τ) {f : ℤ → ℝ → ℝ}
    (hf : ∀ l t, f l t ≠ 0 → |t - (l : ℝ) * τ| ≤ ρ) (t₀ : ℝ) :
    ∃ S : Finset ℤ, ∀ l ∉ S, ∀ t, |t - t₀| < 1 → f l t = 0 := by
  have hfin := finite_lattice_near hτ t₀ (ρ + 1)
  refine ⟨hfin.toFinset, fun l hl t ht => ?_⟩
  by_contra hne
  apply hl
  rw [Set.Finite.mem_toFinset]
  have h1 := hf l t hne
  have h3 : |t₀ - (l : ℝ) * τ| ≤ |t₀ - t| + |t - (l : ℝ) * τ| := by
    have := abs_add_le (t₀ - t) (t - (l : ℝ) * τ)
    simpa using this
  have h2 : |t₀ - t| < 1 := by rwa [abs_sub_comm]
  change |t₀ - (l : ℝ) * τ| ≤ ρ + 1
  linarith

variable {β : ℝ} (I : Ingredients β)

/-- `ζ_{m,k}` is supported in `|t - kτ_m| ≤ (2/3)τ_m`. -/
theorem tf_zetaMK_ne_zero_abs_le (m : ℕ) (k : ℤ) (t : ℝ) (hne : I.zetaMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 2 / 3 * tau β I.Λ m := by
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(2 / 3) : ℝ) (2 / 3) := by
    by_contra hnot
    apply hne
    have h1 := I.zeta_le_ind u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    exact le_antisymm h1 (I.zeta_nonneg u)
  have hτ := I.tau_pos' m
  have : |u| ≤ 2 / 3 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at this
  exact this

/-- Local-in-time finiteness of the `ζ_{m,k}` family. -/
theorem tf_zetaMK_active (m : ℕ) (t₀ : ℝ) :
    ∃ S : Finset ℤ, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → I.zetaMK m k t = 0 :=
  tf_exists_active (I.tau_pos' m) (fun k t h => tf_zetaMK_ne_zero_abs_le I m k t h) t₀

/-- Local-in-time finiteness of the `ξ̂_{m,l}` family. -/
theorem tf_hatXiML_active {m : ℕ} (hm : 1 ≤ m) (t₀ : ℝ) :
    ∃ S : Finset ℤ, ∀ l ∉ S, ∀ t, |t - t₀| < 1 → I.hatXiML m l t = 0 := by
  refine tf_exists_active (I.tauPP_pos' m) (ρ := 1 / 2 * tauPP β I.Λ m + tauP β I.Λ m)
    (fun l t hne => ?_) t₀
  have hle := I.hatXi_le m hm l t
  have hge : 0 ≤ shiftCutoff (I.hatXi m) (l * tauPP β I.Λ m) t :=
    (indIcc_nonneg' _ _ _).trans (I.hatXi_ge m hm l t)
  have hmem : t ∈ Set.Icc ((l - 1 / 2) * tauPP β I.Λ m - tauP β I.Λ m)
      ((l + 1 / 2) * tauPP β I.Λ m + tauP β I.Λ m) := by
    by_contra hnot
    apply hne
    rw [indIcc_eq_zero_of_not_mem hnot] at hle
    exact le_antisymm hle hge
  rw [abs_le]
  constructor <;> nlinarith [hmem.1, hmem.2]

/-! ### Spatial derivatives on the open half space -/

/-- On the open half space the spatial gradient components of a jointly `C^n` function are jointly
`C^m`, `m + 1 ≤ n`. -/
theorem tf_spaceGrad_contDiffOn_Ioi {F : ℝ → Vec 2 → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hF : ContDiffOn ℝ n (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (j : Fin 2) :
    ContDiffOn ℝ m (fun p : ℝ × Vec 2 => spaceGrad (F p.1) p.2 j)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ with hs
  have hso : IsOpen s := isOpen_Ioi.prod isOpen_univ
  have hsu : UniqueDiffOn ℝ s := hso.uniqueDiffOn
  have hn0 : n ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (le_trans le_add_self hmn)).ne'
  have h1 : ContDiffOn ℝ m
      (fun p : ℝ × Vec 2 =>
        fderivWithin ℝ (fun q : ℝ × Vec 2 => F q.1 q.2) s p (0, basisVec j)) s :=
    (hF.fderivWithin hsu hmn).clm_apply contDiffOn_const
  refine h1.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Section5.RelativeError.spaceGrad_slice_eq_fderivWithin
    (F := fun q : ℝ × Vec 2 => F q.1 q.2) (s := s) t x
    (fun y => ⟨ht, trivial⟩) (hF.differentiableOn hn0 (t, x) ⟨ht, trivial⟩) j

/-- The divergence of a jointly `C²` vector field is jointly continuous on the open half space. -/
theorem tf_vecDiv_continuousOn {V : ℝ → Vec 2 → Vec 2}
    (hV : ∀ i : Fin 2, ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => V p.1 p.2 i)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => vecDiv (V p.1) p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  unfold vecDiv
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact (tf_spaceGrad_contDiffOn_Ioi (m := 1) (n := 2) (by norm_num)
    (F := fun t y => V t y i) (hV i) i).continuousOn

/-! ### Matrix-vector smoothness -/

theorem tf_mulVec_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    {s : Set E} {A : E → Matrix (Fin 2) (Fin 2) ℝ} {v : E → Vec 2}
    (hA : ∀ i j, ContDiffOn ℝ n (fun e => A e i j) s) (hv : ∀ j, ContDiffOn ℝ n (fun e => v e j) s)
    (i : Fin 2) : ContDiffOn ℝ n (fun e => (A e).mulVec (v e) i) s := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((hA i 0).mul (hv 0)).add ((hA i 1).mul (hv 1))

end AVenhance.Infra.Section5.Contracts
end
