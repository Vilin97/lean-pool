/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib
public import LeanPool.Odlyzko.DedekindResidue.CompletedZeta.ThetaEstimates

/-!
# The abstract functional-equation pair of the total Hecke theta  (SP1-AGE-4, brick 4c)

Everything before this file culminates in one object: **`heckeFEPair : WeakFEPair ℂ`** —
the total normalised theta `f(x) = ∑_C Ĝ_C(x)` together with

* its clean symmetry `f(1/x) = x^{1/2}·f(x)` (`heckeF_inversion`, so weight `k = 1/2` and
  root number `ε = 1`),
* local integrability on `(0,∞)` (from `continuousOn_heckeF`),
* and super-polynomial approach to the constant term `f₀ = h·w⁻¹·vol`
  (`heckeF_sub_const_isBigO`, from the exponential deviation bound and
  `isBigO_exp_neg_rpow`).

Mathlib's abstract Mellin machinery (`Mathlib.NumberTheory.LSeries.AbstractFuncEq` — the
engine underneath `completedRiemannZeta`) now provides, for free: an entire `Λ₀`, the
meromorphic `Λ` with poles exactly at `σ ∈ {0, 1/2}` and known residues, the Mellin
representation on `Re σ > 1/2`, and the functional equation `Λ(1/2 − σ) = Λ(σ)`.
`Λ_K(s)` will be `heckeFEPair.Λ (s/2)` up to an explicit constant adjustment.
-/

namespace DedekindResidue

@[expose] public section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
open Asymptotics Filter
open scoped nonZeroDivisors Real


/-- A stretched-exponential `exp(-c·x^p)` beats every power at infinity. -/
theorem isBigO_exp_neg_rpow {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (r : ℝ) :
    (fun x : ℝ => Real.exp (-c * x ^ p)) =O[atTop] fun x : ℝ => x ^ r := by
  have h1 : (fun y : ℝ => y ^ (-r / p)) =O[atTop] (fun y => Real.exp (c * y)) :=
    (isLittleO_rpow_exp_pos_mul_atTop (-r / p) hc).isBigO
  obtain ⟨C, hC⟩ := h1.bound
  have htend : Filter.Tendsto (fun x : ℝ => x ^ p) atTop atTop := tendsto_rpow_atTop hp
  have hev := htend.eventually hC
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop (1:ℝ)] with x hx h1x
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos h1x
  have hxr_pos : (0:ℝ) < x ^ r := Real.rpow_pos_of_pos hx0 _
  have hexp_pos : (0:ℝ) < Real.exp (c * x ^ p) := Real.exp_pos _
  have hxp : (x ^ p) ^ (-r / p) = x ^ (-r) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hx ⊢
  rw [hxp, Real.rpow_neg hx0.le, abs_of_pos (by positivity), abs_of_pos hexp_pos] at hx
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hxr_pos]
  have h2 : 1 ≤ C * Real.exp (c * x ^ p) * x ^ r := by
    have h3 := mul_le_mul_of_nonneg_right hx hxr_pos.le
    rwa [inv_mul_cancel₀ hxr_pos.ne'] at h3
  have h4 : Real.exp (-c * x ^ p) = (Real.exp (c * x ^ p))⁻¹ := by
    rw [show -c * x ^ p = -(c * x ^ p) by ring, Real.exp_neg]
  rw [h4]
  calc (Real.exp (c * x ^ p))⁻¹ = (Real.exp (c * x ^ p))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (Real.exp (c * x ^ p))⁻¹ * (C * Real.exp (c * x ^ p) * x ^ r) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * x ^ r := by field_simp

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
theorem continuousOn_heckeGClass (C : ClassGroup (𝓞 K)) :
    ContinuousOn (heckeGClass K C) (Set.Ioi (0:ℝ)) := by
  have hN := idealNormR_pos K (classRep K C)
  have hβ := heckeBeta_pos K
  change ContinuousOn (fun x => heckeG K (classRep K C)
    ((idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K * x)) _
  refine ContinuousOn.comp (g := heckeG K (classRep K C))
    (f := fun x : ℝ => (idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K * x)
    (t := Set.Ioi 0) (continuousOn_heckeG K _)
    ((continuous_const.mul continuous_id).continuousOn) ?_
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  exact Set.mem_Ioi.mpr (by positivity)

open scoped Classical in
theorem continuousOn_heckeF : ContinuousOn (heckeF K) (Set.Ioi (0:ℝ)) := by
  change ContinuousOn (fun x => ∑ C : ClassGroup (𝓞 K), heckeGClass K C x) _
  exact continuousOn_finsetSum _ (fun C _ => continuousOn_heckeGClass K C)

open scoped Classical in
theorem exists_heckeGClass_dev_bound (C : ClassGroup (𝓞 K)) :
    ∃ Cb c' x₀ : ℝ, 0 < Cb ∧ 0 < c' ∧ 1 ≤ x₀ ∧ ∀ {x : ℝ}, x₀ ≤ x →
      |heckeGClass K C x - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K|
        ≤ Cb * Real.exp (-c' * x ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hdev⟩ := exists_heckeG_dev_bound K (classRep K C)
  have hN := idealNormR_pos K (classRep K C)
  have hβ := heckeBeta_pos K
  set s : ℝ := (idealNormR K (classRep K C))⁻¹ ^ 2 * heckeBeta K with hs_def
  have hs : 0 < s := by positivity
  have hn : (0:ℝ) < (1 : ℝ) / (Module.finrank ℚ K) := div_pos one_pos (finrank_pos_real K)
  refine ⟨C₀, c₀ * s ^ ((1 : ℝ) / (Module.finrank ℚ K)), max 1 s⁻¹, hC₀,
    by have := Real.rpow_pos_of_pos hs ((1 : ℝ) / (Module.finrank ℚ K)); positivity,
    le_max_left _ _, fun {x} hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hsx : (1:ℝ) ≤ s * x := by
    have hxs : s⁻¹ ≤ x := le_trans (le_max_right _ _) hx
    calc (1:ℝ) = s * s⁻¹ := (mul_inv_cancel₀ hs.ne').symm
      _ ≤ s * x := mul_le_mul_of_nonneg_left hxs hs.le
  have hdev' := hdev hsx
  have harg : (s * x) ^ ((1 : ℝ) / (Module.finrank ℚ K))
      = s ^ ((1 : ℝ) / (Module.finrank ℚ K)) * x ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
    Real.mul_rpow hs.le hx0.le
  have hshape : heckeGClass K C x = heckeG K (classRep K C) (s * x) := rfl
  rw [hshape]
  calc |heckeG K (classRep K C) (s * x) - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K|
      ≤ C₀ * Real.exp (-c₀ * (s * x) ^ ((1 : ℝ) / (Module.finrank ℚ K))) := hdev'
    _ = C₀ * Real.exp (-(c₀ * s ^ ((1 : ℝ) / (Module.finrank ℚ K)))
          * x ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
        rw [harg]
        ring_nf

open scoped Classical in
/-- The total-theta constant term: `h·w⁻¹·vol` (`h` the class number). -/
noncomputable def heckeFConst : ℝ :=
  (Fintype.card (ClassGroup (𝓞 K)) : ℝ) * ((torsionOrder K : ℝ)⁻¹ * unitBoxVol K)

open scoped Classical in
theorem exists_heckeF_dev_bound :
    ∃ Cb c' x₀ : ℝ, 0 < Cb ∧ 0 < c' ∧ 1 ≤ x₀ ∧ ∀ {x : ℝ}, x₀ ≤ x →
      |heckeF K x - heckeFConst K|
        ≤ Cb * Real.exp (-c' * x ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
  choose Cb c x₀ hCb hc hx₀ hdev using fun C : ClassGroup (𝓞 K) =>
    exists_heckeGClass_dev_bound K C
  have hne : (Finset.univ : Finset (ClassGroup (𝓞 K))).Nonempty := Finset.univ_nonempty
  refine ⟨∑ C, Cb C, Finset.univ.inf' hne c, Finset.univ.sup' hne x₀,
    Finset.sum_pos (fun C _ => hCb C) hne,
    (Finset.lt_inf'_iff hne).mpr (fun C _ => hc C),
    le_trans (hx₀ (hne.choose)) (Finset.le_sup' _ (Finset.mem_univ _)), fun {x} hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x :=
    le_trans (le_trans (hx₀ hne.choose) (Finset.le_sup' _ (Finset.mem_univ _))) hx
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxpow : (0:ℝ) ≤ x ^ ((1 : ℝ) / (Module.finrank ℚ K)) :=
    (Real.rpow_pos_of_pos hx0 _).le
  have hFsum : heckeF K x - heckeFConst K
      = ∑ C : ClassGroup (𝓞 K),
        (heckeGClass K C x - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K) := by
    rw [heckeF, heckeFConst, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hFsum]
  calc |∑ C : ClassGroup (𝓞 K),
        (heckeGClass K C x - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K)|
      ≤ ∑ C : ClassGroup (𝓞 K),
        |heckeGClass K C x - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ C : ClassGroup (𝓞 K),
        Cb C * Real.exp (-(Finset.univ.inf' hne c)
          * x ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
        refine Finset.sum_le_sum (fun C _ => ?_)
        have hdC := hdev C (le_trans (Finset.le_sup' _ (Finset.mem_univ C)) hx)
        refine le_trans hdC ?_
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hCb C).le
        have hcC : Finset.univ.inf' hne c ≤ c C := Finset.inf'_le _ (Finset.mem_univ C)
        nlinarith
    _ = (∑ C, Cb C) * Real.exp (-(Finset.univ.inf' hne c)
          * x ^ ((1 : ℝ) / (Module.finrank ℚ K))) := by
        rw [Finset.sum_mul]

open scoped Classical in
/-- Rapid decay: the total theta approaches its constant term faster than any power. -/
theorem heckeF_sub_const_isBigO (r : ℝ) :
    (fun x : ℝ => heckeF K x - heckeFConst K) =O[atTop] fun x : ℝ => x ^ r := by
  obtain ⟨Cb, c', x₀, hCb, hc', hx₀, hdev⟩ := exists_heckeF_dev_bound K
  have hn : (0:ℝ) < (1 : ℝ) / (Module.finrank ℚ K) := div_pos one_pos (finrank_pos_real K)
  refine IsBigO.trans ?_ (isBigO_exp_neg_rpow hc' hn r)
  rw [isBigO_iff]
  refine ⟨Cb, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hdev hx

open scoped Classical in
/-- **The abstract functional-equation pair of the total Hecke theta**: `f = g = heckeF`
(complex-valued), weight `k = 1/2`, root number `ε = 1`, constant terms `h·w⁻¹·vol`.
Mathlib's `WeakFEPair` machinery turns this into the completed Dedekind zeta function
with its analytic continuation and functional equation. -/
noncomputable def heckeFEPair : WeakFEPair ℂ where
  f := fun x => (heckeF K x : ℂ)
  g := fun x => (heckeF K x : ℂ)
  k := 1 / 2
  ε := 1
  f₀ := (heckeFConst K : ℂ)
  g₀ := (heckeFConst K : ℂ)
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeF K)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeF K)).locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq := fun x hx => by
    have h := heckeF_inversion K (Set.mem_Ioi.mp hx)
    rw [Real.sqrt_eq_rpow] at h
    change ((heckeF K (1 / x) : ℝ) : ℂ) = _
    rw [h, one_mul, smul_eq_mul]
    push_cast
    ring
  hf_top := fun r => by
    have hbase := heckeF_sub_const_isBigO K r
    rw [isBigO_iff] at hbase ⊢
    obtain ⟨C, hC⟩ := hbase
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    calc ‖(heckeF K x : ℂ) - (heckeFConst K : ℂ)‖
        = ‖((heckeF K x - heckeFConst K : ℝ) : ℂ)‖ := by push_cast; ring_nf
      _ = ‖heckeF K x - heckeFConst K‖ := Complex.norm_real _
      _ ≤ C * ‖x ^ r‖ := hx
  hg_top := fun r => by
    have hbase := heckeF_sub_const_isBigO K r
    rw [isBigO_iff] at hbase ⊢
    obtain ⟨C, hC⟩ := hbase
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    calc ‖(heckeF K x : ℂ) - (heckeFConst K : ℂ)‖
        = ‖((heckeF K x - heckeFConst K : ℝ) : ℂ)‖ := by push_cast; ring_nf
      _ = ‖heckeF K x - heckeFConst K‖ := Complex.norm_real _
      _ ≤ C * ‖x ^ r‖ := hx

end

end DedekindResidue
