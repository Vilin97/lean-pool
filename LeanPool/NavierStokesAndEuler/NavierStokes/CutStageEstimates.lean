/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.DiagonalJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCoordinateBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Physical jet estimates for the actual diagonal cutoff stages

The cutoff is the constructed `SmoothCutoffs.scaledCutoff`.  Its derivatives
are estimated before choosing the diagonal scales.  All estimates concern
ordinary Fréchet derivatives on an open smooth domain; the estimate carrier
itself need not be open.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CutStageEstimates

open Set Function Filter
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

/-- A concrete finite bound, used only for constants and derivative losses. -/
noncomputable def finiteBound (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (m + 1), |f k|

theorem finiteBound_one_le (f : ℕ → ℝ) (m : ℕ) : 1 ≤ finiteBound f m := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem le_finiteBound (f : ℕ → ℝ) {k m : ℕ} (hkm : k ≤ m) :
    f k ≤ finiteBound f m := by
  have hb := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m + 1)) => abs_nonneg (f j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hkm))
  exact (le_abs_self _).trans (hb.trans (le_add_of_nonneg_left zero_le_one))

/-- At the normalized argument `1`, every derivative of every nonnegative
scale has a common bound.  Derivative support removes the scale parameter. -/
theorem scaledCutoff_jet_one_bounded (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      ‖iteratedFDeriv ℝ k (SmoothCutoffs.scaledCutoff a) 1‖ ≤ C := by
  cases k with
  | zero =>
      refine ⟨1, zero_le_one, fun a _ => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (SmoothCutoffs.scaledCutoff_mem_Icc a 1).1]
      exact (SmoothCutoffs.scaledCutoff_mem_Icc a 1).2
  | succ k =>
      obtain ⟨C, hC, hb⟩ := SmoothCutoffs.scaledCutoff_iteratedDeriv_bound k
      refine ⟨C, hC, fun a ha => ?_⟩
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        div_one, one_pow, mul_one] using hb a 1 ha zero_lt_one

theorem scaledCutoff_finite_jets_one_bounded (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (SmoothCutoffs.scaledCutoff a) 1‖ ≤ C := by
  choose C hC hb using scaledCutoff_jet_one_bounded
  exact ⟨finiteBound C m, finiteBound_one_le _ _, fun a ha k hk =>
    (hb k a ha).trans (le_finiteBound C hk)⟩

/-- The scalar cutoff is flat at its support boundary, including order zero.
Continuity of each actual derivative supplies the boundary value. -/
theorem cutoff_jets_zero_of_one_le (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    iteratedFDeriv ℝ m SmoothCutoffs.cutoff x = 0 := by
  have he : EqOn (iteratedFDeriv ℝ m SmoothCutoffs.cutoff) (fun _ => 0) (Ioi 1) := by
    intro y hy
    have hg := SmoothCutoffs.cutoff_eventually_zero (hy.trans_le (le_abs_self y))
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hg m).self_of_nhds
  have hc := SmoothCutoffs.cutoff_contDiff.continuous_iteratedFDeriv (nat_le_infty m)
  exact he.closure hc continuous_const (by simpa only [closure_Ioi, mem_Ici] using hx)

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordinary chain-rule bound on an open domain, with a global outer map. -/
theorem composition_jet_bound {f : E → ℝ} {g : ℝ → V} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g)
    {x : E} (hx : x ∈ U) (m : ℕ) {C D : ℝ}
    (hC : ∀ k ≤ m, ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C)
    (hD : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k f x‖ ≤ D ^ k) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤ m.factorial * C * D ^ m := by
  have hb := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf (nat_le_infty m)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
    (fun k hk => by simpa only [iteratedFDerivWithin_univ] using hC k hk)
    (fun k hk hkm => by
      simpa only [iteratedFDerivWithin_of_isOpen k hU hx] using hD k hk hkm)
  simpa only [iteratedFDerivWithin_of_isOpen m hU hx] using hb

/-- Sharp scale-independent cutoff loss.  The relative coordinate `q/q(x)`
has value one at the evaluation point, so the preceding scalar estimate
absorbs every power of the arbitrary cutoff scale. -/
theorem cutoff_jet_bound {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    (hpos : ∀ x ∈ S, 0 < q x) (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ))) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖ ≤
        C * q x ^ (-(m : ℝ)) := by
  obtain ⟨A, hA, hAb⟩ := scaledCutoff_finite_jets_one_bounded m
  let D := finiteBound B m
  have hD : 1 ≤ D := finiteBound_one_le _ _
  have hDp : 0 < D := zero_lt_one.trans_le hD
  refine ⟨m.factorial * A * D ^ m, by positivity, ?_⟩
  intro a ha x hx
  have hqx := hpos x hx
  let f : E → ℝ := fun y => (q x)⁻¹ • q y
  let g : ℝ → ℝ := SmoothCutoffs.scaledCutoff (a * q x)
  have hf : ContDiffOn ℝ ∞ f U := hq.const_smul _
  have hg : ContDiff ℝ ∞ g := SmoothCutoffs.scaledCutoff_contDiff _
  have hfx : f x = 1 := by simp [f, hqx.ne']
  have hfb : ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k f x‖ ≤ (D / q x) ^ k := by
    intro k hk hkm
    have hBk : B k ≤ D ^ k :=
      (le_finiteBound B hkm).trans (by
        simpa only [pow_one] using pow_le_pow_right₀ hD hk)
    have he : (q x)⁻¹ * q x ^ (1 - (k : ℝ)) = q x ^ (-(k : ℝ)) := by
      rw [Real.rpow_sub hqx, Real.rpow_one, Real.rpow_neg hqx.le]
      field_simp [hqx.ne']
    calc
      ‖iteratedFDeriv ℝ k f x‖ = (q x)⁻¹ * ‖iteratedFDeriv ℝ k q x‖ := by
        dsimp only [f]
        rw [iteratedFDeriv_const_smul_apply' ((hq.contDiffAt (hU.mem_nhds (hSU hx))).of_le
          (nat_le_infty k)), norm_smul (q x)⁻¹ (iteratedFDeriv ℝ k q x),
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqx)]
      _ ≤ (q x)⁻¹ * (B k * q x ^ (1 - (k : ℝ))) :=
        mul_le_mul_of_nonneg_left (hB k x hx) (inv_nonneg.mpr hqx.le)
      _ = B k * q x ^ (-(k : ℝ)) := by rw [← he]; ring
      _ ≤ D ^ k * q x ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right hBk (Real.rpow_nonneg hqx.le _)
      _ = (D / q x) ^ k := by
        rw [Real.rpow_neg hqx.le, Real.rpow_natCast, div_pow]
        ring
  have hb := composition_jet_bound hU hf hg (hSU hx) m
    (fun k hk => by rw [hfx]; exact hAb _ (mul_nonneg ha hqx.le) k hk) hfb
  have heq : g ∘ f = fun y => SmoothCutoffs.scaledCutoff a (q y) := by
    funext y
    simp only [Function.comp_apply, g, f, SmoothCutoffs.scaledCutoff, smul_eq_mul]
    congr 1
    field_simp
  rw [heq] at hb
  calc
    _ ≤ m.factorial * A * (D / q x) ^ m := hb
    _ = (m.factorial * A * D ^ m) * q x ^ (-(m : ℝ)) := by
      rw [div_pow, Real.rpow_neg hqx.le, Real.rpow_natCast]
      ring

theorem smul_jet_bound {f : E → ℝ} {g : E → V} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖ := by
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hx (nat_le_infty m)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hb

/-- All jets of the composed cutoff vanish on and beyond its boundary.
This does not require the coordinate to cross that boundary locally. -/
theorem composedCutoff_jets_zero {U : Set E} (hU : IsOpen U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) {x : E} (hx : x ∈ U) (a : ℝ)
    (haq : 1 ≤ a * q x) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y)) x = 0 := by
  let f : E → ℝ := fun y => a * q y
  have hf : ContDiffOn ℝ ∞ f U := contDiffOn_const.mul hq
  let D := finiteBound (fun k => ‖iteratedFDeriv ℝ k f x‖) m
  have hD : 1 ≤ D := finiteBound_one_le _ _
  have hb := composition_jet_bound hU hf SmoothCutoffs.cutoff_contDiff hx m
    (C := 0) (D := D)
    (fun k _ => by rw [cutoff_jets_zero_of_one_le k haq, norm_zero])
    (fun k hk hkm => (le_finiteBound _ hkm).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hD hk))
  apply norm_eq_zero.mp
  simp only [mul_zero, zero_mul] at hb
  exact le_antisymm hb (norm_nonneg _)

theorem cut_product_jets_zero {U : Set E} (hU : IsOpen U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) {A : E → V} (hA : ContDiffOn ℝ ∞ A U)
    {x : E} (hx : x ∈ U) (a : ℝ) (haq : 1 ≤ a * q x) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) x = 0 := by
  have hb := smul_jet_bound hU
    ((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq) hA hx m
  simp only [Function.comp_def, composedCutoff_jets_zero hU hq hx a haq, norm_zero, mul_zero,
    zero_mul, Finset.sum_const_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

/-- The loss depends only on derivative order and the original loss function.
It is deliberately allowed to overestimate the finite maximum. -/
noncomputable def cutLoss (L : ℕ → ℝ) (m : ℕ) : ℝ := finiteBound L m + m

/-- The logarithmic exponent can depend on the stage, but never on its cutoff. -/
noncomputable def cutLog (p : ℕ → ℕ → ℝ) (j m : ℕ) : ℝ := finiteBound (p j) m

/-- Actual uncut jets, only on the portion `q ≤ 1` of the estimate carrier.
No condition is imposed on order zero of the stage sequence. -/
def RawStageBounds (q : E → ℝ) (A : ℕ → E → V) (g L : ℕ → ℝ)
    (C p : ℕ → ℕ → ℝ) (S : Set E) : Prop :=
  ∀ j, 1 ≤ j → ∀ m x, x ∈ S → q x ≤ 1 →
    ‖iteratedFDeriv ℝ m (A j) x‖ ≤
      C j m * (1 + |Real.log (q x)|) ^ (p j m) * q x ^ (g j - L m)

private theorem sum_choose_real (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = 2 ^ m := by
  exact_mod_cast Nat.sum_range_choose m

/-- Leibniz's formula converts the genuine raw jet bounds into uniform
cut-stage bounds.  The constant and logarithmic exponent are independent of
the arbitrary nonnegative cutoff parameter. -/
theorem cut_product_bound {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    {A : E → V} (hA : ContDiffOn ℝ ∞ A U)
    (Q C p L : ℕ → ℝ) (g : ℝ)
    (hcut : ∀ k a, 0 ≤ a → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖ ≤
        Q k * q x ^ (-(k : ℝ)))
    (hraw : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k A x‖ ≤
        C k * (1 + |Real.log (q x)|) ^ (p k) * q x ^ (g - L k))
    (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 ≤ a → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) x‖ ≤
        K * (1 + |Real.log (q x)|) ^ (finiteBound p m) * q x ^ (g - cutLoss L m) := by
  let CQ := finiteBound Q m
  let CA := finiteBound C m
  have hCQ : 0 < CQ := zero_lt_one.trans_le (finiteBound_one_le _ _)
  have hCA : 0 < CA := zero_lt_one.trans_le (finiteBound_one_le _ _)
  refine ⟨2 ^ m * CQ * CA, by positivity, ?_⟩
  intro a ha x hx hq1
  have hqx := hpos x hx
  let l : ℝ := 1 + |Real.log (q x)|
  have hl : 1 ≤ l := le_add_of_nonneg_right (abs_nonneg _)
  have hcut' : ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖ ≤
        CQ * q x ^ (-(i : ℝ)) := by
    intro i hi
    exact (hcut i a ha x hx hq1).trans
      (mul_le_mul_of_nonneg_right (le_finiteBound Q hi) (Real.rpow_nonneg hqx.le _))
  have hraw' : ∀ k ≤ m, ‖iteratedFDeriv ℝ k A x‖ ≤
      CA * l ^ (finiteBound p m) * q x ^ (g - L k) := by
    intro k hk
    apply (hraw k x hx hq1).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hqx.le _)
    calc
      C k * l ^ (p k) ≤ CA * l ^ (p k) :=
        mul_le_mul_of_nonneg_right (le_finiteBound C hk) (Real.rpow_nonneg (by positivity) _)
      _ ≤ CA * l ^ (finiteBound p m) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hl (le_finiteBound p hk)) hCA.le
  have hb := smul_jet_bound hU
    ((SmoothCutoffs.scaledCutoff_contDiff a).comp_contDiffOn hq) hA (hSU hx) m
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * CQ * CA *
        l ^ (finiteBound p m) * q x ^ (g - cutLoss L m) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hki : m - i ≤ m := Nat.sub_le _ _
      have hp : q x ^ (g - L (m - i) - (i : ℝ)) ≤ q x ^ (g - cutLoss L m) := by
        apply Real.rpow_le_rpow_of_exponent_ge hqx hq1
        have hL := le_finiteBound L hki
        have hi' : (i : ℝ) ≤ m := by exact_mod_cast him
        dsimp only [cutLoss]
        linarith
      calc
        _ ≤ (m.choose i : ℝ) * (CQ * q x ^ (-(i : ℝ))) *
            (CA * l ^ (finiteBound p m) * q x ^ (g - L (m - i))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hcut' i him) (Nat.cast_nonneg _)
          · exact hraw' (m - i) hki
          · exact norm_nonneg _
          · positivity
        _ = (m.choose i : ℝ) * CQ * CA * l ^ (finiteBound p m) *
            q x ^ (g - L (m - i) - (i : ℝ)) := by
          rw [show g - L (m - i) - (i : ℝ) = -(i : ℝ) + (g - L (m - i)) by ring,
            Real.rpow_add hqx]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2 ^ m * CQ * CA) * l ^ (finiteBound p m) * q x ^ (g - cutLoss L m) := by
      simp only [← Finset.sum_mul, sum_choose_real]

/-- One family of constants works for every possible choice of cutoff
parameters; these are derived from the uncut jets, not supplied as data. -/
theorem exists_cut_stage_constants {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (B : ℕ → ℝ)
    (hB : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ B k * q x ^ (1 - (k : ℝ)))
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (g L : ℕ → ℝ) (C p : ℕ → ℕ → ℝ)
    (hraw : RawStageBounds q A g L C p S) :
    ∃ K : ℕ → ℕ → ℝ, (∀ j m, 0 < K j m) ∧
      ∀ j, 1 ≤ j → ∀ m a, 0 ≤ a → ∀ x ∈ S, q x ≤ 1 →
        ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y) • A j y) x‖ ≤
          K j m * (1 + |Real.log (q x)|) ^ (cutLog p j m) * q x ^ (g j - cutLoss L m) := by
  have hc := fun m => cutoff_jet_bound hU
    (S := S ∩ {x | q x ≤ 1}) (fun _ hx => hSU hx.1) hq
    (fun x hx => hpos x hx.1) B (fun k x hx => hB k x hx.1 hx.2) m
  choose Q hQ hcut using hc
  have hcut' : ∀ k a, 0 ≤ a → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun y => SmoothCutoffs.scaledCutoff a (q y)) x‖ ≤
        Q k * q x ^ (-(k : ℝ)) := fun k a ha x hx hq1 => hcut k a ha x ⟨hx, hq1⟩
  have hK : ∀ j m, ∃ K : ℝ, 0 < K ∧ (1 ≤ j →
      ∀ a, 0 ≤ a → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y) • A j y) x‖ ≤
        K * (1 + |Real.log (q x)|) ^ (cutLog p j m) * q x ^ (g j - cutLoss L m)) := by
    intro j m
    by_cases hj : 1 ≤ j
    · obtain ⟨K, hK, hb⟩ := cut_product_bound hU hSU hq hpos (hA j hj)
        Q (C j) (p j) L (g j) hcut' (hraw j hj) m
      exact ⟨K, hK, fun _ => hb⟩
    · exact ⟨1, zero_lt_one, fun hj' => False.elim (hj hj')⟩
  choose K hK hb using hK
  exact ⟨K, hK, fun j hj m => hb j m hj⟩

/-- The scalar threshold estimate now applies to the actual differentiated
product.  Outside the threshold its jets vanish, including at the boundary. -/
theorem cut_product_bound_of_threshold {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    {A : E → V} (hA : ContDiffOn ℝ ∞ A U) (m : ℕ)
    {K P g L a ε : ℝ} (ha : 1 ≤ a) (hε : 0 ≤ ε)
    (hcut : ∀ c, 0 ≤ c → ∀ x ∈ S, q x ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff c (q y) • A y) x‖ ≤
        K * (1 + |Real.log (q x)|) ^ P * q x ^ (g - L))
    (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 / a →
      |DiagonalScale.logPowerWeight K P (g / 2) r| ≤ ε) :
    ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) x‖ ≤
        ε * q x ^ (g / 2 - L) := by
  intro x hx
  have hqx := hpos x hx
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  by_cases hqa : q x ≤ 1 / a
  · have hq1 : q x ≤ 1 := hqa.trans (by
      simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one ha)
    exact (hcut a ha0.le x hx hq1).trans ((le_abs_self _).trans
      (DiagonalScale.absorb_logarithmic_weight K P g L (q x) ε hqx (hsmall _ hqx hqa)))
  · have hprod : 1 ≤ a * q x := by
      have hh := (div_le_iff₀ ha0).mp (lt_of_not_ge hqa).le
      simpa only [mul_comm] using hh
    rw [cut_product_jets_zero hU hq hA (hSU hx) a hprod m, norm_zero]
    exact mul_nonneg hε (Real.rpow_nonneg hqx.le _)

/-- One numeric scale sequence controls every derivative budget `m ≤ j+2`
of every positive stage.  The actual cut-stage estimate is proved from the
raw estimates and the coordinate estimates. -/
theorem exists_diagonal_cut_bounds {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    (g L : ℕ → ℝ) (C p : ℕ → ℕ → ℝ)
    (hraw : RawStageBounds q A g L C p S) (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q A
        (fun j => g j / 2) (cutLoss L) S := by
  obtain ⟨K, hK, hb⟩ := exists_cut_stage_constants hU hSU hq hpos Bq hBq hA g L C p hraw
  obtain ⟨a, halower, hapos, hadouble, hamono, _, hasmall⟩ :=
    DiagonalScale.exists_diagonal_scales K (cutLog p) g hg lower
  refine ⟨a, halower, hapos, hadouble, hamono, SolenoidalDiagonal.realScales_tendsto hamono, ?_⟩
  intro j hj m hm x hx
  exact cut_product_bound_of_threshold hU hSU hq hpos (hA j hj) m
    (by exact_mod_cast hapos j) (by positivity) (hb j hj m) (hasmall j hj m hm) x hx

section FiniteFamilies

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

omit [Fintype ι] in
/-- A single doubling schedule for a finite heterogeneous family, such as
Cartesian stream potentials, direct angular fields, and scalar pressures.
The cutoff is applied directly to every component; no extra derivative is
introduced for components that are already velocity fields. -/
theorem exists_finite_diagonal_cut_bounds [Finite ι] {U S : Set E} (hU : IsOpen U) (hSU : S ⊆ U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ S, 0 < q x)
    (Bq : ℕ → ℝ)
    (hBq : ∀ k x, x ∈ S → q x ≤ 1 →
      ‖iteratedFDeriv ℝ k q x‖ ≤ Bq k * q x ^ (1 - (k : ℝ)))
    {A : ∀ i, ℕ → E → W i} (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) U)
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, RawStageBounds q (A i) g L (C i) (p i) S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ)) q (A i)
        (fun j => g j / 2) (cutLoss L) S := by
  classical
  let := Fintype.ofFinite ι
  classical
  choose K hK hb using fun i =>
    exists_cut_stage_constants hU hSU hq hpos Bq hBq (hA i) g L (C i) (p i) (hraw i)
  let Kall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |K i j m|
  let Pall : ℕ → ℕ → ℝ := fun j m => 1 + ∑ i, |cutLog (p i) j m|
  have hKall : ∀ j m, 0 < Kall j m := by
    intro j m
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (K i j m))
    dsimp only [Kall]
    linarith
  have hKle : ∀ i j m, K i j m ≤ Kall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (K i j m))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  have hPle : ∀ i j m, cutLog (p i) j m ≤ Pall j m := by
    intro i j m
    exact (le_abs_self _).trans ((Finset.single_le_sum
      (fun i _ => abs_nonneg (cutLog (p i) j m)) (Finset.mem_univ i)).trans
        (le_add_of_nonneg_left zero_le_one))
  obtain ⟨a, halower, hapos, hadouble, hamono, _, hasmall⟩ :=
    DiagonalScale.exists_diagonal_scales Kall Pall g hg lower
  refine ⟨a, halower, hapos, hadouble, hamono, SolenoidalDiagonal.realScales_tendsto hamono, ?_⟩
  intro i j hj m hm x hx
  apply cut_product_bound_of_threshold hU hSU hq hpos (hA i j hj) m
    (by exact_mod_cast hapos j) (by positivity) (K := Kall j m) (P := Pall j m)
    (g := g j) (L := cutLoss L m) ?_ (hasmall j hj m hm) x hx
  intro c hc y hy hq1
  apply (hb i j hj m c hc y hy hq1).trans
  have hlog : 1 ≤ 1 + |Real.log (q y)| := le_add_of_nonneg_right (abs_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hpos y hy).le _)
  calc
    _ ≤ Kall j m * (1 + |Real.log (q y)|) ^ (cutLog (p i) j m) :=
      mul_le_mul_of_nonneg_right (hKle i j m) (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (hPle i j m)) (hKall j m).le

end FiniteFamilies

/-- Remove the unused zeroth correction without imposing any regularity
or decay hypothesis on the value supplied at that index. -/
noncomputable def positiveStages (A : ℕ → E → V) (j : ℕ) (x : E) : V :=
  if j = 0 then 0 else A j x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ V] in
@[simp] theorem positiveStages_zero (A : ℕ → E → V) : positiveStages A 0 = 0 := by
  funext x
  simp [positiveStages]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem positiveStages_of_pos {A : ℕ → E → V} {j : ℕ} (hj : 1 ≤ j) :
    positiveStages A j = A j := by
  funext x
  simp only [positiveStages, ite_eq_right (by omega : j ≠ 0)]

theorem positiveStages_smooth {U : Set E} {A : ℕ → E → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U) (j : ℕ) :
    ContDiffOn ℝ ∞ (positiveStages A j) U := by
  by_cases hj : j = 0
  · rw [hj, positiveStages_zero]
    exact contDiffOn_const
  · rw [positiveStages_of_pos (by omega : 1 ≤ j)]
    exact hA j (by omega)

theorem positiveStages_cut_bounds {q : E → ℝ} {A : ℕ → E → V}
    {a : ℕ → ℝ} {g L : ℕ → ℝ} {S : Set E}
    (hb : DiagonalJetBounds.CutStageBounds a q A g L S) :
    DiagonalJetBounds.CutStageBounds a q (positiveStages A) g L S := by
  intro j hj m hm x hx
  have he : SolenoidalDiagonal.cutStage a q (positiveStages A) j =
      SolenoidalDiagonal.cutStage a q A j := by
    funext y
    simp only [SolenoidalDiagonal.cutStage, positiveStages_of_pos hj]
  rw [he]
  exact hb j hj m hm x hx

/-- The selected positive-stage series is the actual locally finite sum
and is smooth on the full positive-coordinate domain. -/
theorem positive_sum_smooth {U : Set E} (hU : IsOpen U) {q : E → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hpos : ∀ x ∈ U, 0 < q x)
    {A : ℕ → E → V} (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) U)
    {a : ℕ → ℕ} (ha : StrictMono a) :
    ContDiffOn ℝ ∞ (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) q
      (positiveStages A)) U :=
  SolenoidalDiagonal.potentialSum_contDiffOn (SolenoidalDiagonal.realScales_tendsto ha)
    hU hpos hq (positiveStages_smooth hA)

omit [NormedSpace ℝ E] in
/-- Beyond strict cutoff support the product has a zero germ, regardless
of any arbitrary totalization of the raw field there. -/
theorem cut_product_eventually_zero {q : E → ℝ} {x : E} (hq : ContinuousAt q x)
    (A : E → V) (a : ℝ) (haq : 1 < a * q x) :
    (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) =ᶠ[𝓝 x] (fun _ => 0) := by
  have hc := (SmoothCutoffs.scaledCutoff_eventually_zero
    (haq.trans_le (le_abs_self _))).comp_tendsto hq
  filter_upwards [hc] with y hy
  simp only [Function.comp_apply] at hy
  simp only [hy, zero_smul]

/-- Cutting strictly inside the valid `q`-domain gives an actual smooth
zero extension.  Smoothness of the uncut totalization outside it is unused. -/
theorem cut_product_smooth_of_sublevel {U : Set E} (hU : IsOpen U)
    {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) {A : E → V} {qbig a : ℝ}
    (hA : ContDiffOn ℝ ∞ A (U ∩ {x | q x < qbig}))
    (ha : 0 < a) (hgap : 1 < a * qbig) :
    ContDiffOn ℝ ∞ (fun y => SmoothCutoffs.scaledCutoff a (q y) • A y) U := by
  have hsmall : IsOpen (U ∩ {x | q x < qbig}) :=
    hq.continuousOn.isOpen_inter_preimage hU isOpen_Iio
  intro x hx
  have hqx := hq.contDiffAt (hU.mem_nhds hx)
  by_cases hs : q x < qbig
  · exact (((SmoothCutoffs.scaledCutoff_contDiff a).contDiffAt.comp x hqx).smul
      (hA.contDiffAt (hsmall.mem_nhds ⟨hx, hs⟩))).contDiffWithinAt
  · have hg := cut_product_eventually_zero hqx.continuousAt A a
      (hgap.trans_le (mul_le_mul_of_nonneg_left (le_of_not_gt hs) ha.le))
    exact (contDiffAt_const.congr_of_eventuallyEq hg).contDiffWithinAt

end General

section PhysicalCoordinate

open ProblemStatement

/-- `q` is independent of the radial coordinate.  Using this linear map
avoids charging spurious derivatives of the squared physical radius. -/
noncomputable def physicalProjection : SpaceTime →L[ℝ] PhysicalCoordinateBounds.Point :=
  (ContinuousLinearMap.fst ℝ ℝ Space).prod
    ((0 : SpaceTime →L[ℝ] ℝ).prod
      ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)))

@[simp] theorem physicalProjection_apply (w : SpaceTime) :
    physicalProjection w = (w.1, (0, w.2 2)) := rfl

theorem physicalQ_linear_composition (h : ℝ) :
    PhysicalWaveSum.physicalQ h =
      PhysicalCoordinateBounds.physicalQ (2 * h) ∘ physicalProjection := rfl

/-- The actual Cartesian implicit similarity coordinate has one power of
loss per derivative.  No bound on the physical radius is required. -/
theorem physicalQ_jet_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (PhysicalWaveSum.physicalQ h) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (1 - (m : ℝ)) := by
  have ha : 0 < 2 * h := by positivity
  have ha1 : 2 * h < 1 := by linarith
  obtain ⟨C, hC, hb⟩ := PhysicalCoordinateBounds.physical_q_derivative_bound ha ha1 0 0 1 m
  refine ⟨C * (‖physicalProjection‖ + 1) ^ m, by positivity, ?_⟩
  intro w hw hq1
  have hU : IsOpen {p : PhysicalCoordinateBounds.Point | p.1 < 1} :=
    isOpen_lt continuous_fst continuous_const
  have hq : ContDiffOn ℝ ∞ (PhysicalCoordinateBounds.physicalQ (2 * h))
      {p : PhysicalCoordinateBounds.Point | p.1 < 1} :=
    fun p hp => (PhysicalCoordinateBounds.physicalQ_contDiffAt ha ha1 hp).contDiffWithinAt
  have hlin := PhysicalGraphBounds.norm_jet_comp_linear hU hq physicalProjection
    (x := w) hw m
  rw [← physicalQ_linear_composition] at hlin
  have hzero : PhysicalCoordinateBounds.physicalX (2 * h) (physicalProjection w) ∈ Icc 0 0 := by
    simp only [PhysicalCoordinateBounds.physicalX, Function.comp_apply,
      PhysicalCoordinateBounds.xCoord, PhysicalCoordinateBounds.timeShift,
      physicalProjection_apply, zero_div, mem_Icc, le_refl, and_self]
  have hqb := hb (physicalProjection w) hw hq1 hzero
  have hpow : ‖physicalProjection‖ ^ m ≤ (‖physicalProjection‖ + 1) ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right zero_le_one) m
  have hpos := PhysicalWaveSum.physicalQ_pos hh hh1 hw
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (PhysicalCoordinateBounds.physicalQ (2 * h))
        (physicalProjection w)‖ * ‖physicalProjection‖ ^ m := hlin
    _ ≤ (C * PhysicalWaveSum.physicalQ h w ^ (1 - (m : ℝ))) *
        (‖physicalProjection‖ + 1) ^ m :=
      mul_le_mul hqb hpow (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

theorem physical_cutoff_jet_bound {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m
        (fun z => SmoothCutoffs.scaledCutoff a (PhysicalWaveSum.physicalQ h z)) w‖ ≤
          C * PhysicalWaveSum.physicalQ h w ^ (-(m : ℝ)) := by
  choose B hB hb using physicalQ_jet_bound hh hh1
  obtain ⟨C, hC, hc⟩ := cutoff_jet_bound PhysicalWaveSum.preterminal_open
    (S := PhysicalWaveSum.preterminal ∩ {w | PhysicalWaveSum.physicalQ h w ≤ 1})
    (fun _ hw => hw.1)
    (fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt)
    (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) B
    (fun k w hw => hb k w hw.1 hw.2) m
  exact ⟨C, hC, fun a ha w hw hq1 => hc a ha w ⟨hw, hq1⟩⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual physical cutoff stages and their single selected schedule.
The only stage estimate premise concerns uncut physical derivatives. -/
theorem exists_physical_diagonal_cut_bounds {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ℕ → SpaceTime → V}
    (hA : ∀ j, 1 ≤ j → ContDiffOn ℝ ∞ (A j) PhysicalWaveSum.preterminal)
    (g L : ℕ → ℝ) (C p : ℕ → ℕ → ℝ)
    (hraw : RawStageBounds (PhysicalWaveSum.physicalQ h) A g L C p S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) A (fun j => g j / 2) (cutLoss L) S := by
  choose B hB hb using physicalQ_jet_bound hh hh1
  exact exists_diagonal_cut_bounds PhysicalWaveSum.preterminal_open hS
    (fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt)
    (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw)) B
    (fun k w hw hq1 => hb k w (hS hw) hq1) hA g L C p hraw hg lower

variable {ι : Type*} [Fintype ι] {W : ι → Type*}
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

omit [Fintype ι] in
/-- The same actual implicit coordinate and one unchanged schedule for all
finite stream, direct-field, and pressure components. -/
theorem exists_physical_finite_diagonal_cut_bounds [Finite ι] {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ∀ i, ℕ → SpaceTime → W i}
    (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) PhysicalWaveSum.preterminal)
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, RawStageBounds (PhysicalWaveSum.physicalQ h) (A i) g L (C i) (p i) S)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) (A i) (fun j => g j / 2) (cutLoss L) S := by
  classical
  let := Fintype.ofFinite ι
  choose B hB hb using physicalQ_jet_bound hh hh1
  exact exists_finite_diagonal_cut_bounds PhysicalWaveSum.preterminal_open hS
    (fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt)
    (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw)) B
    (fun k w hw hq1 => hb k w (hS hw) hq1) hA g L C p hraw hg lower

omit [Fintype ι] in
/-- The common case supplied by physical-copy estimates: the uncut bounds
have no logarithmic factor and their constants are existential.  The same
constructed sequence controls all positive components and gives smooth
actual sums on the entire preterminal spacetime domain. -/
theorem exists_physical_positive_sums_of_power [Finite ι] {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ∀ i, ℕ → SpaceTime → W i}
    (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) PhysicalWaveSum.preterminal)
    (g L : ℕ → ℝ)
    (hraw : ∀ i j, 1 ≤ j → ∀ m, ∃ C : ℝ, ∀ w ∈ S,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (A i j) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g j - L m))
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
          (PhysicalWaveSum.physicalQ h) (positiveStages (A i))
          (fun j => g j / 2) (cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h) (positiveStages (A i))) PhysicalWaveSum.preterminal := by
  classical
  let := Fintype.ofFinite ι
  have hex : ∀ i j m, ∃ C : ℝ, 1 ≤ j → ∀ w ∈ S,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (A i j) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g j - L m) := by
    intro i j m
    by_cases hj : 1 ≤ j
    · obtain ⟨C, hb⟩ := hraw i j hj m
      exact ⟨C, fun _ => hb⟩
    · exact ⟨0, fun hj' => False.elim (hj hj')⟩
  choose C hC using hex
  have hb : ∀ i, RawStageBounds (PhysicalWaveSum.physicalQ h) (A i) g L (C i)
      (fun _ _ => 0) S := by
    intro i j hj m w hw hq1
    simpa only [Real.rpow_zero, mul_one] using hC i j m hj w hw hq1
  obtain ⟨a, halower, hapos, hadouble, hamono, hatop, hab⟩ :=
    exists_physical_finite_diagonal_cut_bounds hh hh1 hS hA g L C (fun _ _ _ => 0) hb hg lower
  refine ⟨a, halower, hapos, hadouble, hamono, hatop, fun i => ?_⟩
  exact ⟨positiveStages_cut_bounds (hab i),
    positive_sum_smooth PhysicalWaveSum.preterminal_open
      (fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt)
      (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw) (hA i) hamono⟩

/-- The genuine open validity region for locally constructed raw stages. -/
noncomputable def physicalSublevel (h qbig : ℝ) : Set SpaceTime :=
  PhysicalWaveSum.preterminal ∩ {w | PhysicalWaveSum.physicalQ h w < qbig}

theorem physicalSublevel_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (qbig : ℝ) :
    IsOpen (physicalSublevel h qbig) := by
  have hc : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) PhysicalWaveSum.preterminal :=
    fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  exact hc.continuousOn.isOpen_inter_preimage PhysicalWaveSum.preterminal_open isOpen_Iio

omit [Fintype ι] in
/-- Local raw stages suffice.  The initial scale is chosen so every support
lies strictly inside `q < qbig`; the same actual cut products then extend
smoothly by zero to all preterminal points.  This is the support extension
used in the manuscript before diagonal summation. -/
theorem exists_physical_local_diagonal_cut_bounds [Finite ι] {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hS : S ⊆ PhysicalWaveSum.preterminal)
    {A : ∀ i, ℕ → SpaceTime → W i}
    (hA : ∀ i j, 1 ≤ j → ContDiffOn ℝ ∞ (A i j) (physicalSublevel h qbig))
    (g L : ℕ → ℝ) (C p : ι → ℕ → ℕ → ℝ)
    (hraw : ∀ i, RawStageBounds (PhysicalWaveSum.physicalQ h) (A i) g L (C i) (p i)
      (S ∩ physicalSublevel h qbig))
    (hg : ∀ j, 1 ≤ j → 0 < g j) (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      ∀ i, DiagonalJetBounds.CutStageBounds (fun j => (a j : ℝ))
          (PhysicalWaveSum.physicalQ h) (positiveStages (A i))
          (fun j => g j / 2) (cutLoss L) S ∧
        ContDiffOn ℝ ∞
          (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
            (PhysicalWaveSum.physicalQ h) (positiveStages (A i))) PhysicalWaveSum.preterminal := by
  classical
  let := Fintype.ofFinite ι
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) PhysicalWaveSum.preterminal :=
    fun w hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).contDiffWithinAt
  have hU := physicalSublevel_open hh hh1 qbig
  choose B hB hb using physicalQ_jet_bound hh hh1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hqbig
  obtain ⟨a, halower, hapos, hadouble, hamono, hatop, hab⟩ :=
    exists_finite_diagonal_cut_bounds hU (S := S ∩ physicalSublevel h qbig)
      (fun _ hw => hw.2) (hq.mono inter_subset_left)
      (fun w hw => PhysicalWaveSum.physicalQ_pos hh hh1 hw.2.1) B
      (fun k w hw hq1 => hb k w hw.2.1 hq1) hA g L C p hraw hg (max lower (n + 1))
  have hrecip : ∀ j, 1 / (a j : ℝ) < qbig := by
    intro j
    have haj : n + 1 ≤ a j := ((le_max_right lower (n + 1)).trans halower).trans
      (hamono.monotone (Nat.zero_le j))
    have hle : 1 / (a j : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast Nat.succ_pos n) (by exact_mod_cast haj)
    exact hle.trans_lt (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  have hgap : ∀ j, 1 < (a j : ℝ) * qbig := by
    intro j
    have hp : (0 : ℝ) < a j := by exact_mod_cast hapos j
    simpa only [mul_comm] using (div_lt_iff₀ hp).mp (hrecip j)
  refine ⟨a, (le_max_left lower (n + 1)).trans halower, hapos, hadouble,
    hamono, hatop, hrecip, fun i => ⟨?_, ?_⟩⟩
  · intro j hj m hm w hw
    by_cases hu : w ∈ physicalSublevel h qbig
    · exact positiveStages_cut_bounds (hab i) j hj m hm w ⟨hw, hu⟩
    · have hlarge : qbig ≤ PhysicalWaveSum.physicalQ h w :=
        le_of_not_gt (fun hsmall => hu ⟨hS hw, hsmall⟩)
      have hp : (0 : ℝ) < a j := by exact_mod_cast hapos j
      have hz := cut_product_eventually_zero
        (PhysicalWaveSum.physicalQ_smoothAt hh hh1 (hS hw)).continuousAt
        (positiveStages (A i) j) (a j)
        ((hgap j).trans_le (mul_le_mul_of_nonneg_left hlarge hp.le))
      have hjz := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hz m).self_of_nhds
      change ‖iteratedFDeriv ℝ m
        (fun z => SmoothCutoffs.scaledCutoff (a j) (PhysicalWaveSum.physicalQ h z) •
          positiveStages (A i) j z) w‖ ≤ _
      rw [hjz, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (by positivity)
        (Real.rpow_nonneg (PhysicalWaveSum.physicalQ_pos hh hh1 (hS hw)).le _)
  · have hstage : ∀ j, ContDiffOn ℝ ∞
        (SolenoidalDiagonal.cutStage (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
          (positiveStages (A i)) j) PhysicalWaveSum.preterminal := by
      intro j
      exact cut_product_smooth_of_sublevel PhysicalWaveSum.preterminal_open hq
        (positiveStages_smooth (hA i) j)
        (by change (0 : ℝ) < (a j : ℝ); exact_mod_cast hapos j) (hgap j)
    intro w hw
    have hloc := SolenoidalDiagonal.eventually_zero_tail hatop
      (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw).continuousAt
      (PhysicalWaveSum.physicalQ_pos hh hh1 hw) (positiveStages (A i))
    exact (DiagonalJetBounds.tsum_jet_identity hloc
      (fun j => (hstage j).contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds
          hw))).1.contDiffWithinAt

end PhysicalCoordinate

end NavierStokes.CutStageEstimates
