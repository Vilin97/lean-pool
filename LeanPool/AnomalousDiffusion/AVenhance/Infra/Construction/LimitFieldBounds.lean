/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Conditional hypotheses for the limit-field argument in §2.

`StreamRegularityBounds` is exactly the three estimates in the first part of the stream-regularity
    estimates:
the increment estimate at every order, the estimate on `Φ m` for `n ≥ 2`,
and the low-order estimate on `Φ m` for `n ≤ 1`.  It is data, not an import
of the draft theorem.  `StreamVelocityTimeIncrementBound` isolates the one
additional quantitative input used below for temporal Hölder continuity; it
is the mean-value consequence of the estimate obtained by differentiating
the recursion in (e.psi.recursion.partial.t).
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- The explicit estimates supplied by the stream-regularity estimates (part (i)), with the same
    constant `C` in
its low-order estimate.  The order ranges match the corrected
statement. -/
def StreamRegularityBounds {β : ℝ} (C : ℝ) (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
    (∀ n : ℕ,
      barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
        ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)) ∧
    (∀ n : ℕ, 2 ≤ n →
      barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
    (∀ n : ℕ, n ≤ 1 →
      barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (C * epsilon β I.Λ m ^ n))

theorem LimitFieldBounds.epsilon_pos_for_ingredients {β : ℝ} (I : Ingredients β) (m : ℕ) :
    0 < epsilon β I.Λ m :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le

theorem LimitFieldBounds.continuous_norm_le_of_ae_le {f : Vec 2 → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(volume : Measure (Vec 2)), ‖f x‖ₑ ≤ ENNReal.ofReal B) :
    ∀ x, ‖f x‖ ≤ B := by
  intro x
  by_contra hx
  have hx' : B < ‖f x‖ := lt_of_not_ge hx
  let U : Set (Vec 2) := {y | B < ‖f y‖}
  have hUopen : IsOpen U := isOpen_lt continuous_const (Continuous.norm hf)
  have hUnonempty : U.Nonempty := ⟨x, hx'⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUnonempty
  have hnotU : ∀ᵐ y ∂(volume : Measure (Vec 2)), y ∉ U := by
    filter_upwards [h] with y hy
    intro hyU
    have hle : ENNReal.ofReal ‖f y‖ ≤ ENNReal.ofReal B := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hy
    have hle' : ‖f y‖ ≤ B := (ENNReal.ofReal_le_ofReal_iff hB).mp hle
    exact (not_lt_of_ge hle') hyU
  have hUzero : volume U = 0 := by
    simpa [ae_iff] using hnotU
  exact (ne_of_gt hUpos) hUzero

theorem LimitFieldBounds.barNorm_zero_eq_eLpNorm (R : ℝ) (f : Vec 2 → ℝ) :
    barNorm 0 R f = eLpNorm f ⊤ volume := by
  simp [barNorm]

/-- The zero-order stream-regularity seminorm controls the pointwise size of a continuous
function, since Lebesgue measure has positive measure on every nonempty open
set. -/
theorem barNorm_zero_pointwise {R B : ℝ} {f : Vec 2 → ℝ}
    (hf : Continuous f) (hB : 0 ≤ B)
    (h : barNorm 0 R f ≤ ENNReal.ofReal B) :
    ∀ x, ‖f x‖ ≤ B := by
  apply LimitFieldBounds.continuous_norm_le_of_ae_le hf hB
  have hess : eLpNormEssSup f (volume : Measure (Vec 2)) ≤ ENNReal.ofReal B := by
    have h' := h
    rw [LimitFieldBounds.barNorm_zero_eq_eLpNorm] at h'
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at h'
    exact h'
  exact (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun x hx => hx.trans hess

theorem LimitFieldBounds.barNorm_iterated_pointwise {n : ℕ} {R B : ℝ} {f : Vec 2 → ℝ}
    (i : Fin n → Fin 2)
    (hf : Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))))
    (hR : 0 < R) (hB : 0 ≤ B)
    (h : barNorm n R f ≤ ENNReal.ofReal B) :
    ∀ x, ‖iteratedFDeriv ℝ n f x (fun j => basisVec (i j))‖ ≤
      B / (((n + 1 : ℝ) ^ 2 / (n.factorial : ℝ)) * R⁻¹ ^ n) := by
  let g : Vec 2 → ℝ := fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))
  let c : ℝ := (n + 1 : ℝ) ^ 2 / (n.factorial : ℝ)
  let r : ℝ := c * R⁻¹ ^ n
  let W : ENNReal := ENNReal.ofReal c * (ENNReal.ofReal R)⁻¹ ^ n
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hW : W = ENNReal.ofReal r := by
    dsimp [W, r, c]
    rw [← ENNReal.ofReal_inv_of_pos hR, ← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hWpos : 0 < W := by rw [hW]; exact ENNReal.ofReal_pos.mpr hr
  have hcoord : eLpNorm g ⊤ volume ≤
      (⨆ j : Fin n → Fin 2,
        eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (j k))) ⊤ volume) :=
    le_iSup_of_le i le_rfl
  have hmul : W * eLpNorm g ⊤ volume ≤ ENNReal.ofReal B := by
    calc
      W * eLpNorm g ⊤ volume ≤ W *
          (⨆ j : Fin n → Fin 2,
            eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (j k))) ⊤ volume) :=
        mul_le_mul_of_nonneg_left hcoord (by positivity)
      _ = barNorm n R f := by simp [W, barNorm, c, mul_assoc]
      _ ≤ ENNReal.ofReal B := h
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hprodtop : W * eLpNorm g ⊤ volume ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hmul ENNReal.ofReal_lt_top)
  have hDtop : eLpNorm g ⊤ volume ≠ ⊤ := by
    intro htop
    apply hprodtop
    exact (ENNReal.mul_eq_top).2 (Or.inl ⟨hWne, htop⟩)
  have hDreal : r * (eLpNorm g ⊤ volume).toReal ≤ B := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmul
    rw [ENNReal.toReal_mul, hW, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal hB] at ht
    exact ht
  have hD' : eLpNorm g ⊤ volume ≤ ENNReal.ofReal (B / r) := by
    apply (ENNReal.toReal_le_toReal hDtop ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (div_nonneg hB hr.le)]
    exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using hDreal)
  have hess : eLpNormEssSup g volume ≤ ENNReal.ofReal (B / r) := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hD'
  have hae : ∀ᵐ x ∂(volume : Measure (Vec 2)),
      ‖g x‖ₑ ≤ ENNReal.ofReal (B / r) :=
    (ae_le_eLpNormEssSup (f := g) (μ := volume)).mono fun x hx => hx.trans hess
  have hBr : 0 ≤ B / r := div_nonneg hB hr.le
  have hpoint := LimitFieldBounds.continuous_norm_le_of_ae_le hf hBr hae
  intro x
  simpa [g, c, r] using hpoint x

theorem LimitFieldBounds.continuous_iteratedCoordinate {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n → Fin 2) :
    Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) := by
  have hT : Continuous (fun x => iteratedFDeriv ℝ n f x) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hf.contDiffAt).continuousAt_iteratedFDeriv (by simp)
  fun_prop

/-- Every member of an `IsStreamSeq` is admissible.  The positive indices
follow from the defining previous-index witness; index zero is the zero stream. -/
theorem streamSeq_isAdmissible {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) :
    ∀ m, IsAdmissibleStream (Φ m) := by
  intro m
  cases m with
  | zero =>
      rw [hseq.1]
      constructor
      · fun_prop
      · intro n k t x
        simp
  | succ m =>
      obtain ⟨hm, _⟩ := hseq.2 (m + 2) (by omega)
      simpa using hm

theorem LimitFieldBounds.streamSeq_slice_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hm := (streamSeq_isAdmissible hseq m).1
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (Φ m) (t, x))
  exact hm.comp hmap

/-- Pointwise order-zero increment estimate extracted from the stream-regularity seminorm.
This is the summable bound used for convergence of `Φ m`. -/
theorem streamIncrement_norm_le {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖Φ m t x - Φ (m - 1) t x‖ ≤ 10 * epsilon β I.Λ m ^ β := by
  let f : Vec 2 → ℝ := Φ m t - Φ (m - 1) t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (LimitFieldBounds.streamSeq_slice_contDiff hseq m t).sub
        (LimitFieldBounds.streamSeq_slice_contDiff hseq (m - 1) t)
  have heps := LimitFieldBounds.epsilon_pos_for_ingredients I m
  have hB : 0 ≤ 10 * epsilon β I.Λ m ^ β := by positivity
  have hbar := (hreg m hm t).1 0
  have hpoint := barNorm_zero_pointwise hf.continuous hB hbar x
  simpa [f] using hpoint

/-- First spatial derivatives of a stream increment have the scale used in
`e.C1beta.phi.m.m-1`. -/
theorem streamIncrement_deriv_coordinate_le {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m) (t : ℝ)
    (x : Vec 2) (i : Fin 2) :
    ‖fderiv ℝ (Φ m t - Φ (m - 1) t) x (basisVec i)‖ ≤
      320 * epsilon β I.Λ m ^ (β - 1) := by
  let f : Vec 2 → ℝ := Φ m t - Φ (m - 1) t
  let e : ℝ := epsilon β I.Λ m
  let R : ℝ := 2 ^ 7 * e⁻¹
  have he : 0 < e := LimitFieldBounds.epsilon_pos_for_ingredients I m
  have hR : 0 < R := by dsimp [R, e]; positivity
  have hB : 0 ≤ 10 * e ^ β := by positivity
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (LimitFieldBounds.streamSeq_slice_contDiff hseq m t).sub
        (LimitFieldBounds.streamSeq_slice_contDiff hseq (m - 1) t)
  have hbar : barNorm 1 R f ≤ ENNReal.ofReal (10 * e ^ β) := by
    simpa [R, e, f] using (hreg m hm t).1 1
  have hcoord := LimitFieldBounds.barNorm_iterated_pointwise (i := fun _ : Fin 1 => i)
    (LimitFieldBounds.continuous_iteratedCoordinate hf (fun _ => i)) hR hB hbar x
  have hraw : ‖fderiv ℝ f x (basisVec i)‖ ≤
      (10 * e ^ β) / (4 * R⁻¹) := by
    calc
      ‖fderiv ℝ f x (basisVec i)‖ ≤
          (10 * e ^ β) / ((1 + 1 : ℝ) ^ 2 * R⁻¹) := by
        simpa [f, iteratedFDeriv_one_apply, Nat.factorial] using hcoord
      _ = (10 * e ^ β) / (4 * R⁻¹) := by norm_num
  have hpow : e ^ β = e ^ (β - 1) * e := by
    calc
      e ^ β = e ^ ((β - 1) + 1) :=
        congrArg (fun r : ℝ => e ^ r) (by ring : β = (β - 1) + 1)
      _ = e ^ (β - 1) * e ^ 1 := Real.rpow_add he _ _
      _ = e ^ (β - 1) * e := by rw [Real.rpow_one]
  have hconst : (10 * e ^ β) / (4 * R⁻¹) = 320 * e ^ (β - 1) := by
    rw [hpow]
    dsimp [R]
    field_simp [ne_of_gt he]
    norm_num
  rw [hconst] at hraw
  simpa [e] using hraw

/-- Second spatial derivatives of a stream increment are bounded at scale
`ε_m^(β-2)`.  The displayed constant is deliberately rounded up. -/
theorem streamIncrement_secondCoordinate_le {β : ℝ} {C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m) (t : ℝ)
    (x : Vec 2) (i : Fin 2 → Fin 2) :
    ‖iteratedFDeriv ℝ 2 (Φ m t - Φ (m - 1) t) x
        (fun j => basisVec (i j))‖ ≤
      2 ^ 16 * epsilon β I.Λ m ^ (β - 2) := by
  let f : Vec 2 → ℝ := Φ m t - Φ (m - 1) t
  let e : ℝ := epsilon β I.Λ m
  let R : ℝ := 2 ^ 7 * e⁻¹
  have he : 0 < e := LimitFieldBounds.epsilon_pos_for_ingredients I m
  have hR : 0 < R := by dsimp [R, e]; positivity
  have hB : 0 ≤ 10 * e ^ β := by positivity
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (LimitFieldBounds.streamSeq_slice_contDiff hseq m t).sub
        (LimitFieldBounds.streamSeq_slice_contDiff hseq (m - 1) t)
  have hbar : barNorm 2 R f ≤ ENNReal.ofReal (10 * e ^ β) := by
    simpa [R, e, f] using (hreg m hm t).1 2
  have hcoord := LimitFieldBounds.barNorm_iterated_pointwise (i := i)
    (LimitFieldBounds.continuous_iteratedCoordinate hf i) hR hB hbar x
  have hraw : ‖iteratedFDeriv ℝ 2 f x (fun j => basisVec (i j))‖ ≤
      (10 * e ^ β) / (((2 + 1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * R⁻¹ ^ 2) := by
    simpa [f, Nat.factorial] using hcoord
  have hpowR : e ^ β = e ^ (β - 2) * e ^ ((2 : ℕ) : ℝ) := by
    calc
      e ^ β = e ^ ((β - 2) + 2) :=
        congrArg (fun r : ℝ => e ^ r) (by ring : β = (β - 2) + 2)
      _ = e ^ (β - 2) * e ^ ((2 : ℕ) : ℝ) :=
        Real.rpow_add he (β - 2) (2 : ℝ)
  have hpow : e ^ β = e ^ (β - 2) * e ^ 2 := by
    simpa only [Real.rpow_natCast] using hpowR
  have hconst : (10 * e ^ β) /
      (((2 + 1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * R⁻¹ ^ 2) ≤
      2 ^ 16 * e ^ (β - 2) := by
    rw [hpow]
    dsimp [R]
    have he2 : e ≠ 0 := ne_of_gt he
    field_simp [he2]
    norm_num
  exact hraw.trans hconst

/-- Minimal temporal input for the limit Holder estimate.  The source obtains
this from the differentiated recursion and the bound on `∂ₜ(b_m-b_{m-1})`;
the formulation below is precisely its mean-value consequence. -/
def StreamVelocityTimeIncrementBound {β : ℝ} (A : ℝ) (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ, ∀ x : Vec 2,
    ‖(streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x) -
        (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)‖ ≤
      A * epsilon β I.Λ m ^ (β - 2) * |s - t|

end AVenhance
