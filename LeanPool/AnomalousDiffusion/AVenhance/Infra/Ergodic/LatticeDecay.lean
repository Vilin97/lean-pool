/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.BasicL1
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Exponential sums on integer frequency lattices -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

noncomputable section

/-- Exponential weights in one integer variable are summable. -/
theorem summable_exp_neg_abs_int {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => Real.exp (-a * |(z : ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have h := Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)
    simpa [abs_of_nonneg, mul_comm] using h
  · have h := Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)
    simpa [Int.cast_neg, abs_of_nonpos, mul_comm] using h

theorem LatticeDecay.summable_exp_neg_piNorm_aux : ∀ d : ℕ, ∀ {a : ℝ},
    0 < a → Summable (fun k : Fin d → ℤ => Real.exp (-a * ‖k‖)) := by
  intro d
  induction d with
  | zero =>
      intro a ha
      exact Summable.of_finite
  | succ d ih =>
      intro a ha
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)
      have hInt : Summable (fun z : ℤ => Real.exp (-(a / 2) * |(z : ℝ)|)) :=
        summable_exp_neg_abs_int (by positivity)
      have hTail : Summable (fun k : Fin d → ℤ => Real.exp (-(a / 2) * ‖k‖)) :=
        ih (by positivity)
      let p : ℤ → ℝ := fun z => Real.exp (-(a / 2) * |(z : ℝ)|)
      let q : (Fin d → ℤ) → ℝ := fun k => Real.exp (-(a / 2) * ‖k‖)
      let prodTerm : ℤ × (Fin d → ℤ) → ℝ := fun x => p x.1 * q x.2
      have hprod : Summable prodTerm := by
        rw [summable_prod_of_nonneg (f := prodTerm) (by
          intro x
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
        constructor
        · intro z
          simpa [prodTerm, p, q] using hTail.mul_left (p z)
        · have houter : Summable (fun z : ℤ => p z * ∑' k : Fin d → ℤ, q k) :=
            hInt.mul_right _
          apply houter.congr
          intro z
          change p z * ∑' k : Fin d → ℤ, q k =
            ∑' k : Fin d → ℤ, p z * q k
          rw [← tsum_mul_left]
      have hbound : ∀ x : ℤ × (Fin d → ℤ),
          Real.exp (-a * ‖e x‖) ≤ prodTerm x := by
        intro x
        let k := e x
        have hfirst : |(x.1 : ℝ)| ≤ ‖k‖ := by
          simpa [Int.norm_eq_abs, k, e, Fin.consEquiv_apply] using norm_le_pi_norm k 0
        have htail : ‖x.2‖ ≤ ‖k‖ := by
          apply (pi_norm_le_iff_of_nonneg (norm_nonneg k)).2
          intro i
          simpa [k, e, Fin.consEquiv_apply] using norm_le_pi_norm k i.succ
        have hsum : (a / 2) * |(x.1 : ℝ)| + (a / 2) * ‖x.2‖ ≤ a * ‖k‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ a / 2),
            mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ a / 2)]
        have hexp : -a * ‖k‖ ≤
            (-(a / 2) * |(x.1 : ℝ)|) + (-(a / 2) * ‖x.2‖) := by
          nlinarith [hsum]
        calc
          Real.exp (-a * ‖k‖) ≤
              Real.exp ((-(a / 2) * |(x.1 : ℝ)|) + (-(a / 2) * ‖x.2‖)) :=
            Real.exp_le_exp.mpr hexp
          _ = prodTerm x := by simp [prodTerm, p, q, Real.exp_add]
      have hsmall : Summable (fun x : ℤ × (Fin d → ℤ) => Real.exp (-a * ‖e x‖)) :=
        hprod.of_nonneg_of_le (by intro x; exact Real.exp_nonneg _) hbound
      have hequiv : Summable (fun k : Fin (d + 1) → ℤ => Real.exp (-a * ‖k‖)) :=
        e.summable_iff.mp (by simpa [Function.comp_def, e] using hsmall)
      exact hequiv

/-- The exponential lattice sum converges in every finite dimension. -/
theorem summable_exp_neg_piNorm {d : ℕ} {a : ℝ} (ha : 0 < a) :
    Summable (fun k : Fin d → ℤ => Real.exp (-a * ‖k‖)) :=
  LatticeDecay.summable_exp_neg_piNorm_aux d ha

/-- Quotient coordinates for the frequency sublattice `N ℤ^d`. -/
noncomputable def LatticeDecay.fastFrequencyQuotient {d N : ℕ}
    (k : {k : Fin d → ℤ // IsFastFrequency N k}) : Fin d → ℤ :=
  fun i => Classical.choose (k.property i)

theorem LatticeDecay.fastFrequency_eq_scale {d N : ℕ}
    (k : {k : Fin d → ℤ // IsFastFrequency N k}) :
    k.val = fun i => (N : ℤ) * LatticeDecay.fastFrequencyQuotient k i := by
  funext i
  exact Classical.choose_spec (k.property i)

theorem LatticeDecay.fastFrequencyQuotient_injective {d N : ℕ} :
    Function.Injective (LatticeDecay.fastFrequencyQuotient (d := d) (N := N)) := by
  intro k l h
  apply Subtype.ext
  rw [LatticeDecay.fastFrequency_eq_scale k, LatticeDecay.fastFrequency_eq_scale l, h]

theorem LatticeDecay.norm_fastFrequency_eq {d N : ℕ}
    (k : {k : Fin d → ℤ // IsFastFrequency N k}) :
    ‖k.val‖ = (N : ℝ) * ‖LatticeDecay.fastFrequencyQuotient k‖ := by
  rw [LatticeDecay.fastFrequency_eq_scale]
  have hsmul : (fun i => (N : ℤ) * LatticeDecay.fastFrequencyQuotient k i) =
      (N : ℤ) • LatticeDecay.fastFrequencyQuotient k := by
    funext i
    simp
  rw [hsmul, norm_smul]
  simp

theorem LatticeDecay.norm_ge_one_of_ne_zero_intVector {d : ℕ}
    {k : Fin d → ℤ} (hk : k ≠ 0) : 1 ≤ ‖k‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, k i ≠ 0 := by
    by_contra h
    push Not at h
    apply hk
    funext i
    exact h i
  have hcoord : (1 : ℝ) ≤ ‖k i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact hcoord.trans (norm_le_pi_norm k i)

/-- The nonzero exponential tail on `N ℤ^d` has a dimension-only prefactor.
The scale condition is `tN ≥ 1/512`; the estimate decays as `exp(-tN/2)`. -/
theorem fastFrequency_expTail_le {d N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (hscale : 1 / 512 ≤ t * (N : ℝ)) :
    (∑' k : Fin d → ℤ,
      if k = 0 then 0 else if IsFastFrequency N k then Real.exp (-t * ‖k‖) else 0) ≤
      (∑' ℓ : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖)) *
        Real.exp (-(t * (N : ℝ)) / 2) := by
  classical
  let s : Set (Fin d → ℤ) := {k | k ≠ 0 ∧ IsFastFrequency N k}
  let s' : Set (Fin d → ℤ) := {ℓ | ℓ ≠ 0}
  let f : (Fin d → ℤ) → ℝ := fun k => Real.exp (-t * ‖k‖)
  let g : (Fin d → ℤ) → ℝ := fun ℓ => Real.exp (-(t * (N : ℝ)) * ‖ℓ‖)
  have hgsummable : Summable g := by
    apply summable_exp_neg_piNorm
    exact mul_pos ht (by exact_mod_cast hN)
  let q : {k : Fin d → ℤ // k ∈ s} → s' := fun k =>
    ⟨LatticeDecay.fastFrequencyQuotient ⟨k.val, k.property.2⟩, by
      intro hq
      apply k.property.1
      have heq := LatticeDecay.fastFrequency_eq_scale ⟨k.val, k.property.2⟩
      have hkzero : k.val = 0 := by
        funext i
        rw [heq, hq]
        simp
      exact hkzero⟩
  have hqinj : Function.Injective q := by
    intro k l h
    apply Subtype.ext
    have hqval := congrArg (fun x : s' => (x : Fin d → ℤ)) h
    have hkl := LatticeDecay.fastFrequencyQuotient_injective hqval
    exact congrArg (fun x : {m : Fin d → ℤ // IsFastFrequency N m} => x.val) hkl
  have hgsub : Summable (fun ℓ : s' => g ℓ.val) :=
    hgsummable.comp_injective Subtype.val_injective
  have hfsummable : Summable (fun k : {k : Fin d → ℤ // k ∈ s} => f k.val) := by
    have hcomp := hgsub.comp_injective hqinj
    apply hcomp.congr
    intro k
    change g (q k).val = f k.val
    dsimp [f, g, q]
    have hnorm := LatticeDecay.norm_fastFrequency_eq ⟨k.val, k.property.2⟩
    rw [hnorm]
    congr 1
    ring
  have htailSub :
      (∑' k : Fin d → ℤ,
        if k = 0 then 0 else if IsFastFrequency N k then f k else 0) =
        ∑' k : {k : Fin d → ℤ // k ∈ s}, f k.val := by
    calc
      _ = ∑' k : Fin d → ℤ, s.indicator f k := by
        apply tsum_congr
        intro k
        by_cases hk0 : k = 0 <;> by_cases hfast : IsFastFrequency N k <;>
          simp [s, f, hk0, hfast]
      _ = ∑' k : {k : Fin d → ℤ // k ∈ s}, f k.val := (tsum_subtype s f).symm
  have hsuble :
      (∑' k : {k : Fin d → ℤ // k ∈ s}, f k.val) ≤ ∑' ℓ : s', g ℓ.val := by
    apply hfsummable.tsum_le_tsum_of_inj q hqinj
      (fun _ _ => Real.exp_nonneg _)
    · intro k
      change f k.val ≤ g (q k).val
      dsimp [f, g, q]
      have hnorm := LatticeDecay.norm_fastFrequency_eq ⟨k.val, k.property.2⟩
      rw [hnorm]
      have harg : -t * ((N : ℝ) * ‖LatticeDecay.fastFrequencyQuotient ⟨k.val, k.property.2⟩‖) =
          -(t * (N : ℝ)) * ‖LatticeDecay.fastFrequencyQuotient ⟨k.val, k.property.2⟩‖ := by ring
      rw [harg]
    · exact hgsummable.comp_injective Subtype.val_injective
  have htailFast :
      (∑' ℓ : Fin d → ℤ, if ℓ = 0 then 0 else g ℓ) ≤
        (∑' ℓ : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖)) *
          Real.exp (-(t * (N : ℝ)) / 2) := by
    let aN : ℝ := t * (N : ℝ)
    let v : (Fin d → ℤ) → ℝ := fun ℓ =>
      Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖) * Real.exp (-aN / 2)
    have haN : 0 < aN := mul_pos ht (by exact_mod_cast hN)
    have hUs : Summable (fun ℓ : Fin d → ℤ => if ℓ = 0 then 0 else g ℓ) := by
      apply (summable_exp_neg_piNorm haN).of_nonneg_of_le
      · intro ℓ
        split_ifs <;> positivity
      · intro ℓ
        by_cases hzero : ℓ = 0
        · simp [hzero]
        · simp [hzero, g, aN]
    have hVs : Summable v := by
      simpa [v, aN] using
        (summable_exp_neg_piNorm (d := d) (a := (1 / 1024 : ℝ)) (by norm_num)).mul_right _
    have hv : ∀ ℓ : Fin d → ℤ,
        (if ℓ = 0 then 0 else g ℓ) ≤ v ℓ := by
      intro ℓ
      by_cases hzero : ℓ = 0
      · simp only [hzero, ↓reduceIte]
        positivity
      · have hnorm : 1 ≤ ‖ℓ‖ := LatticeDecay.norm_ge_one_of_ne_zero_intVector hzero
        have haNlower : (1 / 512 : ℝ) ≤ aN := hscale
        have hcoeff : 0 ≤ aN - 1 / 1024 := by linarith
        have hprod : 0 ≤ (aN - 1 / 1024) * (‖ℓ‖ - 1) :=
          mul_nonneg hcoeff (sub_nonneg.mpr hnorm)
        have hmain : aN / 2 ≤ (aN - 1 / 1024) * ‖ℓ‖ := by
          nlinarith [hprod, haNlower]
        have hsum : -aN * ‖ℓ‖ ≤ -(1 / 1024 : ℝ) * ‖ℓ‖ - aN / 2 := by
          nlinarith [hmain]
        simp only [hzero, ge_iff_le]
        calc
          Real.exp (-aN * ‖ℓ‖) ≤
              Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖ - aN / 2) :=
            Real.exp_le_exp.mpr hsum
          _ = v ℓ := by
            calc
              _ = Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖ + (-aN / 2)) := by
                congr 1
                ring
              _ = Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖) * Real.exp (-aN / 2) :=
                Real.exp_add _ _
              _ = v ℓ := rfl
    calc
      _ ≤ ∑' ℓ : Fin d → ℤ, v ℓ := Summable.tsum_le_tsum hv hUs hVs
      _ = (∑' ℓ : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖)) *
          Real.exp (-(t * (N : ℝ)) / 2) := by
        rw [tsum_mul_right]
  have htailSubtype :
      (∑' ℓ : s', g ℓ.val) =
        ∑' ℓ : Fin d → ℤ, if ℓ = 0 then 0 else g ℓ := by
    calc
      _ = ∑' ℓ : Fin d → ℤ, s'.indicator g ℓ := tsum_subtype s' g
      _ = _ := by
        apply tsum_congr
        intro ℓ
        by_cases hℓ : ℓ = 0 <;> simp [s', hℓ]
  calc
    _ = ∑' k : {k : Fin d → ℤ // k ∈ s}, f k.val := htailSub
    _ ≤ ∑' ℓ : s', g ℓ.val := hsuble
    _ ≤ (∑' ℓ : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖ℓ‖)) *
        Real.exp (-(t * (N : ℝ)) / 2) := by
      calc
        _ = ∑' ℓ : Fin d → ℤ, if ℓ = 0 then 0 else g ℓ := htailSubtype
        _ ≤ _ := htailFast

end

end AVenhance.Infra.Ergodic
