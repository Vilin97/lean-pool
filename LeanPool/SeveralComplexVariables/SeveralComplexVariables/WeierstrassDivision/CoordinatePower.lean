/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.AbsMax
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchyDerivatives
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ContourIntegral
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IdentityPrinciple
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.WeierstrassDivision.Basic

/-!
# Division by a coordinate power

Cauchy integrals construct division by `z.2 ^ d`, with a remainder of degree less than `d`. We
establish holomorphic dependence on the parameters, compatibility of the quotient at different
integration radii, uniqueness, and the uniform quotient estimate for bounded numerators.

The main result is `coordinatePower_division`, corresponding to
[Jakóbczak–Jarnicki][JakobczakJarnicki2021], Lemma 1.7.4.

## Main results

* `coordinatePower_division`: **Coordinate-power division
  ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.4).** Every holomorphic function on a polydisc
  has a unique quotient and polynomial remainder on division by `w^d`.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Complex Filter Finset Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {ι : Type*} [Fintype ι]

/-- Algebraic splitting of the Cauchy kernel into a polynomial part of degree `< d` and a remainder
with a factor `w^d`. -/
theorem weierstrass_kernel_identity (d : ℕ) {s w : ℂ} (hs : s ≠ 0) (hsw : s ≠ w) :
    (∑ j ∈ range d, w ^ j / s ^ (j + 1)) + w ^ d / (s ^ d * (s - w)) = (s - w)⁻¹ := by
  have hne : s - w ≠ 0 := sub_ne_zero.mpr hsw
  have hsne : s ^ d ≠ 0 := pow_ne_zero d hs
  have hgeom : ∑ i ∈ range d, s ^ i * w ^ (d - 1 - i) = (s ^ d - w ^ d) / (s - w) :=
    (Commute.all s w).geom_sum₂ hsw d
  have hpoly : ∑ j ∈ range d, w ^ j / s ^ (j + 1) = (s ^ d - w ^ d) / (s ^ d * (s - w)) := by
    have hreindex : ∑ i ∈ range d, w ^ (d - 1 - i) / s ^ (d - i) =
        ∑ j ∈ range d, w ^ j / s ^ (j + 1) := by
      refine Eq.trans ?_ (sum_range_reflect (fun j => w ^ j / s ^ (j + 1)) d)
      refine sum_congr rfl fun i hi => ?_
      have : d - 1 - i + 1 = d - i := by
        have := mem_range.mp hi
        omega
      rw [this]
    trans ∑ i ∈ range d, w ^ (d - 1 - i) / s ^ (d - i)
    · exact hreindex.symm
    trans (∑ i ∈ range d, s ^ i * w ^ (d - 1 - i)) / s ^ d
    · rw [sum_div]
      refine sum_congr rfl fun i hi => ?_
      have hle : i ≤ d := (mem_range.mp hi).le
      have hsi : s ^ (d - i) ≠ 0 := pow_ne_zero _ hs
      field_simp [hsne, hsi, pow_ne_zero i hs]
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    · rw [hgeom, div_div, mul_comm (s - w)]
  have hsplit : (s ^ d - w ^ d) / (s ^ d * (s - w)) + w ^ d / (s ^ d * (s - w)) =
      (s - w)⁻¹ := by
    rw [← add_div, sub_add_cancel, div_mul_eq_div_div, div_self hsne, one_div]
  rw [hpoly, hsplit]

/-- A jointly holomorphic function on a product remains holomorphic in the last coordinate. -/
theorem differentiableOn_snd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {R : ℝ} {g : E × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : E} (hz : z ∈ V) :
    DifferentiableOn ℂ (fun w => g (z, w)) (ball 0 R) := by
  intro w hw
  exact (hg (z, w) ⟨hz, hw⟩).comp w
    ((differentiableAt_const z).prodMk differentiableAt_id).differentiableWithinAt
    (fun t ht => ⟨hz, ht⟩)

/-- Restricting a product slice to a strictly smaller disc gives continuity up to the closed
disc. -/
theorem diffContOnCl_snd_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {R ρ : ℝ} {g : E × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : E} (hz : z ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) :
    DiffContOnCl ℂ (fun w => g (z, w)) (ball 0 ρ) := by
  refine ⟨(differentiableOn_snd_slice hg hz).mono (ball_subset_ball hρR.le), ?_⟩
  rw [closure_ball _ hρ.ne']
  exact hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
    (fun w hw => ⟨hz, closedBall_subset_ball hρR hw⟩)

/-- The Taylor coefficients of a polynomial remainder of degree less than `d`. -/
theorem iteratedDeriv_weierstrassRemainder_const {d : ℕ} (a : Fin d → ℂ) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => ∑ j : Fin d, a j * w ^ (j : ℕ)) 0 =
      if h : k < d then (k.factorial : ℂ) * a ⟨k, h⟩ else 0 := by
  have hsum := iteratedDeriv_fun_sum (I := Finset.univ) (n := k)
    (f := fun j : Fin d => fun w : ℂ => a j * w ^ (j : ℕ))
    (x := (0 : ℂ)) (fun _ _ => by fun_prop)
  simp only [hsum, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_single ⟨k, hk⟩]
    · simp [mul_comm]
    · intro j hj
      have hjk : k ≠ (j : ℕ) := by
        intro h
        exact hj (Fin.ext h.symm)
      simp [hjk]
  · apply Finset.sum_eq_zero
    intro j _
    have hjk : k ≠ (j : ℕ) :=
      ne_of_gt (j.isLt.trans_le (le_of_not_gt hk))
    simp [hjk]

/-- In coordinate-power division the remainder coefficients are the Taylor coefficients of the
last-coordinate slice. -/
theorem coeff_eq_iteratedDeriv_of_coordinatePower_division {d : ℕ}
    {V : Set (ι → ℂ)} {R : ℝ} {g q : (ι → ℂ) × ℂ → ℂ} {a : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a V R)
    (hR : 0 < R) {z : ι → ℂ} (hz : z ∈ V) (j : Fin d) :
    a j z = ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv (j : ℕ) (fun w => g (z, w)) 0 := by
  have hz0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hqA : AnalyticAt ℂ (fun w => q (z, w)) 0 :=
    ((differentiableOn_snd_slice h.differentiableOn_quotient hz).analyticOnNhd_of_finiteDimensional
      isOpen_ball) _ hz0
  have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ d) 0 := analyticAt_id.pow d
  have hprod : AnalyticAt ℂ (fun w => w ^ d * q (z, w)) 0 := hpow.mul hqA
  have hrem : AnalyticAt ℂ (fun w => ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 := by fun_prop
  have hid : (fun w => g (z, w)) =ᶠ[𝓝 0]
      (fun w => w ^ d * q (z, w) + ∑ k : Fin d, a k z * w ^ (k : ℕ)) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz0) fun w hw => by
      have hmem : (z, w) ∈ V ×ˢ ball (0 : ℂ) R := ⟨hz, hw⟩
      simpa [weierstrassRemainder, mul_comm] using h.eq hmem
  have hord : (d : ℕ∞) ≤ analyticOrderAt (fun w => w ^ d * q (z, w)) 0 := by
    have hmul := analyticOrderAt_mul hpow hqA
    have hpow' : analyticOrderAt (fun w : ℂ => w ^ d) 0 = d := by
      have h := analyticOrderAt_pow (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))) d
      simpa [analyticOrderAt_id, Pi.pow_def] using h
    have heq : analyticOrderAt (fun w => w ^ d * q (z, w)) 0 =
        analyticOrderAt ((fun w : ℂ => w ^ d) * fun w => q (z, w)) 0 := by
      congr 1
    rw [heq, hmul, hpow']
    exact le_self_add
  have hvan (k : ℕ) (hk : k < d) :
      iteratedDeriv k (fun w => w ^ d * q (z, w)) 0 = 0 :=
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hprod).mp hord) k hk
  have hder := hid.iteratedDeriv_eq (j : ℕ)
  have hadd :
      iteratedDeriv (j : ℕ)
          (fun w => w ^ d * q (z, w) + ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 =
        iteratedDeriv (j : ℕ) (fun w => w ^ d * q (z, w)) 0 +
          iteratedDeriv (j : ℕ) (fun w => ∑ k : Fin d, a k z * w ^ (k : ℕ)) 0 := by
    convert iteratedDeriv_add (n := (j : ℕ)) (x := (0 : ℂ))
      hprod.contDiffAt hrem.contDiffAt
  have hj : (j : ℕ) < d := j.isLt
  rw [hder, hadd, hvan _ hj, zero_add, iteratedDeriv_weierstrassRemainder_const, dite_eq_left hj]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j : ℕ))]

/-- Coordinate-power decompositions are unique: remainder coefficients are Taylor coefficients of
the last-coordinate slice, and the quotient is then recovered from the identity. Continuity
fills in the central fibre `w = 0`. -/
theorem unique_coordinatePower_division {d : ℕ} {V : Set (ι → ℂ)} {R : ℝ}
    {g q q' : (ι → ℂ) × ℂ → ℂ} {a a' : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a V R)
    (h' : IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q' a' V R)
    (hR : 0 < R) :
    EqOn q q' (V ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (a' j) V := by
  have ha (j : Fin d) : EqOn (a j) (a' j) V := by
    intro z hz
    exact (coeff_eq_iteratedDeriv_of_coordinatePower_division h hR hz j).trans
      (coeff_eq_iteratedDeriv_of_coordinatePower_division h' hR hz j).symm
  refine ⟨?_, ha⟩
  intro z hz
  have hrem : weierstrassRemainder a z = weierstrassRemainder a' z := by
    simp [weierstrassRemainder, ha _ hz.1]
  have hid : q z * z.2 ^ d + weierstrassRemainder a z =
      q' z * z.2 ^ d + weierstrassRemainder a' z :=
    (h.eq hz).symm.trans (h'.eq hz)
  have hmul : q z * z.2 ^ d = q' z * z.2 ^ d := by
    simpa [hrem] using hid
  by_cases hw : z.2 = 0
  · have hqA : AnalyticAt ℂ (fun w => q (z.1, w)) 0 :=
      ((differentiableOn_snd_slice h.differentiableOn_quotient
        hz.1).analyticOnNhd_of_finiteDimensional
        isOpen_ball) _ (mem_ball_self hR)
    have hqA' : AnalyticAt ℂ (fun w => q' (z.1, w)) 0 :=
      ((differentiableOn_snd_slice h'.differentiableOn_quotient
        hz.1).analyticOnNhd_of_finiteDimensional
        isOpen_ball) _ (mem_ball_self hR)
    have heq : (fun w => q (z.1, w)) =ᶠ[𝓝[≠] (0 : ℂ)] fun w => q' (z.1, w) := by
      have hball : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ ball (0 : ℂ) R :=
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hR))
      filter_upwards [hball, self_mem_nhdsWithin] with w hwball hw0
      have hwP : (z.1, w) ∈ V ×ˢ ball (0 : ℂ) R := ⟨hz.1, hwball⟩
      have hremw : weierstrassRemainder a (z.1, w) = weierstrassRemainder a' (z.1, w) := by
        simp [weierstrassRemainder, ha _ hz.1]
      have hidw : q (z.1, w) * w ^ d + weierstrassRemainder a (z.1, w) =
          q' (z.1, w) * w ^ d + weierstrassRemainder a' (z.1, w) :=
        (h.eq hwP).symm.trans (h'.eq hwP)
      have : q (z.1, w) * w ^ d = q' (z.1, w) * w ^ d := by
        simpa [hremw] using hidw
      exact mul_right_cancel₀ (pow_ne_zero d hw0) this
    have hlim : Tendsto (fun w => q (z.1, w)) (𝓝[≠] (0 : ℂ)) (𝓝 (q (z.1, 0))) :=
      hqA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim' : Tendsto (fun w => q' (z.1, w)) (𝓝[≠] (0 : ℂ)) (𝓝 (q' (z.1, 0))) :=
      hqA'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq0 : q (z.1, 0) = q' (z.1, 0) :=
      tendsto_nhds_unique (hlim.congr' heq) hlim'
    rw [show z = (z.1, (0 : ℂ)) from Prod.ext rfl hw]
    exact heq0
  · exact mul_right_cancel₀ (pow_ne_zero d hw) hmul

omit [Fintype ι] in
/-- Mixed last-coordinate derivatives at the origin are Cauchy integrals on a smaller circle. -/
theorem iteratedDeriv_snd_slice_circleIntegral [Finite ι]
    {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {z : ι → ℂ} (hz : z ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) (n : ℕ) :
    iteratedDeriv n (fun w => g (z, w)) 0 =
      (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s) := by
  classical
  let := Fintype.ofFinite ι
  simpa [sub_zero] using
    (diffContOnCl_snd_slice hg hz hρ hρR).iteratedDeriv_eq_circleIntegral_sub_zpow_mul
      hρ n (mem_ball_self hρ)

/-- The Cauchy integral of a jointly holomorphic kernel in the last coordinate remains holomorphic
in the parameters. -/
theorem analyticOnNhd_circleIntegral_snd_zpow_mul
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)) V := by
  have hfθ : ContinuousOn (fun s : ℂ => s ^ (-(n + 1 : ℤ))) (sphere 0 ρ) := by
    refine continuousOn_id.zpow₀ (-(n + 1 : ℤ)) fun s hs => Or.inl ?_
    intro h0
    have hsρ : ‖s‖ = ρ := by
      rw [← dist_zero_right]
      exact mem_sphere.mp hs
    have hs00 : s = 0 := h0
    rw [hs00, norm_zero] at hsρ
    linarith
  have hI := analyticOnNhd_circleIntegral_kernel_mul (E := ι → ℂ) hV hg hρ.le hfθ
    (fun z hz s hs =>
      ⟨hz, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs⟩)
  refine hI.congr hV fun z hz => ?_
  exact circleIntegral.integral_congr hρ.le fun s _ => mul_comm _ _

omit [Fintype ι] in
/-- The Taylor remainder coefficients of a last-coordinate slice depend holomorphically on the
remaining coordinates. -/
theorem differentiableOn_iteratedDeriv_snd_slice [Finite ι]
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hR : 0 < R) (n : ℕ) :
    DifferentiableOn ℂ (fun z => iteratedDeriv n (fun w => g (z, w)) 0) V := by
  classical
  let := Fintype.ofFinite ι
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) :=
    hg.analyticOnNhd_of_finiteDimensional (hV.prod isOpen_ball)
  have hI := analyticOnNhd_circleIntegral_snd_zpow_mul hV hgA hρ hρR n
  have hEq : EqOn (fun z => iteratedDeriv n (fun w => g (z, w)) 0)
      (fun z => (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)) V :=
    fun z hz => iteratedDeriv_snd_slice_circleIntegral hg hz hρ hρR n
  exact ((hI.const_smul (c := (n.factorial : ℂ) * (2 * Real.pi * I : ℂ)⁻¹)).congr hV
    (fun z hz => (hEq hz).symm)).differentiableOn

/-- Cauchy integral representing the Weierstrass quotient for division by `w^d`. -/
private def weierstrassCauchyQuotient (d : ℕ) (g : (ι → ℂ) × ℂ → ℂ) (ρ : ℝ)
    (z : (ι → ℂ) × ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), g (z.1, s) / (s ^ d * (s - z.2))

/-- The Cauchy quotient is jointly holomorphic on a strictly smaller product polydisc. -/
private theorem analyticOnNhd_weierstrassCauchyQuotient
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ₀ ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R))
    (hρ₀ : 0 < ρ₀) (hρ₀ρ : ρ₀ < ρ) (hρR : ρ < R) (d : ℕ) :
    AnalyticOnNhd ℂ (weierstrassCauchyQuotient d g ρ) (V ×ˢ ball 0 ρ₀) := by
  let W : Set (((ι → ℂ) × ℂ) × ℂ) :=
    {p | p.1.1 ∈ V ∧ p.2 ∈ ball (0 : ℂ) R ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1.2}
  let H : ((ι → ℂ) × ℂ) × ℂ → ℂ := fun p =>
    g (p.1.1, p.2) / (p.2 ^ d * (p.2 - p.1.2))
  have hH : AnalyticOnNhd ℂ H W := by
    intro p hp
    have hnum : AnalyticAt ℂ (fun q : ((ι → ℂ) × ℂ) × ℂ => g (q.1.1, q.2)) p :=
      (hg (p.1.1, p.2) ⟨hp.1, hp.2.1⟩).comp_of_eq
        ((analyticAt_fst (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ)) |>.prod
          (analyticAt_snd (𝕜 := ℂ))) rfl
    have hden : AnalyticAt ℂ
        (fun q : ((ι → ℂ) × ℂ) × ℂ => q.2 ^ d * (q.2 - q.1.2)) p :=
      (analyticAt_snd.pow d).mul
        (analyticAt_snd.sub ((analyticAt_snd (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ))))
    exact hnum.div hden (mul_ne_zero (pow_ne_zero d hp.2.2.1)
      (sub_ne_zero.mpr hp.2.2.2))
  have hfθ : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (sphere 0 ρ) := continuousOn_const
  have hmem : ∀ x ∈ V ×ˢ ball (0 : ℂ) ρ₀, ∀ s ∈ sphere (0 : ℂ) ρ, (x, s) ∈ W := by
    intro x hx s hs
    have hsρ : ‖s‖ = ρ := by
      rw [← dist_zero_right]
      exact mem_sphere.mp hs
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hsρ
      linarith
    have hsw : s ≠ x.2 := by
      intro h
      have hxρ : ‖x.2‖ < ρ₀ := by simpa [dist_eq_norm] using hx.2
      rw [h] at hsρ
      linarith
    exact ⟨hx.1, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs, hs0, hsw⟩
  have hI := (analyticOnNhd_circleIntegral_kernel_mul (E := (ι → ℂ) × ℂ)
    (hV.prod isOpen_ball) hH (le_of_lt (hρ₀.trans hρ₀ρ)) hfθ hmem).const_smul
    (c := (2 * Real.pi * I : ℂ)⁻¹)
  refine hI.congr (hV.prod isOpen_ball) fun z hz => ?_
  simp [weierstrassCauchyQuotient, smul_eq_mul, H]

/-- A bound of the form `M / ρ ^ n`, valid for every positive `ρ < R`, persists at `R` itself by
continuity of the bound in `ρ`. -/
theorem le_div_pow_of_forall_lt {M : ℝ} {R : ℝ} (hR : 0 < R) (n : ℕ) {x : ℝ}
    (h : ∀ ρ, 0 < ρ → ρ < R → x ≤ M / ρ ^ n) : x ≤ M / R ^ n := by
  have hcont : ContinuousAt (fun ρ : ℝ => M / ρ ^ n) R :=
    continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne')
  have htendsto : Tendsto (fun ρ : ℝ => M / ρ ^ n) (nhdsWithin R (Iio R)) (nhds (M / R ^ n)) :=
    hcont.continuousWithinAt
  refine ge_of_tendsto htendsto ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds] with ρ hρR hρ0
  exact h ρ hρ0 hρR

omit [Fintype ι] in
/-- Cauchy's estimate for the Taylor coefficients of a last-coordinate slice, uniform up to the
boundary radius `R` even though the function is only assumed holomorphic on the open polydisc. -/
theorem norm_iteratedDeriv_snd_slice_le [Finite ι] {V : Set (ι → ℂ)} {R : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    {M : ℝ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hR : 0 < R) {z : ι → ℂ} (hz : z ∈ V)
    (hM : ∀ w ∈ ball (0 : ℂ) R, ‖g (z, w)‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n (fun w => g (z, w)) 0‖ ≤ (n.factorial : ℝ) * M / R ^ n := by
  classical
  let := Fintype.ofFinite ι
  apply le_div_pow_of_forall_lt hR
  intro ρ hρ hρR
  rw [iteratedDeriv_snd_slice_circleIntegral hg hz hρ hρR n, mul_assoc, norm_mul]
  have hkernel : ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
      ≤ M / ρ ^ n := by
    rw [← smul_eq_mul ((2 * Real.pi * I : ℂ)⁻¹)]
    have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun s => s ^ (-(n + 1 : ℤ)) * g (z, s)) (c := (0 : ℂ)) (R := ρ)
      (C := M / ρ ^ (n + 1)) hρ.le
      (fun s hs => by
        have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
        have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hsρ; exact hρ.ne' hsρ.symm
        have hzpow : ‖s ^ (-(n + 1 : ℤ))‖ = (ρ ^ (n + 1))⁻¹ := by
          have he : (-(n + 1 : ℤ)) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [norm_zpow, hsρ, he, zpow_neg, zpow_natCast]
        rw [norm_mul, hzpow, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (hM s ((mem_ball.mpr (by simpa [hsρ] using hρR))))
          (by positivity))
    calc ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
        ≤ ρ * (M / ρ ^ (n + 1)) := hb
      _ = M / ρ ^ n := by field_simp; ring
  simp only [Complex.norm_natCast]
  calc (n.factorial : ℝ) * ‖(2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), s ^ (-(n + 1 : ℤ)) * g (z, s)‖
      ≤ (n.factorial : ℝ) * (M / ρ ^ n) := mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = (n.factorial : ℝ) * M / ρ ^ n := by ring

omit [Fintype ι] in
/-- The Cauchy coefficient of a last-coordinate slice equals a division-kernel circle integral,
matching the shape used by the coordinate-power kernel identity. -/
theorem cauchyCoeff_eq_of_lt [Finite ι]
    {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) {w : ι → ℂ} (hw : w ∈ V)
    (hρ : 0 < ρ) (hρR : ρ < R) (j : ℕ) :
    (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) =
      ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv j (fun s => g (w, s)) 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [iteratedDeriv_snd_slice_circleIntegral hg hw hρ hρR j]
  have hEq : EqOn (fun s : ℂ => g (w, s) / s ^ (j + 1))
      (fun s => s ^ (-(j + 1 : ℤ)) * g (w, s)) (sphere (0 : ℂ) ρ) := by
    intro s _
    change g (w, s) / s ^ (j + 1) = s ^ (-(j + 1 : ℤ)) * g (w, s)
    rw [div_eq_inv_mul, show (-(j + 1 : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [circleIntegral.integral_congr hρ.le hEq,
    mul_assoc ((j : ℕ).factorial : ℂ) ((2 * Real.pi * I : ℂ)⁻¹),
    inv_mul_cancel_left₀ (by exact_mod_cast j.factorial_ne_zero :
      ((j : ℕ).factorial : ℂ) ≠ 0)]

omit [Fintype ι] in
/-- The Cauchy quotient at a fixed admissible radius solves the coordinate-power division identity
there, with remainder coefficients given by Taylor coefficients of the last-coordinate slice. -/
private theorem coordinatePower_eq_of_lt [Finite ι]
    {V : Set (ι → ℂ)} {R ρ : ℝ} {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hρ : 0 < ρ) (hρR : ρ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) ρ) :
    g (w, ζ) = weierstrassRemainder
        (fun j : Fin d => fun v : ι → ℂ => ((j : ℕ).factorial : ℂ)⁻¹ *
          iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ) +
      ζ ^ d * weierstrassCauchyQuotient d g ρ (w, ζ) := by
  classical
  let := Fintype.ofFinite ι
  have hζρ : ‖ζ‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ
  have hslice : DiffContOnCl ℂ (fun s => g (w, s)) (ball 0 ρ) :=
    diffContOnCl_snd_slice hg hw hρ hρR
  have hcauchy : g (w, ζ) = (2 * Real.pi * I : ℂ)⁻¹ * ∮ s in C(0, ρ), (s - ζ)⁻¹ * g (w, s) := by
    simpa using hslice.iteratedDeriv_eq_circleIntegral_sub_zpow_mul hρ 0 hζ
  have hcontslice : ContinuousOn (fun s => g (w, s)) (sphere (0 : ℂ) ρ) :=
    hg.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun s hs => ⟨hw, (sphere_subset_closedBall.trans (closedBall_subset_ball hρR)) hs⟩)
  have hne0 : ∀ s ∈ sphere (0 : ℂ) ρ, s ≠ 0 := by
    intro s hs hcontra
    have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
    rw [hcontra, norm_zero] at hsρ; exact hρ.ne' hsρ.symm
  have hnesw : ∀ s ∈ sphere (0 : ℂ) ρ, s ≠ ζ := by
    intro s hs hcontra
    have hsρ : ‖s‖ = ρ := by rw [← dist_zero_right]; exact mem_sphere.mp hs
    rw [hcontra] at hsρ; linarith
  have hEqOn : EqOn (fun s => (s - ζ)⁻¹ * g (w, s))
      (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) +
        ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) (sphere (0 : ℂ) ρ) := by
    intro s hs
    change (s - ζ)⁻¹ * g (w, s) =
      (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) + ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)
    rw [← add_mul, weierstrass_kernel_identity d (hne0 s hs) (hnesw s hs)]
  rw [circleIntegral.integral_congr hρ.le hEqOn] at hcauchy
  have hcont1 : ContinuousOn (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s))
      (sphere (0 : ℂ) ρ) := by
    apply ContinuousOn.mul _ hcontslice
    apply continuousOn_finsetSum
    intro j _
    exact ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun s hs => pow_ne_zero _ (hne0 s hs))
  have hcont2 : ContinuousOn (fun s => ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) (sphere (0 : ℂ) ρ) :=
    by
    apply ContinuousOn.mul _ hcontslice
    exact ContinuousOn.div continuousOn_const
      ((continuousOn_pow _).mul (continuousOn_id.sub continuousOn_const))
      (fun s hs => mul_ne_zero (pow_ne_zero _ (hne0 s hs)) (sub_ne_zero.mpr (hnesw s hs)))
  have hcirc1 : CircleIntegrable (fun s => (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rwa [abs_of_pos hρ])
  have hcirc2 : CircleIntegrable (fun s => ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) 0 ρ :=
    ContinuousOn.circleIntegrable' (by rwa [abs_of_pos hρ])
  rw [circleIntegral.integral_add hcirc1 hcirc2] at hcauchy
  have hsum : (∮ s in C(0, ρ), (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) =
      ∑ j ∈ range d, ζ ^ j * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) := by
    have hcongr : (∮ s in C(0, ρ), (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s)) =
        ∮ s in C(0, ρ), ∑ j ∈ range d, ζ ^ j * (g (w, s) / s ^ (j + 1)) := by
      apply circleIntegral.integral_congr hρ.le
      intro s _
      change (∑ j ∈ range d, ζ ^ j / s ^ (j + 1)) * g (w, s) =
        ∑ j ∈ range d, ζ ^ j * (g (w, s) / s ^ (j + 1))
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hcongr, circleIntegral.integral_fun_sum (fun j _ => by
      apply ContinuousOn.circleIntegrable' (R := ρ)
      rw [show |ρ| = ρ from abs_of_pos hρ]
      exact ContinuousOn.mul continuousOn_const
        (ContinuousOn.div hcontslice (continuousOn_pow _) (fun s hs => pow_ne_zero _ (hne0 s hs))))]
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  have hquot : (∮ s in C(0, ρ), ζ ^ d / (s ^ d * (s - ζ)) * g (w, s)) =
      ζ ^ d * ∮ s in C(0, ρ), g (w, s) / (s ^ d * (s - ζ)) := by
    rw [← circleIntegral.integral_const_mul]
    exact circleIntegral.integral_congr hρ.le fun s _ => by ring
  rw [hsum, hquot, mul_add] at hcauchy
  have hstep1 : (2 * Real.pi * I : ℂ)⁻¹ *
        ∑ j ∈ range d, ζ ^ j * ∮ s in C(0, ρ), g (w, s) / s ^ (j + 1) =
      ∑ j ∈ range d, (((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv j (fun s => g (w, s)) 0) * ζ ^ j
        := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [mul_left_comm, cauchyCoeff_eq_of_lt hg hw hρ hρR j, mul_comm]
  rw [hstep1] at hcauchy
  rw [hcauchy, weierstrassCauchyQuotient, weierstrassRemainder,
    Fin.sum_univ_eq_sum_range (fun j => ((j : ℕ).factorial : ℂ)⁻¹ *
      iteratedDeriv j (fun s => g (w, s)) 0 * ζ ^ j)]
  ring

omit [Fintype ι] in
/-- The Cauchy quotient at two admissible radii agrees at every nonzero point where both are
defined. -/
private theorem weierstrassCauchyQuotient_eq_of_ne [Finite ι] {V : Set (ι → ℂ)} {R ρ₁ ρ₂ : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < R) (hρ₂ : 0 < ρ₂) (hρ₂R : ρ₂ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ0 : ζ ≠ 0)
    (hζ₁ : ζ ∈ ball (0 : ℂ) ρ₁) (hζ₂ : ζ ∈ ball (0 : ℂ) ρ₂) :
    weierstrassCauchyQuotient d g ρ₁ (w, ζ) = weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
  classical
  let := Fintype.ofFinite ι
  have h1 := coordinatePower_eq_of_lt hg hρ₁ hρ₁R d hw hζ₁
  have h2 := coordinatePower_eq_of_lt hg hρ₂ hρ₂R d hw hζ₂
  have heq : ζ ^ d * weierstrassCauchyQuotient d g ρ₁ (w, ζ) =
      ζ ^ d * weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
    rw [← add_right_inj (weierstrassRemainder
      (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0)
      (w, ζ)), ← h1, ← h2]
  exact mul_left_cancel₀ (pow_ne_zero d hζ0) heq

omit [Fintype ι] in
/-- The Cauchy quotient at two admissible radii agrees wherever both are defined. -/
private theorem weierstrassCauchyQuotient_eq_of_lt [Finite ι]
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ₁ ρ₂ : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < R) (hρ₂ : 0 < ρ₂) (hρ₂R : ρ₂ < R) (d : ℕ)
    {w : ι → ℂ} (hw : w ∈ V) {ζ : ℂ} (hζ₁ : ζ ∈ ball (0 : ℂ) ρ₁) (hζ₂ : ζ ∈ ball (0 : ℂ) ρ₂) :
    weierstrassCauchyQuotient d g ρ₁ (w, ζ) = weierstrassCauchyQuotient d g ρ₂ (w, ζ) := by
  classical
  let := Fintype.ofFinite ι
  rcases eq_or_ne ζ 0 with hζ0 | hζ0
  · subst hζ0
    set ρ₀ := min ρ₁ ρ₂ / 2 with hρ₀def
    have hρ₀pos : 0 < ρ₀ := by positivity
    have hρ₀ρ₁ : ρ₀ < ρ₁ :=
      calc ρ₀ ≤ ρ₁ / 2 := by rw [hρ₀def]; gcongr; exact min_le_left ρ₁ ρ₂
        _ < ρ₁ := by linarith
    have hρ₀ρ₂ : ρ₀ < ρ₂ :=
      calc ρ₀ ≤ ρ₂ / 2 := by rw [hρ₀def]; gcongr; exact min_le_right ρ₁ ρ₂
        _ < ρ₂ := by linarith
    have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_of_finiteDimensional
      (hV.prod isOpen_ball)
    have hA1 : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) (ball 0 ρ₀) :=
      fun ζ' hζ' => ((analyticOnNhd_weierstrassCauchyQuotient hV hgA hρ₀pos hρ₀ρ₁ hρ₁R d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq
        ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have hA2 : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) (ball 0 ρ₀) :=
      fun ζ' hζ' => ((analyticOnNhd_weierstrassCauchyQuotient hV hgA hρ₀pos hρ₀ρ₂ hρ₂R d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq
        ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have heqn : (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ₀pos))]
        with ζ' hζ'0 hζ'0'
      exact weierstrassCauchyQuotient_eq_of_ne hg hρ₁ hρ₁R hρ₂ hρ₂R d hw hζ'0
        (ball_subset_ball hρ₀ρ₁.le hζ'0') (ball_subset_ball hρ₀ρ₂.le hζ'0')
    have hlim1 : Tendsto (fun ζ' => weierstrassCauchyQuotient d g ρ₁ (w, ζ')) (𝓝[≠] (0 : ℂ))
        (𝓝 (weierstrassCauchyQuotient d g ρ₁ (w, 0))) :=
      (hA1 0 (mem_ball_self hρ₀pos)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun ζ' => weierstrassCauchyQuotient d g ρ₂ (w, ζ')) (𝓝[≠] (0 : ℂ))
        (𝓝 (weierstrassCauchyQuotient d g ρ₂ (w, 0))) :=
      (hA2 0 (mem_ball_self hρ₀pos)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hlim1.congr' heqn) hlim2
  · exact weierstrassCauchyQuotient_eq_of_ne hg hρ₁ hρ₁R hρ₂ hρ₂R d hw hζ0 hζ₁ hζ₂

omit [Fintype ι] in
/-- Subtracting the Taylor polynomial of degree less than `d` from a function bounded by `M` gives a
numerator bounded by `(d + 1) * M`. The triangle inequality and Cauchy's coefficient bounds
control each of the `d` remainder terms on the smaller disc. -/
theorem norm_sub_weierstrassRemainder_iteratedDeriv_le [Finite ι] {V : Set (ι → ℂ)} {R ρ M : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R)) (hρR : ρ < R) (d : ℕ)
    (hM : ∀ z ∈ V ×ˢ ball (0 : ℂ) R, ‖g z‖ ≤ M) {w : ι → ℂ} (hw : w ∈ V) {ζ' : ℂ}
    (hζ' : ζ' ∈ ball (0 : ℂ) ρ) :
    ‖g (w, ζ') - weierstrassRemainder (d := by
  classical
  let := Fintype.ofFinite ι
  exact
    d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
          iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M := by
      have hζ'ρ : ‖ζ'‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ'
      have hζ'R : ‖ζ'‖ < R := hζ'ρ.trans hρR
      have hR0 : 0 < R := (norm_nonneg ζ').trans_lt hζ'R
      have hgb : ‖g (w, ζ')‖ ≤ M := hM (w, ζ') ⟨hw, mem_ball_zero_iff.mpr hζ'R⟩
      have hMnn : 0 ≤ M := (norm_nonneg _).trans hgb
      have haj : ∀ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
          iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0)‖ ≤ M / R ^ (j : ℕ) := by
        intro j
        have hb := norm_iteratedDeriv_snd_slice_le hg hR0 hw (fun s hs => hM (w, s) ⟨hw, hs⟩)
          (j : ℕ)
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        calc ((j : ℕ).factorial : ℝ)⁻¹ * ‖iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0‖
            ≤ ((j : ℕ).factorial : ℝ)⁻¹ * (((j : ℕ).factorial : ℝ) * M / R ^ (j : ℕ)) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = M / R ^ (j : ℕ) := by field_simp
      have hrem : ‖weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
          iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ (d : ℝ) * M := by
        unfold weierstrassRemainder
        calc ‖∑ j : Fin d, (((j : ℕ).factorial : ℂ)⁻¹ *
                iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0) * ζ' ^ (j : ℕ)‖
            ≤ ∑ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
                iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0) * ζ' ^ (j : ℕ)‖ := norm_sum_le _ _
          _ = ∑ j : Fin d, ‖(((j : ℕ).factorial : ℂ)⁻¹ *
                iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0)‖ * ‖ζ'‖ ^ (j : ℕ) := by
                simp [norm_pow]
          _ ≤ ∑ _j : Fin d, (M / R ^ (0 : ℕ)) * R ^ (0 : ℕ) := by
                apply Finset.sum_le_sum
                intro j _
                calc ‖(((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ)
                      (fun s => g (w, s)) 0)‖ * ‖ζ'‖ ^ (j : ℕ)
                    ≤ (M / R ^ (j : ℕ)) * R ^ (j : ℕ) :=
                      mul_le_mul (haj j) (pow_le_pow_left₀ (norm_nonneg _)
                        (hζ'ρ.trans hρR).le _) (by positivity) (by positivity)
                  _ = M := by field_simp
                  _ = (M / R ^ (0 : ℕ)) * R ^ (0 : ℕ) := by simp
          _ = (d : ℝ) * M := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
      calc ‖g (w, ζ') - weierstrassRemainder (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖
          ≤ ‖g (w, ζ')‖ + ‖weierstrassRemainder (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ := norm_sub_le _ _
        _ ≤ M + (d : ℝ) * M := add_le_add hgb hrem
        _ = ((d + 1 : ℕ) : ℝ) * M := by push_cast; ring

omit [Fintype ι] in
/-- The **uniform coordinate-power quotient bound**: the Cauchy quotient at radius `ρ` is bounded by
`(d+1) M / ρ ^ d` throughout the disc, using a bound `M` on the numerator over the whole domain.
The proof compares the numerator to its degree-`< d` Taylor polynomial, bounded by `(d+1) M` via
`norm_sub_weierstrassRemainder_iteratedDeriv_le`, then applies the maximum modulus principle to
the quotient itself and lets the comparison radius approach `ρ`. -/
private theorem norm_weierstrassCauchyQuotient_le [Finite ι]
    {V : Set (ι → ℂ)} (hV : IsOpen V) {R ρ M : ℝ}
    {g : (ι → ℂ) × ℂ → ℂ} (hg : DifferentiableOn ℂ g (V ×ˢ ball 0 R))
    (hρ : 0 < ρ) (hρR : ρ < R) (d : ℕ)
    (hM : ∀ z ∈ V ×ˢ ball (0 : ℂ) R, ‖g z‖ ≤ M) {w : ι → ℂ} (hw : w ∈ V) {ζ0 : ℂ}
    (hζ0 : ζ0 ∈ ball (0 : ℂ) ρ) :
    ‖weierstrassCauchyQuotient d g ρ (w, ζ0)‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ ^ d := by
  classical
  let := Fintype.ofFinite ι
  have hR0 : 0 < R := hρ.trans hρR
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM (w, 0) ⟨hw, mem_ball_self hR0⟩)
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_of_finiteDimensional
    (hV.prod isOpen_ball)
  have hψ : ∀ ζ' : ℂ, ζ' ∈ ball (0 : ℂ) ρ →
      ‖g (w, ζ') - weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
        iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M :=
    fun ζ' hζ' => norm_sub_weierstrassRemainder_iteratedDeriv_le hg hρR d hM hw hζ'
  have hqbound : ∀ ρ', ‖ζ0‖ < ρ' → ρ' < ρ →
      ‖weierstrassCauchyQuotient d g ρ (w, ζ0)‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
    intro ρ' hζ0ρ' hρ'ρ
    have hρ'pos : 0 < ρ' := (norm_nonneg _).trans_lt hζ0ρ'
    have hbdry : ∀ ζ' ∈ sphere (0 : ℂ) ρ',
        ‖weierstrassCauchyQuotient d g ρ (w, ζ')‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
      intro ζ' hζ'
      have hζ'ρ' : ‖ζ'‖ = ρ' := by rw [← dist_zero_right]; exact mem_sphere.mp hζ'
      have hζ'0 : ζ' ≠ 0 := by intro h; rw [h, norm_zero] at hζ'ρ'; exact hρ'pos.ne' hζ'ρ'.symm
      have hζ'ball : ζ' ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hζ'ρ']; exact hρ'ρ
      have heq := coordinatePower_eq_of_lt hg hρ hρR d hw hζ'ball
      have hpsi := hψ ζ' hζ'ball
      have hval : ζ' ^ d * weierstrassCauchyQuotient d g ρ (w, ζ') =
          g (w, ζ') - weierstrassRemainder (d := d) (fun j v => ((j : ℕ).factorial : ℂ)⁻¹ *
            iteratedDeriv (j : ℕ) (fun s => g (v, s)) 0) (w, ζ') := by
        rw [heq]; ring
      have hnorm : ‖ζ'‖ ^ d * ‖weierstrassCauchyQuotient d g ρ (w, ζ')‖ ≤
          ((d + 1 : ℕ) : ℝ) * M := by
        rw [← norm_pow, ← norm_mul, hval]; exact hpsi
      rw [hζ'ρ'] at hnorm
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ρ' ^ d), mul_comm]
      exact hnorm
    obtain ⟨ρ'', hρ'ρ'', hρ''ρ⟩ := exists_between hρ'ρ
    have hAslice : AnalyticOnNhd ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ (w, ζ'))
        (ball (0 : ℂ) ρ'') := fun ζ' hζ' =>
      ((analyticOnNhd_weierstrassCauchyQuotient hV hgA (hρ'pos.trans hρ'ρ'') hρ''ρ hρR d)
        (w, ζ') ⟨hw, hζ'⟩).comp_of_eq ((analyticAt_const (v := w)).prod analyticAt_id) rfl
    have hslice : DiffContOnCl ℂ (fun ζ' => weierstrassCauchyQuotient d g ρ (w, ζ'))
        (ball (0 : ℂ) ρ') :=
      ⟨(hAslice.mono (ball_subset_ball hρ'ρ''.le)).differentiableOn, by
        rw [closure_ball (0 : ℂ) hρ'pos.ne']
        exact hAslice.continuousOn.mono (closedBall_subset_ball hρ'ρ'')⟩
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hslice
      (fun ζ' hζ' => by rw [frontier_ball (0 : ℂ) hρ'pos.ne'] at hζ'; exact hbdry ζ' hζ')
      (subset_closure (mem_ball_zero_iff.mpr hζ0ρ'))
  have hζ0ρ : ‖ζ0‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hζ0
  have hcont : ContinuousAt (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d) ρ :=
    continuousAt_const.div (continuousAt_id.pow d) (pow_ne_zero d hρ.ne')
  have htendsto : Tendsto (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d)
      (nhdsWithin ρ (Iio ρ)) (nhds (((d + 1 : ℕ) : ℝ) * M / ρ ^ d)) :=
    hcont.continuousWithinAt
  refine ge_of_tendsto htendsto ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds hζ0ρ)] with ρ' hρ'ρ hρ'ζ0
  exact hqbound ρ' hρ'ζ0 hρ'ρ

/-- **Coordinate-power division ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.4).** Every
holomorphic function
on a polydisc has a unique quotient and polynomial remainder on division by `w^d`.
The quotient estimate applies whenever the numerator is bounded. Uniqueness follows
from the coordinate-power uniqueness theorem above.
Empty parameter index types and `d = 0` are included. -/
theorem coordinatePower_division (d : ℕ) {r : ι → ℝ} {R : ℝ} (hR : 0 < R)
    {g : (ι → ℂ) × ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (polydisc 0 r ×ˢ ball 0 R)) :
    ∃ q : (ι → ℂ) × ℂ → ℂ, ∃ a : Fin d → (ι → ℂ) → ℂ,
      IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q a (polydisc 0 r) R ∧
      (∀ M : ℝ, 0 ≤ M →
        (∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖g z‖ ≤ M) →
        ∀ z ∈ polydisc 0 r ×ˢ ball 0 R, ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) / R ^ d * M) ∧
      (∀ q' a', IsWeierstrassDivisionOn (fun z => z.2 ^ d) g q' a'
          (polydisc 0 r) R →
        EqOn q q' (polydisc 0 r ×ˢ ball 0 R) ∧
        ∀ j, EqOn (a j) (a' j) (polydisc 0 r)) := by
  set V := polydisc (0 : ι → ℂ) r with hVdef
  have hVo : IsOpen V := isOpen_polydisc _ _
  have hgA : AnalyticOnNhd ℂ g (V ×ˢ ball 0 R) := hg.analyticOnNhd_of_finiteDimensional
    (hVo.prod isOpen_ball)
  set a : Fin d → (ι → ℂ) → ℂ := fun j w =>
    ((j : ℕ).factorial : ℂ)⁻¹ * iteratedDeriv (j : ℕ) (fun s => g (w, s)) 0 with hadef
  set q : (ι → ℂ) × ℂ → ℂ := fun z => weierstrassCauchyQuotient d g ((‖z.2‖ + R) / 2) z with hqdef
  have hρz : ∀ ζ : ℂ, ‖ζ‖ < R → 0 < (‖ζ‖ + R) / 2 ∧ ‖ζ‖ < (‖ζ‖ + R) / 2 ∧
      (‖ζ‖ + R) / 2 < R := fun ζ hζ => ⟨by linarith [norm_nonneg ζ], by linarith, by linarith⟩
  have hqanalytic : AnalyticOnNhd ℂ q (V ×ˢ ball 0 R) := by
    rintro z ⟨hz1, hz2⟩
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    obtain ⟨ρbig, hρ0ρbig, hρbigR⟩ := exists_between hρ0R
    have hkey : ‖z.2‖ < 2 * ρbig - R := by nlinarith
    obtain ⟨ρ0', hζρ0', hρ0'key⟩ := exists_between hkey
    have hρ0'ρbig : ρ0' < ρbig := by linarith
    have hAbig : AnalyticOnNhd ℂ (weierstrassCauchyQuotient d g ρbig) (V ×ˢ ball 0 ρ0') :=
      analyticOnNhd_weierstrassCauchyQuotient hVo hgA
        ((norm_nonneg z.2).trans_lt hζρ0') hρ0'ρbig hρbigR d
    have hzmem : z ∈ V ×ˢ ball (0 : ℂ) ρ0' := ⟨hz1, mem_ball_zero_iff.mpr hζρ0'⟩
    have heqOn : EqOn q (weierstrassCauchyQuotient d g ρbig) (V ×ˢ ball (0 : ℂ) ρ0') := by
      rintro y ⟨hy1, hy2⟩
      have hy2' : ‖y.2‖ < ρ0' := by simpa [mem_ball, dist_eq_norm] using hy2
      have hy2R : ‖y.2‖ < R := hy2'.trans (hρ0'ρbig.trans hρbigR)
      obtain ⟨hρypos, hρyζ, hρyR⟩ := hρz y.2 hy2R
      have hyρbig : ‖y.2‖ < ρbig := hy2'.trans hρ0'ρbig
      have hρylt : (‖y.2‖ + R) / 2 < ρbig := by linarith
      change weierstrassCauchyQuotient d g ((‖y.2‖ + R) / 2) y =
        weierstrassCauchyQuotient d g ρbig y
      exact weierstrassCauchyQuotient_eq_of_lt hVo hg hρypos hρyR
        ((norm_nonneg y.2).trans_lt hyρbig) hρbigR d hy1
        (mem_ball_zero_iff.mpr hρyζ) (mem_ball_zero_iff.mpr hyρbig)
    have heq : q =ᶠ[𝓝 z] weierstrassCauchyQuotient d g ρbig := by
      filter_upwards [(hVo.prod isOpen_ball).mem_nhds hzmem] with y hy using heqOn hy
    exact (hAbig z hzmem).congr heq.symm
  have haholo : ∀ j, DifferentiableOn ℂ (a j) V := fun j =>
    (differentiableOn_iteratedDeriv_snd_slice hVo hg hR (j : ℕ)).const_mul _
  have hqholo : DifferentiableOn ℂ q (V ×ˢ ball 0 R) :=
    hqanalytic.differentiableOn
  have heqOnV : EqOn g (fun z => q z * (fun z => z.2 ^ d) z + weierstrassRemainder a z)
      (V ×ˢ ball 0 R) := by
    rintro z ⟨hz1, hz2⟩
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    have := coordinatePower_eq_of_lt hg hρ0pos hρ0R d hz1 (mem_ball_zero_iff.mpr hρ0ζ)
    change g z = q z * z.2 ^ d + weierstrassRemainder a z
    rw [this]; ring
  refine ⟨q, a, ⟨hqholo, haholo, heqOnV⟩, ?_, ?_⟩
  · intro M hM0 hMb z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hζR : ‖z.2‖ < R := by simpa [mem_ball, dist_eq_norm] using hz2
    obtain ⟨hρ0pos, hρ0ζ, hρ0R⟩ := hρz z.2 hζR
    have hbnd : ∀ ρ', ‖z.2‖ < ρ' → ρ' < R → ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d := by
      intro ρ' hζρ' hρ'R
      have hle := norm_weierstrassCauchyQuotient_le hVo hg ((norm_nonneg z.2).trans_lt hζρ')
        hρ'R d hMb hz1 (mem_ball_zero_iff.mpr hζρ')
      rwa [show q z = weierstrassCauchyQuotient d g ρ' z from
        weierstrassCauchyQuotient_eq_of_lt hVo hg hρ0pos hρ0R
          ((norm_nonneg z.2).trans_lt hζρ') hρ'R d hz1 (mem_ball_zero_iff.mpr hρ0ζ)
          (mem_ball_zero_iff.mpr hζρ')]
    have hcont : ContinuousAt (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d) R :=
      continuousAt_const.div (continuousAt_id.pow d) (pow_ne_zero d hR.ne')
    have htendsto : Tendsto (fun ρ' : ℝ => ((d + 1 : ℕ) : ℝ) * M / ρ' ^ d)
        (nhdsWithin R (Iio R)) (nhds (((d + 1 : ℕ) : ℝ) * M / R ^ d)) :=
      hcont.continuousWithinAt
    have hfinal : ‖q z‖ ≤ ((d + 1 : ℕ) : ℝ) * M / R ^ d := by
      refine ge_of_tendsto htendsto ?_
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds hζR)] with ρ' hρ'R hζρ'
      exact hbnd ρ' hζρ' hρ'R
    rw [show ((d + 1 : ℕ) : ℝ) / R ^ d * M = ((d + 1 : ℕ) : ℝ) * M / R ^ d from by ring]
    exact hfinal
  · intro q' a' h'
    exact unique_coordinatePower_division ⟨hqholo, haholo, heqOnV⟩ h' hR

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
