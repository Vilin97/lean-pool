/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

/-!
# The Hamilton--Ivey reaction coercivity estimate

This file proves the pointwise nonlinear estimate used at a negative minimum
of the Hamilton--Ivey pinching quantity.  We use the normalization of
Chen--Xu--Zhang: `lambda >= mu >= nu` are the eigenvalues of the curvature
operator whose value on a tangent plane is twice its sectional curvature, and
the scalar curvature is `R = lambda + mu + nu`.

No curvature evolution equation or maximum principle is assumed here.  This
is the exact reaction-term calculation which those geometric ingredients
consume.
-/

@[expose] public noncomputable section

namespace HamiltonIveyReaction

/-- A one-dimensional barrier principle tailored to invariant-region
arguments: a differentiable function which points strictly upward wherever it
is negative cannot cross below zero. -/
theorem nonneg_on_Icc_of_deriv_pos_of_neg
    {f f' : ℝ → ℝ} {T : ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hderiv : ∀ x ∈ Set.Icc 0 T, HasDerivAt f (f' x) x)
    (hzero : 0 ≤ f 0)
    (hpoints : ∀ x ∈ Set.Icc 0 T, f x < 0 → 0 < f' x) :
    ∀ x ∈ Set.Icc 0 T, 0 ≤ f x := by
  intro b hb
  by_contra hbnonneg
  have hbneg : f b < 0 := lt_of_not_ge hbnonneg
  have hb0 : 0 ≤ b := hb.1
  obtain ⟨c, hc, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hb0) (hcont.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hb.2⟩))
  have hcneg : f c < 0 := (hmin ⟨hb0, le_rfl⟩).trans_lt hbneg
  have hcpos : 0 < c := by
    have hcne : c ≠ 0 := by
      intro hc0
      subst c
      linarith
    exact lt_of_le_of_ne hc.1 (Ne.symm hcne)
  have hlocal : IsLocalMinOn f (Set.Icc 0 b) c := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmin hx
  have hzero_mem : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb0⟩
  have htangent : (0 : ℝ) - c ∈ posTangentConeAt (Set.Icc 0 b) c :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) b).segment_subset hc hzero_mem)
  have hnonneg := hlocal.hasFDerivWithinAt_nonneg
    (hderiv c ⟨hc.1, hc.2.trans hb.2⟩).hasFDerivAt.hasFDerivWithinAt htangent
  have hderivpos := hpoints c ⟨hc.1, hc.2.trans hb.2⟩ hcneg
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hnonneg
  nlinarith

/-- The scalar curvature in the twice-sectional-curvature eigenvalue convention. -/
def scalar (lambda mu nu : ℝ) : ℝ := lambda + mu + nu

/-- The Hamilton--Ivey pinching quantity with initial lower-curvature scale `K`. -/
def defect (K t lambda mu nu : ℝ) : ℝ :=
  scalar lambda mu nu / (-nu) - Real.log (-nu) + 3 + Real.log (K / (1 + K * t))

/-- The part of the Hamilton--Ivey defect that depends on the least
eigenvalue once scalar curvature is held fixed. -/
def nuProfile (R nu : ℝ) : ℝ := R / (-nu) - Real.log (-nu)

/-- Derivative of the least-eigenvalue profile.  Its sign is controlled by
`R - nu`, which geometrically equals `lambda + mu`. -/
theorem hasDerivAt_nuProfile {R nu : ℝ} (hnu : nu ≠ 0) :
    HasDerivAt (nuProfile R) ((R - nu) / nu ^ 2) nu := by
  have hquot := (hasDerivAt_const nu R).div (hasDerivAt_id nu).neg
    (neg_ne_zero.mpr hnu)
  have hlog := (hasDerivAt_id nu).neg.log (neg_ne_zero.mpr hnu)
  have h := hquot.sub hlog
  change HasDerivAt
    ((fun _ : ℝ => R) / -id - fun y => Real.log ((-id) y))
    ((R - nu) / nu ^ 2) nu
  apply h.congr_deriv
  change (0 * (-nu) - R * (-1)) / (-nu) ^ 2 - (-1) / (-nu) =
    (R - nu) / nu ^ 2
  field_simp [hnu]
  ring

/-- On a negative interval where `R - nu` stays positive, the
least-eigenvalue profile is monotone increasing. -/
theorem nuProfile_mono_of_le_of_neg_of_scalar_sub_pos
    {R a b : ℝ} (hab : a ≤ b) (hb : b < 0) (hRb : 0 < R - b) :
    nuProfile R a ≤ nuProfile R b := by
  by_cases heq : a = b
  · subst b
    exact le_rfl
  have hab' : a < b := lt_of_le_of_ne hab heq
  have hmono : StrictMonoOn (nuProfile R) (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro z hz
      have hzneg : z < 0 := lt_of_le_of_lt hz.2 hb
      exact (hasDerivAt_nuProfile hzneg.ne).continuousAt.continuousWithinAt
    · intro z hz
      have hzmem : z ∈ Set.Icc a b := interior_subset hz
      have hzneg : z < 0 := lt_of_le_of_lt hzmem.2 hb
      have hRz : 0 < R - z := by linarith [hRb, hzmem.2]
      rw [(hasDerivAt_nuProfile hzneg.ne).deriv]
      exact div_pos hRz (sq_pos_of_ne_zero hzneg.ne)
  exact (hmono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab').le

/-- The Hamilton--Ivey defect is the least-eigenvalue profile of scalar
curvature plus its time-dependent normalization. -/
theorem defect_eq_nuProfile (K t lambda mu nu : ℝ) :
    defect K t lambda mu nu =
      nuProfile (scalar lambda mu nu) nu + 3 +
        Real.log (K / (1 + K * t)) := by
  rfl

/-- Replacing the least eigenvalue by an upper support increases the defect
whenever the scalar-minus-support sign is positive. -/
theorem defect_le_nuProfile_of_upper_support
    {K t lambda mu nu q : ℝ}
    (hnuq : nu ≤ q) (hqneg : q < 0)
    (hscalarq : 0 < scalar lambda mu nu - q) :
    defect K t lambda mu nu ≤
      nuProfile (scalar lambda mu nu) q + 3 +
        Real.log (K / (1 + K * t)) := by
  rw [defect_eq_nuProfile]
  gcongr
  exact nuProfile_mono_of_le_of_neg_of_scalar_sub_pos hnuq hqneg hscalarq

/-- The zeroth-order term in `(partial_t - Delta) defect` at a least-eigenvector. -/
def reaction (K t lambda mu nu : ℝ) : ℝ :=
  -2 * nu - K / (1 + K * t) +
    ((lambda - nu) * (mu - nu) / nu ^ 2) * scalar lambda mu nu

/-- The diagonal reaction terms for the three-dimensional curvature-operator ODE. -/
def eigenReaction (lambda mu nu : ℝ) : ℝ × ℝ × ℝ :=
  (lambda ^ 2 + mu * nu, mu ^ 2 + lambda * nu, nu ^ 2 + lambda * mu)

/-- The scalar component of the diagonal curvature-reaction ODE. -/
def scalarReaction (lambda mu nu : ℝ) : ℝ :=
  lambda ^ 2 + mu * nu + (mu ^ 2 + lambda * nu) + (nu ^ 2 + lambda * mu)

/-- The scalar reaction dominates one third of the scalar curvature squared. -/
theorem scalar_sq_div_three_le_reaction (lambda mu nu : ℝ) :
    scalar lambda mu nu ^ 2 / 3 ≤ scalarReaction lambda mu nu := by
  dsimp [scalar, scalarReaction]
  nlinarith [sq_nonneg lambda, sq_nonneg mu, sq_nonneg nu,
    sq_nonneg (lambda + mu), sq_nonneg (lambda + nu), sq_nonneg (mu + nu)]

/-- The formal chain-rule derivative of the Hamilton--Ivey defect along the
diagonal three-dimensional curvature-operator ODE.  This definition expands
the quotient and logarithm rules rather than referring to `reaction`. -/
def defectODEDerivative (K t lambda mu nu : ℝ) : ℝ :=
  let qlambda := lambda ^ 2 + mu * nu
  let qmu := mu ^ 2 + lambda * nu
  let qnu := nu ^ 2 + lambda * mu
  let R := scalar lambda mu nu
  (((qlambda + qmu + qnu) * (-nu) - R * (-qnu)) / (-nu) ^ 2) -
      (-qnu) / (-nu) - K / (1 + K * t)

/-- The expression called `reaction` is exactly the expanded ODE derivative
of the Hamilton--Ivey defect; it is not introduced as an unrelated
positivity certificate. -/
theorem defectODEDerivative_eq_reaction
    {K t lambda mu nu : ℝ} (hnu : nu ≠ 0) :
    defectODEDerivative K t lambda mu nu = reaction K t lambda mu nu := by
  simp only [defectODEDerivative, reaction, scalar]
  field_simp [hnu]
  ring

/-- Along an actual solution of the diagonal curvature-reaction ODE, the
Hamilton--Ivey defect has the derivative computed by
`defectODEDerivative`. -/
theorem hasDerivAt_defect_of_eigenReaction
    {K t : ℝ} {lambda mu nu : ℝ → ℝ}
    (hK : 0 < K) (ht : 0 ≤ t) (hnu0 : nu t ≠ 0)
    (hlambda : HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t)
    (hmu : HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t)
    (hnu : HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t) :
    HasDerivAt
      (fun s ↦ defect K s (lambda s) (mu s) (nu s))
      (reaction K t (lambda t) (mu t) (nu t)) t := by
  have hden : 1 + K * t ≠ 0 := by
    have : 0 < 1 + K * t := by positivity
    exact this.ne'
  have hR := (hlambda.add hmu).add hnu
  have hneg := hnu.neg
  have hquot := hR.div hneg (neg_ne_zero.mpr hnu0)
  have hlognu := hneg.log (neg_ne_zero.mpr hnu0)
  have hlinear := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul K)
  have hscale := (hasDerivAt_const t K).div hlinear hden
  have hlogscale := hscale.log (div_ne_zero hK.ne' hden)
  have htotal := (hquot.sub hlognu).add_const 3 |>.add hlogscale
  change HasDerivAt
    (fun s ↦ ((lambda s + mu s + nu s) / (-nu s) - Real.log (-nu s) + 3) +
      Real.log (K / (1 + K * s)))
    (reaction K t (lambda t) (mu t) (nu t)) t
  have hsame := htotal.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s ↦ by rfl))
  apply hsame.congr_deriv
  simp only [reaction, scalar, Pi.add_apply, Pi.neg_apply, Pi.div_apply, id_eq,
    zero_add, mul_one]
  field_simp [hnu0, hden, hK.ne']
  ring

/-- The sharp elementary logarithmic inequality used in Hamilton--Ivey coercivity.

It is the statement that `s / (log s)^2` has global lower bound `e^2 / 4`
for `s > 1`, proved here without importing any Ricci-flow development. -/
theorem exp_two_mul_log_sq_le_four_mul {s : ℝ} (hs : 1 < s) :
    Real.exp 2 * (Real.log s) ^ 2 ≤ 4 * s := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hz : 0 < Real.log s / 2 := div_pos hlog (by norm_num)
  have hbasic := Real.log_le_sub_one_of_pos hz
  have hexp : Real.log s / 2 ≤ Real.exp (Real.log s / 2 - 1) := by
    have := Real.exp_le_exp.mpr hbasic
    simpa [Real.exp_log hz] using this
  have hsq := (sq_le_sq₀ (le_of_lt hz) (Real.exp_pos _).le).2 hexp
  have hsq' :
      (Real.log s / 2) ^ 2 ≤
        Real.exp ((Real.log s / 2 - 1) + (Real.log s / 2 - 1)) := by
    calc
      (Real.log s / 2) ^ 2 ≤ Real.exp (Real.log s / 2 - 1) ^ 2 := hsq
      _ = Real.exp ((Real.log s / 2 - 1) + (Real.log s / 2 - 1)) := by
        rw [pow_two, ← Real.exp_add]
  have hexp_arg :
      (Real.log s / 2 - 1) + (Real.log s / 2 - 1) = Real.log s - 2 := by ring
  rw [hexp_arg, Real.exp_sub, Real.exp_log hs0] at hsq'
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hsqmul := (le_div_iff₀ he2).1 hsq'
  nlinarith

/-- Scale-invariant form of `exp_two_mul_log_sq_le_four_mul`. -/
theorem scaled_log_sq_bound {A v : ℝ} (hA : 0 < A) (hAv : A < v) :
    Real.exp 2 * A * (Real.log v - Real.log A) ^ 2 ≤ 4 * v := by
  have hv : 0 < v := hA.trans hAv
  have hs : 1 < v / A := (one_lt_div hA).2 hAv
  have h := exp_two_mul_log_sq_le_four_mul hs
  rw [Real.log_div hv.ne' hA.ne'] at h
  have hA0 : 0 ≤ A := hA.le
  have := mul_le_mul_of_nonneg_left h hA0
  field_simp [hA.ne'] at this
  nlinarith

/-- Ordered eigenvalues give the arithmetic-mean bound for the mixed reaction factor.
The inequality is written with a negative scalar factor, so its direction is
the one required at a negative minimum of the pinching quantity. -/
theorem mixed_reaction_lower_bound
    {lambda mu nu R : ℝ}
    (hlm : mu ≤ lambda) (hmn : nu ≤ mu)
    (hR : R = lambda + mu + nu) (hRneg : R < 0) :
    ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
      ((R - 3 * nu) ^ 2 / (4 * nu ^ 2)) * R := by
  have hx : 0 ≤ lambda - nu := by linarith
  have hy : 0 ≤ mu - nu := by linarith
  have hsum : (lambda - nu) + (mu - nu) = R - 3 * nu := by
    rw [hR]
    ring
  have hamgm : 4 * ((lambda - nu) * (mu - nu)) ≤ (R - 3 * nu) ^ 2 := by
    rw [← hsum]
    nlinarith [sq_nonneg ((lambda - nu) - (mu - nu))]
  by_cases hnu : nu = 0
  · subst nu
    simp
  · have hnu_sq : 0 < nu ^ 2 := sq_pos_of_ne_zero hnu
    have hdiv :
        (lambda - nu) * (mu - nu) / nu ^ 2 ≤
          (R - 3 * nu) ^ 2 / (4 * nu ^ 2) := by
      rw [div_le_div_iff₀ hnu_sq (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonpos_right hdiv hRneg.le

/-- **Hamilton--Ivey reaction coercivity.**

At an ordered curvature-operator triple with negative least eigenvalue,
assume the standard scalar lower barrier `R ≥ -3K/(1+Kt)`.  If the
Hamilton--Ivey quantity is negative, then the curvature scale has crossed the
barrier and the complete zeroth-order reaction term is strictly positive.  In
particular it has the quantitative lower bound `(-nu)/9` used in the localized
maximum-principle proof.
-/
theorem hamiltonIvey_reaction_coercive
    {K t lambda mu nu : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t)
    (hlm : mu ≤ lambda) (hmn : nu ≤ mu) (hnu : nu < 0)
    (hscalar : -3 * (K / (1 + K * t)) ≤ scalar lambda mu nu)
    (hdefect : defect K t lambda mu nu < 0) :
    K / (1 + K * t) < -nu ∧
      -nu / 9 ≤ reaction K t lambda mu nu ∧
      0 < reaction K t lambda mu nu := by
  let A : ℝ := K / (1 + K * t)
  let R : ℝ := scalar lambda mu nu
  have hden : 0 < 1 + K * t := by positivity
  have hA : 0 < A := div_pos hK hden
  have hRord : 3 * nu ≤ R := by
    dsimp [R, scalar]
    linarith
  have hlogA : Real.log (K / (1 + K * t)) = Real.log A := rfl
  have hcross : A < -nu := by
    have hnuPos : 0 < -nu := by linarith
    have hratio : 3 * nu / (-nu) ≤ R / (-nu) :=
      (div_le_div_iff₀ hnuPos hnuPos).2 (by nlinarith)
    have hthree : 3 * nu / (-nu) = -3 := by
      calc
        3 * nu / (-nu) = -(3 * (nu / nu)) := by ring
        _ = -3 := by rw [div_self hnu.ne]; norm_num
    have hratio3 : -3 ≤ R / (-nu) := by simpa [hthree] using hratio
    have hlogs : Real.log A < Real.log (-nu) := by
      dsimp [defect] at hdefect
      rw [hlogA] at hdefect
      linarith
    rw [← Real.exp_log hA, ← Real.exp_log hnuPos]
    exact Real.exp_lt_exp.mpr hlogs
  refine ⟨hcross, ?_⟩
  have hnu0 : nu ≠ 0 := hnu.ne
  have hRdef : R = lambda + mu + nu := rfl
  have hI : -nu < -2 * nu - A := by linarith
  by_cases hRnonneg : 0 ≤ R
  · have hlanu : 0 ≤ lambda - nu := by linarith
    have hmunu : 0 ≤ mu - nu := by linarith
    have hmixed_nonneg :
        0 ≤ ((lambda - nu) * (mu - nu) / nu ^ 2) * R := by
      exact mul_nonneg (div_nonneg (mul_nonneg hlanu hmunu) (sq_nonneg nu)) hRnonneg
    have hreact : -nu < reaction K t lambda mu nu := by
      change -nu < -2 * nu - A +
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R
      linarith
    constructor
    · linarith
    · linarith
  · have hRneg : R < 0 := lt_of_not_ge hRnonneg
    have hmixed := mixed_reaction_lower_bound hlm hmn hRdef hRneg
    have hsum_nonneg : 0 ≤ R - 3 * nu := by linarith
    have hnuPos : 0 < -nu := neg_pos.mpr hnu
    have hloglt : Real.log A < Real.log (-nu) :=
      Real.strictMonoOn_log hA hnuPos hcross
    have hlogdiff_pos : 0 < Real.log (-nu) - Real.log A := sub_pos.mpr hloglt
    have hbarrier_log :
        R / (-nu) + 3 < Real.log (-nu) - Real.log A := by
      change R / (-nu) - Real.log (-nu) + 3 + Real.log A < 0 at hdefect
      linarith
    have hquot : (R - 3 * nu) / (-nu) = R / (-nu) + 3 := by
      field_simp [hnu0]
      ring
    have hleft_nonneg : 0 ≤ R / (-nu) + 3 := by
      rw [← hquot]
      exact div_nonneg hsum_nonneg (by linarith)
    have hsqcomp :
        (R - 3 * nu) ^ 2 / (4 * nu ^ 2) ≤
          (Real.log (-nu) - Real.log A) ^ 2 / 4 := by
      have hsquares :=
        (sq_le_sq₀ hleft_nonneg hlogdiff_pos.le).2 hbarrier_log.le
      rw [← hquot] at hsquares
      have hnu_sq : 0 < nu ^ 2 := sq_pos_of_ne_zero hnu0
      rw [div_pow] at hsquares
      have hneg_sq : (-nu) ^ 2 = nu ^ 2 := by ring
      rw [hneg_sq] at hsquares
      have hfour : (0 : ℝ) < 4 := by norm_num
      have hsquares_div := div_le_div_of_nonneg_right hsquares hfour.le
      calc
        (R - 3 * nu) ^ 2 / (4 * nu ^ 2) =
            ((R - 3 * nu) ^ 2 / nu ^ 2) / 4 := by
              field_simp [hnu0]
        _ ≤ (Real.log (-nu) - Real.log A) ^ 2 / 4 := hsquares_div
    have hmixed_log :
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
          ((Real.log (-nu) - Real.log A) ^ 2 / 4) * R := by
      calc
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
            ((R - 3 * nu) ^ 2 / (4 * nu ^ 2)) * R := hmixed
        _ ≥ ((Real.log (-nu) - Real.log A) ^ 2 / 4) * R :=
          mul_le_mul_of_nonpos_right hsqcomp hRneg.le
    have hscaled := scaled_log_sq_bound hA hcross
    have he2 : 0 < Real.exp 2 := Real.exp_pos 2
    have hcoeff :
        (Real.log (-nu) - Real.log A) ^ 2 / 4 ≤ (-nu) / (Real.exp 2 * A) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (mul_pos he2 hA)]
      nlinarith
    have hmixed_scaled :
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
          ((-nu) / (Real.exp 2 * A)) * R := by
      exact (mul_le_mul_of_nonpos_right hcoeff hRneg.le).trans hmixed_log
    have hRlower : -3 * A ≤ R := by simpa [A, R] using hscalar
    have hmixed_final :
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
          3 / Real.exp 2 * nu := by
      calc
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R ≥
            ((-nu) / (Real.exp 2 * A)) * R := hmixed_scaled
        _ ≥ ((-nu) / (Real.exp 2 * A)) * (-3 * A) := by
          exact mul_le_mul_of_nonneg_left hRlower
            (div_nonneg (by linarith) (mul_pos he2 hA).le)
        _ = 3 / Real.exp 2 * nu := by
          field_simp [he2.ne', hA.ne']
    have he1_gt_two : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
      norm_num at h ⊢
      exact h
    have he2_gt_four : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have hconstant : 3 / Real.exp 2 < 8 / 9 := by
      rw [div_lt_iff₀ he2]
      nlinarith
    have hmixed_weak : (8 / 9 : ℝ) * nu ≤
        ((lambda - nu) * (mu - nu) / nu ^ 2) * R := by
      exact (mul_le_mul_of_nonpos_right hconstant.le hnu.le).trans hmixed_final
    have hreact_bound : -nu / 9 ≤ reaction K t lambda mu nu := by
      dsimp [reaction, A, R] at *
      linarith
    constructor
    · exact hreact_bound
    · have : 0 < -nu / 9 := div_pos (by linarith) (by norm_num)
      exact this.trans_le hreact_bound

/-- The scalar lower barrier is itself preserved by every solution of the
three-dimensional curvature-reaction ODE. -/
theorem scalar_lower_barrier_along_eigenReaction
    {K T : ℝ} {lambda mu nu : ℝ → ℝ}
    (hK : 0 < K)
    (hlambda : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t)
    (hmu : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t)
    (hnuODE : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t)
    (hinitial : -3 * K ≤ scalar (lambda 0) (mu 0) (nu 0)) :
    ∀ t ∈ Set.Icc 0 T,
      -3 * (K / (1 + K * t)) ≤ scalar (lambda t) (mu t) (nu t) := by
  let b := fun t ↦ scalar (lambda t) (mu t) (nu t) + 3 * (K / (1 + K * t))
  let b' := fun t ↦ scalarReaction (lambda t) (mu t) (nu t) -
    3 * K ^ 2 / (1 + K * t) ^ 2
  have hbderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt b (b' t) t := by
    intro t ht
    have hden : 1 + K * t ≠ 0 := by
      have hKt : 0 ≤ K * t := mul_nonneg hK.le ht.1
      have : 0 < 1 + K * t := by linarith
      exact this.ne'
    have hR := ((hlambda t ht).add (hmu t ht)).add (hnuODE t ht)
    have hlinear := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul K)
    have hscale := (hasDerivAt_const t K).div hlinear hden
    have htotal := hR.add (hscale.const_mul 3)
    have hsame := htotal.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s ↦ by rfl))
    apply hsame.congr_deriv
    simp only [b', scalarReaction, Pi.add_apply, id_eq, zero_add, mul_one]
    field_simp [hden]
    ring
  have hbcont : ContinuousOn b (Set.Icc 0 T) := by
    intro t ht
    exact (hbderiv t ht).continuousAt.continuousWithinAt
  have hbzero : 0 ≤ b 0 := by
    dsimp [b]
    simp only [mul_zero, add_zero, div_one]
    linarith
  have hb := nonneg_on_Icc_of_deriv_pos_of_neg hbcont hbderiv hbzero
  have hbpoints : ∀ t ∈ Set.Icc 0 T, b t < 0 → 0 < b' t := by
    intro t ht hbt
    let A := K / (1 + K * t)
    let R := scalar (lambda t) (mu t) (nu t)
    have hKt : 0 ≤ K * t := mul_nonneg hK.le ht.1
    have hden : 0 < 1 + K * t := by linarith
    have hA : 0 < A := div_pos hK hden
    have hRlt : R < -3 * A := by
      dsimp [b, R, A] at hbt
      linarith
    have hRsq : 9 * A ^ 2 < R ^ 2 := by
      nlinarith
    have hreaction := scalar_sq_div_three_le_reaction
      (lambda t) (mu t) (nu t)
    have hreactionStrong : 3 * A ^ 2 < scalarReaction (lambda t) (mu t) (nu t) := by
      dsimp [R] at hRsq
      nlinarith
    dsimp [b', A] at *
    have hA_sq : (K / (1 + K * t)) ^ 2 = K ^ 2 / (1 + K * t) ^ 2 := by
      rw [div_pow]
    rw [hA_sq] at hreactionStrong
    have heq : 3 * K ^ 2 / (1 + K * t) ^ 2 =
        3 * (K ^ 2 / (1 + K * t) ^ 2) := by ring
    rw [heq]
    exact sub_pos.mpr hreactionStrong
  have hbnonneg := hb hbpoints
  intro t ht
  have := hbnonneg t ht
  dsimp [b] at this
  linarith

/-- The initial lower bound on the least eigenvalue places the
Hamilton--Ivey defect inside its invariant region. -/
theorem defect_zero_nonneg_of_least_eigenvalue_lower_bound
    {K lambda mu nu : ℝ}
    (hK : 0 < K) (hlm : mu ≤ lambda) (hmn : nu ≤ mu)
    (hnuNeg : nu < 0) (hnuLower : -K ≤ nu) :
    0 ≤ defect K 0 lambda mu nu := by
  have hnuPos : 0 < -nu := by linarith
  have hRord : 3 * nu ≤ scalar lambda mu nu := by
    dsimp [scalar]
    linarith
  have hratio : -3 ≤ scalar lambda mu nu / (-nu) := by
    apply (le_div_iff₀ hnuPos).2
    nlinarith
  have hscale : -nu ≤ K := by linarith
  have hlogle : Real.log (-nu) ≤ Real.log K :=
    Real.strictMonoOn_log.monotoneOn hnuPos hK hscale
  simp only [defect, mul_zero, add_zero, div_one]
  linarith

/-- **Hamilton--Ivey pinching for the curvature-reaction ODE, assuming the
standard scalar lower barrier.**

This turns the pointwise coercivity estimate into an invariant-region result
for differentiable ordered eigenvalue curves.  It is the complete ODE stage of
the argument; applying it to Ricci flow still requires the geometric curvature
evolution and tensor maximum principle. -/
theorem hamiltonIvey_ode_pinching_of_scalar_barrier
    {K T : ℝ} {lambda mu nu : ℝ → ℝ}
    (hK : 0 < K)
    (hlambda : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t)
    (hmu : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t)
    (hnuODE : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t)
    (hlm : ∀ t ∈ Set.Icc 0 T, mu t ≤ lambda t)
    (hmn : ∀ t ∈ Set.Icc 0 T, nu t ≤ mu t)
    (hnuNeg : ∀ t ∈ Set.Icc 0 T, nu t < 0)
    (hscalar : ∀ t ∈ Set.Icc 0 T,
      -3 * (K / (1 + K * t)) ≤ scalar (lambda t) (mu t) (nu t))
    (hinitial : 0 ≤ defect K 0 (lambda 0) (mu 0) (nu 0)) :
    ∀ t ∈ Set.Icc 0 T, 0 ≤ defect K t (lambda t) (mu t) (nu t) := by
  let w := fun t ↦ defect K t (lambda t) (mu t) (nu t)
  let w' := fun t ↦ reaction K t (lambda t) (mu t) (nu t)
  have hwderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt w (w' t) t := by
    intro t ht
    exact hasDerivAt_defect_of_eigenReaction hK ht.1 (hnuNeg t ht).ne
      (hlambda t ht) (hmu t ht) (hnuODE t ht)
  have hwcont : ContinuousOn w (Set.Icc 0 T) := by
    intro t ht
    exact (hwderiv t ht).continuousAt.continuousWithinAt
  apply nonneg_on_Icc_of_deriv_pos_of_neg hwcont hwderiv hinitial
  intro t ht hwt
  exact (hamiltonIvey_reaction_coercive hK ht.1 (hlm t ht) (hmn t ht)
    (hnuNeg t ht) (hscalar t ht) hwt).2.2

/-- ODE Hamilton--Ivey pinching from the standard initial least-eigenvalue
bound; the scalar barrier is derived internally. -/
theorem hamiltonIvey_ode_pinching
    {K T : ℝ} {lambda mu nu : ℝ → ℝ}
    (hK : 0 < K)
    (hlambda : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t)
    (hmu : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t)
    (hnuODE : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t)
    (hlm : ∀ t ∈ Set.Icc 0 T, mu t ≤ lambda t)
    (hmn : ∀ t ∈ Set.Icc 0 T, nu t ≤ mu t)
    (hnuNeg : ∀ t ∈ Set.Icc 0 T, nu t < 0)
    (hT : 0 ≤ T)
    (hnuLower : -K ≤ nu 0) :
    ∀ t ∈ Set.Icc 0 T, 0 ≤ defect K t (lambda t) (mu t) (nu t) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hscalarZero : -3 * K ≤ scalar (lambda 0) (mu 0) (nu 0) := by
    have hRord : 3 * nu 0 ≤ scalar (lambda 0) (mu 0) (nu 0) := by
      dsimp [scalar]
      linarith [hlm 0 hzero, hmn 0 hzero]
    linarith
  have hscalar := scalar_lower_barrier_along_eigenReaction hK
    hlambda hmu hnuODE hscalarZero
  apply hamiltonIvey_ode_pinching_of_scalar_barrier hK hlambda hmu hnuODE
    hlm hmn hnuNeg hscalar
  exact defect_zero_nonneg_of_least_eigenvalue_lower_bound hK
    (hlm 0 hzero) (hmn 0 hzero) (hnuNeg 0 hzero) hnuLower

/-- In the bad region where the Hamilton--Ivey defect is negative, the sum
of the two larger curvature eigenvalues is strictly positive.  This is the
sign needed to compose the defect with an upper support for the least
eigenvalue in the geometric maximum-principle argument. -/
theorem lambda_add_mu_pos_of_defect_neg
    {K t lambda mu nu : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t)
    (hlm : mu ≤ lambda) (hmn : nu ≤ mu) (hnu : nu < 0)
    (hscalar : -3 * (K / (1 + K * t)) ≤ scalar lambda mu nu)
    (hdefect : defect K t lambda mu nu < 0) :
    0 < lambda + mu := by
  let A : ℝ := K / (1 + K * t)
  let v : ℝ := -nu
  let R : ℝ := scalar lambda mu nu
  have hden : 0 < 1 + K * t := by positivity
  have hA : 0 < A := div_pos hK hden
  have hv : 0 < v := by simp [v, hnu]
  have hcrossRaw := (hamiltonIvey_reaction_coercive hK ht hlm hmn hnu
    hscalar hdefect).1
  have hcross : A < v := by simpa [A, v] using hcrossRaw
  by_contra hnot
  have hlmsum : lambda + mu ≤ 0 := le_of_not_gt hnot
  have hRle : R ≤ -v := by
    dsimp [R, scalar, v]
    linarith
  have hscalar' : -3 * A ≤ R := by simpa [A, R] using hscalar
  have hvle : v ≤ 3 * A := by linarith
  have hpoly : 0 ≤ 4 - 3 * A / v - v / A := by
    have hprod : 0 ≤ (3 * A - v) * (v - A) :=
      mul_nonneg (sub_nonneg.mpr hvle) (sub_nonneg.mpr hcross.le)
    rw [show 4 - 3 * A / v - v / A =
        ((3 * A - v) * (v - A)) / (A * v) by
      field_simp [hA.ne', hv.ne']
      ring]
    exact div_nonneg hprod (mul_nonneg hA.le hv.le)
  have hRdiv : -3 * A / v ≤ R / v := by
    exact (div_le_div_iff_of_pos_right hv).2 hscalar'
  have hlogRatio := Real.log_le_sub_one_of_pos (div_pos hv hA)
  have hlogs : Real.log v - Real.log A ≤ v / A - 1 := by
    rw [← Real.log_div hv.ne' hA.ne']
    exact hlogRatio
  have hdefect' : R / v - Real.log v + 3 + Real.log A < 0 := by
    simpa [R, v, A, defect] using hdefect
  have hbase : 0 ≤ -3 * A / v - (v / A - 1) + 3 := by
    convert hpoly using 1 <;> ring
  have hnonneg : 0 ≤ R / v - Real.log v + 3 + Real.log A := by
    linarith [hbase, hRdiv, hlogs]
  exact (not_lt_of_ge hnonneg) hdefect'

end HamiltonIveyReaction
