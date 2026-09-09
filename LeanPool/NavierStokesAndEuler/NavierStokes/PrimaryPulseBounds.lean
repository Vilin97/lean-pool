/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedQuotients
public import LeanPool.NavierStokesAndEuler.NavierStokes.PartitionedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurlClassBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianTailFlat

@[expose] public section

/-!
# Weighted bounds for the actual primary pulses

The homogeneous ODE is reparametrized onto a fixed unit interval.  Its
current endpoint becomes an additional parameter, so the weighted ODE jet
estimate controls actual joint parameter and slot derivatives.
-/

noncomputable section

namespace NavierStokes.PrimaryPulseBounds

open Set Function
open scoped ContDiff Topology InnerProductSpace BigOperators

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section TimeRescaling

variable {Q E F : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def timeLinear (σ : ℝ) : (Q × ℝ) →L[ℝ] (Q × ℝ) :=
  (ContinuousLinearMap.fst ℝ Q ℝ).prod (σ • ContinuousLinearMap.snd ℝ Q ℝ)

@[simp] theorem timeLinear_apply (σ : ℝ) (z : Q × ℝ) : timeLinear σ z = (z.1, σ * z.2) := rfl

theorem timeLinear_norm_le {σ : ℝ} (hσ : |σ| ≤ 1) : ‖timeLinear (Q := Q) σ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [timeLinear_apply, Prod.norm_def, one_mul, Real.norm_eq_abs, abs_mul]
  apply max_le
  · exact le_max_left _ _
  · exact (mul_le_of_le_one_left (abs_nonneg z.2) hσ).trans (le_max_right _ _)

theorem norm_jet_slot_coordinate (z : Q × ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y : Q × ℝ => y.2) z‖ ≤ max 1 |z.2| := by
  have hfd : fderiv ℝ (fun y : Q × ℝ => y.2) =
      fun _ => ContinuousLinearMap.snd ℝ Q ℝ := by
    funext y
    exact (ContinuousLinearMap.snd ℝ Q ℝ).hasFDerivAt.fderiv
  cases j with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using le_max_right 1 |z.2|
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      cases j with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          have hs : ‖ContinuousLinearMap.snd ℝ Q ℝ‖ ≤ 1 := by
            apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
            intro y
            change ‖y.2‖ ≤ 1 * ‖y‖
            simpa only [one_mul] using norm_snd_le y
          exact hs.trans (le_max_left _ _)
      | succ j =>
          rw [iteratedFDeriv_succ_const]
          simp only [Pi.zero_apply, norm_zero]
          exact zero_le_one.trans (le_max_left _ _)

theorem norm_lsmul_le_one : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro r
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg r)
  intro x
  exact le_of_eq (norm_smul r x)

/-- Pointwise higher Leibniz bound.  The right-hand bounds may be frozen
weights at this point, so no derivative of a majorant is introduced. -/
theorem smul_jet_bound {A : Q → ℝ} {B : Q → E} {U : Set Q}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    {x : Q} (hx : x ∈ U) {N j : ℕ} (hj : j ≤ N) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i ≤ N, ‖iteratedFDeriv ℝ i A x‖ ≤ C)
    (hb : ∀ i ≤ N, ‖iteratedFDeriv ℝ i B x‖ ≤ D) :
    ‖iteratedFDeriv ℝ j (fun y => A y • B y) x‖ ≤
      (2 : ℝ) ^ N * C * D := by
  have h := JetBounds.norm_iteratedFDeriv_bilinear_le_on
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)) hU hA hB hx (nat_le_infty j)
  have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i A x‖ * ‖iteratedFDeriv ℝ (j - i) B x‖) ≤ 2 ^ N * C * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C * D := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (ha i (hij.trans hj)) (Nat.cast_nonneg _))
          (hb (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hC)
      _ = (2 : ℝ) ^ j * C * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hc : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hc]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hD
  calc
    _ ≤ ‖ContinuousLinearMap.lsmul ℝ ℝ (E := E)‖ * ((2 : ℝ) ^ N * C * D) :=
      h.trans (mul_le_mul_of_nonneg_left hs
        (norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := E))))
    _ ≤ 1 * ((2 : ℝ) ^ N * C * D) :=
      mul_le_mul_of_nonneg_right (norm_lsmul_le_one (E := E)) (by positivity)
    _ = _ := one_mul _

/-- All derivatives of the rescaled coefficient, including derivatives of
its endpoint prefactor, follow from the original joint coefficient jets. -/
theorem rescale_jet_bound {A : Q × ℝ → E} {U : Set (Q × ℝ)}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    {z : Q × ℝ} {σ C T : ℝ} (hσ : |σ| ≤ 1) (hz : timeLinear σ z ∈ U)
    (hC : 0 ≤ C) (hT : 1 ≤ T) (ht : |z.2| ≤ T) {N j : ℕ} (hj : j ≤ N)
    (hjet : ∀ i ≤ N, ‖iteratedFDeriv ℝ i A (timeLinear σ z)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun y : Q × ℝ => y.2 • A (y.1, σ * y.2)) z‖ ≤
      (2 : ℝ) ^ N * T * C := by
  let V := (timeLinear (Q := Q) σ) ⁻¹' U
  have hV : IsOpen V := hU.preimage (timeLinear σ).continuous
  have hg : ContDiffOn ℝ ∞ (fun y : Q × ℝ => A (timeLinear σ y)) V :=
    hA.comp_continuousLinearMap _
  apply smul_jet_bound hV contDiffOn_snd hg hz hj (zero_le_one.trans hT) hC
  · intro i _
    exact (norm_jet_slot_coordinate z i).trans (max_le hT ht)
  · intro i hi
    have hh := PhaseJetBounds.norm_jet_comp_linear hU hA (timeLinear σ) hz i
    apply hh.trans
    have hn : ‖timeLinear (Q := Q) σ‖ ^ i ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg (timeLinear (Q := Q) σ))
        (timeLinear_norm_le (Q := Q) hσ) i
    exact (mul_le_mul (hjet i hi) hn (pow_nonneg (norm_nonneg _) i) hC).trans_eq (mul_one C)

end TimeRescaling

noncomputable def rescaleConstant (N : ℕ) (K : ℝ) : ℝ := 2 ^ N * K ^ 2 + K + 1

theorem le_rescaleConstant (N : ℕ) (K : ℝ) : K ≤ rescaleConstant N K := by
  unfold rescaleConstant
  nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N) (sq_nonneg K)]

section JointEstimate

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Actual joint derivatives of a homogeneous fundamental solution retain
the reference envelope.  The solution is the constructed Volterra solution
in `JointODE`, rather than an assumed smooth solution family. -/
theorem homogeneous_joint_jet_bound
    {L S K μ : ℝ} (_hL : 0 < L) (hS : 1 ≤ S) (hK : 1 ≤ K) (hμ : 0 ≤ μ)
    (hslot : L ≤ K * S) (hExp : Real.exp (μ * L) ≤ K)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc 0 L ⊆ V)
    (A : Q × ℝ → H →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    (P rate : ℝ → ℝ) (hP : ∀ t, 0 < P t)
    (hdP : ∀ t, HasDerivAt P (rate t * P t) t)
    (e : H) (he : ‖e‖ ≤ 1) {p : Q} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L)
    (henergy : ∀ v ∈ Icc 0 L, ∀ x : H,
      ⟪x, A (p, v) x⟫_ℝ ≤ (rate v + μ) * ‖x‖ ^ 2)
    (m N : ℕ)
    (hjets : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j A (p, v)‖ ≤ K * S ^ m)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j
      (JointODE.reparamSolution 0 A (fun _ => P 0 • e) (fun _ => 0)) (p, t)‖ ≤
      ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (j + 1) *
        S ^ ((m + 2) * (j + 1)) * P t := by
  let K' := rescaleConstant N K
  have hKK' : K ≤ K' := le_rescaleConstant N K
  have hK' : 1 ≤ K' := hK.trans hKK'
  have hKS : 1 ≤ K * S := one_le_mul_of_one_le_of_one_le hK hS
  have hz : (p, t) ∈ U ×ˢ Icc 0 L := ⟨hp, ht⟩
  let Ω := (JointODE.timeMap (P := Q) 0) ⁻¹' (U ×ˢ V)
  have hΩ : IsOpen Ω := (hU.prod hV).preimage (JointODE.contDiff_timeMap 0).continuous
  have hsubset : ({(p, t)} : Set (Q × ℝ)) ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    rintro ⟨z, σ⟩ ⟨hz', hσ⟩
    have heq : z = (p, t) := mem_singleton_iff.mp hz'
    subst z
    exact ⟨hp, hI (JointODE.affineTime_mem ht hσ)⟩
  obtain ⟨O, T, hO, hT, hzO, hIT, hOT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hΩ hsubset
  have hpoint : (p, t) ∈ O := hzO (mem_singleton _)
  have hmap : MapsTo (JointODE.timeMap (P := Q) 0) (O ×ˢ T) (U ×ˢ V) := hOT
  have hAr : ContDiffOn ℝ ∞ (JointODE.rescale 0 A) (O ×ˢ T) :=
    JointODE.rescale_contDiffOn A hA hmap
  have hfr : ContDiffOn ℝ ∞ (JointODE.rescale 0 (fun _ : Q × ℝ => (0 : H))) (O ×ˢ T) :=
    JointODE.rescale_contDiffOn _ contDiffOn_const hmap
  have hinside (σ : Icc (0 : ℝ) 1) : σ.1 * t ∈ Icc 0 L := by
    simpa only [JointODE.affineTime, sub_zero, zero_add] using JointODE.affineTime_mem ht σ.2
  have hweight : ∀ σ, HasDerivAt (fun r => P (r * t))
      ((t * rate (σ * t)) * P (σ * t)) σ := by
    intro σ
    convert! (hdP (σ * t)).comp σ ((hasDerivAt_id σ).mul_const t) using 1
    ring
  have henergy' : ∀ σ : Icc (0 : ℝ) 1, ∀ x : H,
      ⟪x, JointODE.rescale 0 A ((p, t), σ) x⟫_ℝ ≤
        ((t * rate (σ * t)) + t * μ) * ‖x‖ ^ 2 := by
    intro σ x
    have hh := mul_le_mul_of_nonneg_left (henergy _ (hinside σ) x) ht.1
    convert! hh using 1
    · simp only [JointODE.rescale, JointODE.timeMap, JointODE.affineTime, sub_zero, zero_add,
        _root_.smul_apply, real_inner_smul_right]
    · ring
  have hAjet : ∀ k ≤ N, ∀ σ : Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun q => JointODE.rescale 0 A (q, σ)) (p, t)‖ ≤ K' * S ^ (m + 1) := by
    intro k hk σ
    have hσ : |(σ : ℝ)| ≤ 1 := by rw [abs_of_nonneg σ.2.1]; exact σ.2.2
    have hh := rescale_jet_bound (hU.prod hV) hA hσ
      (show timeLinear (σ : ℝ) (p, t) ∈ U ×ˢ V from ⟨hp, hI (hinside σ)⟩)
      (show 0 ≤ K * S ^ m by positivity) hKS
      (show |t| ≤ K * S by rw [abs_of_nonneg ht.1]; exact ht.2.trans hslot) hk
      (fun i hi => hjets i hi _ (hinside σ))
    have hconst : (2 : ℝ) ^ N * K ^ 2 ≤ K' := by
      dsimp [K', rescaleConstant]
      linarith
    calc
      _ ≤ (2 : ℝ) ^ N * (K * S) * (K * S ^ m) := by
        simpa only [JointODE.rescale, JointODE.timeMap, JointODE.affineTime, sub_zero, zero_add]
          using hh
      _ = ((2 : ℝ) ^ N * K ^ 2) * S ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (by positivity)
  have hxjet : ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (fun _ : Q × ℝ => P 0 • e) (p, t)‖ ≤
        1 * K' * S ^ (m + 1) * P ((0 : ℝ) * t) := by
    intro k _
    have hcoef : 1 ≤ K' * S ^ (m + 1) :=
      one_le_mul_of_one_le_of_one_le hK' (one_le_pow₀ hS)
    cases k with
    | zero =>
        rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (hP 0)]
        simp only [one_mul, zero_mul]
        nlinarith [hP 0]
    | succ k =>
        rw [iteratedFDeriv_succ_const]
        simp only [Pi.zero_apply, norm_zero, one_mul, zero_mul]
        have hp0 := hP 0
        positivity
  have hfjet : ∀ k ≤ N, ∀ σ : Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun q => JointODE.rescale 0 (fun _ : Q × ℝ => (0 : H)) (q, σ)) (p, t)‖ ≤
        1 * K' * S ^ (m + 1) * P ((σ : ℝ) * t) := by
    intro k _ σ
    simp only [JointODE.rescale, smul_zero, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero,
      one_mul]
    have hp0 := hP ((σ : ℝ) * t)
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hK')
      (pow_nonneg (zero_le_one.trans hS) _)) hp0.le
  have hExp' : Real.exp ((t * μ) * ((1 : ℝ) - 0)) ≤ K' := by
    apply (Real.exp_le_exp.mpr (show (t * μ) * (1 - 0) ≤ μ * L by nlinarith [ht.2])).trans
    exact hExp.trans hKK'
  have hh := WeightedODEJets.norm_iteratedFDeriv_odeFamily_le_polynomial
    (a := 0) (b := 1) zero_le_one O T hO hT hIT
    (JointODE.rescale 0 A) (fun _ : Q × ℝ => P 0 • e)
    (JointODE.rescale 0 (fun _ : Q × ℝ => (0 : H)))
    hAr contDiffOn_const hfr hpoint (fun σ => t * rate (σ * t)) (fun σ => P (σ * t))
    (mul_nonneg ht.1 hμ) (fun σ => hP _) hweight henergy' hExp' hS hK' zero_le_one
    (show (1 : ℝ) - 0 ≤ K' * S by nlinarith) (m + 1) N hAjet hxjet hfjet j hj
    ⟨1, zero_le_one, le_rfl⟩
  unfold JointODE.reparamSolution
  simpa only [one_mul, Nat.add_assoc] using hh

end JointEstimate

/-- Polynomial jets with a retained pointwise envelope.  This is only an
intermediate family predicate; the constructed solution is proved to satisfy it. -/
structure EnvelopeJets {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : PhaseJetBounds.Domain ι E) (w : ι → E → ℝ) (f : ι → E → F) : Prop where
  nonneg : ∀ i x, x ∈ D.carrier i → 0 ≤ w i x
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (D.carrier i)
  bound : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ i x, x ∈ D.carrier i →
    ∀ j ≤ N, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * D.scale i ^ m * w i x

noncomputable def productDomain {ι E : Type*} [NormedAddCommGroup E]
    (D : PhaseJetBounds.Domain ι E) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) :
    PhaseJetBounds.Domain ι (E × ℝ) where
  scale := D.scale
  carrier i := D.carrier i ×ˢ V i
  isOpen i := (D.isOpen i).prod (hV i)
  one_le_scale := D.one_le_scale

section EnvelopeCalculus

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {D : PhaseJetBounds.Domain ι E} {D' : PhaseJetBounds.Domain ι F}

theorem EnvelopeJets.comp {f : ι → F → G} {w : ι → F → ℝ}
    (hf : EnvelopeJets D' w f) {g : ι → E → F} (hg : PhaseJetBounds.PolynomialJets D g)
    (hscale : ∀ i, D'.scale i = D.scale i)
    (hmap : ∀ i, MapsTo (g i) (D.carrier i) (D'.carrier i)) :
    EnvelopeJets D (fun i x => w i (g i x)) (fun i x => f i (g i x)) := by
  refine ⟨fun i x hx => hf.nonneg i _ (hmap i hx),
    fun i => (hf.smooth i).comp (hg.smooth i) (hmap i), ?_⟩
  intro N
  obtain ⟨A, hA, m, ha⟩ := hf.bound N
  obtain ⟨B, hB, k, hb⟩ := hg.bound N
  refine ⟨(N.factorial : ℝ) * A * B ^ N, ?_, m + k * N, ?_⟩
  · have hfac : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfac hA)
      (one_le_pow₀ hB)
  intro i x hx j hj
  have hC : 1 ≤ B * D.scale i ^ k :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ (D.one_le_scale i))
  have hw := hf.nonneg i (g i x) (hmap i hx)
  have h := norm_iteratedFDerivWithin_comp_le (hf.smooth i) (hg.smooth i) (nat_le_infty j)
    (D'.isOpen i).uniqueDiffOn (D.isOpen i).uniqueDiffOn (hmap i) hx
    (C := A * D'.scale i ^ m * w i (g i x)) (D := B * D.scale i ^ k)
    (fun a haj => ?_) (fun a ha1 haj => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j (D.isOpen i) hx] at h
    change ‖iteratedFDeriv ℝ j (f i ∘ g i) x‖ ≤ _
    have hA0 : 0 ≤ A * D'.scale i ^ m * w i (g i x) := by
      have := zero_le_one.trans (D'.one_le_scale i)
      positivity
    calc
      _ ≤ (j.factorial : ℝ) * (A * D'.scale i ^ m * w i (g i x)) *
          (B * D.scale i ^ k) ^ j := h
      _ ≤ (N.factorial : ℝ) * (A * D'.scale i ^ m * w i (g i x)) *
          (B * D.scale i ^ k) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA0
        · exact pow_le_pow_right₀ hC hj
        · positivity
        · positivity
      _ = _ := by rw [hscale, mul_pow, pow_add, pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen a (D'.isOpen i) (hmap i hx)]
    exact ha i _ (hmap i hx) a (haj.trans hj)
  · rw [iteratedFDerivWithin_of_isOpen a (D.isOpen i) hx]
    exact (hb i a (haj.trans hj) x hx).trans
      (by simpa using pow_le_pow_right₀ hC ha1)

end EnvelopeCalculus

section LinearPullback

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {D : PhaseJetBounds.Domain ι E} {D' : PhaseJetBounds.Domain ι F}

theorem EnvelopeJets.of_polynomial {f : ι → E → G} (hf : PhaseJetBounds.PolynomialJets D f) :
    EnvelopeJets D (fun _ _ => 1) f := by
  refine ⟨fun _ _ _ => zero_le_one, hf.smooth, ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  exact ⟨C, hC, m, fun i x hx j hj => by simpa only [mul_one] using hm i j hj x hx⟩

theorem EnvelopeJets.to_polynomial {w : ι → E → ℝ} {f : ι → E → G}
    (hf : EnvelopeJets D w f) (hw : ∀ i x, x ∈ D.carrier i → w i x ≤ 1) :
    PhaseJetBounds.PolynomialJets D f := by
  refine ⟨hf.smooth, ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i j hj x hx
  exact (hm i x hx j hj).trans (by
    have h0 : 0 ≤ C * D.scale i ^ m :=
      mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans (D.one_le_scale i)) _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw i x hx) h0)

theorem EnvelopeJets.precomp_linear {f : ι → F → G} {w : ι → F → ℝ}
    (hf : EnvelopeJets D' w f) (L : ι → E →L[ℝ] F)
    (hscale : ∀ i, D'.scale i = D.scale i)
    (hmap : ∀ i, MapsTo (L i) (D.carrier i) (D'.carrier i))
    {C : ℝ} {k : ℕ} (hC : 1 ≤ C) (hL : ∀ i, ‖L i‖ ≤ C * D.scale i ^ k) :
    EnvelopeJets D (fun i x => w i (L i x)) (fun i x => f i (L i x)) := by
  refine ⟨fun i x hx => hf.nonneg i _ (hmap i hx),
    fun i => (hf.smooth i).comp (L i).contDiff.contDiffOn (hmap i), ?_⟩
  intro N
  obtain ⟨A, hA, m, hm⟩ := hf.bound N
  refine ⟨A * C ^ N, one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hC), m + k * N, ?_⟩
  intro i x hx j hj
  have hc : 1 ≤ C * D.scale i ^ k :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (D.one_le_scale i))
  have hpow : ‖L i‖ ^ j ≤ (C * D.scale i ^ k) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg _) (hL i) j).trans (pow_le_pow_right₀ hc hj)
  have hw := hf.nonneg i (L i x) (hmap i hx)
  have hb : 0 ≤ A * D'.scale i ^ m * w i (L i x) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hA)
      (pow_nonneg (zero_le_one.trans (D'.one_le_scale i)) _)) hw
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i) (L i x)‖ * ‖L i‖ ^ j :=
      PhaseJetBounds.norm_jet_comp_linear (D'.isOpen i) (hf.smooth i) (L i) (hmap i hx) j
    _ ≤ (A * D'.scale i ^ m * w i (L i x)) * (C * D.scale i ^ k) ^ N :=
      mul_le_mul (hm i _ (hmap i hx) j hj) hpow (pow_nonneg (norm_nonneg _) _) hb
    _ = _ := by rw [hscale, mul_pow, pow_add, pow_mul]; ring

end LinearPullback

section Classes

open WeightedClasses

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def phaseDomain (s : StripData E) : PhaseJetBounds.Domain ℕ E where
  scale := s.slow
  carrier _ := s.domain
  isOpen _ := s.isOpen_domain
  one_le_scale := s.one_le_slow

theorem EnvelopeJets.memClass {D : PhaseJetBounds.Domain ℕ E}
    {w : ℕ → E → ℝ} {f : ℕ → E → F} (hf : EnvelopeJets D w f) (s : StripData E)
    (hscale : ∀ n, D.scale n = s.slow n) (hdom : ∀ n, D.carrier n = s.domain) :
    MemClass s w 0 f := by
  refine ⟨fun n x hx => hf.nonneg n x (hdom n ▸ hx),
    fun n => hdom n ▸ hf.smooth n, ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, zero_le_one.trans hC, m, ?_⟩
  intro n x hx j hj
  have hw := hf.nonneg n x (hdom n ▸ hx)
  have hh := hm n x (hdom n ▸ hx) j hj
  rw [hscale n] at hh
  apply hh.trans
  simp only [majorant, Real.rpow_zero, mul_one]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n))
      (s.slow_le_growth n x) m) (zero_le_one.trans hC)) hw

theorem polynomial_memClass (s : StripData E) {f : ℕ → E → F}
    (hf : PhaseJetBounds.PolynomialJets (phaseDomain s) f) : UnweightedClass s 0 f :=
  (EnvelopeJets.of_polynomial hf).memClass s (fun _ => rfl) (fun _ => rfl)

end Classes

section FamilyODE

variable {ι : Type*} {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every fixed joint jet of the actual homogeneous family has a single
band-uniform polynomial bound times the original reference envelope. -/
theorem homogeneous_family_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (L μ : ι → ℝ) (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    (A : ι → Q × ℝ → H →L[ℝ] H)
    (hA : PhaseJetBounds.PolynomialJets (productDomain D V hV) A)
    (P rate : ι → ℝ → ℝ) (hP : ∀ i t, 0 < P i t)
    (hdP : ∀ i t, HasDerivAt (P i) (rate i t * P i t) t)
    (e : H) (he : ‖e‖ ≤ 1) {K₀ : ℝ} (hK₀ : 1 ≤ K₀)
    (hμ : ∀ i, 0 ≤ μ i) (hslot : ∀ i, L i ≤ K₀ * D.scale i)
    (hExp : ∀ i, Real.exp (μ i * L i) ≤ K₀)
    (henergy : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), ∀ x : H,
      ⟪x, A i (p, v) x⟫_ℝ ≤ (rate i v + μ i) * ‖x‖ ^ 2) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => P i z.2)
      (fun i => JointODE.reparamSolution 0 (A i) (fun _ => P i 0 • e) (fun _ => 0)) := by
  refine ⟨fun i x _ => (hP i x.2).le, ?_, ?_⟩
  · intro i z hz
    exact (JointODE.reparamSolution_contDiffAt (D.carrier i) (V i) (D.isOpen i) (hV i) (hI i)
      (A i) (fun _ => P i 0 • e) (fun _ => 0) (hA.smooth i) contDiffOn_const contDiffOn_const
      (show z ∈ D.carrier i ×ˢ Icc 0 (L i) from ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)).contDiffWithinAt
  intro N
  obtain ⟨C, hC, m, hm⟩ := hA.bound N
  let K := C + K₀ + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hK₀K : K₀ ≤ K := by dsimp [K]; linarith
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  refine ⟨B ^ (N + 1), one_le_pow₀ hB, (m + 2) * (N + 1), ?_⟩
  intro i z hz j hj
  have hAj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L i),
      ‖iteratedFDeriv ℝ k (A i) (z.1, v)‖ ≤ K * D.scale i ^ m := by
    intro k hk v hv
    exact (hm i k hk (z.1, v) ⟨hz.1, hI i hv⟩).trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg (zero_le_one.trans (D.one_le_scale i)) _))
  have hh := homogeneous_joint_jet_bound (hL i) (D.one_le_scale i) hK (hμ i)
    ((hslot i).trans (mul_le_mul_of_nonneg_right hK₀K (zero_le_one.trans (D.one_le_scale i))))
    ((hExp i).trans hK₀K) (D.carrier i) (V i) (D.isOpen i) (hV i) (hI i)
    (A i) (hA.smooth i) (P i) (rate i) (hP i) (hdP i) e he hz.1
    ⟨hz.2.1.le, hz.2.2.le⟩ (henergy i z.1 hz.1) m N hAj j hj
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (hP i z.2).le
  exact mul_le_mul (pow_le_pow_right₀ hB (Nat.add_le_add_right hj 1))
    (pow_le_pow_right₀ (D.one_le_scale i) (Nat.mul_le_mul_left (m + 2) (Nat.add_le_add_right hj 1)))
    (pow_nonneg (zero_le_one.trans (D.one_le_scale i)) _) (pow_nonneg (zero_le_one.trans hB) _)

end FamilyODE

section IntegratedJets

variable {ι : Type*} {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Joint coefficient jets control the actual continuous-path jets in the
supremum norm, uniformly on a fixed compact integration interval. -/
theorem pathFamily_polynomial (D : PhaseJetBounds.Domain ι Q)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) {a b : ℝ}
    (hI : ∀ i, Icc a b ⊆ V i) {F : ι → Q × ℝ → H}
    (hF : PhaseJetBounds.PolynomialJets (productDomain D V hV) F) :
    PhaseJetBounds.PolynomialJets D (fun i => SmoothPathFamily.pathFamily (a := a) (b := b) (F i))
      := by
  refine ⟨fun i => SmoothPathFamily.contDiffOn_pathFamily_of_joint
    (D.carrier i) (V i) (D.isOpen i) (hV i) (hI i) (F i) (hF.smooth i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hF.parameter_bound N
  refine ⟨C, hC, m, ?_⟩
  intro i k hk p hp
  have hC0 : 0 ≤ C * D.scale i ^ m :=
    mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans (D.one_le_scale i)) _)
  apply WeightedODEJets.multilinear_norm_le_of_unit _ hC0
  intro v hv
  apply (ContinuousMap.norm_le _ hC0).mpr
  intro t
  rw [SmoothPathFamily.iteratedFDeriv_pathFamily_apply (D.carrier i) (V i)
    (D.isOpen i) (hV i) (hI i) (F i) (hF.smooth i) hp]
  have hprod : (∏ j, ‖v j‖) ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun j _ => hv j)
  exact ((iteratedFDeriv ℝ k (fun q => F i (q, t)) p).le_opNorm v).trans
    ((mul_le_mul (hm i p t ⟨hp, hI i t.2⟩ k hk) hprod
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC0).trans_eq (mul_one _))

variable [CompleteSpace H]

noncomputable def intervalIntegralCLM {a b : ℝ} (hab : a ≤ b) :
    C(Icc a b, H) →L[ℝ] H :=
  (ContinuousMap.evalCLM ℝ (⟨b, hab, le_rfl⟩ : Icc a b)).comp (ParametricODE.integrator hab)

/-- The actual parameter-dependent integral has polynomial jets; no
smoothness or derivative estimate for the integral is an input. -/
theorem intervalIntegral_polynomial (D : PhaseJetBounds.Domain ι Q)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ i, Icc a b ⊆ V i) {F : ι → Q × ℝ → H}
    (hF : PhaseJetBounds.PolynomialJets (productDomain D V hV) F) :
    PhaseJetBounds.PolynomialJets D (fun i p => ∫ t in a..b, F i (p, t)) := by
  apply ((pathFamily_polynomial D V hV hI hF).clm (intervalIntegralCLM (H := H) hab)).congr
  intro i p hp
  change (∫ t in a..b, ParametricODE.extend hab
    (SmoothPathFamily.pathFamily (F i) p) t) = ∫ t in a..b, F i (p, t)
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  exact (ParametricODE.extend_coe hab _ ⟨t, ht'⟩).trans
    (SmoothPathFamily.pathFamily_apply (F i) p
      (SmoothPathFamily.slice_continuous ((hF.smooth i).continuousOn.mono
        (Set.prod_mono Subset.rfl (hI i))) hp) ⟨t, ht'⟩)

end IntegratedJets

abbrev State := MovingFrameODE.Plane
abbrev Space := MovingFrameODE.Space

noncomputable def positiveSeed : State := !₂[1, 0]

theorem positiveSeed_norm : ‖positiveSeed‖ = 1 := by
  have h : ‖positiveSeed‖ ^ 2 = 1 := by
    calc
      _ = (positiveSeed 0) ^ 2 + (positiveSeed 1) ^ 2 := ViscousPropagator.plane_norm_sq
        positiveSeed
      _ = 1 := by norm_num [positiveSeed]
  nlinarith [norm_nonneg positiveSeed]

noncomputable def referenceP (lam u L t : ℝ) : ℝ :=
  GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u L) (L / 2) t

theorem referenceP_pos (lam u L t : ℝ) : 0 < referenceP lam u L t :=
  GaussianEnvelope.envelope_pos _ _ _

theorem referenceP_hasDerivAt (lam u L t : ℝ) :
    HasDerivAt (referenceP lam u L)
      (GaussianEnvelope.referenceRate lam u L t * referenceP lam u L t) t :=
  ViscousPropagator.hasDerivAt_envelope (ViscousPropagator.continuous_referenceRate lam u L) _ _

theorem referenceP_le_one {lam u L t : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hL : 0 < L) (ht : t ∈ Icc 0 L) : referenceP lam u L t ≤ 1 := by
  apply (GaussianEnvelope.reference_gaussian_bounds hlam hu hL ht).2.trans
  apply Real.exp_le_one_iff.mpr
  have hc := GaussianEnvelope.referenceMinSlope_pos hlam hu
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hu.le hc.le)) (sq_nonneg _))
    (by positivity)

section ActualFundamental

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

noncomputable def fundamental (d : PrimaryODE.FrameData Q) (lam u L : ℝ) : Q × ℝ → State :=
  JointODE.reparamSolution 0 (d.coefficient 1)
    (fun _ => referenceP lam u L 0 • positiveSeed) (fun _ => 0)

/-- The phase-derived coefficient jets are applied to the actual growing
fundamental, with its actual viscosity and four moving-basis errors. -/
theorem fundamental_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (d : ι → PrimaryODE.FrameData Q)
    (hd : PhaseJetBounds.FrameJets (productDomain D V hV) d)
    (lam u L : ι → ℝ) (hlam : ∀ i, 0 < lam i) (_hu : ∀ i, 0 < u i)
    (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    {M C B : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hslot : ∀ i, L i ≤ M * D.scale i)
    (heigen : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      (d i).eigenvalue (p, v) = ViscousPropagator.referenceEigenvalue (lam i) (u i) (L i) v)
    (hν : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), 0 ≤ (d i).viscosity (p, v))
    (hνerr : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      ViscousPropagator.referenceViscosity (lam i) (u i) (L i) v - B / D.scale i ≤
        (d i).viscosity (p, v))
    (herr : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      |(d i).error11 (p, v)| ≤ C / D.scale i ∧ |(d i).error12 (p, v)| ≤ C / D.scale i ∧
      |(d i).error21 (p, v)| ≤ C / D.scale i ∧ |(d i).error22 (p, v)| ≤ C / D.scale i) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) z.2)
      (fun i => fundamental (d i) (lam i) (u i) (L i)) := by
  let μ := fun i => (B + 4 * C) / D.scale i
  let K := M + Real.exp ((B + 4 * C) * M) + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith [Real.exp_pos ((B + 4 * C) * M)]
  have hμ (i) : 0 ≤ μ i := div_nonneg (by positivity) (zero_le_one.trans (D.one_le_scale i))
  apply homogeneous_family_envelope_jets D V hV L μ hL hI (fun i => (d i).coefficient 1)
    (hd.coefficient 1) (fun i => referenceP (lam i) (u i) (L i))
    (fun i => GaussianEnvelope.referenceRate (lam i) (u i) (L i))
    (fun i => referenceP_pos _ _ _) (fun i => referenceP_hasDerivAt _ _ _)
    positiveSeed positiveSeed_norm.le hK hμ
  · intro i
    apply (hslot i).trans
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (D.one_le_scale i))
    dsimp [K]
    linarith [Real.exp_pos ((B + 4 * C) * M)]
  · intro i
    have hS : 0 < D.scale i := zero_lt_one.trans_le (D.one_le_scale i)
    have hμL : μ i * L i ≤ (B + 4 * C) * M := by
      calc
        _ ≤ μ i * (M * D.scale i) := mul_le_mul_of_nonneg_left (hslot i) (hμ i)
        _ = _ := by dsimp [μ]; field_simp
    apply (Real.exp_le_exp.mpr hμL).trans
    dsimp [K]
    linarith
  · intro i p hp v hv x
    have he := (d i).energy_bound (p, v) (by norm_num : (1 : ℤ) ≠ 0)
      (by rw [heigen i p hp v hv]; exact ViscousPropagator.referenceEigenvalue_nonneg (hlam i).le _
        _ _)
      (hν i p hp v hv) (hνerr i p hp v hv) (herr i p hp v hv) x
    rw [heigen i p hp v hv] at he
    exact he

omit [NormedSpace ℝ Q] in
theorem fundamental_eq_primary {d : PrimaryODE.FrameData Q} {lam u L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Q} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L) :
    fundamental d lam u L (p, t) =
      PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t := by
  have he := JointODE.reparamSolution_eq_actualSolution hL.le
    (d.coefficient 1) (fun _ : Q => referenceP lam u L 0 • positiveSeed) (fun _ => 0)
    hA continuousOn_const (z := (p, t)) ⟨hp, ht⟩
  convert! he using 1
  simp only [PrimaryODE.primary, PrimaryODE.solution, PrimaryODE.extendedFamily,
    JointODE.actualSolution, PrimaryODE.FrameData.forcing_zero_function]
  congr 2
  ext k
  fin_cases k <;> simp [PrimaryODE.primarySeed, positiveSeed]

end ActualFundamental

section NormalizeSlot

variable {ι : Type*} {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem timeLinear_norm_le_max (t : ℝ) : ‖timeLinear (Q := Q) t‖ ≤ max 1 |t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _))
  intro z
  rw [timeLinear_apply, Prod.norm_def]
  apply max_le
  · exact (norm_fst_le z).trans (le_mul_of_one_le_left (norm_nonneg z) (le_max_left _ _))
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_max_right _ _) (norm_snd_le z) (abs_nonneg z.2)
      (zero_le_one.trans (le_max_left _ _))

/-- Changing v to Lθ costs polynomial factors only and preserves the exact
Gaussian weight at v=Lθ. -/
theorem EnvelopeJets.normalize_slot
    (D : PhaseJetBounds.Domain ι Q) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    {w : ι → Q × ℝ → ℝ} {f : ι → Q × ℝ → H}
    (hf : EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo)) w f)
    {M : ℝ} (hM : 1 ≤ M) (hslot : ∀ i, L i ≤ M * D.scale i) :
    EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => w i (z.1, L i * z.2)) (fun i z => f i (z.1, L i * z.2)) := by
  refine hf.precomp_linear
    (D := productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
    (fun i => timeLinear (L i)) (fun _ => rfl) ?_
    (show 1 ≤ M + 1 by linarith) (k := 1) ?_
  · intro i z hz
    refine ⟨hz.1, ?_, ?_⟩
    · exact mul_pos (hL i) hz.2.1
    · change L i * z.2 < L i
      nlinarith [hL i, hz.2.2]
  · intro i
    apply (timeLinear_norm_le_max (L i)).trans
    rw [abs_of_pos (hL i), pow_one]
    change max 1 (L i) ≤ (M + 1) * D.scale i
    apply max_le
    · nlinarith [D.one_le_scale i]
    · nlinarith [hslot i, D.one_le_scale i]

end NormalizeSlot

section GeometrySynthesis

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

noncomputable def synthesisColumn (d : PrimaryODE.FrameData Q) (j : Fin 2) (z : Q × ℝ) : Space :=
  MovingFrameODE.pack 1 ((-d.rho z) • d.frame z 0 +
    (if j = 0 then d.eigenvector z else -d.eigenvector z) • d.frame z 1)

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem ambient_eq_synthesis (d : PrimaryODE.FrameData Q) (z : Q × ℝ) (w : State) :
    d.ambient z w = w 0 • synthesisColumn d 0 z + w 1 • synthesisColumn d 1 z := by
  ext i
  fin_cases i <;>
    simp [PrimaryODE.FrameData.ambient, MovingFrameODE.tangent, MovingFrameODE.pack,
      synthesisColumn] <;> ring

theorem synthesisColumn_polynomial {D : PhaseJetBounds.Domain ι (Q × ℝ)}
    {d : ι → PrimaryODE.FrameData Q} (hd : PhaseJetBounds.FrameJets D d) (j : Fin 2) :
    PhaseJetBounds.PolynomialJets D (fun i => synthesisColumn (d i) j) := by
  have hk := hd.rho.neg.smul hd.K
  have hn := hd.eigenvector.smul hd.N
  fin_cases j
  · exact ((PhaseJetBounds.PolynomialJets.const_fixed (D := D) (1 : ℝ)).pair (hk.add hn)).clm
      MovingFrameODE.packCLM
  · apply (((PhaseJetBounds.PolynomialJets.const_fixed (D := D) (1 : ℝ)).pair
      (hk.sub hn)).clm MovingFrameODE.packCLM).congr
    intro i x hx
    change MovingFrameODE.pack 1 ((-(d i).rho x) • (d i).frame x 0 -
      (d i).eigenvector x • (d i).frame x 1) = synthesisColumn (d i) 1 x
    simp [synthesisColumn, sub_eq_add_neg, neg_smul]

end GeometrySynthesis

section DomainRestriction

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem EnvelopeJets.restrict {D D' : PhaseJetBounds.Domain ι E} {w : ι → E → ℝ}
    {f : ι → E → F} (hf : EnvelopeJets D w f)
    (hscale : ∀ i, D.scale i = D'.scale i) (hsub : ∀ i, D'.carrier i ⊆ D.carrier i) :
    EnvelopeJets D' w f := by
  refine ⟨fun i x hx => hf.nonneg i x (hsub i hx), fun i => (hf.smooth i).mono (hsub i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i x hx j hj
  simpa only [hscale i] using hm i x (hsub i hx) j hj

theorem polynomial_memClass_of_domain {D : PhaseJetBounds.Domain ℕ E} {f : ℕ → E → F}
    (hf : PhaseJetBounds.PolynomialJets D f) (s : WeightedClasses.StripData E)
    (hscale : ∀ i, D.scale i = s.slow i) (hdom : ∀ i, D.carrier i = s.domain) :
    WeightedClasses.UnweightedClass s 0 f :=
  (EnvelopeJets.of_polynomial hf).memClass s hscale hdom

end DomainRestriction

section AmbientClass

open WeightedClasses

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable {s : StripData (Q × ℝ)} {P : ℕ → Q × ℝ → ℝ}

theorem synthesis_memClass {c : Fin 2 → ℕ → Q × ℝ → Space}
    {z : ℕ → Q × ℝ → State} (hc : ∀ j, UnweightedClass s 0 (c j))
    (hz : MemClass s P 0 z) :
    MemClass s P 0 (fun n x => z n x 0 • c 0 n x + z n x 1 • c 1 n x) := by
  have hz0 := hz.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  have hz1 := hz.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)
  have h0 : MemClass s P 0 (fun n x => z n x 0 • c 0 n x) := by
    simpa only [PiLp.proj_apply, mul_one, zero_add] using hz0.smul (hc 0)
  have h1 : MemClass s P 0 (fun n x => z n x 1 • c 1 n x) := by
    simpa only [PiLp.proj_apply, mul_one, zero_add] using hz1.smul (hc 1)
  exact h0.add h1

end AmbientClass

section CovarianceIntegrals

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The two actual normalized-slot integrals making up each covariance
column. The prefactor includes the native Haar factor and ci times L. -/
noncomputable def covarianceMatrix (a b : ℝ) (pref : Fin 2 → ι → ℝ)
    (ψ : Fin 2 → ι → Q × ℝ → ℝ) (v : Fin 2 → ι → Q × ℝ → Space)
    (n : ι) (p : Q) : SmoothCovariance.Mat2 :=
  fun r c => pref c n * ∫ t in a..b, (ψ c n (p, t)) ^ 2 *
    (v c n (p, t) 0 * v c n (p, t) r.succ)

theorem covarianceMatrix_entry_polynomial
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    {a b : ℝ} (hab : a ≤ b) (hI : ∀ i, Icc a b ⊆ V i)
    {pref : Fin 2 → ι → ℝ} {ψ : Fin 2 → ι → Q × ℝ → ℝ}
    {v : Fin 2 → ι → Q × ℝ → Space}
    (hpref : ∀ c, PhaseJetBounds.PolynomialJets D (fun n _ => pref c n))
    (hψ : ∀ c, PhaseJetBounds.PolynomialJets (productDomain D V hV) (ψ c))
    (hv : ∀ c, PhaseJetBounds.PolynomialJets (productDomain D V hV) (v c)) (r c : Fin 2) :
    PhaseJetBounds.PolynomialJets D (fun n p => covarianceMatrix a b pref ψ v n p r c) := by
  have hr := (hv c).clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
  have ht := (hv c).clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) r.succ)
  exact (hpref c).mul (intervalIntegral_polynomial D V hV hab hI ((hψ c).pow 2 |>.mul (hr.mul ht)))

/-- A fixed smooth cutoff has the required jets, derived by compactness of
the fixed profile rather than supplied as a family of derivative bounds. -/
theorem slot_profile_polynomial (D : PhaseJetBounds.Domain ι Q)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    PhaseJetBounds.PolynomialJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo)) (fun _ z => ψ z.2) := by
  have ht : PhaseJetBounds.PolynomialJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo)) (fun _ z => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PhaseJetBounds.PolynomialJets.affine
        (D := productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
        (ContinuousLinearMap.snd ℝ Q ℝ) (fun _ => 0) (C := 1) (m := 0) le_rfl
        (fun _ z hz => by simpa only [ContinuousLinearMap.coe_snd', add_zero, pow_zero, one_mul,
          Real.norm_eq_abs, abs_of_pos hz.2.1] using hz.2.2.le))
  exact ht.compact_comp isOpen_univ hψ.contDiffOn isCompact_Icc (subset_univ _)
    (fun _ _ hz => ⟨hz.2.1.le, hz.2.2.le⟩)

end CovarianceIntegrals

section CovarianceInverse

open WeightedClasses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : StripData E}

noncomputable def normalizedMatrix (r : ℝ) (H : SmoothCovariance.Mat2) :
    SmoothCovariance.Mat2 := fun i j => r * H i j

theorem normalizedMatrix_det (r : ℝ) (H : SmoothCovariance.Mat2) :
    (normalizedMatrix r H).det = r ^ 2 * H.det := by
  simp only [Matrix.det_fin_two, normalizedMatrix]
  ring

theorem weights_eq_normalized (r : ℝ) (H : SmoothCovariance.Mat2)
    (T : SmoothCovariance.Vec2) (hr : r ≠ 0) (hH : H.det ≠ 0) (j : Fin 2) :
    SmoothCovariance.weights H T j =
      (r ^ 2 * (normalizedMatrix r H).det⁻¹) * SmoothCovariance.cramerNumerator H T j := by
  rw [SmoothCovariance.weights, normalizedMatrix_det]
  field_simp

/-- Only the normalized matrix's zeroth-order range and determinant gap are
inputs. All inverse jets follow from the actual integrated matrix entries. -/
theorem covariance_weights_class
    {r : ℕ → ℝ} {H : ℕ → E → SmoothCovariance.Mat2}
    {T : ℕ → E → SmoothCovariance.Vec2} {w : ℕ → E → ℝ}
    (hr : PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n _ => r n))
    (hrne : ∀ n, r n ≠ 0)
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n x => H n x i j))
    (hT : ∀ i, MemClass s w 0 (fun n x => T n x i))
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    (hdet : ∀ n x, x ∈ s.domain → b ≤ |(normalizedMatrix (r n) (H n x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j, |r n * H n x i j| ≤ M)
    (j : Fin 2) :
    MemClass s w 0 (fun n x => SmoothCovariance.weights (H n x) (T n x) j) := by
  have hN (i j : Fin 2) := hr.mul (hH i j)
  have hD : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n x => (normalizedMatrix (r n) (H n x)).det) := by
    simpa only [Matrix.det_fin_two, normalizedMatrix] using
      ((hN 0 0).mul (hN 1 1)).sub ((hN 0 1).mul (hN 1 0))
  have hDupper : ∀ n x, x ∈ s.domain →
      |(normalizedMatrix (r n) (H n x)).det| ≤ 2 * M ^ 2 := by
    intro n x hx
    simp only [Matrix.det_fin_two, normalizedMatrix]
    apply (abs_sub _ _).trans
    have h1 := mul_le_mul (hentry n x hx 0 0) (hentry n x hx 1 1)
      (abs_nonneg _) (zero_le_one.trans hM)
    have h2 := mul_le_mul (hentry n x hx 0 1) (hentry n x hx 1 0)
      (abs_nonneg _) (zero_le_one.trans hM)
    simp only [abs_mul] at h1 h2 ⊢
    nlinarith
  have hinv := hD.inv hb hdet hDupper
  have hscale : UnweightedClass s 0 (fun n x => r n ^ 2 *
      (normalizedMatrix (r n) (H n x)).det⁻¹) := polynomial_memClass s ((hr.pow 2).mul hinv)
  have hP (k l i : Fin 2) : MemClass s w 0 (fun n x => T n x i * H n x k l) := by
    simpa only [mul_one, zero_add] using (hT i).mul (polynomial_memClass s (hH k l))
  have hnum : MemClass s w 0 (fun n x => SmoothCovariance.cramerNumerator (H n x) (T n x) j) := by
    fin_cases j
    · have h := CurlClassBounds.class_sub (hP 1 1 0) (hP 0 1 1)
      simp only [SmoothCovariance.cramerNumerator, mul_comm] at h ⊢
      exact h
    · have h := CurlClassBounds.class_sub (hP 0 0 1) (hP 1 0 0)
      simp only [SmoothCovariance.cramerNumerator,
        mul_comm] at h ⊢
      exact h
  apply CurlClassBounds.class_congr (show MemClass s w 0
      (fun n x => (r n ^ 2 * (normalizedMatrix (r n) (H n x)).det⁻¹) *
        SmoothCovariance.cramerNumerator (H n x) (T n x) j) from
      by simpa only [one_mul, zero_add] using hscale.mul hnum)
  intro n x hx
  apply (weights_eq_normalized (r n) (H n x) (T n x) (hrne n) _ j).symm
  intro hz
  have h := hdet n x hx
  rw [normalizedMatrix_det, hz, mul_zero, abs_zero] at h
  linarith

/-- The primary square root retains the edge factor. Positivity is derived
from the positive edge weight and the order-zero lower bound. -/
theorem covariance_amplitudes_class
    {r : ℕ → ℝ} {H : ℕ → E → SmoothCovariance.Mat2}
    {T : ℕ → E → SmoothCovariance.Vec2} {w : ℕ → E → ℝ}
    (hr : PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n _ => r n))
    (hrne : ∀ n, r n ≠ 0)
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n x => H n x i j))
    (hT : ∀ i, MemClass s w 0 (fun n x => T n x i))
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ n x, x ∈ s.domain → b ≤ |(normalizedMatrix (r n) (H n x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j, |r n * H n x i j| ≤ M)
    (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      c * w n x ≤ SmoothCovariance.weights (H n x) (T n x) j)
    (j : Fin 2) :
    MemClass s (fun n x => Real.sqrt (w n x)) 0
      (fun n x => SmoothCovariance.amplitudes (H n x) (T n x) j) := by
  have hpos : ∀ n x, x ∈ s.domain →
      0 < SmoothCovariance.weights (H n x) (T n x) j :=
    fun n x hx => (mul_pos hc (hw n x hx)).trans_le (hlower n x hx j)
  exact SignedCovariance.sqrt_class hw hpos
    (covariance_weights_class hr hrne hH hT hb hM hdet hentry j)
    (SignedCovariance.inverseControl_of_lower hpos hc 0
      (fun n x hx => by simpa only [pow_zero, div_one] using hlower n x hx j))

/-- The manuscript's normalization r=√S is a frozen polynomial family. -/
theorem sqrt_slow_polynomial (s : StripData E) :
    PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n _ => Real.sqrt (s.slow n)) := by
  apply PhaseJetBounds.PolynomialJets.const _ (C := 1) (m := 1) le_rfl
  intro n
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, pow_one,
    phaseDomain]
  have hs := s.one_le_slow n
  have hsq := Real.sq_sqrt (zero_le_one.trans hs)
  nlinarith [Real.sqrt_nonneg (s.slow n)]

end CovarianceInverse

section PrimaryClass

open WeightedClasses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The stripped coefficient uses exactly the positive inverse-weight
amplitude of the physical covariance construction. -/
noncomputable def primaryCoefficient (s : StripData E)
    (H : ℕ → E → SmoothCovariance.Mat2) (T : ℕ → E → SmoothCovariance.Vec2)
    (mask : ℕ → E → ℝ) (v : ℕ → E → Space) (j : Fin 2) :
    ℕ → E → HarmonicCalculus.ComplexVector := fun n x =>
  PartitionedCovariance.amplitude (s.epsilon n) (mask n x) (H n x) (T n x) j •
    CurlClassBounds.complexify (v n x)

/-- All stripped jets of the constructed amplitude retain √ζ P. The
half-power comes from the actual √ε factor, not a bound assumed on it. -/
theorem primaryCoefficient_waveClass
    {s : StripData E} {P : ℕ → E → ℝ}
    {H : ℕ → E → SmoothCovariance.Mat2} {T : ℕ → E → SmoothCovariance.Vec2}
    {mask : ℕ → E → ℝ} {v : ℕ → E → Space}
    (hH : ∀ i j, PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n x => H n x i j))
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hmask : PhaseJetBounds.PolynomialJets (phaseDomain s) mask)
    (hv : MemClass s P 0 v)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n)) (H n x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * H n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      c * s.zeta x ≤ SmoothCovariance.weights (H n x) (T n x) j)
    (j : Fin 2) : WaveClass s P (1 / 2) (primaryCoefficient s H T mask v j) := by
  have ha := covariance_amplitudes_class (sqrt_slow_polynomial s)
    (fun n => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (s.one_le_slow n))).ne')
    hH hT hb hM hc hdet hentry (fun _ x hx => hζ x hx) hlower j
  have ham : WaveClass s P 0 (fun n x =>
      SmoothCovariance.amplitudes (H n x) (T n x) j • CurlClassBounds.complexify (v n x)) := by
    simpa only [zero_add] using ha.smul (hv.map CurlClassBounds.complexify)
  have hm : WaveClass s P 0 (fun n x => mask n x •
      (SmoothCovariance.amplitudes (H n x) (T n x) j • CurlClassBounds.complexify (v n x))) := by
    simpa only [zero_add] using CurlClassBounds.class_mul_real (polynomial_memClass s hmask) ham
  have hε : BandBound s (1 / 2) (fun n => Real.sqrt (s.epsilon n)) := by
    simpa only [Real.sqrt_eq_rpow] using bandBound_rpow s (1 / 2)
  apply CurlClassBounds.class_congr (show WaveClass s P (1 / 2)
      (fun n x => Real.sqrt (s.epsilon n) • (mask n x •
        (SmoothCovariance.amplitudes (H n x) (T n x) j • CurlClassBounds.complexify (v n x)))) from
      by simpa only [zero_add] using hm.band_smul hε)
  intro n x hx
  simp only [primaryCoefficient, PartitionedCovariance.amplitude, smul_smul]
  congr 1
  ring

/-- The actual normal-cross-product curl correction with the rounded
carrier and any nonzero integer harmonic. -/
noncomputable def primaryCurlRemainder (s : StripData E)
    (N : ℕ → E → Space) (R : E → ℝ) (Vr Vθ Vz : ℕ → E → E)
    (harmonic : ℕ → ℤ) (a : ℕ → E → HarmonicCalculus.ComplexVector) :
    ℕ → E → HarmonicCalculus.ComplexVector := fun n =>
  CurlClassBounds.curlRemainder
    (CurlClassBounds.carrierFrequency s n * (harmonic n : ℝ)) R (Vr n) (Vθ n) (Vz n)
    (fun x => CurlClassBounds.normalCoefficient (N n x) (a n x))

theorem primaryCurlRemainder_waveClass
    {s : StripData E} {P : ℕ → E → ℝ} {κ : ℝ}
    {N : ℕ → E → Space} {R : E → ℝ} {Vr Vθ Vz : ℕ → E → E}
    {harmonic : ℕ → ℤ} {a : ℕ → E → HarmonicCalculus.ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N)
    (ha : WaveClass s P (1 / 2) a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hharmonic : ∀ n, harmonic n ≠ 0) :
    WaveClass s P (1 - κ) (primaryCurlRemainder s N R Vr Vθ Vz harmonic a) := by
  have h := CurlClassBounds.normalCurlRemainder_class hN ha hb hlower hupper hκ hr hθ hz hR
    (CurlClassBounds.harmonic_inverse_bandBound s harmonic hharmonic)
  simp only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num] at h
  exact h

/-- In particular the exact-curl change meets the cumulative 0.68 budget. -/
theorem primaryCurlRemainder_budget
    {s : StripData E} {P : ℕ → E → ℝ} {κ : ℝ}
    {N : ℕ → E → Space} {R : E → ℝ} {Vr Vθ Vz : ℕ → E → E}
    {harmonic : ℕ → ℤ} {a : ℕ → E → HarmonicCalculus.ComplexVector}
    (h : WaveClass s P (1 - κ) (primaryCurlRemainder s N R Vr Vθ Vz harmonic a))
    (hκ : κ ≤ 8 / 25) :
    WaveClass s P (17 / 25) (primaryCurlRemainder s N R Vr Vθ Vz harmonic a) :=
  h.mono_exponent (by linarith)

end PrimaryClass

section EnvelopeAlgebra

variable {ι : Type*} {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {D : PhaseJetBounds.Domain ι E} {w : ι → E → ℝ}

theorem EnvelopeJets.congr {f g : ι → E → F} (hf : EnvelopeJets D w f)
    (hfg : ∀ i, EqOn (f i) (g i) (D.carrier i)) : EnvelopeJets D w g := by
  refine ⟨hf.nonneg, fun i => (hf.smooth i).congr (fun x hx => (hfg i hx).symm), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i x hx j hj
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) (hfg i) hx j
  rw [iteratedFDerivWithin_of_isOpen j (D.isOpen i) hx,
    iteratedFDerivWithin_of_isOpen j (D.isOpen i) hx] at he
  rw [← he]
  exact hm i x hx j hj

theorem EnvelopeJets.map {f : ι → E → F} (hf : EnvelopeJets D w f)
    (L : F →L[ℝ] G) : EnvelopeJets D w (fun i x => L (f i x)) := by
  refine ⟨hf.nonneg, fun i => L.contDiff.comp_contDiffOn (hf.smooth i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨(‖L‖ + 1) * C, by nlinarith [norm_nonneg L], m, ?_⟩
  intro i x hx j hj
  change ‖iteratedFDeriv ℝ j (L ∘ f i) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left ((hf.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx))
    (nat_le_infty j)]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * (C * D.scale i ^ m * w i x) :=
      mul_le_mul_of_nonneg_left (hm i x hx j hj) (norm_nonneg L)
    _ ≤ _ := by
      have hs := pow_nonneg (zero_le_one.trans (D.one_le_scale i)) m
      have hw := hf.nonneg i x hx
      have hcw : 0 ≤ C * D.scale i ^ m * w i x := by positivity
      nlinarith [mul_nonneg (show 0 ≤ C by linarith) (mul_nonneg hs hw)]

theorem EnvelopeJets.add {f g : ι → E → F}
    (hf : EnvelopeJets D w f) (hg : EnvelopeJets D w g) :
    EnvelopeJets D w (fun i x => f i x + g i x) := by
  refine ⟨hf.nonneg, fun i => (hf.smooth i).add (hg.smooth i), ?_⟩
  intro N
  obtain ⟨A, hA, m, hm⟩ := hf.bound N
  obtain ⟨B, hB, k, hk⟩ := hg.bound N
  refine ⟨A + B, by linarith, m + k, ?_⟩
  intro i x hx j hj
  rw [fun_iteratedFDeriv_add_apply
    (((hf.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)).of_le (nat_le_infty j))
    (((hg.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)).of_le (nat_le_infty j))]
  have hsm := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_right m k)
  have hsk := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_left k m)
  have hw := hf.nonneg i x hx
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i) x‖ + ‖iteratedFDeriv ℝ j (g i) x‖ := norm_add_le _ _
    _ ≤ A * D.scale i ^ m * w i x + B * D.scale i ^ k * w i x :=
      add_le_add (hm i x hx j hj) (hk i x hx j hj)
    _ ≤ A * D.scale i ^ (m + k) * w i x + B * D.scale i ^ (m + k) * w i x :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsm (zero_le_one.trans hA)) hw)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsk (zero_le_one.trans hB)) hw)
    _ = _ := by ring

/-- Multiplying by an actual polynomial-jet geometric factor preserves the
full envelope, including weights which can become arbitrarily small. -/
theorem EnvelopeJets.smul_polynomial {a : ι → E → ℝ} {f : ι → E → F}
    (ha : EnvelopeJets D w a) (hf : PhaseJetBounds.PolynomialJets D f) :
    EnvelopeJets D w (fun i x => a i x • f i x) := by
  refine ⟨ha.nonneg, fun i => (ha.smooth i).smul (hf.smooth i), ?_⟩
  intro N
  obtain ⟨A, hA, m, hm⟩ := ha.bound N
  obtain ⟨B, hB, k, hk⟩ := hf.bound N
  refine ⟨(2 : ℝ) ^ N * A * B, ?_, m + k, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA) hB
  intro i x hx j hj
  have hs : 0 ≤ D.scale i := zero_le_one.trans (D.one_le_scale i)
  have hw := ha.nonneg i x hx
  calc
    _ ≤ (2 : ℝ) ^ N * (A * D.scale i ^ m * w i x) * (B * D.scale i ^ k) :=
      smul_jet_bound (A := a i) (B := f i) (D.isOpen i) (ha.smooth i) (hf.smooth i) hx hj
        (by positivity) (by positivity) (hm i x hx) (fun l hl => hk i l hl x hx)
    _ = _ := by rw [pow_add]; ring

end EnvelopeAlgebra

section ActualAmbient

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem ambient_envelope_jets {D : PhaseJetBounds.Domain ι (Q × ℝ)}
    {d : ι → PrimaryODE.FrameData Q} {w : ι → Q × ℝ → ℝ} {z : ι → Q × ℝ → State}
    (hz : EnvelopeJets D w z)
    (hc : ∀ j, PhaseJetBounds.PolynomialJets D (fun n => synthesisColumn (d n) j)) :
    EnvelopeJets D w (fun n x => (d n).ambient x (z n x)) := by
  have h0 := (hz.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).smul_polynomial (hc 0)
  have h1 := (hz.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)).smul_polynomial (hc 1)
  apply (h0.add h1).congr
  intro i x hx
  exact (ambient_eq_synthesis _ _ _).symm

noncomputable def normalizedPulse (d : PrimaryODE.FrameData Q) (lam u L : ℝ)
    (z : Q × ℝ) : Space :=
  d.ambient (z.1, L * z.2) (fundamental d lam u L (z.1, L * z.2))

theorem normalizedPulse_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (d : ι → PrimaryODE.FrameData Q)
    (hd : PhaseJetBounds.FrameJets (productDomain D V hV) d)
    (lam u L : ι → ℝ) (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    (hf : EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) z.2)
      (fun i => fundamental (d i) (lam i) (u i) (L i)))
    {M : ℝ} (hM : 1 ≤ M) (hslot : ∀ i, L i ≤ M * D.scale i) :
    EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) (L i * z.2))
      (fun i => normalizedPulse (d i) (lam i) (u i) (L i)) := by
  have hc (j : Fin 2) : PhaseJetBounds.PolynomialJets
      (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i => synthesisColumn (d i) j) := by
    apply ((EnvelopeJets.of_polynomial (synthesisColumn_polynomial hd j)).restrict
      (D' := productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun _ => rfl) (fun i z hz => ⟨hz.1, hI i ⟨hz.2.1.le, hz.2.2.le⟩⟩)).to_polynomial
    intro i z hz
    rfl
  exact (ambient_envelope_jets hf hc).normalize_slot D L hL hM hslot

theorem normalizedPulse_polynomial
    (D : PhaseJetBounds.Domain ι Q) (lam u L : ι → ℝ)
    (d : ι → PrimaryODE.FrameData Q)
    (h : EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) (L i * z.2))
      (fun i => normalizedPulse (d i) (lam i) (u i) (L i)))
    (hlam : ∀ i, 0 < lam i) (hu : ∀ i, 0 < u i) (hL : ∀ i, 0 < L i) :
    PhaseJetBounds.PolynomialJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i => normalizedPulse (d i) (lam i) (u i) (L i)) := by
  apply h.to_polynomial
  intro i z hz
  apply referenceP_le_one (hlam i) (hu i) (hL i)
  constructor
  · exact mul_nonneg (hL i).le hz.2.1.le
  · nlinarith [hL i, hz.2.2]

end ActualAmbient

section ActualCovariance

open MeasureTheory

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The covariance matrix is made from the two constructed ambient pulses,
with the fixed smooth middle cutoff. -/
noncomputable def primaryCovariance (pref : Fin 2 → ι → ℝ)
    (d : Fin 2 → ι → PrimaryODE.FrameData Q) (lam u L : Fin 2 → ι → ℝ) :
    ι → Q → SmoothCovariance.Mat2 :=
  covarianceMatrix (1 / 10) (9 / 10) pref
    (fun _ _ z => GaussianTailFlat.profile z.2)
    (fun c n => normalizedPulse (d c n) (lam c n) (u c n) (L c n))

theorem primaryCovariance_entry_polynomial
    (D : PhaseJetBounds.Domain ι Q)
    (pref : Fin 2 → ι → ℝ) (d : Fin 2 → ι → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ι → ℝ)
    (hpref : ∀ c, PhaseJetBounds.PolynomialJets D (fun n _ => pref c n))
    (hpulse : ∀ c, EnvelopeJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam c i) (u c i) (L c i) (L c i * z.2))
      (fun i => normalizedPulse (d c i) (lam c i) (u c i) (L c i)))
    (hlam : ∀ c i, 0 < lam c i) (hu : ∀ c i, 0 < u c i) (hL : ∀ c i, 0 < L c i)
    (r c : Fin 2) :
    PhaseJetBounds.PolynomialJets D (fun n p => primaryCovariance pref d lam u L n p r c) := by
  exact covarianceMatrix_entry_polynomial D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo)
    (by norm_num) (fun _ t ht => by constructor <;> linarith [ht.1, ht.2])
    hpref (fun _ => slot_profile_polynomial D _ GaussianTailFlat.profile_contDiff)
    (fun c => normalizedPulse_polynomial D (lam c) (u c) (L c) (d c) (hpulse c)
      (hlam c) (hu c) (hL c)) r c

theorem profile_support_covariance_interval :
    support GaussianTailFlat.profile ⊆ Ioc (1 / 10 : ℝ) (9 / 10) := by
  intro t ht
  have hd : |t - 1 / 2| < 1 / 3 := by
    by_contra hn
    exact ht (GaussianTailFlat.profile_zero (le_of_not_gt hn))
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hd
  constructor <;> linarith

/-- Exact change of variables from the physical slot to the fixed middle
interval. The integrand identity can be checked only where the cutoff is
nonzero; no global equality of clamped ODE extensions is required. -/
theorem actualColumn_normalization
    {a b L : ℝ} (hL : 0 < L) (ci : ℝ) (ψ x : ℝ → ℝ)
    (t : ℝ → SmoothCovariance.Vec2) (χ : ℝ → ℝ) (v : ℝ → Space)
    (hχ : support χ ⊆ Ioc a b) (r : Fin 2)
    (hmatch : ∀ s, ψ s ^ 2 * x s * t s r =
      χ (s / L) ^ 2 * (v (s / L) 0 * v (s / L) r.succ)) :
    PulseCovariance.actualColumn ci ψ x t r =
      ci * L * ∫ s in a..b, χ s ^ 2 * (v s 0 * v s r.succ) := by
  let g := fun s => χ s ^ 2 * (v s 0 * v s r.succ)
  have hsupp : support g ⊆ Ioc a b := by
    intro s hs
    apply hχ
    intro hz
    apply hs
    simp [g, hz]
  unfold PulseCovariance.actualColumn
  calc
    _ = ci * ∫ s : ℝ, g (s / L) := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hmatch)
    _ = ci * (L * ∫ s : ℝ, g s) := by
      rw [Measure.integral_comp_div, abs_of_pos hL, smul_eq_mul]
    _ = _ := by
      rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
      dsimp [g]
      ring

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- The matrix estimated above is the literal matrix of native pulse
covariances when the two original pulse integrands are identified. -/
theorem primaryCovariance_eq_pairMatrix
    (pref : Fin 2 → ι → ℝ) (d : Fin 2 → ι → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ι → ℝ) (n : ι) (p : Q)
    (vr vt : TorusInverse.Plane) (radius : ℝ) (ci : SmoothCovariance.Vec2)
    (pulses : Fin 2 → PartitionedCovariance.Pulse)
    (hL : ∀ c, 0 < L c n)
    (hpref : ∀ c, pref c n = PartitionedCovariance.nativePrefactor vr vt radius * ci c * L c n)
    (hmatch : ∀ c r s, (pulses c).ψ s ^ 2 * (pulses c).x s * (pulses c).t s r =
      GaussianTailFlat.profile (s / L c n) ^ 2 *
        (normalizedPulse (d c n) (lam c n) (u c n) (L c n) (p, s / L c n) 0 *
          normalizedPulse (d c n) (lam c n) (u c n) (L c n) (p, s / L c n) r.succ)) :
    primaryCovariance pref d lam u L n p = PartitionedCovariance.pairMatrix vr vt radius ci pulses
      := by
  ext r c
  rw [PartitionedCovariance.pairMatrix, PartitionedCovariance.Pulse.column,
    actualColumn_normalization (hL c) (ci c) (pulses c).ψ (pulses c).x (pulses c).t
      GaussianTailFlat.profile
      (fun s => normalizedPulse (d c n) (lam c n) (u c n) (L c n) (p, s))
      profile_support_covariance_interval r (hmatch c r)]
  simp only [primaryCovariance, covarianceMatrix, hpref]
  ring

end ActualCovariance

section Localization

open Filter

variable {ι : Type*} {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem EnvelopeJets.polynomial_smul {D : PhaseJetBounds.Domain ι E}
    {w : ι → E → ℝ} {a : ι → E → ℝ} {f : ι → E → F}
    (hf : EnvelopeJets D w f) (ha : PhaseJetBounds.PolynomialJets D a) :
    EnvelopeJets D w (fun i x => a i x • f i x) := by
  refine ⟨hf.nonneg, fun i => (ha.smooth i).smul (hf.smooth i), ?_⟩
  intro N
  obtain ⟨A, hA, m, hm⟩ := ha.bound N
  obtain ⟨B, hB, k, hk⟩ := hf.bound N
  refine ⟨(2 : ℝ) ^ N * A * B, ?_, m + k, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA) hB
  intro i x hx j hj
  have hs : 0 ≤ D.scale i := zero_le_one.trans (D.one_le_scale i)
  have hw := hf.nonneg i x hx
  calc
    _ ≤ (2 : ℝ) ^ N * (A * D.scale i ^ m) * (B * D.scale i ^ k * w i x) :=
      smul_jet_bound (A := a i) (B := f i) (D.isOpen i) (ha.smooth i) (hf.smooth i) hx hj
        (by positivity) (by positivity) (fun l hl => hm i l hl x hx) (hk i x hx)
    _ = _ := by rw [pow_add]; ring

theorem EnvelopeJets.mono_weight {D : PhaseJetBounds.Domain ι E}
    {w v : ι → E → ℝ} {f : ι → E → F} (hf : EnvelopeJets D w f)
    (hvw : ∀ i x, x ∈ D.carrier i → w i x ≤ v i x) : EnvelopeJets D v f := by
  refine ⟨fun i x hx => (hf.nonneg i x hx).trans (hvw i x hx), hf.smooth, ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i x hx j hj
  exact (hm i x hx j hj).trans (mul_le_mul_of_nonneg_left (hvw i x hx)
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans (D.one_le_scale i)) m)))

private theorem jet_eq_of_eventuallyEq {f g : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] g) (j : ℕ) : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
  have h' : f =ᶠ[𝓝[univ] x] g := by simpa using h
  simpa only [iteratedFDerivWithin_univ] using h'.iteratedFDerivWithin_eq h.eq_of_nhds j

/-- A compactly contained cutoff extends the actual slot solution with all
jets. No smoothness of the uncut solution outside the slot is used. -/
theorem EnvelopeJets.localize {D D' : PhaseJetBounds.Domain ι E}
    {w : ι → E → ℝ} {f : ι → E → F} {a : ι → E → ℝ}
    (hf : EnvelopeJets D w f) (ha : PhaseJetBounds.PolynomialJets D' a)
    (hscale : ∀ i, D.scale i = D'.scale i) (hsub : ∀ i, D.carrier i ⊆ D'.carrier i)
    (hw : ∀ i x, x ∈ D'.carrier i → 0 ≤ w i x)
    (hsupport : ∀ i, tsupport (a i) ∩ D'.carrier i ⊆ D.carrier i) :
    EnvelopeJets D' w (fun i x => a i x • f i x) := by
  have hasmall : PhaseJetBounds.PolynomialJets D a := by
    apply ((EnvelopeJets.of_polynomial ha).restrict (D' := D)
      (fun i => (hscale i).symm) hsub).to_polynomial
    intro i x hx
    rfl
  have hp := hf.polynomial_smul hasmall
  have hout (i) (x) (hx : x ∈ D'.carrier i) (hn : x ∉ D.carrier i) :
      (fun y => a i y • f i y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
    have hn' : x ∉ tsupport (a i) := fun h => hn (hsupport i ⟨h, hx⟩)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn'] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]
  refine ⟨hw, ?_, ?_⟩
  · intro i x hx
    by_cases hn : x ∈ D.carrier i
    · exact ((hp.smooth i).contDiffAt ((D.isOpen i).mem_nhds hn)).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hout i x hx hn)).contDiffWithinAt
  · intro N
    obtain ⟨C, hC, m, hm⟩ := hp.bound N
    refine ⟨C, hC, m, ?_⟩
    intro i x hx j hj
    by_cases hn : x ∈ D.carrier i
    · simpa only [hscale i] using hm i x hn j hj
    · rw [jet_eq_of_eventuallyEq (hout i x hx hn) j]
      have hz : ‖iteratedFDeriv ℝ j (fun _ : E => (0 : F)) x‖ = 0 := by
        cases j with
        | zero => simp only [norm_iteratedFDeriv_zero, norm_zero]
        | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      rw [hz]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans (D'.one_le_scale i)) m)) (hw i x hx)

/-- All profile jets are obtained from the constructed compact smooth bump. -/
theorem profile_linear_polynomial (D : PhaseJetBounds.Domain ι E) (L : E →L[ℝ] ℝ) :
    PhaseJetBounds.PolynomialJets D (fun _ x => GaussianTailFlat.profile (L x)) := by
  let R : PhaseJetBounds.Domain ι ℝ := {
    scale := D.scale
    carrier := fun _ => univ
    isOpen := fun _ => isOpen_univ
    one_le_scale := D.one_le_scale }
  have hp : PhaseJetBounds.PolynomialJets R (fun _ => GaussianTailFlat.profile) := by
    refine ⟨fun _ => GaussianTailFlat.profile_contDiff.contDiffOn, ?_⟩
    intro N
    obtain ⟨C, hC, hc⟩ := GaussianTailFlat.finite_jet_bounds GaussianTailFlat.profile_jet_bounded N
    refine ⟨C + 1, by linarith, 0, ?_⟩
    intro i j hj x hx
    simpa only [pow_zero, mul_one] using (hc j hj x).trans (le_add_of_nonneg_right zero_le_one)
  simpa only [add_zero] using hp.precomp_affine (D := D) L (fun _ => 0) (fun _ => rfl)
    (fun _ _ _ => mem_univ _)

end Localization

section CutoffPulse

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

noncomputable def cutoffPulse (d : PrimaryODE.FrameData Q) (lam u L : ℝ)
    (z : Q × ℝ) : Space :=
  GaussianTailFlat.profile z.2 • normalizedPulse d lam u L z

omit [NormedSpace ℝ Q] in
theorem profile_tsupport_slot :
    tsupport (fun z : Q × ℝ => GaussianTailFlat.profile z.2) ⊆
      {z : Q × ℝ | z.2 ∈ Ioo (0 : ℝ) 1} := by
  have hcl : tsupport (fun z : Q × ℝ => GaussianTailFlat.profile z.2) ⊆
      {z : Q × ℝ | z.2 ∈ Icc (1 / 10 : ℝ) (9 / 10)} := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_snd)
    intro z hz
    exact ⟨(profile_support_covariance_interval hz).1.le,
      (profile_support_covariance_interval hz).2⟩
  intro z hz
  obtain ⟨hl, hr⟩ := hcl hz
  constructor <;> linarith

/-- The actual cutoff pulse has global slot-coordinate jets with the
zero-extended Gaussian envelope. This is the form used in physical charts. -/
theorem cutoffPulse_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (d : ι → PrimaryODE.FrameData Q) (lam u L : ι → ℝ)
    (hp : EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) (L i * z.2))
      (fun i => normalizedPulse (d i) (lam i) (u i) (L i))) :
    EnvelopeJets (productDomain D (fun _ => (univ : Set ℝ)) (fun _ => isOpen_univ))
      (fun i z => GaussianTailFlat.referenceSlotEnvelope (lam i) (u i) (L i) z.2)
      (fun i => cutoffPulse (d i) (lam i) (u i) (L i)) := by
  have hweight : ∀ i (z : Q × ℝ),
      0 ≤ GaussianTailFlat.referenceSlotEnvelope (lam i) (u i) (L i) z.2 := by
    intro i z
    unfold GaussianTailFlat.referenceSlotEnvelope
    split_ifs
    · exact (GaussianEnvelope.envelope_pos _ _ _).le
    · rfl
  have hp' := hp.mono_weight (v := fun i z =>
      GaussianTailFlat.referenceSlotEnvelope (lam i) (u i) (L i) z.2) (by
    intro i z hz
    rw [GaussianTailFlat.referenceSlotEnvelope, ite_eq_left ⟨hz.2.1.le, hz.2.2.le⟩]
    rfl)
  apply hp'.localize
    (profile_linear_polynomial
      (productDomain D (fun _ => (univ : Set ℝ)) (fun _ => isOpen_univ))
      (ContinuousLinearMap.snd ℝ Q ℝ)) (fun _ => rfl)
      (fun _ z hz => ⟨hz.1, mem_univ _⟩) (fun i z _ => hweight i z)
  intro i z hz
  exact ⟨hz.2.1, profile_tsupport_slot hz.1⟩

end CutoffPulse

section PhaseInstantiation

open PhaseJetBounds

variable {ι : Type*}

/-- The actual PhaseCalculus normal and reconstructed frame supply the ODE
coefficient jets. Only normalized base-field jets and previously quantified
zeroth-order geometric/viscous errors are inputs. Rounding and all fixed
representative choices stay constant within each label. -/
theorem phase_normalizedPulse_envelope_jets
    (a : PhaseFamily ι) (D : Domain ι Slow) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (lam c0 u L ν B : ι → ℝ) (K : ι → Plane) (s δ : ι → Slow × ℝ → ℝ)
    (hF : PolynomialJets D a.F) (hG : PolynomialJets D a.G)
    {r b M : ℝ} (hr : 0 < r) (hb : 0 < b) (hM : 1 ≤ M)
    (hconstant : ∀ i, |a.epsilon i| ≤ M ∧ |a.p i| ≤ M ∧ |a.pz i| ≤ M ∧ |a.x0 i| ≤ M)
    (heps : ∀ i, a.epsilon i ≠ 0)
    (hR : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M)
    (hslot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i)
    (hlam : ∀ i, |lam i| ≤ M) (hc : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M)
    (hu : ∀ i, |u i| ≤ M) (hrate : ∀ i, |u i / L i| * D.scale i ≤ M)
    (hν : ∀ i, |ν i| ≤ M)
    (hB : ∀ i, 2 * b ≤ B i ∧ B i ≤ M) (hK : ∀ i, ‖K i‖ = 1)
    (hs : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, |s i z| ≤ M)
    (hδ : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, δ i z ≤ B i / 2)
    (hclose : ∀ i, ∀ z ∈ (D.slot V hV).carrier i,
      ‖a.normal i z - MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ δ i z)
    (hlampos : ∀ i, 0 < lam i) (hupos : ∀ i, 0 < u i) (hL : ∀ i, 0 < L i)
    (hI : ∀ i, Icc 0 (L i) ⊆ V i) (hνpos : ∀ i, 0 ≤ ν i)
    {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hvisc : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      ViscousPropagator.referenceViscosity (lam i) (u i) (L i) v - E / D.scale i ≤
        (a.frameData lam c0 u L ν i).viscosity (p, v))
    (herr : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      |(a.frameData lam c0 u L ν i).error11 (p, v)| ≤ C / D.scale i ∧
      |(a.frameData lam c0 u L ν i).error12 (p, v)| ≤ C / D.scale i ∧
      |(a.frameData lam c0 u L ν i).error21 (p, v)| ≤ C / D.scale i ∧
      |(a.frameData lam c0 u L ν i).error22 (p, v)| ≤ C / D.scale i) :
    EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (lam i) (u i) (L i) (L i * z.2))
      (fun i => normalizedPulse (a.frameData lam c0 u L ν i) (lam i) (u i) (L i)) := by
  have hd := a.frameData_jets_of_phase_comparison D V hV lam c0 u L ν B K s δ hF hG
    hr hb hM hconstant heps hR hslot hlam hc hu hrate hν hB hK hs hδ hclose
  have hlen (i) : L i ≤ M * D.scale i := by
    simpa only [abs_of_pos (hL i)] using hslot i (L i) (hI i ⟨(hL i).le, le_rfl⟩)
  have hνactual : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      0 ≤ (a.frameData lam c0 u L ν i).viscosity (p, v) := by
    intro i p hp v hv
    change 0 ≤ ν i * ‖a.normal i (p, v)‖ ^ 2
    exact mul_nonneg (hνpos i) (sq_nonneg _)
  have hf := fundamental_envelope_jets D V hV (a.frameData lam c0 u L ν) hd lam u L
    hlampos hupos hL hI hM hC hE hlen (fun _ _ _ _ _ => rfl) hνactual hvisc herr
  exact normalizedPulse_envelope_jets D V hV (a.frameData lam c0 u L ν) hd lam u L hL hI
    hf hM hlen

end PhaseInstantiation

section ChartAssembly

open WeightedClasses

variable {Q E : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def chartCovariance
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ) :
    ℕ → E → SmoothCovariance.Mat2 := fun n x => primaryCovariance pref d lam u L n (χ n x).1

noncomputable def primaryWave (s : StripData E)
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ) (c : Fin 2) :
    ℕ → E → HarmonicCalculus.ComplexVector :=
  primaryCoefficient s (chartCovariance pref d lam u L χ) T mask
    (fun n x => cutoffPulse (d c n) (lam c n) (u c n) (L c n) (χ n x)) c

/-- Assembly with the actual phase-frame pulse, the actual integrated
covariance matrix, the fixed slot cutoff, and a chart of polynomial scale.
The remaining matrix hypotheses are strictly order zero. -/
theorem primaryWave_waveClass
    (s : StripData E) (D : PhaseJetBounds.Domain ℕ Q)
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ)
    (hscale : ∀ n, D.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ D.carrier n)
    (hpref : ∀ c, PhaseJetBounds.PolynomialJets D (fun n _ => pref c n))
    (hpulse : ∀ c, EnvelopeJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun n z => referenceP (lam c n) (u c n) (L c n) (L c n * z.2))
      (fun n => normalizedPulse (d c n) (lam c n) (u c n) (L c n)))
    (hlam : ∀ c n, 0 < lam c n) (hu : ∀ c n, 0 < u c n) (hL : ∀ c n, 0 < L c n)
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hmask : PhaseJetBounds.PolynomialJets (phaseDomain s) mask)
    {b M a : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (ha : 0 < a)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n)) (chartCovariance pref d lam u L χ n x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * chartCovariance pref d lam u L χ n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      a * s.zeta x ≤ SmoothCovariance.weights (chartCovariance pref d lam u L χ n x) (T n x) j)
    (c : Fin 2) :
    WaveClass s (fun n x => GaussianTailFlat.referenceSlotEnvelope
      (lam c n) (u c n) (L c n) (χ n x).2) (1 / 2)
      (primaryWave s pref d lam u L χ T mask c) := by
  have hH (i j : Fin 2) : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n x => chartCovariance pref d lam u L χ n x i j) := by
    apply ((EnvelopeJets.of_polynomial
      (primaryCovariance_entry_polynomial D pref d lam u L hpref hpulse hlam hu hL i j)).comp
      (hχ.clm (ContinuousLinearMap.fst ℝ Q ℝ)) hscale hmap).to_polynomial
    intro n x hx
    rfl
  have hp := cutoffPulse_envelope_jets D (d c) (lam c) (u c) (L c) (hpulse c)
  have hpc := hp.comp hχ hscale (fun n x hx => ⟨hmap n x hx, mem_univ _⟩)
  have hv := hpc.memClass s (fun _ => rfl) (fun _ => rfl)
  exact primaryCoefficient_waveClass hH hT hmask hv hb hM ha hdet hentry hζ hlower c

end ChartAssembly

section PhaseConstruction

open PhaseJetBounds WeightedClasses

variable {ι : Type*}

/-- Explicit input data for one sign of the phase construction. There are
no solution, propagator, covariance, or output-jet assumptions in this
record. The error fields are the order-zero moving-frame estimates. -/
structure PhaseConstruction (D : Domain ι Slow) where
  phase : PhaseFamily ι
  V : ι → Set ℝ
  openV : ∀ i, IsOpen (V i)
  lam : ι → ℝ
  c0 : ι → ℝ
  u : ι → ℝ
  L : ι → ℝ
  viscosity : ι → ℝ
  B : ι → ℝ
  K : ι → Plane
  slope : ι → Slow × ℝ → ℝ
  error : ι → Slow × ℝ → ℝ
  r : ℝ
  b : ℝ
  M : ℝ
  C : ℝ
  E : ℝ
  r_pos : 0 < r
  b_pos : 0 < b
  one_le_M : 1 ≤ M
  C_nonneg : 0 ≤ C
  E_nonneg : 0 ≤ E
  baseF : PolynomialJets D phase.F
  baseG : PolynomialJets D phase.G
  constants : ∀ i, |phase.epsilon i| ≤ M ∧ |phase.p i| ≤ M ∧
    |phase.pz i| ≤ M ∧ |phase.x0 i| ≤ M
  epsilon_ne : ∀ i, phase.epsilon i ≠ 0
  radius : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M
  slot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i
  lam_bound : ∀ i, |lam i| ≤ M
  c0_bound : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M
  u_bound : ∀ i, |u i| ≤ M
  rate_bound : ∀ i, |u i / L i| * D.scale i ≤ M
  viscosity_bound : ∀ i, |viscosity i| ≤ M
  B_bound : ∀ i, 2 * b ≤ B i ∧ B i ≤ M
  K_unit : ∀ i, ‖K i‖ = 1
  slope_bound : ∀ i, ∀ z ∈ (D.slot V openV).carrier i, |slope i z| ≤ M
  error_small : ∀ i, ∀ z ∈ (D.slot V openV).carrier i, error i z ≤ B i / 2
  normal_close : ∀ i, ∀ z ∈ (D.slot V openV).carrier i,
    ‖phase.normal i z - MovingFrameODE.pack (B i * slope i z) (B i • K i)‖ ≤ error i z
  lam_pos : ∀ i, 0 < lam i
  u_pos : ∀ i, 0 < u i
  L_pos : ∀ i, 0 < L i
  interval : ∀ i, Icc 0 (L i) ⊆ V i
  viscosity_nonneg : ∀ i, 0 ≤ viscosity i
  damping_error : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
    ViscousPropagator.referenceViscosity (lam i) (u i) (L i) v - E / D.scale i ≤
      (phase.frameData lam c0 u L viscosity i).viscosity (p, v)
  modal_errors : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
    |(phase.frameData lam c0 u L viscosity i).error11 (p, v)| ≤ C / D.scale i ∧
    |(phase.frameData lam c0 u L viscosity i).error12 (p, v)| ≤ C / D.scale i ∧
    |(phase.frameData lam c0 u L viscosity i).error21 (p, v)| ≤ C / D.scale i ∧
    |(phase.frameData lam c0 u L viscosity i).error22 (p, v)| ≤ C / D.scale i

noncomputable def PhaseConstruction.frame {D : Domain ι Slow} (p : PhaseConstruction D) :
    ι → PrimaryODE.FrameData Slow := p.phase.frameData p.lam p.c0 p.u p.L p.viscosity

theorem PhaseConstruction.pulse_jets {D : Domain ι Slow} (p : PhaseConstruction D) :
    EnvelopeJets (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun i z => referenceP (p.lam i) (p.u i) (p.L i) (p.L i * z.2))
      (fun i => normalizedPulse (p.frame i) (p.lam i) (p.u i) (p.L i)) :=
  phase_normalizedPulse_envelope_jets p.phase D p.V p.openV p.lam p.c0 p.u p.L p.viscosity
    p.B p.K p.slope p.error p.baseF p.baseG p.r_pos p.b_pos p.one_le_M p.constants
    p.epsilon_ne p.radius p.slot p.lam_bound p.c0_bound p.u_bound p.rate_bound
    p.viscosity_bound p.B_bound p.K_unit p.slope_bound p.error_small p.normal_close
    p.lam_pos p.u_pos p.L_pos p.interval p.viscosity_nonneg p.C_nonneg p.E_nonneg
    p.damping_error p.modal_errors

theorem PhaseConstruction.normal_jets {D : Domain ι Slow} (p : PhaseConstruction D) :
    PolynomialJets (D.slot p.V p.openV) p.phase.normal :=
  (p.phase.polynomial_jets D p.V p.openV p.baseF p.baseG p.r_pos p.one_le_M p.constants
    p.epsilon_ne p.radius p.slot).1

theorem PhaseConstruction.normal_range {D : Domain ι Slow} (p : PhaseConstruction D) :
    (∀ i, ∀ z ∈ (D.slot p.V p.openV).carrier i, p.b ≤ ‖p.phase.normal i z‖) ∧
    (∀ i, ∀ z ∈ (D.slot p.V p.openV).carrier i, ‖p.phase.normal i z‖ ≤ p.M ^ 2 + 3 * p.M) := by
  have h := normal_range_of_reference_close p.B p.K p.slope p.error p.b_pos p.one_le_M
    p.B_bound p.K_unit p.slope_bound p.error_small p.normal_close
  exact ⟨fun i z hz => (h.1 i z hz).trans (PhaseEstimates.tail_norm_le _), h.2⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def phaseCovariance {D : Domain ℕ Slow} (F : Fin 2 → PhaseConstruction D)
    (pref : Fin 2 → ℕ → ℝ) : ℕ → Slow → SmoothCovariance.Mat2 :=
  primaryCovariance pref (fun c => (F c).frame) (fun c => (F c).lam)
    (fun c => (F c).u) (fun c => (F c).L)

noncomputable def phaseWave (s : StripData E) {D : Domain ℕ Slow}
    (F : Fin 2 → PhaseConstruction D) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → E → Slow × ℝ) (T : ℕ → E → SmoothCovariance.Vec2)
    (mask : ℕ → E → ℝ) (c : Fin 2) : ℕ → E → HarmonicCalculus.ComplexVector :=
  primaryWave s pref (fun c => (F c).frame) (fun c => (F c).lam)
    (fun c => (F c).u) (fun c => (F c).L) χ T mask c

/-- End-to-end primary class membership from the actual phase/base inputs.
The covariance matrix in the hypotheses is the integral of these same
constructed pulses. Its derivative bounds and all amplitude jets are
derived in the proof. -/
theorem phaseWave_waveClass
    (s : StripData E) (D : Domain ℕ Slow) (F : Fin 2 → PhaseConstruction D)
    (pref : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Slow × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ)
    (hscale : ∀ n, D.scale n = s.slow n)
    (hχ : PolynomialJets (phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ D.carrier n)
    (hpref : ∀ c, PolynomialJets D (fun n _ => pref c n))
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hmask : PolynomialJets (phaseDomain s) mask)
    {b M a : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (ha : 0 < a)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n))
        (phaseCovariance F pref n (χ n x).1)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * phaseCovariance F pref n (χ n x).1 i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      a * s.zeta x ≤ SmoothCovariance.weights (phaseCovariance F pref n (χ n x).1) (T n x) j)
    (c : Fin 2) :
    WaveClass s (fun n x => GaussianTailFlat.referenceSlotEnvelope
      ((F c).lam n) ((F c).u n) ((F c).L n) (χ n x).2) (1 / 2)
      (phaseWave s F pref χ T mask c) :=
  primaryWave_waveClass s D pref (fun c => (F c).frame) (fun c => (F c).lam)
    (fun c => (F c).u) (fun c => (F c).L) χ T mask hscale hχ hmap hpref
    (fun c => (F c).pulse_jets) (fun c => (F c).lam_pos) (fun c => (F c).u_pos)
    (fun c => (F c).L_pos) hT hmask hb hM ha hdet hentry hζ hlower c

end PhaseConstruction

section LocalProfiles

variable {Q : Type} [NormedAddCommGroup Q]

/-- The local cutoff uses exactly the already constructed primary ODE
solution, including its Gaussian initial normalization. -/
theorem cutoffPulse_eq_ambient_primary
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Q} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L) :
    cutoffPulse d lam u L (p, t / L) = GaussianTailFlat.slotCutoff L t •
      d.ambient (p, t) (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t) := by
  have hLt : L * (t / L) = t := by field_simp
  unfold cutoffPulse normalizedPulse
  dsimp only
  rw [hLt, fundamental_eq_primary hL U hA hp ht]
  rfl

noncomputable def localPrimaryProfile (d : PrimaryODE.FrameData Q) (lam u L radius : ℝ)
    (p : Q) (z : TorusInverse.Plane) : Space :=
  PartitionedCovariance.cutoff radius z.1 • cutoffPulse d lam u L (p, z.2 / L)

theorem localPrimaryProfile_radial
    (d : PrimaryODE.FrameData Q) (lam u radius : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Q} (hp : p ∈ U) (P : PartitionedCovariance.Pulse)
    (z : TorusInverse.Plane) (hz : z.2 ∈ Icc 0 L)
    (hψ : P.ψ z.2 = GaussianTailFlat.slotCutoff L z.2)
    (hx : P.x z.2 = (d.ambient (p, z.2)
      (PrimaryODE.primary hL.le d (fun w => referenceP lam u L w.2) p z.2)) 0) :
    P.radialProfile radius z = localPrimaryProfile d lam u L radius p z 0 := by
  rw [localPrimaryProfile, cutoffPulse_eq_ambient_primary d lam u hL U hA hp hz]
  simp only [PartitionedCovariance.Pulse.radialProfile, PiLp.smul_apply, smul_eq_mul, hψ, hx]
  ring

theorem localPrimaryProfile_tangent
    (d : PrimaryODE.FrameData Q) (lam u radius : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Q} (hp : p ∈ U) (P : PartitionedCovariance.Pulse)
    (z : TorusInverse.Plane) (hz : z.2 ∈ Icc 0 L) (i : Fin 2)
    (hψ : P.ψ z.2 = GaussianTailFlat.slotCutoff L z.2)
    (ht : P.t z.2 i = (d.ambient (p, z.2)
      (PrimaryODE.primary hL.le d (fun w => referenceP lam u L w.2) p z.2)) i.succ) :
    P.tangentProfile radius i z = localPrimaryProfile d lam u L radius p z i.succ := by
  rw [localPrimaryProfile, cutoffPulse_eq_ambient_primary d lam u hL U hA hp hz]
  simp only [PartitionedCovariance.Pulse.tangentProfile, PiLp.smul_apply, smul_eq_mul, hψ, ht]
  ring

end LocalProfiles

section PhaseCurl

open PhaseJetBounds WeightedClasses

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : StripData E} {D : Domain ℕ Slow}

noncomputable def PhaseConstruction.chartNormal (p : PhaseConstruction D)
    (χ : ℕ → E → Slow × ℝ) (n : ℕ) (x : E) : Space :=
  p.phase.normal n ((χ n x).1, p.L n * (χ n x).2)

/-- The normal appearing in the curl coefficient is the actual phase
normal. Its jets and lower bound are derived from the same phase inputs. -/
theorem PhaseConstruction.chartNormal_bounds (p : PhaseConstruction D)
    (χ : ℕ → E → Slow × ℝ) (hscale : ∀ n, D.scale n = s.slow n)
    (hχ : PolynomialJets (phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ D.carrier n)
    (hslot : ∀ n x, x ∈ s.domain → p.L n * (χ n x).2 ∈ p.V n) :
    PolynomialJets (phaseDomain s) (p.chartNormal χ) ∧
    (∀ n x, x ∈ s.domain → p.b ≤ ‖p.chartNormal χ n x‖) ∧
    (∀ n x, x ∈ s.domain → ‖p.chartNormal χ n x‖ ≤ p.M ^ 2 + 3 * p.M) := by
  have hL : PolynomialJets (phaseDomain s) (fun n _ => p.L n) := by
    apply PolynomialJets.const _ (m := 1) p.one_le_M
    intro n
    have hh := p.slot n (p.L n) (p.interval n ⟨(p.L_pos n).le, le_rfl⟩)
    simpa only [phaseDomain, pow_one, Real.norm_eq_abs, hscale n] using hh
  have hg := (hχ.clm (ContinuousLinearMap.fst ℝ Slow ℝ)).pair
    (hL.mul (hχ.clm (ContinuousLinearMap.snd ℝ Slow ℝ)))
  have hmaps : ∀ n, MapsTo (fun x => ((χ n x).1, p.L n * (χ n x).2))
      s.domain ((D.slot p.V p.openV).carrier n) :=
    fun n x hx => ⟨hmap n x hx, hslot n x hx⟩
  have hj := (EnvelopeJets.of_polynomial p.normal_jets).comp hg hscale hmaps
  refine ⟨hj.to_polynomial (fun _ _ _ => le_rfl), ?_, ?_⟩
  · intro n x hx
    exact p.normal_range.1 n _ (hmaps n hx)
  · intro n x hx
    exact p.normal_range.2 n _ (hmaps n hx)

/-- The exact-curl remainder bound specializes to the actual phase normal,
without an assumed normal-jet or propagator estimate. -/
theorem PhaseConstruction.curlRemainder_waveClass (p : PhaseConstruction D)
    (χ : ℕ → E → Slow × ℝ) (hscale : ∀ n, D.scale n = s.slow n)
    (hχ : PolynomialJets (phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x).1 ∈ D.carrier n)
    (hslot : ∀ n x, x ∈ s.domain → p.L n * (χ n x).2 ∈ p.V n)
    {P : ℕ → E → ℝ} {a : ℕ → E → HarmonicCalculus.ComplexVector}
    (ha : WaveClass s P (1 / 2) a) {κ : ℝ} (hκ : 0 ≤ κ)
    {R : E → ℝ} {Vr Vθ Vz : ℕ → E → E} {harmonic : ℕ → ℤ}
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hharmonic : ∀ n, harmonic n ≠ 0) :
    WaveClass s P (1 - κ)
      (primaryCurlRemainder s (p.chartNormal χ) R Vr Vθ Vz harmonic a) := by
  obtain ⟨hn, hlo, hup⟩ := p.chartNormal_bounds χ hscale hχ hmap hslot
  exact primaryCurlRemainder_waveClass hn ha p.b_pos hlo hup hκ hr hθ hz hR hharmonic

end PhaseCurl

section CanonicalPulse

variable {Q : Type} [NormedAddCommGroup Q]

theorem slotCutoff_zero_of_not_mem_Icc {L t : ℝ} (hL : 0 < L) (ht : t ∉ Icc 0 L) :
    GaussianTailFlat.slotCutoff L t = 0 := by
  apply GaussianTailFlat.profile_zero
  have hout : t < 0 ∨ L < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases hout with ht | ht
  · have hq : t / L < 0 := div_neg_of_neg_of_pos ht hL
    rw [abs_of_nonpos (by linarith : t / L - 1 / 2 ≤ 0)]
    linarith
  · have hq : 1 < t / L := (lt_div_iff₀ hL).mpr (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ t / L - 1 / 2)]
    linarith

theorem slotCutoff_hasCompactSupport {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (GaussianTailFlat.slotCutoff L) := by
  change IsCompact (tsupport (GaussianTailFlat.slotCutoff L))
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) L)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  exact ht (slotCutoff_zero_of_not_mem_Icc hL hn)

/-- The continuous path is obtained from the actual ambient ODE, including
both endpoints; no continuity of a clamped derivative is claimed. -/
noncomputable def canonicalPrimaryPath
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) : C(Icc (0 : ℝ) L, Space) where
  toFun t := d.ambient (p, t) (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t)
  continuous_toFun := by
    have hf : ContinuousOn (d.forcing (fun _ => 0)) (U ×ˢ Icc 0 L) := by
      simpa only [PrimaryODE.FrameData.forcing_zero_function] using
        (continuousOn_const : ContinuousOn (fun _ : Q × ℝ => (0 : State)) (U ×ˢ Icc 0 L))
    have hc : ContinuousOn (fun t => d.ambient (p, t)
        (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t)) (Icc 0 L) := by
      intro t ht
      exact (PrimaryODE.ambientSolution_hasDerivAt hL.le d 1
        (PrimaryODE.primarySeed 0 (fun z => referenceP lam u L z.2)) (fun _ => 0)
        hA hf hp hk ht).continuousAt.continuousWithinAt
    exact hc.domRestrict

/-- A literal `PartitionedCovariance.Pulse` made from this same primary
solution. Only its uncut components are continuously clamped; the cutoff
has compact support strictly inside the interval. -/
noncomputable def canonicalPrimaryPulse
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) : PartitionedCovariance.Pulse where
  ψ := GaussianTailFlat.slotCutoff L
  x t := ParametricODE.extend hL.le (canonicalPrimaryPath d lam u hL U hA p hp hk) t 0
  t t i := ParametricODE.extend hL.le (canonicalPrimaryPath d lam u hL U hA p hp hk) t i.succ
  ψ_continuous := (GaussianTailFlat.slotCutoff_contDiff L).continuous
  x_continuous := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0 : Space →L[ℝ] ℝ).continuous.comp
    (ParametricODE.continuous_extend hL.le (canonicalPrimaryPath d lam u hL U hA p hp hk))
  t_continuous := continuous_pi (fun i : Fin 2 =>
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i.succ : Space →L[ℝ] ℝ).continuous.comp
      (ParametricODE.continuous_extend hL.le (canonicalPrimaryPath d lam u hL U hA p hp hk)))
  ψ_compact := slotCutoff_hasCompactSupport hL

theorem canonicalPrimaryPulse_x
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) {t : ℝ} (ht : t ∈ Icc 0 L) :
    (canonicalPrimaryPulse d lam u hL U hA p hp hk).x t =
      (d.ambient (p, t) (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t)) 0 :=
  congrArg (fun v : Space => v 0) (ParametricODE.extend_coe hL.le
    (canonicalPrimaryPath d lam u hL U hA p hp hk) ⟨t, ht⟩)

theorem canonicalPrimaryPulse_t
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) {t : ℝ} (ht : t ∈ Icc 0 L) (i : Fin 2) :
    (canonicalPrimaryPulse d lam u hL U hA p hp hk).t t i =
      (d.ambient (p, t) (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t)) i.succ
        :=
  congrArg (fun v : Space => v i.succ) (ParametricODE.extend_coe hL.le
    (canonicalPrimaryPath d lam u hL U hA p hp hk) ⟨t, ht⟩)

/-- Global equality of the literal radial profiles, including off-slot
points where both sides vanish by the constructed cutoff. -/
theorem canonicalPrimaryPulse_radialProfile
    (d : PrimaryODE.FrameData Q) (lam u radius : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) (z : TorusInverse.Plane) :
    (canonicalPrimaryPulse d lam u hL U hA p hp hk).radialProfile radius z =
      localPrimaryProfile d lam u L radius p z 0 := by
  by_cases hz : z.2 ∈ Icc 0 L
  · exact localPrimaryProfile_radial d lam u radius hL U hA hp _ z hz rfl
      (canonicalPrimaryPulse_x d lam u hL U hA p hp hk hz)
  · have hzero := slotCutoff_zero_of_not_mem_Icc hL hz
    have hpz : GaussianTailFlat.profile (z.2 / L) = 0 := hzero
    simp only [canonicalPrimaryPulse, PartitionedCovariance.Pulse.radialProfile, hzero,
      mul_zero, zero_mul, localPrimaryProfile, cutoffPulse, hpz, zero_smul, smul_zero,
        PiLp.zero_apply]

theorem canonicalPrimaryPulse_tangentProfile
    (d : PrimaryODE.FrameData Q) (lam u radius : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) (z : TorusInverse.Plane) (i : Fin 2) :
    (canonicalPrimaryPulse d lam u hL U hA p hp hk).tangentProfile radius i z =
      localPrimaryProfile d lam u L radius p z i.succ := by
  by_cases hz : z.2 ∈ Icc 0 L
  · exact localPrimaryProfile_tangent d lam u radius hL U hA hp _ z hz i rfl
      (canonicalPrimaryPulse_t d lam u hL U hA p hp hk hz i)
  · have hzero := slotCutoff_zero_of_not_mem_Icc hL hz
    have hpz : GaussianTailFlat.profile (z.2 / L) = 0 := hzero
    simp only [canonicalPrimaryPulse, PartitionedCovariance.Pulse.tangentProfile, hzero,
      mul_zero, zero_mul, localPrimaryProfile, cutoffPulse, hpz, zero_smul, smul_zero,
        PiLp.zero_apply]

theorem canonicalPrimaryPulse_integrand
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) (i : Fin 2) (t : ℝ) :
    (canonicalPrimaryPulse d lam u hL U hA p hp hk).ψ t ^ 2 *
      (canonicalPrimaryPulse d lam u hL U hA p hp hk).x t *
      (canonicalPrimaryPulse d lam u hL U hA p hp hk).t t i =
    GaussianTailFlat.profile (t / L) ^ 2 *
      (normalizedPulse d lam u L (p, t / L) 0 * normalizedPulse d lam u L (p, t / L) i.succ) := by
  by_cases ht : t ∈ Icc 0 L
  · have hLt : L * (t / L) = t := by field_simp
    have hv : normalizedPulse d lam u L (p, t / L) =
        d.ambient (p, t) (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t) := by
      simp only [normalizedPulse, hLt]
      rw [fundamental_eq_primary hL U hA hp ht]
    rw [canonicalPrimaryPulse_x d lam u hL U hA p hp hk ht,
      canonicalPrimaryPulse_t d lam u hL U hA p hp hk ht i, hv]
    change GaussianTailFlat.profile (t / L) ^ 2 * _ * _ = _
    ring
  · have hz := slotCutoff_zero_of_not_mem_Icc hL ht
    have hpz : GaussianTailFlat.profile (t / L) = 0 := hz
    simp only [canonicalPrimaryPulse, hz, hpz, zero_pow (by omega : 2 ≠ 0), zero_mul]

theorem primaryCovariance_eq_canonicalPairMatrix
    {ι : Type*} (pref : Fin 2 → ι → ℝ) (d : Fin 2 → ι → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ι → ℝ) (n : ι)
    (U : Set Q) (p : Q) (hp : p ∈ U)
    (hL : ∀ c, 0 < L c n)
    (hA : ∀ c, ContinuousOn ((d c n).coefficient 1) (U ×ˢ Icc 0 (L c n)))
    (hk : ∀ c, (d c n).Kinematics p (Icc 0 (L c n)))
    (vr vt : TorusInverse.Plane) (radius : ℝ) (ci : SmoothCovariance.Vec2)
    (hpref : ∀ c, pref c n = PartitionedCovariance.nativePrefactor vr vt radius * ci c * L c n) :
    primaryCovariance pref d lam u L n p = PartitionedCovariance.pairMatrix vr vt radius ci
      (fun c => canonicalPrimaryPulse (d c n) (lam c n) (u c n) (hL c) U (hA c) p hp (hk c)) := by
  apply primaryCovariance_eq_pairMatrix pref d lam u L n p vr vt radius ci _ hL hpref
  intro c i t
  exact canonicalPrimaryPulse_integrand (d c n) (lam c n) (u c n) (hL c) U (hA c) p hp (hk c) i t

end CanonicalPulse

section UncutEquation

variable {Q : Type} [NormedAddCommGroup Q]

/-- The uncut normalized pulse satisfies the actual projected equation.
This is the unit fundamental used before the separate Gaussian cutoff. -/
theorem normalizedPulse_hasDerivAt
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    {p : Q} (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => normalizedPulse d lam u L (p, t))
      (L • TangentProjection.projectedRhs (d.normal (p, L * θ)) (d.normalMotion (p, L * θ))
        (normalizedPulse d lam u L (p, θ))
        (MovingFrameODE.baseAction (d.F (p, L * θ)) (d.shear (p, L * θ))
          (normalizedPulse d lam u L (p, θ))) 0 (d.viscosity (p, L * θ))) θ := by
  let f := fun t => d.ambient (p, t)
    (PrimaryODE.primary hL.le d (fun z => referenceP lam u L z.2) p t)
  have hslot {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : L * t ∈ Icc 0 L := by
    constructor
    · exact mul_nonneg hL.le ht.1.le
    · nlinarith [ht.2]
  have heq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : normalizedPulse d lam u L (p, t) = f (L * t) := by
    unfold normalizedPulse f
    rw [fundamental_eq_primary hL U hA hp (hslot ht)]
  have he : (fun t => normalizedPulse d lam u L (p, t)) =ᶠ[nhds θ] (fun t => f (L * t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact heq t ht
  have hf : ContinuousOn (d.forcing (fun _ => 0)) (U ×ˢ Icc 0 L) := by
    simpa only [PrimaryODE.FrameData.forcing_zero_function] using
      (continuousOn_const : ContinuousOn (fun _ : Q × ℝ => (0 : State)) (U ×ˢ Icc 0 L))
  have hd := PrimaryODE.ambientSolution_hasDerivAt hL.le d 1
    (PrimaryODE.primarySeed 0 (fun z => referenceP lam u L z.2)) (fun _ => 0)
    hA hf hp hk (hslot hθ)
  have hc := hd.scomp θ ((hasDerivAt_id θ).const_mul L)
  change HasDerivAt (fun t => f (L * t)) ((L * 1) • _) θ at hc
  rw [mul_one, PrimaryODE.FrameData.damping_one] at hc
  have hout := hc.congr_of_eventuallyEq he
  have hv : PrimaryODE.ambientSolution hL.le d 1
      (PrimaryODE.primarySeed 0 (fun z => referenceP lam u L z.2)) (fun _ => 0) p (L * θ) =
      normalizedPulse d lam u L (p, θ) := (heq θ hθ).symm
  simpa only [hv] using hout

end UncutEquation

section CutoffFactorization

open WeightedClasses

variable {Q E : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def uncutPrimaryWave (s : StripData E)
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ) (c : Fin 2) :
    ℕ → E → HarmonicCalculus.ComplexVector :=
  primaryCoefficient s (chartCovariance pref d lam u L χ) T mask
    (fun n x => normalizedPulse (d c n) (lam c n) (u c n) (L c n) (χ n x)) c

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
/-- The slot cutoff occurs exactly once. This identity matches a linear-wave
coefficient's external `withCutoff` operation to the physical primary. -/
theorem primaryWave_eq_cutoff (s : StripData E)
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ) (c : Fin 2) (n : ℕ) (x : E) :
    primaryWave s pref d lam u L χ T mask c n x =
      GaussianTailFlat.profile (χ n x).2 • uncutPrimaryWave s pref d lam u L χ T mask c n x := by
  simp only [primaryWave, uncutPrimaryWave, primaryCoefficient, cutoffPulse, map_smul,
    smul_smul, mul_comm]

/-- The same quantitative estimate before applying the external Gaussian
slot cutoff. This is the class used for the homogeneous principal equation. -/
theorem uncutPrimaryWave_waveClass
    (s : StripData E) (D : PhaseJetBounds.Domain ℕ Q)
    (pref : Fin 2 → ℕ → ℝ) (d : Fin 2 → ℕ → PrimaryODE.FrameData Q)
    (lam u L : Fin 2 → ℕ → ℝ) (χ : ℕ → E → Q × ℝ)
    (T : ℕ → E → SmoothCovariance.Vec2) (mask : ℕ → E → ℝ)
    (hscale : ∀ n, D.scale n = s.slow n)
    (hχ : PhaseJetBounds.PolynomialJets (phaseDomain s) χ)
    (hmap : ∀ n x, x ∈ s.domain → (χ n x) ∈ D.carrier n ×ˢ Ioo (0 : ℝ) 1)
    (hpref : ∀ c, PhaseJetBounds.PolynomialJets D (fun n _ => pref c n))
    (hpulse : ∀ c, EnvelopeJets
      (productDomain D (fun _ => Ioo (0 : ℝ) 1) (fun _ => isOpen_Ioo))
      (fun n z => referenceP (lam c n) (u c n) (L c n) (L c n * z.2))
      (fun n => normalizedPulse (d c n) (lam c n) (u c n) (L c n)))
    (hlam : ∀ c n, 0 < lam c n) (hu : ∀ c n, 0 < u c n) (hL : ∀ c n, 0 < L c n)
    (hT : ∀ i, MeanClass s 0 (fun n x => T n x i))
    (hmask : PhaseJetBounds.PolynomialJets (phaseDomain s) mask)
    {b M a : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (ha : 0 < a)
    (hdet : ∀ n x, x ∈ s.domain →
      b ≤ |(normalizedMatrix (Real.sqrt (s.slow n)) (chartCovariance pref d lam u L χ n x)).det|)
    (hentry : ∀ n x, x ∈ s.domain → ∀ i j,
      |Real.sqrt (s.slow n) * chartCovariance pref d lam u L χ n x i j| ≤ M)
    (hζ : ∀ x, x ∈ s.domain → 0 < s.zeta x)
    (hlower : ∀ n x, x ∈ s.domain → ∀ j,
      a * s.zeta x ≤ SmoothCovariance.weights (chartCovariance pref d lam u L χ n x) (T n x) j)
    (c : Fin 2) :
    WaveClass s (fun n x => referenceP (lam c n) (u c n) (L c n) (L c n * (χ n x).2))
      (1 / 2) (uncutPrimaryWave s pref d lam u L χ T mask c) := by
  have hH (i j : Fin 2) : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n x => chartCovariance pref d lam u L χ n x i j) := by
    apply ((EnvelopeJets.of_polynomial
      (primaryCovariance_entry_polynomial D pref d lam u L hpref hpulse hlam hu hL i j)).comp
      (hχ.clm (ContinuousLinearMap.fst ℝ Q ℝ)) hscale (fun n x hx => (hmap n x hx).1)).to_polynomial
    intro n x hx
    rfl
  have hp := (hpulse c).comp hχ hscale hmap
  have hv := hp.memClass s (fun _ => rfl) (fun _ => rfl)
  exact primaryCoefficient_waveClass hH hT hmask hv hb hM ha hdet hentry hζ hlower c

end CutoffFactorization

end NavierStokes.PrimaryPulseBounds
