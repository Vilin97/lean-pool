/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverClass
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopySolveCompatibility
public import LeanPool.NavierStokesAndEuler.NavierStokes.CopyAngularInvariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryCopyBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveBounds

@[expose] public section

/-!
# Particular waves from the actual forced copy-path solve

The estimates below apply to the Volterra solution itself. Endpoint rescaling
proves bounds for full joint derivatives, so no fixed-time to joint-smoothness
inference or assumed output class is used. The source envelope stays explicit
along the whole integration path.
-/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace BigOperators
open PrimaryPulseBounds

section JointEstimate

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Full joint parameter and endpoint jets of the actual zero-entry forced
solution. The factor `w` is frozen at the parameter being estimated; no
regularity or derivative bound on this majorant is required. -/
theorem forced_joint_jet_bound
    {L S K μ w : ℝ} (_hL : 0 < L) (hS : 1 ≤ S) (hK : 1 ≤ K) (hμ : 0 ≤ μ)
    (hw : 0 ≤ w) (hslot : L ≤ K * S) (hExp : Real.exp (μ * L) ≤ K)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc 0 L ⊆ V)
    (A : Q × ℝ → H →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A (U ×ˢ V))
    (P rate : ℝ → ℝ) (hP : ∀ t, 0 < P t)
    (hdP : ∀ t, HasDerivAt P (rate t * P t) t)
    (f : Q × ℝ → H) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) {p : Q} (hp : p ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L)
    (henergy : ∀ v ∈ Icc 0 L, ∀ x : H,
      ⟪x, A (p, v) x⟫_ℝ ≤ (rate v + μ) * ‖x‖ ^ 2)
    (m N : ℕ)
    (hjets : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j A (p, v)‖ ≤ K * S ^ m)
    (hfjets : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j f (p, v)‖ ≤ w * K * S ^ m * P v)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j
      (JointODE.reparamSolution 0 A (fun _ => 0) f) (p, t)‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (j + 1) *
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
  have hfr : ContDiffOn ℝ ∞ (JointODE.rescale 0 f) (O ×ˢ T) :=
    JointODE.rescale_contDiffOn f hf hmap
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
      ‖iteratedFDeriv ℝ k (fun _ : Q × ℝ => (0 : H)) (p, t)‖ ≤
        w * K' * S ^ (m + 1) * P ((0 : ℝ) * t) := by
    intro k _
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_mul]
    have hp0 := hP 0
    positivity
  have hfjet : ∀ k ≤ N, ∀ σ : Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ k (fun q => JointODE.rescale 0 f (q, σ)) (p, t)‖ ≤
        w * K' * S ^ (m + 1) * P ((σ : ℝ) * t) := by
    intro k hk σ
    have hσ : |(σ : ℝ)| ≤ 1 := by rw [abs_of_nonneg σ.2.1]; exact σ.2.2
    have hp0 := hP ((σ : ℝ) * t)
    have hh := rescale_jet_bound (hU.prod hV) hf hσ
      (show timeLinear (σ : ℝ) (p, t) ∈ U ×ˢ V from ⟨hp, hI (hinside σ)⟩)
      (show 0 ≤ w * K * S ^ m * P ((σ : ℝ) * t) by positivity) hKS
      (show |t| ≤ K * S by rw [abs_of_nonneg ht.1]; exact ht.2.trans hslot) hk
      (fun i hi => hfjets i hi _ (hinside σ))
    have hconst : (2 : ℝ) ^ N * K ^ 2 ≤ K' := by
      dsimp [K', rescaleConstant]
      linarith
    calc
      _ ≤ (2 : ℝ) ^ N * (K * S) * (w * K * S ^ m * P ((σ : ℝ) * t)) := by
        simpa only [JointODE.rescale, JointODE.timeMap, JointODE.affineTime, sub_zero, zero_add]
          using hh
      _ = w * ((2 : ℝ) ^ N * K ^ 2) * S ^ (m + 1) * P ((σ : ℝ) * t) := by
        rw [pow_succ]
        ring
      _ ≤ _ := by gcongr
  have hExp' : Real.exp ((t * μ) * ((1 : ℝ) - 0)) ≤ K' := by
    apply (Real.exp_le_exp.mpr (show (t * μ) * (1 - 0) ≤ μ * L by nlinarith [ht.2])).trans
    exact hExp.trans hKK'
  have hh := WeightedODEJets.norm_iteratedFDeriv_odeFamily_le_polynomial
    (a := 0) (b := 1) zero_le_one O T hO hT hIT
    (JointODE.rescale 0 A) (fun _ : Q × ℝ => (0 : H))
    (JointODE.rescale 0 f)
    hAr contDiffOn_const hfr hpoint (fun σ => t * rate (σ * t)) (fun σ => P (σ * t))
    (mul_nonneg ht.1 hμ) (fun σ => hP _) hweight henergy' hExp' hS hK' hw
    (show (1 : ℝ) - 0 ≤ K' * S by nlinarith) (m + 1) N hAjet hxjet hfjet j hj
    ⟨1, zero_le_one, le_rfl⟩
  simp only [one_mul, Nat.add_assoc] at hh ⊢
  exact hh


end JointEstimate

section FamilyEstimate

variable {ι : Type*} {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A band-uniform family version of the joint forced estimate. Both input
predicates refer to actual full derivatives of the coefficient and source. -/
theorem forced_family_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (L μ : ι → ℝ) (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    (A : ι → Q × ℝ → H →L[ℝ] H)
    (hA : PhaseJetBounds.PolynomialJets (productDomain D V hV) A)
    (P rate : ι → ℝ → ℝ) (hP : ∀ i t, 0 < P i t)
    (hdP : ∀ i t, HasDerivAt (P i) (rate i t * P i t) t)
    (w : ι → Q → ℝ) (hw : ∀ i p, p ∈ D.carrier i → 0 ≤ w i p)
    (f : ι → Q × ℝ → H)
    (hf : EnvelopeJets (productDomain D V hV) (fun i z => w i z.1 * P i z.2) f)
    {K₀ : ℝ} (hK₀ : 1 ≤ K₀) (hμ : ∀ i, 0 ≤ μ i)
    (hslot : ∀ i, L i ≤ K₀ * D.scale i)
    (hExp : ∀ i, Real.exp (μ i * L i) ≤ K₀)
    (henergy : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), ∀ x : H,
      ⟪x, A i (p, v) x⟫_ℝ ≤ (rate i v + μ i) * ‖x‖ ^ 2) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => w i z.1 * P i z.2)
      (fun i => JointODE.reparamSolution 0 (A i) (fun _ => 0) (f i)) := by
  refine ⟨fun i x hx => mul_nonneg (hw i x.1 hx.1) (hP i x.2).le, ?_, ?_⟩
  · intro i z hz
    exact (JointODE.reparamSolution_contDiffAt (D.carrier i) (V i) (D.isOpen i) (hV i) (hI i)
      (A i) (fun _ => 0) (f i) (hA.smooth i) contDiffOn_const (hf.smooth i)
      (show z ∈ D.carrier i ×ˢ Icc 0 (L i) from ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)).contDiffWithinAt
  intro N
  obtain ⟨C, hC, m, hm⟩ := hA.bound N
  obtain ⟨C', hC', m', hm'⟩ := hf.bound N
  let K := C + C' + K₀ + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hC'K : C' ≤ K := by dsimp [K]; linarith
  have hK₀K : K₀ ≤ K := by dsimp [K]; linarith
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  refine ⟨B ^ (N + 1), one_le_pow₀ hB, (m + m' + 2) * (N + 1), ?_⟩
  intro i z hz j hj
  have hS := D.one_le_scale i
  have hS0 := zero_le_one.trans hS
  have hw0 := hw i z.1 hz.1
  have hAj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L i),
      ‖iteratedFDeriv ℝ k (A i) (z.1, v)‖ ≤ K * D.scale i ^ (m + m') := by
    intro k hk v hv
    exact (hm i k hk (z.1, v) ⟨hz.1, hI i hv⟩).trans
      (mul_le_mul hCK (pow_le_pow_right₀ hS (Nat.le_add_right m m'))
        (pow_nonneg hS0 _) (zero_le_one.trans hK))
  have hfj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L i),
      ‖iteratedFDeriv ℝ k (f i) (z.1, v)‖ ≤ w i z.1 * K * D.scale i ^ (m + m') * P i v := by
    intro k hk v hv
    calc
      _ ≤ C' * D.scale i ^ m' * (w i z.1 * P i v) := hm' i (z.1, v) ⟨hz.1, hI i hv⟩ k hk
      _ ≤ K * D.scale i ^ (m + m') * (w i z.1 * P i v) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hC'K
          (pow_le_pow_right₀ hS (Nat.le_add_left m' m)) (pow_nonneg hS0 _)
          (zero_le_one.trans hK)) (mul_nonneg hw0 (hP i v).le)
      _ = _ := by ring
  have hh := forced_joint_jet_bound (hL i) hS hK (hμ i) hw0
    ((hslot i).trans (mul_le_mul_of_nonneg_right hK₀K hS0))
    ((hExp i).trans hK₀K) (D.carrier i) (V i) (D.isOpen i) (hV i) (hI i)
    (A i) (hA.smooth i) (P i) (rate i) (hP i) (hdP i) (f i) (hf.smooth i) hz.1
    ⟨hz.2.1.le, hz.2.2.le⟩ (henergy i z.1 hz.1) (m + m') N hAj hfj j hj
  calc
    _ ≤ w i z.1 * B ^ (j + 1) * D.scale i ^ ((m + m' + 2) * (j + 1)) * P i z.2 := hh
    _ = (B ^ (j + 1) * D.scale i ^ ((m + m' + 2) * (j + 1))) *
        (w i z.1 * P i z.2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_right₀ hB (Nat.add_le_add_right hj 1))
        (pow_le_pow_right₀ hS (Nat.mul_le_mul_left _ (Nat.add_le_add_right hj 1)))
        (pow_nonneg hS0 _) (pow_nonneg (zero_le_one.trans hB) _))
      (mul_nonneg hw0 (hP i z.2).le)

end FamilyEstimate

section EnvelopeTransfer

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {D : PhaseJetBounds.Domain ι E} {w : ι → E → ℝ} {f g : ι → E → F}

/-- Local equality transfers the actual derivative estimates; no derivatives
of an extension outside the open carrier are used. -/
theorem envelopeJets_congr (hf : EnvelopeJets D w f)
    (he : ∀ i, EqOn (f i) (g i) (D.carrier i)) : EnvelopeJets D w g := by
  refine ⟨hf.nonneg, fun i => (hf.smooth i).congr (he i).symm, ?_⟩
  intro N
  obtain ⟨C, hC, m, hb⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i x hx j hj
  have heq : f i =ᶠ[𝓝 x] g i := eventually_of_mem ((D.isOpen i).mem_nhds hx) (he i)
  have heq' : f i =ᶠ[𝓝[univ] x] g i := by simpa only [nhdsWithin_univ] using heq
  have hjet := heq'.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.self_of_nhds j
  simp only [iteratedFDerivWithin_univ] at hjet
  rw [← hjet]
  exact hb i x hx j hj

end EnvelopeTransfer

section AffineEvaluation

variable {ι E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Relative version of the affine higher chain rule. The affine map need
not be bounded at order zero, and `f` need only be smooth on its open domain. -/
theorem norm_jet_comp_affine {U : Set F} (hU : IsOpen U) {f : F → G}
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] F) (c : F) {x : E}
    (hx : c + L x ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f (c + L y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (c + L x)‖ * ‖L‖ ^ j := by
  let V := (fun y : F => c + y) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hft : ContDiffOn ℝ ∞ (fun y : F => f (c + y)) V :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ hy => hy)
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left] using
    PhaseJetBounds.norm_jet_comp_linear hV hft L hx j

theorem envelopeJets_precomp_affine {D : PhaseJetBounds.Domain ι E}
    {D' : PhaseJetBounds.Domain ι F} {w : ι → F → ℝ} {f : ι → F → G}
    (hf : EnvelopeJets D' w f) (L : ι → E →L[ℝ] F) (c : ι → F)
    (hscale : ∀ i, D'.scale i = D.scale i)
    (hmap : ∀ i, MapsTo (fun x => c i + L i x) (D.carrier i) (D'.carrier i))
    {C : ℝ} {k : ℕ} (hC : 1 ≤ C) (hL : ∀ i, ‖L i‖ ≤ C * D.scale i ^ k) :
    EnvelopeJets D (fun i x => w i (c i + L i x)) (fun i x => f i (c i + L i x)) := by
  refine ⟨fun i x hx => hf.nonneg i _ (hmap i hx),
    fun i => (hf.smooth i).comp (contDiffOn_const.add (L i).contDiff.contDiffOn) (hmap i), ?_⟩
  intro N
  obtain ⟨A, hA, m, hm⟩ := hf.bound N
  refine ⟨A * C ^ N, one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hC), m + k * N, ?_⟩
  intro i x hx j hj
  have hc : 1 ≤ C * D.scale i ^ k :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (D.one_le_scale i))
  have hpow : ‖L i‖ ^ j ≤ (C * D.scale i ^ k) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg _) (hL i) j).trans (pow_le_pow_right₀ hc hj)
  have hw := hf.nonneg i (c i + L i x) (hmap i hx)
  have hb : 0 ≤ A * D'.scale i ^ m * w i (c i + L i x) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hA)
      (pow_nonneg (zero_le_one.trans (D'.one_le_scale i)) _)) hw
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i) (c i + L i x)‖ * ‖L i‖ ^ j :=
      norm_jet_comp_affine (D'.isOpen i) (hf.smooth i) (L i) (c i) (hmap i hx) j
    _ ≤ (A * D'.scale i ^ m * w i (c i + L i x)) * (C * D.scale i ^ k) ^ N :=
      mul_le_mul (hm i _ (hmap i hx) j hj) hpow (pow_nonneg (norm_nonneg _) _) hb
    _ = _ := by rw [hscale, mul_pow, pow_add, pow_mul]; ring

end AffineEvaluation

section CopyFamilies

open CommonCoverSolve
open TorusInverse

variable {ι : Type} {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The same bound for the actual copy-path Volterra extension. Uniqueness
identifies it with the endpoint-rescaled solve on an open slot. -/
theorem anchoredSolve_family_envelope_jets
    (D : PhaseJetBounds.Domain ι (P × Plane)) (I : ι → Set ℝ) (hI : ∀ i, IsOpen (I i))
    (L μ : ι → ℝ) (hL : ∀ i, 0 < L i) (hslotI : ∀ i, Icc 0 (L i) ⊆ I i)
    (d : ι → LinearData P V H) (g : ι → Geometry) (copy : ι → Frequency)
    (hA : PhaseJetBounds.PolynomialJets (productDomain D I hI)
      (fun i => (d i).coefficientAlong (g i) (copy i)))
    (W rate : ι → ℝ → ℝ) (hW : ∀ i t, 0 < W i t)
    (hdW : ∀ i t, HasDerivAt (W i) (rate i t * W i t) t)
    (w : ι → P × Plane → ℝ) (hw : ∀ i p, p ∈ D.carrier i → 0 ≤ w i p)
    (hf : EnvelopeJets (productDomain D I hI) (fun i z => w i z.1 * W i z.2)
      (fun i => (d i).forcingAlong (g i) (copy i)))
    {K : ℝ} (hK : 1 ≤ K) (hμ : ∀ i, 0 ≤ μ i)
    (hslot : ∀ i, L i ≤ K * D.scale i) (hExp : ∀ i, Real.exp (μ i * L i) ≤ K)
    (henergy : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), ∀ x : H,
      ⟪x, (d i).coefficientAlong (g i) (copy i) (p, v) x⟫_ℝ ≤ (rate i v + μ i) * ‖x‖ ^ 2) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => w i z.1 * W i z.2)
      (fun i z => (d i).anchoredSolve (g i) (hL i).le (copy i) z.1 z.2) := by
  have hs := forced_family_envelope_jets D I hI L μ hL hslotI _ hA W rate hW hdW w hw _ hf
    hK hμ hslot hExp henergy
  apply envelopeJets_congr hs
  intro i z hz
  have hAc := (hA.smooth i).continuousOn.mono (prod_mono Subset.rfl (hslotI i))
  have hfc := (hf.smooth i).continuousOn.mono (prod_mono Subset.rfl (hslotI i))
  exact JointODE.reparamSolution_eq_actualSolution (hL i).le _ _ _ hAc hfc
    ⟨hz.1, hz.2.1.le, hz.2.2.le⟩

/-- Evaluation at the current native slot costs only the norm of the actual
affine coordinate map. This statement is uniform over copy indices. -/
theorem copySolve_envelope_of_anchored
    (D D' : PhaseJetBounds.Domain ι (P × Plane)) (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (d : ι → LinearData P V H) (g : ι → Geometry) (copy : ι → Frequency)
    (w : ι → P × Plane → ℝ) (W : ι → ℝ → ℝ)
    (hs : EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => w i z.1 * W i z.2)
      (fun i z => (d i).anchoredSolve (g i) (hL i).le (copy i) z.1 z.2))
    (hscale : ∀ i, D.scale i = D'.scale i)
    (hdom : ∀ i, D'.carrier i ⊆ D.carrier i)
    (hslot : ∀ i p, p ∈ D'.carrier i → ((g i).coordinates (copy i) p.2).2 ∈ Ioo 0 (L i))
    {C : ℝ} {k : ℕ} (hC : 1 ≤ C)
    (hcost : ∀ i, CommonCoverClass.argumentCost (g i) ≤ C * D'.scale i ^ k) :
    EnvelopeJets D' (fun i p => w i p * W i ((g i).coordinates (copy i) p.2).2)
      (fun i => (d i).copySolve (g i) (hL i).le (copy i)) := by
  have hh := envelopeJets_precomp_affine hs
    (fun i => CommonCoverClass.currentLinear P (g i))
    (fun i => CommonCoverClass.currentArgument (P := P) (g i) (copy i) 0)
    hscale (fun i p hp => ?_) hC
    (fun i => (CommonCoverClass.norm_currentLinear_le (P := P) (g i)).trans (hcost i))
  · simp_rw [← CommonCoverClass.currentArgument_affine] at hh
    simp only [CommonCoverClass.currentArgument] at hh ⊢
    exact hh
  · dsimp only
    rw [← CommonCoverClass.currentArgument_affine]
    exact ⟨hdom i hp, hslot i p hp⟩

end CopyFamilies

section CopyJointEstimate

open CommonCoverSolve TorusInverse

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Full derivatives of the actual current copy field. In particular the
scale `S` may be the frozen spatial growth/edge factor at `p`; no uniform
distance from a cutoff edge is required. -/
theorem copySolve_joint_jet_bound (d : LinearData P V H) (g : Geometry) (copy : Frequency)
    {L S K μ w : ℝ} (hL : 0 < L) (hS : 1 ≤ S) (hK : 1 ≤ K) (hμ : 0 ≤ μ) (hw : 0 ≤ w)
    (hslot : L ≤ K * S) (hExp : Real.exp (μ * L) ≤ K)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    (W rate : ℝ → ℝ) (hW : ∀ t, 0 < W t) (hdW : ∀ t, HasDerivAt W (rate t * W t) t)
    {p : P × Plane} (hp : p.1 ∈ U) (heta : (g.coordinates copy p.2).2 ∈ Ioo 0 L)
    (henergy : ∀ v ∈ Icc 0 L, ∀ x : H,
      ⟪x, d.coefficientAlong g copy (p, v) x⟫_ℝ ≤ (rate v + μ) * ‖x‖ ^ 2)
    (m N : ℕ)
    (hAj : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j (d.coefficientAlong g copy) (p, v)‖ ≤ K * S ^ m)
    (hfj : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j (d.forcingAlong g copy) (p, v)‖ ≤ w * K * S ^ m * W v)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (d.copySolve g hL.le copy) p‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (j + 1) *
        S ^ ((m + 2) * (j + 1)) * W (g.coordinates copy p.2).2 *
          CommonCoverClass.argumentCost g ^ j := by
  let A := d.coefficientAlong g copy
  let f := d.forcingAlong g copy
  let r := JointODE.reparamSolution 0 A (fun _ => 0) f
  let T := (U ×ˢ (univ : Set Plane)) ×ˢ Ioo 0 L
  have hT : IsOpen T := (hU.prod isOpen_univ).prod isOpen_Ioo
  have hAs : ContDiffOn ℝ ∞ A ((U ×ˢ univ) ×ˢ (univ : Set ℝ)) := d.coefficientAlong_contDiffOn g
    copy hA
  have hfs : ContDiffOn ℝ ∞ f ((U ×ˢ univ) ×ˢ (univ : Set ℝ)) := d.forcingAlong_contDiffOn g copy
    hB hf
  have hrs : ContDiffOn ℝ ∞ r T := by
    intro z hz
    exact (JointODE.reparamSolution_contDiffAt (U ×ˢ univ) univ (hU.prod isOpen_univ)
      isOpen_univ (subset_univ _) A (fun _ => 0) f hAs contDiffOn_const hfs
      (show z ∈ (U ×ˢ univ) ×ˢ Icc 0 L from ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)).contDiffWithinAt
  have hcur : CommonCoverClass.currentArgument g copy p ∈ T := ⟨⟨hp, mem_univ _⟩, heta⟩
  have heq : (fun q => r (CommonCoverClass.currentArgument g copy q)) =ᶠ[𝓝 p]
      d.copySolve g hL.le copy := by
    filter_upwards [((CommonCoverClass.currentArgument_smooth (P := P) g
      copy).continuous.isOpen_preimage _ hT).mem_nhds hcur] with q hq
    exact JointODE.reparamSolution_eq_actualSolution hL.le A (fun _ => 0) f
      (hAs.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
      (hfs.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
      (show CommonCoverClass.currentArgument g copy q ∈ (U ×ˢ univ) ×ˢ Icc 0 L from
        ⟨hq.1, hq.2.1.le, hq.2.2.le⟩)
  have heq' : (fun q => r (CommonCoverClass.currentArgument g copy q)) =ᶠ[𝓝[univ] p]
      d.copySolve g hL.le copy := by simpa only [nhdsWithin_univ] using heq
  have hjet := heq'.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.self_of_nhds j
  simp only [iteratedFDerivWithin_univ] at hjet
  rw [← hjet]
  have haff := norm_jet_comp_affine hT hrs (CommonCoverClass.currentLinear P g)
    (CommonCoverClass.currentArgument (P := P) g copy 0)
    (by simpa only [← CommonCoverClass.currentArgument_affine] using hcur) j
  simp_rw [← CommonCoverClass.currentArgument_affine] at haff
  have hbnd := forced_joint_jet_bound hL hS hK hμ hw hslot hExp (U ×ˢ univ) univ
    (hU.prod isOpen_univ) isOpen_univ (subset_univ _) A hAs W rate hW hdW f hfs
    ⟨hp, mem_univ _⟩ ⟨heta.1.le, heta.2.le⟩ henergy m N hAj hfj j hj
  apply haff.trans
  exact mul_le_mul hbnd
    (pow_le_pow_left₀ (norm_nonneg _) (CommonCoverClass.norm_currentLinear_le (P := P) g) j)
    (pow_nonneg (norm_nonneg _) j)
    (by
      have := hW (g.coordinates copy p.2).2
      have hR := hK.trans (le_rescaleConstant N K)
      positivity)

end CopyJointEstimate

section CopyClass

open CommonCoverSolve TorusInverse WeightedClasses

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual particular solution belongs to `W_α`. Input bounds are on
the full joint derivatives of the pulled-back coefficient and source;
the edge power may depend on the requested derivative order. -/
theorem copySolve_waveClass
    (s : StripData (P × Plane)) (α : ℝ)
    (d : ℕ → LinearData P V H) (g : ℕ → Geometry) (copy : ℕ → Frequency)
    (L μ : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W rate : ℕ → ℝ → ℝ) (hW : ∀ n t, 0 < W n t)
    (hdW : ∀ n t, HasDerivAt (W n) (rate n t * W n t) t)
    {U : Set P} (hU : IsOpen U) (hdom : ∀ p ∈ s.domain, p.1 ∈ U)
    (hA : ∀ n, ContDiffOn ℝ ∞ (d n).coefficient (U ×ˢ univ))
    (hB : ∀ n, ContDiffOn ℝ ∞ (d n).forcingMap (U ×ˢ univ))
    (hf : ∀ n, ContDiffOn ℝ ∞ (d n).source (U ×ˢ univ))
    (heta : ∀ n p, p ∈ s.domain → ((g n).coordinates (copy n) p.2).2 ∈ Ioo 0 (L n))
    {K₀ : ℝ} {q : ℕ} (hK₀ : 1 ≤ K₀) (hμ : ∀ n, 0 ≤ μ n)
    (hslot : ∀ n, L n ≤ K₀ * s.slow n) (hExp : ∀ n, Real.exp (μ n * L n) ≤ K₀)
    (hcost : ∀ n, CommonCoverClass.argumentCost (g n) ≤ K₀ * s.slow n ^ q)
    (henergy : ∀ n p, p ∈ s.domain → ∀ v ∈ Icc 0 (L n), ∀ x : H,
      ⟪x, (d n).coefficientAlong (g n) (copy n) (p, v) x⟫_ℝ ≤
        (rate n v + μ n) * ‖x‖ ^ 2)
    (hinput : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ n p, p ∈ s.domain →
      ∀ j ≤ N, ∀ v ∈ Icc 0 (L n),
        ‖iteratedFDeriv ℝ j ((d n).coefficientAlong (g n) (copy n)) (p, v)‖ ≤
          C * s.growth n p ^ m ∧
        ‖iteratedFDeriv ℝ j ((d n).forcingAlong (g n) (copy n)) (p, v)‖ ≤
          (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * C * s.growth n p ^ m * W n v) :
    WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α
      (fun n => (d n).copySolve (g n) (hL n).le (copy n)) := by
  refine ⟨fun n p _ => mul_nonneg (Real.sqrt_nonneg _) (hW n _).le, ?_, ?_⟩
  · intro n p hp
    exact ((d n).copySolve_contDiffAt (g n) (hL n).le hU (copy n)
      (hA n) (hB n) (hf n) (hdom p hp) (heta n p hp)).contDiffWithinAt
  intro N
  obtain ⟨C, hC, m, hm⟩ := hinput N
  let K := C + K₀ + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hK₀K : K₀ ≤ K := by dsimp [K]; linarith
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB' : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  refine ⟨B ^ (N + 1) * K₀ ^ N, by positivity, (m + 2) * (N + 1) + q * N, ?_⟩
  intro n p hp j hj
  have hG := s.one_le_growth n p
  have hG0 := s.growth_nonneg n p
  have heps := (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le
  have hw : 0 ≤ s.epsilon n ^ α * Real.sqrt (s.zeta p) := mul_nonneg heps (Real.sqrt_nonneg _)
  have hAj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ k ((d n).coefficientAlong (g n) (copy n)) (p, v)‖ ≤ K * s.growth n p ^ m :=
        by
    intro k hk v hv
    exact ((hm n p hp k hk v hv).1).trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg hG0 _))
  have hfj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ k ((d n).forcingAlong (g n) (copy n)) (p, v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * K * s.growth n p ^ m * W n v := by
    intro k hk v hv
    exact ((hm n p hp k hk v hv).2).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCK hw) (pow_nonneg hG0 _)) (hW n v).le)
  have hh := copySolve_joint_jet_bound (d n) (g n) (copy n) (hL n) hG hK (hμ n) hw
    ((hslot n).trans (mul_le_mul hK₀K (s.slow_le_growth n p)
      (zero_le_one.trans (s.one_le_slow n)) (zero_le_one.trans hK)))
    ((hExp n).trans hK₀K) hU (hA n) (hB n) (hf n) (W n) (rate n) (hW n) (hdW n)
    (hdom p hp) (heta n p hp) (henergy n p hp) m N hAj hfj j hj
  have hcg : CommonCoverClass.argumentCost (g n) ≤ K₀ * s.growth n p ^ q :=
    (hcost n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n p) q)
      (zero_le_one.trans hK₀))
  have hcp : CommonCoverClass.argumentCost (g n) ^ j ≤ K₀ ^ N * s.growth n p ^ (q * N) := by
    calc
      _ ≤ (K₀ * s.growth n p ^ q) ^ j := pow_le_pow_left₀
        (zero_le_one.trans (CommonCoverClass.one_le_argumentCost (g n))) hcg j
      _ ≤ (K₀ * s.growth n p ^ q) ^ N := pow_le_pow_right₀
        (one_le_mul_of_one_le_of_one_le hK₀ (one_le_pow₀ hG)) hj
      _ = _ := by rw [mul_pow, pow_mul]
  have hwp := (hW n ((g n).coordinates (copy n) p.2).2).le
  calc
    _ ≤ (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * B ^ (j + 1) *
        s.growth n p ^ ((m + 2) * (j + 1)) * W n ((g n).coordinates (copy n) p.2).2 *
        CommonCoverClass.argumentCost (g n) ^ j := hh
    _ ≤ (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * B ^ (N + 1) *
        s.growth n p ^ ((m + 2) * (N + 1)) * W n ((g n).coordinates (copy n) p.2).2 *
        (K₀ ^ N * s.growth n p ^ (q * N)) := by
      apply mul_le_mul _ hcp
        (pow_nonneg (zero_le_one.trans (CommonCoverClass.one_le_argumentCost (g n))) _)
        (by positivity)
      apply mul_le_mul_of_nonneg_right _ hwp
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB' (Nat.add_le_add_right hj 1)) hw)
        (pow_le_pow_right₀ hG (Nat.mul_le_mul_left _ (Nat.add_le_add_right hj 1)))
        (pow_nonneg hG0 _) (by positivity)
    _ = _ := by unfold majorant; rw [pow_add]; ring

end CopyClass

section ControlData

open CommonCoverSolve TorusInverse WeightedClasses

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Primitive data for the direct weighted Volterra estimate. No field in
this structure bounds a solution or assumes its differential equation. -/
structure CopyControl (s : StripData (P × Plane)) (α : ℝ)
    (d : ℕ → LinearData P V H) (g : ℕ → Geometry) (copy : ℕ → Frequency)
    (L : ℕ → ℝ) (W : ℕ → ℝ → ℝ) where
  slowDomain : Set P
  open_slow : IsOpen slowDomain
  domain : ∀ p ∈ s.domain, p.1 ∈ slowDomain
  coefficient_smooth : ∀ n, ContDiffOn ℝ ∞ (d n).coefficient (slowDomain ×ˢ univ)
  forcingMap_smooth : ∀ n, ContDiffOn ℝ ∞ (d n).forcingMap (slowDomain ×ˢ univ)
  source_smooth : ∀ n, ContDiffOn ℝ ∞ (d n).source (slowDomain ×ˢ univ)
  length_pos : ∀ n, 0 < L n
  current_slot : ∀ n p, p ∈ s.domain → ((g n).coordinates (copy n) p.2).2 ∈ Ioo 0 (L n)
  rate : ℕ → ℝ → ℝ
  envelope_pos : ∀ n v, 0 < W n v
  envelope_deriv : ∀ n v, HasDerivAt (W n) (rate n v * W n v) v
  errorRate : ℕ → ℝ
  errorRate_nonneg : ∀ n, 0 ≤ errorRate n
  boundConstant : ℝ
  constant_ge_one : 1 ≤ boundConstant
  coordinate_power : ℕ
  length_bound : ∀ n, L n ≤ boundConstant * s.slow n
  exponential_bound : ∀ n, Real.exp (errorRate n * L n) ≤ boundConstant
  coordinate_bound : ∀ n, CommonCoverClass.argumentCost (g n) ≤ boundConstant * s.slow n ^
    coordinate_power
  energy : ∀ n p, p ∈ s.domain → ∀ v ∈ Icc 0 (L n), ∀ x : H,
    ⟪x, (d n).coefficientAlong (g n) (copy n) (p, v) x⟫_ℝ ≤ (rate n v + errorRate n) * ‖x‖ ^ 2
  input_jets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ n p, p ∈ s.domain →
    ∀ j ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ j ((d n).coefficientAlong (g n) (copy n)) (p, v)‖ ≤ C * s.growth n p ^ m ∧
      ‖iteratedFDeriv ℝ j ((d n).forcingAlong (g n) (copy n)) (p, v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * C * s.growth n p ^ m * W n v

theorem CopyControl.waveClass {s : StripData (P × Plane)} {α : ℝ}
    {d : ℕ → LinearData P V H} {g : ℕ → Geometry} {copy : ℕ → Frequency}
    {L : ℕ → ℝ} {W : ℕ → ℝ → ℝ} (h : CopyControl s α d g copy L W)
    (hL : ∀ n, 0 < L n) :
    WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α
      (fun n => (d n).copySolve (g n) (hL n).le (copy n)) :=
  copySolve_waveClass s α d g copy L h.errorRate hL W h.rate h.envelope_pos h.envelope_deriv
    h.open_slow h.domain h.coefficient_smooth h.forcingMap_smooth h.source_smooth h.current_slot
    h.constant_ge_one h.errorRate_nonneg h.length_bound h.exponential_bound h.coordinate_bound
      h.energy h.input_jets

end ControlData

section CopyEquation

open CommonCoverSolve TorusInverse

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Direction of increasing native slot time in common coordinates. -/
noncomputable def slotDirection (g : Geometry) : Plane :=
  (coverPower g.gap).symm (g.basis (0, 1))

theorem path_hasDerivAt (g : Geometry) (k : Frequency) (Y : Plane) (s : ℝ) :
    HasDerivAt (g.path k Y) (slotDirection g) s := by
  have he : g.path k Y = fun t => Y + (t - (g.coordinates k Y).2) • slotDirection g := by
    funext t
    rw [g.path_eq_shift]
    simp only [slotDirection, map_smul]
  rw [he]
  simpa only [one_smul, id_eq] using
    (((hasDerivAt_id s).sub_const (g.coordinates k Y).2).smul_const (slotDirection g)).const_add Y

/-- Differentiation of the actual reanchored copy solve is differentiation
along the fixed common-coordinate slot vector. -/
theorem along_copySolve (d : LinearData P V H) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane) (heta : (g.coordinates k Y).2 ∈ Ioo a b) :
    HarmonicCalculus.along (fun _ => ((0 : P), slotDirection g)) (d.copySolve g hab k) (p, Y) =
      d.coefficient (p, g.coordinates k Y) (d.copySolve g hab k (p, Y)) +
        d.forcingMap (p, g.coordinates k Y) (d.source (p, Y)) := by
  let t := (g.coordinates k Y).2
  have hpath : HasDerivAt (fun s => (p, g.path k Y s)) ((0 : P), slotDirection g) t :=
    (hasDerivAt_const t p).prodMk (path_hasDerivAt g k Y t)
  have hcopy : DifferentiableAt ℝ (d.copySolve g hab k) (p, Y) :=
    (d.copySolve_contDiffAt g hab hU k hA hB hf (p := (p, Y)) hp heta).differentiableAt (by simp)
  have hc : HasFDerivAt (d.copySolve g hab k)
      (fderiv ℝ (d.copySolve g hab k) (p, Y)) (p, g.path k Y t) := by
    simpa only [t, g.path_current] using hcopy.hasFDerivAt
  have hd : HasDerivAt (fun s => d.copySolve g hab k (p, g.path k Y s))
      (fderiv ℝ (d.copySolve g hab k) (p, Y) ((0 : P), slotDirection g)) t :=
    HasFDerivAt.comp_hasDerivAt (l := d.copySolve g hab k)
      (l' := fderiv ℝ (d.copySolve g hab k) (p, Y))
      (f := fun s => (p, g.path k Y s)) t hc hpath
  have hs := d.copySolve_alongPath_hasDerivAt g hab k hA.continuousOn hB.continuousOn
    hf.continuousOn hp Y ⟨t, heta.1.le, heta.2.le⟩
  have he := hd.unique hs
  simpa only [HarmonicCalculus.along, LinearData.coefficientAlong, LinearData.forcingAlong,
    t, g.path_current, Prod.mk.eta] using he

noncomputable def nativePoint (g : Geometry) (k : Frequency) (p : P × Plane) : P × Plane :=
  (p.1, g.coordinates k p.2)

/-- The pressure coefficient is constructed from the solved tangent field,
the actual normal motion, and the source at the current common point. -/
noncomputable def copyPressureReal (t : TangentData P H) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) (p : P × Plane) : ℝ :=
  TangentProjection.pressureCoefficient (t.normal (nativePoint g k p))
    (t.normalDot (nativePoint g k p)) (t.linearData.copySolve g hab k p)
    (t.action (nativePoint g k p) (t.linearData.copySolve g hab k p)) (t.source p)

noncomputable def copyPressure (t : TangentData P H) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) (frequency : ℝ) (p : P × Plane) : ℂ :=
  Complex.I * (copyPressureReal t g hab k p : ℂ) / (frequency : ℂ)

/-- Exact pressure cancellation for the constructed copy solution. This
equation is derived from the ODE; it is not an assumption on an output. -/
theorem copySolve_pressure_balance (t : TangentData P H) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ t.linearData.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ t.source (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane) (heta : (g.coordinates k Y).2 ∈ Ioo a b) :
    HarmonicCalculus.along (fun _ => ((0 : P), slotDirection g))
        (t.linearData.copySolve g hab k) (p, Y) +
      t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y)) +
      t.damping (p, g.coordinates k Y) • t.linearData.copySolve g hab k (p, Y) -
      copyPressureReal t g hab k (p, Y) • t.normal (p, g.coordinates k Y) = -t.source (p, Y) := by
  rw [along_copySolve t.linearData g hab hU k hA hB hf hp Y heta]
  simp only [show t.linearData.source = t.source from rfl]
  have he : t.linearData.coefficient (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y))
    +
      t.linearData.forcingMap (p, g.coordinates k Y) (t.source (p, Y)) =
      TangentProjection.projectedRhs (t.normal (p, g.coordinates k Y))
        (t.normalDot (p, g.coordinates k Y)) (t.linearData.copySolve g hab k (p, Y))
        (t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y)))
        (t.source (p, Y)) (t.damping (p, g.coordinates k Y)) := by
    simp only [TangentData.linearData, negativeTangentProjection_apply,
      ← sub_eq_add_neg, TangentODE.projectedOperator_apply]
  rw [he]
  exact TangentProjection.pressure_cancellation _ _ _ _ _ _

end CopyEquation

section WeightedPressure

open WeightedClasses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : StripData E} {w : ℕ → E → ℝ} {α : ℝ}

/-- The epsilon power retained in a constructed envelope is exactly the
exponent in the manuscript's all-jet class. -/
theorem envelopeJets_memClass {f : ℕ → E → ProblemStatement.Space}
    (hf : EnvelopeJets (PrimaryPulseBounds.phaseDomain s)
      (fun n x => s.epsilon n ^ α * w n x) f)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) : MemClass s w α f := by
  have hg := hf.memClass s (fun _ => rfl) (fun _ => rfl)
  refine ⟨hw, hg.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hg.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  convert! hb n x hx j hj using 1
  simp only [majorant, Real.rpow_zero]
  ring

theorem real_inner_class {u v : ℕ → E → ProblemStatement.Space}
    (hu : UnweightedClass s 0 u) (hv : MemClass s w α v) :
    MemClass s w α (fun n x => ⟪u n x, v n x⟫_ℝ) := by
  have h := hu.bilinear hv (innerSL ℝ)
  simp only [one_mul, zero_add] at h
  exact h

/-- Actual normal, normal-motion, action, and source jets give the pressure
numerator and its inverse-normal normalization. -/
theorem pressureCoefficient_class
    {N Ndot a f : ℕ → E → ProblemStatement.Space}
    {A : ℕ → E → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) N)
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    (ha : MemClass s w α a) (hf : MemClass s w α f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    MemClass s w α (fun n x => TangentProjection.pressureCoefficient
      (N n x) (Ndot n x) (a n x) (A n x (a n x)) (f n x)) := by
  have hNu := CurlClassBounds.polynomialJets_unweighted hN
  have hAa : MemClass s w α (fun n x => A n x (a n x)) := by
    have h := hA.bilinear ha (ContinuousLinearMap.apply ℝ ProblemStatement.Space).flip
    simp only [one_mul, zero_add] at h
    exact h
  have hnum := (LinearWaveBounds.class_sub (real_inner_class hNu hAa)
    (real_inner_class hNdot ha)).add (real_inner_class hNu hf)
  have hi := CurlClassBounds.normalInverse_unweighted hN hb hlower hupper
  have hh := hi.mul hnum
  simpa only [one_mul, mul_one, zero_add, TangentProjection.pressureCoefficient,
    real_inner_self_eq_norm_sq, div_eq_mul_inv, mul_comm] using hh

/-- Multiplication by the actual inverse carrier supplies the half-power
gain in the pressure; all derivatives are still the actual derivatives. -/
theorem pressure_class
    {N Ndot a f : ℕ → E → ProblemStatement.Space}
    {A : ℕ → E → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) N)
    (hNdot : UnweightedClass s 0 Ndot) (hA : UnweightedClass s 0 A)
    (ha : MemClass s w α a) (hf : MemClass s w α f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)
    {frequency : ℕ → ℝ} (hfreq : BandBound s (1 / 2) (fun n => 1 / frequency n)) :
    MemClass s w (α + 1 / 2) (fun n x => Complex.I *
      (TangentProjection.pressureCoefficient (N n x) (Ndot n x) (a n x)
        (A n x (a n x)) (f n x) : ℂ) / (frequency n : ℂ)) := by
  have hpc := (pressureCoefficient_class hN hNdot hA ha hf hb hlower hupper).map Complex.ofRealCLM
  have hh := (LinearWaveBounds.constant_complex_mul hpc Complex.I).band_smul hfreq
  simpa only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, one_div,
    div_eq_mul_inv, mul_comm, mul_one, Complex.ofReal_inv, Complex.ofRealCLM_apply] using hh

end WeightedPressure

section PrincipalCancellation

open HarmonicCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def projectedPressure (frequency : ℝ)
    (N Ndot u action source : E → ProblemStatement.Space) (x : E) : ℂ :=
  Complex.I * (TangentProjection.pressureCoefficient
    (N x) (Ndot x) (u x) (action x) (source x) : ℂ) / (frequency : ℂ)

/-- The actual projected directional equation implies the exact principal
PDE cancellation. It works with any initial value and therefore also with
the nonzero homogeneous primary seed. -/
theorem principal_eq_neg_source_of_projected
    (ε frequency : ℝ) (hfrequency : frequency ≠ 0)
    (R F G Φ : E → ℝ) (Vr Vθ Vz Vf : E → E)
    (u Ndot action source : E → ProblemStatement.Space) {x : E}
    (hu : DifferentiableAt ℝ u x)
    (hdu : along Vf u x = TangentProjection.projectedRhs
      (phaseNormal R Vr Vθ Vz Φ x) (Ndot x) (u x) (action x) (source x)
      (ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2))
    (haction : CurlClassBounds.complexify (action x) =
      LinearWaveResidual.shear R F G Vr (fun y => CurlClassBounds.complexify (u y)) x) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ
      (fun y => CurlClassBounds.complexify (u y))
      (projectedPressure frequency (phaseNormal R Vr Vθ Vz Φ) Ndot u action source) x =
      -CurlClassBounds.complexify (source x) := by
  let N := phaseNormal R Vr Vθ Vz Φ x
  let c := TangentProjection.pressureCoefficient N (Ndot x) (u x) (action x) (source x)
  have hb := TangentProjection.pressure_cancellation N (Ndot x) (u x) (action x)
    (source x) (ε * frequency ^ 2 * ‖N‖ ^ 2)
  rw [← hdu] at hb
  have hp := TangentProjection.complex_pressure_sign (c : ℂ) (frequency : ℂ)
    (Complex.ofReal_ne_zero.mpr hfrequency)
  ext i
  have hi := congrArg (fun v => CurlClassBounds.complexify v i) hb
  simp only [ CurlClassBounds.complexify_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] at hi
  have hd := LinearWaveResidual.along_map
    ((Complex.ofRealCLM).comp (EuclideanSpace.proj i)) Vf hu
  have ha := congrFun haction i
  change (action x i : ℂ) = _ at ha
  change along Vf (fun y => (u y i : ℂ)) x = _ at hd
  simp only [LinearWaveResidual.principal, CurlClassBounds.complexify_apply, Pi.neg_apply]
  rw [hd, ← ha]
  have hp' : phaseFactor frequency * (N i : ℂ) *
      projectedPressure frequency (phaseNormal R Vr Vθ Vz Φ) Ndot u action source x =
      -(c : ℂ) * (N i : ℂ) := by
    calc
      _ = ((Complex.I * (frequency : ℂ)) * (Complex.I * (c : ℂ) / (frequency : ℂ))) *
          (N i : ℂ) := by
        simp only [phaseFactor, projectedPressure, N, c]
        ring
      _ = _ := by rw [hp]
  change _ + _ + _ + phaseFactor frequency * (N i : ℂ) * _ = _
  rw [hp']
  simp only [Complex.ofReal_mul, sub_eq_add_neg, neg_mul, c, N] at hi ⊢
  exact hi

end PrincipalCancellation

section ActualCopyWave

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def copyVelocity (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) (p : P × Plane) : ComplexVector :=
  CurlClassBounds.complexify (t.linearData.copySolve g hab k p)

theorem normalDot_complexify (N a : ProblemStatement.Space) :
    normalDot N (CurlClassBounds.complexify a) = (⟪N, a⟫_ℝ : ℂ) := by
  simp [normalDot, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- Tangency is propagated by the constructed ODE, then transferred to
the complex coefficient used in the harmonic field. -/
theorem copyVelocity_tangent (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (k : Frequency)
    (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn t.source (U ×ˢ univ)) (hδ : ContinuousOn t.damping (U ×ˢ univ))
    {p : P} (hp : p ∈ U) (Y : Plane)
    (hn0 : ∀ v ∈ Icc a b, t.normal (p, ((g.coordinates k Y).1, v)) ≠ 0)
    (hn : ∀ v ∈ Icc a b,
      HasDerivAt (fun r => t.normal (p, ((g.coordinates k Y).1, r)))
        (t.normalDot (p, ((g.coordinates k Y).1, v))) v)
    (heta : (g.coordinates k Y).2 ∈ Icc a b) :
    normalDot (t.normal (p, g.coordinates k Y)) (copyVelocity t g hab k (p, Y)) = 0 := by
  rw [copyVelocity, normalDot_complexify,
    t.copySolve_tangent g hab k hA hB hf hδ hp Y hn0 hn heta]
  rfl

/-- The pressure in `copyPressure` cancels the actual principal operator
of the copy wave. The three matching hypotheses identify only primitive
normal, damping, and base-action data with the displayed physical operator. -/
theorem copySolve_principal (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (hU : IsOpen U) (k : Frequency)
    (hA : ContDiffOn ℝ ∞ t.linearData.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ t.source (U ×ˢ univ))
    (ε frequency : ℝ) (hfrequency : frequency ≠ 0)
    (R F G Φ : P × Plane → ℝ) (Vr Vθ Vz : P × Plane → P × Plane)
    {p : P} (hp : p ∈ U) (Y : Plane) (heta : (g.coordinates k Y).2 ∈ Ioo a b)
    (hN : phaseNormal R Vr Vθ Vz Φ (p, Y) = t.normal (p, g.coordinates k Y))
    (hδ : t.damping (p, g.coordinates k Y) =
      ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2)
    (hK : CurlClassBounds.complexify
        (t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y))) =
      LinearWaveResidual.shear R F G Vr (copyVelocity t g hab k) (p, Y)) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz
      (fun _ => ((0 : P), slotDirection g)) Φ (copyVelocity t g hab k)
      (copyPressure t g hab k frequency) (p, Y) = -CurlClassBounds.complexify (t.source (p, Y)) :=
        by
  have hu : DifferentiableAt ℝ (t.linearData.copySolve g hab k) (p, Y) :=
    (t.linearData.copySolve_contDiffAt g hab hU k hA hB hf (p := (p, Y)) hp heta).differentiableAt
      (by simp)
  have hd := along_copySolve t.linearData g hab hU k hA hB hf hp Y heta
  simp only [TangentData.linearData, negativeTangentProjection_apply,
    ← sub_eq_add_neg, TangentODE.projectedOperator_apply] at hd
  have hdu : along (fun _ => ((0 : P), slotDirection g)) (t.linearData.copySolve g hab k) (p, Y) =
      TangentProjection.projectedRhs (phaseNormal R Vr Vθ Vz Φ (p, Y))
        (t.normalDot (p, g.coordinates k Y)) (t.linearData.copySolve g hab k (p, Y))
        (t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y)))
        (t.source (p, Y)) (ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2) := by
    rw [← hδ, hN]
    exact hd
  have hh := principal_eq_neg_source_of_projected ε frequency hfrequency R F G Φ Vr Vθ Vz
    (fun _ => ((0 : P), slotDirection g)) (t.linearData.copySolve g hab k)
    (fun z => t.normalDot (nativePoint g k z))
    (fun z => t.action (nativePoint g k z) (t.linearData.copySolve g hab k z)) t.source hu hdu hK
  ext i
  have hi := congrFun hh i
  simp only [LinearWaveResidual.principal, projectedPressure, copyPressure, copyPressureReal,
    copyVelocity, nativePoint, hN, Pi.neg_apply] at hi ⊢
  exact hi

/-- The coefficient family to which the cutoff and exact-curl construction
is applied; neither velocity nor pressure is supplied as an output input. -/
noncomputable def copyCoefficients (base : LinearWaveBounds.WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (g : ℕ → Geometry)
    (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) :
    LinearWaveBounds.WaveCoefficients (P × Plane) :=
  { base with
    amplitude := fun n => copyVelocity (t n) (g n) (hL n).le (copy n)
    pressure := fun n => copyPressure (t n) (g n) (hL n).le (copy n) (base.frequency n) }

theorem copyVelocity_class {s : StripData (P × Plane)} {W : ℕ → P × Plane → ℝ} {α : ℝ}
    {t : ℕ → TangentData P ProblemStatement.Space} {g : ℕ → Geometry}
    {copy : ℕ → Frequency} {L : ℕ → ℝ} {hL : ∀ n, 0 < L n}
    (hu : WaveClass s W α (fun n => (t n).linearData.copySolve (g n) (hL n).le (copy n))) :
    WaveClass s W α (fun n => copyVelocity (t n) (g n) (hL n).le (copy n)) :=
  hu.map CurlClassBounds.complexify

theorem copyPressure_class {s : StripData (P × Plane)} {W : ℕ → P × Plane → ℝ} {α : ℝ}
    {t : ℕ → TangentData P ProblemStatement.Space} {g : ℕ → Geometry}
    {copy : ℕ → Frequency} {L : ℕ → ℝ} {hL : ∀ n, 0 < L n}
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hu : WaveClass s W α (fun n => (t n).linearData.copySolve (g n) (hL n).le (copy n)))
    (hf : WaveClass s W α (fun n => (t n).source))
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    {frequency : ℕ → ℝ} (hfreq : BandBound s (1 / 2) (fun n => 1 / frequency n)) :
    WaveClass s W (α + 1 / 2) (fun n => copyPressure (t n) (g n) (hL n).le (copy n) (frequency n))
      :=
  pressure_class hN hNdot hA hu hf hb hlower hupper hfreq

end ActualCopyWave

section ModalConstruction

open PrimaryODE

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The explicit source projection in the two-dimensional moving frame. -/
noncomputable def frameForcingLinear (d : FrameData Q) (z : Q × ℝ) : PrimaryODE.Space →L[ℝ]
  PrimaryODE.State :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => d.forcing (fun _ => f) z
    map_add' := by
      intro f g
      ext i
      fin_cases i <;>
        simp [FrameData.forcing, FrameData.forceX, FrameData.forceY, inner_add_right,
          MovingFrameODE.tail_add] <;> ring
    map_smul' := by
      intro c f
      ext i
      fin_cases i <;>
        simp [FrameData.forcing, FrameData.forceX, FrameData.forceY,
          inner_smul_right, MovingFrameODE.tail_smul] <;> ring }

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
@[simp] theorem frameForcingLinear_apply (d : FrameData Q) (f : Q × ℝ → PrimaryODE.Space) (z : Q ×
  ℝ) :
    frameForcingLinear d z (f z) = d.forcing f z := rfl

omit [NormedAddCommGroup Q] [NormedSpace ℝ Q] in
theorem forcing_eq_columns (d : FrameData Q) (f : Q × ℝ → PrimaryODE.Space) (z : Q × ℝ) :
    d.forcing f z = ∑ i : Fin 3, f z i • d.forcing (fun _ => ProblemStatement.coordinateVector i) z
      := by
  have hsum : (∑ i : Fin 3, f z i • ProblemStatement.coordinateVector i) = f z := by
    ext j
    fin_cases j <;> simp [ProblemStatement.coordinateVector, Fin.sum_univ_three]
  have hh := congrArg (frameForcingLinear d z) hsum
  simp only [map_sum, map_smul, frameForcingLinear_apply] at hh
  exact hh.symm

variable {ι : Type*}

/-- The actual moving-frame source projection preserves the entire source
envelope, including its small prefactor. -/
theorem frame_forcing_envelope_jets
    {D : PhaseJetBounds.Domain ι (Q × ℝ)} {d : ι → FrameData Q}
    (hd : PhaseJetBounds.FrameJets D d) {w : ι → Q × ℝ → ℝ} {f : ι → Q × ℝ → PrimaryODE.Space}
    (hf : EnvelopeJets D w f) : EnvelopeJets D w (fun i => (d i).forcing (f i)) := by
  have hc (j : Fin 3) : PhaseJetBounds.PolynomialJets D
      (fun i => (d i).forcing (fun _ => ProblemStatement.coordinateVector j)) :=
    hd.forcing (PhaseJetBounds.PolynomialJets.const_fixed _)
  have h (j : Fin 3) := (hf.map (EuclideanSpace.proj j)).smul_polynomial (hc j)
  apply (h 0 |>.add (h 1) |>.add (h 2)).congr
  intro i z hz
  rw [forcing_eq_columns, Fin.sum_univ_three]
  rfl

/-- A forced family in the genuine modal coordinates. The energy estimate
comes from the four explicit modal errors and nonnegative viscosity, rather
than an energy hypothesis about the ambient projected operator. -/
theorem forced_modal_family_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    (d : ι → FrameData Q) (hd : PhaseJetBounds.FrameJets (productDomain D V hV) d)
    (harmonic : ℤ) (hharmonic : harmonic ≠ 0)
    (W rate referenceDamping : ι → ℝ → ℝ) (hW : ∀ i t, 0 < W i t)
    (hdW : ∀ i t, HasDerivAt (W i) (rate i t * W i t) t)
    (w : ι → Q → ℝ) (hw : ∀ i p, p ∈ D.carrier i → 0 ≤ w i p)
    (f : ι → Q × ℝ → PrimaryODE.Space)
    (hf : EnvelopeJets (productDomain D V hV) (fun i z => w i z.1 * W i z.2) f)
    {K C E : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hslot : ∀ i, L i ≤ K * D.scale i)
    (href : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      rate i v = (d i).eigenvalue (p, v) - referenceDamping i v)
    (hlam : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), 0 ≤ (d i).eigenvalue (p, v))
    (hvisc : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), 0 ≤ (d i).viscosity (p, v))
    (hviscError : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      referenceDamping i v - E / D.scale i ≤ (d i).viscosity (p, v))
    (herror : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      |(d i).error11 (p, v)| ≤ C / D.scale i ∧ |(d i).error12 (p, v)| ≤ C / D.scale i ∧
      |(d i).error21 (p, v)| ≤ C / D.scale i ∧ |(d i).error22 (p, v)| ≤ C / D.scale i) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => w i z.1 * W i z.2)
      (fun i z => solution (hL i).le (d i) harmonic (fun _ => 0) (f i) z.1 z.2) := by
  let μ := fun i => (E + 4 * C) / D.scale i
  let K' := K + Real.exp ((E + 4 * C) * K) + 1
  have hKK' : K ≤ K' := by dsimp [K']; linarith [Real.exp_pos ((E + 4 * C) * K)]
  have hK' : 1 ≤ K' := hK.trans hKK'
  have hμ : ∀ i, 0 ≤ μ i := fun i => div_nonneg (by positivity) (zero_le_one.trans (D.one_le_scale
    i))
  have hExp : ∀ i, Real.exp (μ i * L i) ≤ K' := by
    intro i
    have hs : 0 < D.scale i := lt_of_lt_of_le zero_lt_one (D.one_le_scale i)
    have hr : L i / D.scale i ≤ K := (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hslot i)
    have hh : μ i * L i ≤ (E + 4 * C) * K := by
      dsimp [μ]
      calc
        _ = (E + 4 * C) * (L i / D.scale i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
    exact (Real.exp_le_exp.mpr hh).trans (by dsimp [K']; linarith)
  have henergy : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), ∀ x : PrimaryODE.State,
      ⟪x, (d i).coefficient harmonic (p, v) x⟫_ℝ ≤ (rate i v + μ i) * ‖x‖ ^ 2 := by
    intro i p hp v hv x
    rw [href i p hp v hv]
    exact (d i).energy_bound (p, v) hharmonic (hlam i p hp v hv) (hvisc i p hp v hv)
      (hviscError i p hp v hv) (herror i p hp v hv) x
  have hs := forced_family_envelope_jets D V hV L μ hL hI
    (fun i => (d i).coefficient harmonic) (hd.coefficient harmonic) W rate hW hdW w hw
    (fun i => (d i).forcing (f i)) (frame_forcing_envelope_jets hd hf) hK' hμ
    (fun i => (hslot i).trans (mul_le_mul_of_nonneg_right hKK' (zero_le_one.trans (D.one_le_scale
      i))))
    hExp henergy
  apply hs.congr
  intro i z hz
  exact JointODE.reparamSolution_eq_actualSolution (hL i).le _ _ _
    (((hd.smoothOn i).coefficient harmonic).continuousOn.mono (prod_mono Subset.rfl (hI i)))
    (((hd.smoothOn i).forcing (hf.smooth i)).continuousOn.mono (prod_mono Subset.rfl (hI i)))
    ⟨hz.1, hz.2.1.le, hz.2.2.le⟩

/-- The same forced estimate after actual moving-frame reconstruction. The
reference energy bound is used only in the modal two-dimensional state. -/
theorem forced_ambient_family_envelope_jets
    (D : PhaseJetBounds.Domain ι Q) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) (hI : ∀ i, Icc 0 (L i) ⊆ V i)
    (d : ι → FrameData Q) (hd : PhaseJetBounds.FrameJets (productDomain D V hV) d)
    (harmonic : ℤ) (hharmonic : harmonic ≠ 0)
    (W rate referenceDamping : ι → ℝ → ℝ) (hW : ∀ i t, 0 < W i t)
    (hdW : ∀ i t, HasDerivAt (W i) (rate i t * W i t) t)
    (w : ι → Q → ℝ) (hw : ∀ i p, p ∈ D.carrier i → 0 ≤ w i p)
    (f : ι → Q × ℝ → PrimaryODE.Space)
    (hf : EnvelopeJets (productDomain D V hV) (fun i z => w i z.1 * W i z.2) f)
    {K C E : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hslot : ∀ i, L i ≤ K * D.scale i)
    (href : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      rate i v = (d i).eigenvalue (p, v) - referenceDamping i v)
    (hlam : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), 0 ≤ (d i).eigenvalue (p, v))
    (hvisc : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i), 0 ≤ (d i).viscosity (p, v))
    (hviscError : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      referenceDamping i v - E / D.scale i ≤ (d i).viscosity (p, v))
    (herror : ∀ i p, p ∈ D.carrier i → ∀ v ∈ Icc 0 (L i),
      |(d i).error11 (p, v)| ≤ C / D.scale i ∧ |(d i).error12 (p, v)| ≤ C / D.scale i ∧
      |(d i).error21 (p, v)| ≤ C / D.scale i ∧ |(d i).error22 (p, v)| ≤ C / D.scale i) :
    EnvelopeJets (productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
      (fun i z => w i z.1 * W i z.2)
      (fun i z => ambientSolution (hL i).le (d i) harmonic (fun _ => 0) (f i) z.1 z.2) := by
  have hm := forced_modal_family_envelope_jets D V hV L hL hI d hd harmonic hharmonic
    W rate referenceDamping hW hdW w hw f hf hK hC hE hslot href hlam hvisc hviscError herror
  apply ambient_envelope_jets hm
  intro j
  have hc := EnvelopeJets.of_polynomial (synthesisColumn_polynomial hd j)
  have hcr := hc.restrict (D' := productDomain D (fun i => Ioo 0 (L i)) (fun _ => isOpen_Ioo))
    (fun _ => rfl) (fun i z hz => ⟨hz.1, hI i ⟨hz.2.1.le, hz.2.2.le⟩⟩)
  exact hcr.to_polynomial (fun _ _ _ => le_rfl)

end ModalConstruction

section ModalJetTransfer

open PrimaryODE

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

noncomputable def ambientJetConstant (N : ℕ) : ℝ :=
  2 ^ N * (‖(EuclideanSpace.proj (0 : Fin 2) : PrimaryODE.State →L[ℝ] ℝ)‖ +
    ‖(EuclideanSpace.proj (1 : Fin 2) : PrimaryODE.State →L[ℝ] ℝ)‖)

/-- Finite full-jet bound for actual reconstruction, suitable for a source
majorant whose edge exponent depends on the derivative order. -/
theorem ambient_jet_bound (d : FrameData Q) {T : Set (Q × ℝ)} (hT : IsOpen T)
    {u : Q × ℝ → PrimaryODE.State} (hu : ContDiffOn ℝ ∞ u T)
    (hc : ∀ i : Fin 2, ContDiffOn ℝ ∞ (synthesisColumn d i) T)
    {x : Q × ℝ} (hx : x ∈ T) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {N j : ℕ} (hj : j ≤ N)
    (huj : ∀ k ≤ N, ‖iteratedFDeriv ℝ k u x‖ ≤ A)
    (hcj : ∀ i : Fin 2, ∀ k ≤ N, ‖iteratedFDeriv ℝ k (synthesisColumn d i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => d.ambient y (u y)) x‖ ≤ ambientJetConstant N * A * B := by
  have hcomp (i : Fin 2) : ContDiffOn ℝ ∞ (fun y => u y i) T :=
    (EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ).contDiff.comp_contDiffOn hu
  have hcompj (i : Fin 2) (k : ℕ) (hk : k ≤ N) :
      ‖iteratedFDeriv ℝ k (fun y => u y i) x‖ ≤ ‖(EuclideanSpace.proj i : PrimaryODE.State →L[ℝ]
        ℝ)‖ * A := by
    change ‖iteratedFDeriv ℝ k ((EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ) ∘ u) x‖ ≤ _
    rw [(EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ).iteratedFDeriv_comp_left (hu.contDiffAt
      (hT.mem_nhds hx)) (nat_le_infty k)]
    exact ((EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ).norm_compContinuousMultilinearMap_le
      _).trans
      (mul_le_mul_of_nonneg_left (huj k hk) (norm_nonneg _))
  have hb (i : Fin 2) := smul_jet_bound hT (hcomp i) (hc i) hx hj
    (mul_nonneg (norm_nonneg _) hA) hB (hcompj i) (hcj i)
  have he : (fun y => d.ambient y (u y)) = fun y =>
      u y 0 • synthesisColumn d 0 y + u y 1 • synthesisColumn d 1 y := by
    funext y
    exact ambient_eq_synthesis d y (u y)
  rw [he]
  change ‖iteratedFDeriv ℝ j ((fun y => u y 0 • synthesisColumn d 0 y) +
    (fun y => u y 1 • synthesisColumn d 1 y)) x‖ ≤ _
  rw [iteratedFDeriv_add_apply
    (f := fun y => u y 0 • synthesisColumn d 0 y)
    (g := fun y => u y 1 • synthesisColumn d 1 y)
    (((hcomp 0).smul (hc 0)).contDiffAt (hT.mem_nhds hx) |>.of_le (nat_le_infty j))
    (((hcomp 1).smul (hc 1)).contDiffAt (hT.mem_nhds hx) |>.of_le (nat_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => u y 0 • synthesisColumn d 0 y) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => u y 1 • synthesisColumn d 1 y) x‖ := norm_add_le _ _
    _ ≤ 2 ^ N * (‖(EuclideanSpace.proj (0 : Fin 2) : PrimaryODE.State →L[ℝ] ℝ)‖ * A) * B +
        2 ^ N * (‖(EuclideanSpace.proj (1 : Fin 2) : PrimaryODE.State →L[ℝ] ℝ)‖ * A) * B :=
          add_le_add (hb 0) (hb 1)
    _ = _ := by unfold ambientJetConstant; ring

end ModalJetTransfer

section ActualModalCopy

open CommonCoverSolve TorusInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Full current-copy derivatives from the modal ODE and genuine frame
reconstruction. The reference-energy hypothesis concerns the actual
two-dimensional modal coefficient, never the ambient projected operator. -/
theorem copySolve_jet_bound_from_modal
    (d : PrimaryODE.FrameData (P × ℝ)) (t : TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : Geometry) (copy : Frequency)
    {L S K μ w : ℝ} (hL : 0 < L) (hS : 1 ≤ S) (hK : 1 ≤ K) (hμ : 0 ≤ μ) (hw : 0 ≤ w)
    (hslot : L ≤ K * S) (hExp : Real.exp (μ * L) ≤ K)
    (Ω : Set (P × Plane)) (I : Set ℝ) (hΩ : IsOpen Ω) (hI : IsOpen I) (hLI : Icc 0 L ⊆ I)
    (bridge : PrimaryCopyBridge.Inputs d t harmonic g copy Ω 0 L)
    (hA : ContDiffOn ℝ ∞ ((PrimaryCopyBridge.copyFrame d g copy).coefficient harmonic) (Ω ×ˢ I))
    (hf : ContDiffOn ℝ ∞ ((PrimaryCopyBridge.copyFrame d g copy).forcing
      (PrimaryCopyBridge.copySource t.source g copy)) (Ω ×ˢ I))
    (hc : ∀ i : Fin 2, ContDiffOn ℝ ∞ (synthesisColumn (PrimaryCopyBridge.copyFrame d g copy) i) (Ω
      ×ˢ I))
    (W rate : ℝ → ℝ) (hW : ∀ v, 0 < W v) (hdW : ∀ v, HasDerivAt W (rate v * W v) v)
    {p : P × Plane} (hp : p ∈ Ω) (heta : (g.coordinates copy p.2).2 ∈ Ioo 0 L)
    (henergy : ∀ v ∈ Icc 0 L, ∀ x : PrimaryODE.State,
      ⟪x, (PrimaryCopyBridge.copyFrame d g copy).coefficient harmonic (p, v) x⟫_ℝ ≤
        (rate v + μ) * ‖x‖ ^ 2)
    (m N : ℕ)
    (hAj : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame d g copy).coefficient harmonic) (p, v)‖ ≤ K
        * S ^ m)
    (hfj : ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame d g copy).forcing
        (PrimaryCopyBridge.copySource t.source g copy)) (p, v)‖ ≤ w * K * S ^ m * W v)
    (hcj : ∀ i : Fin 2, ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j (synthesisColumn (PrimaryCopyBridge.copyFrame d g copy) i) (p, v)‖ ≤ K *
        S ^ m)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (t.linearData.copySolve g hL.le copy) p‖ ≤
      ambientJetConstant N *
        (w * ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (N + 1) *
          S ^ ((m + 2) * (N + 1)) * W (g.coordinates copy p.2).2) *
        (K * S ^ m) * CommonCoverClass.argumentCost g ^ j := by
  let frame := PrimaryCopyBridge.copyFrame d g copy
  let A := frame.coefficient harmonic
  let f := frame.forcing (PrimaryCopyBridge.copySource t.source g copy)
  let u := JointODE.reparamSolution 0 A (fun _ => 0) f
  let T := Ω ×ˢ Ioo 0 L
  have hT : IsOpen T := hΩ.prod isOpen_Ioo
  have hus : ContDiffOn ℝ ∞ u T := by
    intro z hz
    exact (JointODE.reparamSolution_contDiffAt Ω I hΩ hI hLI A (fun _ => 0) f hA contDiffOn_const hf
      ⟨hz.1, hz.2.1.le, hz.2.2.le⟩).contDiffWithinAt
  have hcols (i : Fin 2) : ContDiffOn ℝ ∞ (synthesisColumn frame i) T :=
    (hc i).mono (prod_mono Subset.rfl (fun _ hv => hLI ⟨hv.1.le, hv.2.le⟩))
  have hcomp (i : Fin 2) : ContDiffOn ℝ ∞ (fun y => u y i) T :=
    (EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ).contDiff.comp_contDiffOn hus
  have hps : ContDiffOn ℝ ∞ (PrimaryCopyBridge.reparamPath d t harmonic g copy 0) T := by
    apply (((hcomp 0).smul (hcols 0)).add ((hcomp 1).smul (hcols 1))).congr
    intro z hz
    exact ambient_eq_synthesis frame z (u z)
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  let M := w * B ^ (N + 1) * S ^ ((m + 2) * (N + 1)) * W (g.coordinates copy p.2).2
  have hM : 0 ≤ M := by have := hW (g.coordinates copy p.2).2; dsimp [M]; positivity
  have huj : ∀ k ≤ N, ‖iteratedFDeriv ℝ k u (p, (g.coordinates copy p.2).2)‖ ≤ M := by
    intro k hk
    have hh := forced_joint_jet_bound hL hS hK hμ hw hslot hExp Ω I hΩ hI hLI A hA W rate hW hdW
      f hf hp ⟨heta.1.le, heta.2.le⟩ henergy m N hAj hfj k hk
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (hW _).le
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.add_le_add_right hk 1))
      hw)
      (pow_le_pow_right₀ hS (Nat.mul_le_mul_left _ (Nat.add_le_add_right hk 1)))
      (pow_nonneg (zero_le_one.trans hS) _) (by positivity)
  have hamb := ambient_jet_bound frame hT hus hcols (show (p, (g.coordinates copy p.2).2) ∈ T from
    ⟨hp, heta⟩)
    hM (show 0 ≤ K * S ^ m by positivity) hj huj (fun i k hk => hcj i k hk _ ⟨heta.1.le, heta.2.le⟩)
  have haff := norm_jet_comp_affine hT hps (CommonCoverClass.currentLinear P g)
    (CommonCoverClass.currentArgument (P := P) g copy 0)
    (by rw [← CommonCoverClass.currentArgument_affine]; exact ⟨hp, heta⟩) j
  simp_rw [← CommonCoverClass.currentArgument_affine] at haff
  have he := PrimaryCopyBridge.reparamCopy_iteratedFDeriv_eq d t harmonic g copy hL.le hΩ bridge
    (show p ∈ PrimaryCopyBridge.copyInterior g copy Ω 0 L from ⟨hp, heta⟩) j
  rw [← he]
  apply haff.trans
  exact mul_le_mul hamb
    (pow_le_pow_left₀ (norm_nonneg _) (CommonCoverClass.norm_currentLinear_le (P := P) g) j)
    (pow_nonneg (norm_nonneg _) _) (by unfold ambientJetConstant; positivity)

end ActualModalCopy

section ModalControl

open CommonCoverSolve TorusInverse WeightedClasses

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Joint smoothness of the actual copy solve from local modal data on a
neighborhood of the finite integration interval. -/
theorem copySolve_contDiffOn_from_modal
    (d : PrimaryODE.FrameData (P × ℝ)) (t : TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : Geometry) (copy : Frequency)
    {L : ℝ} (hL : 0 < L) {Ω : Set (P × Plane)} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hLI : Icc 0 L ⊆ I)
    (bridge : PrimaryCopyBridge.Inputs d t harmonic g copy Ω 0 L)
    (hA : ContDiffOn ℝ ∞ ((PrimaryCopyBridge.copyFrame d g copy).coefficient harmonic) (Ω ×ˢ I))
    (hf : ContDiffOn ℝ ∞ ((PrimaryCopyBridge.copyFrame d g copy).forcing
      (PrimaryCopyBridge.copySource t.source g copy)) (Ω ×ˢ I))
    (hc : ∀ i : Fin 2, ContDiffOn ℝ ∞ (synthesisColumn (PrimaryCopyBridge.copyFrame d g copy) i) (Ω
      ×ˢ I))
    (heta : ∀ p ∈ Ω, (g.coordinates copy p.2).2 ∈ Ioo 0 L) :
    ContDiffOn ℝ ∞ (t.linearData.copySolve g hL.le copy) Ω := by
  let frame := PrimaryCopyBridge.copyFrame d g copy
  let u := JointODE.reparamSolution 0 (frame.coefficient harmonic) (fun _ => 0)
    (frame.forcing (PrimaryCopyBridge.copySource t.source g copy))
  let T := Ω ×ˢ Ioo 0 L
  have hus : ContDiffOn ℝ ∞ u T := by
    intro z hz
    exact (JointODE.reparamSolution_contDiffAt Ω I hΩ hI hLI _ _ _ hA contDiffOn_const hf
      ⟨hz.1, hz.2.1.le, hz.2.2.le⟩).contDiffWithinAt
  have hcols (i : Fin 2) : ContDiffOn ℝ ∞ (synthesisColumn frame i) T :=
    (hc i).mono (prod_mono Subset.rfl (fun _ hv => hLI ⟨hv.1.le, hv.2.le⟩))
  have hcomp (i : Fin 2) : ContDiffOn ℝ ∞ (fun y => u y i) T :=
    (EuclideanSpace.proj i : PrimaryODE.State →L[ℝ] ℝ).contDiff.comp_contDiffOn hus
  have hpath : ContDiffOn ℝ ∞ (PrimaryCopyBridge.reparamPath d t harmonic g copy 0) T := by
    apply (((hcomp 0).smul (hcols 0)).add ((hcomp 1).smul (hcols 1))).congr
    intro z hz
    exact ambient_eq_synthesis frame z (u z)
  have hcurrent : ContDiff ℝ ∞ (CommonCoverClass.currentArgument (P := P) g copy) := by
    simpa only [← CommonCoverClass.currentArgument_affine] using
      (contDiff_const.add (CommonCoverClass.currentLinear P g).contDiff :
        ContDiff ℝ ∞ (fun p => CommonCoverClass.currentArgument (P := P) g copy 0 +
          CommonCoverClass.currentLinear P g p))
  have hh := hpath.comp hcurrent.contDiffOn (fun p hp => ⟨hp, heta p hp⟩)
  apply hh.congr
  intro p hp
  exact (PrimaryCopyBridge.reparamCopy_eq_copySolve d t harmonic g copy hL.le bridge hp
    ⟨(heta p hp).1.le, (heta p hp).2.le⟩).symm

/-- Input bounds for the genuine modal equation on every copy path. The
energy bound is in the two-dimensional modal state. The edge exponent in
`input_jets` may depend on the requested derivative order. -/
structure ModalCopyControl (s : StripData (P × Plane)) (α : ℝ)
    (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (t : ℕ → TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : ℕ → Geometry) (copy : ℕ → Frequency)
    (L : ℕ → ℝ) (W : ℕ → ℝ → ℝ) where
  interval : ℕ → Set ℝ
  open_interval : ∀ n, IsOpen (interval n)
  length_pos : ∀ n, 0 < L n
  contains_interval : ∀ n, Icc 0 (L n) ⊆ interval n
  bridge : ∀ n, PrimaryCopyBridge.Inputs (d n) (t n) harmonic (g n) (copy n) s.domain 0 (L n)
  coefficient_smooth : ∀ n, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).coefficient harmonic) (s.domain ×ˢ interval
      n)
  forcing_smooth : ∀ n, ContDiffOn ℝ ∞
    ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).forcing
      (PrimaryCopyBridge.copySource (t n).source (g n) (copy n))) (s.domain ×ˢ interval n)
  columns_smooth : ∀ n (i : Fin 2), ContDiffOn ℝ ∞
    (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)) i) (s.domain ×ˢ interval n)
  current_slot : ∀ n p, p ∈ s.domain → ((g n).coordinates (copy n) p.2).2 ∈ Ioo 0 (L n)
  rate : ℕ → ℝ → ℝ
  envelope_pos : ∀ n v, 0 < W n v
  envelope_deriv : ∀ n v, HasDerivAt (W n) (rate n v * W n v) v
  errorRate : ℕ → ℝ
  errorRate_nonneg : ∀ n, 0 ≤ errorRate n
  boundConstant : ℝ
  constant_ge_one : 1 ≤ boundConstant
  coordinate_power : ℕ
  length_bound : ∀ n, L n ≤ boundConstant * s.slow n
  exponential_bound : ∀ n, Real.exp (errorRate n * L n) ≤ boundConstant
  coordinate_bound : ∀ n, CommonCoverClass.argumentCost (g n) ≤ boundConstant * s.slow n ^
    coordinate_power
  energy : ∀ n p, p ∈ s.domain → ∀ v ∈ Icc 0 (L n), ∀ x : PrimaryODE.State,
    ⟪x, (PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).coefficient harmonic (p, v) x⟫_ℝ ≤
      (rate n v + errorRate n) * ‖x‖ ^ 2
  input_jets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ n p, p ∈ s.domain →
    ∀ j ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).coefficient harmonic)
          (p, v)‖ ≤ C * s.growth n p ^ m ∧
      ‖iteratedFDeriv ℝ j ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).forcing
          (PrimaryCopyBridge.copySource (t n).source (g n) (copy n))) (p, v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * C * s.growth n p ^ m * W n v ∧
      ∀ i : Fin 2, ‖iteratedFDeriv ℝ j
        (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)) i) (p, v)‖ ≤
          C * s.growth n p ^ m

/-- Local joint smoothness is obtained before any quantitative estimate. -/
theorem ModalCopyControl.contDiffOn {s : StripData (P × Plane)} {α : ℝ}
    {d : ℕ → PrimaryODE.FrameData (P × ℝ)} {t : ℕ → TangentData P ProblemStatement.Space}
    {harmonic : ℤ} {g : ℕ → Geometry} {copy : ℕ → Frequency} {L : ℕ → ℝ} {W : ℕ → ℝ → ℝ}
    (h : ModalCopyControl s α d t harmonic g copy L W) (hL : ∀ n, 0 < L n) (n : ℕ) :
    ContDiffOn ℝ ∞ ((t n).linearData.copySolve (g n) (hL n).le (copy n)) s.domain :=
  copySolve_contDiffOn_from_modal (d n) (t n) harmonic (g n) (copy n) (hL n)
    s.isOpen_domain (h.open_interval n) (h.contains_interval n) (h.bridge n)
    (h.coefficient_smooth n) (h.forcing_smooth n) (h.columns_smooth n) (h.current_slot n)

/-- The actual ambient copy solution belongs to `W_α`, with all edge losses
retained and with no ambient reference-energy assumption. -/
theorem ModalCopyControl.waveClass {s : StripData (P × Plane)} {α : ℝ}
    {d : ℕ → PrimaryODE.FrameData (P × ℝ)} {t : ℕ → TangentData P ProblemStatement.Space}
    {harmonic : ℤ} {g : ℕ → Geometry} {copy : ℕ → Frequency} {L : ℕ → ℝ} {W : ℕ → ℝ → ℝ}
    (h : ModalCopyControl s α d t harmonic g copy L W) (hL : ∀ n, 0 < L n) :
    WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α
      (fun n => (t n).linearData.copySolve (g n) (hL n).le (copy n)) := by
  refine ⟨fun n p _ => mul_nonneg (Real.sqrt_nonneg _) (h.envelope_pos n _).le, ?_, ?_⟩
  · exact h.contDiffOn hL
  intro N
  obtain ⟨C, hC, m, hm⟩ := h.input_jets N
  let K := C + h.boundConstant + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith [h.constant_ge_one]
  have hCK : C ≤ K := by dsimp [K]; linarith [h.constant_ge_one]
  have hK₀K : h.boundConstant ≤ K := by dsimp [K]; linarith
  let B := (2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (hK.trans (le_rescaleConstant N K)))
  have hconst : 0 ≤ ambientJetConstant N := by unfold ambientJetConstant; positivity
  have hK₀ : 0 ≤ h.boundConstant := zero_le_one.trans h.constant_ge_one
  refine ⟨ambientJetConstant N * B ^ (N + 1) * K * h.boundConstant ^ N,
    by positivity, (m + 2) * (N + 1) + m + h.coordinate_power * N, ?_⟩
  intro n p hp j hj
  have hG := s.one_le_growth n p
  have hG0 := s.growth_nonneg n p
  have hw : 0 ≤ s.epsilon n ^ α * Real.sqrt (s.zeta p) :=
    mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le (Real.sqrt_nonneg _)
  have hAj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ k ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).coefficient harmonic)
        (p, v)‖ ≤ K * s.growth n p ^ m := by
    intro k hk v hv
    exact (hm n p hp k hk v hv).1.trans (mul_le_mul_of_nonneg_right hCK (pow_nonneg hG0 _))
  have hfj : ∀ k ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ k ((PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)).forcing
        (PrimaryCopyBridge.copySource (t n).source (g n) (copy n))) (p, v)‖ ≤
        (s.epsilon n ^ α * Real.sqrt (s.zeta p)) * K * s.growth n p ^ m * W n v := by
    intro k hk v hv
    exact (hm n p hp k hk v hv).2.1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCK hw) (pow_nonneg hG0 _)) (h.envelope_pos n v).le)
  have hcj : ∀ i : Fin 2, ∀ k ≤ N, ∀ v ∈ Icc 0 (L n),
      ‖iteratedFDeriv ℝ k (synthesisColumn (PrimaryCopyBridge.copyFrame (d n) (g n) (copy n)) i)
        (p, v)‖ ≤ K * s.growth n p ^ m := by
    intro i k hk v hv
    exact (hm n p hp k hk v hv).2.2 i |>.trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg hG0 _))
  have hh := copySolve_jet_bound_from_modal (d n) (t n) harmonic (g n) (copy n) (hL n) hG hK
    (h.errorRate_nonneg n) hw
    ((h.length_bound n).trans (mul_le_mul hK₀K (s.slow_le_growth n p)
      (zero_le_one.trans (s.one_le_slow n)) (zero_le_one.trans hK)))
    ((h.exponential_bound n).trans hK₀K) s.domain (h.interval n) s.isOpen_domain (h.open_interval n)
    (h.contains_interval n) (h.bridge n) (h.coefficient_smooth n) (h.forcing_smooth n)
      (h.columns_smooth n)
    (W n) (h.rate n) (h.envelope_pos n) (h.envelope_deriv n) hp (h.current_slot n p hp)
    (h.energy n p hp) m N hAj hfj hcj j hj
  have hcg : CommonCoverClass.argumentCost (g n) ≤ h.boundConstant * s.growth n p ^
    h.coordinate_power :=
    (h.coordinate_bound n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n p) _)
      (zero_le_one.trans h.constant_ge_one))
  have hcp : CommonCoverClass.argumentCost (g n) ^ j ≤
      h.boundConstant ^ N * s.growth n p ^ (h.coordinate_power * N) := by
    calc
      _ ≤ (h.boundConstant * s.growth n p ^ h.coordinate_power) ^ j := pow_le_pow_left₀
        (zero_le_one.trans (CommonCoverClass.one_le_argumentCost (g n))) hcg j
      _ ≤ (h.boundConstant * s.growth n p ^ h.coordinate_power) ^ N := pow_le_pow_right₀
        (one_le_mul_of_one_le_of_one_le h.constant_ge_one (one_le_pow₀ hG)) hj
      _ = _ := by rw [mul_pow, pow_mul]
  apply hh.trans
  have hW := (h.envelope_pos n ((g n).coordinates (copy n) p.2).2).le
  calc
    _ ≤ ambientJetConstant N *
        ((s.epsilon n ^ α * Real.sqrt (s.zeta p)) * B ^ (N + 1) *
          s.growth n p ^ ((m + 2) * (N + 1)) * W n ((g n).coordinates (copy n) p.2).2) *
        (K * s.growth n p ^ m) * (h.boundConstant ^ N * s.growth n p ^ (h.coordinate_power * N)) :=
          by
      apply mul_le_mul_of_nonneg_left hcp
      exact mul_nonneg (mul_nonneg hconst (by positivity)) (by positivity)
    _ = _ := by unfold majorant; simp only [pow_add]; ring

end ModalControl

section LocalCopyEquation

open CommonCoverSolve TorusInverse HarmonicCalculus

variable {P V H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Local version of the copy derivative identity. Continuity is required
only on the actual finite paths, and joint differentiability can be supplied
by the modal reconstruction theorem. -/
theorem along_copySolve_of_path (d : LinearData P V H) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) {Ω : Set (P × Plane)}
    (hA : ContinuousOn (d.coefficientAlong g k) (Ω ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcingAlong g k) (Ω ×ˢ Icc a b))
    (p : P) (Y : Plane) (hp : (p, Y) ∈ Ω) (heta : (g.coordinates k Y).2 ∈ Icc a b)
    (hcopy : DifferentiableAt ℝ (d.copySolve g hab k) (p, Y)) :
    along (fun _ => ((0 : P), slotDirection g)) (d.copySolve g hab k) (p, Y) =
      d.coefficient (p, g.coordinates k Y) (d.copySolve g hab k (p, Y)) +
        d.forcingMap (p, g.coordinates k Y) (d.source (p, Y)) := by
  let v := (g.coordinates k Y).2
  have hpath : HasDerivAt (fun s => (p, g.path k Y s)) ((0 : P), slotDirection g) v :=
    (hasDerivAt_const v p).prodMk (path_hasDerivAt g k Y v)
  have hc : HasFDerivAt (d.copySolve g hab k)
      (fderiv ℝ (d.copySolve g hab k) (p, Y)) (p, g.path k Y v) := by
    simpa only [v, g.path_current] using hcopy.hasFDerivAt
  have hd : HasDerivAt (fun s => d.copySolve g hab k (p, g.path k Y s))
      (fderiv ℝ (d.copySolve g hab k) (p, Y) ((0 : P), slotDirection g)) v :=
    HasFDerivAt.comp_hasDerivAt (l := d.copySolve g hab k)
      (l' := fderiv ℝ (d.copySolve g hab k) (p, Y))
      (f := fun s => (p, g.path k Y s)) v hc hpath
  have hs := PrimaryCopyBridge.anchoredSolve_hasDerivAt_along d g hab k hA hf hp heta
  have hs' : HasDerivAt (fun s => d.copySolve g hab k (p, g.path k Y s))
      (d.coefficientAlong g k ((p, Y), v) (d.anchoredSolve g hab k (p, Y) v) +
        d.forcingAlong g k ((p, Y), v)) v := by
    simpa only [LinearData.copySolve_path] using hs
  simpa only [along, LinearData.coefficientAlong, LinearData.forcingAlong,
    LinearData.copySolve, v, g.path_current, Prod.mk.eta] using hd.unique hs'

/-- Principal cancellation using only continuity along finite paths and
the actual local derivative of the copy solve. -/
theorem copySolve_principal_of_path (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) {Ω : Set (P × Plane)}
    (hA : ContinuousOn (t.linearData.coefficientAlong g k) (Ω ×ˢ Icc a b))
    (hf : ContinuousOn (t.linearData.forcingAlong g k) (Ω ×ˢ Icc a b))
    (ε frequency : ℝ) (hfrequency : frequency ≠ 0)
    (R F G Φ : P × Plane → ℝ) (Vr Vθ Vz : P × Plane → P × Plane)
    (p : P) (Y : Plane) (hp : (p, Y) ∈ Ω) (heta : (g.coordinates k Y).2 ∈ Icc a b)
    (hu : DifferentiableAt ℝ (t.linearData.copySolve g hab k) (p, Y))
    (hN : phaseNormal R Vr Vθ Vz Φ (p, Y) = t.normal (p, g.coordinates k Y))
    (hδ : t.damping (p, g.coordinates k Y) =
      ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2)
    (hK : CurlClassBounds.complexify
        (t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y))) =
      LinearWaveResidual.shear R F G Vr (copyVelocity t g hab k) (p, Y)) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz
      (fun _ => ((0 : P), slotDirection g)) Φ (copyVelocity t g hab k)
      (copyPressure t g hab k frequency) (p, Y) = -CurlClassBounds.complexify (t.source (p, Y)) :=
        by
  have hd := along_copySolve_of_path t.linearData g hab k hA hf p Y hp heta hu
  simp only [TangentData.linearData, negativeTangentProjection_apply,
    ← sub_eq_add_neg, TangentODE.projectedOperator_apply] at hd
  have hdu : along (fun _ => ((0 : P), slotDirection g)) (t.linearData.copySolve g hab k) (p, Y) =
      TangentProjection.projectedRhs (phaseNormal R Vr Vθ Vz Φ (p, Y))
        (t.normalDot (p, g.coordinates k Y)) (t.linearData.copySolve g hab k (p, Y))
        (t.action (p, g.coordinates k Y) (t.linearData.copySolve g hab k (p, Y)))
        (t.source (p, Y)) (ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2) := by
    rw [← hδ, hN]
    exact hd
  have hh := principal_eq_neg_source_of_projected ε frequency hfrequency R F G Φ Vr Vθ Vz
    (fun _ => ((0 : P), slotDirection g)) (t.linearData.copySolve g hab k)
    (fun z => t.normalDot (nativePoint g k z))
    (fun z => t.action (nativePoint g k z) (t.linearData.copySolve g hab k z)) t.source hu hdu hK
  ext i
  have hi := congrFun hh i
  simp only [LinearWaveResidual.principal, projectedPressure, copyPressure, copyPressureReal,
    copyVelocity, nativePoint, hN, Pi.neg_apply] at hi ⊢
  exact hi

end LocalCopyEquation

section ModalTangency

open CommonCoverSolve TorusInverse HarmonicCalculus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
/-- Tangency of the actual copy solve follows from frame reconstruction
and uniqueness, including at both endpoints of the finite path. -/
theorem copyVelocity_tangent_of_modal
    (d : PrimaryODE.FrameData (P × ℝ)) (t : TangentData P ProblemStatement.Space)
    (harmonic : ℤ) (g : Geometry) (k : Frequency) {a b : ℝ} (hab : a ≤ b)
    {Ω : Set (P × Plane)} (bridge : PrimaryCopyBridge.Inputs d t harmonic g k Ω a b)
    {p : P × Plane} (hp : p ∈ Ω) (heta : (g.coordinates k p.2).2 ∈ Icc a b) :
    normalDot (t.normal (nativePoint g k p)) (copyVelocity t g hab k p) = 0 := by
  have ht := PrimaryCopyBridge.reconstructedPath_tangent d t harmonic g k hab bridge hp heta
  rw [PrimaryCopyBridge.reconstructedPath_eq_anchoredSolve d t harmonic g k hab bridge hp heta] at
    ht
  rw [copyVelocity, normalDot_complexify]
  have hr : ⟪t.normal (nativePoint g k p), t.linearData.copySolve g hab k p⟫_ℝ = 0 := by
    simpa only [nativePoint, LinearData.copySolve, Prod.mk.eta] using ht
  rw [hr, Complex.ofReal_zero]

end ModalTangency

section ComplexSources

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses

noncomputable def realPart : ComplexVector →L[ℝ] ProblemStatement.Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => !₂[(a 0).re, (a 1).re, (a 2).re]
    map_add' := by intro a b; ext i; fin_cases i <;> simp
    map_smul' := by intro c a; ext i; fin_cases i <;> simp }

noncomputable def imagPart : ComplexVector →L[ℝ] ProblemStatement.Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => !₂[(a 0).im, (a 1).im, (a 2).im]
    map_add' := by intro a b; ext i; fin_cases i <;> simp
    map_smul' := by intro c a; ext i; fin_cases i <;> simp }

@[simp] theorem realPart_apply (a : ComplexVector) (i : Fin 3) : realPart a i = (a i).re := by
  fin_cases i <;> rfl
@[simp] theorem imagPart_apply (a : ComplexVector) (i : Fin 3) : imagPart a i = (a i).im := by
  fin_cases i <;> rfl

noncomputable def complexScale (c : ℂ) : ComplexVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi fun i => ((ContinuousLinearMap.mul ℝ ℂ) c).comp (ContinuousLinearMap.proj
    i)

@[simp] theorem complexScale_apply (c : ℂ) (a : ComplexVector) : complexScale c a = c • a := rfl

theorem complex_parts (a : ComplexVector) :
    CurlClassBounds.complexify (realPart a) + Complex.I • CurlClassBounds.complexify (imagPart a) =
      a := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, CurlClassBounds.complexify_apply, realPart_apply,
    imagPart_apply, smul_eq_mul]
  rw [mul_comm, Complex.re_add_im]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def realData (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) : TangentData P ProblemStatement.Space :=
  { t with source := fun p => realPart (source p) }

noncomputable def imagData (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) : TangentData P ProblemStatement.Space :=
  { t with source := fun p => imagPart (source p) }

/-- The actual particular coefficient for an arbitrary complex harmonic
source, obtained from two real Volterra solves with the same geometry. -/
noncomputable def complexCopyVelocity (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) (p : P × Plane) : ComplexVector :=
  copyVelocity (realData t source) g hab copy p +
    Complex.I • copyVelocity (imagData t source) g hab copy p

noncomputable def complexCopyPressure (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) (frequency : ℝ) (p : P × Plane) : ℂ :=
  copyPressure (realData t source) g hab copy frequency p +
    Complex.I * copyPressure (imagData t source) g hab copy frequency p

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Function-level equations keep the finite-path solver opaque when the
principal operator is assembled. -/
theorem complexCopyVelocity_eq_parts (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) :
    complexCopyVelocity t source g hab copy = fun x =>
      copyVelocity (realData t source) g hab copy x +
        Complex.I • copyVelocity (imagData t source) g hab copy x := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyPressure_eq_parts (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) (frequency : ℝ) :
    complexCopyPressure t source g hab copy frequency = fun x =>
      copyPressure (realData t source) g hab copy frequency x +
        Complex.I * copyPressure (imagData t source) g hab copy frequency x := rfl

theorem copyVelocity_component_differentiable (t : TangentData P ProblemStatement.Space)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (copy : Frequency) {p : P × Plane}
    (hu : DifferentiableAt ℝ (t.linearData.copySolve g hab copy) p) (i : Fin 3) :
    DifferentiableAt ℝ (fun z => copyVelocity t g hab copy z i) p :=
  (((ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).comp
    CurlClassBounds.complexify).differentiableAt
    (x := t.linearData.copySolve g hab copy p)).comp p hu

noncomputable def complexCopyCoefficients (base : LinearWaveBounds.WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) :
    LinearWaveBounds.WaveCoefficients (P × Plane) :=
  { base with
    amplitude := fun n => complexCopyVelocity (t n) (source n) (g n) (hL n).le (copy n)
    pressure := fun n => complexCopyPressure (t n) (source n) (g n) (hL n).le (copy n)
      (base.frequency n) }

theorem complexCopyVelocity_class {s : StripData (P × Plane)} {W : ℕ → P × Plane → ℝ} {α : ℝ}
    {t : ℕ → TangentData P ProblemStatement.Space} {source : ℕ → P × Plane → ComplexVector}
    {g : ℕ → Geometry} {copy : ℕ → Frequency} {L : ℕ → ℝ} {hL : ∀ n, 0 < L n}
    (hr : WaveClass s W α (fun n => (realData (t n) (source n)).linearData.copySolve (g n) (hL
      n).le (copy n)))
    (hi : WaveClass s W α (fun n => (imagData (t n) (source n)).linearData.copySolve (g n) (hL
      n).le (copy n))) :
    WaveClass s W α (fun n => complexCopyVelocity (t n) (source n) (g n) (hL n).le (copy n)) :=
  (copyVelocity_class (hL := hL) hr).add ((copyVelocity_class (hL := hL) hi).map (complexScale
    Complex.I))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complex linearity of the displayed principal operator. The directional
derivative terms are differentiated before the algebraic combination. -/
theorem principal_add_smul (ε frequency : ℝ) (R F G Φ : E → ℝ) (Vr Vθ Vz Vf : E → E)
    (a b : E → ComplexVector) (p q : E → ℂ) (c : ℂ) {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ
      (fun y => a y + c • b y) (fun y => p y + c * q y) x =
      LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ a p x +
        c • LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ b q x := by
  ext i
  have hcb : DifferentiableAt ℝ (fun y => c * b y i) x := (differentiableAt_const c).mul (hb i)
  have hd : along Vf (fun y => a y i + c * b y i) x =
      along Vf (fun y => a y i) x + c * along Vf (fun y => b y i) x := by
    rw [along_add Vf (ha i) hcb, along_const_mul Vf c (hb i)]
  simp only [LinearWaveResidual.principal, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hd]
  fin_cases i <;> simp [LinearWaveResidual.shear] <;> ring

private theorem principal_parts_cancel (ε frequency : ℝ) (R F G Φ : E → ℝ)
    (Vr Vθ Vz Vf : E → E) (a b : E → ComplexVector) (p q : E → ℂ)
    (u v : ComplexVector) {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x)
    (hra : LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ a p x = -u)
    (hrb : LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ b q x = -v) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz Vf Φ
      (fun y => a y + Complex.I • b y) (fun y => p y + Complex.I * q y) x =
        -(u + Complex.I • v) := by
  rw [principal_add_smul ε frequency R F G Φ Vr Vθ Vz Vf a b p q Complex.I ha hb, hra, hrb]
  simp only [smul_neg, neg_add]

private theorem shear_at_constant (R F G : E → ℝ) (Vr : E → E)
    (a : E → ComplexVector) (x : E) :
    LinearWaveResidual.shear R F G Vr (fun _ => a x) x =
      LinearWaveResidual.shear R F G Vr a x := rfl

/-- Exact cancellation for an arbitrary complex source, obtained from
the two actual real copy solves. -/
theorem complexCopy_principal (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U) (copy : Frequency)
    (hA : ContDiffOn ℝ ∞ t.linearData.coefficient (U ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ source (U ×ˢ univ))
    (ε frequency : ℝ) (hfrequency : frequency ≠ 0)
    (R F G Φ : P × Plane → ℝ) (Vr Vθ Vz : P × Plane → P × Plane)
    {p : P} (hp : p ∈ U) (Y : Plane) (heta : (g.coordinates copy Y).2 ∈ Ioo a b)
    (hN : phaseNormal R Vr Vθ Vz Φ (p, Y) = t.normal (p, g.coordinates copy Y))
    (hδ : t.damping (p, g.coordinates copy Y) =
      ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2)
    (hK : ∀ v : ProblemStatement.Space,
      CurlClassBounds.complexify (t.action (p, g.coordinates copy Y) v) =
        LinearWaveResidual.shear R F G Vr (fun _ => CurlClassBounds.complexify v) (p, Y)) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz
      (fun _ => ((0 : P), slotDirection g)) Φ (complexCopyVelocity t source g hab copy)
      (complexCopyPressure t source g hab copy frequency) (p, Y) = -source (p, Y) := by
  rw [complexCopyVelocity_eq_parts, complexCopyPressure_eq_parts]
  have hfr : ContDiffOn ℝ ∞ (realData t source).source (U ×ˢ univ) :=
    realPart.contDiff.comp_contDiffOn hf
  have hfi : ContDiffOn ℝ ∞ (imagData t source).source (U ×ˢ univ) :=
    imagPart.contDiff.comp_contDiffOn hf
  have hr := copySolve_principal (realData t source) g hab hU copy hA hB hfr ε frequency hfrequency
    R F G Φ Vr Vθ Vz
    (p := p) hp Y heta hN hδ (
      (hK ((realData t source).linearData.copySolve g hab copy (p, Y))).trans
        (shear_at_constant R F G Vr (copyVelocity (realData t source) g hab copy) (p, Y)))
  have hi := copySolve_principal (imagData t source) g hab hU copy hA hB hfi ε frequency hfrequency
    R F G Φ Vr Vθ Vz
    (p := p) hp Y heta hN hδ (
      (hK ((imagData t source).linearData.copySolve g hab copy (p, Y))).trans
        (shear_at_constant R F G Vr (copyVelocity (imagData t source) g hab copy) (p, Y)))
  have hur : DifferentiableAt ℝ ((realData t source).linearData.copySolve g hab copy) (p, Y) :=
    ((realData t source).linearData.copySolve_contDiffAt g hab hU copy hA hB hfr (p := (p, Y)) hp
      heta).differentiableAt (by simp)
  have hui : DifferentiableAt ℝ ((imagData t source).linearData.copySolve g hab copy) (p, Y) :=
    ((imagData t source).linearData.copySolve_contDiffAt g hab hU copy hA hB hfi (p := (p, Y)) hp
      heta).differentiableAt (by simp)
  have hvr := copyVelocity_component_differentiable (realData t source) g hab copy (p := (p, Y)) hur
  have hvi := copyVelocity_component_differentiable (imagData t source) g hab copy (p := (p, Y)) hui
  have hc := principal_parts_cancel ε frequency R F G Φ Vr Vθ Vz
    (fun _ => ((0 : P), slotDirection g)) (copyVelocity (realData t source) g hab copy)
      (copyVelocity (imagData t source) g hab copy)
    (copyPressure (realData t source) g hab copy frequency) (copyPressure (imagData t source) g hab
      copy frequency)
    (CurlClassBounds.complexify ((realData t source).source (p, Y))) (CurlClassBounds.complexify
      ((imagData t source).source (p, Y)))
    (x := (p, Y)) hvr hvi hr hi
  have hparts : CurlClassBounds.complexify ((realData t source).source (p, Y)) +
      Complex.I • CurlClassBounds.complexify ((imagData t source).source (p, Y)) = source (p, Y) :=
    complex_parts (source (p, Y))
  exact hc.trans (congrArg Neg.neg hparts)

/-- The same exact cancellation with regularity required only along the
actual finite copy paths. -/
theorem complexCopy_principal_of_path (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) {Ω : Set (P × Plane)}
    (hA : ContinuousOn (t.linearData.coefficientAlong g copy) (Ω ×ˢ Icc a b))
    (hfr : ContinuousOn ((realData t source).linearData.forcingAlong g copy) (Ω ×ˢ Icc a b))
    (hfi : ContinuousOn ((imagData t source).linearData.forcingAlong g copy) (Ω ×ˢ Icc a b))
    (ε frequency : ℝ) (hfrequency : frequency ≠ 0)
    (R F G Φ : P × Plane → ℝ) (Vr Vθ Vz : P × Plane → P × Plane)
    (p : P) (Y : Plane) (hp : (p, Y) ∈ Ω) (heta : (g.coordinates copy Y).2 ∈ Icc a b)
    (hur : DifferentiableAt ℝ ((realData t source).linearData.copySolve g hab copy) (p, Y))
    (hui : DifferentiableAt ℝ ((imagData t source).linearData.copySolve g hab copy) (p, Y))
    (hN : phaseNormal R Vr Vθ Vz Φ (p, Y) = t.normal (p, g.coordinates copy Y))
    (hδ : t.damping (p, g.coordinates copy Y) =
      ε * frequency ^ 2 * ‖phaseNormal R Vr Vθ Vz Φ (p, Y)‖ ^ 2)
    (hK : ∀ v : ProblemStatement.Space,
      CurlClassBounds.complexify (t.action (p, g.coordinates copy Y) v) =
        LinearWaveResidual.shear R F G Vr (fun _ => CurlClassBounds.complexify v) (p, Y)) :
    LinearWaveResidual.principal ε frequency R F G Vr Vθ Vz
      (fun _ => ((0 : P), slotDirection g)) Φ (complexCopyVelocity t source g hab copy)
      (complexCopyPressure t source g hab copy frequency) (p, Y) = -source (p, Y) := by
  rw [complexCopyVelocity_eq_parts, complexCopyPressure_eq_parts]
  have hr := copySolve_principal_of_path (realData t source) g hab copy hA hfr ε frequency
    hfrequency R F G Φ Vr Vθ Vz
    p Y hp heta hur hN hδ (
      (hK ((realData t source).linearData.copySolve g hab copy (p, Y))).trans
        (shear_at_constant R F G Vr (copyVelocity (realData t source) g hab copy) (p, Y)))
  have hi := copySolve_principal_of_path (imagData t source) g hab copy hA hfi ε frequency
    hfrequency R F G Φ Vr Vθ Vz
    p Y hp heta hui hN hδ (
      (hK ((imagData t source).linearData.copySolve g hab copy (p, Y))).trans
        (shear_at_constant R F G Vr (copyVelocity (imagData t source) g hab copy) (p, Y)))
  have hvr := copyVelocity_component_differentiable (realData t source) g hab copy (p := (p, Y)) hur
  have hvi := copyVelocity_component_differentiable (imagData t source) g hab copy (p := (p, Y)) hui
  have hc := principal_parts_cancel ε frequency R F G Φ Vr Vθ Vz
    (fun _ => ((0 : P), slotDirection g)) (copyVelocity (realData t source) g hab copy)
      (copyVelocity (imagData t source) g hab copy)
    (copyPressure (realData t source) g hab copy frequency) (copyPressure (imagData t source) g hab
      copy frequency)
    (CurlClassBounds.complexify ((realData t source).source (p, Y))) (CurlClassBounds.complexify
      ((imagData t source).source (p, Y)))
    (x := (p, Y)) hvr hvi hr hi
  have hparts : CurlClassBounds.complexify ((realData t source).source (p, Y)) +
      Complex.I • CurlClassBounds.complexify ((imagData t source).source (p, Y)) = source (p, Y) :=
    complex_parts (source (p, Y))
  exact hc.trans (congrArg Neg.neg hparts)

end ComplexSources

section ConstructedWave

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses LinearWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def zeroAmplitudes (base : WaveCoefficients (P × Plane)) : WaveCoefficients (P ×
  Plane) :=
  { base with amplitude := fun _ _ => 0, pressure := fun _ _ => 0 }

/-- Matches of primitive physical geometry with the native projected ODE.
The action equality is required for every vector, not just the solution. -/
structure CopyGeometryMatch (s : StripData (P × Plane)) (dirs : GraphDirections (P × Plane))
    (base : WaveCoefficients (P × Plane)) (t : ℕ → TangentData P ProblemStatement.Space)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) : Prop where
  normal : ∀ n x, x ∈ s.domain → base.normal s dirs n x = (t n).normal (nativePoint (g n) (copy n)
    x)
  damping : ∀ n x, x ∈ s.domain → (t n).damping (nativePoint (g n) (copy n) x) =
    s.epsilon n * base.frequency n ^ 2 * ‖base.normal s dirs n x‖ ^ 2
  fast : ∀ n, dirs.fastScale n • dirs.fast = ((0 : P), slotDirection (g n))
  action : ∀ n x, x ∈ s.domain → ∀ v : ProblemStatement.Space,
    CurlClassBounds.complexify ((t n).action (nativePoint (g n) (copy n) x) v) =
      LinearWaveResidual.shear (base.radius n) (base.frequencyBase n) (base.axialBase n)
        (dirs.radialField n) (fun _ => CurlClassBounds.complexify v) x

/-- Every amplitude and pressure hypothesis of the linear-wave estimate
is obtained from the actual forced solves and their primitive input bounds. -/
theorem complexCopy_inputBounds
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ)
    (hr : CopyControl s α (fun n => (realData (t n) (source n)).linearData) g copy L W)
    (hi : CopyControl s α (fun n => (imagData (t n) (source n)).linearData) g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n)) :
    InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (complexCopyCoefficients base t source g copy L hL) := by
  have hru := hr.waveClass hL
  have hiu := hi.waveClass hL
  have hv := complexCopyVelocity_class (hL := hL) hru hiu
  have hpr := copyPressure_class (t := fun n => realData (t n) (source n)) (hL := hL)
    hN hNdot hA hru (hf.map realPart) hpos hlower hupper hfrequency
  have hpi := copyPressure_class (t := fun n => imagData (t n) (source n)) (hL := hL)
    hN hNdot hA hiu (hf.map imagPart) hpos hlower hupper hfrequency
  have hp := hpr.add (constant_complex_mul hpi Complex.I)
  exact { hb with
    amplitude := fun i => hv.map (ContinuousLinearMap.proj i)
    pressure := hp }

/-- Every amplitude and pressure hypothesis of the linear-wave estimate
is obtained from the actual forced solves and their primitive input bounds. -/
theorem complexCopy_inputBounds_of_modal
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n)) :
    InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (complexCopyCoefficients base t source g copy L hL) := by
  have hru := hr.waveClass hL
  have hiu := hi.waveClass hL
  have hv := complexCopyVelocity_class (hL := hL) hru hiu
  have hpr := copyPressure_class (t := fun n => realData (t n) (source n)) (hL := hL)
    hN hNdot hA hru (hf.map realPart) hpos hlower hupper hfrequency
  have hpi := copyPressure_class (t := fun n => imagData (t n) (source n)) (hL := hL)
    hN hNdot hA hiu (hf.map imagPart) hpos hlower hupper hfrequency
  have hp := hpr.add (constant_complex_mul hpi Complex.I)
  exact { hb with
    amplitude := fun i => hv.map (ContinuousLinearMap.proj i)
    pressure := hp }

/-- The constructed complex coefficient satisfies the principal cancellation
needed by the exact residual decomposition. No cancellation hypothesis is
accepted as an input. -/
theorem complexCopyCoefficients_principal
    {s : StripData (P × Plane)} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    {U : Set P} (hU : IsOpen U) (hdom : ∀ p ∈ s.domain, p.1 ∈ U)
    (hA : ∀ n, ContDiffOn ℝ ∞ (t n).linearData.coefficient (U ×ˢ univ))
    (hB : ∀ n, ContDiffOn ℝ ∞ (t n).linearData.forcingMap (U ×ˢ univ))
    (hf : ∀ n, ContDiffOn ℝ ∞ (source n) (U ×ˢ univ))
    (hslot : ∀ n p, p ∈ s.domain → ((g n).coordinates (copy n) p.2).2 ∈ Ioo 0 (L n))
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency : ∀ n, base.frequency n ≠ 0) :
    ∀ n x, x ∈ s.domain →
      (complexCopyCoefficients base t source g copy L hL).principal s dirs n x = -source n x := by
  intro n x hx
  have hh := complexCopy_principal (t n) (source n) (g n) (hL n).le hU (copy n) (hA n) (hB n) (hf n)
    (s.epsilon n) (base.frequency n) (hfrequency n) (base.radius n) (base.frequencyBase n)
    (base.axialBase n) (base.phase n) (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField
      s n)
    (hdom x hx) x.2 (hslot n x hx) (hgeometry.normal n x hx) (hgeometry.damping n x hx)
    (hgeometry.action n x hx)
  have hfast : dirs.fastField n = fun _ => ((0 : P), slotDirection (g n)) := by
    funext z
    exact hgeometry.fast n
  simpa only [WaveCoefficients.principal, complexCopyCoefficients, hfast, Prod.mk.eta] using hh

/-- The principal equation for the actual modal construction. All required
regularity is local to the finite integration interval. -/
theorem complexCopyCoefficients_principal_of_modal
    {s : StripData (P × Plane)} {α : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency : ∀ n, base.frequency n ≠ 0) :
    ∀ n x, x ∈ s.domain →
      (complexCopyCoefficients base t source g copy L hL).principal s dirs n x = -source n x := by
  intro n x hx
  have hur := ((hr.contDiffOn hL n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
    simp)
  have hui := ((hi.contDiffOn hL n).contDiffAt (s.isOpen_domain.mem_nhds hx)).differentiableAt (by
    simp)
  have hh := complexCopy_principal_of_path (t n) (source n) (g n) (hL n).le (copy n)
    (hr.bridge n).ambient_coefficient (hr.bridge n).ambient_forcing (hi.bridge n).ambient_forcing
    (s.epsilon n) (base.frequency n) (hfrequency n) (base.radius n) (base.frequencyBase n)
    (base.axialBase n) (base.phase n) (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField
      s n)
    x.1 x.2 hx ⟨(hr.current_slot n x hx).1.le, (hr.current_slot n x hx).2.le⟩
    hur hui (hgeometry.normal n x hx) (hgeometry.damping n x hx) (hgeometry.action n x hx)
  have hfast : dirs.fastField n = fun _ => ((0 : P), slotDirection (g n)) := by
    funext z
    exact hgeometry.fast n
  simpa only [WaveCoefficients.principal, complexCopyCoefficients, hfast, Prod.mk.eta] using hh

/-- The complex tangent condition comes from the two reconstructed modal
solutions, before applying any cutoff or exact curl. -/
theorem complexCopyCoefficients_tangent_of_modal
    {s : StripData (P × Plane)} {α : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hgeometry : CopyGeometryMatch s dirs base t g copy) :
    ∀ n x, x ∈ s.domain → normalDot (base.normal s dirs n x)
      ((complexCopyCoefficients base t source g copy L hL).amplitude n x) = 0 := by
  intro n x hx
  have htR := copyVelocity_tangent_of_modal (d n) (realData (t n) (source n)) harmonic (g n) (copy
    n)
    (hL n).le (hr.bridge n) hx ⟨(hr.current_slot n x hx).1.le, (hr.current_slot n x hx).2.le⟩
  have htI := copyVelocity_tangent_of_modal (d n) (imagData (t n) (source n)) harmonic (g n) (copy
    n)
    (hL n).le (hi.bridge n) hx ⟨(hi.current_slot n x hx).1.le, (hi.current_slot n x hx).2.le⟩
  rw [hgeometry.normal n x hx]
  change normalDot ((t n).normal (nativePoint (g n) (copy n) x))
    (copyVelocity (realData (t n) (source n)) (g n) (hL n).le (copy n) x +
      Complex.I • copyVelocity (imagData (t n) (source n)) (g n) (hL n).le (copy n) x) = 0
  have hadd (N : ProblemStatement.Space) (a b : ComplexVector) :
      normalDot N (a + Complex.I • b) = normalDot N a + Complex.I * normalDot N b := by
    simp only [normalDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change normalDot ((t n).normal (nativePoint (g n) (copy n) x))
    (copyVelocity (realData (t n) (source n)) (g n) (hL n).le (copy n) x) = 0 at htR
  change normalDot ((t n).normal (nativePoint (g n) (copy n) x))
    (copyVelocity (imagData (t n) (source n)) (g n) (hL n).le (copy n) x) = 0 at htI
  rw [hadd, htR, htI, mul_zero, add_zero]

/-- Complete class and actual residual statements for the constructed complex
particular wave. Both Gaussian cutoff terms remain on the right-hand side. -/
theorem constructed_particular_wave
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ)
    (hr : CopyControl s α (fun n => (realData (t n) (source n)).linearData) g copy L W)
    (hi : CopyControl s α (fun n => (imagData (t n) (source n)).linearData) g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n))
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency_ne : ∀ n, base.frequency n ≠ 0)
    (hsource_smooth : ∀ n, ContDiffOn ℝ ∞ (source n) (hr.slowDomain ×ˢ univ))
    (hκ : κ ≤ 1 / 2) (ψ : ℕ → P × Plane → ℝ) (hψ : UnweightedClass s 0 ψ)
    {R : P × Plane → ℝ} (hR : base.radius = fun _ => R)
    (hg : ExactConditions s dirs ((complexCopyCoefficients base t source g copy L hL).corrected s
      dirs ψ)) :
    let a := complexCopyCoefficients base t source g copy L hL
    let P := fun n p => W n ((g n).coordinates (copy n) p.2).2
    WaveClass s P α a.amplitude ∧
    WaveClass s P α (a.corrected s dirs ψ).amplitude ∧
    WaveClass s P (α + 1 / 2) (a.corrected s dirs ψ).pressure ∧
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s dirs ψ) ∧
    ∀ n x, x ∈ s.domain →
      (a.corrected s dirs ψ).harmonicResidual s dirs n x +
        (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.constructedGood s dirs ψ n x i +
        excludedSlotError dirs ψ a.amplitude source n x i) * carrier (a.frequency n) (a.phase n) x)
          := by
  let a := complexCopyCoefficients base t source g copy L hL
  have h0 := complexCopy_inputBounds base t source g copy L hL W hr hi hb hN hNdot hA hf
    hpos hlower hupper hfrequency
  have hNa : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s dirs) := by
    apply hN.congr
    intro n x hx
    exact (hgeometry.normal n x hx).symm
  have hlow : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s dirs n x‖ := by
    intro n x hx
    change b ≤ ‖base.normal s dirs n x‖
    rw [hgeometry.normal n x hx]
    exact hlower n x hx
  have hupp : ∀ n x, x ∈ s.domain → ‖a.normal s dirs n x‖ ≤ M := by
    intro n x hx
    change ‖base.normal s dirs n x‖ ≤ M
    rw [hgeometry.normal n x hx]
    exact hupper n x hx
  have hsolve := complexCopyCoefficients_principal base t source g copy L hL hr.open_slow hr.domain
    hr.coefficient_smooth hr.forcingMap_smooth hsource_smooth hr.current_slot hgeometry
      hfrequency_ne
  have hcorr := (h0.with_cutoff hψ).curlCorrection_class hR hNa hpos hlow hupp hfrequency
  have hc := (h0.with_cutoff hψ).add_curl_amplitude hκ (fun i => CurlClassBounds.class_component
    hcorr i)
  have hout := constructed_linear_wave_with_excluded h0 hκ hψ hR hNa hpos hlow hupp hfrequency
    hsolve hg
  exact ⟨component_classes h0.amplitude, component_classes hc.amplitude, hc.pressure, hout.1,
    hout.2⟩

/-- The cutoff remainder is both retained in the exact equation and proved
smaller than every prescribed epsilon power under the Gaussian envelope. -/
theorem constructed_particular_wave_with_flat_error
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ)
    (hr : CopyControl s α (fun n => (realData (t n) (source n)).linearData) g copy L W)
    (hi : CopyControl s α (fun n => (imagData (t n) (source n)).linearData) g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n))
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency_ne : ∀ n, base.frequency n ≠ 0)
    (hsource_smooth : ∀ n, ContDiffOn ℝ ∞ (source n) (hr.slowDomain ×ˢ univ))
    (hκ : κ ≤ 1 / 2) (slot : GaussianTailFlat.SlotFamily s)
    (hfast : ∀ n, slot.linear n (dirs.fastScale n • dirs.fast) = (slot.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {c : ℝ} (hc : 0 < c)
    (hW : ∀ n x, x ∈ s.domain → W n ((g n).coordinates (copy n) x.2).2 ≤
      Real.exp (-c * (slot.coordinate n x - 1 / 2) ^ 2 * slot.length n))
    {R : P × Plane → ℝ} (hR : base.radius = fun _ => R)
    (hg : ExactConditions s dirs ((complexCopyCoefficients base t source g copy L hL).corrected s
      dirs slot.cutoff)) :
    let a := complexCopyCoefficients base t source g copy L hL
    let P := fun n p => W n ((g n).coordinates (copy n) p.2).2
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s dirs slot.cutoff) ∧
    (∀ β : ℝ, UnweightedClass s β (excludedSlotError dirs slot.cutoff a.amplitude source)) ∧
    ∀ n x, x ∈ s.domain →
      (a.corrected s dirs slot.cutoff).harmonicResidual s dirs n x +
        (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.constructedGood s dirs slot.cutoff n x i +
        excludedSlotError dirs slot.cutoff a.amplitude source n x i) * carrier (a.frequency n)
          (a.phase n) x) := by
  have hres := constructed_particular_wave base t source g copy L hL W hr hi hb hN hNdot hA hf
    hpos hlower hupper hfrequency hgeometry hfrequency_ne hsource_smooth hκ slot.cutoff
      slot.cutoff_memClass hR hg
  exact ⟨hres.2.2.2.1, fun β => excludedSlotError_all_gains slot dirs hfast edges scales hres.1 hf
    hc hW β,
    hres.2.2.2.2⟩


/-- Complete class and actual residual statements for the constructed complex
particular wave. Both Gaussian cutoff terms remain on the right-hand side. -/
theorem constructed_modal_particular_wave
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n))
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency_ne : ∀ n, base.frequency n ≠ 0)
    (hκ : κ ≤ 1 / 2) (ψ : ℕ → P × Plane → ℝ) (hψ : UnweightedClass s 0 ψ)
    {R : P × Plane → ℝ} (hR : base.radius = fun _ => R)
    (hg : ExactConditions s dirs ((complexCopyCoefficients base t source g copy L hL).corrected s
      dirs ψ)) :
    let a := complexCopyCoefficients base t source g copy L hL
    let P := fun n p => W n ((g n).coordinates (copy n) p.2).2
    WaveClass s P α a.amplitude ∧
    WaveClass s P α (a.corrected s dirs ψ).amplitude ∧
    WaveClass s P (α + 1 / 2) (a.corrected s dirs ψ).pressure ∧
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s dirs ψ) ∧
    ∀ n x, x ∈ s.domain →
      (a.corrected s dirs ψ).harmonicResidual s dirs n x +
        (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.constructedGood s dirs ψ n x i +
        excludedSlotError dirs ψ a.amplitude source n x i) * carrier (a.frequency n) (a.phase n) x)
          := by
  let a := complexCopyCoefficients base t source g copy L hL
  have h0 := complexCopy_inputBounds_of_modal base t source g copy L hL W d harmonic hr hi hb hN
    hNdot hA hf
    hpos hlower hupper hfrequency
  have hNa : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s) (a.normal s dirs) := by
    apply hN.congr
    intro n x hx
    exact (hgeometry.normal n x hx).symm
  have hlow : ∀ n x, x ∈ s.domain → b ≤ ‖a.normal s dirs n x‖ := by
    intro n x hx
    change b ≤ ‖base.normal s dirs n x‖
    rw [hgeometry.normal n x hx]
    exact hlower n x hx
  have hupp : ∀ n x, x ∈ s.domain → ‖a.normal s dirs n x‖ ≤ M := by
    intro n x hx
    change ‖base.normal s dirs n x‖ ≤ M
    rw [hgeometry.normal n x hx]
    exact hupper n x hx
  have hsolve := complexCopyCoefficients_principal_of_modal base t source g copy L hL W d harmonic
    hr hi hgeometry hfrequency_ne
  have hcorr := (h0.with_cutoff hψ).curlCorrection_class hR hNa hpos hlow hupp hfrequency
  have hc := (h0.with_cutoff hψ).add_curl_amplitude hκ (fun i => CurlClassBounds.class_component
    hcorr i)
  have hout := constructed_linear_wave_with_excluded h0 hκ hψ hR hNa hpos hlow hupp hfrequency
    hsolve hg
  exact ⟨component_classes h0.amplitude, component_classes hc.amplitude, hc.pressure, hout.1,
    hout.2⟩

/-- The cutoff remainder is both retained in the exact equation and proved
smaller than every prescribed epsilon power under the Gaussian envelope. -/
theorem constructed_modal_particular_wave_with_flat_error
    {s : StripData (P × Plane)} {α κ : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hb : InputBounds s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α κ dirs
      (zeroAmplitudes base))
    (hN : PhaseJetBounds.PolynomialJets (CurlClassBounds.phaseDomain s)
      (fun n p => (t n).normal (nativePoint (g n) (copy n) p)))
    (hNdot : UnweightedClass s 0 (fun n p => (t n).normalDot (nativePoint (g n) (copy n) p)))
    (hA : UnweightedClass s 0 (fun n p => (t n).action (nativePoint (g n) (copy n) p)))
    (hf : WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α source)
    {b M : ℝ} (hpos : 0 < b)
    (hlower : ∀ n p, p ∈ s.domain → b ≤ ‖(t n).normal (nativePoint (g n) (copy n) p)‖)
    (hupper : ∀ n p, p ∈ s.domain → ‖(t n).normal (nativePoint (g n) (copy n) p)‖ ≤ M)
    (hfrequency : BandBound s (1 / 2) (fun n => 1 / base.frequency n))
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (hfrequency_ne : ∀ n, base.frequency n ≠ 0)
    (hκ : κ ≤ 1 / 2) (slot : GaussianTailFlat.SlotFamily s)
    (hfast : ∀ n, slot.linear n (dirs.fastScale n • dirs.fast) = (slot.length n)⁻¹)
    (edges : GaussianTailFlat.FlatEdges s) (scales : GaussianTailFlat.BandScaleControl s)
    {c : ℝ} (hc : 0 < c)
    (hW : ∀ n x, x ∈ s.domain → W n ((g n).coordinates (copy n) x.2).2 ≤
      Real.exp (-c * (slot.coordinate n x - 1 / 2) ^ 2 * slot.length n))
    {R : P × Plane → ℝ} (hR : base.radius = fun _ => R)
    (hg : ExactConditions s dirs ((complexCopyCoefficients base t source g copy L hL).corrected s
      dirs slot.cutoff)) :
    let a := complexCopyCoefficients base t source g copy L hL
    let P := fun n p => W n ((g n).coordinates (copy n) p.2).2
    WaveClass s P (α + 1 / 2 - 3 * κ) (a.constructedGood s dirs slot.cutoff) ∧
    (∀ β : ℝ, UnweightedClass s β (excludedSlotError dirs slot.cutoff a.amplitude source)) ∧
    ∀ n x, x ∈ s.domain →
      (a.corrected s dirs slot.cutoff).harmonicResidual s dirs n x +
        (fun i => source n x i * carrier (a.frequency n) (a.phase n) x) =
      (fun i => (a.constructedGood s dirs slot.cutoff n x i +
        excludedSlotError dirs slot.cutoff a.amplitude source n x i) * carrier (a.frequency n)
          (a.phase n) x) := by
  have hres := constructed_modal_particular_wave base t source g copy L hL W d harmonic hr hi hb hN
    hNdot hA hf
    hpos hlower hupper hfrequency hgeometry hfrequency_ne hκ slot.cutoff slot.cutoff_memClass hR hg
  exact ⟨hres.2.2.2.1, fun β => excludedSlotError_all_gains slot dirs hfast edges scales hres.1 hf
    hc hW β,
    hres.2.2.2.2⟩

end ConstructedWave

section AngularAndCurl

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses LinearWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Primitive angular invariance of the real geometry and source is
preserved by both actual complex outputs. The carrier remains equivariant. -/
theorem complexCopyCoefficients_invariant
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (θ : P)
    (hr : ∀ n, CopyAngularInvariance.TangentInvariant θ (realData (t n) (source n)))
    (hi : ∀ n, CopyAngularInvariance.TangentInvariant θ (imagData (t n) (source n))) (n : ℕ) :
    CopyAngularInvariance.Invariant (θ, (0 : Plane))
      ((complexCopyCoefficients base t source g copy L hL).amplitude n) ∧
    CopyAngularInvariance.Invariant (θ, (0 : Plane))
      ((complexCopyCoefficients base t source g copy L hL).pressure n) := by
  constructor
  · exact (((hr n).copySolve_invariant (g n) (hL n).le (copy n)).map
    CurlClassBounds.complexify).map₂
      (((hi n).copySolve_invariant (g n) (hL n).le (copy n)).map CurlClassBounds.complexify)
      (fun a b => a + Complex.I • b)
  · exact ((hr n).copyPressure_invariant (g n) (hL n).le (copy n) (base.frequency n)).map₂
      ((hi n).copyPressure_invariant (g n) (hL n).le (copy n) (base.frequency n))
      (fun a b => a + Complex.I * b)

/-- The modal construction really realizes the corrected field as a curl,
and its actual harmonic divergence vanishes. No output tangency or smoothness
hypothesis is used. -/
theorem modal_corrected_is_curl_and_divergence_zero
    {s : StripData (P × Plane)} {α : ℝ} {dirs : GraphDirections (P × Plane)}
    (base : WaveCoefficients (P × Plane))
    (t : ℕ → TangentData P ProblemStatement.Space) (source : ℕ → P × Plane → ComplexVector)
    (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (W : ℕ → ℝ → ℝ) (d : ℕ → PrimaryODE.FrameData (P × ℝ)) (harmonic : ℤ)
    (hr : ModalCopyControl s α d (fun n => realData (t n) (source n)) harmonic g copy L W)
    (hi : ModalCopyControl s α d (fun n => imagData (t n) (source n)) harmonic g copy L W)
    (hgeometry : CopyGeometryMatch s dirs base t g copy)
    (ψ : ℕ → P × Plane → ℝ) (n : ℕ) (hψ : ContDiffOn ℝ ∞ (ψ n) s.domain)
    (G : CurlClassBounds.CylindricalGeometry s.domain (base.radius n) (dirs.radialField n)
      (fun _ => dirs.angular) (dirs.axialField s n))
    (hK : base.frequency n ≠ 0) (hΦ : ContDiffOn ℝ ∞ (base.phase n) s.domain)
    (hn : ∀ x ∈ s.domain, base.normal s dirs n x ≠ 0) {x : P × Plane} (hx : x ∈ s.domain) :
    let a := complexCopyCoefficients base t source g copy L hL
    CurlClassBounds.cylindricalCurl (base.radius n) (dirs.radialField n) (fun _ => dirs.angular)
        (dirs.axialField s n) ((a.withCutoff ψ).curlPotential s dirs n) x =
      vectorMode (base.frequency n) (base.phase n) ((a.corrected s dirs ψ).amplitude n) x ∧
    cylindricalDivergence (base.radius n) (dirs.radialField n) (fun _ => dirs.angular)
      (dirs.axialField s n)
      (vectorMode (base.frequency n) (base.phase n) ((a.corrected s dirs ψ).amplitude n)) x = 0 :=
        by
  let a := complexCopyCoefficients base t source g copy L hL
  have hvr := CurlClassBounds.complexify.contDiff.comp_contDiffOn (hr.contDiffOn hL n)
  have hvi := CurlClassBounds.complexify.contDiff.comp_contDiffOn (hi.contDiffOn hL n)
  have hv : ContDiffOn ℝ ∞ (a.amplitude n) s.domain :=
    hvr.add ((complexScale Complex.I).contDiff.comp_contDiffOn hvi)
  have ht := complexCopyCoefficients_tangent_of_modal base t source g copy L hL W d harmonic hr hi
    hgeometry n
  have hcut := cutoff_tangent (a := a) ψ n ht
  exact ⟨CurlClassBounds.cylindricalCurl_vectorPotential G hK hΦ (hψ.smul hv) hn hcut hx,
    CurlClassBounds.realizedCoefficient_divergence G hK hΦ (hψ.smul hv) hn hcut hx⟩

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Localization is retained after taking the actual curl, including on
the cutoff boundary. -/
theorem correctedCurl_tsupport_subset (s : StripData D) (dirs : GraphDirections D)
    (a : WaveCoefficients D) (ψ : ℕ → D → ℝ) (n : ℕ) :
    tsupport (CurlClassBounds.cylindricalCurl (a.radius n) (dirs.radialField n) (fun _ =>
      dirs.angular)
      (dirs.axialField s n) ((a.withCutoff ψ).curlPotential s dirs n)) ⊆
      tsupport (ψ n) ∩ tsupport (a.amplitude n) := by
  have h := CurlClassBounds.realizedWave_tsupport_subset (a.frequency n) (a.radius n)
    (dirs.radialField n) (fun _ => dirs.angular) (dirs.axialField s n) (a.phase n)
    (fun x => ψ n x • a.amplitude n x)
  exact h.trans (subset_inter (tsupport_smul_subset_left _ _) (tsupport_smul_subset_right _ _))

end AngularAndCurl

section RealityAndSupport

open CommonCoverSolve TorusInverse HarmonicCalculus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def scaleTangentSource (t : TangentData P ProblemStatement.Space) (c : ℝ) :
    TangentData P ProblemStatement.Space := { t with source := fun p => c • t.source p }

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyVelocity_scaleSource (t : TangentData P ProblemStatement.Space) (c : ℝ)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency) (p : P × Plane) :
    copyVelocity (scaleTangentSource t c) g hab k p = c • copyVelocity t g hab k p := by
  change CurlClassBounds.complexify
    ((CopySolveCompatibility.scaleSource t.linearData c).copySolve g hab k p) = _
  rw [CopySolveCompatibility.copySolve_scaleSource]
  exact map_smul _ _ _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyPressureReal_scaleSource (t : TangentData P ProblemStatement.Space) (c : ℝ)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency) (p : P × Plane) :
    copyPressureReal (scaleTangentSource t c) g hab k p = c * copyPressureReal t g hab k p := by
  have hs : (scaleTangentSource t c).linearData.copySolve g hab k p =
      c • t.linearData.copySolve g hab k p :=
    CopySolveCompatibility.copySolve_scaleSource t.linearData g hab c k p.1 p.2
  change TangentProjection.pressureCoefficient (t.normal (nativePoint g k p))
    (t.normalDot (nativePoint g k p)) ((scaleTangentSource t c).linearData.copySolve g hab k p)
    (t.action (nativePoint g k p) ((scaleTangentSource t c).linearData.copySolve g hab k p))
    (c • t.source p) = c * TangentProjection.pressureCoefficient (t.normal (nativePoint g k p))
      (t.normalDot (nativePoint g k p)) (t.linearData.copySolve g hab k p)
      (t.action (nativePoint g k p) (t.linearData.copySolve g hab k p)) (t.source p)
  rw [hs]
  simp only [TangentProjection.pressureCoefficient, map_smul, real_inner_smul_right]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem copyPressure_scaleSource (t : TangentData P ProblemStatement.Space) (c : ℝ)
    (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency) (frequency : ℝ) (p : P × Plane) :
    copyPressure (scaleTangentSource t c) g hab k frequency p = c • copyPressure t g hab k
      frequency p := by
  simp only [copyPressure, copyPressureReal_scaleSource, Complex.ofReal_mul, Complex.real_smul]
  ring

noncomputable def conjugateSource (f : P × Plane → ComplexVector) : P × Plane → ComplexVector :=
  fun p i => star (f p i)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realData_conjugate (t : TangentData P ProblemStatement.Space) (f : P × Plane →
  ComplexVector) :
    realData t (conjugateSource f) = realData t f := by
  have he : (fun p => realPart (conjugateSource f p)) = fun p => realPart (f p) := by
    funext p
    ext i
    simp [conjugateSource]
  unfold realData
  rw [he]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem imagData_conjugate (t : TangentData P ProblemStatement.Space) (f : P × Plane →
  ComplexVector) :
    imagData t (conjugateSource f) = scaleTangentSource (imagData t f) (-1) := by
  have he : (fun p => imagPart (conjugateSource f p)) = fun p => (-1 : ℝ) • imagPart (f p) := by
    funext p
    ext i
    simp [conjugateSource]
  unfold imagData scaleTangentSource
  rw [he]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Conjugation of a source conjugates the actual zero-entry velocity. -/
theorem complexCopyVelocity_conjugate (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (p : P × Plane) :
    complexCopyVelocity t (conjugateSource f) g hab k p =
      fun i => star (complexCopyVelocity t f g hab k p i) := by
  rw [complexCopyVelocity, realData_conjugate, imagData_conjugate, copyVelocity_scaleSource]
  ext i
  simp [complexCopyVelocity, copyVelocity]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The sign change of the harmonic frequency is essential to pressure
conjugation. This proves the symmetry required for a real paired wave. -/
theorem complexCopyPressure_conjugate (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (frequency : ℝ) (p : P × Plane) :
    complexCopyPressure t (conjugateSource f) g hab k (-frequency) p =
      star (complexCopyPressure t f g hab k frequency p) := by
  rw [complexCopyPressure, realData_conjugate, imagData_conjugate, copyPressure_scaleSource]
  simp [complexCopyPressure, copyPressure]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyVelocity_at_entry (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (p : P) (ξ : ℝ) :
    complexCopyVelocity t f g hab k (p, g.point k (ξ, a)) = 0 := by
  simp only [complexCopyVelocity, copyVelocity, LinearData.copySolve_at_entry,
    map_zero, smul_zero, add_zero]

/-- Support is propagated along the actual earlier-point path. Pointwise
vanishing of the source at only the current point is not used. -/
theorem complexCopyVelocity_zero_of_path (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (p : P) (Y : Plane)
    (hf : ∀ v ∈ Icc a b, f (p, g.path k Y v) = 0) :
    complexCopyVelocity t f g hab k (p, Y) = 0 := by
  have hr := (realData t f).linearData.copySolve_zero_of_source_zero g hab k p Y
    (fun v hv => by change realPart (f (p, g.path k Y v)) = 0; rw [hf v hv, map_zero])
  have hi := (imagData t f).linearData.copySolve_zero_of_source_zero g hab k p Y
    (fun v hv => by change imagPart (f (p, g.path k Y v)) = 0; rw [hf v hv, map_zero])
  simp only [complexCopyVelocity, copyVelocity, hr, hi, map_zero, smul_zero, add_zero]

theorem copyPressure_zero_of_path (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k : Frequency) (frequency : ℝ) (p : P) (Y : Plane)
    (hf : ∀ v ∈ Icc a b, t.source (p, g.path k Y v) = 0)
    (hcurrent : t.source (p, Y) = 0) : copyPressure t g hab k frequency (p, Y) = 0 := by
  have hu := t.linearData.copySolve_zero_of_source_zero g hab k p Y hf
  simp [copyPressure, copyPressureReal, hu, hcurrent, TangentProjection.pressureCoefficient]

theorem complexCopyPressure_zero_of_path (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (frequency : ℝ) (p : P) (Y : Plane)
    (hf : ∀ v ∈ Icc a b, f (p, g.path k Y v) = 0)
    (heta : (g.coordinates k Y).2 ∈ Icc a b) :
    complexCopyPressure t f g hab k frequency (p, Y) = 0 := by
  have hcurrent : f (p, Y) = 0 := by simpa only [g.path_current] using hf _ heta
  have hr := copyPressure_zero_of_path (realData t f) g hab k frequency p Y
    (fun v hv => by change realPart (f (p, g.path k Y v)) = 0; rw [hf v hv, map_zero])
    (by change realPart (f (p, Y)) = 0; rw [hcurrent, map_zero])
  have hi := copyPressure_zero_of_path (imagData t f) g hab k frequency p Y
    (fun v hv => by change imagPart (f (p, g.path k Y v)) = 0; rw [hf v hv, map_zero])
    (by change imagPart (f (p, Y)) = 0; rw [hcurrent, map_zero])
  simp only [complexCopyPressure, hr, hi, mul_zero, add_zero]

end RealityAndSupport

section CommonTorus

open CommonCoverSolve TorusInverse HarmonicCalculus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem copyVelocity_deck (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k m : Frequency) (p : P) (hp : PeriodicAt t.source p) (Y : Plane) :
    copyVelocity t g hab (k + coverIndex g.gap m) (p, Y + TorusAverages.latticePoint m) =
      copyVelocity t g hab k (p, Y) := by
  unfold copyVelocity
  rw [t.linearData.copySolve_deck g hab k m p hp Y]

theorem copyPressure_deck (t : TangentData P ProblemStatement.Space) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) (k m : Frequency) (frequency : ℝ)
    (p : P) (hp : PeriodicAt t.source p) (Y : Plane) :
    copyPressure t g hab (k + coverIndex g.gap m) frequency (p, Y + TorusAverages.latticePoint m) =
      copyPressure t g hab k frequency (p, Y) := by
  simp only [copyPressure, copyPressureReal, nativePoint, g.coordinates_deck,
    t.linearData.copySolve_deck g hab k m p hp Y, hp Y m]

theorem complexCopyVelocity_deck (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k m : Frequency) (p : P) (hp : PeriodicAt f p) (Y : Plane) :
    complexCopyVelocity t f g hab (k + coverIndex g.gap m) (p, Y + TorusAverages.latticePoint m) =
      complexCopyVelocity t f g hab k (p, Y) := by
  have hr : PeriodicAt (realData t f).source p := fun Y m => congrArg realPart (hp Y m)
  have hi : PeriodicAt (imagData t f).source p := fun Y m => congrArg imagPart (hp Y m)
  simp only [complexCopyVelocity, copyVelocity_deck _ g hab k m p hr Y,
    copyVelocity_deck _ g hab k m p hi Y]

theorem complexCopyPressure_deck (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k m : Frequency) (frequency : ℝ) (p : P) (hp : PeriodicAt f p) (Y : Plane) :
    complexCopyPressure t f g hab (k + coverIndex g.gap m) frequency (p, Y +
      TorusAverages.latticePoint m) =
      complexCopyPressure t f g hab k frequency (p, Y) := by
  have hr : PeriodicAt (realData t f).source p := fun Y m => congrArg realPart (hp Y m)
  have hi : PeriodicAt (imagData t f).source p := fun Y m => congrArg imagPart (hp Y m)
  simp only [complexCopyPressure, copyPressure_deck _ g hab k m frequency p hr Y,
    copyPressure_deck _ g hab k m frequency p hi Y]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

noncomputable def periodizedCopies (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (p : P × Plane) : H :=
  ∑' k : Frequency, κ (g.coordinates k p.2) • F k p

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
/-- Compact localization makes the displayed series an actual finite sum
at each point; no summability fallback is used by the construction. -/
theorem periodizedCopies_eq_finite_sum (g : Geometry) {κ : Plane → ℝ} (hκ : HasCompactSupport κ)
    (F : Frequency → P × Plane → H) (p : P × Plane) :
    ∃ I : Finset Frequency, periodizedCopies g κ F p = ∑ k ∈ I, κ (g.coordinates k p.2) • F k p :=
      by
  obtain ⟨I, hI⟩ := g.finite_copy_cutoffs hκ ‖p.2‖
  refine ⟨I, tsum_eq_sum (fun k hk => ?_)⟩
  rw [hI p.2 le_rfl k hk, zero_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
/-- On a plateau occupied by exactly one copy, periodization gives that
actual copy. No summability convention enters this equality. -/
theorem periodizedCopies_eq_single (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (k : Frequency) (p : P × Plane)
    (hk : κ (g.coordinates k p.2) = 1)
    (hother : ∀ l : Frequency, l ≠ k → κ (g.coordinates l p.2) = 0) :
    periodizedCopies g κ F p = F k p := by
  unfold periodizedCopies
  rw [tsum_eq_single k (fun l hl => by rw [hother l hl, zero_smul]), hk, one_smul]

omit [NormedSpace ℝ P] [CompleteSpace H] in
theorem periodizedCopies_eventuallyEq_single (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (k : Frequency) (p : P × Plane)
    (hκ : ∀ᶠ y in 𝓝 p, κ (g.coordinates k y.2) = 1 ∧
      ∀ l : Frequency, l ≠ k → κ (g.coordinates l y.2) = 0) :
    periodizedCopies g κ F =ᶠ[𝓝 p] F k := by
  filter_upwards [hκ] with y hy
  exact periodizedCopies_eq_single g κ F k y hy.1 hy.2

omit [CompleteSpace H] in
/-- Germ agreement preserves every actual Fréchet derivative, including
mixed derivatives in the slow and torus variables. -/
theorem periodizedCopies_iteratedFDeriv_eq_single (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (k : Frequency) (p : P × Plane)
    (hκ : ∀ᶠ y in 𝓝 p, κ (g.coordinates k y.2) = 1 ∧
      ∀ l : Frequency, l ≠ k → κ (g.coordinates l y.2) = 0) (m : ℕ) :
    iteratedFDeriv ℝ m (periodizedCopies g κ F) p = iteratedFDeriv ℝ m (F k) p := by
  have he := periodizedCopies_eventuallyEq_single g κ F k p hκ
  have hw : periodizedCopies g κ F =ᶠ[𝓝[univ] p] F k := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq he.self_of_nhds m

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace H] in
theorem periodizedCopies_periodic (g : Geometry) (κ : Plane → ℝ)
    (F : Frequency → P × Plane → H) (p : P)
    (hF : ∀ k m Y, F (k + coverIndex g.gap m) (p, Y + TorusAverages.latticePoint m) = F k (p, Y)) :
    PeriodicAt (periodizedCopies g κ F) p := by
  intro Y m
  unfold periodizedCopies
  calc
    _ = ∑' k : Frequency, κ (g.coordinates (k + coverIndex g.gap m) (Y + TorusAverages.latticePoint
      m)) •
        F (k + coverIndex g.gap m) (p, Y + TorusAverages.latticePoint m) :=
      ((Equiv.addRight (coverIndex g.gap m)).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [g.coordinates_deck, hF k m Y]

noncomputable def commonVelocity (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Plane → ℝ) :
    P × Plane → ComplexVector := periodizedCopies g κ (fun k => complexCopyVelocity t f g hab k)

noncomputable def commonPressure (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Plane → ℝ)
    (frequency : ℝ) : P × Plane → ℂ := periodizedCopies g κ (fun k => complexCopyPressure t f g hab
      k frequency)

theorem commonVelocity_periodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Plane → ℝ)
    (p : P) (hp : PeriodicAt f p) : PeriodicAt (commonVelocity t f g hab κ) p :=
  periodizedCopies_periodic g κ _ p (fun k m Y => complexCopyVelocity_deck t f g hab k m p hp Y)

theorem commonPressure_periodic (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (κ : Plane → ℝ)
    (frequency : ℝ) (p : P) (hp : PeriodicAt f p) : PeriodicAt (commonPressure t f g hab κ
      frequency) p :=
  periodizedCopies_periodic g κ _ p (fun k m Y => complexCopyPressure_deck t f g hab k m frequency
    p hp Y)

end CommonTorus

section IsometricCoordinates

open WeightedClasses HarmonicCalculus LinearWaveBounds

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def reindexStrip (e : E ≃ₗᵢ[ℝ] F) (s : StripData F) : StripData E where
  domain := e ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage e.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (e x)
  delta_pos := fun x hx => s.delta_pos (e x) hx
  zeta := fun x => s.zeta (e x)
  zeta_smooth := s.zeta_smooth.comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun x hx => s.zeta_nonneg (e x) hx

/-- Reassociation of coordinates preserves every actual derivative norm. -/
theorem memClass_reindex (e : E ≃ₗᵢ[ℝ] F) {s : StripData F} {w : ℕ → F → ℝ} {α : ℝ}
    {f : ℕ → F → H} (hf : MemClass s w α f) :
    MemClass (reindexStrip e s) (fun n x => w n (e x)) α (fun n x => f n (e x)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n (e x) hx,
    fun n => (hf.smooth n).comp e.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro N
  obtain ⟨C, hC, m, hb⟩ := hf.bounds N
  refine ⟨C, hC, m, ?_⟩
  intro n x hx j hj
  change ‖iteratedFDeriv ℝ j (f n ∘ e) x‖ ≤ _
  rw [e.norm_iteratedFDeriv_comp_right]
  exact hb n (e x) hx j hj

theorem waveClass_reindex (e : E ≃ₗᵢ[ℝ] F) {s : StripData F} {W : ℕ → F → ℝ} {α : ℝ}
    {f : ℕ → F → H} (hf : WaveClass s W α f) :
    WaveClass (reindexStrip e s) (fun n x => W n (e x)) α (fun n x => f n (e x)) :=
  memClass_reindex e hf

noncomputable def reindexVector (e : E ≃ₗᵢ[ℝ] F) (V : F → F) : E → E := fun x => e.symm (V (e x))

theorem along_reindex (e : E ≃ₗᵢ[ℝ] F) (V : F → F) {f : F → H} {x : E}
    (hf : DifferentiableAt ℝ f (e x)) :
    along (reindexVector e V) (fun y => f (e y)) x = along V f (e x) := by
  have hd := (hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at hd
  unfold along reindexVector
  rw [hd]
  simp

theorem phaseNormal_reindex (e : E ≃ₗᵢ[ℝ] F) (R : F → ℝ) (Vr Vθ Vz : F → F)
    {Φ : F → ℝ} {x : E} (hΦ : DifferentiableAt ℝ Φ (e x)) :
    phaseNormal (fun y => R (e y)) (reindexVector e Vr) (reindexVector e Vθ) (reindexVector e Vz)
      (fun y => Φ (e y)) x = phaseNormal R Vr Vθ Vz Φ (e x) := by
  simp only [phaseNormal, along_reindex e _ hΦ]

theorem principal_reindex (e : E ≃ₗᵢ[ℝ] F) (ε frequency : ℝ)
    (R F₀ G Φ : F → ℝ) (Vr Vθ Vz Vf : F → F) (a : F → ComplexVector) (p : F → ℂ)
    {x : E} (hF : DifferentiableAt ℝ F₀ (e x)) (hG : DifferentiableAt ℝ G (e x))
    (hΦ : DifferentiableAt ℝ Φ (e x))
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) (e x)) :
    LinearWaveResidual.principal ε frequency (fun y => R (e y)) (fun y => F₀ (e y)) (fun y => G (e
      y))
      (reindexVector e Vr) (reindexVector e Vθ) (reindexVector e Vz) (reindexVector e Vf)
      (fun y => Φ (e y)) (fun y => a (e y)) (fun y => p (e y)) x =
      LinearWaveResidual.principal ε frequency R F₀ G Vr Vθ Vz Vf Φ a p (e x) := by
  have hN := phaseNormal_reindex e R Vr Vθ Vz hΦ
  have hK : LinearWaveResidual.shear (fun y => R (e y)) (fun y => F₀ (e y)) (fun y => G (e y))
      (reindexVector e Vr) (fun y => a (e y)) x = LinearWaveResidual.shear R F₀ G Vr a (e x) := by
    simp only [LinearWaveResidual.shear, along_reindex e Vr hF, along_reindex e Vr hG]
  ext i
  simp only [LinearWaveResidual.principal, hN, hK, along_reindex e Vf (ha i)]

noncomputable def reindexCoefficients (e : E ≃ₗᵢ[ℝ] F) (a : WaveCoefficients F) : WaveCoefficients
  E where
  radius n x := a.radius n (e x)
  radialBase n x := a.radialBase n (e x)
  frequencyBase n x := a.frequencyBase n (e x)
  axialBase n x := a.axialBase n (e x)
  phase n x := a.phase n (e x)
  amplitude n x := a.amplitude n (e x)
  pressure n x := a.pressure n (e x)
  frequency := a.frequency

noncomputable def reindexDirections (e : E ≃ₗᵢ[ℝ] F) (d : GraphDirections F) : GraphDirections E
  where
  radial := e.symm d.radial
  auxiliary := e.symm d.auxiliary
  axial := e.symm d.axial
  angular := e.symm d.angular
  slow := e.symm d.slow
  fast := e.symm d.fast
  radialScale := d.radialScale
  fastScale := d.fastScale
  radialProfile := fun x => d.radialProfile (e x)

theorem reindex_radialField (e : E ≃ₗᵢ[ℝ] F) (d : GraphDirections F) (n : ℕ) :
    (reindexDirections e d).radialField n = reindexVector e (d.radialField n) := by
  funext x
  simp only [GraphDirections.radialField, reindexDirections, reindexVector, map_add, map_smul]

theorem reindex_axialField (e : E ≃ₗᵢ[ℝ] F) (d : GraphDirections F) (s : StripData F) (n : ℕ) :
    (reindexDirections e d).axialField (reindexStrip e s) n = reindexVector e (d.axialField s n) :=
      by
  funext x
  simp only [GraphDirections.axialField, reindexDirections, reindexStrip, reindexVector, map_smul]

theorem reindex_fastField (e : E ≃ₗᵢ[ℝ] F) (d : GraphDirections F) (n : ℕ) :
    (reindexDirections e d).fastField n = reindexVector e (d.fastField n) := by
  funext x
  simp only [GraphDirections.fastField, reindexDirections, reindexVector, map_smul]

/-- Explicit associator from `PressureStream.Lift S` to the common-copy
domain with slow parameter `P = ℝ × S`. -/
noncomputable def liftAssoc (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] :
    (ℝ × (S × TorusInverse.Plane)) ≃ₗᵢ[ℝ] ((ℝ × S) × TorusInverse.Plane) :=
  (LinearIsometryEquiv.prodAssoc ℝ ℝ S TorusInverse.Plane).symm

@[simp] theorem liftAssoc_apply (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S]
    (x : ℝ × (S × TorusInverse.Plane)) : liftAssoc S x = ((x.1, x.2.1), x.2.2) := rfl

end IsometricCoordinates



end NavierStokes.ParticularWaveBounds
