/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryTargetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Weighted native estimates for the constructed primary copies

The local domains retain the actual label-dependent slow cells.  Every
constant is chosen before that label, its band, and the lattice copy.  The
square-root estimates retain the vanishing flat weight.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PrimaryCopyBounds

open Set Function Filter PhaseJetBounds PrimaryPulseBounds WeightedClasses
open scoped Topology ContDiff BigOperators InnerProductSpace

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {ι : Type*} {D : Type} {E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A local chart domain with the actual slow/inverse-edge growth. -/
structure JetDomain (ι D : Type*) [NormedAddCommGroup D] extends Domain ι D where
  /-- Growth of `JetDomain`, of type `ι → D → ℝ`. -/
  growth : ι → D → ℝ
  scale_le_growth : ∀ i x, x ∈ carrier i → scale i ≤ growth i x

omit [NormedSpace ℝ D] in
theorem JetDomain.one_le_growth (V : JetDomain ι D) (i : ι) {x : D}
    (hx : x ∈ V.carrier i) : 1 ≤ V.growth i x :=
  (V.one_le_scale i).trans (V.scale_le_growth i x hx)

/-- Actual full jets on varying native cells, retaining their full weight. -/
structure NativeJets (V : JetDomain ι D) (w : ι → D → ℝ) (f : ι → D → E) : Prop where
  nonneg : ∀ i x, x ∈ V.carrier i → 0 ≤ w i x
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (V.carrier i)
  bound : ∀ m : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ i x, x ∈ V.carrier i → ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C * V.growth i x ^ p * w i x

namespace NativeJets

variable {V : JetDomain ι D} {w v : ι → D → ℝ} {f g : ι → D → E}

theorem of_envelope (hf : EnvelopeJets V.toDomain w f) : NativeJets V w f := by
  refine ⟨hf.nonneg, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C, hC, p, ?_⟩
  intro i x hx j hj
  exact (hb i x hx j hj).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_scale i)) (V.scale_le_growth i x hx) p)
      (zero_le_one.trans hC)) (hf.nonneg i x hx))

theorem of_polynomial (hf : PolynomialJets V.toDomain f) :
    NativeJets V (fun _ _ => 1) f := of_envelope (EnvelopeJets.of_polynomial hf)

theorem congr (hf : NativeJets V w f) (he : ∀ i, EqOn (f i) (g i) (V.carrier i)) :
    NativeJets V w g := by
  refine ⟨hf.nonneg, fun i => (hf.smooth i).congr (fun _ hx => (he i hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C, hC, p, ?_⟩
  intro i x hx j hj
  have hjet := iteratedFDerivWithin_congr (𝕜 := ℝ) (he i) hx j
  rw [iteratedFDerivWithin_of_isOpen j (V.isOpen i) hx,
    iteratedFDerivWithin_of_isOpen j (V.isOpen i) hx] at hjet
  rw [← hjet]
  exact hb i x hx j hj

theorem map (hf : NativeJets V w f) (L : E →L[ℝ] F) :
    NativeJets V w (fun i x => L (f i x)) := by
  refine ⟨hf.nonneg, fun i => L.contDiff.comp_contDiffOn (hf.smooth i), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨(‖L‖ + 1) * C, one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg L]) hC, p, ?_⟩
  intro i x hx j hj
  have hc := L.iteratedFDeriv_comp_left
    ((hf.smooth i).contDiffAt ((V.isOpen i).mem_nhds hx)) (nat_le_infty j)
  change ‖iteratedFDeriv ℝ j (L ∘ f i) x‖ ≤ _
  rw [hc]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ (‖L‖ + 1) * (C * V.growth i x ^ p * w i x) :=
      mul_le_mul (by linarith) (hb i x hx j hj) (norm_nonneg _)
        (by linarith [norm_nonneg L])
    _ = _ := by ring

theorem add (hf : NativeJets V w f) (hg : NativeJets V w g) :
    NativeJets V w (fun i x => f i x + g i x) := by
  refine ⟨hf.nonneg, fun i => (hf.smooth i).add (hg.smooth i), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bound m
  obtain ⟨B, hB, q, hb⟩ := hg.bound m
  refine ⟨A + B, by linarith, p + q, ?_⟩
  intro i x hx j hj
  have hG := V.one_le_growth i hx
  have hw := hf.nonneg i x hx
  rw [fun_iteratedFDeriv_add_apply
    (((hf.smooth i).contDiffAt ((V.isOpen i).mem_nhds hx)).of_le (nat_le_infty j))
    (((hg.smooth i).contDiffAt ((V.isOpen i).mem_nhds hx)).of_le (nat_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f i) x‖ + ‖iteratedFDeriv ℝ j (g i) x‖ := norm_add_le _ _
    _ ≤ A * V.growth i x ^ p * w i x + B * V.growth i x ^ q * w i x :=
      add_le_add (ha i x hx j hj) (hb i x hx j hj)
    _ ≤ A * V.growth i x ^ (p + q) * w i x + B * V.growth i x ^ (p + q) * w i x := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hG (Nat.le_add_right p q)) (zero_le_one.trans hA)) hw)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hG (Nat.le_add_left q p)) (zero_le_one.trans hB)) hw)
    _ = _ := by ring

theorem neg (hf : NativeJets V w f) : NativeJets V w (fun i x => -f i x) :=
  hf.map (-ContinuousLinearMap.id ℝ E)

theorem sub (hf : NativeJets V w f) (hg : NativeJets V w g) :
    NativeJets V w (fun i x => f i x - g i x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem bilinear {f : ι → D → E} {g : ι → D → F}
    (hf : NativeJets V w f) (hg : NativeJets V v g) (L : E →L[ℝ] F →L[ℝ] G) :
    NativeJets V (fun i x => w i x * v i x) (fun i x => L (f i x) (g i x)) := by
  refine ⟨fun i x hx => mul_nonneg (hf.nonneg i x hx) (hg.nonneg i x hx),
    fun i => (L.contDiff.comp_contDiffOn (hf.smooth i)).clm_apply (hg.smooth i), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bound m
  obtain ⟨B, hB, q, hb⟩ := hg.bound m
  refine ⟨(‖L‖ + 1) * 2 ^ m * A * B, ?_, p + q, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by
            linarith [norm_nonneg L]) (one_le_pow₀ (by norm_num))) hA) hB
  intro i x hx j hj
  have hG : 0 ≤ V.growth i x := zero_le_one.trans (V.one_le_growth i hx)
  have hw := hf.nonneg i x hx
  have hv := hg.nonneg i x hx
  have h := LabelSumBounds.bilinear_jet_bound L (V.isOpen i) (hf.smooth i) (hg.smooth i) hx hj
    (by positivity : 0 ≤ A * V.growth i x ^ p * w i x)
    (by positivity : 0 ≤ B * V.growth i x ^ q * v i x)
    (ha i x hx) (hb i x hx)
  calc
    _ ≤ ‖L‖ * 2 ^ m * (A * V.growth i x ^ p * w i x) *
        (B * V.growth i x ^ q * v i x) := h
    _ ≤ (‖L‖ + 1) * 2 ^ m * (A * V.growth i x ^ p * w i x) *
        (B * V.growth i x ^ q * v i x) := by gcongr; linarith
    _ = _ := by rw [pow_add]; ring

theorem mul {f g : ι → D → ℝ} (hf : NativeJets V w f) (hg : NativeJets V v g) :
    NativeJets V (fun i x => w i x * v i x) (fun i x => f i x * g i x) :=
  hf.bilinear hg (ContinuousLinearMap.mul ℝ ℝ)

theorem smul {f : ι → D → ℝ} {g : ι → D → E}
    (hf : NativeJets V w f) (hg : NativeJets V v g) :
    NativeJets V (fun i x => w i x * v i x) (fun i x => f i x • g i x) :=
  hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem polynomial_smul {a : ι → D → ℝ} (hf : NativeJets V w f)
    (ha : PolynomialJets V.toDomain a) :
    NativeJets V w (fun i x => a i x • f i x) := by
  simpa only [one_mul] using (of_polynomial ha).smul hf

theorem polynomial_mul {f a : ι → D → ℝ} (hf : NativeJets V w f)
    (ha : PolynomialJets V.toDomain a) :
    NativeJets V w (fun i x => a i x * f i x) := by
  simpa only [smul_eq_mul] using hf.polynomial_smul ha

theorem band_smul (hf : NativeJets V w f) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    NativeJets V (fun i x => a i * w i x) (fun i x => a i • f i x) := by
  refine ⟨fun i x hx => mul_nonneg (ha i) (hf.nonneg i x hx),
    fun i => (hf.smooth i).const_smul _, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bound m
  refine ⟨C, hC, p, ?_⟩
  intro i x hx j hj
  rw [iteratedFDeriv_const_smul_apply'
    (((hf.smooth i).contDiffAt ((V.isOpen i).mem_nhds hx)).of_le (nat_le_infty j)),
    norm_smul (a i) (iteratedFDeriv ℝ j (f i) x), Real.norm_of_nonneg (ha i)]
  exact (mul_le_mul_of_nonneg_left (hb i x hx j hj) (ha i)).trans_eq (by ring)

/-- The exact square root of a vanishing weight is retained.  The lower
bound is proportional to that weight; no positive minimum is introduced. -/
theorem sqrt {g : ι → D → ℝ} (hg : NativeJets V w g)
    (hw : ∀ i x, x ∈ V.carrier i → 0 < w i x)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ i x, x ∈ V.carrier i → c * w i x ≤ g i x) :
    NativeJets V (fun i x => Real.sqrt (w i x)) (fun i x => Real.sqrt (g i x)) := by
  have hpos : ∀ i x, x ∈ V.carrier i → 0 < g i x :=
    fun i x hx => (mul_pos hc (hw i x hx)).trans_le (hlower i x hx)
  refine ⟨fun _ _ _ => Real.sqrt_nonneg _,
    fun i => (hg.smooth i).sqrt (fun x hx => (hpos i x hx).ne'), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hg.bound m
  let K := C + c⁻¹ + 1
  have hK : 1 ≤ K := by dsimp [K]; have := inv_pos.mpr hc; linarith
  have hCK : C ≤ K := by dsimp [K]; have := inv_pos.mpr hc; linarith
  have hiK : c⁻¹ ≤ K := by dsimp [K]; linarith
  let A := WeightedQuotients.orderBound (1 / 2) m + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [WeightedQuotients.orderBound_nonneg (1 / 2) m]
  refine ⟨A * K ^ (2 * m + 1), one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hK),
    p * (2 * m + 1), ?_⟩
  intro i x hx j hj
  have hG := V.one_le_growth i hx
  let B := K * V.growth i x ^ p
  have hKB : K ≤ B := le_mul_of_one_le_right (zero_le_one.trans hK) (one_le_pow₀ hG)
  have hB : 1 ≤ B := hK.trans hKB
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hcb : 1 ≤ c * B := by
    have h : 1 / c ≤ B := by simpa only [one_div] using hiK.trans hKB
    simpa only [mul_comm] using (div_le_iff₀ hc).mp h
  have hlo : w i x / B ≤ g i x := by
    apply (div_le_iff₀ hBpos).mpr
    calc
      w i x = w i x * 1 := (mul_one _).symm
      _ ≤ w i x * (c * B) := mul_le_mul_of_nonneg_left hcb (hw i x hx).le
      _ = (c * w i x) * B := by ring
      _ ≤ g i x * B := mul_le_mul_of_nonneg_right (hlower i x hx) hBpos.le
  have hjets : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (g i) x‖ ≤ w i x * B := by
    intro k hk
    exact (hb i x hx k (hk.trans hj)).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK
        (pow_nonneg (zero_le_one.trans hG) _)) (hw i x hx).le).trans_eq (by dsimp [B]; ring))
  have h := WeightedQuotients.sqrt_jet_bound (V.isOpen i) (hg.smooth i)
    (hpos i) hx (hw i x hx) hB j hlo hjets
  have hjA : (j.factorial : ℝ) * WeightedQuotients.coeffBound (1 / 2) j ≤ A :=
    (WeightedQuotients.orderBound_le (1 / 2) hj).trans (by dsimp [A]; linarith)
  calc
    _ ≤ Real.sqrt (w i x) * ((j.factorial : ℝ) * WeightedQuotients.coeffBound (1 / 2) j) * B ^ (2 *
        j + 1) := h
    _ ≤ Real.sqrt (w i x) * A * B ^ (2 * m + 1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hjA (Real.sqrt_nonneg _)
      · exact pow_le_pow_right₀ hB (by omega)
      · positivity
      · positivity
    _ = _ := by dsimp [B]; rw [mul_pow, ← pow_mul]; ring

end NativeJets

section Covariance

variable {V : JetDomain ι D} {w : ι → D → ℝ}
  {r : ι → ℝ} {H : ι → D → SmoothCovariance.Mat2}
  {T : ι → D → SmoothCovariance.Vec2}

/-- Cramer's actual formula on the varying native cells.  Only the
normalized matrix has a positive lower bound; the target keeps its weight. -/
theorem covariance_weights_jets
    (hr : PolynomialJets V.toDomain (fun i _ => r i)) (hrne : ∀ i, r i ≠ 0)
    (hH : ∀ k l, PolynomialJets V.toDomain (fun i x => H i x k l))
    (hT : ∀ k, NativeJets V w (fun i x => T i x k))
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    (hdet : ∀ i x, x ∈ V.carrier i → b ≤ |(normalizedMatrix (r i) (H i x)).det|)
    (hentry : ∀ i x, x ∈ V.carrier i → ∀ k l, |r i * H i x k l| ≤ M)
    (j : Fin 2) : NativeJets V w (fun i x => SmoothCovariance.weights (H i x) (T i x) j) := by
  have hN (k l : Fin 2) := hr.mul (hH k l)
  have hD : PolynomialJets V.toDomain (fun i x => (normalizedMatrix (r i) (H i x)).det) := by
    simpa only [Matrix.det_fin_two, normalizedMatrix] using
      ((hN 0 0).mul (hN 1 1)).sub ((hN 0 1).mul (hN 1 0))
  have hDupper : ∀ i x, x ∈ V.carrier i → |(normalizedMatrix (r i) (H i x)).det| ≤ 2 * M ^ 2 := by
    intro i x hx
    simp only [Matrix.det_fin_two, normalizedMatrix]
    apply (abs_sub _ _).trans
    have h1 := mul_le_mul (hentry i x hx 0 0) (hentry i x hx 1 1)
      (abs_nonneg _) (zero_le_one.trans hM)
    have h2 := mul_le_mul (hentry i x hx 0 1) (hentry i x hx 1 0)
      (abs_nonneg _) (zero_le_one.trans hM)
    simp only [abs_mul] at h1 h2 ⊢
    nlinarith
  have hi := hD.inv hb hdet hDupper
  have hscale := (hr.pow 2).mul hi
  have hP (k l j : Fin 2) : NativeJets V w (fun i x => T i x j * H i x k l) := by
    simpa only [mul_comm] using (hT j).polynomial_mul (hH k l)
  have hnum : NativeJets V w (fun i x => SmoothCovariance.cramerNumerator (H i x) (T i x) j) := by
    fin_cases j
    · have he := (hP 1 1 0).sub (hP 0 1 1)
      simp only [SmoothCovariance.cramerNumerator, mul_comm] at he ⊢
      exact he
    · have he := (hP 0 0 1).sub (hP 1 0 0)
      simp only [SmoothCovariance.cramerNumerator,
        mul_comm] at he ⊢
      exact he
  apply (hnum.polynomial_mul hscale).congr
  intro i x hx
  apply (weights_eq_normalized (r i) (H i x) (T i x) (hrne i) _ j).symm
  intro he
  have h := hdet i x hx
  rw [normalizedMatrix_det, he, mul_zero, abs_zero] at h
  linarith

theorem covariance_amplitudes_jets
    (hr : PolynomialJets V.toDomain (fun i _ => r i)) (hrne : ∀ i, r i ≠ 0)
    (hH : ∀ k l, PolynomialJets V.toDomain (fun i x => H i x k l))
    (hT : ∀ k, NativeJets V w (fun i x => T i x k))
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hdet : ∀ i x, x ∈ V.carrier i → b ≤ |(normalizedMatrix (r i) (H i x)).det|)
    (hentry : ∀ i x, x ∈ V.carrier i → ∀ k l, |r i * H i x k l| ≤ M)
    (hw : ∀ i x, x ∈ V.carrier i → 0 < w i x)
    (hlower : ∀ i x, x ∈ V.carrier i → ∀ k, c * w i x ≤ SmoothCovariance.weights (H i x) (T i x) k)
    (j : Fin 2) :
    NativeJets V (fun i x => Real.sqrt (w i x)) (fun i x => SmoothCovariance.amplitudes (H i x) (T
        i x) j) :=
  (covariance_weights_jets hr hrne hH hT hb hM hdet hentry j).sqrt hw hc
    (fun i x hx => hlower i x hx j)

end Covariance

section Pressure

variable {V : JetDomain ι D} {w : ι → D → ℝ}

theorem pressureCoefficient_jets
    {N Ndot u : ι → D → ProblemStatement.Space}
    {A : ι → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
    (hN : PolynomialJets V.toDomain N) (hNdot : PolynomialJets V.toDomain Ndot)
    (hA : PolynomialJets V.toDomain A) (hu : NativeJets V w u)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ i x, x ∈ V.carrier i → b ≤ ‖N i x‖)
    (hhi : ∀ i x, x ∈ V.carrier i → ‖N i x‖ ≤ M) :
    NativeJets V w (fun i x => TangentProjection.pressureCoefficient
      (N i x) (Ndot i x) (u i x) (A i x (u i x)) 0) := by
  have hNsq := hN.inner hN
  have hInv := hNsq.inv (b := b ^ 2) (M := M ^ 2) (sq_pos_of_pos hb)
    (by
      intro i x hx
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hb.le (hlo i x hx) 2)
    (by
      intro i x hx
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hhi i x hx) 2)
  have hAu : NativeJets V w (fun i x => A i x (u i x)) := by
    have he := (NativeJets.of_polynomial hA).bilinear hu
      (ContinuousLinearMap.apply ℝ ProblemStatement.Space).flip
    simp only [one_mul] at he
    exact he
  have hnum : NativeJets V w (fun i x => ⟪N i x, A i x (u i x)⟫_ℝ - ⟪Ndot i x, u i x⟫_ℝ) := by
    have h1 := (NativeJets.of_polynomial hN).bilinear hAu (innerSL ℝ)
    have h2 := (NativeJets.of_polynomial hNdot).bilinear hu (innerSL ℝ)
    have he := h1.sub h2
    simp only [one_mul] at he
    exact he
  simpa only [TangentProjection.pressureCoefficient, inner_zero_right, add_zero,
    real_inner_self_eq_norm_sq, div_eq_mul_inv, mul_comm] using hnum.polynomial_mul hInv

end Pressure

section ConstructedPulse

variable {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}

/-- Pulse matrix, defined pointwise by `primaryCovariance pref (fun j => (F j).frame) (fun j =>
(F j).lam) (fun j => (F j).u) (fun j => (F j).L) i (χ i x).1`. -/
noncomputable def pulseMatrix (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → D → PhaseCalculus.Slow × ℝ) :
    ι → D → SmoothCovariance.Mat2 := fun i x =>
  primaryCovariance pref (fun j => (F j).frame) (fun j => (F j).lam)
    (fun j => (F j).u) (fun j => (F j).L) i (χ i x).1

/-- Pulse vector, defined pointwise by `normalizedPulse ((F j).frame i) ((F j).lam i) ((F j).u
i) ((F j).L i) (χ i x)`. -/
noncomputable def pulseVector (F : Fin 2 → PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ι → D → ProblemStatement.Space :=
  fun i x => normalizedPulse ((F j).frame i) ((F j).lam i) ((F j).u i) ((F j).L i) (χ i x)

/-- Pulse envelope, defined pointwise by `referenceP ((F j).lam i) ((F j).u i) ((F j).L i) ((F
j).L i * (χ i x).2)`. -/
noncomputable def pulseEnvelope (F : Fin 2 → PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) : ι → D → ℝ := fun i x =>
  referenceP ((F j).lam i) ((F j).u i) ((F j).L i) ((F j).L i * (χ i x).2)

/-- Primary velocity, defined pointwise by `PartitionedCovariance.amplitude (ε i) (mask i x)
(pulseMatrix F pref χ i x) (T i x) j • pulseVector F χ j i x`. -/
noncomputable def primaryVelocity (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → D → PhaseCalculus.Slow × ℝ) (ε : ι → ℝ)
    (T : ι → D → SmoothCovariance.Vec2) (mask : ι → D → ℝ) (j : Fin 2) :
    ι → D → ProblemStatement.Space := fun i x =>
  PartitionedCovariance.amplitude (ε i) (mask i x) (pulseMatrix F pref χ i x) (T i x) j •
    pulseVector F χ j i x

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem primaryVelocity_mask_mul (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → D → PhaseCalculus.Slow × ℝ) (ε : ι → ℝ)
    (T : ι → D → SmoothCovariance.Vec2) (mask κ : ι → D → ℝ) (j : Fin 2) (i : ι) (x : D) :
    primaryVelocity F pref χ ε T (fun i x => κ i x * mask i x) j i x =
      κ i x • primaryVelocity F pref χ ε T mask j i x := by
  simp only [primaryVelocity, PartitionedCovariance.amplitude, smul_smul]
  congr 1
  ring

theorem primaryVelocity_complexify {U : Domain ℕ PhaseCalculus.Slow}
    (s : StripData D) (F : Fin 2 → PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (T : ℕ → D → SmoothCovariance.Vec2)
    (mask : ℕ → D → ℝ) (j : Fin 2) (n : ℕ) (x : D) :
    CurlClassBounds.complexify (primaryVelocity F pref χ s.epsilon T mask j n x) =
      PrimaryPulseBounds.uncutPrimaryWave s pref (fun j => (F j).frame)
        (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L) χ T mask j n x := by
  simp only [primaryVelocity, map_smul, PrimaryPulseBounds.uncutPrimaryWave,
    primaryCoefficient, chartCovariance, pulseMatrix, pulseVector]

theorem pulseMatrix_jets (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i)
    (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → (χ i x).1 ∈ U.carrier i)
    (hpref : ∀ j, PolynomialJets U (fun i _ => pref j i)) (j k : Fin 2) :
    PolynomialJets V.toDomain (fun i x => pulseMatrix F pref χ i x j k) := by
  exact ((EnvelopeJets.of_polynomial (primaryCovariance_entry_polynomial U pref
    (fun j => (F j).frame) (fun j => (F j).lam) (fun j => (F j).u) (fun j => (F j).L)
    hpref (fun j => (F j).pulse_jets) (fun j => (F j).lam_pos)
    (fun j => (F j).u_pos) (fun j => (F j).L_pos) j k)).comp
      (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale hmap).to_polynomial
        (fun _ _ _ => le_rfl)

theorem pulseVector_jets (F : Fin 2 → PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i)
    (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1)
    (j : Fin 2) : NativeJets V (pulseEnvelope F χ j) (pulseVector F χ j) :=
  NativeJets.of_envelope ((F j).pulse_jets.comp hχ hscale hmap)

theorem sqrt_scale_jets (V : JetDomain ι D) :
    PolynomialJets V.toDomain (fun i _ => Real.sqrt (V.scale i)) := by
  apply PolynomialJets.const (C := 1) (m := 1) _ le_rfl
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul, pow_one]
  have h := V.one_le_scale i
  have hn := Real.sqrt_nonneg (V.scale i)
  have hs := Real.sq_sqrt (zero_le_one.trans h)
  nlinarith

/-- The native primary is the actual homogeneous Volterra pulse, scaled
by the actual Cramer square root and physical square-root epsilon factor. -/
theorem primaryVelocity_jets (F : Fin 2 → PhaseConstruction U)
    (pref : Fin 2 → ι → ℝ) (χ : ι → D → PhaseCalculus.Slow × ℝ) (ε : ι → ℝ)
    (T : ι → D → SmoothCovariance.Vec2) (mask : ι → D → ℝ) (ζ : ι → D → ℝ)
    (hscale : ∀ i, U.scale i = V.scale i)
    (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1)
    (hpref : ∀ j, PolynomialJets U (fun i _ => pref j i))
    (hT : ∀ k, NativeJets V ζ (fun i x => T i x k))
    (hm : PolynomialJets V.toDomain mask)
    (hζ : ∀ i x, x ∈ V.carrier i → 0 < ζ i x)
    {b M c : ℝ} (hb : 0 < b) (hM : 1 ≤ M) (hc : 0 < c)
    (hzero : ∀ i x, x ∈ V.carrier i →
      PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (V.scale i)) b M c (ζ i x)
        (pulseMatrix F pref χ i x) (T i x)) (j : Fin 2) :
    NativeJets V (fun i x => Real.sqrt (ε i) * (Real.sqrt (ζ i x) * pulseEnvelope F χ j i x))
      (primaryVelocity F pref χ ε T mask j) := by
  have hr := sqrt_scale_jets V
  have hrne (i : ι) : Real.sqrt (V.scale i) ≠ 0 :=
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le (V.one_le_scale i))).ne'
  have hH := pulseMatrix_jets F pref χ hscale hχ (fun i x hx => (hmap i x hx).1) hpref
  have hw := covariance_amplitudes_jets hr hrne hH hT hb hM hc
    (fun i x hx => (hzero i x hx).determinant)
    (fun i x hx => (hzero i x hx).entries) hζ
    (fun i x hx k => (hzero i x hx).weight_lower
      (Real.one_le_sqrt.mpr (V.one_le_scale i)) hc.le (hζ i x hx).le k) j
  have hu := (hw.smul (pulseVector_jets F χ hscale hχ hmap j)).polynomial_smul hm
  apply (hu.band_smul (fun i => Real.sqrt (ε i)) (fun i => Real.sqrt_nonneg _)).congr
  intro i x hx
  simp only [primaryVelocity, PartitionedCovariance.amplitude, smul_smul]
  congr 1
  ring

end ConstructedPulse

namespace NativeJets

variable {V : JetDomain ι D} {w : ι → D → ℝ} {f : ι → D → E}

theorem constant_weight (a : ι → E) (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    {C : ℝ} (hC : 1 ≤ C) (p : ℕ)
    (ha : ∀ i, ‖a i‖ ≤ C * V.scale i ^ p * v i) :
    NativeJets V (fun i _ => v i) (fun i _ => a i) := by
  refine ⟨fun i _ _ => hv i, fun _ => contDiffOn_const, fun _ => ⟨C, hC, p, ?_⟩⟩
  intro i x hx j _
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact (ha i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (V.one_le_scale i)) (V.scale_le_growth i x hx) p)
        (zero_le_one.trans hC)) (hv i))
  | succ j =>
    rw [iteratedFDeriv_succ_const]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hC)
      (pow_nonneg (zero_le_one.trans (V.one_le_growth i hx)) _)) (hv i)

/-- A compactly contained outer cutoff extends the true native function.
Every cutoff derivative is included in the product estimate. -/
theorem localize {V' : JetDomain ι D} {a : ι → D → ℝ}
    (hf : NativeJets V w f) (ha : PolynomialJets V'.toDomain a)
    (hscale : ∀ i, V'.scale i = V.scale i)
    (hsub : ∀ i, V.carrier i ⊆ V'.carrier i)
    (hgrowth : ∀ i x, x ∈ V.carrier i → V.growth i x = V'.growth i x)
    (hw : ∀ i x, x ∈ V'.carrier i → 0 ≤ w i x)
    (hsupport : ∀ i, tsupport (a i) ∩ V'.carrier i ⊆ V.carrier i) :
    NativeJets V' w (fun i x => a i x • f i x) := by
  have ha' : PolynomialJets V.toDomain a := by
    refine ⟨fun i => (ha.smooth i).mono (hsub i), ?_⟩
    intro m
    obtain ⟨C, hC, p, hb⟩ := ha.bound m
    exact ⟨C, hC, p, fun i j hj x hx => by simpa only [hscale] using hb i j hj x (hsub i hx)⟩
  have hp := hf.polynomial_smul ha'
  have hout (i : ι) (x : D) (hx : x ∈ V'.carrier i) (hn : x ∉ V.carrier i) :
      (fun y => a i y • f i y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
    have ht : x ∉ tsupport (a i) := fun ht => hn (hsupport i ⟨ht, hx⟩)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]
  refine ⟨hw, ?_, ?_⟩
  · intro i x hx
    by_cases hi : x ∈ V.carrier i
    · exact ((hp.smooth i).contDiffAt ((V.isOpen i).mem_nhds hi)).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hout i x hx hi)).contDiffWithinAt
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hp.bound m
    refine ⟨C, hC, p, ?_⟩
    intro i x hx j hj
    by_cases hi : x ∈ V.carrier i
    · simpa only [hgrowth i x hi] using hb i x hi j hj
    · rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq (hout i x hx hi) j,
        iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC)
        (pow_nonneg (zero_le_one.trans (V'.one_le_growth i hx)) _)) (hw i x hx)

end NativeJets

section PressureGain

variable {V : JetDomain ι D} {w : ι → D → ℝ}

/-- The literal projected pressure gains the inverse-carrier half power.
The source is homogeneous, so its pressure source term is exactly zero. -/
theorem projectedPressure_jets
    {N Ndot u : ι → D → ProblemStatement.Space}
    {A : ι → D → ProblemStatement.Space →L[ℝ] ProblemStatement.Space}
    (hN : PolynomialJets V.toDomain N) (hNdot : PolynomialJets V.toDomain Ndot)
    (hA : PolynomialJets V.toDomain A) (hu : NativeJets V w u)
    {b M : ℝ} (hb : 0 < b)
    (hlo : ∀ i x, x ∈ V.carrier i → b ≤ ‖N i x‖)
    (hhi : ∀ i x, x ∈ V.carrier i → ‖N i x‖ ≤ M)
    (ε frequency : ι → ℝ) (hε : ∀ i, 0 < ε i)
    {C : ℝ} (hC : 1 ≤ C) (p : ℕ)
    (hfrequency : ∀ i, |1 / frequency i| ≤ C * V.scale i ^ p * Real.sqrt (ε i)) :
    NativeJets V (fun i x => Real.sqrt (ε i) * w i x)
      (fun i => ParticularWaveBounds.projectedPressure (frequency i) (N i) (Ndot i)
        (u i) (fun x => A i x (u i x)) (fun _ => 0)) := by
  have hpc := pressureCoefficient_jets hN hNdot hA hu hb hlo hhi
  let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM
  have hcomplex := hpc.map L
  have hfreq : NativeJets V (fun i _ => Real.sqrt (ε i)) (fun i _ => 1 / frequency i) :=
    NativeJets.constant_weight _ _ (fun i => (Real.sqrt_pos.mpr (hε i)).le) hC p
      (fun i => by simpa only [Real.norm_eq_abs] using hfrequency i)
  apply (hfreq.smul hcomplex).congr
  intro i x hx
  simp [ParticularWaveBounds.projectedPressure, L, Complex.real_smul, div_eq_mul_inv, mul_comm]

end PressureGain

section NativePressure

variable {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}

/-- The actual phase is evaluated at the physical native time `L*tau`. -/
noncomputable def phasePoint (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) : ι → D → PhaseCalculus.Slow × ℝ :=
  fun i x => ((χ i x).1, p.L i * (χ i x).2)

/-- Phase pressure as an element of `ι → D → ℂ`. -/
noncomputable def phasePressure (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (frequency : ι → ℝ)
    (u : ι → D → ProblemStatement.Space) : ι → D → ℂ := fun i =>
  ParticularWaveBounds.projectedPressure (frequency i)
    (fun x => p.phase.normal i (phasePoint p χ i x))
    (fun x => p.phase.velocity i (phasePoint p χ i x))
    (u i)
    (fun x => PrimaryCopyBridge.baseOperator (p.phase.F i (χ i x).1)
      (p.phase.shear i (phasePoint p χ i x)) (u i x))
    (fun _ => 0)

theorem phasePoint_jets (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i) (hχ : PolynomialJets V.toDomain χ) :
    PolynomialJets V.toDomain (phasePoint p χ) := by
  have hL : PolynomialJets V.toDomain (fun i _ => p.L i) := by
    apply PolynomialJets.const (C := p.M) (m := 1) _ p.one_le_M
    intro i
    simpa only [Real.norm_eq_abs, pow_one, ← hscale] using
      p.slot i (p.L i) (p.interval i ⟨p.L_pos i |>.le, le_rfl⟩)
  exact (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)).pair
    (hL.mul (hχ.clm (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow ℝ)))

omit [NormedSpace ℝ D] in
theorem phasePoint_maps (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1) :
    ∀ i x, x ∈ V.carrier i → phasePoint p χ i x ∈ (U.slot p.V p.openV).carrier i := by
  intro i x hx
  refine ⟨(hmap i x hx).1, p.interval i ?_⟩
  have ht := (hmap i x hx).2
  exact ⟨mul_nonneg (p.L_pos i).le ht.1.le,
    (mul_le_mul_of_nonneg_left ht.2.le (p.L_pos i).le).trans_eq (mul_one _)⟩

/-- Phase-normal, normal-motion and shear estimates all come from the
same base and phase construction as the true homogeneous pulse. -/
theorem phasePressure_jets (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i) (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1)
    {w : ι → D → ℝ} {u : ι → D → ProblemStatement.Space}
    (hu : NativeJets V w u)
    (ε frequency : ι → ℝ) (hε : ∀ i, 0 < ε i)
    {C : ℝ} (hC : 1 ≤ C) (q : ℕ)
    (hfrequency : ∀ i, |1 / frequency i| ≤ C * V.scale i ^ q * Real.sqrt (ε i)) :
    NativeJets V (fun i x => Real.sqrt (ε i) * w i x) (phasePressure p χ frequency u) := by
  have hp := phasePoint_jets p χ hscale hχ
  have hm := phasePoint_maps p χ hmap
  have hbase := p.phase.polynomial_jets U p.V p.openV p.baseF p.baseG
    p.r_pos p.one_le_M p.constants p.epsilon_ne p.radius p.slot
  have hN := ((EnvelopeJets.of_polynomial hbase.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hNd := ((EnvelopeJets.of_polynomial hbase.2.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hs := ((EnvelopeJets.of_polynomial hbase.2.2).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hF := ((EnvelopeJets.of_polynomial p.baseF).comp
    (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale
    (fun i x hx => (hmap i x hx).1)).to_polynomial (fun _ _ _ => le_rfl)
  have hA := (hF.pair hs).clm PrimaryCopyBridge.baseOperatorFamily
  exact projectedPressure_jets hN hNd hA hu p.b_pos
    (fun i x hx => p.normal_range.1 i _ (hm i x hx))
    (fun i x hx => p.normal_range.2 i _ (hm i x hx)) ε frequency hε hC q hfrequency

/-- The rounded carrier gives the claimed half-power without a frequency
bound supplied by the caller. -/
theorem phasePressure_carrier_jets (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i) (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1)
    {w : ι → D → ℝ} {u : ι → D → ProblemStatement.Space}
    (hu : NativeJets V w u) (h : ℝ) (hh : 0 ≤ h) (band : ι → ℕ) :
    NativeJets V (fun i x => Real.sqrt (ChartScales.epsilon h (band i)) * w i x)
      (phasePressure p χ (fun i => (ChartScales.carrier h (band i) : ℝ)) u) := by
  apply phasePressure_jets p χ hscale hχ hmap hu
    (fun i => ChartScales.epsilon h (band i)) _ (fun i => ChartScales.epsilon_pos h (band i))
    (C := 1) le_rfl 0
  intro i
  rw [pow_zero, mul_one, one_mul, abs_of_nonneg (by
      positivity : 0 ≤ 1 / (ChartScales.carrier h (band i) : ℝ))]
  exact (ChartScales.carrier_inv_bounds h hh (band i)).2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem phasePressure_smul (p : PhaseConstruction U)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (frequency : ι → ℝ)
    (a : ι → D → ℝ) (u : ι → D → ProblemStatement.Space) (i : ι) (x : D) :
    phasePressure p χ frequency (fun i x => a i x • u i x) i x =
      a i x • phasePressure p χ frequency u i x := by
  simp only [phasePressure, ParticularWaveBounds.projectedPressure,
    TangentProjection.pressureCoefficient, map_smul, real_inner_smul_right,
    inner_zero_right, add_zero, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.real_smul]
  ring

end NativePressure

/-! ### The actual outer slot cutoff -/

/-- Outer bump, bundling `rIn`, `rOut`, `rIn_pos`, `rIn_lt_rOut`. -/
noncomputable def outerBump : ContDiffBump (1 / 2 : ℝ) where
  rIn := 3 / 8
  rOut := 5 / 12
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Outer cutoff, given by `outerBump`. -/
noncomputable def outerCutoff : ℝ → ℝ := outerBump

theorem outerCutoff_smooth : ContDiff ℝ ∞ outerCutoff := outerBump.contDiff

theorem outerCutoff_support : tsupport outerCutoff ⊆ Icc (1 / 12 : ℝ) (11 / 12) := by
  rw [show tsupport outerCutoff = Metric.closedBall (1 / 2 : ℝ) (5 / 12) from outerBump.tsupport_eq]
  intro t ht
  have h : |t - 1 / 2| ≤ 5 / 12 := by simpa only [Metric.mem_closedBall, Real.dist_eq] using ht
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem outerCutoff_one {t : ℝ} (ht : |t - 1 / 2| ≤ 1 / 3) : outerCutoff t = 1 := by
  apply outerBump.one_of_mem_closedBall
  change dist t (1 / 2) ≤ 3 / 8
  rw [Real.dist_eq]
  linarith

theorem profile_mul_outerCutoff (t : ℝ) :
    GaussianTailFlat.profile t * outerCutoff t = GaussianTailFlat.profile t := by
  by_cases h : |t - 1 / 2| ≤ 1 / 3
  · rw [outerCutoff_one h, mul_one]
  · rw [GaussianTailFlat.profile_zero (le_of_not_ge h), zero_mul]

theorem outerCutoff_jet_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ m outerCutoff t‖ ≤ C := by
  have hs := outerBump.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) m
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous
    (outerCutoff_smooth.continuous_iteratedFDeriv (nat_le_infty m))
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

theorem affine_profile_jets (U : Domain ι D) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hjets : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ m f t‖ ≤ C)
    (L : ι → D →L[ℝ] ℝ) (c : ι → ℝ) {K : ℝ} (hK : 1 ≤ K) (q : ℕ)
    (hL : ∀ i, ‖L i‖ ≤ K * U.scale i ^ q) :
    PolynomialJets U (fun i x => f (L i x + c i)) := by
  refine ⟨fun i => (hf.comp ((L i).contDiff.add contDiff_const)).contDiffOn, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := GaussianTailFlat.finite_jet_bounds hjets m
  refine ⟨(C + 1) * K ^ m, one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hK), q * m, ?_⟩
  intro i j hj x hx
  have hSK : 1 ≤ K * U.scale i ^ q :=
    one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ (U.one_le_scale i))
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f (L i x + c i)‖ * ‖L i‖ ^ j :=
      norm_jet_comp_affine isOpen_univ hf.contDiffOn (L i) (c i) (mem_univ _) j
    _ ≤ (C + 1) * (K * U.scale i ^ q) ^ m :=
      mul_le_mul ((hb j hj _).trans (by linarith))
        ((pow_le_pow_left₀ (norm_nonneg _) (hL i) j).trans (pow_le_pow_right₀ hSK hj))
        (by positivity) (by linarith)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem outerCutoff_affine_jets (U : Domain ι D) (L : ι → D →L[ℝ] ℝ)
    (c : ι → ℝ) {K : ℝ} (hK : 1 ≤ K) (q : ℕ)
    (hL : ∀ i, ‖L i‖ ≤ K * U.scale i ^ q) :
    PolynomialJets U (fun i x => outerCutoff (L i x + c i)) :=
  affine_profile_jets U outerCutoff outerCutoff_smooth outerCutoff_jet_bounded L c hK q hL

theorem gaussianCutoff_affine_jets (U : Domain ι D) (L : ι → D →L[ℝ] ℝ)
    (c : ι → ℝ) {K : ℝ} (hK : 1 ≤ K) (q : ℕ)
    (hL : ∀ i, ‖L i‖ ≤ K * U.scale i ^ q) :
    PolynomialJets U (fun i x => GaussianTailFlat.profile (L i x + c i)) :=
  affine_profile_jets U GaussianTailFlat.profile GaussianTailFlat.profile_contDiff
    GaussianTailFlat.profile_jet_bounded L c hK q hL

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The outer extension never inserts a second Gaussian cutoff. -/
theorem gaussian_outer_primary (u : D → E) (τ : D → ℝ) :
    (fun x => GaussianTailFlat.profile (τ x) • (outerCutoff (τ x) • u x)) =
      (fun x => GaussianTailFlat.profile (τ x) • u x) := by
  funext x
  rw [smul_smul, profile_mul_outerCutoff]

theorem outerCutoff_affine_support (L : D →L[ℝ] ℝ) (c : ℝ) :
    tsupport (fun x => outerCutoff (L x + c)) ⊆ {x | L x + c ∈ Ioo (0 : ℝ) 1} := by
  have hs : tsupport (fun x => outerCutoff (L x + c)) ⊆
      {x | L x + c ∈ Icc (1 / 12 : ℝ) (11 / 12)} := by
    apply closure_minimal _ (isClosed_Icc.preimage (L.continuous.add continuous_const))
    intro x hx
    exact outerCutoff_support (subset_tsupport outerCutoff hx)
  intro x hx
  have h := hs hx
  constructor <;> linarith [h.1, h.2]

/-- The actual outer cutoff permits a larger native domain while retaining
the uncut fundamental's Gaussian envelope and flat weight. -/
theorem outer_localized_jets {V V' : JetDomain ι D} {w : ι → D → ℝ} {f : ι → D → E}
    (hf : NativeJets V w f) (L : ι → D →L[ℝ] ℝ) (c : ι → ℝ)
    {K : ℝ} (hK : 1 ≤ K) (q : ℕ) (hL : ∀ i, ‖L i‖ ≤ K * V'.scale i ^ q)
    (hscale : ∀ i, V'.scale i = V.scale i)
    (hsub : ∀ i, V.carrier i ⊆ V'.carrier i)
    (hgrowth : ∀ i x, x ∈ V.carrier i → V.growth i x = V'.growth i x)
    (hinside : ∀ i x, x ∈ V'.carrier i → L i x + c i ∈ Ioo (0 : ℝ) 1 → x ∈ V.carrier i)
    (hw : ∀ i x, x ∈ V'.carrier i → 0 ≤ w i x) :
    NativeJets V' w (fun i x => outerCutoff (L i x + c i) • f i x) := by
  apply hf.localize (outerCutoff_affine_jets V'.toDomain L c hK q hL) hscale hsub hgrowth hw
  intro i x hx
  exact hinside i x hx.2 (outerCutoff_affine_support (L i) (c i) hx.1)

/-! ### Transfer to the actual copy coordinates -/

section Copies

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Λ I : Type*} {V : JetDomain ι D} {w : ι → D → ℝ} {f : ι → D → E}

/-- Affine copy, defined pointwise by `f (index l n) (L l n i x + c l n i)`. -/
noncomputable def affineCopy (f : ι → D → E) (index : Λ → ℕ → ι)
    (L : Λ → ℕ → I → X →L[ℝ] D) (c : Λ → ℕ → I → D) : Λ → ℕ → I → X → E :=
  fun l n i x => f (index l n) (L l n i x + c l n i)

/-- The copy translation is arbitrary.  Only the linear part's uniform
polynomial size matters, so the constants precede the lattice index. -/
theorem NativeJets.copy_localJets (hf : NativeJets V w f)
    (s : StripData X) (W : Λ → ℕ → X → ℝ) (α : ℝ)
    (index : Λ → ℕ → ι) (L : Λ → ℕ → I → X →L[ℝ] D) (c : Λ → ℕ → I → D)
    (K : Λ → ℕ → I → Set X)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hmap : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      L l n i x + c l n i ∈ V.carrier (index l n))
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (a b : ℕ)
    (hgrowth : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      V.growth (index l n) (L l n i x + c l n i) ≤ A * s.growth n x ^ a)
    (hlinear : ∀ l n i, ‖L l n i‖ ≤ B * s.slow n ^ b)
    (hweight : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      w (index l n) (L l n i x + c l n i) ≤ s.epsilon n ^ α * W l n x) :
    PeriodizedWaveBounds.UniformLocalJets s W α K (affineCopy f index L c) := by
  refine ⟨?_, ?_⟩
  · intro l n i x hx hk
    exact ((hf.smooth (index l n)).contDiffAt
      ((V.isOpen (index l n)).mem_nhds (hmap l n i x hx hk))).comp x
        (((L l n i).contDiff.add contDiff_const).contDiffAt)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bound m
    refine ⟨C * A ^ p * B ^ m, by positivity, a * p + b * m, ?_⟩
    intro l n i x hx hk j hj
    have hG := s.one_le_growth n x
    have hW0 := hW l n x hx
    have heps := (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le
    have ht := hmap l n i x hx hk
    have hGN := V.one_le_growth (index l n) ht
    have hBs : 1 ≤ B * s.slow n ^ b :=
      one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ (s.one_le_slow n))
    have hL : ‖L l n i‖ ^ j ≤ B ^ m * s.growth n x ^ (b * m) := by
      calc
        _ ≤ (B * s.slow n ^ b) ^ m :=
          (pow_le_pow_left₀ (norm_nonneg _) (hlinear l n i) j).trans (pow_le_pow_right₀ hBs hj)
        _ ≤ (B * s.growth n x ^ b) ^ m := by
          apply pow_le_pow_left₀ (zero_le_one.trans hBs)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) b)
            (zero_le_one.trans hB)
        _ = _ := by rw [mul_pow, ← pow_mul]
    have hu := norm_jet_comp_affine (V.isOpen (index l n)) (hf.smooth (index l n))
      (L l n i) (c l n i) ht j
    change ‖iteratedFDeriv ℝ j (fun x => f (index l n) (L l n i x + c l n i)) x‖ ≤ _
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (f (index l n)) (L l n i x + c l n i)‖ * ‖L l n i‖ ^ j := hu
      _ ≤ (C * V.growth (index l n) (L l n i x + c l n i) ^ p *
          w (index l n) (L l n i x + c l n i)) * (B ^ m * s.growth n x ^ (b * m)) :=
        mul_le_mul (hb _ _ ht j hj) hL (by positivity)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hGN) _))
            (hf.nonneg _ _ ht))
      _ ≤ (C * (A * s.growth n x ^ a) ^ p * (s.epsilon n ^ α * W l n x)) *
          (B ^ m * s.growth n x ^ (b * m)) := by
        gcongr
        · exact hf.nonneg _ _ ht
        · exact hgrowth l n i x hx hk
        · exact hweight l n i x hx hk
      _ = majorant s (W l) α (C * A ^ p * B ^ m) (a * p + b * m) n x := by
        rw [majorant, mul_pow, ← pow_mul, pow_add]
        ring

/-- A literal cutoff times the native function gives its own support
proof.  Local finiteness and uniqueness then retain the very same uniform
constants in the actual infinite copy sum. -/
theorem NativeJets.localized_copy_sum_uniformClass (hf : NativeJets V w f)
    (s : StripData X) (W : Λ → ℕ → X → ℝ) (α : ℝ)
    (κ : ι → D → ℝ) (hκ : PolynomialJets V.toDomain κ)
    (index : Λ → ℕ → ι) (L : Λ → ℕ → I → X →L[ℝ] D) (c : Λ → ℕ → I → D)
    (K : Λ → PeriodizedWaveBounds.Cells X I)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hcut : ∀ l n i x, κ (index l n) (L l n i x + c l n i) ≠ 0 → x ∈ (K l).carrier n i)
    (hmap : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      L l n i x + c l n i ∈ V.carrier (index l n))
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (a b : ℕ)
    (hgrowth : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      V.growth (index l n) (L l n i x + c l n i) ≤ A * s.growth n x ^ a)
    (hlinear : ∀ l n i, ‖L l n i‖ ≤ B * s.slow n ^ b)
    (hweight : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      w (index l n) (L l n i x + c l n i) ≤ s.epsilon n ^ α * W l n x) :
    LabelSumBounds.UniformClass s W α
      (fun l n => PeriodizedWaveBounds.copySum
        (affineCopy (fun i x => κ i x • f i x) index L c l n)) := by
  apply PeriodizedWaveBounds.copySum_uniformClass K hW
  · intro l n i x hx
    apply hcut l n i x
    intro he
    exact hx (by simp only [affineCopy, he, zero_smul])
  · exact (hf.polynomial_smul hκ).copy_localJets s W α index L c
      (fun l => (K l).carrier) hW hmap hA hB a b hgrowth hlinear hweight

/-- The explicit outer slot bump is included in the differentiated
cutoff.  This endpoint assumes support only of the scalar cutoffs. -/
theorem NativeJets.outer_copy_sum_uniformClass (hf : NativeJets V w f)
    (s : StripData X) (W : Λ → ℕ → X → ℝ) (α : ℝ)
    (κ : ι → D → ℝ) (hκ : PolynomialJets V.toDomain κ)
    (τ : ι → D →L[ℝ] ℝ) (t0 : ι → ℝ) {H : ℝ} (hH : 1 ≤ H) (q : ℕ)
    (hτ : ∀ i, ‖τ i‖ ≤ H * V.scale i ^ q)
    (index : Λ → ℕ → ι) (L : Λ → ℕ → I → X →L[ℝ] D) (c : Λ → ℕ → I → D)
    (K : Λ → PeriodizedWaveBounds.Cells X I)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hcut : ∀ l n i x, κ (index l n) (L l n i x + c l n i) ≠ 0 →
      outerCutoff (τ (index l n) (L l n i x + c l n i) + t0 (index l n)) ≠ 0 →
        x ∈ (K l).carrier n i)
    (hmap : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      L l n i x + c l n i ∈ V.carrier (index l n))
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (a b : ℕ)
    (hgrowth : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      V.growth (index l n) (L l n i x + c l n i) ≤ A * s.growth n x ^ a)
    (hlinear : ∀ l n i, ‖L l n i‖ ≤ B * s.slow n ^ b)
    (hweight : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      w (index l n) (L l n i x + c l n i) ≤ s.epsilon n ^ α * W l n x) :
    LabelSumBounds.UniformClass s W α
      (fun l n => PeriodizedWaveBounds.copySum
        (affineCopy (fun i x => (κ i x * outerCutoff (τ i x + t0 i)) • f i x) index L c l n)) := by
  apply hf.localized_copy_sum_uniformClass s W α
    (fun i x => κ i x * outerCutoff (τ i x + t0 i))
    (hκ.mul (outerCutoff_affine_jets V.toDomain τ t0 hH q hτ)) index L c K hW
    _ hmap hA hB a b hgrowth hlinear hweight
  intro l n i x hx
  exact hcut l n i x (mul_ne_zero_iff.mp hx).1 (mul_ne_zero_iff.mp hx).2

end Copies

namespace NativeJets

variable {V : JetDomain ι D} {w : ι → D → ℝ} {f : ι → D → E}

/-- Order-by-order bounds give one bound for each finite jet, with the
constant still preceding the native label. -/
theorem of_order (hw : ∀ i x, x ∈ V.carrier i → 0 ≤ w i x)
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (V.carrier i))
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ i x, x ∈ V.carrier i →
      ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C * V.growth i x ^ p * w i x) :
    NativeJets V w f := by
  refine ⟨hw, hs, ?_⟩
  intro m
  induction m with
  | zero =>
    obtain ⟨C, hC, p, hp⟩ := hb 0
    refine ⟨C + 1, by linarith, p, ?_⟩
    intro i x hx j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hp i x hx).trans (by
      apply mul_le_mul_of_nonneg_right _ (hw i x hx)
      exact mul_le_mul_of_nonneg_right (by linarith)
        (pow_nonneg (zero_le_one.trans (V.one_le_growth i hx)) p))
  | succ m ih =>
    obtain ⟨A, hA, p, ha⟩ := ih
    obtain ⟨B, hB, q, hq⟩ := hb (m + 1)
    refine ⟨A + B, by linarith, p + q, ?_⟩
    intro i x hx j hj
    have hG := V.one_le_growth i hx
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact (ha i x hx j (Nat.le_of_lt_succ hj)).trans (by
        apply mul_le_mul_of_nonneg_right _ (hw i x hx)
        exact mul_le_mul (by linarith) (pow_le_pow_right₀ hG (Nat.le_add_right p q))
          (pow_nonneg (zero_le_one.trans hG) p) (by linarith))
    · exact (hq i x hx).trans (by
        apply mul_le_mul_of_nonneg_right _ (hw i x hx)
        exact mul_le_mul (by linarith) (pow_le_pow_right₀ hG (Nat.le_add_left q p))
          (pow_nonneg (zero_le_one.trans hG) q) (by linarith))

/-- Genuine chain-rule estimates with point-dependent edge growth. -/
theorem comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : JetDomain ι X} {v : ι → X → ℝ} {g : ι → X → E}
    (hg : NativeJets U v g) {χ : ι → D → X}
    (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i, MapsTo (χ i) (V.carrier i) (U.carrier i))
    (hG : ∀ i x, x ∈ V.carrier i → U.growth i (χ i x) ≤ V.growth i x) :
    NativeJets V (fun i x => v i (χ i x)) (fun i x => g i (χ i x)) := by
  refine ⟨fun i x hx => hg.nonneg i _ (hmap i hx),
    fun i => (hg.smooth i).comp (hχ.smooth i) (hmap i), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hg.bound m
  obtain ⟨B, hB, q, hb⟩ := hχ.bound m
  refine ⟨(m.factorial : ℝ) * A * B ^ m, ?_, p + q * m, ?_⟩
  · have hfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfac hA)
      (one_le_pow₀ hB)
  intro i x hx j hj
  have hgrowth := V.one_le_growth i hx
  have hCG : 1 ≤ B * V.growth i x ^ q :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hgrowth)
  have hw := hg.nonneg i (χ i x) (hmap i hx)
  have h := norm_iteratedFDerivWithin_comp_le (hg.smooth i) (hχ.smooth i)
    (nat_le_infty j) (U.isOpen i).uniqueDiffOn (V.isOpen i).uniqueDiffOn (hmap i) hx
    (C := A * V.growth i x ^ p * v i (χ i x)) (D := B * V.growth i x ^ q)
    (fun a haj => ?_) (fun a ha1 haj => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j (V.isOpen i) hx] at h
    change ‖iteratedFDeriv ℝ j (g i ∘ χ i) x‖ ≤ _
    have hA0 : 0 ≤ A * V.growth i x ^ p * v i (χ i x) := by positivity
    calc
      _ ≤ (j.factorial : ℝ) * (A * V.growth i x ^ p * v i (χ i x)) *
          (B * V.growth i x ^ q) ^ j := h
      _ ≤ (m.factorial : ℝ) * (A * V.growth i x ^ p * v i (χ i x)) *
          (B * V.growth i x ^ q) ^ m := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA0
        · exact pow_le_pow_right₀ hCG hj
        · positivity
        · positivity
      _ = _ := by rw [mul_pow, pow_add, pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen a (U.isOpen i) (hmap i hx)]
    exact (ha i _ (hmap i hx) a (haj.trans hj)).trans (by
      apply mul_le_mul_of_nonneg_right _ hw
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hA)
      exact pow_le_pow_left₀ (zero_le_one.trans (U.one_le_growth i (hmap i hx))) (hG i x hx) p)
  · rw [iteratedFDerivWithin_of_isOpen a (V.isOpen i) hx]
    exact (hb i a (haj.trans hj) x hx).trans ((by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hB)
      exact pow_le_pow_left₀ (zero_le_one.trans (V.one_le_scale i))
        (V.scale_le_growth i x hx) q : B * V.scale i ^ q ≤ B * V.growth i x ^ q).trans
      (by simpa using pow_le_pow_right₀ hCG ha1))

end NativeJets

/-! ### The same-profile prepared construction -/

section Prepared

variable {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
  (H₀ : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v₀ : ModulatedProfileAssembly.Witness ld)

/-- The full open active annulus, retaining the inverse edge distance. -/
noncomputable def leadingDomain (W : NominalProfile.Witness F₀) (ι : Type*) :
    JetDomain ι SlowBorelBase.Inner where
  carrier := fun _ => Ioo (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W) ×ˢ Ioo (-1 : ℝ) 1
  isOpen := fun _ => isOpen_Ioo.prod isOpen_Ioo
  scale := fun _ => 1
  one_le_scale := fun _ => le_rfl
  growth := fun _ x => max 1 (FinalSlowBase.edgeDistance W x)⁻¹
  scale_le_growth := fun _ _ _ => le_max_left _ _

theorem leadingDomain_mem_annulus (i : ι) {x : SlowBorelBase.Inner}
    (hx : x ∈ (leadingDomain W₀ ι).carrier i) : x ∈ FinalSlowBase.annulus W₀ :=
  ⟨hx.1, hx.2.1.le, hx.2.2.le⟩

/-- The native target estimate is derived from the actual constructed
profile.  The flat weight can approach zero at either edge. -/
theorem leadingStress_nativeJets (hcone : LeadingStressWeights.FullTrueCone v₀) :
    NativeJets (leadingDomain W₀ ι) (fun _ => FinalSlowBase.weight W₀)
      (fun _ => FinalSlowBase.leadingStress v₀) := by
  have hweight (i : ι) (x : SlowBorelBase.Inner)
      (hx : x ∈ (leadingDomain W₀ ι).carrier i) : 0 ≤ FinalSlowBase.weight W₀ x := by
    apply (ActiveAnnulusWeight.radialWeight_pos ?_).le
    have hm := leadingDomain_mem_annulus i hx
    rw [FinalSlowBase.annulus_eq] at hm
    exact hm.1
  apply NativeJets.of_order hweight
  · intro i x hx
    exact (FinalSlowBase.leadingStress_smoothAt v₀
      ((NominalConeAssembly.activeLeft_pos W₀).trans hx.1.1)
      ⟨hx.2.1.le, hx.2.2.le⟩).contDiffWithinAt
  · intro m
    obtain ⟨C, hC, p, hb⟩ := FinalSlowBase.leading_radial_jets v₀ hcone m
    refine ⟨C, hC.le, p, ?_⟩
    intro i x hx
    have he := BaseResidual.activeDelta_bounds
      (show x ∈ BaseResidual.activeWindow (FinalSlowBase.logLeft W₀)
        (FinalSlowBase.logRight W₀) from by
        rw [← FinalSlowBase.annulus_eq]
        exact leadingDomain_mem_annulus i hx)
    calc
      _ ≤ C * FinalSlowBase.weight W₀ x * (FinalSlowBase.edgeDistance W₀ x)⁻¹ ^ p :=
        hb x (leadingDomain_mem_annulus i hx)
      _ = C * (FinalSlowBase.edgeDistance W₀ x)⁻¹ ^ p * FinalSlowBase.weight W₀ x := by ring
      _ ≤ C * (leadingDomain W₀ ι).growth i x ^ p * FinalSlowBase.weight W₀ x := by
        apply mul_le_mul_of_nonneg_right _ (hweight i x hx)
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact pow_le_pow_left₀ (inv_nonneg.mpr he.1.le) (le_max_right _ _) p

/-- Actual normalized leading stress on a native slow domain, from only
pointwise chart geometry and the inverse-edge growth comparison. -/
theorem actualTarget_jets (hcone : LeadingStressWeights.FullTrueCone v₀)
    (V : JetDomain ι PhaseCalculus.Slow) {r M qlo qhi : ℝ}
    (hr : 0 < r) (hqlo : 0 < qlo)
    (hgeom : BaseChartJets.GeometryBounds V.toDomain F₀.data.h r M qlo qhi
      (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀))
    (hedge : ∀ i p, p ∈ V.carrier i →
      (FinalSlowBase.edgeDistance W₀ (BaseChartJets.normalizedCoordinates F₀.data.h p).2)⁻¹ ≤
        V.growth i p) :
    NativeJets V (fun _ => PrimaryTargetBounds.movingWeight W₀)
      (fun _ => PrimaryTargetBounds.actualTarget v₀) := by
  have hcoord := BaseChartJets.polynomial_of_unit
    (BaseChartJets.normalizedCoordinates_polynomial F₀.data.h_pos F₀.data.h_lt_half hqlo hgeom)
  have hinner := hcoord.clm (ContinuousLinearMap.snd ℝ ℝ SlowBorelBase.Inner)
  have hmap (i : ι) : MapsTo (fun p => (BaseChartJets.normalizedCoordinates F₀.data.h p).2)
      (V.carrier i) ((leadingDomain W₀ ι).carrier i) := by
    intro p hp
    exact ⟨hgeom.x_range i p hp, abs_lt.mp (BaseChartJets.normalizedCoordinates_eta
      F₀.data.h_pos F₀.data.h_lt_half (hgeom.time i p hp))⟩
  have hlead := (leadingStress_nativeJets (ι := ι) v₀ hcone).comp hinner hmap
    (fun i p hp => max_le (V.one_le_growth i hp) (hedge i p hp))
  have hplane := hlead.map MovingFrameODE.pairCLM
  have hq := hcoord.clm (ContinuousLinearMap.fst ℝ ℝ SlowBorelBase.Inner)
  have hpower : PolynomialJets V.toDomain (fun _ p =>
      (BaseChartJets.normalizedCoordinates F₀.data.h p).1 ^ (-CoordinateAlgebra.A F₀.data.h - 1/2))
          := by
    apply hq.compact_comp isOpen_Ioi
      (show ContDiffOn ℝ ∞ (fun x : ℝ => x ^ (-CoordinateAlgebra.A F₀.data.h - 1/2))
        (Ioi 0) from fun x hx => (contDiffAt_id.rpow_const_of_ne hx.ne').contDiffWithinAt)
      isCompact_Icc (fun x hx => hqlo.trans_le hx.1)
    · intro i p hp
      exact ⟨(hgeom.q_range i p hp).1.le, (hgeom.q_range i p hp).2.le⟩
  have hactual : NativeJets V
      (fun _ p => FinalSlowBase.weight W₀ (BaseChartJets.normalizedCoordinates F₀.data.h p).2)
      (fun _ => PrimaryTargetBounds.actualTarget v₀) := by
    apply (hplane.polynomial_smul hpower).congr
    intro i p hp
    rfl
  refine ⟨fun i p hp => PrimaryTargetBounds.movingWeight_nonneg W₀ p, hactual.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, q, hb⟩ := hactual.bound m
  refine ⟨C, hC, q, ?_⟩
  intro i p hp j hj
  rw [PrimaryTargetBounds.movingWeight_eq W₀ (hgeom.time i p hp) (hr.trans_le (hgeom.radius i p
      hp))]
  exact hb i p hp j hj

/-- Prepared prefactor, constructed using `PartitionedCovariance.nativePrefactor`. -/
noncomputable def preparedPrefactor (r0 : ℝ) (vr vt : TorusInverse.Plane) {N : ℕ}
    (_j : Fin 2) (L : PrimaryGeometryAssembly.Index W₀ N) : ℝ :=
  PartitionedCovariance.nativePrefactor vr vt r0 *
    ChartScales.timeCoefficient F₀.data.h (BaseChartJets.cellBand L) *
      ChartScales.slotLength r0 F₀.data.h (BaseChartJets.cellBand L)

theorem preparedPrefactor_eq (r0 : ℝ) (vr vt : TorusInverse.Plane) {N : ℕ}
    (j : Fin 2) (L : PrimaryGeometryAssembly.Index W₀ N) :
    preparedPrefactor r0 vr vt j L = PartitionedCovariance.nativePrefactor vr vt r0 * (2 * r0) := by
  unfold preparedPrefactor ChartScales.slotLength
  field_simp [(ChartScales.timeCoefficient_pos F₀.data.h (BaseChartJets.cellBand L)).ne']

theorem preparedPrefactor_jets (r0 : ℝ) (vr vt : TorusInverse.Plane) (N : ℕ) (j : Fin 2) :
    PolynomialJets (PrimaryGeometryAssembly.domain W₀ N)
      (fun L _ => preparedPrefactor r0 vr vt j L) := by
  simpa only [preparedPrefactor_eq] using
    (PolynomialJets.const_fixed (D := PrimaryGeometryAssembly.domain W₀ N)
      (PartitionedCovariance.nativePrefactor vr vt r0 * (2 * r0)))

/-- The determinant, entry and inverse-weight constants are produced by
the actual same-profile construction before the label and copy chart are
chosen.  The target is the literal leading stress of that same profile. -/
theorem exists_prepared_primary_jets
    (hcone : LeadingStressWeights.FullTrueCone v₀) (upper : ℝ) (B : ℕ)
    (r0 : ℝ) (hr0 : 0 < r0)
    (hbox : 2 * NominalConeAssembly.activeRight W₀ ≤ FinalSlowBase.boxRadius W₀ upper)
    (N0 : ℕ) (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0,
      ∀ (V : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) D)
        (χ : PrimaryGeometryAssembly.Index W₀ a.N → D → PhaseCalculus.Slow × ℝ)
        (mask : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ),
      (∀ L, (PrimaryGeometryAssembly.domain W₀ a.N).scale L = V.scale L) →
      PolynomialJets V.toDomain χ →
      (∀ L x, x ∈ V.carrier L →
        χ L x ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L ×ˢ Ioo (0 : ℝ) 1) →
      (∀ L x, x ∈ V.carrier L → (χ L x).1 ∈
        PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀)) →
      (∀ k, NativeJets V (fun L x => PrimaryTargetBounds.movingWeight W₀ (χ L x).1)
        (fun L x => PrimaryTargetBounds.actualTarget v₀ (χ L x).1 k)) →
      PolynomialJets V.toDomain mask →
      (∀ L x, x ∈ V.carrier L → 0 < PrimaryTargetBounds.movingWeight W₀ (χ L x).1) →
      ∀ j : Fin 2,
      NativeJets V
        (fun L x => Real.sqrt (ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L)) *
          (Real.sqrt (PrimaryTargetBounds.movingWeight W₀ (χ L x).1) *
            pulseEnvelope (PrimaryGeometryAssembly.construction H₀ v₀ a hr0) χ j L x))
        (primaryVelocity (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
          (preparedPrefactor r0 vr vt) χ
          (fun L => ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L))
          (fun L x k => PrimaryTargetBounds.actualTarget v₀ (χ L x).1 k) mask j) := by
  obtain ⟨a, dg, eb, il, hdg, heb, hil, hz⟩ := PrimaryTargetBounds.exists_constructed_bounds
    H₀ v₀ hcone upper B r0 hr0 hbox N0 vr vt hdet
  refine ⟨a, ?_⟩
  intro V χ mask hscale hχ hmap hpositive hT hm hw j
  apply primaryVelocity_jets (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
    (preparedPrefactor r0 vr vt) χ
    (fun L => ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L))
    (fun L x k => PrimaryTargetBounds.actualTarget v₀ (χ L x).1 k) mask
    (fun L x => PrimaryTargetBounds.movingWeight W₀ (χ L x).1)
    hscale hχ hmap (fun j => preparedPrefactor_jets r0 vr vt a.N j)
    hT hm hw hdg heb hil _ j
  intro L x hx
  have h := hz L (χ L x).1 (hpositive L x hx) (hmap L x hx).1
  have hsc : V.scale L = ChartScales.S (BaseChartJets.cellBand L) := (hscale L).symm
  simp only [hsc, pulseMatrix] at h ⊢
  exact h

/-- The final native primary estimate has no target-jet premise: the
actual leading target is pulled back from its proved profile estimates.
The remaining chart hypotheses are pointwise geometry and polynomial
jets of the primitive coordinate map and scalar mask. -/
theorem exists_prepared_pair_jets
    (hcone : LeadingStressWeights.FullTrueCone v₀) (upper : ℝ) (B : ℕ)
    (r0 : ℝ) (hr0 : 0 < r0)
    (hbox : 2 * NominalConeAssembly.activeRight W₀ ≤ FinalSlowBase.boxRadius W₀ upper)
    (N0 : ℕ) (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0,
      ∀ (V : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) D)
        (S : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) PhaseCalculus.Slow)
        (χ : PrimaryGeometryAssembly.Index W₀ a.N → D → PhaseCalculus.Slow × ℝ)
        (mask : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ)
        (r M qlo qhi : ℝ),
      (∀ L, (PrimaryGeometryAssembly.domain W₀ a.N).scale L = V.scale L) →
      PolynomialJets V.toDomain χ →
      (∀ L x, x ∈ V.carrier L →
        χ L x ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L ×ˢ Ioo (0 : ℝ) 1) →
      (∀ L x, x ∈ V.carrier L → (χ L x).1 ∈
        PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀)) →
      (∀ L x, x ∈ V.carrier L → (χ L x).1 ∈ S.carrier L) →
      (∀ L x, x ∈ V.carrier L → S.growth L (χ L x).1 ≤ V.growth L x) →
      0 < r → 0 < qlo →
      BaseChartJets.GeometryBounds S.toDomain F₀.data.h r M qlo qhi
        (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀) →
      (∀ L p, p ∈ S.carrier L →
        (FinalSlowBase.edgeDistance W₀ (BaseChartJets.normalizedCoordinates F₀.data.h p).2)⁻¹ ≤
          S.growth L p) →
      PolynomialJets V.toDomain mask →
      ∀ j : Fin 2,
      let ε := fun L : PrimaryGeometryAssembly.Index W₀ a.N =>
        ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L)
      let F := PrimaryGeometryAssembly.construction H₀ v₀ a hr0
      let u := primaryVelocity F (preparedPrefactor r0 vr vt) χ ε
        (fun L x k => PrimaryTargetBounds.actualTarget v₀ (χ L x).1 k) mask j
      let w := fun L x => Real.sqrt (PrimaryTargetBounds.movingWeight W₀ (χ L x).1) *
        pulseEnvelope F χ j L x
      NativeJets V (fun L x => Real.sqrt (ε L) * w L x) u ∧
      NativeJets V (fun L x => ε L * w L x)
        (phasePressure (F j) χ
          (fun L => (ChartScales.carrier F₀.data.h (BaseChartJets.cellBand L) : ℝ)) u) := by
  obtain ⟨a, ha⟩ := exists_prepared_primary_jets (D := D) H₀ v₀ hcone upper B r0 hr0 hbox N0 vr vt
      hdet
  refine ⟨a, ?_⟩
  intro V S χ mask r M qlo qhi hscale hχ hmap hpositive hS hgrowth hr hqlo hgeom hedge hmask j
  dsimp only
  have ht := (actualTarget_jets v₀ hcone S hr hqlo hgeom hedge).comp
    (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hS hgrowth
  have htarget (k : Fin 2) :
      NativeJets V (fun L x => PrimaryTargetBounds.movingWeight W₀ (χ L x).1)
        (fun L x => PrimaryTargetBounds.actualTarget v₀ (χ L x).1 k) :=
    ht.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) k)
  have hw (L : PrimaryGeometryAssembly.Index W₀ a.N) (x : D) (hx : x ∈ V.carrier L) :
      0 < PrimaryTargetBounds.movingWeight W₀ (χ L x).1 := by
    have hs := hS L x hx
    rw [PrimaryTargetBounds.movingWeight_eq W₀ (hgeom.time L _ hs)
      (hr.trans_le (hgeom.radius L _ hs))]
    apply ActiveAnnulusWeight.radialWeight_pos
    simp only [FinalSlowBase.logLeft, FinalSlowBase.logRight,
      Real.exp_log (NominalConeAssembly.activeLeft_pos W₀),
      Real.exp_log (FinalSlowBase.terminal_pos W₀)]
    exact hgeom.x_range L _ hs
  have hu := ha V χ mask hscale hχ hmap hpositive htarget hmask hw j
  refine ⟨hu, ?_⟩
  have hp := phasePressure_carrier_jets (PrimaryGeometryAssembly.construction H₀ v₀ a hr0 j)
    χ hscale hχ hmap hu F₀.data.h F₀.data.h_pos.le BaseChartJets.cellBand
  have he : (fun L x => Real.sqrt (ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L)) *
      (Real.sqrt (ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L)) *
        (Real.sqrt (PrimaryTargetBounds.movingWeight W₀ (χ L x).1) *
          pulseEnvelope (PrimaryGeometryAssembly.construction H₀ v₀ a hr0) χ j L x))) =
      (fun L x => ChartScales.epsilon F₀.data.h (BaseChartJets.cellBand L) *
        (Real.sqrt (PrimaryTargetBounds.movingWeight W₀ (χ L x).1) *
          pulseEnvelope (PrimaryGeometryAssembly.construction H₀ v₀ a hr0) χ j L x)) := by
    funext L x
    rw [← mul_assoc, Real.mul_self_sqrt (ChartScales.epsilon_pos F₀.data.h _).le]
  rw [he] at hp
  exact hp

end Prepared

/-! ### Actual slow-mask jets and zero germs -/

/-- Position continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def positionCLM : PhaseCalculus.Slow →L[ℝ] SlotColoring.Position :=
  LinearMap.toContinuousLinearMap {
    toFun := PrimaryRepresentatives.position
    map_add' := by intro x y; ext j; fin_cases j <;> rfl
    map_smul' := by intro c x; ext j; fin_cases j <;> rfl }

theorem norm_positionCLM_le : ‖positionCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  fin_cases j
  · exact norm_fst_le x
  · exact (norm_fst_le x.2).trans (norm_snd_le x)
  · exact (norm_snd_le x.2).trans (norm_snd_le x)

/-- All derivatives of the actual squared-partition mask have uniform
polynomial bounds, including every grid node. -/
theorem nativeMask_jets (U : Domain ι PhaseCalculus.Slow)
    (band : ι → ℕ) (grid : ι → SlotColoring.Grid)
    (hband : ∀ i, 1 ≤ band i) (hscale : ∀ i, U.scale i = ChartScales.S (band i)) :
    PolynomialJets U (fun i => PrimaryRepresentatives.nativeMask (band i) (grid i)) := by
  let V : JetDomain ι PhaseCalculus.Slow := {
    toDomain := U
    growth := fun i _ => U.scale i
    scale_le_growth := fun _ _ _ => le_rfl }
  have hb : NativeJets V (fun _ _ => 1)
      (fun i => PrimaryRepresentatives.nativeMask (band i) (grid i)) := by
    apply NativeJets.of_order (fun _ _ _ => zero_le_one)
      (fun i => (PrimaryRepresentatives.nativeMask_smooth (band i) (grid i)).contDiffOn)
    intro m
    obtain ⟨C, hC, hjet⟩ := SquaredPartition.slowMask_all_jet_bounds m
    refine ⟨C, hC.le, 3 * m, ?_⟩
    intro i x hx
    calc
      _ ≤ ‖iteratedFDeriv ℝ m (SquaredPartition.slowMask (band i) (grid i))
          (positionCLM x)‖ * ‖positionCLM‖ ^ m :=
        norm_jet_comp_linear isOpen_univ (SquaredPartition.slowMask_smooth _ _).contDiffOn
          positionCLM (mem_univ _) m
      _ ≤ (C * ChartScales.S (band i) ^ (3 * m)) * 1 :=
        mul_le_mul (hjet (band i) (hband i) (grid i) (positionCLM x))
          (pow_le_one₀ (norm_nonneg _) norm_positionCLM_le) (by positivity)
          (mul_nonneg hC.le (pow_nonneg (ChartScales.S_pos (hband i)).le _))
      _ = C * V.growth i x ^ (3 * m) * 1 := by simp only [V, hscale]
  refine ⟨hb.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hp⟩ := hb.bound m
  exact ⟨C, hC, p, fun i j hj x hx => by simpa only [V, mul_one] using hp i x hx j hj⟩

theorem nativeMask_comp_jets (U : Domain ι D)
    (χ : ι → D → PhaseCalculus.Slow) (hχ : PolynomialJets U χ)
    (band : ι → ℕ) (grid : ι → SlotColoring.Grid)
    (hband : ∀ i, 1 ≤ band i) (hscale : ∀ i, U.scale i = ChartScales.S (band i)) :
    PolynomialJets U (fun i x => PrimaryRepresentatives.nativeMask (band i) (grid i) (χ i x)) := by
  let S : Domain ι PhaseCalculus.Slow := {
    carrier := fun _ => univ
    isOpen := fun _ => isOpen_univ
    scale := U.scale
    one_le_scale := U.one_le_scale }
  exact ((EnvelopeJets.of_polynomial (nativeMask_jets S band grid hband hscale)).comp
    hχ (fun _ => rfl) (fun _ _ _ => mem_univ _)).to_polynomial (fun _ _ _ => le_rfl)

/-- Off the actual label's enlarged slow cell, its mask has a zero germ.
This is the extension fact needed before applying whole-torus copy bounds. -/
theorem preparedMask_zero_germ {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
    {N : ℕ} (L : PrimaryGeometryAssembly.Index W₀ N) {p : PhaseCalculus.Slow}
    (hT : 0 < p.2.2) (hout : p ∉ (PrimaryGeometryAssembly.domain W₀ N).carrier L) :
    PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W₀ L).1
      (PrimaryGeometryAssembly.label W₀ L).2 =ᶠ[𝓝 p] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hs
  apply hout
  exact PrimaryGeometryAssembly.cellDomain_support L ⟨hs, hT⟩

/-- The actual slow mask and actual outer bump extend a native field to
the whole larger chart. Off its own cell it is locally zero, including
all slow-mask and slot-cutoff derivatives. -/
theorem NativeJets.prepared_mask_outer_localize
    {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀} {N : ℕ}
    {V V' : JetDomain (PrimaryGeometryAssembly.Index W₀ N) D}
    {w : PrimaryGeometryAssembly.Index W₀ N → D → ℝ}
    {f : PrimaryGeometryAssembly.Index W₀ N → D → E} (hf : NativeJets V w f)
    (χ : PrimaryGeometryAssembly.Index W₀ N → D → PhaseCalculus.Slow)
    (hχ : PolynomialJets V'.toDomain χ)
    (hscaleBand : ∀ L, V'.scale L = ChartScales.S (PrimaryGeometryAssembly.label W₀ L).1)
    (hT : ∀ L x, x ∈ V'.carrier L → 0 < (χ L x).2.2)
    (τ : PrimaryGeometryAssembly.Index W₀ N → D →L[ℝ] ℝ)
    (t0 : PrimaryGeometryAssembly.Index W₀ N → ℝ)
    {K : ℝ} (hK : 1 ≤ K) (q : ℕ) (hτ : ∀ L, ‖τ L‖ ≤ K * V'.scale L ^ q)
    (hscale : ∀ L, V'.scale L = V.scale L)
    (hsub : ∀ L, V.carrier L ⊆ V'.carrier L)
    (hgrowth : ∀ L x, x ∈ V.carrier L → V.growth L x = V'.growth L x)
    (hinside : ∀ L x, x ∈ V'.carrier L →
      χ L x ∈ (PrimaryGeometryAssembly.domain W₀ N).carrier L →
      τ L x + t0 L ∈ Ioo (0 : ℝ) 1 → x ∈ V.carrier L)
    (hw : ∀ L x, x ∈ V'.carrier L → 0 ≤ w L x) :
    NativeJets V' w (fun L x =>
      (PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W₀ L).1
        (PrimaryGeometryAssembly.label W₀ L).2 (χ L x) * outerCutoff (τ L x + t0 L)) • f L x) := by
  have hm := nativeMask_comp_jets V'.toDomain χ hχ
    (fun L => (PrimaryGeometryAssembly.label W₀ L).1)
    (fun L => (PrimaryGeometryAssembly.label W₀ L).2)
    (fun L => L.val.property.1) hscaleBand
  apply hf.localize (hm.mul (outerCutoff_affine_jets V'.toDomain τ t0 hK q hτ))
    hscale hsub hgrowth hw
  intro L x hx
  apply hinside L x hx.2
  · have hs := tsupport_mul_subset_left hx.1
    by_contra hout
    have hz := preparedMask_zero_germ L (hT L x hx.2) hout
    have hz' := hz.comp_tendsto
      (((hχ.smooth L).contDiffAt ((V'.isOpen L).mem_nhds hx.2)).continuousAt)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz') hs
  · exact outerCutoff_affine_support (τ L) (t0 L) (tsupport_mul_subset_right hx.1)

/-! ### The two orientations share one family of constants -/

/-- Sign domain, bundling `carrier`, `isOpen`, `scale`, `one_le_scale` and the required
compatibility proofs. -/
noncomputable def signDomain (V : JetDomain ι D) : JetDomain (Fin 2 × ι) D where
  carrier i := V.carrier i.2
  isOpen i := V.isOpen i.2
  scale i := V.scale i.2
  one_le_scale i := V.one_le_scale i.2
  growth i := V.growth i.2
  scale_le_growth i := V.scale_le_growth i.2

theorem NativeJets.both_signs {V : JetDomain ι D}
    {w : Fin 2 → ι → D → ℝ} {f : Fin 2 → ι → D → E}
    (hf : ∀ j, NativeJets V (w j) (f j)) :
    NativeJets (signDomain V) (fun i => w i.1 i.2) (fun i => f i.1 i.2) := by
  refine ⟨fun i => (hf i.1).nonneg i.2, fun i => (hf i.1).smooth i.2, ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := (hf 0).bound m
  obtain ⟨B, hB, q, hb⟩ := (hf 1).bound m
  refine ⟨A + B, by linarith, p + q, ?_⟩
  intro i x hx k hk
  have hG := V.one_le_growth i.2 hx
  rcases i with ⟨j, i⟩
  fin_cases j
  · exact (ha i x hx k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith) (pow_le_pow_right₀ hG (Nat.le_add_right p q))
        (pow_nonneg (zero_le_one.trans hG) p) (by linarith)) ((hf 0).nonneg i x hx))
  · exact (hb i x hx k hk).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith) (pow_le_pow_right₀ hG (Nat.le_add_left q p))
        (pow_nonneg (zero_le_one.trans hG) q) (by linarith)) ((hf 1).nonneg i x hx))

/-! ### The actual common-cover copy map -/

section NativeCopies

open CommonCoverSolve TorusInverse

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {Λ : Type*}

/-- Native point linear, given by `(ContinuousLinearMap.fst ℝ P TorusInverse.Plane).prod
(g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P TorusInverse.Plane))`. -/
noncomputable def nativePointLinear (g : Geometry) : (P × TorusInverse.Plane) →L[ℝ] (P ×
    TorusInverse.Plane) :=
  (ContinuousLinearMap.fst ℝ P TorusInverse.Plane).prod
    (g.coordinateLinear.comp (ContinuousLinearMap.snd ℝ P TorusInverse.Plane))

theorem nativePoint_affine (g : Geometry) (k : Frequency) (x : P × TorusInverse.Plane) :
    ParticularWaveBounds.nativePoint g k x =
      nativePointLinear g x + ParticularWaveBounds.nativePoint g k 0 := by
  apply Prod.ext
  · simp [ParticularWaveBounds.nativePoint, nativePointLinear]
  · change g.coordinates k x.2 = g.coordinateLinear x.2 + g.coordinates k 0
    rw [g.coordinates_eq_affine k x.2, add_comm]

theorem norm_nativePointLinear_le (g : Geometry) :
    ‖nativePointLinear (P := P) g‖ ≤ CommonCoverClass.argumentCost g := by
  have hcost := CommonCoverClass.one_le_argumentCost g
  have hc : ‖g.coordinateLinear‖ ≤ CommonCoverClass.argumentCost g := by
    unfold CommonCoverClass.argumentCost
    have h : 0 ≤ ‖g.pointLinear‖ * (1 + ‖g.coordinateLinear‖) := by positivity
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hcost)
  intro x
  change ‖(x.1, g.coordinateLinear x.2)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_fst_le x).trans (le_mul_of_one_le_left (norm_nonneg x) hcost)
  · exact (g.coordinateLinear.le_opNorm x.2).trans
      (mul_le_mul hc (norm_snd_le x) (norm_nonneg _) (zero_le_one.trans hcost))

/-- For the actual band basis, the affine derivative cost is uniform in
the center and lattice translation. -/
theorem nativePointLinear_band_bound (B : TorusInverse.Plane ≃L[ℝ] TorusInverse.Plane) {h : ℝ} (hh
    : 0 ≤ h)
    {n gap Δ : ℕ} (hn : 4 ≤ n) (hgap : gap ≤ Δ) (center : TorusInverse.Plane) :
    ‖nativePointLinear (P := P) (CommonCoverClass.bandGeometry B h n gap center)‖ ≤
      CommonCoverClass.bandArgumentCost B Δ * ChartScales.S n :=
  (norm_nativePointLinear_le _).trans
    (CommonCoverClass.bandGeometry_argumentCost_le B hh hn hgap center)

theorem NativeJets.native_copy_localJets
    {V : JetDomain ι (P × TorusInverse.Plane)} {w : ι → P × TorusInverse.Plane → ℝ} {f : ι → P ×
        TorusInverse.Plane → H}
    (hf : NativeJets V w f) (s : StripData (P × TorusInverse.Plane))
    (W : Λ → ℕ → P × TorusInverse.Plane → ℝ) (α : ℝ)
    (index : Λ → ℕ → ι) (g : Λ → ℕ → Geometry) (Ω : Λ → ℕ → Set TorusInverse.Plane)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hmap : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      ParticularWaveBounds.nativePoint (g l n) k x ∈ V.carrier (index l n))
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (a b : ℕ)
    (hgrowth : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      V.growth (index l n) (ParticularWaveBounds.nativePoint (g l n) k x) ≤ A * s.growth n x ^ a)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ B * s.slow n ^ b)
    (hweight : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      w (index l n) (ParticularWaveBounds.nativePoint (g l n) k x) ≤ s.epsilon n ^ α * W l n x) :
    PeriodizedWaveBounds.UniformLocalJets s W α
      (fun l n => PeriodizedWaveBounds.nativeCell (g l n) (Ω l n))
      (fun l n k x => f (index l n) (ParticularWaveBounds.nativePoint (g l n) k x)) := by
  have h := hf.copy_localJets s W α index
    (fun l n _ => nativePointLinear (g l n))
    (fun l n k => ParticularWaveBounds.nativePoint (g l n) k 0)
    (fun l n => PeriodizedWaveBounds.nativeCell (g l n) (Ω l n)) hW
    (by simp only [← nativePoint_affine]; exact hmap) hA hB a b
    (by simp only [← nativePoint_affine]; exact hgrowth)
    (fun l n _ => (norm_nativePointLinear_le (g l n)).trans (hgeometry l n))
    (by simp only [← nativePoint_affine]; exact hweight)
  have he : affineCopy f index (fun l n _ => nativePointLinear (g l n))
      (fun l n k => ParticularWaveBounds.nativePoint (g l n) k 0) =
      (fun l n k x => f (index l n) (ParticularWaveBounds.nativePoint (g l n) k x)) := by
    funext l n k x
    dsimp only [affineCopy]
    rw [← nativePoint_affine]
  rw [he] at h
  exact h

/-- The constructed native field is periodized over the genuine covering
lattice.  Support is proved from the scalar cutoff, and the native cells
are constructed from compactness and injectivity of that patch. -/
theorem NativeJets.native_copy_sum_uniformClass
    {V : JetDomain ι (P × TorusInverse.Plane)} {w : ι → P × TorusInverse.Plane → ℝ} {f : ι → P ×
        TorusInverse.Plane → H}
    (hf : NativeJets V w f) (s : StripData (P × TorusInverse.Plane))
    (W : Λ → ℕ → P × TorusInverse.Plane → ℝ) (α : ℝ)
    (index : Λ → ℕ → ι) (g : Λ → ℕ → Geometry) (Ω : Λ → ℕ → Set TorusInverse.Plane)
    (hcompact : ∀ l n, IsCompact (Ω l n))
    (hinj : ∀ l n, InjOn TorusAverages.quotientPoint
      ((fun z => (g l n).center + (g l n).basis z) '' Ω l n))
    (κ : ι → TorusInverse.Plane → ℝ) (hκ : PolynomialJets V.toDomain (fun i x => κ i x.2))
    (hcut : ∀ l n, support (κ (index l n)) ⊆ Ω l n)
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hmap : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      ParticularWaveBounds.nativePoint (g l n) k x ∈ V.carrier (index l n))
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (a b : ℕ)
    (hgrowth : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      V.growth (index l n) (ParticularWaveBounds.nativePoint (g l n) k x) ≤ A * s.growth n x ^ a)
    (hgeometry : ∀ l n, CommonCoverClass.argumentCost (g l n) ≤ B * s.slow n ^ b)
    (hweight : ∀ l n k x, x ∈ s.domain → (g l n).coordinates k x.2 ∈ Ω l n →
      w (index l n) (ParticularWaveBounds.nativePoint (g l n) k x) ≤ s.epsilon n ^ α * W l n x) :
    LabelSumBounds.UniformClass s W α
      (fun l n => ParticularWaveBounds.periodizedCopies (g l n) (κ (index l n))
        (fun k x => f (index l n) (ParticularWaveBounds.nativePoint (g l n) k x))) := by
  apply PeriodizedWaveBounds.copySum_uniformClass
    (fun l => PeriodizedWaveBounds.nativeCells (g l) (Ω l) (hcompact l) (hinj l)) hW
  · intro l n
    exact PeriodizedWaveBounds.native_localized_support (g l n) (hcut l n)
      (fun k x => f (index l n) (ParticularWaveBounds.nativePoint (g l n) k x))
  · exact (hf.polynomial_smul hκ).native_copy_localJets s W α index g Ω hW
      hmap hA hB a b hgrowth hgeometry hweight

end NativeCopies

end NavierStokes.PrimaryCopyBounds
