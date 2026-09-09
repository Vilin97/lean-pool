/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FourierAlias
public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialPullback
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFamilyTorusInverse
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform seminorm bounds for families of exact Fourier aliases

All constants are chosen before the source and the band. The estimates use
actual derivatives and actual translated integrals.
-/

@[expose] public section


noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Interval Topology BigOperators

namespace NavierStokes.UniformFourierAlias

open TorusInverse JetBounds

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))

section JetOperations

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_map (L : E →L[ℝ] F) {f : D → E}
    (hf : ContDiff ℝ ∞ f) (m : ℕ) (z : D) :
    ‖iteratedFDeriv ℝ m (fun x => L (f x)) z‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m f z‖ := by
  have he := L.iteratedFDeriv_comp_left hf.contDiffAt (nat_le_smooth m) (x := z)
  change iteratedFDeriv ℝ m (fun x => L (f x)) z = _ at he
  rw [he]
  exact L.norm_compContinuousMultilinearMap_le _

theorem finiteJetBound_fixedPartial {f : D → E} (hf : ContDiff ℝ ∞ f)
    {s : Set D} {C : ℝ} {m : ℕ} (hb : FiniteJetBound (m + 1) f s C)
    (v : D) (hv : ‖v‖ ≤ 1) :
    FiniteJetBound m (fun x => fderiv ℝ f x v) s C := by
  intro j hj z hz
  have h := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (c := v)
    (hf.fderiv_right (by simp)).contDiffAt (nat_le_smooth j) (x := z)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans ((mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb (j + 1) (Nat.add_le_add_right hj 1) z hz))

end JetOperations

section IterationBounds

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sourceJet_mem (G : (ℝ × E → F) → Prop) (J : (ℝ × E → F) → ℝ × E → F)
    (hclosed : ∀ f, G f → G (RadialAlias.slowDeriv (J f))) (p : ℕ)
    {f : ℝ × E → F} (hf : G f) : G (RadialAlias.sourceJet J f p) := by
  induction p with
  | zero => exact hf
  | succ p ih =>
    rw [RadialAlias.sourceJet_succ]
    exact hclosed _ ih

/-- A finite-loss estimate for an actual operator propagates through the
successive slow derivatives used in radial integration by parts. This lemma
is instantiated below with the constructed torus inverse. -/
theorem sourceJet_uniform_finiteJets
    (G : (ℝ × E → F) → Prop) (J : (ℝ × E → F) → ℝ × E → F)
    (s : Set (ℝ × E)) (loss : ℕ)
    (hclosed : ∀ f, G f → G (RadialAlias.slowDeriv (J f)))
    (hsmooth : ∀ f, G f → ContDiff ℝ ∞ (J f))
    (htame : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + loss) f s C → FiniteJetBound m (J f) s (K * C))
    (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + (loss + 1) * p) f s C →
      FiniteJetBound m (RadialAlias.sourceJet J f p) s (K * C) := by
  have hgood : ∀ p : ℕ, ∀ f, G f → G (RadialAlias.sourceJet J f p) := by
    intro p
    induction p with
    | zero => exact fun _ h => h
    | succ p ih =>
      intro f hf
      rw [RadialAlias.sourceJet_succ]
      exact hclosed _ (ih f hf)
  induction p generalizing m with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro f _ C _ hb
    simpa only [Nat.mul_zero, Nat.add_zero, RadialAlias.sourceJet_zero, one_mul] using hb
  | succ p ih =>
    obtain ⟨A, hA, hAbound⟩ := ih (m + 1 + loss)
    obtain ⟨B, hB, hBbound⟩ := htame (m + 1)
    refine ⟨B * A, mul_nonneg hB hA, ?_⟩
    intro f hf C hC hb
    have hsource : FiniteJetBound (m + 1 + loss + (loss + 1) * p) f s C := by
      convert! hb using 1
      ring
    have hprev := hAbound f hf C hC hsource
    have hinverse := hBbound _ (hgood p f hf) (A * C) (mul_nonneg hA hC) hprev
    have hderiv := finiteJetBound_fixedPartial (hsmooth _ (hgood p f hf)) hinverse
      ((1 : ℝ), (0 : E)) (by simp)
    rw [RadialAlias.sourceJet_succ]
    unfold RadialAlias.slowDeriv
    simpa only [mul_assoc] using hderiv

end IterationBounds

section Integrals

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The exact defect in the compact transport primitive, with all auxiliary
slow variables retained in `E`. -/
noncomputable def exactAlias (χ : ℝ → ℝ) (M : ℝ) (v : E)
    (f : ℝ × E → F) (z : ℝ × E) : F :=
  deriv χ z.1 • TransportPrimitive.totalIntegral M v f z

theorem exactAlias_smooth {a b M : ℝ} {v : E} {χ : ℝ → ℝ} {f : ℝ × E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) :
    ContDiff ℝ ∞ (exactAlias χ M v f) :=
  (((contDiff_infty_iff_deriv.mp hχ).2).comp contDiff_fst).smul
    (TransportPrimitive.totalIntegral_contDiff hf hs)

omit [CompleteSpace F] in
theorem exactAlias_supported {a b M : ℝ} {v : E} {χ : ℝ → ℝ} {f : ℝ × E → F}
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) :
    RadialAlias.RadiallySupported a b (exactAlias χ M v f) := by
  intro z hz
  have hl : a ≤ z.1 := by
    by_contra hn
    have heq : χ =ᶠ[𝓝 z.1] (fun _ => 0) :=
      (eventually_lt_nhds (lt_of_not_ge hn)).mono (fun u hu => hleft u hu.le)
    have hd : deriv χ z.1 = 0 := by simpa using heq.deriv_eq
    exact hz (by simp only [exactAlias, hd, zero_smul])
  have hr : z.1 ≤ b := by
    by_contra hn
    have heq : χ =ᶠ[𝓝 z.1] (fun _ => 1) :=
      (eventually_gt_nhds (lt_of_not_ge hn)).mono (fun u hu => hright u hu.le)
    have hd : deriv χ z.1 = 0 := by simpa using heq.deriv_eq
    exact hz (by simp only [exactAlias, hd, zero_smul])
  exact ⟨hl, hr⟩

theorem transport_compact_exactAlias {a b M : ℝ} {v : E} {χ : ℝ → ℝ} {f : ℝ × E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (z : ℝ × E) :
    TransportPrimitive.fixedDeriv (1, M • v) (TransportPrimitive.compactIntegral χ M v f) z =
      f z - exactAlias χ M v f z :=
  TransportPrimitive.transport_compactIntegral hχ hf hs z

/-- Repeated integration by parts for full derivative tensors. The last
premise bounds genuine source jets, not the alias. -/
theorem totalIntegral_sourceJet_bound {a b M C : ℝ} {v : E}
    (J : (ℝ × E → F) → ℝ × E → F) (f : ℝ × E → F) (p m : ℕ)
    (hab : a ≤ b) (hM : M ≠ 0)
    (hf : ContDiff ℝ ∞ f) (hsf : RadialAlias.RadiallySupported a b f)
    (hJ : ∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n)))
    (hsJ : ∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n)))
    (hr : ∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
      RadialAlias.sourceJet J f n)
    (hbound : FiniteJetBound m (RadialAlias.sourceJet J f p) (Prod.fst ⁻¹' Icc a b) C)
    (j : ℕ) (hj : j ≤ m) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M v f) z‖ ≤
      (C * (b - a)) * (|M|⁻¹) ^ p := by
  have hg : ContDiff ℝ ∞ (RadialAlias.sourceJet J f p) := by
    cases p with
    | zero => exact hf
    | succ p =>
      rw [RadialAlias.sourceJet_succ]
      exact TransportPrimitive.fixedDeriv_contDiff (hJ p (Nat.lt_succ_self p)) (1, 0)
  have hsg := RadialAlias.sourceJet_radiallySupported J f p hsf hsJ
  have heq : TransportPrimitive.totalIntegral M v f = fun z =>
      (-M⁻¹) ^ p • TransportPrimitive.totalIntegral M v (RadialAlias.sourceJet J f p) z := by
    funext w
    rw [TransportPrimitive.totalIntegral_eq_wholeAlias hf.continuous hsf,
      TransportPrimitive.totalIntegral_eq_wholeAlias hg.continuous hsg]
    exact RadialAlias.wholeAlias_sourceJet J f p hM
      (fun n hn => (hJ n hn).of_le (by simp)) hsJ hr
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((TransportPrimitive.totalIntegral_contDiff hg hsg).of_le (nat_le_smooth j)).contDiffAt]
  have hn := norm_smul ((-M⁻¹) ^ p : ℝ)
    (iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M v (RadialAlias.sourceJet J f p)) z)
  rw [hn, Real.norm_eq_abs, abs_pow, abs_neg, abs_inv, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le hab hg hsg j
    (fun u hu Y => hbound j hj (u, Y) hu) z

/-- A source-independent constant for the compactification defect, retaining
the entire cutoff Leibniz expansion. -/
theorem exactAlias_sourceJet_bound {a b : ℝ} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (J : (ℝ × E → F) → ℝ × E → F)
      (f : ℝ × E → F) (p : ℕ) (C : ℝ), M ≠ 0 → 0 ≤ C →
      ContDiff ℝ ∞ f → RadialAlias.RadiallySupported a b f →
      (∀ n < p, ContDiff ℝ ∞ (J (RadialAlias.sourceJet J f n))) →
      (∀ n < p, RadialAlias.RadiallySupported a b (J (RadialAlias.sourceJet J f n))) →
      (∀ n < p, RadialAlias.directionalDeriv v (J (RadialAlias.sourceJet J f n)) =
        RadialAlias.sourceJet J f n) →
      FiniteJetBound m (RadialAlias.sourceJet J f p) (Prod.fst ⁻¹' Icc a b) C →
      ∀ j ≤ m, ∀ z : ℝ × E,
        ‖iteratedFDeriv ℝ j (exactAlias χ M v f) z‖ ≤ K * C * (|M|⁻¹) ^ p := by
  obtain ⟨B, hB, hcut⟩ := RadialPullback.radial_multiplier_finiteJets_uniform (E := E) (V := F)
    a b (contDiff_infty_iff_deriv.mp hχ).2 m
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab
  refine ⟨B * (b - a), mul_nonneg hB hL, ?_⟩
  intro M v J f p C hM hC hf hs hJ hsJ hr hb j hj z
  by_cases hz : z.1 ∈ Icc a b
  · have h := hcut (TransportPrimitive.totalIntegral M v f)
      (TransportPrimitive.totalIntegral_contDiff hf hs) z hz (C * (b - a) * (|M|⁻¹) ^ p)
      (by positivity)
      (fun i hi => totalIntegral_sourceJet_bound J f p m hab hM hf hs hJ hsJ hr hb i hi z)
      j hj
    convert! h using 1
    ring
  · have hsj := TransportPrimitive.iteratedFDeriv_supported
      (exactAlias_supported (M := M) (v := v) (f := f) hleft hright) j
    have heq : iteratedFDeriv ℝ j (exactAlias χ M v f) z = 0 := by
      by_contra hnonzero
      exact hz (hsj hnonzero)
    rw [heq, norm_zero]
    positivity

theorem totalIntegral_uniform_of_inverse {a b : ℝ} {v : E}
    (G : (ℝ × E → F) → Prop) (J : (ℝ × E → F) → ℝ × E → F) (loss : ℕ)
    (hab : a ≤ b)
    (hregular : ∀ f, G f → ContDiff ℝ ∞ f ∧ RadialAlias.RadiallySupported a b f)
    (hsmooth : ∀ f, G f → ContDiff ℝ ∞ (J f))
    (hsupport : ∀ f, G f → RadialAlias.RadiallySupported a b (J f))
    (hsolve : ∀ f, G f → RadialAlias.directionalDeriv v (J f) = f)
    (hclosed : ∀ f, G f → G (RadialAlias.slowDeriv (J f)))
    (htame : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + loss) f (Prod.fst ⁻¹' Icc a b) C →
        FiniteJetBound m (J f) (Prod.fst ⁻¹' Icc a b) (K * C)) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + (loss + 1) * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × E,
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M v f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  obtain ⟨B, hB, hbound⟩ := sourceJet_uniform_finiteJets G J (Prod.fst ⁻¹' Icc a b)
    loss hclosed hsmooth htame p m
  refine ⟨B * (b - a), mul_nonneg hB (sub_nonneg.mpr hab), ?_⟩
  intro f hf C hC hb M hM j hj z
  have h := totalIntegral_sourceJet_bound J f p m hab hM (hregular f hf).1 (hregular f hf).2
    (fun n _ => hsmooth _ (sourceJet_mem G J hclosed n hf))
    (fun n _ => hsupport _ (sourceJet_mem G J hclosed n hf))
    (fun n _ => hsolve _ (sourceJet_mem G J hclosed n hf))
    (hbound f hf C hC hb) j hj z
  convert! h using 1
  ring

theorem exactAlias_uniform_of_inverse {a b : ℝ} {v : E} {χ : ℝ → ℝ}
    (G : (ℝ × E → F) → Prop) (J : (ℝ × E → F) → ℝ × E → F) (loss : ℕ)
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    (hregular : ∀ f, G f → ContDiff ℝ ∞ f ∧ RadialAlias.RadiallySupported a b f)
    (hsmooth : ∀ f, G f → ContDiff ℝ ∞ (J f))
    (hsupport : ∀ f, G f → RadialAlias.RadiallySupported a b (J f))
    (hsolve : ∀ f, G f → RadialAlias.directionalDeriv v (J f) = f)
    (hclosed : ∀ f, G f → G (RadialAlias.slowDeriv (J f)))
    (htame : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + loss) f (Prod.fst ⁻¹' Icc a b) C →
        FiniteJetBound m (J f) (Prod.fst ⁻¹' Icc a b) (K * C)) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f, G f → ∀ C : ℝ, 0 ≤ C →
      FiniteJetBound (m + (loss + 1) * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × E,
        ‖iteratedFDeriv ℝ j (exactAlias χ M v f) z‖ ≤ K * C * (|M|⁻¹) ^ p := by
  obtain ⟨A, hA, hAbound⟩ := exactAlias_sourceJet_bound (E := E) (F := F)
    hab hχ hleft hright m
  obtain ⟨B, hB, hBbound⟩ := sourceJet_uniform_finiteJets G J (Prod.fst ⁻¹' Icc a b)
    loss hclosed hsmooth htame p m
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro f hf C hC hb M hM j hj z
  have h := hAbound M v J f p (B * C) hM (mul_nonneg hB hC)
    (hregular f hf).1 (hregular f hf).2
    (fun n _ => hsmooth _ (sourceJet_mem G J hclosed n hf))
    (fun n _ => hsupport _ (sourceJet_mem G J hclosed n hf))
    (fun n _ => hsolve _ (sourceJet_mem G J hclosed n hf))
    (hBbound f hf C hC hb) j hj z
  simpa only [mul_assoc] using h

end Integrals

section RealTransfer

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complexify, given by `f z`. -/
noncomputable def complexify (f : D → ℝ) (z : D) : ℂ := f z

theorem complexify_smooth {f : D → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (complexify f) := Complex.ofRealCLM.contDiff.comp hf

theorem norm_iteratedFDeriv_complexify {f : D → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (z : D) :
    ‖iteratedFDeriv ℝ m (complexify f) z‖ = ‖iteratedFDeriv ℝ m f z‖ :=
  Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (nat_le_smooth m)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem complexify_supported {a b : ℝ} {f : ℝ × E → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (complexify f) := by
  intro z hz
  apply hs
  intro h
  exact hz (by simp only [complexify, h, Complex.ofReal_zero])

theorem totalIntegral_complexify (M : ℝ) (v : E) (f : ℝ × E → ℝ) :
    TransportPrimitive.totalIntegral M v (complexify f) =
      complexify (TransportPrimitive.totalIntegral M v f) := by
  funext z
  exact Complex.ofRealLI.integral_comp_comm (fun u => f (TransportPrimitive.shift M v z u))

theorem norm_iteratedFDeriv_totalIntegral_complexify {a b M : ℝ} {v : E}
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported a b f)
    (m : ℕ) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ m (TransportPrimitive.totalIntegral M v (complexify f)) z‖ =
      ‖iteratedFDeriv ℝ m (TransportPrimitive.totalIntegral M v f) z‖ := by
  rw [totalIntegral_complexify]
  exact norm_iteratedFDeriv_complexify (TransportPrimitive.totalIntegral_contDiff hf hs) m z

theorem exactAlias_complexify (χ : ℝ → ℝ) (M : ℝ) (v : E) (f : ℝ × E → ℝ) :
    exactAlias χ M v (complexify f) = complexify (exactAlias χ M v f) := by
  funext z
  rw [exactAlias, totalIntegral_complexify]
  exact (Complex.ofRealCLM.map_smul (deriv χ z.1)
    (TransportPrimitive.totalIntegral M v f z)).symm

theorem norm_iteratedFDeriv_exactAlias_complexify {a b M : ℝ} {v : E}
    {χ : ℝ → ℝ} {f : ℝ × E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (m : ℕ) (z : ℝ × E) :
    ‖iteratedFDeriv ℝ m (exactAlias χ M v (complexify f)) z‖ =
      ‖iteratedFDeriv ℝ m (exactAlias χ M v f) z‖ := by
  rw [exactAlias_complexify]
  exact norm_iteratedFDeriv_complexify (exactAlias_smooth hχ hf hs) m z

end RealTransfer

section ParameterGeometry

variable {S F : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Reassociate radial, slow, and torus variables without changing the norm. -/
noncomputable def toProduct (f : ℝ × (S × Plane) → F) (z : (ℝ × S) × Plane) : F :=
  f (z.1.1, (z.1.2, z.2))

/-- From product, given by `f ((z.1, z.2.1), z.2.2)`. -/
noncomputable def fromProduct (f : (ℝ × S) × Plane → F) (z : ℝ × (S × Plane)) : F :=
  f ((z.1, z.2.1), z.2.2)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp] theorem fromProduct_toProduct (f : ℝ × (S × Plane) → F) :
    fromProduct (toProduct f) = f := rfl

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp] theorem toProduct_fromProduct (f : (ℝ × S) × Plane → F) :
    toProduct (fromProduct f) = f := rfl

theorem toProduct_smooth {f : ℝ × (S × Plane) → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (toProduct f) :=
  hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv.contDiff

theorem fromProduct_smooth {f : (ℝ × S) × Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fromProduct f) :=
  hf.comp (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv.contDiff

theorem norm_iteratedFDeriv_toProduct (f : ℝ × (S × Plane) → F)
    (m : ℕ) (z : (ℝ × S) × Plane) :
    ‖iteratedFDeriv ℝ m (toProduct f) z‖ =
      ‖iteratedFDeriv ℝ m f (z.1.1, (z.1.2, z.2))‖ :=
  (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).norm_iteratedFDeriv_comp_right f z m

theorem norm_iteratedFDeriv_fromProduct (f : (ℝ × S) × Plane → F)
    (m : ℕ) (z : ℝ × (S × Plane)) :
    ‖iteratedFDeriv ℝ m (fromProduct f) z‖ =
      ‖iteratedFDeriv ℝ m f ((z.1, z.2.1), z.2.2)‖ :=
  (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.norm_iteratedFDeriv_comp_right f z m

/-- Source mean, given by `FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)))`. -/
noncomputable def sourceMean (f : ℝ × (S × Plane) → F) (p : ℝ × S) : F :=
  FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)))

/-- Source periodic, given by `∀ U s, FourierAlias.TorusPeriodic (fun Y => f (U, (s, Y)))`. -/
noncomputable def SourcePeriodic (f : ℝ × (S × Plane) → F) : Prop :=
  ∀ U s, FourierAlias.TorusPeriodic (fun Y => f (U, (s, Y)))

/-- Radial slice, given by `f (z.1, (s, z.2))`. -/
noncomputable def radialSlice (f : ℝ × (S × Plane) → F) (s : S) (z : ℝ × Plane) : F :=
  f (z.1, (s, z.2))

theorem radialSlice_smooth {f : ℝ × (S × Plane) → F} (hf : ContDiff ℝ ∞ f) (s : S) :
    ContDiff ℝ ∞ (radialSlice f s) :=
  hf.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedSpace ℝ F] in
theorem radialSlice_supported {a b : ℝ} {f : ℝ × (S × Plane) → F}
    (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    RadialAlias.RadiallySupported a b (radialSlice f s) :=
  fun z hz => @hs (z.1, (s, z.2)) hz

theorem totalIntegral_radialSlice (M : ℝ) (v : Plane) (f : ℝ × (S × Plane) → F)
    (U : ℝ) (s : S) (Y : Plane) :
    TransportPrimitive.totalIntegral M ((0 : S), v) f (U, (s, Y)) =
      TransportPrimitive.totalIntegral M v (radialSlice f s) (U, Y) := by
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [TransportPrimitive.shift, radialSlice, Prod.mk_add_mk, Prod.smul_mk,
    smul_zero, add_zero]

theorem sourceMean_totalIntegral {a b M : ℝ} {v : Plane} {f : ℝ × (S × Plane) → F}
    (hab : a ≤ b) (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f)
    (hs : RadialAlias.RadiallySupported a b f) (U : ℝ) (s : S) :
    sourceMean (TransportPrimitive.totalIntegral M ((0 : S), v) f) (U, s) =
      ∫ u in a..b, sourceMean f (u, s) := by
  change FourierAlias.torusMean (fun Y => TransportPrimitive.totalIntegral M ((0 : S), v) f
    (U, (s, Y))) = _
  simp_rw [totalIntegral_radialSlice]
  exact FourierAlias.torusMean_totalIntegral hab (radialSlice_smooth hf s).continuous
    (fun u => hp u s) (radialSlice_supported hs s) U

theorem exactAlias_sourceMean_zero {a b M : ℝ} {v : Plane}
    {f : ℝ × (S × Plane) → F} (χ : ℝ → ℝ) (hab : a ≤ b)
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hm : ∀ s, (∫ u in a..b, sourceMean f (u, s)) = 0) (p : ℝ × S) :
    sourceMean (exactAlias χ M ((0 : S), v) f) p = 0 := by
  change FourierAlias.torusMean (fun Y => deriv χ p.1 •
    TransportPrimitive.totalIntegral M ((0 : S), v) f (p.1, (p.2, Y))) = 0
  rw [FourierAlias.torusMean_smul]
  change deriv χ p.1 • sourceMean (TransportPrimitive.totalIntegral M ((0 : S), v) f) p = 0
  rw [sourceMean_totalIntegral hab hf hp hs, hm p.2, smul_zero]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceMean_complexify (f : ℝ × (S × Plane) → ℝ) (p : ℝ × S) :
    sourceMean (complexify f) p = ((sourceMean f p : ℝ) : ℂ) := by
  simp only [sourceMean, FourierAlias.torusMean, complexify, intervalIntegral.integral_ofReal]

end ParameterGeometry

section RealInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Parameter periodic, given by `∀ p, FourierAlias.TorusPeriodic (fun Y => f (p, Y))`. -/
noncomputable def ParameterPeriodic {F : Type} (f : P × Plane → F) : Prop :=
  ∀ p, FourierAlias.TorusPeriodic (fun Y => f (p, Y))

/-- Parameter mean, given by `FourierAlias.torusMean (fun Y => f (p, Y))`. -/
noncomputable def parameterMean {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P × Plane → F) (p : P) : F := FourierAlias.torusMean (fun Y => f (p, Y))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexify_parameterPeriodic {f : P × Plane → ℝ} (hp : ParameterPeriodic f) :
    SmoothFamilyTorusInverse.Periodic (complexify f) := by
  intro p Y k
  exact congrArg Complex.ofReal (hp p Y k)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem parameterMean_complexify (f : P × Plane → ℝ) (p : P) :
    parameterMean (complexify f) p = ((parameterMean f p : ℝ) : ℂ) := by
  simp only [parameterMean, FourierAlias.torusMean, complexify, intervalIntegral.integral_ofReal]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem familyMean_eq_parameterMean (f : P × Plane → ℂ) (p : P) :
    SmoothFamilyTorusInverse.mean f p = parameterMean f p :=
  SmoothFamilyTorusInverse.mean_eq_integral f p

theorem torusMean_map {F H : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace F] [CompleteSpace H]
    (L : F →L[ℝ] H) {f : Plane → F} (hf : Continuous f) :
    FourierAlias.torusMean (fun Y => L (f Y)) = L (FourierAlias.torusMean f) := by
  have hx (y : ℝ) : (∫ x in (0 : ℝ)..1, L (f (x, y))) =
      L (∫ x in (0 : ℝ)..1, f (x, y)) :=
    L.intervalIntegral_comp_comm
      ((hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  have hc : Continuous (fun y => ∫ x in (0 : ℝ)..1, f (x, y)) :=
    FourierAlias.continuous_parameter_interval (g := fun p : ℝ × ℝ => f (p.2, p.1))
      (hf.comp (continuous_snd.prodMk continuous_fst)) (by norm_num)
  unfold FourierAlias.torusMean
  simp_rw [hx]
  exact L.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)

/-- A genuine real directional inverse, obtained from the actual complex
Fourier inverse by real part. -/
noncomputable def realInverse (d : Direction) (f : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  Complex.re (SmoothFamilyTorusInverse.inverse d (complexify f) z)

/-- Real centered, given by `f z - parameterMean f z.1`. -/
noncomputable def realCentered (f : P × Plane → ℝ) (z : P × Plane) : ℝ :=
  f z - parameterMean f z.1

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexify_realCentered (f : P × Plane → ℝ) :
    complexify (realCentered f) = SmoothFamilyTorusInverse.nonbarPart (complexify f) := by
  funext z
  change ((f z - parameterMean f z.1 : ℝ) : ℂ) =
    (f z : ℂ) - SmoothFamilyTorusInverse.mean (complexify f) z.1
  rw [Complex.ofReal_sub, familyMean_eq_parameterMean, parameterMean_complexify]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_eq_re_nonbar (f : P × Plane → ℝ) :
    realCentered f = fun z => Complex.re (SmoothFamilyTorusInverse.nonbarPart (complexify f) z) :=
        by
  funext z
  have h := congrArg Complex.re (congrFun (complexify_realCentered f) z)
  exact h

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_periodic {f : P × Plane → ℝ} (hp : ParameterPeriodic f) :
    ParameterPeriodic (realCentered f) := by
  intro p Y k
  exact congrArg (fun c => c - parameterMean f p) (hp p Y k)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realCentered_preserves_parameter_support (f : P × Plane → ℝ)
    (S : Set P) (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, realCentered f (p, Y) = 0 := by
  have hc := SmoothFamilyTorusInverse.nonbarPart_preserves_parameter_support (complexify f) S
    (fun p hp Y => by simp only [complexify, hs p hp Y, Complex.ofReal_zero])
  intro p hp Y
  rw [realCentered_eq_re_nonbar]
  change Complex.re (SmoothFamilyTorusInverse.nonbarPart (complexify f) (p, Y)) = 0
  rw [hc p hp Y, Complex.zero_re]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realInverse_periodic (d : Direction) (f : P × Plane → ℝ) :
    ParameterPeriodic (realInverse d f) := by
  intro p Y k
  exact congrArg Complex.re (SmoothFamilyTorusInverse.inverse_periodic d (complexify f) p Y k)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realInverse_preserves_parameter_support (d : Direction) (f : P × Plane → ℝ)
    (S : Set P) (hs : ∀ p, p ∉ S → ∀ Y, f (p, Y) = 0) :
    ∀ p, p ∉ S → ∀ Y, realInverse d f (p, Y) = 0 := by
  have hh := SmoothFamilyTorusInverse.inverse_preserves_parameter_support d (complexify f) S
    (fun p hp Y => by simp only [complexify, hs p hp Y, Complex.ofReal_zero])
  intro p hp Y
  change Complex.re (SmoothFamilyTorusInverse.inverse d (complexify f) (p, Y)) = 0
  rw [hh p hp Y, Complex.zero_re]

variable [FiniteDimensional ℝ P]

theorem realCentered_smooth {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ParameterPeriodic f) : ContDiff ℝ ∞ (realCentered f) := by
  rw [realCentered_eq_re_nonbar]
  exact Complex.reCLM.contDiff.comp
    (SmoothFamilyTorusInverse.nonbarPart_smooth (complexify_smooth hf)
        (complexify_parameterPeriodic hp))

omit [FiniteDimensional ℝ P] in
theorem realCentered_zeroMean {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : ParameterPeriodic f) : ∀ p, parameterMean (realCentered f) p = 0 := by
  intro p
  have hc := SmoothFamilyTorusInverse.nonbarPart_zeroMean (complexify_smooth hf)
    (complexify_parameterPeriodic hp) p
  rw [familyMean_eq_parameterMean, ← complexify_realCentered, parameterMean_complexify] at hc
  exact Complex.ofReal_eq_zero.mp hc

theorem realInverse_smooth (d : Direction) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ParameterPeriodic f) : ContDiff ℝ ∞ (realInverse d f) :=
  Complex.reCLM.contDiff.comp
    (SmoothFamilyTorusInverse.inverse_smooth d (complexify_smooth hf) (complexify_parameterPeriodic
        hp))

theorem realInverse_zeroMean (d : Direction) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ParameterPeriodic f) :
    ∀ p, parameterMean (realInverse d f) p = 0 := by
  intro p
  have hi := SmoothFamilyTorusInverse.inverse_smooth d (complexify_smooth hf)
    (complexify_parameterPeriodic hp)
  have hm := SmoothFamilyTorusInverse.inverse_zeroMean d (complexify_smooth hf)
    (complexify_parameterPeriodic hp) p
  change FourierAlias.torusMean (fun Y => Complex.reCLM
    (SmoothFamilyTorusInverse.inverse d (complexify f) (p, Y))) = 0
  rw [torusMean_map Complex.reCLM
    (f := fun Y => SmoothFamilyTorusInverse.inverse d (complexify f) (p, Y))
    (hi.continuous.comp (continuous_const.prodMk continuous_id))]
  change Complex.re (parameterMean (SmoothFamilyTorusInverse.inverse d (complexify f)) p) = 0
  rw [← familyMean_eq_parameterMean, hm, Complex.zero_re]

theorem realInverse_solves (d : Direction) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ParameterPeriodic f) (hm : ∀ p, parameterMean f p = 0)
    (z : P × Plane) :
    fderiv ℝ (realInverse d f) z (0, vector d) = f z := by
  have hi := SmoothFamilyTorusInverse.inverse_smooth d (complexify_smooth hf)
    (complexify_parameterPeriodic hp)
  have hmc : SmoothFamilyTorusInverse.ZeroMean (complexify f) := by
    intro p
    rw [familyMean_eq_parameterMean, parameterMean_complexify, hm p, Complex.ofReal_zero]
  have hsolve := congrFun (SmoothFamilyTorusInverse.inverse_solves d (complexify_smooth hf)
    (complexify_parameterPeriodic hp) hmc) z
  have heq := (Complex.reCLM.hasFDerivAt.comp z
    ((hi.differentiable (by simp)) z).hasFDerivAt).fderiv
  change fderiv ℝ (Complex.reCLM ∘ SmoothFamilyTorusInverse.inverse d (complexify f)) z
    (0, vector d) = f z
  rw [heq]
  change Complex.re (fderiv ℝ (SmoothFamilyTorusInverse.inverse d (complexify f)) z
    (0, vector d)) = f z
  rw [show fderiv ℝ (SmoothFamilyTorusInverse.inverse d (complexify f)) z (0, vector d) =
    complexify f z from hsolve]
  rfl

theorem norm_iteratedFDeriv_realInverse_le (d : Direction) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ParameterPeriodic f) (m : ℕ) (z : P × Plane) :
    ‖iteratedFDeriv ℝ m (realInverse d f) z‖ ≤
      ‖iteratedFDeriv ℝ m (SmoothFamilyTorusInverse.inverse d (complexify f)) z‖ := by
  have hi := SmoothFamilyTorusInverse.inverse_smooth d (complexify_smooth hf)
    (complexify_parameterPeriodic hp)
  have hnorm : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro c
    simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm c
  exact (norm_iteratedFDeriv_map Complex.reCLM hi m z).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _))

theorem realInverse_finiteJets (d : Direction) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : P × Plane → ℝ) (A : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + 5, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (realInverse d f) (p, Y)‖ ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.inverse_finiteJets (P := P) d m
  refine ⟨K, hK, ?_⟩
  intro f A C hf hp hC hsource j hj p hpA Y
  apply (norm_iteratedFDeriv_realInverse_le d hf hp j (p, Y)).trans
  apply hb (complexify f) A C (complexify_smooth hf) (complexify_parameterPeriodic hp) hC
    _ j hj p hpA Y
  intro i hi q hq Z
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi q hq Z

theorem realCentered_finiteJets (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : P × Plane → ℝ) (A : Set P) (C : ℝ),
      ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + 4, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (realCentered f) (p, Y)‖ ≤ K * C := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.nonbarPart_finiteJets (P := P) m
  refine ⟨K, hK, ?_⟩
  intro f A C hf hp hC hsource j hj p hpA Y
  rw [← norm_iteratedFDeriv_complexify (realCentered_smooth hf hp), complexify_realCentered]
  apply hb (complexify f) A C (complexify_smooth hf) (complexify_parameterPeriodic hp) hC
    _ j hj p hpA Y
  intro i hi q hq Z
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi q hq Z

end RealInverse

section TransportInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- Family inverse, given by `fromProduct (SmoothFamilyTorusInverse.inverse d (toProduct f))`. -/
noncomputable def familyInverse (d : Direction) (f : ℝ × (S × Plane) → ℂ) :
    ℝ × (S × Plane) → ℂ := fromProduct (SmoothFamilyTorusInverse.inverse d (toProduct f))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem mean_toProduct (f : ℝ × (S × Plane) → ℂ) (p : ℝ × S) :
    SmoothFamilyTorusInverse.mean (toProduct f) p = sourceMean f p :=
  SmoothFamilyTorusInverse.mean_eq_integral _ _

/-- Real center source, given by `fromProduct (realCentered (toProduct f))`. -/
noncomputable def realCenterSource (f : ℝ × (S × Plane) → ℝ) : ℝ × (S × Plane) → ℝ :=
  fromProduct (realCentered (toProduct f))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_apply (f : ℝ × (S × Plane) → ℝ) (z : ℝ × (S × Plane)) :
    realCenterSource f z = f z - sourceMean f (z.1, z.2.1) := rfl

theorem realCenterSource_smooth {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) : ContDiff ℝ ∞ (realCenterSource f) :=
  fromProduct_smooth (realCentered_smooth (toProduct_smooth hf) (fun p => hp p.1 p.2))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_periodic {f : ℝ × (S × Plane) → ℝ} (hp : SourcePeriodic f) :
    SourcePeriodic (realCenterSource f) := by
  intro U s Y k
  exact realCentered_periodic (fun p => hp p.1 p.2) (U, s) Y k

omit [FiniteDimensional ℝ S] in
theorem realCenterSource_zeroMean {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) : ∀ p, sourceMean (realCenterSource f) p = 0 :=
  realCentered_zeroMean (toProduct_smooth hf) (fun p => hp p.1 p.2)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem realCenterSource_supported {a b : ℝ} {f : ℝ × (S × Plane) → ℝ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (realCenterSource f) := by
  have hh : ∀ p : ℝ × S, p ∉ (Prod.fst ⁻¹' Icc a b) → ∀ Y : Plane,
      toProduct f (p, Y) = 0 := by
    intro p hp Y
    by_contra hn
    exact hp (@hs (p.1, (p.2, Y)) hn)
  have hi := realCentered_preserves_parameter_support (toProduct f) (Prod.fst ⁻¹' Icc a b) hh
  intro z hz
  by_contra hn
  exact hz (hi (z.1, z.2.1) hn z.2.2)

theorem totalIntegral_realCenterSource {a b M : ℝ} {v : Plane}
    {f : ℝ × (S × Plane) → ℝ} (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f)
    (hs : RadialAlias.RadiallySupported a b f)
    (hm : ∀ s, (∫ U in a..b, sourceMean f (U, s)) = 0) (z : ℝ × (S × Plane)) :
    TransportPrimitive.totalIntegral M ((0 : S), v) (realCenterSource f) z =
      TransportPrimitive.totalIntegral M ((0 : S), v) f z := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval (realCenterSource_smooth hf hp).continuous
      (realCenterSource_supported hs),
    TransportPrimitive.totalIntegral_eq_radialInterval hf.continuous hs]
  have hshift (U : ℝ) : z.2 + (M * (U - z.1)) • ((0 : S), v) =
      (z.2.1, z.2.2 + (M * (U - z.1)) • v) := by
    apply Prod.ext <;> simp
  simp_rw [hshift, realCenterSource_apply]
  have hc : Continuous (fun U => f (U, (z.2.1, z.2.2 + (M * (U - z.1)) • v))) :=
    hf.continuous.comp (continuous_id.prodMk (continuous_const.prodMk
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).smul
        continuous_const))))
  have ht : Continuous (fun U => Complex.re
      (SmoothFamilyTorusInverse.mean (toProduct (complexify f)) (U, z.2.1))) :=
    Complex.continuous_re.comp
      ((SmoothFamilyTorusInverse.coefficient_smooth (toProduct_smooth (complexify_smooth hf))
          0).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hmc : Continuous (fun U => sourceMean f (U, z.2.1)) := by
    simpa only [mean_toProduct, sourceMean_complexify, Complex.ofReal_re] using ht
  rw [intervalIntegral.integral_sub
    (f := fun U => f (U, (z.2.1, z.2.2 + (M * (U - z.1)) • v)))
    (g := fun U => sourceMean f (U, z.2.1)) (hc.intervalIntegrable _ _) (hmc.intervalIntegrable _
        _),
    hm z.2.1, sub_zero]

theorem exactAlias_eq_realCenterSource {a b M : ℝ} {v : Plane}
    {f : ℝ × (S × Plane) → ℝ} (χ : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) (hs : RadialAlias.RadiallySupported a b f)
    (hm : ∀ s, (∫ U in a..b, sourceMean f (U, s)) = 0) :
    exactAlias χ M ((0 : S), v) f = exactAlias χ M ((0 : S), v) (realCenterSource f) := by
  funext z
  unfold exactAlias
  rw [totalIntegral_realCenterSource hf hp hs hm]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem periodic_toProduct {f : ℝ × (S × Plane) → ℂ} (hp : SourcePeriodic f) :
    SmoothFamilyTorusInverse.Periodic (toProduct f) := fun p => hp p.1 p.2

theorem familyInverse_smooth (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f)) :
    ContDiff ℝ ∞ (familyInverse d f) :=
  fromProduct_smooth (SmoothFamilyTorusInverse.inverse_smooth d (toProduct_smooth hf) hp)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem familyInverse_periodic (d : Direction) (f : ℝ × (S × Plane) → ℂ) :
    SmoothFamilyTorusInverse.Periodic (toProduct (familyInverse d f)) :=
  SmoothFamilyTorusInverse.inverse_periodic d _

omit [FiniteDimensional ℝ S] in
theorem familyInverse_zeroMean (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f)) :
    SmoothFamilyTorusInverse.ZeroMean (toProduct (familyInverse d f)) :=
  SmoothFamilyTorusInverse.inverse_zeroMean d (toProduct_smooth hf) hp

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem familyInverse_supported (d : Direction) {a b : ℝ} {f : ℝ × (S × Plane) → ℂ}
    (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (familyInverse d f) := by
  have hh : ∀ p : ℝ × S, p ∉ (Prod.fst ⁻¹' Icc a b) → ∀ Y : Plane,
      toProduct f (p, Y) = 0 := by
    intro p hp Y
    by_contra hn
    exact hp (@hs (p.1, (p.2, Y)) hn)
  have hi := SmoothFamilyTorusInverse.inverse_preserves_parameter_support d (toProduct f)
    (Prod.fst ⁻¹' Icc a b) hh
  intro z hz
  by_contra hn
  exact hz (hi (z.1, z.2.1) hn z.2.2)

omit [FiniteDimensional ℝ S] in
theorem toProduct_slowDeriv {f : ℝ × (S × Plane) → ℂ} (hf : ContDiff ℝ ∞ f) :
    toProduct (RadialAlias.slowDeriv f) =
      SmoothFamilyTorusInverse.parameterPartial ((1 : ℝ), (0 : S)) (toProduct f) := by
  funext z
  let e := (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).toContinuousLinearEquiv
  have he := (((hf.differentiable (by simp)) (e z)).hasFDerivAt.comp z e.hasFDerivAt).fderiv
  change fderiv ℝ f (e z) (1, 0) = fderiv ℝ (f ∘ e) z ((1, 0), 0)
  rw [he]
  rfl

theorem familyInverse_solves (d : Direction) {f : ℝ × (S × Plane) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : SmoothFamilyTorusInverse.Periodic (toProduct f))
    (hm : SmoothFamilyTorusInverse.ZeroMean (toProduct f)) :
    RadialAlias.directionalDeriv ((0 : S), vector d) (familyInverse d f) = f := by
  funext z
  let g := SmoothFamilyTorusInverse.inverse d (toProduct f)
  have hg : ContDiff ℝ ∞ g := SmoothFamilyTorusInverse.inverse_smooth d (toProduct_smooth hf) hp
  let e := (LinearIsometryEquiv.prodAssoc ℝ ℝ S Plane).symm.toContinuousLinearEquiv
  have he := (((hg.differentiable (by simp)) (e z)).hasFDerivAt.comp z e.hasFDerivAt).fderiv
  change fderiv ℝ (g ∘ e) z (0, (0, vector d)) = f z
  rw [he]
  have hi := congrFun (SmoothFamilyTorusInverse.inverse_solves d (toProduct_smooth hf) hp hm) (e z)
  exact hi

/-- Admissible, constructed using `ContDiff`. -/
noncomputable def Admissible (a b : ℝ) (f : ℝ × (S × Plane) → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ SmoothFamilyTorusInverse.Periodic (toProduct f) ∧
    SmoothFamilyTorusInverse.ZeroMean (toProduct f) ∧ RadialAlias.RadiallySupported a b f

theorem admissible_step (d : Direction) {a b : ℝ} {f : ℝ × (S × Plane) → ℂ}
    (hf : Admissible a b f) : Admissible a b (RadialAlias.slowDeriv (familyInverse d f)) := by
  have hi := familyInverse_smooth d hf.1 hf.2.1
  refine ⟨TransportPrimitive.fixedDeriv_contDiff hi (1, 0), ?_, ?_,
    RadialAlias.radialSupport_slowDeriv (familyInverse_supported d hf.2.2.2)⟩
  · rw [toProduct_slowDeriv hi]
    exact SmoothFamilyTorusInverse.parameterPartial_periodic (familyInverse_periodic d f) (1, 0)
  · rw [toProduct_slowDeriv hi]
    exact SmoothFamilyTorusInverse.parameterPartial_zeroMean (toProduct_smooth hi)
      (familyInverse_zeroMean d hf.1 hf.2.1) (1, 0)

theorem familyInverse_finiteJets (d : Direction) (a b : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℂ) (C : ℝ),
      ContDiff ℝ ∞ f → SmoothFamilyTorusInverse.Periodic (toProduct f) → 0 ≤ C →
      FiniteJetBound (m + 5) f (Prod.fst ⁻¹' Icc a b) C →
      FiniteJetBound m (familyInverse d f) (Prod.fst ⁻¹' Icc a b) (K * C) := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.inverse_finiteJets (P := ℝ × S) d m
  refine ⟨K, hK, ?_⟩
  intro f C hf hp hC hsource
  have hin : SmoothFamilyTorusInverse.JetBound (toProduct f)
      (Prod.fst ⁻¹' Icc a b) (m + 5) C := by
    intro j hj p hpA Y
    rw [norm_iteratedFDeriv_toProduct]
    exact hsource j hj (p.1, (p.2, Y)) hpA
  have hout := hb (toProduct f) (Prod.fst ⁻¹' Icc a b) C (toProduct_smooth hf) hp hC hin
  intro j hj z hz
  change ‖iteratedFDeriv ℝ j (fromProduct (SmoothFamilyTorusInverse.inverse d (toProduct f))) z‖ ≤ _
  rw [norm_iteratedFDeriv_fromProduct]
  exact hout j hj (z.1, z.2.1) hz z.2.2

theorem realCenterSource_finiteJets (a b : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℝ) (C : ℝ),
      ContDiff ℝ ∞ f → SourcePeriodic f → 0 ≤ C →
      FiniteJetBound (m + 4) f (Prod.fst ⁻¹' Icc a b) C →
      FiniteJetBound m (realCenterSource f) (Prod.fst ⁻¹' Icc a b) (K * C) := by
  obtain ⟨K, hK, hb⟩ := realCentered_finiteJets (P := ℝ × S) m
  refine ⟨K, hK, ?_⟩
  intro f C hf hp hC hsource
  have hin : ∀ j ≤ m + 4, ∀ p ∈ (Prod.fst ⁻¹' Icc a b : Set (ℝ × S)), ∀ Y,
      ‖iteratedFDeriv ℝ j (toProduct f) (p, Y)‖ ≤ C := by
    intro j hj p hpA Y
    rw [norm_iteratedFDeriv_toProduct]
    exact hsource j hj (p.1, (p.2, Y)) hpA
  have hout := hb (toProduct f) (Prod.fst ⁻¹' Icc a b) C (toProduct_smooth hf)
    (fun p => hp p.1 p.2) hC hin
  intro j hj z hz
  change ‖iteratedFDeriv ℝ j (fromProduct (realCentered (toProduct f))) z‖ ≤ _
  rw [norm_iteratedFDeriv_fromProduct]
  exact hout j hj (z.1, z.2.1) hz z.2.2

/-- Actual, source-uniform finite-seminorm estimate for the translated total
integral. Every integration by parts consumes one radial derivative and five
orders for the genuine torus inverse. -/
theorem totalIntegral_finiteJets (d : Direction) {a b : ℝ} (hab : a ≤ b) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℂ), Admissible a b f →
      ∀ C : ℝ, 0 ≤ C → FiniteJetBound (m + 6 * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  apply totalIntegral_uniform_of_inverse (Admissible a b) (familyInverse d) 5 hab
    (fun _ hf => ⟨hf.1, hf.2.2.2⟩)
    (fun _ hf => familyInverse_smooth d hf.1 hf.2.1)
    (fun _ hf => familyInverse_supported d hf.2.2.2)
    (fun _ hf => familyInverse_solves d hf.1 hf.2.1 hf.2.2.1)
    (fun _ hf => admissible_step d hf) _ m p
  intro k
  obtain ⟨K, hK, hb⟩ := familyInverse_finiteJets (S := S) d a b k
  exact ⟨K, hK, fun f hf C hC hsource => hb f C hf.1 hf.2.1 hC hsource⟩

/-- The retained alias has the same arbitrary inverse-frequency gain, with
all source dependence confined to a finite actual derivative bound. -/
theorem exactAlias_finiteJets (d : Direction) {a b : ℝ} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℂ), Admissible a b f →
      ∀ C : ℝ, 0 ≤ C → FiniteJetBound (m + 6 * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
        ‖iteratedFDeriv ℝ j (exactAlias χ M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  apply exactAlias_uniform_of_inverse (Admissible a b) (familyInverse d) 5 hab hχ hleft hright
    (fun _ hf => ⟨hf.1, hf.2.2.2⟩)
    (fun _ hf => familyInverse_smooth d hf.1 hf.2.1)
    (fun _ hf => familyInverse_supported d hf.2.2.2)
    (fun _ hf => familyInverse_solves d hf.1 hf.2.1 hf.2.2.1)
    (fun _ hf => admissible_step d hf) _ m p
  intro k
  obtain ⟨K, hK, hb⟩ := familyInverse_finiteJets (S := S) d a b k
  exact ⟨K, hK, fun f hf C hC hsource => hb f C hf.1 hf.2.1 hC hsource⟩

end TransportInverse

section MeanClassBounds

open WeightedRadialPrimitive WeightedClasses

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The flat radial weight absorbs every fixed inverse-edge power, giving a
global finite seminorm bound for a genuine mean-class family. -/
theorem meanClass_global_finiteJets {a b cL cR : ℝ} (ha : 0 < a)
    (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    {α : ℝ} {f : ℕ → ℝ × E → F}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℕ, ∀ n,
      FiniteJetBound m (f n) Set.univ (C * ε n ^ α * S n ^ q) := by
  obtain ⟨C, hC, q, hb⟩ := hf.bounds m
  obtain ⟨W, hW, hw⟩ := weight_uniform_bound hcL hcR (logLength a b) q
  refine ⟨C * W, mul_nonneg hC hW, q, ?_⟩
  intro n j hj z _
  have hεα : 0 < ε n ^ α := Real.rpow_pos_of_pos (hε n) α
  have hSn : 0 ≤ S n := zero_le_one.trans (hS n)
  by_cases hz : z.1 ∈ Ioo a b
  · have h := hb n z hz j hj
    rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α C q n z hz] at h
    calc
      _ ≤ (C * ε n ^ α * S n ^ q) * logWeight cL cR a b q z.1 := h
      _ ≤ (C * ε n ^ α * S n ^ q) * W :=
        mul_le_mul_of_nonneg_left (hw _ (logPosition_mem ha hz))
          (by positivity)
      _ = (C * W) * ε n ^ α * S n ^ q := by ring
  · have hsj := TransportPrimitive.iteratedFDeriv_supported (hs n) j
    have heq : iteratedFDeriv ℝ j (f n) z = 0 := by
      have hc : Continuous (fun u : ℝ => iteratedFDeriv ℝ j (f n) (u, z.2)) :=
        (TransportPrimitive.iteratedFDeriv_contDiff (hfc n) j).continuous.comp
          (continuous_id.prodMk continuous_const)
      have hsupport : support (fun u : ℝ => iteratedFDeriv ℝ j (f n) (u, z.2)) ⊆ Ioo a b := by
        simpa only [interior_Icc] using hc.isOpen_support.subset_interior_iff.mpr
          (show support (fun u : ℝ => iteratedFDeriv ℝ j (f n) (u, z.2)) ⊆ Icc a b from
            fun u hu => hsj hu)
      by_contra hn
      exact hz (hsupport hn)
    rw [heq, norm_zero]
    positivity

/-- The actual power-chart normalization transports the source family class;
all constants are uniform in the band and every auxiliary variable. -/
theorem meanClass_normalizeSource {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    {α : ℝ} {f : ℕ → ℝ × E → F}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) :
    MeanClass (logStripData (a ^ d) (b ^ d) (d ^ 2 * cL) (d ^ 2 * cR)
      (Real.rpow_pos_of_pos ha d) (mul_pos (sq_pos_of_pos hd) hcL) (mul_pos (sq_pos_of_pos hd) hcR)
      ε S hε hεone hS) α (fun n => RadialPullback.normalizeSource d a (f n)) := by
  let st := logStripData (E := E) (a ^ d) (b ^ d) (d ^ 2 * cL) (d ^ 2 * cR)
    (Real.rpow_pos_of_pos ha d) (mul_pos (sq_pos_of_pos hd) hcL) (mul_pos (sq_pos_of_pos hd) hcR)
    ε S hε hεone hS
  refine ⟨fun n z hz => st.zeta_nonneg z hz, ?_, ?_⟩
  · intro n
    exact (RadialPullback.normalizeSource_contDiff ha hd (hfc n)).contDiffOn
  · intro m
    obtain ⟨C, hC, q, hb⟩ := hf.bounds m
    obtain ⟨K, hK, hnorm⟩ := RadialPullback.normalizeSource_finiteJets_uniform (E := E) (V := F)
      ha hab hd cL cR q m
    refine ⟨K * C, mul_nonneg hK hC, q, ?_⟩
    intro n z hz j hj
    have hεα : 0 < ε n ^ α := Real.rpow_pos_of_pos (hε n) α
    have hSn : 0 ≤ S n := zero_le_one.trans (hS n)
    have hinput : ∀ i ≤ m, ∀ R ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ i (f n) (R, Y)‖ ≤
          (C * ε n ^ α * S n ^ q) * logWeight cL cR a b q R := by
      intro i hi R hR Y
      have h := hb n (R, Y) hR i hi
      rwa [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α C q n (R, Y) hR] at h
    have h := hnorm (f n) (hfc n) (C * ε n ^ α * S n ^ q) (by positivity)
      hinput z hz j hj
    rw [logStrip_majorant_eq (Real.rpow_pos_of_pos ha d)
      (mul_pos (sq_pos_of_pos hd) hcL) (mul_pos (sq_pos_of_pos hd) hcR)
      ε S hε hεone hS α (K * C) q n z hz]
    convert! h using 1
    ring

end MeanClassBounds

section FiberClass

open WeightedClasses WeightedRadialPrimitive

variable {S F H : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A proved finite loss on each parameter fiber preserves the actual
all-order mean class, including its radial weight. -/
theorem fiberOperator_preserves_meanClass
    (T : (((ℝ × S) × Plane) → F) → ((ℝ × S) × Plane) → H) (loss : ℕ)
    (hTsmooth : ∀ f, ContDiff ℝ ∞ f → ParameterPeriodic f → ContDiff ℝ ∞ (T f))
    (hTbound : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ((ℝ × S) × Plane) → F)
      (A : Set (ℝ × S)) (C : ℝ), ContDiff ℝ ∞ f → ParameterPeriodic f → 0 ≤ C →
      (∀ j ≤ m + loss, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j f (p, Y)‖ ≤ C) →
      ∀ j ≤ m, ∀ p ∈ A, ∀ Y, ‖iteratedFDeriv ℝ j (T f) (p, Y)‖ ≤ K * C)
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → ℝ × (S × Plane) → F}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => fromProduct (T (toProduct (f n)))) := by
  let st := logStripData (E := S × Plane) a b cL cR ha hcL hcR ε R hε hεone hR
  have hprod (n : ℕ) : ParameterPeriodic (toProduct (f n)) := fun p => hp n p.1 p.2
  refine ⟨fun n z hz => st.zeta_nonneg z hz, ?_, ?_⟩
  · intro n
    exact (fromProduct_smooth (hTsmooth _ (toProduct_smooth (hfc n)) (hprod n))).contDiffOn
  · intro m
    obtain ⟨K, hK, hbound⟩ := hTbound m
    obtain ⟨C, hC, q, hb⟩ := hf.bounds (m + loss)
    refine ⟨K * C, mul_nonneg hK hC, q, ?_⟩
    intro n z hz j hj
    let B := (C * ε n ^ α * R n ^ q) * logWeight cL cR a b q z.1
    have hεα : 0 < ε n ^ α := Real.rpow_pos_of_pos (hε n) α
    have hRn : 0 ≤ R n := zero_le_one.trans (hR n)
    have hw : 0 < logWeight cL cR a b q z.1 := weight_pos cL cR q (logPosition_mem ha hz)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hin : ∀ i ≤ m + loss, ∀ p ∈ ({(z.1, z.2.1)} : Set (ℝ × S)), ∀ Y,
        ‖iteratedFDeriv ℝ i (toProduct (f n)) (p, Y)‖ ≤ B := by
      intro i hi p hpA Y
      have heq : p = (z.1, z.2.1) := Set.mem_singleton_iff.mp hpA
      subst p
      rw [norm_iteratedFDeriv_toProduct]
      have h := hb n (z.1, (z.2.1, Y)) hz i hi
      rw [logStrip_majorant_eq ha hcL hcR ε R hε hεone hR α C q n (z.1, (z.2.1, Y)) hz] at h
      exact h
    rw [norm_iteratedFDeriv_fromProduct,
      logStrip_majorant_eq ha hcL hcR ε R hε hεone hR α (K * C) q n z hz]
    calc
      _ ≤ K * B := hbound (toProduct (f n)) {(z.1, z.2.1)} B (toProduct_smooth (hfc n))
        (hprod n) hB hin j hj (z.1, z.2.1) (Set.mem_singleton _) z.2.2
      _ = ((K * C) * ε n ^ α * R n ^ q) * logWeight cL cR a b q z.1 := by dsimp [B]; ring

variable [FiniteDimensional ℝ S]

theorem meanClass_realInverse (d : Direction) {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => fromProduct (realInverse d (toProduct (f n)))) :=
  fiberOperator_preserves_meanClass (realInverse d) 5
    (fun _ hf hp => realInverse_smooth d hf hp) (realInverse_finiteJets d)
    ha hcL hcR ε R hε hεone hR hf hfc hp

theorem meanClass_realCenterSource {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    {α : ℝ} {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n)) :
    MeanClass (logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => realCenterSource (f n)) :=
  fiberOperator_preserves_meanClass realCentered 4
    (fun _ hf hp => realCentered_smooth hf hp) realCentered_finiteJets
    ha hcL hcR ε R hε hεone hR hf hfc hp

end FiberClass

section BandScales

/-- The actual slow scale, clipped only at the finitely many initial bands. -/
noncomputable def bandSlow (n : ℕ) : ℝ := max 1 (ChartScales.S n)

theorem one_le_bandSlow (n : ℕ) : 1 ≤ bandSlow n := le_max_left _ _

theorem bandSlow_eventually_eq : ∀ᶠ n : ℕ in atTop, bandSlow n = ChartScales.S n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply max_eq_right
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  change 1 ≤ (n : ℝ) ^ 2
  nlinarith

/-- Choose the number of integrations by parts before learning the finite
polynomial slow-scale loss of the required source seminorm. -/
theorem frequency_gain_absorbs_family_growth {M : ℕ → ℝ} {h κ A growth α : ℝ}
    (hh : 0 < h) (hκ : 0 < κ)
    (hbound : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (N : ℕ) :
    ∃ p : ℕ, ∀ q : ℕ, ∀ C : ℝ, 0 ≤ C →
      ∀ᶠ n in atTop,
        C * ChartScales.epsilon h n ^ α * bandSlow n ^ q * (|M n|⁻¹) ^ p ≤
          C * ChartScales.epsilon h n ^ N := by
  obtain ⟨p, hp⟩ := exists_nat_gt (((N : ℝ) + 1 - α) / (κ / 2))
  have hNp : (N : ℝ) + 1 ≤ α + (κ / 2) * (p : ℝ) := by
    have hp' := (div_lt_iff₀ (half_pos hκ)).mp hp
    nlinarith
  refine ⟨p, ?_⟩
  intro q C hC
  have hslow := ChartScales.eventually_slow_power_epsilon_lt h hh (q : ℝ) 1 1
    zero_lt_one zero_lt_one
  simp only [Real.rpow_natCast, Real.rpow_one] at hslow
  filter_upwards [FourierAlias.inverse_frequency_eventually_small hh hκ hbound,
    hslow, bandSlow_eventually_eq] with n hn hsn hband
  rw [hband]
  have hε := ChartScales.epsilon_pos h n
  have hS : 0 ≤ ChartScales.S n := sq_nonneg (n : ℝ)
  have hpower : (|M n|⁻¹) ^ p ≤ ChartScales.epsilon h n ^ ((κ / 2) * (p : ℝ)) := by
    rw [Real.rpow_mul_natCast hε.le]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) hn p
  have hεα : 0 ≤ ChartScales.epsilon h n ^ α := (Real.rpow_pos_of_pos hε α).le
  calc
    _ ≤ C * ChartScales.epsilon h n ^ α * ChartScales.S n ^ q *
        ChartScales.epsilon h n ^ ((κ / 2) * (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = C * ChartScales.epsilon h n ^ (α + (κ / 2) * (p : ℝ)) * ChartScales.S n ^ q := by
      rw [Real.rpow_add hε]
      ring
    _ ≤ C * ChartScales.epsilon h n ^ ((N : ℝ) + 1) * ChartScales.S n ^ q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε
          (ChartScales.epsilon_le_one h hh.le n) hNp) hC) (pow_nonneg hS q)
    _ = (C * ChartScales.epsilon h n ^ N) *
        (ChartScales.S n ^ q * ChartScales.epsilon h n) := by
      rw [Real.rpow_add hε, Real.rpow_natCast, Real.rpow_one]
      ring
    _ ≤ (C * ChartScales.epsilon h n ^ N) * 1 :=
      mul_le_mul_of_nonneg_left hsn.le (by positivity)
    _ = C * ChartScales.epsilon h n ^ N := mul_one _

end BandScales

section UniformFamilies

open WeightedClasses WeightedRadialPrimitive

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The concrete radial strip with the manuscript's actual band scales. -/
noncomputable def chartStrip (a b cL cR : ℝ) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (h : ℝ) (hh : 0 < h) : StripData (ℝ × E) :=
  logStripData a b cL cR ha hcL hcR (ChartScales.epsilon h) bandSlow
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) one_le_bandSlow

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- Band-dependent sources in the actual all-order mean class have uniformly
superflat aliases. The proof chooses one finite IBP order before extracting
the required source seminorm and its polynomial growth degree. -/
theorem meanClass_alias_superflat (d : Direction) {a b cL cR h α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {f : ℕ → ℝ × (S × Plane) → ℂ}
    (hf : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hgood : ∀ n, Admissible a b (f n))
    {M : ℕ → ℝ} {κ A growth : ℝ} (hκ : 0 < κ)
    (hM : ∀ᶠ n in atTop, M n ≠ 0)
    (hfrequency : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
      ‖iteratedFDeriv ℝ j (exactAlias χ (M n) ((0 : S), vector d) (f n)) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  obtain ⟨p, hp⟩ := frequency_gain_absorbs_family_growth (α := α) hh hκ hfrequency N
  obtain ⟨K, hK, hbound⟩ := exactAlias_finiteJets (S := S) d hab hχ hleft hright m p
  obtain ⟨C, hC, q, hsource⟩ := meanClass_global_finiteJets ha hcL hcR
    (ChartScales.epsilon h) bandSlow (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h hh.le) one_le_bandSlow hf
    (fun n => (hgood n).2.2.2) (fun n => (hgood n).1) (m + 6 * p)
  refine ⟨K * C, mul_nonneg hK hC, ?_⟩
  filter_upwards [hM, hp q (K * C) (mul_nonneg hK hC)] with n hn hgain
  intro j hj z
  have hεα : 0 < ChartScales.epsilon h n ^ α :=
    Real.rpow_pos_of_pos (ChartScales.epsilon_pos h n) α
  have hslow : 0 ≤ bandSlow n := zero_le_one.trans (one_le_bandSlow n)
  have hb := hbound (f n) (hgood n) (C * ChartScales.epsilon h n ^ α * bandSlow n ^ q)
    (by positivity) (fun i hi x _ => hsource n i hi x (Set.mem_univ x)) (M n) hn j hj z
  calc
    _ ≤ K * (C * ChartScales.epsilon h n ^ α * bandSlow n ^ q) * (|M n|⁻¹) ^ p := hb
    _ = (K * C) * ChartScales.epsilon h n ^ α * bandSlow n ^ q * (|M n|⁻¹) ^ p := by ring
    _ ≤ (K * C) * ChartScales.epsilon h n ^ N := hgain

omit [FiniteDimensional ℝ S] in
theorem admissible_complexify {a b : ℝ} {f : ℝ × (S × Plane) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : SourcePeriodic f) (hm : ∀ p, sourceMean f p = 0)
    (hs : RadialAlias.RadiallySupported a b f) : Admissible a b (complexify f) := by
  refine ⟨complexify_smooth hf, ?_, ?_, complexify_supported hs⟩
  · intro p Y k
    exact congrArg Complex.ofReal (hp p.1 p.2 Y k)
  · intro p
    rw [mean_toProduct, sourceMean_complexify, hm p, Complex.ofReal_zero]

theorem real_totalIntegral_finiteJets (d : Direction) {a b : ℝ} (hab : a ≤ b) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      (∀ q, sourceMean f q = 0) → RadialAlias.RadiallySupported a b f →
      ∀ C : ℝ, 0 ≤ C → FiniteJetBound (m + 6 * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  obtain ⟨K, hK, hb⟩ := totalIntegral_finiteJets (S := S) d hab m p
  refine ⟨K, hK, ?_⟩
  intro f hf hp hm hs C hC hsource M hM j hj z
  rw [← norm_iteratedFDeriv_totalIntegral_complexify hf hs]
  apply hb (complexify f) (admissible_complexify hf hp hm hs) C hC _ M hM j hj z
  intro i hi x hx
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi x hx

theorem real_exactAlias_finiteJets (d : Direction) {a b : ℝ} {χ : ℝ → ℝ}
    (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      (∀ q, sourceMean f q = 0) → RadialAlias.RadiallySupported a b f →
      ∀ C : ℝ, 0 ≤ C → FiniteJetBound (m + 6 * p) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
        ‖iteratedFDeriv ℝ j (exactAlias χ M ((0 : S), vector d) f) z‖ ≤ K * C * (|M|⁻¹) ^ p := by
  obtain ⟨K, hK, hb⟩ := exactAlias_finiteJets (S := S) d hab hχ hleft hright m p
  refine ⟨K, hK, ?_⟩
  intro f hf hp hm hs C hC hsource M hM j hj z
  rw [← norm_iteratedFDeriv_exactAlias_complexify hχ hf hs]
  apply hb (complexify f) (admissible_complexify hf hp hm hs) C hC _ M hM j hj z
  intro i hi x hx
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi x hx

/-- Only the integrated torus mean must vanish. Mean subtraction costs four
extra finite derivative orders and changes the exact alias by zero. -/
theorem real_exactAlias_finiteJets_of_integratedMean_zero (d : Direction)
    {a b : ℝ} {χ : ℝ → ℝ} (hab : a ≤ b) (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ × (S × Plane) → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      (∀ s, (∫ U in a..b, sourceMean f (U, s)) = 0) → RadialAlias.RadiallySupported a b f →
      ∀ C : ℝ, 0 ≤ C → FiniteJetBound (m + 6 * p + 4) f (Prod.fst ⁻¹' Icc a b) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
        ‖iteratedFDeriv ℝ j (exactAlias χ M ((0 : S), vector d) f) z‖ ≤ K * C * (|M|⁻¹) ^ p := by
  obtain ⟨A, hA, ha⟩ := real_exactAlias_finiteJets (S := S) d hab hχ hleft hright m p
  obtain ⟨B, hB, hb⟩ := realCenterSource_finiteJets (S := S) a b (m + 6 * p)
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro f hf hp hm hs C hC hsource M hM j hj z
  rw [exactAlias_eq_realCenterSource χ hf hp hs hm]
  have h := ha (realCenterSource f) (realCenterSource_smooth hf hp) (realCenterSource_periodic hp)
    (realCenterSource_zeroMean hf hp) (realCenterSource_supported hs) (B * C) (mul_nonneg hB hC)
    (hb f C hf hp hC hsource) M hM j hj z
  simpa only [mul_assoc] using h

theorem realMeanClass_alias_superflat (d : Direction) {a b cL cR h α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n))
    (hm : ∀ n p, sourceMean (f n) p = 0)
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    {M : ℕ → ℝ} {κ A growth : ℝ} (hκ : 0 < κ)
    (hM : ∀ᶠ n in atTop, M n ≠ 0)
    (hfrequency : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
      ‖iteratedFDeriv ℝ j (exactAlias χ (M n) ((0 : S), vector d) (f n)) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  have hcomplex : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α
      (fun n => complexify (f n)) := hf.map Complex.ofRealCLM
  obtain ⟨C, hC, hb⟩ := meanClass_alias_superflat d ha hab hcL hcR hh hχ hleft hright hcomplex
    (fun n => admissible_complexify (hfc n) (hp n) (hm n) (hs n)) hκ hM hfrequency m N
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with n hn
  intro j hj z
  rw [← norm_iteratedFDeriv_exactAlias_complexify hχ (hfc n) (hs n)]
  exact hn j hj z

theorem radial_realMeanClass_alias_superflat {a b cL cR h α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n))
    (hm : ∀ n p, sourceMean (f n) p = 0)
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
      ‖iteratedFDeriv ℝ j
        (exactAlias χ (ChartScales.radialCoefficient h n) ((0 : S), vector .radial) (f n)) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  apply realMeanClass_alias_superflat .radial (A := ChartScales.Lambda) (growth := ChartScales.rho)
    ha hab hcL hcR hh hχ hleft hright hf hfc hp hm hs
    (show 0 < ChartScales.kappa by norm_num [ChartScales.kappa])
    (Filter.Eventually.of_forall (fun n => ne_of_gt (ChartScales.radialCoefficient_pos h n)))
    _ m N
  filter_upwards [eventually_ge_atTop 4] with n hn
  simpa only [abs_of_pos (ChartScales.radialCoefficient_pos h n)] using
    ChartScales.radialCoefficient_inv_upper h hh.le hn

theorem realMeanClass_alias_superflat_of_integratedMean_zero (d : Direction)
    {a b cL cR h α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n))
    (hm : ∀ n s, (∫ U in a..b, sourceMean (f n) (U, s)) = 0)
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n))
    {M : ℕ → ℝ} {κ A growth : ℝ} (hκ : 0 < κ)
    (hM : ∀ᶠ n in atTop, M n ≠ 0)
    (hfrequency : ∀ᶠ n in atTop, |M n|⁻¹ ≤
      A * ChartScales.epsilon h n ^ κ * ChartScales.S n ^ growth) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
      ‖iteratedFDeriv ℝ j (exactAlias χ (M n) ((0 : S), vector d) (f n)) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  have hcenter : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α
      (fun n => realCenterSource (f n)) :=
    meanClass_realCenterSource ha hcL hcR (ChartScales.epsilon h) bandSlow
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) one_le_bandSlow hf hfc hp
  obtain ⟨C, hC, hb⟩ := realMeanClass_alias_superflat d ha hab hcL hcR hh hχ hleft hright hcenter
    (fun n => realCenterSource_smooth (hfc n) (hp n)) (fun n => realCenterSource_periodic (hp n))
    (fun n => realCenterSource_zeroMean (hfc n) (hp n)) (fun n => realCenterSource_supported (hs n))
    hκ hM hfrequency m N
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with n hn
  intro j hj z
  rw [exactAlias_eq_realCenterSource χ (hfc n) (hp n) (hs n) (hm n)]
  exact hn j hj z

theorem radial_realMeanClass_alias_superflat_of_integratedMean_zero {a b cL cR h α : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    {f : ℕ → ℝ × (S × Plane) → ℝ}
    (hf : MeanClass (chartStrip a b cL cR ha hcL hcR h hh) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, SourcePeriodic (f n))
    (hm : ∀ n s, (∫ U in a..b, sourceMean (f n) (U, s)) = 0)
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ j ≤ m, ∀ z : ℝ × (S × Plane),
      ‖iteratedFDeriv ℝ j
        (exactAlias χ (ChartScales.radialCoefficient h n) ((0 : S), vector .radial) (f n)) z‖ ≤
        C * ChartScales.epsilon h n ^ N := by
  apply realMeanClass_alias_superflat_of_integratedMean_zero .radial
    (A := ChartScales.Lambda) (growth := ChartScales.rho)
    ha hab hcL hcR hh hχ hleft hright hf hfc hp hm hs
    (show 0 < ChartScales.kappa by norm_num [ChartScales.kappa])
    (Filter.Eventually.of_forall (fun n => ne_of_gt (ChartScales.radialCoefficient_pos h n)))
    _ m N
  filter_upwards [eventually_ge_atTop 4] with n hn
  simpa only [abs_of_pos (ChartScales.radialCoefficient_pos h n)] using
    ChartScales.radialCoefficient_inv_upper h hh.le hn

end UniformFamilies

end NavierStokes.UniformFourierAlias
