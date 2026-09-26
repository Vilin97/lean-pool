/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import LeanPool.SNumbers.BasicResults.Spectral.MonotoneConvergence

/-!
# The spectral projection of `S*S` over `ℂ`

*Why this file is needed:* it supplies the **complex** spectral projection,
`exists_spectral_projection_complex`. The real case (`RealProjection`) and the uniform `RCLike`
projection (`Representation`) both reduce to it.

The complex-Hilbert-space operator algebra `H →L[ℂ] H` is a C⋆-algebra, so Mathlib's continuous
functional calculus applies to `P = S*S`. The projection `E = E_{[c²,∞)}(P)` is built as the
strong-operator limit of `cfc gₙ P`, where `gₙ` is a continuous approximation decreasing to the
indicator `𝟙_{[c²,∞)}`. This file also proves `cfc_comm_of_comm`: anything commuting with `P`
commutes with `E` — the ingredient that makes the projection conjugation/scalar invariant (used
by `RealProjection` and `Representation`).

## The approximating family `stepDown`

`stepDown t n` is the continuous function equal to `1` on `[t, ∞)`, ramping
linearly down to `0` on `[t - 1/(n+1), t]`, and `0` below. As `n → ∞` it
decreases pointwise to `𝟙_{[t,∞)}`. This part of the file develops its
elementary properties (continuity, `0 ≤ · ≤ 1`, antitone in `n`, value `1`
above the threshold).
-/

@[expose] public section

open ContinuousLinearMap

namespace SpectralRepresentation

/-- Continuous approximation, from above, of the indicator `𝟙_{[t,∞)}`:
`stepDown t n` is `1` for `s ≥ t`, ramps down to `0` over `[t - 1/(n+1), t]`,
and is `0` below `t - 1/(n+1)`. -/
noncomputable def stepDown (t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  max 0 (min 1 (1 + ((n : ℝ) + 1) * (s - t)))

@[fun_prop]
lemma stepDown_continuous (t : ℝ) (n : ℕ) : Continuous (stepDown t n) := by
  unfold stepDown; fun_prop

lemma stepDown_nonneg (t : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ stepDown t n s :=
  le_max_left _ _

lemma stepDown_le_one (t : ℝ) (n : ℕ) (s : ℝ) : stepDown t n s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- Above the threshold the approximation is exactly `1`. -/
lemma stepDown_eq_one (t : ℝ) (n : ℕ) {s : ℝ} (hs : t ≤ s) : stepDown t n s = 1 := by
  have h0 : 0 ≤ ((n : ℝ) + 1) * (s - t) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hs)
  rw [stepDown, min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The family is antitone in `n`: a larger `n` gives a steeper ramp, hence a
smaller value below the threshold (and `1` above). -/
lemma stepDown_antitone (t s : ℝ) : Antitone (fun n => stepDown t n s) := by
  intro m n hmn
  change stepDown t n s ≤ stepDown t m s
  rcases le_total t s with hts | hst
  · rw [stepDown_eq_one t n hts, stepDown_eq_one t m hts]
  · refine max_le_max le_rfl (min_le_min le_rfl ?_)
    have hst' : s - t ≤ 0 := by linarith
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith [hst', hmn']

/-- **Uniform ramp estimate.** `(s - t) · stepDown t n` is within `1/(n+1)` of
`(s - t)⁺ = max (s - t) 0`, uniformly in `s`. This drives the norm convergence
`cfc ((s-t)·stepDownₙ) P → cfc (s-t)⁺ P` (no Dini theorem needed: the bound is
explicit). -/
lemma stepDown_ramp_bound (t : ℝ) (n : ℕ) (s : ℝ) :
    |(s - t) * stepDown t n s - max (s - t) 0| ≤ ((n : ℝ) + 1)⁻¹ := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases le_total t s with hts | hst
  · rw [stepDown_eq_one t n hts, max_eq_left (by linarith : (0 : ℝ) ≤ s - t), mul_one,
      sub_self, abs_zero]
    positivity
  · rw [max_eq_right (by linarith : s - t ≤ (0 : ℝ)), sub_zero,
      abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (stepDown_nonneg t n s)),
      show -((s - t) * stepDown t n s) = (t - s) * stepDown t n s by ring]
    refine (mul_le_mul_of_nonneg_left
      (max_le_max le_rfl (min_le_right (1 : ℝ) _) : stepDown t n s ≤ max 0 (1 + ((n : ℝ) + 1) *
          (s - t)))
      (by linarith : (0 : ℝ) ≤ t - s)).trans ?_
    rcases le_total (1 + ((n : ℝ) + 1) * (s - t)) 0 with h | h
    · rw [max_eq_left h, mul_zero]; positivity
    · rw [max_eq_right h, inv_eq_one_div, le_div_iff₀ hn1]
      nlinarith [sq_nonneg (((n : ℝ) + 1) * (t - s) - 1 / 2)]

open Filter Topology
open scoped InnerProductSpace

variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- **Commutation engine.** A continuous `ℝ`-linear map `J` of `H₁` that commutes with a
self-adjoint `P` commutes with `cfcHom hP f` for *every* continuous symbol `f`. Proved by the
Stone–Weierstrass induction on `f` (constants, `id`, sums, products, and a closure step), exactly
as Mathlib's `Commute.cfcHom` — but here `J` is an *external* map (it may even be conjugate-linear
over `ℂ`, only `ℝ`-linearity is used), which is why we cannot use the algebra-internal version. -/
lemma cfcHom_comm_of_comm {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P)
    (J : H₁ →L[ℝ] H₁) (hJP : ∀ x, J (P x) = P (J x)) (f : C(spectrum ℝ P, ℝ)) :
    ∀ x, J (cfcHom hP f x) = cfcHom hP f (J x) := by
  open scoped ContinuousFunctionalCalculus in
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
      intro x
      rw [show (ContinuousMap.const (spectrum ℝ P) r) = algebraMap ℝ C(spectrum ℝ P, ℝ) r from rfl,
        AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
      simp only [smul_apply, one_apply_eq_self, map_smul]
  | id => intro x; rw [cfcHom_id hP]; exact hJP x
  | star_id => intro x; rw [map_star, cfcHom_id hP, hP.star_eq]; exact hJP x
  | add f g hf hg =>
      intro x
      rw [map_add, add_apply, add_apply, map_add, hf x, hg x]
  | mul f g hf hg =>
      intro x
      rw [map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
        hf (cfcHom hP g x), hg x]
  | frequently f hf =>
      have hSclosed : IsClosed {g : C(spectrum ℝ P, ℝ) |
          ∀ x, J (cfcHom hP g x) = cfcHom hP g (J x)} := by
        rw [Set.ofPred_forall]
        exact isClosed_iInter fun x => isClosed_eq
          (J.continuous.comp ((cfcHom_continuous hP).clm_apply continuous_const))
          ((cfcHom_continuous hP).clm_apply continuous_const)
      have hmem : f ∈ closure {g : C(spectrum ℝ P, ℝ) |
          ∀ x, J (cfcHom hP g x) = cfcHom hP g (J x)} := mem_closure_iff_frequently.mpr hf
      rwa [hSclosed.closure_eq] at hmem

/-- A continuous `ℝ`-linear map `J` commuting with a self-adjoint `P` commutes with `cfc g P`
for every continuous `g`. -/
lemma cfc_comm_of_comm {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P) (J : H₁ →L[ℝ] H₁)
    (hJP : ∀ x, J (P x) = P (J x)) {g : ℝ → ℝ} (hg : Continuous g) (x : H₁) :
    J (cfc g P x) = cfc g P (J x) := by
  rw [cfc_apply (a := P) (ha := hP) (hf := hg.continuousOn)]
  exact cfcHom_comm_of_comm hP J hJP _ x

/-- **Spectral projection of `S*S` (over `ℂ`).** -/
theorem exists_spectral_projection_complex [Nontrivial H₁]
    (S : H₁ →L[ℂ] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[ℂ] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c ∧
        ∀ J : H₁ →L[ℝ] H₁, (∀ x, J (((adjoint S).comp S) x) = ((adjoint S).comp S) (J x)) →
          ∀ x, J (E x) = E (J x) := by
  classical
  set P : H₁ →L[ℂ] H₁ := (adjoint S).comp S with hPdef
  have hPsa : IsSelfAdjoint P := by
    rw [hPdef, ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  set T : ℕ → (H₁ →L[ℂ] H₁) := fun n => cfc (stepDown (c ^ 2) n) P with hTdef
  have hTpos : ∀ n, (T n).IsPositive := by
    intro n
    have h0 : (0 : H₁ →L[ℂ] H₁) ≤ T n :=
      cfc_nonneg (fun s _ => stepDown_nonneg (c ^ 2) n s)
    rwa [ContinuousLinearMap.le_def, sub_zero] at h0
  have hTanti : Antitone T := fun m n hmn => by
    change cfc (stepDown (c ^ 2) n) P ≤ cfc (stepDown (c ^ 2) m) P
    exact (cfc_le_iff (stepDown (c ^ 2) n) (stepDown (c ^ 2) m) P
      (stepDown_continuous (c ^ 2) n).continuousOn
      (stepDown_continuous (c ^ 2) m).continuousOn).mpr
      fun s _ => stepDown_antitone (c ^ 2) s hmn
  obtain ⟨E, hEtend⟩ := exists_continuousLinearMap_tendsto hTpos hTanti
  -- `‖S u‖² = re⟪P u, u⟫`.
  have hSnorm : ∀ u : H₁, ‖S u‖ ^ 2 = RCLike.re (⟪P u, u⟫_ℂ) := fun u => by
    rw [hPdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq]
  -- `P` is positive, hence its spectrum is nonnegative.
  have hPpos : P.IsPositive := by
    refine ⟨fun x y => ?_, fun u => ?_⟩
    · change ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ
      rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.isSelfAdjoint_iff'.mp hPsa]
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← hSnorm u]; positivity
  have hP0 : (0 : H₁ →L[ℂ] H₁) ≤ P := by
    rw [ContinuousLinearMap.le_def, sub_zero]; exact hPpos
  -- Composition of two continuous functions of `P` multiplies the symbols.
  have hcomp : ∀ f g : ℝ → ℝ, Continuous f → Continuous g →
      (cfc f P).comp (cfc g P) = cfc (fun s => f s * g s) P := fun f g hf hg => by
    rw [cfc_mul f g P hf.continuousOn hg.continuousOn]; rfl
  have hcompP : ∀ g : ℝ → ℝ, Continuous g →
      P.comp (cfc g P) = cfc (fun s => s * g s) P := fun g hg => by
    rw [cfc_mul (R := ℝ) (fun s : ℝ => s) g P (by fun_prop) hg.continuousOn,
      cfc_id' (R := ℝ) (a := P) (ha := hPsa)]; rfl
  -- `1 - T n` as a continuous function of `P`.
  have hii : ∀ n, (1 : H₁ →L[ℂ] H₁) - T n = cfc (fun s => 1 - stepDown (c ^ 2) n s) P := by
    intro n
    rw [cfc_sub (fun _ => (1 : ℝ)) (stepDown (c ^ 2) n) P (by fun_prop) (by fun_prop),
      cfc_const _ _ hPsa, map_one]
  -- `(1 - T n) ∘ P ∘ (1 - T n)` as a continuous function of `P`.
  have htriple : ∀ n, (1 - T n).comp (P.comp (1 - T n))
      = cfc (fun s => (1 - stepDown (c ^ 2) n s) ^ 2 * s) P := by
    intro n
    rw [hii n, hcompP (fun s => 1 - stepDown (c ^ 2) n s) (by fun_prop),
      hcomp _ _ (by fun_prop) (by fun_prop)]
    congr 1; ext s; ring
  -- Key per-`n` operator bound: `(1 - T n) P (1 - T n) ≤ c² • 1`.
  have hkey : ∀ n, (1 - T n).comp (P.comp (1 - T n)) ≤ c ^ 2 • (1 : H₁ →L[ℂ] H₁) := by
    intro n
    rw [htriple n, show c ^ 2 • (1 : H₁ →L[ℂ] H₁) = cfc (fun _ : ℝ => c ^ 2) P by
      rw [cfc_const _ _ hPsa, Algebra.algebraMap_eq_smul_one],
      cfc_le_iff _ _ P (by fun_prop) (by fun_prop)]
    intro s hs
    have hs0 : 0 ≤ s := spectrum_nonneg_of_nonneg hP0 hs
    have hg0 : 0 ≤ 1 - stepDown (c ^ 2) n s := by
      have := stepDown_le_one (c ^ 2) n s; linarith
    have hg1 : 1 - stepDown (c ^ 2) n s ≤ 1 := by
      have := stepDown_nonneg (c ^ 2) n s; linarith
    rcases le_total s (c ^ 2) with hsc | hsc
    · have h2 : (1 - stepDown (c ^ 2) n s) ^ 2 ≤ 1 := pow_le_one₀ hg0 hg1
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) hs0, hsc]
    · rw [stepDown_eq_one (c ^ 2) n hsc]
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_mul, ge_iff_le]
      positivity
  have hQsa : ∀ n, IsSelfAdjoint (1 - T n) := fun n => by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, ContinuousLinearMap.adjoint_one,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (hTpos n).isSelfAdjoint]
  refine ⟨E, ?_, ?_, ?_⟩
  · -- bound (a): `c · ‖E x‖ ≤ ‖S (E x)‖`.
    set A : H₁ →L[ℂ] H₁ := cfc (fun s => max (s - c ^ 2) 0) P with hA_def
    have hA0 : (0 : H₁ →L[ℂ] H₁) ≤ A := cfc_nonneg fun s _ => le_max_right _ _
    have hEpos : E.IsPositive := isPositive_of_tendsto hTpos hEtend
    have hE0 : (0 : H₁ →L[ℂ] H₁) ≤ E := by
      rw [ContinuousLinearMap.le_def, sub_zero]; exact hEpos
    have hEsymm : (E : H₁ →ₗ[ℂ] H₁).IsSymmetric :=
      isSymmetric_of_tendsto (fun n => (hTpos n).1) hEtend
    have hDcfc : cfc (fun s => s - c ^ 2) P = P - c ^ 2 • (1 : H₁ →L[ℂ] H₁) := by
      rw [cfc_sub (fun s => s) (fun _ => c ^ 2) P (by fun_prop) (by fun_prop),
        cfc_id' (R := ℝ) (a := P) (ha := hPsa), cfc_const _ _ hPsa, Algebra.algebraMap_eq_smul_one]
    have hcfcT : ∀ n, (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)
        = cfc (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s) P := fun n => by
      rw [← hDcfc]
      exact hcomp (fun s => s - c ^ 2) (stepDown (c ^ 2) n) (by fun_prop) (by fun_prop)
    have hnorm : Tendsto (fun n => (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) atTop (𝓝 A) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (g := fun n : ℕ => ((n : ℝ) + 1)⁻¹)
        (fun n => norm_nonneg _) (fun n => ?_) ?_
      · have hsub : (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A
            = cfc (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s - max (s - c ^ 2) 0) P := by
          rw [hcfcT n, hA_def,
            ← cfc_sub (fun s => (s - c ^ 2) * stepDown (c ^ 2) n s) (fun s => max (s - c ^ 2) 0) P
              (by fun_prop) (by fun_prop)]
        rw [hsub]
        exact norm_cfc_le (by positivity)
          fun s _ => by simpa [Real.norm_eq_abs] using stepDown_ramp_bound (c ^ 2) n s
      · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simp only [one_div] at h
        exact h
    have hDE : (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp E = A := by
      ext x
      have hb : Tendsto
          (fun n => ‖(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp hnorm
      have h1 : Tendsto (fun n => ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) x) atTop
          (𝓝 (((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp E) x)) := by
        simp only [ContinuousLinearMap.comp_apply]
        exact ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).continuous.tendsto _).comp (hEtend x)
      have h2 : Tendsto (fun n => ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n)) x) atTop (𝓝 (A
          x)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hb.mul_const ‖x‖)
        rw [← sub_apply]
        exact ((P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)).comp (T n) - A).le_opNorm x
      exact tendsto_nhds_unique h1 h2
    have hEA : E.comp A = A.comp E := by
      refine commute_of_tendsto (fun n => ?_) hEtend
      change (cfc (stepDown (c ^ 2) n) P).comp A = A.comp (cfc (stepDown (c ^ 2) n) P)
      rw [hA_def, hcomp _ _ (by fun_prop) (by fun_prop), hcomp _ _ (by fun_prop) (by fun_prop)]
      congr 1; ext s; ring
    have hEcomp0 : (0 : H₁ →L[ℂ] H₁) ≤ E.comp A := Commute.mul_nonneg hE0 hA0 hEA
    have hEcompPos : (E.comp A).IsPositive := by
      rw [ContinuousLinearMap.le_def, sub_zero] at hEcomp0; exact hEcomp0
    intro x
    have hsymm_eq : ⟪A x, E x⟫_ℂ = ⟪(E.comp A) x, x⟫_ℂ := by
      rw [ContinuousLinearMap.comp_apply]; exact (hEsymm (A x) x).symm
    have hkey_a : 0 ≤ RCLike.re (⟪(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x), E x⟫_ℂ) := by
      rw [show (P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x) = A x by
            rw [← ContinuousLinearMap.comp_apply, hDE],
        hsymm_eq, ← ContinuousLinearMap.reApplyInnerSelf_apply]
      exact hEcompPos.2 x
    have hexpand : RCLike.re (⟪(P - c ^ 2 • (1 : H₁ →L[ℂ] H₁)) (E x), E x⟫_ℂ)
        = ‖S (E x)‖ ^ 2 - c ^ 2 * ‖E x‖ ^ 2 := by
      rw [sub_apply, inner_sub_left, map_sub, ← hSnorm (E x)]
      congr 1
      rw [smul_apply, one_apply_eq_self,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hsqle : c ^ 2 * ‖E x‖ ^ 2 ≤ ‖S (E x)‖ ^ 2 := by
      have h := hkey_a; rw [hexpand] at h; linarith
    exact le_of_sq_le_sq (by rw [mul_pow]; exact hsqle) (norm_nonneg _)
  · -- bound (b): `‖S ∘ (1 - E)‖ ≤ c`.
    refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun y => ?_
    rw [ContinuousLinearMap.comp_apply]
    have hrhs : RCLike.re (⟪(c ^ 2 • (1 : H₁ →L[ℂ] H₁)) y, y⟫_ℂ) = c ^ 2 * ‖y‖ ^ 2 := by
      rw [smul_apply, one_apply_eq_self,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, RCLike.conj_ofReal,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hpern : ∀ n, RCLike.re (⟪P ((1 - T n) y), (1 - T n) y⟫_ℂ) ≤ c ^ 2 * ‖y‖ ^ 2 := by
      intro n
      have hmono := reApplyInnerSelf_mono (hkey n) y
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.reApplyInnerSelf_apply,
        hrhs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp (hQsa n)] at hmono
      exact hmono
    have hu : Tendsto (fun n => (1 - T n) y) atTop (𝓝 ((1 - E) y)) := by
      simp only [sub_apply, one_apply_eq_self]
      exact tendsto_const_nhds.sub (hEtend y)
    have hlim : RCLike.re (⟪P ((1 - E) y), (1 - E) y⟫_ℂ) ≤ c ^ 2 * ‖y‖ ^ 2 :=
      le_of_tendsto'
        ((RCLike.continuous_re.tendsto _).comp (((P.continuous.tendsto _).comp hu).inner hu)) hpern
    have hsq : ‖S ((1 - E) y)‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by
      rw [hSnorm ((1 - E) y), mul_pow]; exact hlim
    exact le_of_sq_le_sq hsq (mul_nonneg hc0 (norm_nonneg _))
  · -- commutation: `E` commutes with any `ℝ`-linear `J` commuting with `P = S*S`.
    intro J hJ x
    have hcomm : ∀ n, J (T n x) = T n (J x) := fun n =>
      cfc_comm_of_comm hPsa J hJ (stepDown_continuous (c ^ 2) n) x
    have l1 : Tendsto (fun n => J (T n x)) atTop (𝓝 (J (E x))) :=
      (J.continuous.tendsto _).comp (hEtend x)
    have l2 : Tendsto (fun n => J (T n x)) atTop (𝓝 (E (J x))) := by
      simp only [hcomm]; exact hEtend (J x)
    exact tendsto_nhds_unique l1 l2

end SpectralRepresentation

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
