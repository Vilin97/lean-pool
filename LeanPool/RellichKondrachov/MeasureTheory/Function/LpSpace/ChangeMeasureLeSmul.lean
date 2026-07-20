/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul`

Transfer `L^p` spaces across comparable measures.

This file packages a common pattern used in manifold analysis: if two measures are comparable
up to a scalar multiple (`ν ≤ c • μ` with `c ≠ ∞`), then any `L^p(μ)` function is also in `L^p(ν)`,
and the identity map induces a bounded linear operator `Lp E p μ →L[ℝ] Lp E p ν`.

If the measures are mutually comparable (`ν ≤ c₁ • μ` and `μ ≤ c₂ • ν`), we get a continuous linear
equivalence between `Lp` spaces, and compactness of operators can be transported across it.

Tracking: Beads `lean-103.5.2.26.5.3.3.1`.
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
private lemma memLp_changeMeasure {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) (f : Lp E p μ) :
    MeasureTheory.MemLp (fun x : α => f x) p ν := by
  have hfμ : MeasureTheory.MemLp (fun x : α => f x) p μ := by
    simpa using (MeasureTheory.Lp.memLp f)
  exact
    MeasureTheory.MemLp.of_measure_le_smul
      (μ := μ) (μ' := ν) (p := p) (f := fun x : α => f x) hc hν hfμ

private noncomputable def changeMeasureFun {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) (f : Lp E p μ) :
    Lp E p ν :=
  (memLp_changeMeasure (μ := μ) (ν := ν) (p := p) hc hν f).toLp fun x : α => f x

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
private lemma changeMeasureFun_coe {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) (f : Lp E p μ) :
    (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f : α → E) =ᵐ[ν] f := by
    simpa [changeMeasureFun] using
      (MeasureTheory.MemLp.coeFn_toLp (memLp_changeMeasure (μ := μ) (ν := ν) (p := p) hc hν f))

/-- The identity map as a linear map `Lp E p μ →ₗ[ℝ] Lp E p ν` under a measure bound `ν ≤ c • μ`. -/
noncomputable def changeMeasureₗ {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) :
    Lp E p μ →ₗ[ℝ] Lp E p ν where
  toFun := changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν
  map_add' f g := by
    classical
    refine MeasureTheory.Lp.ext ?_
    have habs : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
    have haddμ : ⇑(f + g) =ᵐ[ν] (f + g) :=
      habs.ae_le (by
        exact (MeasureTheory.Lp.coeFn_add (μ := μ) f g))
    filter_upwards
      [ changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν (f + g)
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν f
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν g
      , haddμ
      , MeasureTheory.Lp.coeFn_add
          (μ := ν)
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f)
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g)
      ] with x hfg hf hg haddμ hadd
    have hadd' :
        (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x +
            (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x =
          (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f +
              changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := by
      simpa [Pi.add_apply] using hadd.symm
    calc
      changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν (f + g) x = (f + g) x := by
            simpa using hfg
      _ = f x + g x := by
            simpa [Pi.add_apply] using haddμ
      _ = (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x +
            (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := by
            simp [hf, hg]
      _ = (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f +
            changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν g) x := hadd'
  map_smul' r f := by
    classical
    refine MeasureTheory.Lp.ext ?_
    have habs : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
    have hsmulμ : ⇑(r • f) =ᵐ[ν] (r • (f : α → E)) :=
      habs.ae_le (by
        exact (MeasureTheory.Lp.coeFn_smul (μ := μ) r f))
    filter_upwards
      [ changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν (r • f)
      , changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc hν f
      , hsmulμ
      , MeasureTheory.Lp.coeFn_smul (μ := ν) r (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f)
      ] with x hrf hf hsmulμ hsmul
    have hsmul' :
        r • (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x =
          (r • changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := by
      simpa [Pi.smul_apply] using hsmul.symm
    calc
      changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν (r • f) x = (r • f) x := by
            simpa using hrf
      _ = r • f x := by
            simpa [Pi.smul_apply] using hsmulμ
      _ = r • (changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := by
            simp [hf]
      _ = (r • changeMeasureFun (μ := μ) (ν := ν) (p := p) hc hν f) x := hsmul'

omit [Fact (1 ≤ p)] in
private lemma norm_changeMeasureFun_le {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) (f : Lp E p μ) :
    p ≠ ∞ →
    ‖changeMeasureₗ (μ := μ) (ν := ν) (E := E) (p := p) hc hν f‖ ≤
      ENNReal.toReal (c ^ (1 / p).toReal) * ‖f‖ := by
  classical
  intro hp
  have hfν : MeasureTheory.MemLp (fun x : α => f x) p ν :=
    memLp_changeMeasure (μ := μ) (ν := ν) (p := p) hc hν f
  have hnorm_out :
      ‖changeMeasureₗ (μ := μ) (ν := ν) (E := E) (p := p) hc hν f‖ =
        ENNReal.toReal (MeasureTheory.eLpNorm (fun x : α => f x) p ν) := by
    dsimp [changeMeasureₗ, changeMeasureFun]
    simp [MeasureTheory.Lp.norm_toLp (f := fun x : α => f x) hfν]
  have hle_eLpNorm :
      MeasureTheory.eLpNorm (fun x : α => f x) p ν ≤
        (c ^ (1 / p).toReal) * MeasureTheory.eLpNorm (fun x : α => f x) p μ := by
    have hmono :
        MeasureTheory.eLpNorm (fun x : α => f x) p ν ≤
          MeasureTheory.eLpNorm (fun x : α => f x) p (c • μ) :=
      MeasureTheory.eLpNorm_mono_measure (f := fun x : α => f x) (p := p) (ν := ν) (μ := c • μ) hν
    -- Expand the `smul` measure scaling.
    have hscale :
        MeasureTheory.eLpNorm (fun x : α => f x) p (c • μ) =
          (c ^ (1 / p).toReal) * MeasureTheory.eLpNorm (fun x : α => f x) p μ := by
      simpa [ENNReal.smul_def, mul_assoc, mul_left_comm, mul_comm] using
        (MeasureTheory.eLpNorm_smul_measure_of_ne_top
          (μ := μ) (p := p) (f := fun x : α => f x) hp c)
    exact hmono.trans_eq hscale
  have htoReal :
      ENNReal.toReal (MeasureTheory.eLpNorm (fun x : α => f x) p ν) ≤
        ENNReal.toReal ((c ^ (1 / p).toReal) * MeasureTheory.eLpNorm (fun x : α => f x) p μ) := by
    refine (ENNReal.toReal_le_toReal ?_ ?_).2 hle_eLpNorm
    · exact hfν.2.ne
    · have hfμ : MeasureTheory.MemLp (fun x : α => f x) p μ := by
        simpa using (MeasureTheory.Lp.memLp f)
      have hfμ_ne : MeasureTheory.eLpNorm (fun x : α => f x) p μ ≠ ∞ := hfμ.2.ne
      have hcPow : c ^ (1 / p).toReal ≠ ∞ := by
        have hy0 : 0 ≤ (1 / p).toReal := by
          exact ENNReal.toReal_nonneg
        exact ENNReal.rpow_ne_top_of_nonneg hy0 hc
      exact ENNReal.mul_ne_top hcPow hfμ_ne
  -- Finish.
  rw [hnorm_out]
  refine htoReal.trans_eq ?_
  -- Rewrite the RHS to match the `Lp` norms.
  simp [ENNReal.toReal_mul, MeasureTheory.Lp.norm_def]

/-- The identity map as a continuous linear map `Lp E p μ →L[ℝ] Lp E p ν` under `ν ≤ c • μ`.

This is stated for `p ≠ ∞` (the only case needed in this repo; in particular we use `p = 2`). -/
noncomputable def changeMeasureL {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ) (hp : p ≠ ∞) :
    Lp E p μ →L[ℝ] Lp E p ν :=
  (changeMeasureₗ (μ := μ) (ν := ν) (E := E) (p := p) hc hν).mkContinuous
    (ENNReal.toReal (c ^ (1 / p).toReal))
    (by
      intro f
      exact norm_changeMeasureFun_le (μ := μ) (ν := ν) (E := E) (p := p) hc hν f hp)

lemma changeMeasureL_coeFn_ae_eq {c : ℝ≥0∞} (hc : c ≠ ∞) (hν : ν ≤ c • μ)
    (hp : p ≠ ∞) (f : Lp E p μ) :
    (changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc hν hp f : α → E) =ᵐ[ν] f := by
  -- `mkContinuous` does not change the underlying function.
  simpa [changeMeasureL, changeMeasureₗ, changeMeasureFun] using
    (changeMeasureFun_coe (μ := μ) (ν := ν) (E := E) (p := p) (c := c) hc hν f)

lemma changeMeasureL_congr {c : ℝ≥0∞} (hc₁ hc₂ : c ≠ ∞) (hν₁ hν₂ : ν ≤ c • μ) (hp₁ hp₂ : p ≠ ∞) :
    changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc₁ hν₁ hp₁ =
      changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc₂ hν₂ hp₂ := by
  refine ContinuousLinearMap.ext ?_
  intro f
  refine MeasureTheory.Lp.ext (μ := ν) (E := E) (p := p) ?_
  have h₁ :
      (changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc₁ hν₁ hp₁ f : α → E) =ᵐ[ν] f :=
    changeMeasureL_coeFn_ae_eq (μ := μ) (ν := ν) (E := E) (p := p) hc₁ hν₁ hp₁ f
  have h₂ :
      (changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc₂ hν₂ hp₂ f : α → E) =ᵐ[ν] f :=
    changeMeasureL_coeFn_ae_eq (μ := μ) (ν := ν) (E := E) (p := p) hc₂ hν₂ hp₂ f
  exact h₁.trans h₂.symm

/-!
## Mutual comparability: `Lp` equivalence

If we have *both* `ν ≤ c₁ • μ` and `μ ≤ c₂ • ν` (with finite constants), then the identity
map gives a continuous linear equivalence between the two `Lp` spaces.
-/

/-- If `ν ≤ c₁ • μ` and `μ ≤ c₂ • ν` (with `c₁, c₂ ≠ ∞`) and `p ≠ ∞`,
then the identity map induces a continuous linear equivalence
`Lp E p μ ≃L[ℝ] Lp E p ν`. -/
noncomputable def changeMeasureEquiv {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (hν : ν ≤ c₁ • μ) (hμ : μ ≤ c₂ • ν) (hp : p ≠ ∞) :
    Lp E p μ ≃L[ℝ] Lp E p ν := by
  classical
  let fwd : Lp E p μ →L[ℝ] Lp E p ν :=
    changeMeasureL (μ := μ) (ν := ν) (E := E) (p := p) hc₁ hν hp
  let bwd : Lp E p ν →L[ℝ] Lp E p μ :=
    changeMeasureL (μ := ν) (ν := μ) (E := E) (p := p) hc₂ hμ hp
  refine
    ContinuousLinearEquiv.equivOfInverse'
      (f₁ := fwd) (f₂ := bwd) ?_ ?_
  · refine ContinuousLinearMap.ext ?_
    intro g
    refine (Lp.ext (μ := ν) (E := E) (p := p) ?_)
    have habs : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
    have hbwdμ : (bwd g : α → E) =ᵐ[μ] g := by
      simpa [bwd, changeMeasureL, changeMeasureₗ] using
        (changeMeasureFun_coe (μ := ν) (ν := μ) (p := p) hc₂ hμ g)
    have hbwdν : (bwd g : α → E) =ᵐ[ν] g := habs.ae_le hbwdμ
    have hfwd : (fwd (bwd g) : α → E) =ᵐ[ν] (bwd g) := by
      simpa [fwd, bwd, changeMeasureL, changeMeasureₗ] using
        (changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc₁ hν (bwd g))
    filter_upwards [hfwd, hbwdν] with x hfwd hbwd
    exact hfwd.trans hbwd
  · refine ContinuousLinearMap.ext ?_
    intro f
    refine (Lp.ext (μ := μ) (E := E) (p := p) ?_)
    have habs : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hμ
    have hbwd : (bwd (fwd f) : α → E) =ᵐ[μ] (fwd f) := by
      simpa [fwd, bwd, changeMeasureL, changeMeasureₗ] using
        (changeMeasureFun_coe (μ := ν) (ν := μ) (p := p) hc₂ hμ (fwd f))
    have hfwdν : (fwd f : α → E) =ᵐ[ν] f := by
      simpa [fwd, changeMeasureL, changeMeasureₗ] using
        (changeMeasureFun_coe (μ := μ) (ν := ν) (p := p) hc₁ hν f)
    have hfwdμ : (fwd f : α → E) =ᵐ[μ] f := habs.ae_le hfwdν
    filter_upwards [hbwd, hfwdμ] with x hbwd hfwd
    exact hbwd.trans hfwd

lemma changeMeasureEquiv_coeFn_ae_eq {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (hν : ν ≤ c₁ • μ) (hμ : μ ≤ c₂ • ν) (hp : p ≠ ∞) (f : Lp E p μ) :
    (changeMeasureEquiv (μ := μ) (ν := ν) (E := E) (p := p)
      hc₁ hc₂ hν hμ hp f : α → E) =ᵐ[ν] f := by
  -- Unfold `changeMeasureEquiv` and use the defining `changeMeasureL` coherence lemma.
  classical
  -- The forward map is `changeMeasureL`; it is a.e. equal to the identity under `ν`.
  simp [changeMeasureEquiv,
    changeMeasureL_coeFn_ae_eq (μ := μ) (ν := ν) (E := E) (p := p) hc₁ hν hp]
/-!
## Compactness transport

Pre- and post-composition by continuous linear equivalences preserves compactness.
-/

lemma isCompactOperator_comp_continuousLinearEquiv_iff {F : Type*} [TopologicalSpace F]
    [AddCommMonoid F] [Module ℝ F] (e : Lp E p μ ≃L[ℝ] Lp E p ν) (T : Lp E p ν →L[ℝ] F) :
    IsCompactOperator (T.comp e.toContinuousLinearMap) ↔ IsCompactOperator T := by
  constructor
  · intro h
    have h' : IsCompactOperator ((T.comp e.toContinuousLinearMap) ∘ e.symm.toContinuousLinearMap) :=
      h.comp_clm (e.symm.toContinuousLinearMap)
    have hcomp :
        (⇑(T.comp e.toContinuousLinearMap) ∘ ⇑e.symm.toContinuousLinearMap) =
          (⇑T : Lp E p ν → F) := by
      funext x
      simp [Function.comp]
    -- `h'` is stated in terms of coercions, so rewrite it to recover compactness of `T`.
    rw [hcomp] at h'
    exact h'
  · intro h
    have hc : IsCompactOperator (⇑T ∘ ⇑(e.toContinuousLinearMap)) :=
      h.comp_clm (e.toContinuousLinearMap)
    rwa [← ContinuousLinearMap.coe_comp] at hc

end

end Lp

end MeasureTheory
