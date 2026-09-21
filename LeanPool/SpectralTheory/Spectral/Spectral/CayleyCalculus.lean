/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.SpectralTheory.Spectral.Cayley.Basic
import LeanPool.SpectralTheory.Spectral.PVM.Unbounded

/-!
# Cayley spectral calculus

This module connects the bounded Cayley transform with unbounded coordinate integration. Its main
result turns a PVM representation of the scalar Cayley phase into containment of the original
self-adjoint operator, after which self-adjoint maximality upgrades containment to equality.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem PVM.integral_congr (E_pvm : PVM E) {f g : ℝ → ℂ}
    (hfg : f = g) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ r, ‖f r‖ ≤ C) (hbddg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    E_pvm.integral f hf hbddf = E_pvm.integral g hg hbddg := by
  subst g
  rfl

private theorem PVM.integral_one (E_pvm : PVM E) :
    E_pvm.integral (fun _ : ℝ => (1 : ℂ)) measurable_const
      ⟨1, fun _ => by rw [norm_one]⟩ = 1 := by
  have hUniform : TendstoUniformly
      (fun (_n : ℕ) (r : ℝ) => (1 : SimpleFunc ℝ ℂ) r)
      (fun _r : ℝ => (1 : ℂ)) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    apply Filter.Eventually.of_forall
    intro n r
    change dist (1 : ℂ) 1 < ε
    rw [dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (fun _ : ℝ => (1 : ℂ)) measurable_const
    ⟨1, fun _ => by rw [norm_one]⟩
    (fun _n => (1 : SimpleFunc ℝ ℂ)) hUniform
  have hone : Filter.Tendsto (fun _n : ℕ => (1 : E →L[ℂ] E))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  apply tendsto_nhds_unique hlim
  simpa only [E_pvm.simpleIntegral_one] using hone

private theorem PVM.integral_const (E_pvm : PVM E) (z : ℂ) :
    E_pvm.integral (fun _ : ℝ => z) measurable_const
      ⟨‖z‖, fun _ => le_refl _⟩ = z • 1 := by
  have hUniform : TendstoUniformly
      (fun (_n : ℕ) (r : ℝ) => SimpleFunc.const ℝ z r)
      (fun _r : ℝ => z) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    apply Filter.Eventually.of_forall
    intro n r
    change dist z z < ε
    rw [dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (fun _ : ℝ => z) measurable_const ⟨‖z‖, fun _ => le_refl _⟩
    (fun _n => SimpleFunc.const ℝ z) hUniform
  have hconst : Filter.Tendsto (fun _n : ℕ => z • (1 : E →L[ℂ] E))
      Filter.atTop (nhds (z • 1)) := tendsto_const_nhds
  apply tendsto_nhds_unique hlim
  simpa only [E_pvm.simpleIntegral_const] using hconst

private theorem sub_bounded
    (f g : ℝ → ℂ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    ∃ C, ∀ r, ‖f r - g r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun r => ?_⟩
  exact (norm_sub_le (f r) (g r)).trans (add_le_add (hC r) (hD r))

private theorem mul_bounded
    (f g : ℝ → ℂ) (hf : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (hg : ∃ C, ∀ r, ‖g r‖ ≤ C) :
    ∃ C, ∀ r, ‖(f * g) r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  refine ⟨C * D, fun r => ?_⟩
  change ‖f r * g r‖ ≤ C * D
  rw [norm_mul]
  exact mul_le_mul (hC r) (hD r) (norm_nonneg (g r)) hC0

/-- If a PVM integrates a bounded Cayley phase to the Cayley transform of a self-adjoint
operator, then that operator is contained in the PVM's coordinate integral. -/
theorem PVM.selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
    (E_pvm : PVM E) (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (phase : ℝ → ℂ) (hphaseMeas : Measurable phase)
    (hphaseBdd : ∃ C, ∀ r, ‖phase r‖ ≤ C)
    (hphaseRelation : ∀ r : ℝ,
      (r : ℂ) * (1 - phase r) = Complex.I * (1 + phase r))
    (hphaseIntegral : E_pvm.integral phase hphaseMeas hphaseBdd =
      cayleyTransform A hA) :
    A ≤ E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable := by
  let coord : ℝ → ℂ := (↑)
  have hcoord : Measurable coord := Complex.continuous_ofReal.measurable
  let B := E_pvm.unboundedIntegral coord hcoord
  let oneF : ℝ → ℂ := fun _ => 1
  have honeMeas : Measurable oneF := measurable_const
  let honeBdd : ∃ C, ∀ r, ‖oneF r‖ ≤ C :=
    ⟨1, fun _ => by rw [norm_one]⟩
  let d : ℝ → ℂ := oneF - phase
  have hdMeas : Measurable d := honeMeas.sub hphaseMeas
  let hdBdd : ∃ C, ∀ r, ‖d r‖ ≤ C :=
    sub_bounded oneF phase honeBdd hphaseBdd
  let c : ℂ := ((2 : ℂ) * Complex.I)⁻¹
  let cF : ℝ → ℂ := fun _ => c
  have hcMeas : Measurable cF := measurable_const
  let hcBdd : ∃ C, ∀ r, ‖cF r‖ ≤ C :=
    ⟨‖c‖, fun _ => le_refl _⟩
  let f : ℝ → ℂ := cF * d
  have hfMeas : Measurable f := hcMeas.mul hdMeas
  let hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C :=
    mul_bounded cF d hcBdd hdBdd
  let negOneF : ℝ → ℂ := fun _ => -1
  have hnegOneMeas : Measurable negOneF := measurable_const
  let hnegOneBdd : ∃ C, ∀ r, ‖negOneF r‖ ≤ C :=
    ⟨1, fun _ => by rw [norm_neg, norm_one]⟩
  let negPhase : ℝ → ℂ := negOneF * phase
  have hnegPhaseMeas : Measurable negPhase := hnegOneMeas.mul hphaseMeas
  let hnegPhaseBdd : ∃ C, ∀ r, ‖negPhase r‖ ≤ C :=
    mul_bounded negOneF phase hnegOneBdd hphaseBdd
  let s : ℝ → ℂ := oneF - negPhase
  have hsMeas : Measurable s := honeMeas.sub hnegPhaseMeas
  let hsBdd : ∃ C, ∀ r, ‖s r‖ ≤ C :=
    sub_bounded oneF negPhase honeBdd hnegPhaseBdd
  let k : ℂ := c * Complex.I
  let kF : ℝ → ℂ := fun _ => k
  have hkMeas : Measurable kF := measurable_const
  let hkBdd : ∃ C, ∀ r, ‖kF r‖ ≤ C :=
    ⟨‖k‖, fun _ => le_refl _⟩
  let p : ℝ → ℂ := kF * s
  have hpMeas : Measurable p := hkMeas.mul hsMeas
  let hpBdd : ∃ C, ∀ r, ‖p r‖ ≤ C :=
    mul_bounded kF s hkBdd hsBdd
  have hprodEq : coord * f = p := by
    funext r
    change (r : ℂ) * (c * (1 - phase r)) =
      (c * Complex.I) * (1 - ((-1 : ℂ) * phase r))
    calc
      (r : ℂ) * (c * (1 - phase r)) =
          c * ((r : ℂ) * (1 - phase r)) := by ring
      _ = c * (Complex.I * (1 + phase r)) := by rw [hphaseRelation r]
      _ = (c * Complex.I) * (1 - ((-1 : ℂ) * phase r)) := by ring
  have hprodBdd : ∃ C, ∀ r, ‖(coord * f) r‖ ≤ C := by
    obtain ⟨C, hC⟩ := hpBdd
    refine ⟨C, fun r => ?_⟩
    rw [congrFun hprodEq r]
    exact hC r
  have honeInt : E_pvm.integral oneF honeMeas honeBdd = 1 := by
    simpa only [oneF] using E_pvm.integral_one
  have hdInt : E_pvm.integral d hdMeas hdBdd =
      1 - cayleyTransform A hA := by
    change E_pvm.integral (oneF - phase) (honeMeas.sub hphaseMeas) hdBdd = _
    rw [E_pvm.integral_sub oneF phase honeMeas hphaseMeas
      honeBdd hphaseBdd hdBdd, honeInt, hphaseIntegral]
  have hcInt : E_pvm.integral cF hcMeas hcBdd = c • 1 := by
    simpa only [cF] using E_pvm.integral_const c
  have hfInt : E_pvm.integral f hfMeas hfBdd =
      c • (1 - cayleyTransform A hA) := by
    change E_pvm.integral (cF * d) (hcMeas.mul hdMeas) hfBdd = _
    rw [E_pvm.integral_mul cF d hcMeas hdMeas hcBdd hdBdd hfBdd,
      hcInt, hdInt, smul_mul_assoc, one_mul]
  have hnegOneInt : E_pvm.integral negOneF hnegOneMeas hnegOneBdd =
      (-1 : ℂ) • 1 := by
    simpa only [negOneF] using E_pvm.integral_const (-1 : ℂ)
  have hnegPhaseInt : E_pvm.integral negPhase hnegPhaseMeas hnegPhaseBdd =
      -cayleyTransform A hA := by
    change E_pvm.integral (negOneF * phase)
      (hnegOneMeas.mul hphaseMeas) hnegPhaseBdd = _
    rw [E_pvm.integral_mul negOneF phase hnegOneMeas hphaseMeas
      hnegOneBdd hphaseBdd hnegPhaseBdd, hnegOneInt, hphaseIntegral,
      smul_mul_assoc, one_mul, neg_one_smul]
  have hsInt : E_pvm.integral s hsMeas hsBdd =
      1 + cayleyTransform A hA := by
    change E_pvm.integral (oneF - negPhase)
      (honeMeas.sub hnegPhaseMeas) hsBdd = _
    rw [E_pvm.integral_sub oneF negPhase honeMeas hnegPhaseMeas
      honeBdd hnegPhaseBdd hsBdd, honeInt, hnegPhaseInt, sub_neg_eq_add]
  have hkInt : E_pvm.integral kF hkMeas hkBdd = k • 1 := by
    simpa only [kF] using E_pvm.integral_const k
  have hpInt : E_pvm.integral p hpMeas hpBdd =
      k • (1 + cayleyTransform A hA) := by
    change E_pvm.integral (kF * s) (hkMeas.mul hsMeas) hpBdd = _
    rw [E_pvm.integral_mul kF s hkMeas hsMeas hkBdd hsBdd hpBdd,
      hkInt, hsInt, smul_mul_assoc, one_mul]
  have hprodInt : E_pvm.integral (coord * f) (hcoord.mul hfMeas) hprodBdd =
      k • (1 + cayleyTransform A hA) := by
    calc
      E_pvm.integral (coord * f) (hcoord.mul hfMeas) hprodBdd =
          E_pvm.integral p hpMeas hpBdd :=
        E_pvm.integral_congr hprodEq _ _ _ _
      _ = k • (1 + cayleyTransform A hA) := hpInt
  have htwoI : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hgraph (x : A.domain) :
      ∃ hxB : (x : E) ∈ B.domain, B ⟨x, hxB⟩ = A x := by
    let y : E := A x + Complex.I • (x : E)
    have hUy : cayleyTransform A hA y = A x - Complex.I • (x : E) := by
      exact cayleyTransform_apply_plus A hA x
    have hdomF : E_pvm.integral f hfMeas hfBdd y ∈ B.domain := by
      exact E_pvm.integral_mem_domain_unboundedIntegral
        f hfMeas hfBdd coord hcoord hprodBdd y
    have hfY : E_pvm.integral f hfMeas hfBdd y = (x : E) := by
      rw [hfInt, smul_apply, sub_apply, one_apply_eq_self, hUy]
      have hdiff : y - (A x - Complex.I • (x : E)) =
          ((2 : ℂ) * Complex.I) • (x : E) := by
        dsimp only [y]
        module
      rw [hdiff, smul_smul]
      change (((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I)) •
        (x : E) = (x : E)
      rw [inv_mul_cancel₀ htwoI, one_smul]
    have hprodY : E_pvm.integral (coord * f)
        (hcoord.mul hfMeas) hprodBdd y = A x := by
      rw [hprodInt, smul_apply, add_apply, one_apply_eq_self, hUy]
      have hsum : y + (A x - Complex.I • (x : E)) =
          (2 : ℂ) • A x := by
        dsimp only [y]
        module
      rw [hsum, smul_smul]
      have hkTwo : c * Complex.I * 2 = 1 := by
        dsimp only [c]
        calc
          ((2 : ℂ) * Complex.I)⁻¹ * Complex.I * 2 =
              ((2 : ℂ) * Complex.I)⁻¹ * ((2 : ℂ) * Complex.I) := by ring
          _ = 1 := inv_mul_cancel₀ htwoI
      rw [show k * 2 = 1 by exact hkTwo, one_smul]
    have haction := E_pvm.unboundedIntegral_integral
      f hfMeas hfBdd coord hcoord hprodBdd y
    let z : B.domain := ⟨E_pvm.integral f hfMeas hfBdd y, hdomF⟩
    have hzAction : B z = A x := by
      change B ⟨E_pvm.integral f hfMeas hfBdd y, hdomF⟩ = A x
      exact haction.trans hprodY
    have hxB : (x : E) ∈ B.domain := by
      rw [← hfY]
      exact hdomF
    refine ⟨hxB, ?_⟩
    let xB : B.domain := ⟨x, hxB⟩
    have hzx : z = xB := Subtype.ext hfY
    change B xB = A x
    rw [← hzx]
    exact hzAction
  change A ≤ B
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Classical.choose (hgraph ⟨x, hx⟩)
  · intro x y hxy
    obtain ⟨hxB, hxAction⟩ := hgraph x
    let xB : B.domain := ⟨x, hxB⟩
    have hyx : y = xB := Subtype.ext hxy.symm
    rw [hyx]
    exact hxAction.symm

/-- A symmetric extension of a self-adjoint partial linear operator equals that operator. -/
theorem eq_of_selfAdjoint_le_formalSelfAdjoint
    (A B : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (hAB : A ≤ B) (hB : B.IsFormalAdjoint B) : B = A := by
  have hformal : A.IsFormalAdjoint B := by
    intro x y
    let xB : B.domain := ⟨x, hAB.1 x.property⟩
    calc
      @inner ℂ E _ (A x) (y : E) = @inner ℂ E _ (B xB) (y : E) := by
        rw [hAB.2 (x := x) (y := xB) rfl]
      _ = @inner ℂ E _ (x : E) (B y) := hB xB y
  have hBA : B ≤ A.adjoint := hformal.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hBA
  exact le_antisymm hBA hAB
