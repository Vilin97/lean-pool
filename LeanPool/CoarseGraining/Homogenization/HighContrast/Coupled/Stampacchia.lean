/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy
import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia.DeGiorgiCore
import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Median

/-!
# The coupled Stampacchia estimate (Proposition 3.3)

The `H1` assembly.  Given the coupled weak form on the centered open
triadic cube `U = openCubeSet (originCube d m)`, there is a constant `c` (the
median of the pair `(v − ½p·x, −v* + ½p·x)`) such that, almost everywhere on `U`,
`|v − ½p·x − c| ≤ C_d · L · M` and `|v* − ½p·x + c| ≤ C_d · L · M`,
with `L = 3^m`, `M = √(Θ|p|² + |q|²)`.

The proof:
* Part C (`coupled_levelEnergy`) supplies the measurable representatives
  `w₁ ≈ v − ½p·x`, `w₂ ≈ −v* + ½p·x` and, for the *negated* problem,
  `w₁' ≈ −(v − ½p·x)`, `w₂' ≈ −(−v* + ½p·x)`, together with the level-energy
  estimate in the De Giorgi core's shape.
* `exists_two_function_median` produces a single median `m`.
* `deGiorgi_one_sided_core` is applied four times — to `(w₁,w₂)`, `(w₂,w₁)`
  (upper tails, median `m`) and `(w₁',w₂')`, `(w₂',w₁')` (lower tails, median
  `−m`) — after transporting the core from `axisCube` to `openCubeSet` through the
  set identity `openCubeSet (originCube d m) = axisCube (fun _ => −½·3^m) (3^m)`.
-/

namespace Homogenization

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- Commuting the two summands inside the level-energy predicate. -/
private theorem le_sqrt_add_comm {S1 S2 V1 V2 E : ℝ}
    (h : S1 + S2 ≤ E * Real.sqrt (V1 + V2)) :
    S2 + S1 ≤ E * Real.sqrt (V2 + V1) := by
  rw [add_comm S2 S1, add_comm V2 V1]; exact h

/-- `vecNormSq` is even. -/
private theorem vecNormSq_neg (r : Vec d) : vecNormSq (-r) = vecNormSq r := by
  simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

/-- The centered open triadic cube is the axis cube with corner `−½·3^m` and side
`3^m`. -/
theorem openCubeSet_originCube_eq_axisCube (m : ℤ) :
    openCubeSet (originCube d m)
      = axisCube (fun _ => (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m) ((3 : ℝ) ^ m) := by
  have harith : (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m + (3 : ℝ) ^ m = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    ring
  ext x
  simp only [mem_openCubeSet_originCube_iff, axisCube, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo, harith]

/-- **Coupled Stampacchia estimate (Prop 3.3).**

Given `hEll` and the coupled weak form + shared trace (the consumed conjuncts of
the representation package), there is a dimensional constant `Cd ≥ 0` and a level `c` with,
almost everywhere on `U = openCubeSet (originCube d m)`,
`|v.toFun x − ½ p·x − c| ≤ Cd · 3^m · √(Θ|p|² + |q|²)` and the mirror bound for
`v*`. -/
theorem coupled_stampacchia (hd : 3 ≤ d) {m : ℤ} {Θ : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) {p q : Vec d}
    {v vstar : H1Function (openCubeSet (originCube d m))}
    (hCWF : CoupledWeakForm a (openCubeSet (originCube d m)) q v vstar)
    (htrace : MemH10 (openCubeSet (originCube d m))
      (fun x => v.toFun x + vstar.toFun x - vecDot p x)) :
    ∃ (Cd c : ℝ), 0 ≤ Cd ∧
      (∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
        |v.toFun x - (1 / 2 : ℝ) * vecDot p x - c|
          ≤ Cd * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)) ∧
      (∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
        |vstar.toFun x - (1 / 2 : ℝ) * vecDot p x + c|
          ≤ Cd * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hUbcd : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    measurableSet_openCubeSet (originCube d m)
  -- ellipticity transferred to the open cube
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a :=
    hEll.mono hUmeas (openCubeSet_subset_cubeSet (originCube d m))
  -- `Θ ≥ 0` via ellipticity at the cube's center `0`
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hΘ : 0 ≤ Θ := by
    have hmem0 : (0 : Vec d) ∈ cubeSet (originCube d m) := by
      rw [mem_cubeSet_originCube_iff]
      intro i; refine ⟨by simp; linarith, by simp; linarith⟩
    exact le_trans zero_le_one (hEll.2 (0 : Vec d) hmem0).2.1
  set M2 : ℝ := Θ * vecNormSq p + vecNormSq q with hM2_def
  have hM2 : 0 ≤ M2 := add_nonneg (mul_nonneg hΘ (vecNormSq_nonneg p)) (vecNormSq_nonneg q)
  set E₀ : ℝ := 2 * Real.sqrt d * Real.sqrt M2 with hE0_def
  have hE₀ : 0 ≤ E₀ := by rw [hE0_def]; positivity
  -- Part C for `(v, v*, p, q)`
  obtain ⟨w₁, w₂, hw1meas, hw2meas, hw1ae, hw2ae, hmatch, hlevel⟩ :=
    coupled_levelEnergy hUbcd hΘ hEllO hCWF htrace
  -- Part C for the negated problem `(−v, −v*, −p, −q)`
  have hCWF' : CoupledWeakForm a (openCubeSet (originCube d m)) (-q) (-v) (-vstar) :=
    coupledWeakForm_neg hCWF
  have htrace' : MemH10 (openCubeSet (originCube d m))
      (fun x => (-v).toFun x + (-vstar).toFun x - vecDot (-p) x) := by
    have hfun : (fun x => (-v).toFun x + (-vstar).toFun x - vecDot (-p) x)
        = (fun x => -(v.toFun x + vstar.toFun x - vecDot p x)) := by
      funext x
      simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hfun]; exact memH10_neg htrace
  obtain ⟨w₁', w₂', hw1'meas, hw2'meas, hw1'ae, hw2'ae, hmatch', hlevel'⟩ :=
    coupled_levelEnergy hUbcd hΘ hEllO hCWF' htrace'
  -- median of `(w₁, w₂)`
  obtain ⟨m₀, hup, hlow⟩ :=
    exists_two_function_median (μ := volumeMeasureOn (openCubeSet (originCube d m)))
      hw1meas.aemeasurable hw2meas.aemeasurable
  -- the core, transported to the open cube
  obtain ⟨Cd, hCd0, hcore⟩ := deGiorgi_one_sided_core (d := d) hd
  have hset := openCubeSet_originCube_eq_axisCube (d := d) m
  have hcore' := hcore (fun _ => (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m) ((3 : ℝ) ^ m) h3pos
  rw [← hset] at hcore'
  -- measure conversions
  have hμconv : ∀ (w : Vec d → ℝ), Measurable w → ∀ t : ℝ,
      (volumeMeasureOn (openCubeSet (originCube d m))) {x | t < w x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ t < w x} := by
    intro w hw t
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply
      (measurableSet_lt measurable_const hw)]
    congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  have hμconv_lt : ∀ (w : Vec d → ℝ), Measurable w → ∀ t : ℝ,
      (volumeMeasureOn (openCubeSet (originCube d m))) {x | w x < t}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w x < t} := by
    intro w hw t
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply
      (measurableSet_lt hw measurable_const)]
    congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  have hunivvol :
      (volumeMeasureOn (openCubeSet (originCube d m))) Set.univ
        = volume (openCubeSet (originCube d m)) := by
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  -- volume of a level set is invariant under a.e.-equal functions
  have hvol_ae : ∀ (f g : Vec d → ℝ), f =ᵐ[volume.restrict (openCubeSet (originCube d m))] g →
      ∀ t : ℝ, volume {x | x ∈ openCubeSet (originCube d m) ∧ t < f x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ t < g x} := by
    intro f g hfg t
    refine measure_congr ?_
    have hfg' : ∀ᵐ x ∂volume, x ∈ openCubeSet (originCube d m) → f x = g x :=
      (MeasureTheory.ae_restrict_iff' hUmeas).1 hfg
    filter_upwards [hfg'] with x hx
    simp only [eq_iff_iff]
    constructor <;> rintro ⟨hxU, hlt⟩ <;> exact ⟨hxU, by rw [hx hxU] at *; assumption⟩
  -- normalise the negated-problem level energy to `p`, `q`
  simp only [vecNormSq_neg] at hlevel'
  -- `w₁' ≈ −w₁`, `w₂' ≈ −w₂`
  have hw1'neg : w₁'.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (fun x => -w₁.toFun x) := by
    filter_upwards [hw1'ae, hw1ae] with x hx' hx
    rw [hx']
    simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]
    rw [hx]; ring
  have hw2'neg : w₂'.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (fun x => -w₂.toFun x) := by
    filter_upwards [hw2'ae, hw2ae] with x hx' hx
    rw [hx']
    simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]
    rw [hx]; ring
  -- the bound `K = Cd · L · E₀`
  set K : ℝ := Cd * (3 : ℝ) ^ m * E₀ with hK_def
  -- median hypotheses in the core's shape
  have hmed12 : volume {x | x ∈ openCubeSet (originCube d m) ∧ m₀ < w₁.toFun x}
        + volume {x | x ∈ openCubeSet (originCube d m) ∧ m₀ < w₂.toFun x}
      ≤ volume (openCubeSet (originCube d m)) := by
    rw [← hμconv w₁.toFun hw1meas m₀, ← hμconv w₂.toFun hw2meas m₀, ← hunivvol]; exact hup
  have hmed12' : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₁'.toFun x}
        + volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₂'.toFun x}
      ≤ volume (openCubeSet (originCube d m)) := by
    have e1 : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₁'.toFun x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w₁.toFun x < m₀} := by
      rw [hvol_ae w₁'.toFun (fun x => -w₁.toFun x) hw1'neg (-m₀)]
      congr 1; ext x; simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    have e2 : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₂'.toFun x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w₂.toFun x < m₀} := by
      rw [hvol_ae w₂'.toFun (fun x => -w₂.toFun x) hw2'neg (-m₀)]
      congr 1; ext x; simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [e1, e2, ← hμconv_lt w₁.toFun hw1meas m₀, ← hμconv_lt w₂.toFun hw2meas m₀, ← hunivvol]
    exact hlow
  -- matched traces for the swapped pairs
  have hmatch21 : MemH10 (openCubeSet (originCube d m)) (fun x => w₂.toFun x - w₁.toFun x) := by
    have h := memH10_neg hmatch
    have hfun : (fun x => -(w₁.toFun x - w₂.toFun x)) = fun x => w₂.toFun x - w₁.toFun x := by
      funext x; ring
    rwa [hfun] at h
  have hmatch21' : MemH10 (openCubeSet (originCube d m)) (fun x => w₂'.toFun x - w₁'.toFun x) := by
    have h := memH10_neg hmatch'
    have hfun : (fun x => -(w₁'.toFun x - w₂'.toFun x)) = fun x => w₂'.toFun x - w₁'.toFun x := by
      funext x; ring
    rwa [hfun] at h
  -- the four core applications
  have hA : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₁.toFun x ≤ m₀ + K :=
    hcore' w₁ w₂ hw1meas hw2meas hmatch m₀ E₀ hE₀ hmed12 (fun k hk => hlevel m₀ k hk)
  have hB : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₂.toFun x ≤ m₀ + K :=
    hcore' w₂ w₁ hw2meas hw1meas hmatch21 m₀ E₀ hE₀
      (by rw [add_comm]; exact hmed12) (fun k hk => le_sqrt_add_comm (hlevel m₀ k hk))
  have hC : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₁'.toFun x ≤ -m₀ + K :=
    hcore' w₁' w₂' hw1'meas hw2'meas hmatch' (-m₀) E₀ hE₀ hmed12'
      (fun k hk => hlevel' (-m₀) k hk)
  have hD : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₂'.toFun x ≤ -m₀ + K :=
    hcore' w₂' w₁' hw2'meas hw1'meas hmatch21' (-m₀) E₀ hE₀
      (by rw [add_comm]; exact hmed12') (fun k hk => le_sqrt_add_comm (hlevel' (-m₀) k hk))
  -- assemble the two-sided bounds
  refine ⟨2 * Real.sqrt d * Cd, m₀, by positivity, ?_, ?_⟩
  · -- bound for `v`
    have hKeq : (2 * Real.sqrt d * Cd) * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)
        = K := by rw [hK_def, hE0_def, hM2_def]; ring
    rw [hKeq]
    filter_upwards [hA, hC, hw1ae, hw1'ae] with x hxA hxC hx1 hx1'
    rw [hx1] at hxA
    have hx1'' : w₁'.toFun x = -v.toFun x + (1 / 2 : ℝ) * vecDot p x := by
      rw [hx1']; simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hx1''] at hxC
    rw [abs_le]; constructor <;> linarith
  · -- bound for `v*`
    have hKeq : (2 * Real.sqrt d * Cd) * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)
        = K := by rw [hK_def, hE0_def, hM2_def]; ring
    rw [hKeq]
    filter_upwards [hB, hD, hw2ae, hw2'ae] with x hxB hxD hx2 hx2'
    rw [hx2] at hxB
    have hx2'' : w₂'.toFun x = vstar.toFun x - (1 / 2 : ℝ) * vecDot p x := by
      rw [hx2']; simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hx2''] at hxD
    rw [abs_le]; constructor <;> linarith

/-- **Uniform coupled Stampacchia estimate (Prop 3.3, constant-outside form).**

Identical to `coupled_stampacchia` but with the dimensional constant `Cd`
quantified *outside* all field data.  The De Giorgi core's constant is already
uniform (`deGiorgi_one_sided_core` has the shape `∃ Cd, ∀ …`), so we obtain it
once at the top and then quantify over the coupled weak-form data; the body is the
same four core applications as `coupled_stampacchia`.  Consumed by the uniform
per-core energy bound. -/
theorem coupled_stampacchia_uniform (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} {Θ : ℝ} {a : CoeffField d}
        (_hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) {p q : Vec d}
        {v vstar : H1Function (openCubeSet (originCube d m))}
        (_hCWF : CoupledWeakForm a (openCubeSet (originCube d m)) q v vstar)
        (_htrace : MemH10 (openCubeSet (originCube d m))
          (fun x => v.toFun x + vstar.toFun x - vecDot p x)),
      ∃ c : ℝ,
        (∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
          |v.toFun x - (1 / 2 : ℝ) * vecDot p x - c|
            ≤ Cd * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)) ∧
        (∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
          |vstar.toFun x - (1 / 2 : ℝ) * vecDot p x + c|
            ≤ Cd * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)) := by
  classical
  -- obtain the uniform De Giorgi core constant ONCE, before quantifying field data
  obtain ⟨Cd, hCd0, hcore⟩ := deGiorgi_one_sided_core (d := d) hd
  refine ⟨2 * Real.sqrt d * Cd, by positivity, ?_⟩
  intro m Θ a hEll p q v vstar hCWF htrace
  have : NeZero d := ⟨by omega⟩
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hUbcd : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    measurableSet_openCubeSet (originCube d m)
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a :=
    hEll.mono hUmeas (openCubeSet_subset_cubeSet (originCube d m))
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hΘ : 0 ≤ Θ := by
    have hmem0 : (0 : Vec d) ∈ cubeSet (originCube d m) := by
      rw [mem_cubeSet_originCube_iff]
      intro i; refine ⟨by simp; linarith, by simp; linarith⟩
    exact le_trans zero_le_one (hEll.2 (0 : Vec d) hmem0).2.1
  set M2 : ℝ := Θ * vecNormSq p + vecNormSq q with hM2_def
  have hM2 : 0 ≤ M2 := add_nonneg (mul_nonneg hΘ (vecNormSq_nonneg p)) (vecNormSq_nonneg q)
  set E₀ : ℝ := 2 * Real.sqrt d * Real.sqrt M2 with hE0_def
  have hE₀ : 0 ≤ E₀ := by rw [hE0_def]; positivity
  obtain ⟨w₁, w₂, hw1meas, hw2meas, hw1ae, hw2ae, hmatch, hlevel⟩ :=
    coupled_levelEnergy hUbcd hΘ hEllO hCWF htrace
  have hCWF' : CoupledWeakForm a (openCubeSet (originCube d m)) (-q) (-v) (-vstar) :=
    coupledWeakForm_neg hCWF
  have htrace' : MemH10 (openCubeSet (originCube d m))
      (fun x => (-v).toFun x + (-vstar).toFun x - vecDot (-p) x) := by
    have hfun : (fun x => (-v).toFun x + (-vstar).toFun x - vecDot (-p) x)
        = (fun x => -(v.toFun x + vstar.toFun x - vecDot p x)) := by
      funext x
      simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hfun]; exact memH10_neg htrace
  obtain ⟨w₁', w₂', hw1'meas, hw2'meas, hw1'ae, hw2'ae, hmatch', hlevel'⟩ :=
    coupled_levelEnergy hUbcd hΘ hEllO hCWF' htrace'
  obtain ⟨m₀, hup, hlow⟩ :=
    exists_two_function_median (μ := volumeMeasureOn (openCubeSet (originCube d m)))
      hw1meas.aemeasurable hw2meas.aemeasurable
  have hset := openCubeSet_originCube_eq_axisCube (d := d) m
  have hcore' := hcore (fun _ => (-(1 / 2 : ℝ)) * (3 : ℝ) ^ m) ((3 : ℝ) ^ m) h3pos
  rw [← hset] at hcore'
  have hμconv : ∀ (w : Vec d → ℝ), Measurable w → ∀ t : ℝ,
      (volumeMeasureOn (openCubeSet (originCube d m))) {x | t < w x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ t < w x} := by
    intro w hw t
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply
      (measurableSet_lt measurable_const hw)]
    congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  have hμconv_lt : ∀ (w : Vec d → ℝ), Measurable w → ∀ t : ℝ,
      (volumeMeasureOn (openCubeSet (originCube d m))) {x | w x < t}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w x < t} := by
    intro w hw t
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply
      (measurableSet_lt hw measurable_const)]
    congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  have hunivvol :
      (volumeMeasureOn (openCubeSet (originCube d m))) Set.univ
        = volume (openCubeSet (originCube d m)) := by
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hvol_ae : ∀ (f g : Vec d → ℝ), f =ᵐ[volume.restrict (openCubeSet (originCube d m))] g →
      ∀ t : ℝ, volume {x | x ∈ openCubeSet (originCube d m) ∧ t < f x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ t < g x} := by
    intro f g hfg t
    refine measure_congr ?_
    have hfg' : ∀ᵐ x ∂volume, x ∈ openCubeSet (originCube d m) → f x = g x :=
      (MeasureTheory.ae_restrict_iff' hUmeas).1 hfg
    filter_upwards [hfg'] with x hx
    simp only [eq_iff_iff]
    constructor <;> rintro ⟨hxU, hlt⟩ <;> exact ⟨hxU, by rw [hx hxU] at *; assumption⟩
  simp only [vecNormSq_neg] at hlevel'
  have hw1'neg : w₁'.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (fun x => -w₁.toFun x) := by
    filter_upwards [hw1'ae, hw1ae] with x hx' hx
    rw [hx']
    simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]
    rw [hx]; ring
  have hw2'neg : w₂'.toFun =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      (fun x => -w₂.toFun x) := by
    filter_upwards [hw2'ae, hw2ae] with x hx' hx
    rw [hx']
    simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]
    rw [hx]; ring
  set K : ℝ := Cd * (3 : ℝ) ^ m * E₀ with hK_def
  have hmed12 : volume {x | x ∈ openCubeSet (originCube d m) ∧ m₀ < w₁.toFun x}
        + volume {x | x ∈ openCubeSet (originCube d m) ∧ m₀ < w₂.toFun x}
      ≤ volume (openCubeSet (originCube d m)) := by
    rw [← hμconv w₁.toFun hw1meas m₀, ← hμconv w₂.toFun hw2meas m₀, ← hunivvol]; exact hup
  have hmed12' : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₁'.toFun x}
        + volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₂'.toFun x}
      ≤ volume (openCubeSet (originCube d m)) := by
    have e1 : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₁'.toFun x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w₁.toFun x < m₀} := by
      rw [hvol_ae w₁'.toFun (fun x => -w₁.toFun x) hw1'neg (-m₀)]
      congr 1; ext x; simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    have e2 : volume {x | x ∈ openCubeSet (originCube d m) ∧ -m₀ < w₂'.toFun x}
        = volume {x | x ∈ openCubeSet (originCube d m) ∧ w₂.toFun x < m₀} := by
      rw [hvol_ae w₂'.toFun (fun x => -w₂.toFun x) hw2'neg (-m₀)]
      congr 1; ext x; simp only [Set.mem_ofPred_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [e1, e2, ← hμconv_lt w₁.toFun hw1meas m₀, ← hμconv_lt w₂.toFun hw2meas m₀, ← hunivvol]
    exact hlow
  have hmatch21 : MemH10 (openCubeSet (originCube d m)) (fun x => w₂.toFun x - w₁.toFun x) := by
    have h := memH10_neg hmatch
    have hfun : (fun x => -(w₁.toFun x - w₂.toFun x)) = fun x => w₂.toFun x - w₁.toFun x := by
      funext x; ring
    rwa [hfun] at h
  have hmatch21' : MemH10 (openCubeSet (originCube d m)) (fun x => w₂'.toFun x - w₁'.toFun x) := by
    have h := memH10_neg hmatch'
    have hfun : (fun x => -(w₁'.toFun x - w₂'.toFun x)) = fun x => w₂'.toFun x - w₁'.toFun x := by
      funext x; ring
    rwa [hfun] at h
  have hA : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₁.toFun x ≤ m₀ + K :=
    hcore' w₁ w₂ hw1meas hw2meas hmatch m₀ E₀ hE₀ hmed12 (fun k hk => hlevel m₀ k hk)
  have hB : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₂.toFun x ≤ m₀ + K :=
    hcore' w₂ w₁ hw2meas hw1meas hmatch21 m₀ E₀ hE₀
      (by rw [add_comm]; exact hmed12) (fun k hk => le_sqrt_add_comm (hlevel m₀ k hk))
  have hC : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₁'.toFun x ≤ -m₀ + K :=
    hcore' w₁' w₂' hw1'meas hw2'meas hmatch' (-m₀) E₀ hE₀ hmed12'
      (fun k hk => hlevel' (-m₀) k hk)
  have hD : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))), w₂'.toFun x ≤ -m₀ + K :=
    hcore' w₂' w₁' hw2'meas hw1'meas hmatch21' (-m₀) E₀ hE₀
      (by rw [add_comm]; exact hmed12') (fun k hk => le_sqrt_add_comm (hlevel' (-m₀) k hk))
  refine ⟨m₀, ?_, ?_⟩
  · have hKeq : (2 * Real.sqrt d * Cd) * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)
        = K := by rw [hK_def, hE0_def, hM2_def]; ring
    rw [hKeq]
    filter_upwards [hA, hC, hw1ae, hw1'ae] with x hxA hxC hx1 hx1'
    rw [hx1] at hxA
    have hx1'' : w₁'.toFun x = -v.toFun x + (1 / 2 : ℝ) * vecDot p x := by
      rw [hx1']; simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hx1''] at hxC
    rw [abs_le]; constructor <;> linarith
  · have hKeq : (2 * Real.sqrt d * Cd) * (3 : ℝ) ^ m * Real.sqrt (Θ * vecNormSq p + vecNormSq q)
        = K := by rw [hK_def, hE0_def, hM2_def]; ring
    rw [hKeq]
    filter_upwards [hB, hD, hw2ae, hw2'ae] with x hxB hxD hx2 hx2'
    rw [hx2] at hxB
    have hx2'' : w₂'.toFun x = vstar.toFun x - (1 / 2 : ℝ) * vecDot p x := by
      rw [hx2']; simp only [Homogenization.H1Function.neg_toFun, vecDot_neg_left]; ring
    rw [hx2''] at hxD
    rw [abs_le]; constructor <;> linarith

end

end Homogenization
