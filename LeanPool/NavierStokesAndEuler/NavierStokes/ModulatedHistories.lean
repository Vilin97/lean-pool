/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricModulation
public import LeanPool.NavierStokesAndEuler.NavierStokes.FiveProfileMoments
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
import LeanPool.NavierStokesAndEuler.NavierStokes.ShapeTransition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual histories and moment repair for radial modulation

The normalized angular field is modulated multiplicatively, so the unchanged
axis germ is retained. All history differences below are actual integrals.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ModulatedHistories

/-- Point: an abbreviation for `ℝ × ℝ`. -/
abbrev Point := ℝ × ℝ
/-- Field: an abbreviation for `Point → ℝ`. -/
abbrev Field := Point → ℝ
/-- Debt: an abbreviation for `FiveProfileMoments.Debt`. -/
abbrev Debt := FiveProfileMoments.Debt
/-- Coefficient: an abbreviation for `FiveProfileMoments.Coeff`. -/
abbrev Coeff := FiveProfileMoments.Coeff

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Window data, collecting `left`, `right`, `left_pos`, `ordered`. -/
structure Window where
  /-- Left of `Window`, of type `ℝ`. -/
  left : ℝ
  /-- Right of `Window`, of type `ℝ`. -/
  right : ℝ
  left_pos : 0 < left
  ordered : left < right

/-- Clamp, given by `projIcc W.left W.right W.ordered.le X`. -/
noncomputable def Window.clamp (W : Window) (X : ℝ) : ℝ :=
  projIcc W.left W.right W.ordered.le X

theorem Window.clamp_mem (W : Window) (X : ℝ) : W.clamp X ∈ Icc W.left W.right :=
  (projIcc W.left W.right W.ordered.le X).2

/-- Density at, given by `![U, 2 * X * f, U * (2 * X * f), U ^ 2 - X * f ^ 2, f ^ 2]`. -/
noncomputable def densityAt (X f U : ℝ) : Debt :=
  ![U, 2 * X * f, U * (2 * X * f), U ^ 2 - X * f ^ 2, f ^ 2]

/-- Density, given by `densityAt p.1 (f p) (U p)`. -/
noncomputable def density (f U : Field) (p : Point) : Debt := densityAt p.1 (f p) (U p)

theorem density_contDiff (f U : Field) (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U)
    (i : Fin 5) : ContDiff ℝ ∞ (fun p => density f U p i) := by
  fin_cases i
  · exact hU
  · exact (contDiff_const.mul contDiff_fst).mul hf
  · exact hU.mul ((contDiff_const.mul contDiff_fst).mul hf)
  · exact (hU.pow 2).sub (contDiff_fst.mul (hf.pow 2))
  · exact hf.pow 2

theorem density_eq_physical (X f U : ℝ) (hX : 0 < X) :
    densityAt X f U =
      ![U, Real.sqrt (2 * X) * (Real.sqrt (2 * X) * f),
        U * Real.sqrt (2 * X) * (Real.sqrt (2 * X) * f),
        U ^ 2 - (Real.sqrt (2 * X) * f) ^ 2 / 2,
        (Real.sqrt (2 * X) * f) ^ 2 / (2 * X)] := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * X by positivity)
  have h1 : Real.sqrt (2 * X) * (Real.sqrt (2 * X) * f) = 2 * X * f := by
    calc
      _ = Real.sqrt (2 * X) ^ 2 * f := by ring
      _ = _ := by rw [hs]
  have h2 : (Real.sqrt (2 * X) * f) ^ 2 = 2 * X * f ^ 2 := by rw [mul_pow, hs]
  ext i
  fin_cases i
  · rfl
  · exact h1.symm
  · change U * (2 * X * f) = U * Real.sqrt (2 * X) * (Real.sqrt (2 * X) * f)
    simpa only [mul_assoc] using congrArg (fun z => U * z) h1.symm
  · change U ^ 2 - X * f ^ 2 = U ^ 2 - (Real.sqrt (2 * X) * f) ^ 2 / 2
    rw [h2]
    ring
  · change f ^ 2 = (Real.sqrt (2 * X) * f) ^ 2 / (2 * X)
    rw [h2]
    field_simp

variable {a m p₁ p₂ : Point → ℝ} {K B : Set Point}

/-- Raw F, given by `ParametricModulation.realizedE r f N p.1 p.2`. -/
noncomputable def rawF (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f : Field) (N : ℝ) (p : Point) : ℝ :=
  ParametricModulation.realizedE r f N p.1 p.2

/-- Raw U, given by `ParametricModulation.realizedU r E U N p.1 p.2`. -/
noncomputable def rawU (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (E U : Field) (N : ℝ) (p : Point) : ℝ :=
  ParametricModulation.realizedU r E U N p.1 p.2

theorem rawF_physical (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f E : Field) (N X eta : ℝ) (hE : E (X, eta) = Real.sqrt (2 * X) * f (X, eta)) :
    Real.sqrt (2 * X) * rawF r f N (X, eta) = ParametricModulation.realizedE r E N X eta := by
  dsimp [rawF, ParametricModulation.realizedE, RadialModulation.modulatedE]
  rw [hE]
  ring

/-- Density family, constructed using `densityAt`. -/
noncomputable def densityFamily
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (z : RadialModulation.FamilyPoint) : Debt :=
  densityAt z.2.1
    (RadialModulation.angularFamily (fun X eta => f (X, eta))
      (ParametricModulation.asRadialPrimitive r.angularPrimitive) z)
    (RadialModulation.axialFamily (fun X eta => U (X, eta))
      (ParametricModulation.asRadialPrimitive (r.axialPrimitive E)) z)

theorem densityFamily_contDiff
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (i : Fin 5) :
    ContDiff ℝ ∞ (fun z => densityFamily r f E U z i) := by
  obtain ⟨hA, hB⟩ := r.primitives_smooth E ha hm hp₂ hE
  have hAp := ParametricModulation.asRadialPrimitive_contDiff _ hA
  have hBp := ParametricModulation.asRadialPrimitive_contDiff _ hB
  have hbase : ContDiff ℝ ∞ (fun z : RadialModulation.FamilyPoint => (z.2.1, z.2.2.1)) :=
    contDiff_snd.fst.prodMk contDiff_snd.snd.fst
  have hfamF : ContDiff ℝ ∞ (RadialModulation.angularFamily (fun X eta => f (X, eta))
      (ParametricModulation.asRadialPrimitive r.angularPrimitive)) :=
    (hf.comp hbase).mul ((contDiff_fst.mul (hAp.comp contDiff_snd)).exp)
  have hfamU : ContDiff ℝ ∞ (RadialModulation.axialFamily (fun X eta => U (X, eta))
      (ParametricModulation.asRadialPrimitive (r.axialPrimitive E))) :=
    (hU.comp hbase).add (contDiff_fst.mul (hBp.comp contDiff_snd))
  fin_cases i
  · exact hfamU
  · exact (contDiff_const.mul contDiff_snd.fst).mul hfamF
  · exact hfamU.mul ((contDiff_const.mul contDiff_snd.fst).mul hfamF)
  · exact (hfamU.pow 2).sub (contDiff_snd.fst.mul (hfamF.pow 2))
  · exact hfamF.pow 2

theorem densityFamily_periodic
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (eps X eta : ℝ) (i : Fin 5) :
    Function.Periodic (fun theta => densityFamily r f E U (eps, X, eta, theta) i) 1 := by
  intro theta
  have h := r.primitives_periodic E ha hm hp₂ (X, eta)
  simp only [densityFamily, RadialModulation.angularFamily, RadialModulation.axialFamily,
    ParametricModulation.asRadialPrimitive, h.1 theta, h.2 theta]

theorem densityFamily_zero
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (X eta theta : ℝ) : densityFamily r f E U (0, X, eta, theta) = density f U (X, eta) := by
  simp [densityFamily, RadialModulation.angularFamily, RadialModulation.axialFamily, density]

theorem densityFamily_frequency
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (N X eta : ℝ) :
    densityFamily r f E U (1 / N, X, eta, N * Real.log X) =
      density (rawF r f N) (rawU r E U N) (X, eta) := by
  simp only [densityFamily, density, rawF, rawU, ParametricModulation.realizedE,
    ParametricModulation.realizedU, RadialModulation.angularFamily, RadialModulation.axialFamily,
    RadialModulation.modulatedE, RadialModulation.modulatedU, RadialModulation.phasePoint,
    div_eq_mul_inv, one_mul, mul_comm (N⁻¹)]

theorem density_uniform_eta_jets
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (KX S : Set ℝ) (hKX : IsCompact KX) (hS : IsCompact S) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ X ∈ KX, ∀ eta ∈ S, ∀ j ≤ q, ∀ i : Fin 5,
      |iteratedDeriv j (fun e => density (rawF r f N) (rawU r E U N) (X, e) i) eta -
        iteratedDeriv j (fun e => density f U (X, e) i) eta| ≤ C / N := by
  have hone (j : Fin (q + 1)) (i : Fin 5) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
      ∀ X ∈ KX, ∀ eta ∈ S,
      |iteratedDeriv j (fun e => density (rawF r f N) (rawU r E U N) (X, e) i) eta -
        iteratedDeriv j (fun e => density f U (X, e) i) eta| ≤ C / N := by
    obtain ⟨C, hC, hb⟩ := RadialModulation.uniform_periodic_family_eta_jets
      (fun z => densityFamily r f E U z i) (densityFamily_contDiff r f E U ha hm hp₂ hf hE hU i)
      (fun eps X eta => densityFamily_periodic r f E U ha hm hp₂ eps X eta i) KX S hKX hS j
    refine ⟨C, hC, ?_⟩
    intro N hN X hX eta heta
    have h := hb N hN X hX eta heta (N * Real.log X)
    simpa only [densityFamily_frequency, densityFamily_zero] using h
  choose c hc hbound using hone
  let C : ℝ := 1 + ∑ j : Fin (q + 1), ∑ i : Fin 5, c j i
  have hsum : 0 ≤ ∑ j : Fin (q + 1), ∑ i : Fin 5, c j i :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hc j i))
  have hle (j : Fin (q + 1)) (i : Fin 5) : c j i ≤ C := by
    have hi := Finset.single_le_sum (fun i _ => hc j i) (Finset.mem_univ i)
    have hj := Finset.single_le_sum
      (f := fun j : Fin (q + 1) => ∑ i : Fin 5, c j i)
      (fun j _ => Finset.sum_nonneg (fun i _ => hc j i)) (Finset.mem_univ j)
    dsimp [C]
    linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro N hN X hX eta heta j hj i
  exact (hbound ⟨j, Nat.lt_succ_of_le hj⟩ i N hN X hX eta heta).trans
    (div_le_div_of_nonneg_right (hle _ i) (le_trans zero_le_one hN))

/-- Density difference, given by `density (rawF r f N) (rawU r E U N) p - density f U p`. -/
noncomputable def densityDifference
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f E U : Field) (N : ℝ) (p : Point) : Debt :=
  density (rawF r f N) (rawU r E U N) p - density f U p

theorem densityDifference_contDiffAt
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (N X eta : ℝ) (hX : X ≠ 0) (i : Fin 5) :
    ContDiffAt ℝ ∞ (fun p => densityDifference r f E U N p i) (X, eta) := by
  have hgraph : ContDiffAt ℝ ∞
      (fun p : Point => ((1 / N : ℝ), p.1, p.2, N * Real.log p.1)) (X, eta) :=
    contDiffAt_const.prodMk (contDiffAt_fst.prodMk
      (contDiffAt_snd.prodMk (contDiffAt_const.mul (contDiffAt_fst.log hX))))
  have hcomp := (densityFamily_contDiff r f E U ha hm hp₂ hf hE hU i).contDiffAt.comp (X, eta)
      hgraph
  have hd : ContDiffAt ℝ ∞ (fun p : Point => density (rawF r f N) (rawU r E U N) p i) (X, eta) := by
    simpa only [Function.comp_def, densityFamily_frequency, Prod.eta] using hcomp
  exact hd.sub (density_contDiff f U hf hU i).contDiffAt

/-- History difference, defined pointwise by `∫ s in W.left..W.clamp X, densityDifference r f E
U N (s, eta) i`. -/
noncomputable def historyDifference (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f E U : Field) (N X eta : ℝ) : Debt :=
  fun i => ∫ s in W.left..W.clamp X, densityDifference r f E U N (s, eta) i

theorem historyDifference_smooth (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (N X : ℝ) :
    ContDiff ℝ ∞ (historyDifference W r f E U N X) := by
  apply contDiff_pi.mpr
  intro i
  exact (ShapeTransition.smooth_parameter_interval (W.clamp_mem X).1
    (fun s hs eta => densityDifference_contDiffAt r f E U ha hm hp₂ hf hE hU N s eta
      (ne_of_gt (W.left_pos.trans_le hs.1)) i)).1

theorem density_raw_slice_smooth
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (N X : ℝ) (i : Fin 5) :
    ContDiff ℝ ∞ (fun eta => density (rawF r f N) (rawU r E U N) (X, eta) i) := by
  have hg : ContDiff ℝ ∞ (fun eta : ℝ => ((1 / N : ℝ), X, eta, N * Real.log X)) :=
    contDiff_const.prodMk (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have h' : ContDiff ℝ ∞ (fun eta => densityFamily r f E U (1 / N, X, eta, N * Real.log X) i) :=
    (densityFamily_contDiff r f E U ha hm hp₂ hf hE hU i).comp hg
  simpa only [densityFamily_frequency] using h'

theorem historyDifference_scalar_jets (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ X : ℝ, ∀ eta ∈ S, ∀ j ≤ q, ∀ i : Fin 5,
      |iteratedDeriv j (fun e => historyDifference W r f E U N X e i) eta| ≤ C / N := by
  obtain ⟨C, hC, hbound⟩ := density_uniform_eta_jets r f E U ha hm hp₂ hf hE hU
    (Icc W.left W.right) S isCompact_Icc hS q
  refine ⟨C * (W.right - W.left), mul_pos hC (sub_pos.mpr W.ordered), ?_⟩
  intro N hN X eta heta j hj i
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hh := ShapeTransition.integral_jet_bound_on (W.clamp_mem X).1
    (F := fun p => densityDifference r f E U N p i)
    (fun s hs e => densityDifference_contDiffAt r f E U ha hm hp₂ hf hE hU N s e
      (ne_of_gt (W.left_pos.trans_le hs.1)) i) j eta (B := C / N) ?_
  · apply hh.trans
    calc
      _ ≤ (C / N) * (W.right - W.left) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (W.clamp_mem X).2 _)
          (div_nonneg hC.le hNpos.le)
      _ = _ := by ring
  · intro s hs
    have hraw := density_raw_slice_smooth r f E U ha hm hp₂ hf hE hU N s i
    have hnom : ContDiff ℝ ∞ (fun e => density f U (s, e) i) :=
      (density_contDiff f U hf hU i).comp (contDiff_const.prodMk contDiff_id)
    change |iteratedDeriv j ((fun e => density (rawF r f N) (rawU r E U N) (s, e) i) -
      (fun e => density f U (s, e) i)) eta| ≤ C / N
    rw [iteratedDeriv_sub (hraw.of_le (nat_le_infty j)).contDiffAt
      (hnom.of_le (nat_le_infty j)).contDiffAt]
    exact hbound N hN s ⟨hs.1.le, hs.2.trans (W.clamp_mem X).2⟩ eta heta j hj i

theorem clm_iteratedDeriv {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G)
    {v : ℝ → F} (hv : ContDiff ℝ ∞ v) (j : ℕ) (eta : ℝ) :
    iteratedDeriv j (fun e => L (v e)) eta = L (iteratedDeriv j v eta) := by
  have h := L.iteratedFDeriv_comp_left (x := eta) hv.contDiffAt (nat_le_infty j)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  exact congrArg (fun T => T (fun _ : Fin j => (1 : ℝ))) h

theorem historyDifference_jets (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ X : ℝ,
      JetBounds.FiniteJetBound q (historyDifference W r f E U N X) S (C / N) := by
  obtain ⟨C, hC, hb⟩ := historyDifference_scalar_jets W r f E U ha hm hp₂ hf hE hU S hS q
  refine ⟨C, hC, ?_⟩
  intro N hN X j hj eta heta
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC.le (le_trans zero_le_one hN))).mpr
  intro i
  have he := clm_iteratedDeriv (ContinuousLinearMap.proj i)
    (historyDifference_smooth W r f E U ha hm hp₂ hf hE hU N X) j eta
  simp only [ContinuousLinearMap.proj_apply] at he
  rw [← he]
  exact hb N hN X eta heta j hj i

/-! ## Localization and genuine axis histories -/

/-- Splice, with branches according to `p.1 ∈ Ioc W.left W.right`. -/
noncomputable def splice (W : Window) (base actual : Field) (p : Point) : ℝ :=
  if p.1 ∈ Ioc W.left W.right then actual p else base p

theorem splice_eq_before (W : Window) (base actual : Field) {p : Point}
    (hp : p.1 ≤ W.left) : splice W base actual p = base p := by
  simp [splice, show p.1 ∉ Ioc W.left W.right from fun h => (not_lt_of_ge hp) h.1]

theorem splice_eq_after (W : Window) (base actual : Field) {p : Point}
    (hp : W.right < p.1) : splice W base actual p = base p := by
  simp [splice, show p.1 ∉ Ioc W.left W.right from fun h => (not_le_of_gt hp) h.2]

theorem splice_eq_of_eq (W : Window) {base actual : Field} {p : Point}
    (hp : actual p = base p) : splice W base actual p = base p := by
  unfold splice
  split_ifs <;> simp_all

theorem splice_contDiffOn (W : Window) {base actual : Field} {Ω : Set ℝ}
    (hbase : ContDiff ℝ ∞ base)
    (hactual : ∀ p : Point, p.1 ∈ Icc W.left W.right → ContDiffAt ℝ ∞ actual p)
    (hcollar : ∀ eta ∈ Ω, (actual =ᶠ[𝓝 (W.left, eta)] base) ∧
      (actual =ᶠ[𝓝 (W.right, eta)] base)) :
    ContDiffOn ℝ ∞ (splice W base actual) (univ ×ˢ Ω) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hl : p.1 = W.left
  · apply hbase.contDiffAt.congr_of_eventuallyEq
    have hc := (hcollar p.2 hp.2).1
    rw [← hl] at hc
    filter_upwards [hc] with q hq
    exact splice_eq_of_eq W hq
  by_cases hr : p.1 = W.right
  · apply hbase.contDiffAt.congr_of_eventuallyEq
    have hc := (hcollar p.2 hp.2).2
    rw [← hr] at hc
    filter_upwards [hc] with q hq
    exact splice_eq_of_eq W hq
  by_cases hin : p.1 ∈ Ioo W.left W.right
  · apply (hactual p ⟨hin.1.le, hin.2.le⟩).congr_of_eventuallyEq
    have hn : {q : Point | q.1 ∈ Ioo W.left W.right} ∈ 𝓝 p :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds hin
    filter_upwards [hn] with q hq
    exact ite_eq_left ⟨hq.1, hq.2.le⟩
  · have hout : p.1 < W.left ∨ W.right < p.1 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hin
      rcases hin with h | h
      · exact Or.inl (lt_of_le_of_ne h hl)
      · exact Or.inr (lt_of_le_of_ne h (Ne.symm hr))
    apply hbase.contDiffAt.congr_of_eventuallyEq
    rcases hout with h | h
    · have hn : {q : Point | q.1 < W.left} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds h
      filter_upwards [hn] with q hq
      exact splice_eq_before W base actual hq.le
    · have hn : {q : Point | W.right < q.1} ∈ 𝓝 p :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds h
      filter_upwards [hn] with q hq
      exact splice_eq_after W base actual hq

/-- Localized F, given by `splice W f (rawF r f N)`. -/
noncomputable def localizedF (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f : Field) (N : ℝ) : Field := splice W f (rawF r f N)

/-- Localized U, given by `splice W U (rawU r E U N)`. -/
noncomputable def localizedU (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (E U : Field) (N : ℝ) : Field := splice W U (rawU r E U N)

theorem localized_density_difference (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f E U : Field) (N X eta : ℝ) (i : Fin 5) :
    density (localizedF W r f N) (localizedU W r E U N) (X, eta) i -
      density f U (X, eta) i =
      (Ioc W.left W.right).indicator (fun s => densityDifference r f E U N (s, eta) i) X := by
  by_cases hX : X ∈ Ioc W.left W.right
  · simp only [localizedF, localizedU, density, splice, hX, ite_eq_left, indicator_of_mem,
      densityDifference, Pi.sub_apply]
  · simp only [localizedF, localizedU, density, splice, hX, ite_false,
      sub_self]
    exact (indicator_of_notMem hX _).symm

theorem integral_indicator_window (W : Window) (F : ℝ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    (∫ s in (0 : ℝ)..X, (Ioc W.left W.right).indicator F s) =
      ∫ s in W.left..W.clamp X, F s := by
  have hset : Ioc W.left W.right ∩ Ioc 0 X = Ioc W.left (W.clamp X) := by
    by_cases hXa : X ≤ W.left
    · have hc : W.clamp X = W.left := by
        exact congrArg Subtype.val (projIcc_of_le_left W.ordered.le hXa)
      rw [hc, Ioc_self]
      apply eq_empty_iff_forall_notMem.mpr
      rintro s ⟨hs, hs'⟩
      exact (not_lt_of_ge (hs'.2.trans hXa)) hs.1
    · have haX : W.left ≤ X := (lt_of_not_ge hXa).le
      have hc : W.clamp X = min W.right X := by
        exact max_eq_right (le_min W.ordered.le haX)
      rw [hc]
      ext s
      simp only [mem_inter_iff, mem_Ioc, le_min_iff]
      constructor
      · rintro ⟨⟨ha, hb⟩, ⟨_, hX⟩⟩
        exact ⟨ha, hb, hX⟩
      · rintro ⟨ha, hb, hX⟩
        exact ⟨⟨ha, hb⟩, ⟨W.left_pos.trans ha, hX⟩⟩
  rw [intervalIntegral.integral_of_le hX, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, hset,
    ← intervalIntegral.integral_of_le (W.clamp_mem X).1]

theorem densityDifference_continuousOn (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (N eta : ℝ) (i : Fin 5) :
    ContinuousOn (fun s => densityDifference r f E U N (s, eta) i) (Icc W.left W.right) := by
  intro s hs
  have hg : ContDiffAt ℝ ∞ (fun x : ℝ => (x, eta)) s :=
    contDiffAt_id.prodMk contDiffAt_const
  have ho : ContDiffAt ℝ ∞ (fun p : Point => densityDifference r f E U N p i) (s, eta) :=
    densityDifference_contDiffAt r f E U ha hm hp₂ hf hE hU N s eta
      (ne_of_gt (W.left_pos.trans_le hs.1)) i
  have hc := ContDiffAt.comp (f := fun x : ℝ => (x, eta))
    (g := fun p : Point => densityDifference r f E U N p i) s ho hg
  exact hc.continuousAt.continuousWithinAt

/-- Axis history, defined pointwise by `∫ s in (0 : ℝ)..p.1, density f U (s, p.2) i`. -/
noncomputable def axisHistory (f U : Field) (p : Point) : Debt :=
  fun i => ∫ s in (0 : ℝ)..p.1, density f U (s, p.2) i

theorem axisHistory_localized_sub (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (N X eta : ℝ) (hX : 0 ≤ X) :
    axisHistory (localizedF W r f N) (localizedU W r E U N) (X, eta) -
      axisHistory f U (X, eta) = historyDifference W r f E U N X eta := by
  ext i
  have hd : IntegrableOn (fun s => densityDifference r f E U N (s, eta) i)
      (Icc W.left W.right) volume :=
    (densityDifference_continuousOn W r f E U ha hm hp₂ hf hE hU N eta i).integrableOn_Icc
  have hi := (hd.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hnom : IntervalIntegrable (fun s => density f U (s, eta) i) volume 0 X :=
    ((density_contDiff f U hf hU i).continuous.comp (continuous_id.prodMk
        continuous_const)).intervalIntegrable 0 X
  have hnew : IntervalIntegrable
      (fun s => density (localizedF W r f N) (localizedU W r E U N) (s, eta) i) volume 0 X := by
    have hsum := hnom.add hi.intervalIntegrable
    apply hsum.congr_ae
    filter_upwards with s
    linarith [localized_density_difference W r f E U N s eta i]
  change (∫ s in (0 : ℝ)..X, density (localizedF W r f N) (localizedU W r E U N) (s, eta) i) -
    (∫ s in (0 : ℝ)..X, density f U (s, eta) i) = _
  rw [← intervalIntegral.integral_sub hnew hnom]
  simp_rw [localized_density_difference]
  exact integral_indicator_window W _ hX

theorem actual_axisHistory_jets (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ X : ℝ, 0 ≤ X →
      JetBounds.FiniteJetBound q (fun eta =>
        axisHistory (localizedF W r f N) (localizedU W r E U N) (X, eta) -
          axisHistory f U (X, eta)) S (C / N) := by
  obtain ⟨C, hC, hb⟩ := historyDifference_jets W r f E U ha hm hp₂ hf hE hU S hS q
  refine ⟨C, hC, ?_⟩
  intro N hN X hX
  have he : (fun eta => axisHistory (localizedF W r f N) (localizedU W r E U N) (X, eta) -
      axisHistory f U (X, eta)) = historyDifference W r f E U N X := by
    funext eta
    exact axisHistory_localized_sub W r f E U ha hm hp₂ hf hE hU N X eta hX
  rw [he]
  exact hb N hN X

/-! ## A linear finite-jet bound for the actual nonlinear inverse -/

theorem iteratedFDeriv_comp_clm_on {F G H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : G → H} {V : Set G} (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (L : F →L[ℝ] G) {x : F} (hx : L x ∈ V) (j : ℕ) :
    iteratedFDeriv ℝ j (g ∘ L) x =
      (iteratedFDeriv ℝ j g (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre := hV.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hg hV.uniqueDiffOn hpre.uniqueDiffOn hx
    (nat_le_infty j)
  rw [iteratedFDerivWithin_of_isOpen j hpre hx,
    iteratedFDerivWithin_of_isOpen j hV hx] at he
  exact he

/-- All finite jets retain the linear smallness of the input. The proof
rescales the input and the inverse branch in opposite directions before
applying the genuine higher chain-rule estimate. -/
theorem smooth_solver_linear_jets {g : Coeff → Coeff} {r C : ℝ}
    (hr : 0 < r) (hC : 0 < C) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r))
    (hvalue : ∀ z ∈ Metric.ball (0 : Coeff) r, ‖g z‖ ≤ C * ‖z‖) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → Coeff), ContDiff ℝ ∞ f →
      ∀ (delta eta : ℝ), 0 < delta → delta ≤ min 1 (r / 2) →
        (∀ j ≤ q, ‖iteratedFDeriv ℝ j f eta‖ ≤ delta) →
        ∀ j ≤ q, ‖iteratedFDeriv ℝ j (g ∘ f) eta‖ ≤ K * delta := by
  obtain ⟨D, hD, hgb⟩ := FiveProfileMoments.smooth_solver_jet_bound hr hg q
  refine ⟨(q.factorial : ℝ) * (C + D), by positivity, ?_⟩
  intro f hf delta eta hd hdmax hfj j hj
  have hd1 : delta ≤ 1 := hdmax.trans (min_le_left _ _)
  have hdr : delta ≤ r / 2 := hdmax.trans (min_le_right _ _)
  have hfx : ‖f eta‖ ≤ delta := by
    simpa only [norm_iteratedFDeriv_zero] using hfj 0 (Nat.zero_le q)
  have hxclosed : f eta ∈ Metric.closedBall (0 : Coeff) (r / 2) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hfx.trans hdr
  have hxball : f eta ∈ Metric.ball (0 : Coeff) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hfx.trans_lt (by linarith : delta < r)
  let L : Coeff →L[ℝ] Coeff := delta • ContinuousLinearMap.id ℝ Coeff
  let v : ℝ → Coeff := fun x => delta⁻¹ • f x
  let G : Coeff → Coeff := g ∘ L
  let V : Set Coeff := L ⁻¹' Metric.ball 0 r
  let T : Set ℝ := v ⁻¹' V
  have hLv (x : ℝ) : L (v x) = f x := by
    simp [L, v, smul_smul, hd.ne']
  have hLnorm : ‖L‖ ≤ delta := by
    dsimp [L]
    rw [norm_smul delta (ContinuousLinearMap.id ℝ Coeff), Real.norm_of_nonneg hd.le]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Coeff)) hd.le
  have hv : ContDiff ℝ ∞ v := hf.const_smul _
  have hV : IsOpen V := Metric.isOpen_ball.preimage L.continuous
  have hT : IsOpen T := hV.preimage hv.continuous
  have hG : ContDiffOn ℝ ∞ G V := hg.comp_continuousLinearMap L
  have heta : eta ∈ T := by
    change L (v eta) ∈ Metric.ball 0 r
    rwa [hLv]
  have hinner (k : ℕ) (hk : k ≤ q) : ‖iteratedFDeriv ℝ k v eta‖ ≤ 1 := by
    dsimp [v]
    rw [iteratedFDeriv_const_smul_apply' (hf.of_le (nat_le_infty k)).contDiffAt,
      norm_smul (delta⁻¹) (iteratedFDeriv ℝ k f eta), Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ delta⁻¹ * delta := mul_le_mul_of_nonneg_left (hfj k hk) (inv_nonneg.mpr hd.le)
      _ = 1 := inv_mul_cancel₀ hd.ne'
  have houter (k : ℕ) (hk : k ≤ q) :
      ‖iteratedFDeriv ℝ k G (v eta)‖ ≤ (C + D) * delta := by
    by_cases hk0 : k = 0
    · subst k
      rw [norm_iteratedFDeriv_zero]
      change ‖g (L (v eta))‖ ≤ _
      rw [hLv]
      exact ((hvalue _ hxball).trans (mul_le_mul_of_nonneg_left hfx hC.le)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hd.le)
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hp : delta ^ k ≤ delta := by
        simpa only [pow_one] using pow_le_pow_of_le_one hd.le hd1 hk1
      have he := iteratedFDeriv_comp_clm_on Metric.isOpen_ball hg L
        (x := v eta) (by rwa [hLv]) k
      change ‖iteratedFDeriv ℝ k (g ∘ L) (v eta)‖ ≤ _
      rw [he]
      calc
        _ ≤ ‖iteratedFDeriv ℝ k g (L (v eta))‖ * ∏ _ : Fin k, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ k g (f eta)‖ * ‖L‖ ^ k := by
            simp only [hLv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ D * delta ^ k := mul_le_mul (hgb k hk _ hxclosed)
          (pow_le_pow_left₀ (norm_nonneg _) hLnorm k) (pow_nonneg (norm_nonneg _) k) hD.le
        _ ≤ D * delta := mul_le_mul_of_nonneg_left hp hD.le
        _ ≤ (C + D) * delta := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) hd.le
  have hchain := norm_iteratedFDerivWithin_comp_le hG hv.contDiffOn (nat_le_infty j)
    hV.uniqueDiffOn hT.uniqueDiffOn (show MapsTo v T V from fun _ hx => hx) heta
    (C := (C + D) * delta) (D := 1)
    (fun k hk => ?_) (fun k _ hk => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j hT heta] at hchain
    have heq : G ∘ v = g ∘ f := funext (fun x => congrArg g (hLv x))
    rw [heq, one_pow, mul_one] at hchain
    refine hchain.trans ?_
    calc
      _ = (j.factorial : ℝ) * (C + D) * delta := by ring
      _ ≤ (q.factorial : ℝ) * (C + D) * delta :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.factorial_le hj) (add_nonneg hC.le hD.le)) hd.le
  · rw [iteratedFDerivWithin_of_isOpen k hV heta]
    exact houter k (hk.trans hj)
  · rw [iteratedFDerivWithin_of_isOpen k hT heta, one_pow]
    exact hinner k (hk.trans hj)

/-! ## Smooth localized profiles and the canonical pressure -/

theorem exists_smooth_localization (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hBK : B ⊆ K)
    (hends : ∀ eta ∈ S, (W.left, eta) ∈ B ∧ (W.right, eta) ∈ B) :
    ∃ (Ω : Set ℝ) (V : Set Point), IsOpen Ω ∧ S ⊆ Ω ∧ IsOpen V ∧ B ⊆ V ∧
      (∀ N : ℝ, ContDiffOn ℝ ∞ (localizedF W r f N) (univ ×ˢ Ω) ∧
        ContDiffOn ℝ ∞ (localizedU W r E U N) (univ ×ˢ Ω)) ∧
      (∀ N : ℝ, ∀ p ∈ V, localizedF W r f N p = f p ∧ localizedU W r E U N p = U p) := by
  obtain ⟨V, hV, hBV, hz⟩ := r.boundary_vanishing E ha hm hBK
  let Ω : Set ℝ := (fun eta => (W.left, eta)) ⁻¹' V ∩ (fun eta => (W.right, eta)) ⁻¹' V
  have hΩ : IsOpen Ω :=
    (hV.preimage (continuous_const.prodMk continuous_id)).inter
      (hV.preimage (continuous_const.prodMk continuous_id))
  have hSΩ : S ⊆ Ω := fun eta heta => ⟨hBV (hends eta heta).1, hBV (hends eta heta).2⟩
  have heq (N : ℝ) (p : Point) (hp : p ∈ V) : rawF r f N p = f p ∧ rawU r E U N p = U p := by
    have h := hz p hp (N * Real.log p.1)
    simp only [rawF, rawU, ParametricModulation.realizedE, ParametricModulation.realizedU,
      RadialModulation.modulatedE, RadialModulation.modulatedU, RadialModulation.phasePoint,
      ParametricModulation.asRadialPrimitive, Prod.eta, h.1, h.2, zero_div, Real.exp_zero,
      mul_one, add_zero, and_self]
  refine ⟨Ω, V, hΩ, hSΩ, hV, hBV, ?_, ?_⟩
  · intro N
    have hcollar (eta : ℝ) (heta : eta ∈ Ω) :
        ((rawF r f N =ᶠ[𝓝 (W.left, eta)] f) ∧ (rawF r f N =ᶠ[𝓝 (W.right, eta)] f)) ∧
        ((rawU r E U N =ᶠ[𝓝 (W.left, eta)] U) ∧ (rawU r E U N =ᶠ[𝓝 (W.right, eta)] U)) := by
      have hl : ∀ᶠ p in 𝓝 (W.left, eta), rawF r f N p = f p ∧ rawU r E U N p = U p := by
        filter_upwards [hV.mem_nhds heta.1] with p hp
        exact heq N p hp
      have hr : ∀ᶠ p in 𝓝 (W.right, eta), rawF r f N p = f p ∧ rawU r E U N p = U p := by
        filter_upwards [hV.mem_nhds heta.2] with p hp
        exact heq N p hp
      exact ⟨⟨hl.mono (fun _ h => h.1), hr.mono (fun _ h => h.1)⟩,
        ⟨hl.mono (fun _ h => h.2), hr.mono (fun _ h => h.2)⟩⟩
    constructor
    · apply splice_contDiffOn W hf _ (fun eta heta => (hcollar eta heta).1)
      rintro ⟨X, eta⟩ hX
      exact (ParametricModulation.realized_profiles_contDiffAt r f U ha hm hp₂ hf hU
        N X eta (ne_of_gt (W.left_pos.trans_le hX.1))).1
    · apply splice_contDiffOn W hU _ (fun eta heta => (hcollar eta heta).2)
      rintro ⟨X, eta⟩ hX
      exact (ParametricModulation.realized_profiles_contDiffAt r E U ha hm hp₂ hE hU
        N X eta (ne_of_gt (W.left_pos.trans_le hX.1))).2
  · intro N p hp
    exact ⟨splice_eq_of_eq W (heq N p hp).1, splice_eq_of_eq W (heq N p hp).2⟩

/-- Strip domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
noncomputable def stripDomain (Ω : Set ℝ) (hΩ : IsOpen Ω) : ProfileHistories.RadialDomain where
  carrier := univ ×ˢ Ω
  isOpen := isOpen_univ.prod hΩ
  scale_mem := fun _ hp _ _ => ⟨mem_univ _, hp.2⟩

/-- Profiles, bundling `f`, `U`, `f_smooth`, `U_smooth` and the required compatibility proofs. -/
noncomputable def profiles (Ω : Set ℝ) (hΩ : IsOpen Ω) (f U : Field) (P0 : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ Ω)) (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ω))
    (hP0 : ContDiffOn ℝ ∞ P0 Ω) : ProfileHistories.Profiles (stripDomain Ω hΩ) where
  f := f
  U := U
  f_smooth := hf
  U_smooth := hU
  pressure0 := P0
  pressure0_smooth := fun _ hp => hP0.contDiffAt (hΩ.mem_nhds hp.2)

/-- Profile rows, given by `![P.M p, P.I p, P.J p, P.S p, P.pressure p]`. -/
noncomputable def profileRows {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (p : Point) : Debt :=
  ![P.M p, P.I p, P.J p, P.S p, P.pressure p]

theorem profileRows_eq_axisHistory {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (p : Point) :
    profileRows P p = axisHistory P.f P.U p + Pi.single 4 (P.pressure0 p.2) := by
  ext i
  fin_cases i <;>
    simp [profileRows, axisHistory, density, densityAt, ProfileHistories.Profiles.M,
      ProfileHistories.Profiles.I, ProfileHistories.Profiles.J, ProfileHistories.Profiles.S,
      ProfileHistories.Profiles.pressure, ProfileHistories.Profiles.H,
      ProfileHistories.Profiles.transportDensity, ProfileHistories.Profiles.energyDensity,
      ProfileHistories.primitive, add_comm]

theorem profileRows_sub {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    (hp : P.pressure0 = Q.pressure0) (p : Point) :
    profileRows P p - profileRows Q p = axisHistory P.f P.U p - axisHistory Q.f Q.U p := by
  rw [profileRows_eq_axisHistory, profileRows_eq_axisHistory, hp]
  abel

/-! ## An actual small five-row correction -/

theorem smooth_extension_ball {g : Coeff → Coeff} {r : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r)) :
    ∃ G : Coeff → Coeff, ContDiff ℝ ∞ G ∧ EqOn G g (Metric.ball 0 (r / 2)) := by
  obtain ⟨χ⟩ := ParametricModulation.exists_compactCutoff
    (Metric.closedBall (0 : Coeff) (r / 2)) (Metric.ball 0 r)
    (isCompact_closedBall _ _) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by linarith))
  let G : Coeff → Coeff := fun z => χ.value z • g z
  refine ⟨G, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ Metric.ball (0 : Coeff) r
    · exact χ.smooth.contDiffAt.smul (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hz))
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coeff => (0 : Coeff))
        z).congr_of_eventuallyEq
      filter_upwards [χ.zero_near z hz] with y hy
      change χ.value y • g y = 0
      rw [hy, zero_smul]
  · intro z hz
    change χ.value z • g z = g z
    rw [χ.one_on z (χ.contains (Metric.ball_subset_closedBall hz)), one_smul]

/-- The inverse branch is constructed once, then applied to the actual debt
family. The extension outside its small ball only supplies a globally smooth
coefficient curve; every asserted moment identity is inside the original branch. -/
theorem repair_family_rate (P : FiveProfileMoments.Patch) (b : ℝ)
    (hb : FiveProfileMoments.GoodExponent b) (S : Set ℝ) (hS : IsCompact S)
    (A G : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G)
    (hApos : ∀ eta, 0 < A eta) (q : ℕ)
    (d : ℝ → ℝ → Debt) (hd : ∀ N, ContDiff ℝ ∞ (d N))
    (D : ℝ) (hD : 0 < D)
    (hdb : ∀ N : ℝ, 1 ≤ N → JetBounds.FiniteJetBound q (d N) S (D / N)) :
    ∃ N0 C : ℝ, 1 ≤ N0 ∧ 0 < C ∧ ∀ N : ℝ, N0 ≤ N →
      ∃ (c : ℝ → Coeff) (V : Set ℝ), ContDiff ℝ ∞ c ∧ IsOpen V ∧ S ⊆ V ∧
        (∀ eta ∈ V, FiveProfileMoments.physicalMoments P b (A eta) (G eta) (c eta) = d N eta ∧
          ∀ X : ℝ, 0 < X → 0 < FiveProfileMoments.physicalE P b (A eta) (c eta) X) ∧
        JetBounds.FiniteJetBound q c S (C / N) := by
  obtain ⟨g, r, C0, hr, hC0, hg, _, hbranch⟩ := FiveProfileMoments.exists_normalized_repair P b hb
  obtain ⟨gext, hgext, hext⟩ := smooth_extension_ball hr hg
  have hr2 : 0 < r / 2 := by positivity
  have hvalue : ∀ z ∈ Metric.ball (0 : Coeff) (r / 2), ‖gext z‖ ≤ C0 * ‖z‖ := by
    intro z hz
    rw [hext hz]
    exact (hbranch z ((Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) hz)).2.1
  obtain ⟨J, hJ, hjet⟩ := smooth_solver_linear_jets hr2 hC0 hgext.contDiffOn hvalue q
  obtain ⟨B0, hB0, hnormal⟩ := FiveProfileMoments.compact_normalizedDebt_jets
    S hS hA hG (fun eta => (hApos eta).ne') q
  let delta : ℝ := min 1 (r / 2 / 2)
  have hdelta : 0 < delta := lt_min zero_lt_one (by positivity)
  let N0 : ℝ := max 1 (B0 * D / delta)
  refine ⟨N0, J * (B0 * D), le_max_left _ _, by positivity, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := zero_lt_one.trans_le hN1
  have hsmall : B0 * D / N ≤ delta := by
    apply (div_le_iff₀ hNpos).mpr
    have ht := (div_le_iff₀ hdelta).mp ((le_max_right _ _).trans hN)
    nlinarith
  let v : ℝ → Coeff := fun eta => FiveProfileMoments.normalizedDebt (A eta) (G eta) (d N eta)
  have hv : ContDiff ℝ ∞ v := FiveProfileMoments.normalizedDebt_contDiff hA hG (hd N)
    (fun eta => (hApos eta).ne')
  have hvb : JetBounds.FiniteJetBound q v S (B0 * D / N) := by
    convert! hnormal (d N) (hd N) (D / N) (div_nonneg hD.le hNpos.le) (hdb N hN1) using 1; ring
  let c : ℝ → Coeff := gext ∘ v
  let V : Set ℝ := v ⁻¹' Metric.ball 0 (r / 2)
  have hV : IsOpen V := Metric.isOpen_ball.preimage hv.continuous
  have hSV : S ⊆ V := by
    intro eta heta
    change ‖v eta - 0‖ < r / 2
    rw [sub_zero]
    exact (hvb.norm_le heta).trans_lt (hsmall.trans_lt (by
      dsimp [delta]
      exact (min_le_right _ _).trans_lt (by linarith)))
  refine ⟨c, V, hgext.comp hv, hV, hSV, ?_, ?_⟩
  · intro eta heta
    have hb0 := hbranch (v eta) ((Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) heta)
    have hc : c eta = g (v eta) := hext heta
    constructor
    · rw [hc, FiveProfileMoments.physicalMoments_eq P b (A eta) (G eta) (hApos eta).ne']
      rw [hb0.1]
      exact FiveProfileMoments.physical_normalized_debt (A eta) (G eta) (hApos eta).ne' (d N eta)
    · intro X hX
      rw [hc]
      exact mul_pos (hApos eta) (hb0.2.2.2 X hX)
  · intro j hj eta heta
    have hjb := hjet v hv (B0 * D / N) eta (div_pos (mul_pos hB0 hD) hNpos)
      hsmall (fun k hk => hvb k hk eta heta) j hj
    convert! hjb using 1; ring

/-- Repair debt, given by `-historyDifference W r f E U N W.right eta`. -/
noncomputable def repairDebt (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B)
    (f E U : Field) (N eta : ℝ) : Debt := -historyDifference W r f E U N W.right eta

theorem actual_repair_family (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (b : ℝ) (hb : FiveProfileMoments.GoodExponent b)
    (S : Set ℝ) (hS : IsCompact S) (A G : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ eta, 0 < A eta) (q : ℕ) :
    ∃ N0 C : ℝ, 1 ≤ N0 ∧ 0 < C ∧ ∀ N : ℝ, N0 ≤ N →
      ∃ (c : ℝ → Coeff) (V : Set ℝ), ContDiff ℝ ∞ c ∧ IsOpen V ∧ S ⊆ V ∧
        (∀ eta ∈ V, FiveProfileMoments.physicalMoments P b (A eta) (G eta) (c eta) =
            repairDebt W r f E U N eta ∧
          ∀ X : ℝ, 0 < X → 0 < FiveProfileMoments.physicalE P b (A eta) (c eta) X) ∧
        JetBounds.FiniteJetBound q c S (C / N) := by
  obtain ⟨D, hD, hdb⟩ := historyDifference_jets W r f E U ha hm hp₂ hf hE hU S hS q
  apply repair_family_rate P b hb S hS A G hA hG hApos q (repairDebt W r f E U)
    (fun N => (historyDifference_smooth W r f E U ha hm hp₂ hf hE hU N W.right).neg) D hD
  intro N hN j hj eta heta
  change ‖iteratedFDeriv ℝ j (-(historyDifference W r f E U N W.right)) eta‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hdb N hN W.right j hj eta heta

theorem finiteJet_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} {A : ℝ → ℝ} {c : ℝ → F} {S : Set ℝ} {B C : ℝ}
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAb : JetBounds.FiniteJetBound q A S B) (hcb : JetBounds.FiniteJetBound q c S C) :
    JetBounds.FiniteJetBound q (fun eta => A eta • c eta) S ((2 : ℝ) ^ q * B * C) := by
  intro n hn eta heta
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i A eta‖ * ‖iteratedFDeriv ℝ (n - i) c eta‖ :=
      norm_iteratedFDeriv_smul_le hA hc eta (nat_le_infty n)
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb i (hi'.trans hn) eta heta) (Nat.cast_nonneg
          _))
        (hcb (n - i) ((Nat.sub_le _ _).trans hn) eta heta) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ n * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ (2 : ℝ) ^ q * B * C := by gcongr; norm_num

/-- Edit U, given by `A p.2 * FiveProfileMoments.u P (c p.2) p.1`. -/
noncomputable def editU (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (p : Point) : ℝ := A p.2 * FiveProfileMoments.u P (c p.2) p.1

/-- Edit E, given by `A p.2 * FiveProfileMoments.e P (c p.2) p.1`. -/
noncomputable def editE (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (p : Point) : ℝ := A p.2 * FiveProfileMoments.e P (c p.2) p.1

/-- Edit F, given by `editE P A c p / Real.sqrt (2 * p.1)`. -/
noncomputable def editF (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (p : Point) : ℝ := editE P A c p / Real.sqrt (2 * p.1)

/-- Apply repair F, given by `f p + editF P A c p`. -/
noncomputable def applyRepairF (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f : Field) (p : Point) : ℝ := f p + editF P A c p

/-- Apply repair U, given by `U p + editU P A c p`. -/
noncomputable def applyRepairU (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (U : Field) (p : Point) : ℝ := U p + editU P A c p

theorem editU_contDiff (P : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (editU P A c) := by
  apply (hA.comp contDiff_snd).mul
  unfold FiveProfileMoments.u FiveProfileMoments.correction
  apply ContDiff.sum
  intro i _
  exact ((ContinuousLinearMap.proj i).contDiff.comp (hc.fst.comp contDiff_snd)).mul
    ((FiveProfileMoments.bump_contDiff P.leftHalf i).comp contDiff_fst)

theorem editE_contDiff (P : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (editE P A c) := by
  apply (hA.comp contDiff_snd).mul
  unfold FiveProfileMoments.e FiveProfileMoments.correction
  apply ContDiff.sum
  intro i _
  exact ((ContinuousLinearMap.proj i).contDiff.comp (hc.snd.comp contDiff_snd)).mul
    ((FiveProfileMoments.bump_contDiff P.rightHalf i).comp contDiff_fst)

theorem edits_zero_outside (P : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → Coeff)
    {p : Point} (hp : p.1 ∉ Ioo P.left P.right) :
    editU P A c p = 0 ∧ editE P A c p = 0 ∧ editF P A c p = 0 := by
  simp [editU, editE, editF, FiveProfileMoments.u_zero_outside P (c p.2) hp,
    FiveProfileMoments.e_zero_outside P (c p.2) hp]

theorem editF_contDiff (P : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (editF P A c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 < P.left
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point => (0 : ℝ)) p).congr_of_eventuallyEq
    have hn : {q : Point | q.1 < P.left} ∈ 𝓝 p :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hp
    filter_upwards [hn] with q hq
    exact (edits_zero_outside P A c (fun h => (not_lt_of_ge hq.le) h.1)).2.2
  · have hp0 : 0 < p.1 := P.left_pos.trans_le (le_of_not_gt hp)
    have hs : ContDiffAt ℝ ∞ (fun q : Point => Real.sqrt (2 * q.1)) p :=
      (contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)
    exact (editE_contDiff P A c hA hc).contDiffAt.div hs (by positivity)

theorem repair_preserves_outside (P : FiveProfileMoments.Patch) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (f U : Field) {p : Point} (hp : p.1 ∉ Ioo P.left P.right) :
    applyRepairF P A c f p = f p ∧ applyRepairU P A c U p = U p := by
  have hz := edits_zero_outside P A c hp
  simp [applyRepairF, applyRepairU, hz.1, hz.2.2]

theorem repair_preserves_radial_germ (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (X eta : ℝ) (hX : X ∉ Ioo P.left P.right) :
    ((fun x => applyRepairF P A c f (x, eta)) =ᶠ[𝓝 X] (fun x => f (x, eta))) ∧
    ((fun x => applyRepairU P A c U (x, eta)) =ᶠ[𝓝 X] (fun x => U (x, eta))) := by
  have hu : X ∉ tsupport (fun x => A eta * FiveProfileMoments.u P (c eta) x) :=
    fun h => hX ((FiveProfileMoments.physical_edits_tsupport P (A eta) (c eta)).1 h)
  have he : X ∉ tsupport (fun x => A eta * FiveProfileMoments.e P (c eta) x) :=
    fun h => hX ((FiveProfileMoments.physical_edits_tsupport P (A eta) (c eta)).2 h)
  rw [notMem_tsupport_iff_eventuallyEq] at hu he
  constructor
  · filter_upwards [he] with x hx
    simp [applyRepairF, editF, editE, hx]
  · filter_upwards [hu] with x hx
    simp [applyRepairU, editU, hx]

theorem physical_mixed_edits_bound (P : FiveProfileMoments.Patch) (S : Set ℝ)
    (hS : IsCompact S) (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ → Coeff, ContDiff ℝ ∞ c → ∀ eps : ℝ, 0 ≤ eps →
      JetBounds.FiniteJetBound q c S eps → ∀ eta ∈ S, ∀ k ≤ q, ∀ j ≤ q, ∀ X : ℝ,
        ‖iteratedFDeriv ℝ j (fun e => iteratedDeriv k (fun x => editU P A c (x, e)) X) eta‖ ≤ K *
            eps ∧
        ‖iteratedFDeriv ℝ j (fun e => iteratedDeriv k (fun x => editE P A c (x, e)) X) eta‖ ≤ K *
            eps := by
  obtain ⟨B0, hB0, hAb⟩ := FiveProfileMoments.compact_global_jet_bound S hS hA q
  obtain ⟨J, hJ, hjets⟩ := FiveProfileMoments.mixed_jet_bound P q
  refine ⟨J * (2 : ℝ) ^ q * B0, by positivity, ?_⟩
  intro c hc eps heps hcb eta heta k hk j hj X
  let v : ℝ → Coeff := fun e => A e • c e
  have hv : ContDiff ℝ ∞ v := hA.smul hc
  have hvb := finiteJet_smul hA hc hB0.le heps hAb hcb
  have hUfun : (fun e => iteratedDeriv k (fun x => editU P A c (x, e)) X) =
      fun e => iteratedDeriv k (FiveProfileMoments.u P (v e)) X := by
    funext e
    congr 1
    funext x
    simp [editU, v, FiveProfileMoments.u, FiveProfileMoments.correction,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
    ring
  have hEfun : (fun e => iteratedDeriv k (fun x => editE P A c (x, e)) X) =
      fun e => iteratedDeriv k (FiveProfileMoments.e P (v e)) X := by
    funext e
    congr 1
    funext x
    simp [editE, v, FiveProfileMoments.e, FiveProfileMoments.correction,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hUfun, hEfun]
  have hb := hjets k hk j v eta hv.contDiffAt X
  have hcost : J * ‖iteratedFDeriv ℝ j v eta‖ ≤ (J * (2 : ℝ) ^ q * B0) * eps := by
    calc
      _ ≤ J * ((2 : ℝ) ^ q * B0 * eps) := mul_le_mul_of_nonneg_left (hvb j hj eta heta) hJ.le
      _ = _ := by ring
  exact ⟨hb.1.trans hcost, hb.2.trans hcost⟩

/-! ## Exact restoration beyond the reserved patch -/

theorem normalized_density_change (X f U dE dU : ℝ) (hX : 0 < X) :
    densityAt X (f + dE / Real.sqrt (2 * X)) (U + dU) - densityAt X f U =
      FiveProfileMoments.profileChangeDensity (fun _ => U)
        (fun _ => Real.sqrt (2 * X) * f) (fun _ => dU) (fun _ => dE) X := by
  have hs : Real.sqrt (2 * X) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have he : Real.sqrt (2 * X) * (f + dE / Real.sqrt (2 * X)) = Real.sqrt (2 * X) * f + dE := by
    rw [mul_add, mul_div_cancel₀ _ hs]
  rw [density_eq_physical X (f + dE / Real.sqrt (2 * X)) (U + dU) hX,
    density_eq_physical X f U hX]
  simp only [he]
  ext i
  fin_cases i <;> dsimp [FiveProfileMoments.profileChangeDensity] <;> ring

theorem density_repair_change (P : FiveProfileMoments.Patch) (b : ℝ) (A G : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (eta : ℝ)
    (hU : ∀ X ∈ Ioo P.left P.right, U (X, eta) = G eta)
    (hE : ∀ X ∈ Ioo P.left P.right, Real.sqrt (2 * X) * f (X, eta) = A eta * X ^ b)
    (X : ℝ) :
    density (applyRepairF P A c f) (applyRepairU P A c U) (X, eta) - density f U (X, eta) =
      FiveProfileMoments.physicalDensity P b (A eta) (G eta) (c eta) X := by
  by_cases hX : X ∈ Ioo P.left P.right
  · have hXpos : 0 < X := P.left_pos.trans hX.1
    change densityAt X (f (X, eta) + editE P A c (X, eta) / Real.sqrt (2 * X))
      (U (X, eta) + editU P A c (X, eta)) - densityAt X (f (X, eta)) (U (X, eta)) = _
    rw [normalized_density_change _ _ _ _ _ hXpos]
    have heq := FiveProfileMoments.local_profile_change P b (A eta) (G eta) (c eta)
      (fun x => U (x, eta)) (fun x => Real.sqrt (2 * x) * f (x, eta)) hU hE X
    exact heq
  · have hz := repair_preserves_outside P A c f U (p := (X, eta)) hX
    rw [FiveProfileMoments.physicalDensity_zero_outside P b (A eta) (G eta) (c eta) hX]
    change densityAt X (applyRepairF P A c f (X, eta)) (applyRepairU P A c U (X, eta)) -
      densityAt X (f (X, eta)) (U (X, eta)) = 0
    rw [hz.1, hz.2, sub_self]

theorem axisHistory_repair_sub (P : FiveProfileMoments.Patch) (b : ℝ) (A G : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (eta X : ℝ) (hX : P.right ≤ X) (hA : A eta ≠ 0)
    (hU : ∀ x ∈ Ioo P.left P.right, U (x, eta) = G eta)
    (hE : ∀ x ∈ Ioo P.left P.right, Real.sqrt (2 * x) * f (x, eta) = A eta * x ^ b)
    (hi : ∀ i : Fin 5, IntervalIntegrable (fun x => density f U (x, eta) i) volume 0 X) :
    axisHistory (applyRepairF P A c f) (applyRepairU P A c U) (X, eta) -
      axisHistory f U (X, eta) = FiveProfileMoments.physicalMoments P b (A eta) (G eta) (c eta) :=
          by
  ext i
  have hc := FiveProfileMoments.physicalDensity_integrable P b (A eta) (G eta) hA (c eta) i
  have hnew : IntervalIntegrable
      (fun x => density (applyRepairF P A c f) (applyRepairU P A c U) (x, eta) i) volume 0 X := by
    apply ((hi i).add hc.intervalIntegrable).congr_ae
    filter_upwards with x
    have he := congrFun (density_repair_change P b A G c f U eta hU hE x) i
    simp only [Pi.sub_apply] at he
    linarith
  change (∫ x in (0 : ℝ)..X, density (applyRepairF P A c f) (applyRepairU P A c U) (x, eta) i) -
    (∫ x in (0 : ℝ)..X, density f U (x, eta) i) = _
  rw [← intervalIntegral.integral_sub hnew (hi i)]
  have he (x : ℝ) := congrFun (density_repair_change P b A G c f U eta hU hE x) i
  simp only [Pi.sub_apply] at he
  simp_rw [he]
  have hs : support (fun x => FiveProfileMoments.physicalDensity P b (A eta) (G eta) (c eta) x i) ⊆
      Ioc 0 X := by
    intro x hx
    have hp : x ∈ Ioo P.left P.right := by
      by_contra hp
      exact hx (by
          simp [FiveProfileMoments.physicalDensity_zero_outside P b (A eta) (G eta) (c eta) hp])
    exact ⟨P.left_pos.trans hp.1, hp.2.le.trans hX⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs]
  rfl

theorem localized_density_integrable (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (N X eta : ℝ) (i : Fin 5) :
    IntervalIntegrable (fun s => density (localizedF W r f N) (localizedU W r E U N) (s, eta) i)
        volume 0 X := by
  have hd : IntegrableOn (fun s => densityDifference r f E U N (s, eta) i)
      (Icc W.left W.right) volume :=
    (densityDifference_continuousOn W r f E U ha hm hp₂ hf hE hU N eta i).integrableOn_Icc
  have hi := (hd.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hnom : IntervalIntegrable (fun s => density f U (s, eta) i) volume 0 X :=
    ((density_contDiff f U hf hU i).continuous.comp (continuous_id.prodMk
        continuous_const)).intervalIntegrable 0 X
  apply (hnom.add hi.intervalIntegrable).congr_ae
  filter_upwards with s
  linarith [localized_density_difference W r f E U N s eta i]

theorem actual_histories_restored (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (b : ℝ) (A G : ℝ → ℝ)
    (c : ℝ → Coeff) (N eta X : ℝ) (hX : P.right ≤ X) (hA : A eta ≠ 0)
    (hpatchU : ∀ x ∈ Ioo P.left P.right, U (x, eta) = G eta)
    (hpatchE : ∀ x ∈ Ioo P.left P.right, Real.sqrt (2 * x) * f (x, eta) = A eta * x ^ b)
    (hrepair : FiveProfileMoments.physicalMoments P b (A eta) (G eta) (c eta) =
      repairDebt W r f E U N eta) :
    axisHistory (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (X, eta) = axisHistory f U (X, eta) := by
  have heq (x : ℝ) (hx : x ∈ Ioo P.left P.right) :
      localizedF W r f N (x, eta) = f (x, eta) ∧ localizedU W r E U N (x, eta) = U (x, eta) :=
    ⟨splice_eq_after W _ _ (hWP.trans hx.1), splice_eq_after W _ _ (hWP.trans hx.1)⟩
  have hrep := axisHistory_repair_sub P b A G c (localizedF W r f N) (localizedU W r E U N)
    eta X hX hA (fun x hx => (heq x hx).2.trans (hpatchU x hx))
    (fun x hx => by rw [(heq x hx).1]; exact hpatchE x hx)
    (localized_density_integrable W r f E U ha hm hp₂ hf hE hU N X eta)
  have hmod := axisHistory_localized_sub W r f E U ha hm hp₂ hf hE hU N X eta
    (P.left_pos.le.trans (P.ordered.le.trans hX))
  have hWX : W.right ≤ X := hWP.le.trans (P.ordered.le.trans hX)
  have hcx : W.clamp X = W.right :=
    congrArg Subtype.val (projIcc_of_right_le W.ordered.le hWX)
  have hcr : W.clamp W.right = W.right :=
    congrArg Subtype.val (projIcc_of_right_le W.ordered.le le_rfl)
  have hhist : historyDifference W r f E U N X eta = historyDifference W r f E U N W.right eta := by
    unfold historyDifference
    rw [hcx, hcr]
  rw [hrepair, repairDebt, ← hhist, ← hmod] at hrep
  exact (sub_eq_iff_eq_add.mp hrep).trans (by abel)

/-! ## Quantitative histories throughout the repair -/

theorem deriv_add_bound {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (eta B C : ℝ) (hB : |iteratedDeriv n f eta| ≤ B)
    (hC : |iteratedDeriv n g eta| ≤ C) :
    |iteratedDeriv n (fun e => f e + g e) eta| ≤ B + C := by
  rw [show (fun e => f e + g e) = f + g from rfl,
    iteratedDeriv_add (hf.of_le (nat_le_infty n)).contDiffAt (hg.of_le (nat_le_infty n)).contDiffAt]
  exact (abs_add_le _ _).trans (add_le_add hB hC)

theorem deriv_sub_bound {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (eta B C : ℝ) (hB : |iteratedDeriv n f eta| ≤ B)
    (hC : |iteratedDeriv n g eta| ≤ C) :
    |iteratedDeriv n (fun e => f e - g e) eta| ≤ B + C := by
  rw [show (fun e => f e - g e) = f - g from rfl,
    iteratedDeriv_sub (hf.of_le (nat_le_infty n)).contDiffAt (hg.of_le (nat_le_infty n)).contDiffAt]
  exact (abs_sub _ _).trans (add_le_add hB hC)

theorem deriv_const_mul_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (eta t B : ℝ) (hB : |iteratedDeriv n f eta| ≤ B) :
    |iteratedDeriv n (fun e => t * f e) eta| ≤ |t| * B := by
  rw [iteratedDeriv_const_mul _ (hf.of_le (nat_le_infty n)).contDiffAt, abs_mul]
  exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)

theorem density_perturbation_jet_bound (f U df dU : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U)
    (hdf : ContDiff ℝ ∞ df) (hdU : ContDiff ℝ ∞ dU)
    (n : ℕ) (eta X R B eps : ℝ) (hR : 0 ≤ R) (hX : |X| ≤ R)
    (hB : 0 ≤ B) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hfb : ∀ j ≤ n, |iteratedDeriv j f eta| ≤ B)
    (hUb : ∀ j ≤ n, |iteratedDeriv j U eta| ≤ B)
    (hdfb : ∀ j ≤ n, |iteratedDeriv j df eta| ≤ eps)
    (hdUb : ∀ j ≤ n, |iteratedDeriv j dU eta| ≤ eps) (i : Fin 5) :
    |iteratedDeriv n (fun e =>
        (densityAt X (f e + df e) (U e + dU e) - densityAt X (f e) (U e)) i) eta|
      ≤ ((1 + 2 * R) * (1 + (2 : ℝ) ^ n * (2 * B + 1))) * eps := by
  let H : ℝ := (2 : ℝ) ^ n * (2 * B + 1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcross : |iteratedDeriv n (fun e => U e * df e) eta| ≤ (2 : ℝ) ^ n * B * eps :=
    ShapeTransition.product_jet_bound hU hdf n eta hB heps hUb hdfb
  have hcross' : |iteratedDeriv n (fun e => f e * dU e) eta| ≤ (2 : ℝ) ^ n * B * eps :=
    ShapeTransition.product_jet_bound hf hdU n eta hB heps hfb hdUb
  have hsmall : |iteratedDeriv n (fun e => dU e * df e) eta| ≤ (2 : ℝ) ^ n * eps := by
    have h := ShapeTransition.product_jet_bound hdU hdf n eta heps heps hdUb hdfb
    exact h.trans (mul_le_of_le_one_right (by positivity) heps1)
  have hJ : |iteratedDeriv n (fun e => U e * df e + f e * dU e + dU e * df e) eta| ≤ H * eps := by
    have h := deriv_add_bound ((hU.mul hdf).add (hf.mul hdU)) (hdU.mul hdf) n eta _ _
      (deriv_add_bound (hU.mul hdf) (hf.mul hdU) n eta _ _ hcross hcross') hsmall
    convert! h using 1; dsimp [H]; ring
  have square (g dg : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hdg : ContDiff ℝ ∞ dg)
      (hgb : ∀ j ≤ n, |iteratedDeriv j g eta| ≤ B)
      (hdgb : ∀ j ≤ n, |iteratedDeriv j dg eta| ≤ eps) :
      |iteratedDeriv n (fun e => 2 * (g e * dg e) + dg e * dg e) eta| ≤ H * eps := by
    have hp := ShapeTransition.product_jet_bound hg hdg n eta hB heps hgb hdgb
    have hs := ShapeTransition.product_jet_bound hdg hdg n eta heps heps hdgb hdgb
    have hs' : |iteratedDeriv n (fun e => dg e * dg e) eta| ≤ (2 : ℝ) ^ n * eps :=
      hs.trans (mul_le_of_le_one_right (by positivity) heps1)
    have hm := deriv_const_mul_bound (hg.mul hdg) n eta 2 _ hp
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm
    have hh := deriv_add_bound (contDiff_const.mul (hg.mul hdg)) (hdg.mul hdg) n eta _ _ hm hs'
    convert! hh using 1; dsimp [H]; ring
  have hS := square U dU hU hdU hUb hdUb
  have hP := square f df hf hdf hfb hdfb
  have heq : (fun e => densityAt X (f e + df e) (U e + dU e) - densityAt X (f e) (U e)) =
      fun e => ![dU e, 2 * X * df e, 2 * X * (U e * df e + f e * dU e + dU e * df e),
        (2 * (U e * dU e) + dU e * dU e) - X * (2 * (f e * df e) + df e * df e),
        2 * (f e * df e) + df e * df e] := by
    funext e
    ext j
    fin_cases j <;> dsimp [densityAt] <;> ring
  change |iteratedDeriv n (fun e => ((fun e => densityAt X (f e + df e) (U e + dU e) - densityAt X
      (f e) (U e)) e) i) eta| ≤ _
  rw [heq]
  have hK0 : 1 ≤ (1 + 2 * R) * (1 + H) := by nlinarith
  have hK1 : 2 * R ≤ (1 + 2 * R) * (1 + H) := by nlinarith
  have hK2 : (2 * R) * H ≤ (1 + 2 * R) * (1 + H) := by nlinarith
  have hK3 : (1 + R) * H ≤ (1 + 2 * R) * (1 + H) := by nlinarith
  have hK4 : H ≤ (1 + 2 * R) * (1 + H) := by nlinarith
  fin_cases i
  · exact (hdUb n le_rfl).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hK0 heps)
  · have h := deriv_const_mul_bound hdf n eta (2 * X) eps (hdfb n le_rfl)
    have hc : |2 * X| ≤ 2 * R := by
        simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by
            norm_num)] using mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
    exact h.trans (mul_le_mul_of_nonneg_right (hc.trans hK1) heps)
  · have h := deriv_const_mul_bound ((hU.mul hdf).add (hf.mul hdU) |>.add (hdU.mul hdf))
      n eta (2 * X) (H * eps) hJ
    have hc : |2 * X| ≤ 2 * R := by
        simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by
            norm_num)] using mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
    exact h.trans (by calc
      _ ≤ (2 * R) * (H * eps) := mul_le_mul_of_nonneg_right hc (mul_nonneg hH heps)
      _ = ((2 * R) * H) * eps := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK2 heps)
  · have hm := deriv_const_mul_bound ((contDiff_const.mul (hf.mul hdf)).add (hdf.mul hdf)) n eta X
      _ hP
    have h := deriv_sub_bound ((contDiff_const.mul (hU.mul hdU)).add (hdU.mul hdU))
      (contDiff_const.mul ((contDiff_const.mul (hf.mul hdf)).add (hdf.mul hdf))) n eta _ _ hS hm
    exact h.trans (by calc
      _ ≤ H * eps + R * (H * eps) := add_le_add_right (mul_le_mul_of_nonneg_right hX (mul_nonneg hH
          heps)) _
      _ = ((1 + R) * H) * eps := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK3 heps)
  · exact hP.trans (mul_le_mul_of_nonneg_right hK4 heps)

theorem compact_eta_jet_bound (F : Field) (hF : ContDiff ℝ ∞ F)
    (KX S : Set ℝ) (hKX : IsCompact KX) (hS : IsCompact S) (q : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ X ∈ KX, ∀ eta ∈ S, ∀ j ≤ q,
      |iteratedDeriv j (fun e => F (X, e)) eta| ≤ B := by
  have hsingle (j : Fin (q + 1)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ X ∈ KX, ∀ eta ∈ S,
      |iteratedDeriv j (fun e => F (X, e)) eta| ≤ B := by
    obtain ⟨B, hb⟩ := (hKX.prod hS).exists_bound_of_continuousOn
      (ShapeTransition.partial_jet_continuous hF j).continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro X hX eta heta
    exact (hb (X, eta) ⟨hX, heta⟩).trans (le_max_left _ _)
  choose B hB hb using hsingle
  refine ⟨1 + ∑ j : Fin (q + 1), B j, ?_, ?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hB j)
    linarith
  · intro X hX eta heta j hj
    have hsum := Finset.single_le_sum (fun j _ => hB j)
      (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (q + 1)))
    exact (hb ⟨j, Nat.lt_succ_of_le hj⟩ X hX eta heta).trans (by linarith)

theorem normalized_edits_eta_bound (P : FiveProfileMoments.Patch) (S : Set ℝ)
    (hS : IsCompact S) (A : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ → Coeff, ContDiff ℝ ∞ c → ∀ eps : ℝ, 0 ≤ eps →
      JetBounds.FiniteJetBound q c S eps → ∀ eta ∈ S, ∀ j ≤ q, ∀ X : ℝ,
        |iteratedDeriv j (fun e => editF P A c (X, e)) eta| ≤ K * eps ∧
        |iteratedDeriv j (fun e => editU P A c (X, e)) eta| ≤ K * eps := by
  obtain ⟨J, hJ, hj⟩ := physical_mixed_edits_bound P S hS A hA q
  let t : ℝ := (Real.sqrt (2 * P.left))⁻¹
  have ht : 0 ≤ t := inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨(1 + t) * J, by positivity, ?_⟩
  intro c hc eps heps hcb eta heta j hjq X
  have h := hj c hc eps heps hcb eta heta 0 (Nat.zero_le q) j hjq X
  simp only [iteratedDeriv_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  have hcost : J * eps ≤ ((1 + t) * J) * eps :=
    mul_le_mul_of_nonneg_right (by nlinarith : J ≤ (1 + t) * J) heps
  refine ⟨?_, h.1.trans hcost⟩
  by_cases hX : X ∈ Ioo P.left P.right
  · have hXs : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by linarith [P.left_pos, hX.1])
    have hts : (Real.sqrt (2 * X))⁻¹ ≤ t := by
      apply inv_anti₀ (Real.sqrt_pos.2 (by linarith [P.left_pos]))
      exact Real.sqrt_le_sqrt (by linarith [hX.1])
    have he : (fun e => editF P A c (X, e)) =
        fun e => (Real.sqrt (2 * X))⁻¹ * editE P A c (X, e) := by
      funext e
      simp [editF, div_eq_mul_inv, mul_comm]
    rw [he]
    have hec : ContDiff ℝ ∞ (fun e => editE P A c (X, e)) :=
      (editE_contDiff P A c hA hc).comp (contDiff_const.prodMk contDiff_id)
    have hb := deriv_const_mul_bound hec j eta (Real.sqrt (2 * X))⁻¹ (J * eps) h.2
    rw [abs_of_nonneg (inv_nonneg.mpr hXs.le)] at hb
    exact hb.trans (by
      calc
        _ ≤ t * (J * eps) := mul_le_mul_of_nonneg_right hts (mul_nonneg hJ.le heps)
        _ ≤ ((1 + t) * J) * eps := by nlinarith)
  · have he : (fun e => editF P A c (X, e)) = fun _ => (0 : ℝ) := by
      funext e
      exact (edits_zero_outside P A c hX).2.2
    rw [he]
    have hz (k : ℕ) : iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      induction k with
      | zero => rfl
      | succ k hk =>
        rw [iteratedDeriv_succ, hk]
        funext x
        exact deriv_const x 0
    rw [hz]
    simpa only [abs_zero] using (show 0 ≤ ((1 + t) * J) * eps by positivity)

/-- Patch window, given by `⟨P.left, P.right, P.left_pos, P.ordered⟩`. -/
noncomputable def patchWindow (P : FiveProfileMoments.Patch) : Window :=
  ⟨P.left, P.right, P.left_pos, P.ordered⟩

/-- Repair density, given by `density (applyRepairF P A c f) (applyRepairU P A c U) p - density
f U p`. -/
noncomputable def repairDensity (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (p : Point) : Debt :=
  density (applyRepairF P A c f) (applyRepairU P A c U) p - density f U p

/-- Repair history difference, defined pointwise by `∫ s in P.left..(patchWindow P).clamp X,
repairDensity P A c f U (s, eta) i`. -/
noncomputable def repairHistoryDifference (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (X eta : ℝ) : Debt :=
  fun i => ∫ s in P.left..(patchWindow P).clamp X, repairDensity P A c f U (s, eta) i

theorem repairDensity_contDiff (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U) (i : Fin 5) :
    ContDiff ℝ ∞ (fun p => repairDensity P A c f U p i) :=
  (density_contDiff _ _ (hf.add (editF_contDiff P A c hA hc))
    (hU.add (editU_contDiff P A c hA hc)) i).sub (density_contDiff f U hf hU i)

theorem repairHistory_smooth (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U) (X : ℝ) :
    ContDiff ℝ ∞ (repairHistoryDifference P A c f U X) := by
  apply contDiff_pi.mpr
  intro i
  exact (ShapeTransition.smooth_parameter_interval ((patchWindow P).clamp_mem X).1
    (fun _ _ _ => (repairDensity_contDiff P A c f U hA hc hf hU i).contDiffAt)).1

theorem repairHistory_scalar_jets (P : FiveProfileMoments.Patch) (S : Set ℝ)
    (hS : IsCompact S) (A : ℝ → ℝ) (f U : Field)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U) (q : ℕ) :
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧ ∀ c : ℝ → Coeff, ContDiff ℝ ∞ c →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ delta → JetBounds.FiniteJetBound q c S eps →
      ∀ X eta : ℝ, eta ∈ S → ∀ j ≤ q, ∀ i : Fin 5,
        |iteratedDeriv j (fun e => repairHistoryDifference P A c f U X e i) eta| ≤ K * eps := by
  obtain ⟨J, hJ, hj⟩ := normalized_edits_eta_bound P S hS A hA q
  obtain ⟨Bf, hBf, hbf⟩ := compact_eta_jet_bound f hf (Icc P.left P.right) S isCompact_Icc hS q
  obtain ⟨BU, hBU, hbU⟩ := compact_eta_jet_bound U hU (Icc P.left P.right) S isCompact_Icc hS q
  let B0 : ℝ := Bf + BU
  let K0 : ℝ := (1 + 2 * P.right) * (1 + (2 : ℝ) ^ q * (2 * B0 + 1)) * J
  have hR : 0 < P.right := P.left_pos.trans P.ordered
  have hB0 : 0 < B0 := add_pos hBf hBU
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  refine ⟨1 / J, K0 * (P.right - P.left), by positivity, mul_pos hK0 (sub_pos.mpr P.ordered), ?_⟩
  intro c hc eps heps hepsJ hcb X eta heta j hjq i
  have hsmall : J * eps ≤ 1 := by
    have h := (le_div_iff₀ hJ).mp hepsJ
    nlinarith
  have hdensity : ∀ s ∈ Ioc P.left ((patchWindow P).clamp X),
      |iteratedDeriv j (fun e => repairDensity P A c f U (s, e) i) eta| ≤ K0 * eps := by
    intro s hs
    have hsP : s ∈ Icc P.left P.right := ⟨hs.1.le, hs.2.trans ((patchWindow P).clamp_mem X).2⟩
    have hsliceF : ContDiff ℝ ∞ (fun e => f (s, e)) := hf.comp (contDiff_const.prodMk contDiff_id)
    have hsliceU : ContDiff ℝ ∞ (fun e => U (s, e)) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hsliceDF : ContDiff ℝ ∞ (fun e => editF P A c (s, e)) :=
      (editF_contDiff P A c hA hc).comp (contDiff_const.prodMk contDiff_id)
    have hsliceDU : ContDiff ℝ ∞ (fun e => editU P A c (s, e)) :=
      (editU_contDiff P A c hA hc).comp (contDiff_const.prodMk contDiff_id)
    have hb := density_perturbation_jet_bound _ _ _ _ hsliceF hsliceU hsliceDF hsliceDU
      j eta s P.right B0 (J * eps) hR.le
      (by rw [abs_of_nonneg (P.left_pos.le.trans hsP.1)]; exact hsP.2)
      hB0.le (mul_nonneg hJ.le heps) hsmall
      (fun k hk => (hbf s hsP eta heta k (hk.trans hjq)).trans (le_add_of_nonneg_right hBU.le))
      (fun k hk => (hbU s hsP eta heta k (hk.trans hjq)).trans (le_add_of_nonneg_left hBf.le))
      (fun k hk => (hj c hc eps heps hcb eta heta k (hk.trans hjq) s).1)
      (fun k hk => (hj c hc eps heps hcb eta heta k (hk.trans hjq) s).2) i
    apply hb.trans
    change ((1 + 2 * P.right) * (1 + 2 ^ j * (2 * B0 + 1))) * (J * eps) ≤ _
    dsimp [K0]
    calc
      _ ≤ ((1 + 2 * P.right) * (1 + 2 ^ q * (2 * B0 + 1))) * (J * eps) := by
        gcongr
        norm_num
      _ = _ := by ring
  have hb := ShapeTransition.integral_jet_bound_on ((patchWindow P).clamp_mem X).1
    (fun _ _ _ => (repairDensity_contDiff P A c f U hA hc hf hU i).contDiffAt) j eta hdensity
  apply hb.trans
  calc
    _ ≤ (K0 * eps) * (P.right - P.left) := mul_le_mul_of_nonneg_left
      (sub_le_sub_right ((patchWindow P).clamp_mem X).2 _) (mul_nonneg hK0.le heps)
    _ = _ := by ring

theorem repairHistory_jets (P : FiveProfileMoments.Patch) (S : Set ℝ)
    (hS : IsCompact S) (A : ℝ → ℝ) (f U : Field)
    (hA : ContDiff ℝ ∞ A) (hf : ContDiff ℝ ∞ f) (hU : ContDiff ℝ ∞ U) (q : ℕ) :
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧ ∀ c : ℝ → Coeff, ContDiff ℝ ∞ c →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ delta → JetBounds.FiniteJetBound q c S eps → ∀ X : ℝ,
        JetBounds.FiniteJetBound q (repairHistoryDifference P A c f U X) S (K * eps) := by
  obtain ⟨delta, K, hd, hK, hb⟩ := repairHistory_scalar_jets P S hS A f U hA hf hU q
  refine ⟨delta, K, hd, hK, ?_⟩
  intro c hc eps heps hed hcb X j hj eta heta
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK.le heps)).mpr
  intro i
  have he := clm_iteratedDeriv (ContinuousLinearMap.proj i)
    (repairHistory_smooth P A c f U hA hc hf hU X) j eta
  simp only [ContinuousLinearMap.proj_apply] at he
  rw [← he]
  exact hb c hc eps heps hed hcb X eta heta j hj i

theorem repairDensity_zero_outside (P : FiveProfileMoments.Patch) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (f U : Field) {p : Point} (hp : p.1 ∉ Ioo P.left P.right) :
    repairDensity P A c f U p = 0 := by
  have h := repair_preserves_outside P A c f U hp
  simp only [repairDensity, density, h.1, h.2, sub_self]

theorem repairDensity_localized (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (A : ℝ → ℝ)
    (c : ℝ → Coeff) (N : ℝ) (p : Point) :
    repairDensity P A c (localizedF W r f N) (localizedU W r E U N) p = repairDensity P A c f U p
        := by
  by_cases hp : p.1 ∈ Ioo P.left P.right
  · have hf0 : localizedF W r f N p = f p := splice_eq_after W _ _ (hWP.trans hp.1)
    have hU0 : localizedU W r E U N p = U p := splice_eq_after W _ _ (hWP.trans hp.1)
    simp only [repairDensity, density, applyRepairF, applyRepairU, hf0, hU0]
  · rw [repairDensity_zero_outside P A c _ _ hp, repairDensity_zero_outside P A c f U hp]

theorem actual_repair_history_identity (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) (N X eta : ℝ) (hX : 0 ≤ X) :
    axisHistory (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (X, eta) -
      axisHistory (localizedF W r f N) (localizedU W r E U N) (X, eta) =
        repairHistoryDifference P A c f U X eta := by
  ext i
  have hdelta (x : ℝ) := congrFun (repairDensity_localized W r f E U P hWP A c N (x, eta)) i
  change ∀ x : ℝ, _ at hdelta
  have hi := localized_density_integrable W r f E U ha hm hp₂ hf hE hU N X eta i
  have hd : IntervalIntegrable (fun x => repairDensity P A c f U (x, eta) i) volume 0 X :=
    ((repairDensity_contDiff P A c f U hA hc hf hU i).continuous.comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 X
  have hn : IntervalIntegrable
      (fun x => density (applyRepairF P A c (localizedF W r f N))
        (applyRepairU P A c (localizedU W r E U N)) (x, eta) i) volume 0 X := by
    apply (hi.add hd).congr_ae
    filter_upwards with x
    have he := hdelta x
    dsimp only [repairDensity, Pi.sub_apply] at he
    dsimp only [repairDensity, Pi.sub_apply]
    linarith
  change (∫ x in (0 : ℝ)..X, density (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (x, eta) i) -
    (∫ x in (0 : ℝ)..X, density (localizedF W r f N) (localizedU W r E U N) (x, eta) i) = _
  rw [← intervalIntegral.integral_sub hn hi]
  have he (x : ℝ) : density (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (x, eta) i -
        density (localizedF W r f N) (localizedU W r E U N) (x, eta) i =
        repairDensity P A c f U (x, eta) i := hdelta x
  simp_rw [he]
  have hs : support (fun x => repairDensity P A c f U (x, eta) i) ⊆ Ioc P.left P.right := by
    intro x hx
    by_cases hout : x ∈ Ioo P.left P.right
    · exact ⟨hout.1, hout.2.le⟩
    · exact False.elim (hx (by simp [repairDensity_zero_outside P A c f U (p := (x, eta)) hout]))
  have hiw := integral_indicator_window (patchWindow P) (fun x => repairDensity P A c f U (x, eta)
      i) hX
  change (∫ s in (0 : ℝ)..X, (Ioc P.left P.right).indicator
      (fun x => repairDensity P A c f U (x, eta) i) s) =
      ∫ s in P.left..(patchWindow P).clamp X, repairDensity P A c f U (s, eta) i at hiw
  rw [indicator_eq_self.mpr hs] at hiw
  exact hiw

theorem repaired_axisHistory_identity (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (A : ℝ → ℝ) (c : ℝ → Coeff)
    (hA : ContDiff ℝ ∞ A) (hc : ContDiff ℝ ∞ c) (N X eta : ℝ) (hX : 0 ≤ X) :
    axisHistory (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (X, eta) - axisHistory f U (X, eta) =
        historyDifference W r f E U N X eta + repairHistoryDifference P A c f U X eta := by
  rw [← axisHistory_localized_sub W r f E U ha hm hp₂ hf hE hU N X eta hX,
    ← actual_repair_history_identity W r f E U ha hm hp₂ hf hE hU P hWP A c hA hc N X eta hX]
  abel

/-- Uniform in the frequency, the upper endpoint, and every actual smooth
coefficient curve with the stated small finite jets. In particular choosing
the constructed repair with `eps=C/N` retains the `1/N` rate. -/
theorem repaired_axisHistory_jets (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (A : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ delta C1 C2 : ℝ, 0 < delta ∧ 0 < C1 ∧ 0 < C2 ∧ ∀ N : ℝ, 1 ≤ N →
      ∀ c : ℝ → Coeff, ContDiff ℝ ∞ c → ∀ eps : ℝ, 0 ≤ eps → eps ≤ delta →
        JetBounds.FiniteJetBound q c S eps → ∀ X : ℝ, 0 ≤ X →
        JetBounds.FiniteJetBound q (fun eta =>
          axisHistory (applyRepairF P A c (localizedF W r f N))
            (applyRepairU P A c (localizedU W r E U N)) (X, eta) - axisHistory f U (X, eta))
          S (C1 / N + C2 * eps) := by
  obtain ⟨C1, hC1, hb1⟩ := historyDifference_jets W r f E U ha hm hp₂ hf hE hU S hS q
  obtain ⟨delta, C2, hd, hC2, hb2⟩ := repairHistory_jets P S hS A f U hA hf hU q
  refine ⟨delta, C1, C2, hd, hC1, hC2, ?_⟩
  intro N hN c hc eps heps hed hcb X hX
  have heq : (fun eta => axisHistory (applyRepairF P A c (localizedF W r f N))
      (applyRepairU P A c (localizedU W r E U N)) (X, eta) - axisHistory f U (X, eta)) =
      fun eta => historyDifference W r f E U N X eta + repairHistoryDifference P A c f U X eta := by
    funext eta
    exact repaired_axisHistory_identity W r f E U ha hm hp₂ hf hE hU P hWP A c hA hc N X eta hX
  rw [heq]
  intro j hj eta heta
  rw [fun_iteratedFDeriv_add_apply
    ((historyDifference_smooth W r f E U ha hm hp₂ hf hE hU N X).of_le (nat_le_infty j)).contDiffAt
    ((repairHistory_smooth P A c f U hA hc hf hU X).of_le (nat_le_infty j)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hb1 N hN X j hj eta heta)
    (hb2 c hc eps heps hed hcb X j hj eta heta))

/-- An actual smooth correction for every sufficiently large frequency,
with exact restoration on an open parameter neighborhood. Its debt is the
integral of the constructed modulation, rather than an assumed small row. -/
theorem exists_actual_restoring_repair (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (hWP : W.right < P.left) (b : ℝ)
    (hb : FiveProfileMoments.GoodExponent b) (A G : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ eta, 0 < A eta)
    (S J : Set ℝ) (hS : IsCompact S) (hJ : IsOpen J) (hSJ : S ⊆ J)
    (hpatchU : ∀ eta ∈ J, ∀ X ∈ Ioo P.left P.right, U (X, eta) = G eta)
    (hpatchE : ∀ eta ∈ J, ∀ X ∈ Ioo P.left P.right,
      Real.sqrt (2 * X) * f (X, eta) = A eta * X ^ b) (q : ℕ) :
    ∃ N0 C : ℝ, 1 ≤ N0 ∧ 0 < C ∧ ∀ N : ℝ, N0 ≤ N →
      ∃ (c : ℝ → Coeff) (V : Set ℝ), ContDiff ℝ ∞ c ∧ IsOpen V ∧ S ⊆ V ∧ V ⊆ J ∧
        JetBounds.FiniteJetBound q c S (C / N) ∧
        ∀ eta ∈ V, ∀ X : ℝ, P.right ≤ X →
          axisHistory (applyRepairF P A c (localizedF W r f N))
            (applyRepairU P A c (localizedU W r E U N)) (X, eta) = axisHistory f U (X, eta) := by
  obtain ⟨N0, C, hN0, hC, hsolve⟩ := actual_repair_family W r f E U ha hm hp₂ hf hE hU
    P b hb S hS A G hA hG hApos q
  refine ⟨N0, C, hN0, hC, ?_⟩
  intro N hN
  obtain ⟨c, V, hc, hV, hSV, hmom, hcb⟩ := hsolve N hN
  refine ⟨c, V ∩ J, hc, hV.inter hJ, fun eta heta => ⟨hSV heta, hSJ heta⟩,
    inter_subset_right, hcb, ?_⟩
  intro eta heta X hX
  exact actual_histories_restored W r f E U ha hm hp₂ hf hE hU P hWP b A G c N eta X hX
    (hApos eta).ne' (hpatchU eta heta.2) (hpatchE eta heta.2) (hmom eta heta.1).1

theorem profileRows_eq_of_axisHistory_eq {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    (hP0 : P.pressure0 = Q.pressure0) {p : Point}
    (h : axisHistory P.f P.U p = axisHistory Q.f Q.U p) : profileRows P p = profileRows Q p := by
  apply sub_eq_zero.mp
  rw [profileRows_sub P Q hP0 p, h, sub_self]

end NavierStokes.ModulatedHistories
