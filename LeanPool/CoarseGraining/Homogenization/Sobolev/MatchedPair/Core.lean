/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.MatchedPair.ScaledPoincare
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotient

/-! # Core -/

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

/-!
# Matched-pair Poincaré on axis cubes

Assembles the zero-set lower bound and the matched-pair Poincaré inequality (the
high-moment paper's `e.doubled.poincare`, Armstrong–Kuusi–Loher, to appear)
from the scaled Poincaré inequalities of `ScaledPoincare`.  All `L²` bookkeeping
is carried out on the Lebesgue `L²` realizations `H1Function.toScalarL2`, whose
triangle inequality is free, and converted to the `eLpNorm` spelling at the
interface.
-/

noncomputable section

variable {d : ℕ}

/-! ## Generic `L²`-realization helpers -/

/-- The `L²` realization is subtractive. -/
theorem toScalarL2_sub {U : Set (Homogenization.Vec d)} (u v : H1Function U) :
    (u - v).toScalarL2 = u.toScalarL2 - v.toScalarL2 := by
  rw [sub_eq_add_neg, H1Function.toScalarL2_add]
  have : (-v).toScalarL2 = -(v.toScalarL2) := by
    have h := H1Function.toScalarL2_smul (-1 : ℝ) v
    simpa using h
  rw [this, ← sub_eq_add_neg]

/-- The `L²` realization depends only on the underlying function. -/
theorem toScalarL2_congr {U : Set (Homogenization.Vec d)} {u v : H1Function U}
    (h : u.toFun = v.toFun) : u.toScalarL2 = v.toScalarL2 := by
  simp only [H1Function.toScalarL2, Homogenization.toScalarL2]
  refine MeasureTheory.MemLp.toLp_congr u.memL2 v.memL2 ?_
  rw [h]

/-- Triangle inequality for the `L²` realization of a sum. -/
theorem norm_toScalarL2_add_le {U : Set (Homogenization.Vec d)} (u v : H1Function U) :
    ‖(u + v).toScalarL2‖ ≤ ‖u.toScalarL2‖ + ‖v.toScalarL2‖ := by
  rw [H1Function.toScalarL2_add]
  exact norm_add_le _ _

/-- Triangle inequality for the `L²` realization of a difference. -/
theorem norm_toScalarL2_sub_le {U : Set (Homogenization.Vec d)} (u v : H1Function U) :
    ‖(u - v).toScalarL2‖ ≤ ‖u.toScalarL2‖ + ‖v.toScalarL2‖ := by
  rw [toScalarL2_sub]
  exact norm_sub_le _ _

/-- The squared `L²`-realization norm is the integral of the square. -/
theorem l2_normSq_eq_integral {U : Set (Homogenization.Vec d)} (u : H1Function U) :
    ‖u.toScalarL2‖ ^ 2 = ∫ x in U, u.toFun x ^ 2 ∂MeasureTheory.volume := by
  rw [norm_toScalarL2_eq]
  exact toReal_eLpNorm_two_sq_eq_integral_sq u.memL2

/-- Elementary: `x ≤ a + b` whenever `x² ≤ a² + b²` and all are nonnegative. -/
private theorem le_add_of_sq_le_sq_add_sq {x a b : ℝ}
    (_hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x ^ 2 ≤ a ^ 2 + b ^ 2) :
    x ≤ a + b := by
  nlinarith [mul_nonneg ha hb]

/-! ## F2: the zero-set lower bound -/

/-- **Zero-set lower bound.**  If the value sets of `f` and `g` together
cover at most `|U|`, then for every level `c` the `L²` norm of the constant `c`
on `U = axisCube z L` is dominated by the two centered `L²` norms `‖f − c‖` and
`‖g − c‖`.  (Requires measurable representatives, satisfied by the level-set
truncations fed in downstream.) -/
theorem matchedPair_zeroSet (z : Homogenization.Vec d) {L : ℝ}
    (f g : H1Function (axisCube z L)) (c : ℝ)
    (hfm : Measurable f.toFun) (hgm : Measurable g.toFun)
    (hzero : MeasureTheory.volume {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0}
             + MeasureTheory.volume {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0}
             ≤ MeasureTheory.volume (axisCube z L)) :
    ‖(H1Function.const (U := axisCube z L) c).toScalarL2‖
      ≤ ‖(f.addConst (-c)).toScalarL2‖ + ‖(g.addConst (-c)).toScalarL2‖ := by
  classical
  have hUmeas : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  -- Level sets and their complements inside `U`.
  set Sf : Set (Homogenization.Vec d) := {x | x ∈ axisCube z L ∧ f.toFun x = 0} with hSfdef
  set Sg : Set (Homogenization.Vec d) := {x | x ∈ axisCube z L ∧ g.toFun x = 0} with hSgdef
  set Nf : Set (Homogenization.Vec d) := {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0} with hNfdef
  set Ng : Set (Homogenization.Vec d) := {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0} with hNgdef
  have hSf : MeasurableSet Sf :=
    hUmeas.inter (hfm (measurableSet_singleton 0))
  have hSg : MeasurableSet Sg :=
    hUmeas.inter (hgm (measurableSet_singleton 0))
  have hNf : MeasurableSet Nf :=
    hUmeas.inter (hfm (measurableSet_singleton 0)).compl
  have hNg : MeasurableSet Ng :=
    hUmeas.inter (hgm (measurableSet_singleton 0)).compl
  -- Squares are integrable on `U`.
  have hsqInt : ∀ (h : H1Function (axisCube z L)),
      MeasureTheory.IntegrableOn (fun x => h.toFun x ^ 2) (axisCube z L)
        MeasureTheory.volume := by
    intro h
    have := (h.memL2.integrable_norm_pow (p := 2) (by norm_num))
    simpa [MeasureTheory.IntegrableOn, Real.norm_eq_abs, sq_abs] using this
  -- Lower bound: `∫_U (h − c)² ≥ c² · |{h = 0} ∩ U|`.
  have hlower : ∀ (h : H1Function (axisCube z L)) (S : Set (Homogenization.Vec d)),
      MeasurableSet S → S ⊆ axisCube z L → (∀ x ∈ S, h.toFun x = 0) →
      c ^ 2 * (MeasureTheory.volume S).toReal ≤
        ∫ x in axisCube z L, (h.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume := by
    intro h S hSmeas hSsub hSzero
    have hcongr : ∀ x ∈ S, (h.addConst (-c)).toFun x ^ 2 = c ^ 2 := by
      intro x hx
      have hx0 : h.toFun x = 0 := hSzero x hx
      simp only [H1Function.addConst_apply, hx0]
      ring
    have heq : ∫ x in S, (h.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume =
        c ^ 2 * (MeasureTheory.volume S).toReal := by
      rw [MeasureTheory.setIntegral_congr_fun hSmeas hcongr]
      rw [MeasureTheory.setIntegral_const]
      rw [smul_eq_mul, mul_comm]
      rfl
    have hmono : ∫ x in S, (h.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume ≤
        ∫ x in axisCube z L, (h.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume := by
      refine MeasureTheory.setIntegral_mono_set (hsqInt _) ?_ ?_
      · exact Filter.Eventually.of_forall fun x => by positivity
      · exact Filter.Eventually.of_forall (fun x hx => hSsub hx)
    rw [heq] at hmono
    exact hmono
  have hlf := hlower f Sf hSf (fun x hx => hx.1) (fun x hx => hx.2)
  have hlg := hlower g Sg hSg (fun x hx => hx.1) (fun x hx => hx.2)
  -- Measure complement: `|Sf| + |Sg| ≥ |U|`.
  have hUlt : MeasureTheory.volume (axisCube z L) < ⊤ := by
    have h := (isFiniteMeasure_volumeMeasureOn_axisCube z L).measure_univ_lt_top
    rwa [volumeMeasureOn, MeasureTheory.Measure.restrict_apply_univ] at h
  have hpartf : MeasureTheory.volume (axisCube z L) =
      MeasureTheory.volume Sf + MeasureTheory.volume Nf := by
    have hunion : Sf ∪ Nf = axisCube z L := by
      ext x; by_cases hx : x ∈ axisCube z L <;> by_cases h0 : f.toFun x = 0 <;>
        simp [hSfdef, hNfdef, hx, h0]
    have hdisj : Disjoint Sf Nf := by
      rw [Set.disjoint_left]; rintro x hxf hxn; exact hxn.2 hxf.2
    rw [← hunion, MeasureTheory.measure_union hdisj hNf]
  have hpartg : MeasureTheory.volume (axisCube z L) =
      MeasureTheory.volume Sg + MeasureTheory.volume Ng := by
    have hunion : Sg ∪ Ng = axisCube z L := by
      ext x; by_cases hx : x ∈ axisCube z L <;> by_cases h0 : g.toFun x = 0 <;>
        simp [hSgdef, hNgdef, hx, h0]
    have hdisj : Disjoint Sg Ng := by
      rw [Set.disjoint_left]; rintro x hxg hxn; exact hxn.2 hxg.2
    rw [← hunion, MeasureTheory.measure_union hdisj hNg]
  have hvolLe : MeasureTheory.volume (axisCube z L) ≤
      MeasureTheory.volume Sf + MeasureTheory.volume Sg := by
    have hsum : MeasureTheory.volume (axisCube z L) + MeasureTheory.volume (axisCube z L) =
        (MeasureTheory.volume Sf + MeasureTheory.volume Sg) +
          (MeasureTheory.volume Nf + MeasureTheory.volume Ng) := by
      nth_rewrite 1 [hpartf]
      nth_rewrite 1 [hpartg]
      ring
    have hle : MeasureTheory.volume (axisCube z L) + MeasureTheory.volume (axisCube z L) ≤
        (MeasureTheory.volume Sf + MeasureTheory.volume Sg) +
          MeasureTheory.volume (axisCube z L) := by
      rw [hsum]
      exact add_le_add (le_refl (MeasureTheory.volume Sf + MeasureTheory.volume Sg)) hzero
    exact (ENNReal.add_le_add_iff_right hUlt.ne).1 hle
  -- Pass to reals.
  have hvolReal : (MeasureTheory.volume (axisCube z L)).toReal ≤
      (MeasureTheory.volume Sf).toReal + (MeasureTheory.volume Sg).toReal := by
    have hSflt : MeasureTheory.volume Sf ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) hUlt).ne
    have hSglt : MeasureTheory.volume Sg ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) hUlt).ne
    calc (MeasureTheory.volume (axisCube z L)).toReal
        ≤ (MeasureTheory.volume Sf + MeasureTheory.volume Sg).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hSflt, hSglt⟩) hvolLe
      _ = (MeasureTheory.volume Sf).toReal + (MeasureTheory.volume Sg).toReal :=
          ENNReal.toReal_add hSflt hSglt
  -- Assemble the squared inequality.
  have hconstSq : ‖(H1Function.const (U := axisCube z L) c).toScalarL2‖ ^ 2 =
      c ^ 2 * (MeasureTheory.volume (axisCube z L)).toReal := by
    rw [l2_normSq_eq_integral]
    have : ∫ x in axisCube z L, (H1Function.const (U := axisCube z L) c).toFun x ^ 2
        ∂MeasureTheory.volume = ∫ _ in axisCube z L, c ^ 2 ∂MeasureTheory.volume := by
      apply MeasureTheory.setIntegral_congr_fun hUmeas
      intro x _; simp [H1Function.const_apply]
    rw [this, MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have hcsq_nonneg : 0 ≤ c ^ 2 := sq_nonneg c
  have hkey : ‖(H1Function.const (U := axisCube z L) c).toScalarL2‖ ^ 2 ≤
      ‖(f.addConst (-c)).toScalarL2‖ ^ 2 + ‖(g.addConst (-c)).toScalarL2‖ ^ 2 := by
    rw [hconstSq, l2_normSq_eq_integral, l2_normSq_eq_integral]
    calc c ^ 2 * (MeasureTheory.volume (axisCube z L)).toReal
        ≤ c ^ 2 * ((MeasureTheory.volume Sf).toReal + (MeasureTheory.volume Sg).toReal) :=
          mul_le_mul_of_nonneg_left hvolReal hcsq_nonneg
      _ = c ^ 2 * (MeasureTheory.volume Sf).toReal +
            c ^ 2 * (MeasureTheory.volume Sg).toReal := by ring
      _ ≤ (∫ x in axisCube z L, (f.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume) +
            (∫ x in axisCube z L, (g.addConst (-c)).toFun x ^ 2 ∂MeasureTheory.volume) :=
          add_le_add hlf hlg
  exact le_add_of_sq_le_sq_add_sq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hkey

/-! ## Gradient uniqueness and the `H¹`-input Dirichlet Poincaré -/

/-- Two `H¹` witnesses with the same value have a.e. equal gradient coordinates
on an open domain. -/
theorem gradCoord_ae_eq_of_toFun_eq {U : Set (Homogenization.Vec d)} (hU : IsOpen U)
    (p q : H1Function U) (h : p.toFun = q.toFun) (i : Fin d) :
    (fun x => p.grad x i) =ᵐ[MeasureTheory.volume.restrict U] (fun x => q.grad x i) := by
  refine HasWeakPartialDerivOn.ae_eq hU
    (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((p.gradMemL2 i).locallyIntegrable (by norm_num)))
    (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((q.gradMemL2 i).locallyIntegrable (by norm_num))) ?_ (q.hasWeakGradient i)
  have hp := p.hasWeakGradient i
  rw [h] at hp
  exact hp

/-- **Scaled Dirichlet Poincaré for `H¹` inputs.**  If `w ∈ H¹(axisCube z L)` has a zero-trace
representative (`MemH10 U w.toFun`), then `w` obeys the scaled Dirichlet Poincaré
with its *own* gradient on the right-hand side. -/
theorem scaled_dirichlet_poincare_h1 {d : ℕ} [NeZero d] (z : Homogenization.Vec d) {L : ℝ}
    (hL : 0 < L) (w : H1Function (axisCube z L))
    (hw : MemH10 (axisCube z L) w.toFun) :
    ‖w.toScalarL2‖ ≤ unitDirichletPoincareConst d * L * w.gradientCoordL2NormSum := by
  obtain ⟨v, hv⟩ := hw
  have hbound := scaled_dirichlet_poincare_norm z hL v
  have hval : ‖v.toH1Function.toScalarL2‖ = ‖w.toScalarL2‖ := by
    rw [toScalarL2_congr hv]
  have hgrad : v.toH1Function.gradientCoordL2NormSum = w.gradientCoordL2NormSum := by
    unfold H1Function.gradientCoordL2NormSum
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [norm_gradCoordToScalarL2_eq, norm_gradCoordToScalarL2_eq]
    exact congrArg ENNReal.toReal
      (MeasureTheory.eLpNorm_congr_ae
        (gradCoord_ae_eq_of_toFun_eq (isOpen_axisCube z L) v.toH1Function w hv i))
  rw [hval, hgrad] at hbound
  exact hbound

/-- The `i`th gradient `L²` realization is subtractive. -/
theorem gradCoordToScalarL2_sub {U : Set (Homogenization.Vec d)} (u v : H1Function U) (i : Fin d) :
    (u - v).gradCoordToScalarL2 i = u.gradCoordToScalarL2 i - v.gradCoordToScalarL2 i := by
  rw [sub_eq_add_neg, H1Function.gradCoordToScalarL2_add]
  have hneg : (-v).gradCoordToScalarL2 i = -(v.gradCoordToScalarL2 i) := by
    have h := H1Function.gradCoordToScalarL2_smul (-1 : ℝ) v i
    simpa using h
  rw [hneg, ← sub_eq_add_neg]

/-- The coordinate-sum gradient norm is subadditive under differences. -/
theorem gradientCoordL2NormSum_sub_le {U : Set (Homogenization.Vec d)} (u v : H1Function U) :
    (u - v).gradientCoordL2NormSum ≤
      u.gradientCoordL2NormSum + v.gradientCoordL2NormSum := by
  unfold H1Function.gradientCoordL2NormSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _
  rw [gradCoordToScalarL2_sub]
  exact norm_sub_le _ _

/-! ## F3: the matched-pair Poincaré inequality -/

/-- The matched-pair Poincaré constant `3 (2 C₁ + C₂)`, with `C₁` the mean-zero
and `C₂` the Dirichlet unit-cube constants. -/
noncomputable def matchedPairPoincareConst (d : ℕ) [NeZero d] : ℝ :=
  3 * (2 * unitMeanZeroPoincareConst d + unitDirichletPoincareConst d)

theorem matchedPairPoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ matchedPairPoincareConst d := by
  unfold matchedPairPoincareConst
  have := unitMeanZeroPoincareConst_nonneg d
  have := unitDirichletPoincareConst_nonneg d
  positivity

/-- **Matched-pair Poincaré (norm form; the high-moment paper's `e.doubled.poincare`).**

If `f, g ∈ H¹(axisCube z L)` share a boundary trace (`f − g ∈ H¹₀`) and their
value sets together cover at most `|U|`, then
`‖f‖_{L²} + ‖g‖_{L²} ≤ C_d · L · (‖∇f‖ + ‖∇g‖)`. -/
theorem matchedPair_poincare {d : ℕ} [NeZero d] (z : Homogenization.Vec d) {L : ℝ}
    (hL : 0 < L) (f g : H1Function (axisCube z L))
    (hfm : Measurable f.toFun) (hgm : Measurable g.toFun)
    (hfg : MemH10 (axisCube z L) (fun x => f.toFun x - g.toFun x))
    (hzero : MeasureTheory.volume {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0}
             + MeasureTheory.volume {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0}
             ≤ MeasureTheory.volume (axisCube z L)) :
    ‖f.toScalarL2‖ + ‖g.toScalarL2‖ ≤
      matchedPairPoincareConst d * L *
        (f.gradientCoordL2NormSum + g.gradientCoordL2NormSum) := by
  classical
  let U := axisCube z L
  set C₁ := unitMeanZeroPoincareConst d with hC1def
  set C₂ := unitDirichletPoincareConst d with hC2def
  set Gf := f.gradientCoordL2NormSum with hGfdef
  set Gg := g.gradientCoordL2NormSum with hGgdef
  set af := integralAverage U f.toFun with hafdef
  set ag := integralAverage U g.toFun with hagdef
  set c := (af + ag) / 2 with hcdef
  have hL_nn : 0 ≤ L := hL.le
  have hC1_nn : 0 ≤ C₁ := unitMeanZeroPoincareConst_nonneg d
  have hC2_nn : 0 ≤ C₂ := unitDirichletPoincareConst_nonneg d
  have hGf_nn : 0 ≤ Gf := f.gradientCoordL2NormSum_nonneg
  have hGg_nn : 0 ≤ Gg := g.gradientCoordL2NormSum_nonneg
  have hG_nn : 0 ≤ Gf + Gg := add_nonneg hGf_nn hGg_nn
  -- The constant-`t` `L²` elements scale linearly.
  have const_smul : ∀ t : ℝ, (H1Function.const (U := U) t).toScalarL2 =
      t • (H1Function.const (U := U) 1).toScalarL2 := by
    intro t
    rw [← H1Function.toScalarL2_smul]
    apply toScalarL2_congr
    funext x
    simp [H1Function.smul_toFun, H1Function.const_apply]
  set s := ‖(H1Function.const (U := U) 1).toScalarL2‖ with hsdef
  have const_norm : ∀ t : ℝ, ‖(H1Function.const (U := U) t).toScalarL2‖ = |t| * s := by
    intro t
    rw [const_smul t, norm_smul, Real.norm_eq_abs]
  -- `f − g` as an `H¹` function with a zero-trace representative.
  have hfmg_mem : MemH10 U (f - g).toFun := by
    simpa [H1Function.sub_toFun] using hfg
  have hfmg_grad_le : (f - g).gradientCoordL2NormSum ≤ Gf + Gg :=
    gradientCoordL2NormSum_sub_le f g
  -- S1/S2: mean-subtracted Poincaré on `f` and `g`.
  have S1 : ‖f.subAverage.toScalarL2‖ ≤ C₁ * L * Gf := by
    have h := scaled_meanZero_poincare z hL f
    rwa [← norm_toScalarL2_eq, ← gradientCoordL2NormSum_eq_sum_eLpNorm] at h
  have S2 : ‖g.subAverage.toScalarL2‖ ≤ C₁ * L * Gg := by
    have h := scaled_meanZero_poincare z hL g
    rwa [← norm_toScalarL2_eq, ← gradientCoordL2NormSum_eq_sum_eLpNorm] at h
  -- S3: Dirichlet Poincaré on `f − g`.
  have S3 : ‖(f - g).toScalarL2‖ ≤ C₂ * L * (Gf + Gg) := by
    have h := scaled_dirichlet_poincare_h1 z hL (f - g) hfmg_mem
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left hfmg_grad_le (by positivity)
  -- S4: mean-subtracted Poincaré on `f − g`.
  have S4 : ‖(f - g).subAverage.toScalarL2‖ ≤ C₁ * L * (Gf + Gg) := by
    have h := scaled_meanZero_poincare z hL (f - g)
    rw [← norm_toScalarL2_eq, ← gradientCoordL2NormSum_eq_sum_eLpNorm] at h
    exact h.trans (mul_le_mul_of_nonneg_left hfmg_grad_le (by positivity))
  -- The mean gap `⨍(f−g) = af − ag`.
  have hmean : integralAverage U (fun x => f.toFun x - g.toFun x) = af - ag := by
    rw [hafdef, hagdef]
    simp only [integralAverage]
    rw [MeasureTheory.integral_sub f.integrableOn.integrable g.integrableOn.integrable]
    ring
  -- Gap bound: `|af − ag| · s ≤ (C₁ + C₂) L (Gf + Gg)`.
  have hgap : |af - ag| * s ≤ (C₁ + C₂) * L * (Gf + Gg) := by
    have heq : ‖(H1Function.const (U := U) (af - ag)).toScalarL2‖ =
        ‖((f - g) - (f - g).subAverage).toScalarL2‖ := by
      apply congrArg
      apply toScalarL2_congr
      funext x
      simp only [H1Function.sub_toFun, H1Function.subAverage_apply, H1Function.const_apply, hmean]
      ring
    rw [const_norm] at heq
    calc |af - ag| * s = ‖((f - g) - (f - g).subAverage).toScalarL2‖ := heq
      _ ≤ ‖(f - g).toScalarL2‖ + ‖(f - g).subAverage.toScalarL2‖ :=
          norm_toScalarL2_sub_le _ _
      _ ≤ C₂ * L * (Gf + Gg) + C₁ * L * (Gf + Gg) := add_le_add S3 S4
      _ = (C₁ + C₂) * L * (Gf + Gg) := by ring
  -- Centered Poincaré: `‖f − c‖ + ‖g − c‖ ≤ (2C₁ + C₂) L (Gf + Gg)`.
  have hs_nn : 0 ≤ s := norm_nonneg _
  have hafc : |af - c| = |af - ag| / 2 := by
    rw [show af - c = (af - ag) / 2 by rw [hcdef]; ring, abs_div]
    norm_num
  have hagc : |ag - c| = |af - ag| / 2 := by
    rw [show ag - c = -((af - ag) / 2) by rw [hcdef]; ring, abs_neg, abs_div]
    norm_num
  have hfc_center : ‖(f.addConst (-c)).toScalarL2‖ ≤
      ‖f.subAverage.toScalarL2‖ + |af - c| * s := by
    have heq : (f.addConst (-c)).toScalarL2 =
        f.subAverage.toScalarL2 + (H1Function.const (U := U) (af - c)).toScalarL2 := by
      rw [← H1Function.toScalarL2_add]
      apply toScalarL2_congr
      funext x
      simp only [H1Function.add_toFun, H1Function.addConst_apply, H1Function.subAverage_apply,
        H1Function.const_apply, hafdef]
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [const_norm]
  have hgc_center : ‖(g.addConst (-c)).toScalarL2‖ ≤
      ‖g.subAverage.toScalarL2‖ + |ag - c| * s := by
    have heq : (g.addConst (-c)).toScalarL2 =
        g.subAverage.toScalarL2 + (H1Function.const (U := U) (ag - c)).toScalarL2 := by
      rw [← H1Function.toScalarL2_add]
      apply toScalarL2_congr
      funext x
      simp only [H1Function.add_toFun, H1Function.addConst_apply, H1Function.subAverage_apply,
        H1Function.const_apply, hagdef]
      ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [const_norm]
  have hcentered : ‖(f.addConst (-c)).toScalarL2‖ + ‖(g.addConst (-c)).toScalarL2‖ ≤
      (2 * C₁ + C₂) * L * (Gf + Gg) := by
    have hsum : ‖(f.addConst (-c)).toScalarL2‖ + ‖(g.addConst (-c)).toScalarL2‖ ≤
        (‖f.subAverage.toScalarL2‖ + ‖g.subAverage.toScalarL2‖) + |af - ag| * s := by
      calc ‖(f.addConst (-c)).toScalarL2‖ + ‖(g.addConst (-c)).toScalarL2‖
          ≤ (‖f.subAverage.toScalarL2‖ + |af - c| * s) +
              (‖g.subAverage.toScalarL2‖ + |ag - c| * s) := add_le_add hfc_center hgc_center
        _ = (‖f.subAverage.toScalarL2‖ + ‖g.subAverage.toScalarL2‖) +
              (|af - c| + |ag - c|) * s := by ring
        _ = (‖f.subAverage.toScalarL2‖ + ‖g.subAverage.toScalarL2‖) + |af - ag| * s := by
              rw [hafc, hagc]; ring
    refine hsum.trans ?_
    calc (‖f.subAverage.toScalarL2‖ + ‖g.subAverage.toScalarL2‖) + |af - ag| * s
        ≤ (C₁ * L * Gf + C₁ * L * Gg) + (C₁ + C₂) * L * (Gf + Gg) :=
          add_le_add (add_le_add S1 S2) hgap
      _ = (2 * C₁ + C₂) * L * (Gf + Gg) := by ring
  -- F2: control of the constant `c`.
  have hF2 : ‖(H1Function.const (U := U) c).toScalarL2‖ ≤
      ‖(f.addConst (-c)).toScalarL2‖ + ‖(g.addConst (-c)).toScalarL2‖ :=
    matchedPair_zeroSet z f g c hfm hgm hzero
  -- Reconstruct `f`, `g` from centered parts.
  have hf_split : ‖f.toScalarL2‖ ≤
      ‖(f.addConst (-c)).toScalarL2‖ + ‖(H1Function.const (U := U) c).toScalarL2‖ := by
    have heq : f.toScalarL2 =
        (f.addConst (-c)).toScalarL2 + (H1Function.const (U := U) c).toScalarL2 := by
      rw [← H1Function.toScalarL2_add]
      apply toScalarL2_congr
      funext x
      simp only [H1Function.add_toFun, H1Function.addConst_apply, H1Function.const_apply]
      ring
    rw [heq]; exact norm_add_le _ _
  have hg_split : ‖g.toScalarL2‖ ≤
      ‖(g.addConst (-c)).toScalarL2‖ + ‖(H1Function.const (U := U) c).toScalarL2‖ := by
    have heq : g.toScalarL2 =
        (g.addConst (-c)).toScalarL2 + (H1Function.const (U := U) c).toScalarL2 := by
      rw [← H1Function.toScalarL2_add]
      apply toScalarL2_congr
      funext x
      simp only [H1Function.add_toFun, H1Function.addConst_apply, H1Function.const_apply]
      ring
    rw [heq]; exact norm_add_le _ _
  -- Assemble.
  set Nfc := ‖(f.addConst (-c)).toScalarL2‖ with hNfcdef
  set Ngc := ‖(g.addConst (-c)).toScalarL2‖ with hNgcdef
  set Nc := ‖(H1Function.const (U := U) c).toScalarL2‖ with hNcdef
  have hfinal : ‖f.toScalarL2‖ + ‖g.toScalarL2‖ ≤ 3 * (Nfc + Ngc) := by
    calc ‖f.toScalarL2‖ + ‖g.toScalarL2‖
        ≤ (Nfc + Nc) + (Ngc + Nc) := add_le_add hf_split hg_split
      _ = (Nfc + Ngc) + 2 * Nc := by ring
      _ ≤ (Nfc + Ngc) + 2 * (Nfc + Ngc) := by linarith [hF2]
      _ = 3 * (Nfc + Ngc) := by ring
  refine hfinal.trans ?_
  calc 3 * (Nfc + Ngc) ≤ 3 * ((2 * C₁ + C₂) * L * (Gf + Gg)) :=
        mul_le_mul_of_nonneg_left hcentered (by norm_num)
    _ = matchedPairPoincareConst d * L * (Gf + Gg) := by
        rw [matchedPairPoincareConst, hC1def, hC2def]; ring

end

end Homogenization
