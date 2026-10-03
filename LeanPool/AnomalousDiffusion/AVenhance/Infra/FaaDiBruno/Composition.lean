/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Resummation
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Sharp composition bounds

The analytic composition estimate is proved from the ordered-finpartition
Faà di Bruno formula, keeping the paper's coordinate seminorms and constants.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open MeasureTheory
open Homogenization

/-- Use Lebesgue measure on real time in the integral estimates. -/
local instance realMeasureSpace : MeasureSpace ℝ := Real.measureSpace

/-- The map `g` viewed as an endomorphism of the `ℓ¹` copy of `Vec d`. -/
def liftVecOneEndo {d : ℕ} (g : Vec d → Vec d) : VecOne d → VecOne d :=
  (vecOneEquiv d).symm ∘ liftVecOne g

@[simp] theorem liftVecOneEndo_apply {d : ℕ} (g : Vec d → Vec d) (x : VecOne d) :
    liftVecOneEndo g x = (vecOneEquiv d).symm (g ((vecOneEquiv d) x)) := rfl

theorem liftVecOne_comp_liftVecOneEndo {d : ℕ} (h : Vec d → ℝ)
    (g : Vec d → Vec d) :
    liftVecOne (h ∘ g) = liftVecOne h ∘ liftVecOneEndo g := by
  funext x
  simp [liftVecOne, liftVecOneEndo]

theorem contDiff_liftVecOneEndo {d m : ℕ} (g : Vec d → Vec d)
    (hg : ContDiff ℝ m g) : ContDiff ℝ m (liftVecOneEndo g) := by
  let L : Vec d →L[ℝ] VecOne d := (vecOneEquiv d).symm.toContinuousLinearMap
  have hg' : ContDiff ℝ m (liftVecOne g) := contDiff_liftVecOne hg
  simpa [liftVecOneEndo, liftVecOne, L] using
    (L.contDiff.comp hg')

theorem Composition.compositionCoordinateTupleNonempty (d n : ℕ) [Nonempty (Fin d)] :
    (Finset.univ : Finset (Fin n → Fin d)).Nonempty :=
  ⟨fun _ ↦ Classical.choice ‹Nonempty (Fin d)›, Finset.mem_univ _⟩

theorem Composition.operatorDerivativeF_ae_le_derivativeSup
    {d n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F) :
    ∀ᵐ x ∂vecVolume d,
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
  let μ := vecVolume d
  have hcoord : ∀ᵐ x ∂μ, ∀ I : Fin n → Fin d,
      ‖orderedPartial n f x I‖ₑ ≤ derivativeSup n f := by
    apply ae_all_iff.2
    intro I
    have hI : partialSup n f I ≤ derivativeSup n f := le_iSup_of_le I le_rfl
    have hae : ∀ᵐ x ∂μ,
        ‖orderedPartial n f x I‖ₑ ≤ partialSup n f I := by
      simpa [partialSup, eLpNormEssSup_eq_essSup_enorm] using
        (ae_le_essSup
          (f := fun x : Vec d ↦ ‖orderedPartial n f x I‖ₑ) (μ := μ))
    exact hae.mono fun x hx ↦ hx.trans hI
  have hOp : ∀ᵐ x ∂μ,
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
    filter_upwards [hcoord] with x hx
    by_cases htop : derivativeSup n f = ⊤
    · simp [htop]
    · let T := iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
      have hcoordReal : ∀ I : Fin n → Fin d,
          ‖T (fun j ↦ coordinateVectorOne d (I j))‖ ≤ (derivativeSup n f).toReal := by
        intro I
        have hbound : ENNReal.ofReal
            ‖orderedPartial n f x I‖ ≤ derivativeSup n f := by
          simpa [Real.enorm_eq_ofReal_abs] using hx I
        rw [ENNReal.ofReal_le_iff_le_toReal htop] at hbound
        simpa [T, orderedPartial] using hbound
      have hsup : coordinateEvaluationSup T ≤ (derivativeSup n f).toReal := by
        unfold coordinateEvaluationSup
        refine Finset.sup'_le (Composition.compositionCoordinateTupleNonempty d n) _ ?_
        intro I hI
        exact hcoordReal I
      have hop := norm_continuousMultilinearMap_le_coordinateEvaluationSup T
      have hopen : ENNReal.ofReal ‖T‖ ≤ derivativeSup n f := by
        rw [ENNReal.ofReal_le_iff_le_toReal htop]
        exact hop.trans hsup
      simpa [T] using hopen
  simpa [μ] using hOp

theorem Composition.operatorDerivativeF_pointwise_le_derivativeSup
    {d n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F)
    (hf : ContDiff ℝ n f) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
  let μ := vecVolume d
  have hOpenPos : μ.IsOpenPosMeasure := by
    change (Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))).IsOpenPosMeasure
    infer_instance
  have hae := Composition.operatorDerivativeF_ae_le_derivativeSup (n := n) f
  have hderivCont : Continuous fun y : VecOne d ↦
      iteratedFDeriv ℝ n (liftVecOne f) y :=
    (contDiff_liftVecOne hf).continuous_iteratedFDeriv le_rfl
  have hpointCont : Continuous fun y : Vec d ↦
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 y)‖ₑ := by
    exact (hderivCont.comp (by fun_prop)).enorm
  have hclosed : IsClosed {y : Vec d |
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 y)‖ₑ ≤ derivativeSup n f} :=
    isClosed_le hpointCont continuous_const
  have hset : {y : Vec d |
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 y)‖ₑ ≤ derivativeSup n f} ∈ ae μ := hae
  have hsupport := μ.support_subset_of_isClosed hclosed hset
  have hx : x ∈ μ.support := by
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, hxV⟩
    have hVne : μ V ≠ 0 := hOpenPos.open_pos V hVopen ⟨x, hxV⟩
    exact lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hVne) (measure_mono hVU)
  exact hsupport hx

theorem Composition.vecOneEquiv_symm_opNorm_le_card {d : ℕ} :
    ‖(vecOneEquiv d).symm.toContinuousLinearMap‖ ≤ (d : ℝ) := by
  let L : Vec d →L[ℝ] VecOne d := (vecOneEquiv d).symm.toContinuousLinearMap
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun x ↦ ?_
  calc
    ‖L x‖ = ∑ i : Fin d, ‖(L x) i‖ := by rw [PiLp.norm_eq_of_L1]
    _ ≤ ∑ _i : Fin d, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoord : (L x) i = x i := by
        change (WithLp.toLp 1 x : VecOne d) i = x i
        rfl
      rw [hcoord]
      rw [Pi.norm_def]
      change (‖x i‖₊ : ℝ) ≤ _
      exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin d ↦ ‖x j‖₊)
        (Finset.mem_univ i)
    _ = (d : ℝ) * ‖x‖ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Recover the paper's coordinate derivative supremum from its normalized
seminorm, with the exact factorial and radius factors. -/
theorem derivativeSup_le_of_snorm_le {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F)
    {R C : ℝ} (hR : 0 < R)
    (hs : snorm f n R ≤ ENNReal.ofReal C) :
    derivativeSup n f ≤ ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
  let w : ℝ := (n + 1 : ℝ) ^ 2 / n.factorial
  let r : ENNReal := ENNReal.ofReal R
  let a : ENNReal := ENNReal.ofReal w * r⁻¹ ^ n
  have hw : 0 < w := by dsimp [w]; positivity
  have hr0 : r ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hrtop : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hw).ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr
        hrtop))
  have hatop : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hr0))
  have hs' : a * derivativeSup n f ≤ ENNReal.ofReal C := by
    simpa [snorm, w, r, a, mul_assoc] using hs
  have hmul := mul_le_mul_left hs' a⁻¹
  have hleft : a⁻¹ * (a * derivativeSup n f) = derivativeSup n f := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  have hfactor : a⁻¹ * ENNReal.ofReal C = ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
    have hwpos : 0 < w := hw
    have hreal : w⁻¹ * R ^ n * C = C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
      dsimp [w]
      field_simp
    have hpow : (r⁻¹ ^ n)⁻¹ = ENNReal.ofReal (R ^ n) := by
      rw [← ENNReal.inv_pow, inv_inv]
      simp [r, ENNReal.ofReal_pow (le_of_lt hR)]
    have hainv : a⁻¹ = ENNReal.ofReal w⁻¹ * ENNReal.ofReal (R ^ n) := by
      dsimp only [a]
      rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hw).ne')
        (Or.inl ENNReal.ofReal_ne_top)]
      rw [ENNReal.ofReal_inv_of_pos hw, hpow]
    calc
      a⁻¹ * ENNReal.ofReal C =
          ENNReal.ofReal (w⁻¹ * R ^ n) * ENNReal.ofReal C := by rw [hainv]; rw [←
              ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hw))]
      _ = ENNReal.ofReal (w⁻¹ * R ^ n * C) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by rw [hreal]
  have hmul' : a⁻¹ * (a * derivativeSup n f) ≤ a⁻¹ * ENNReal.ofReal C := by
    calc
      _ = a * derivativeSup n f * a⁻¹ := by ac_rfl
      _ ≤ ENNReal.ofReal C * a⁻¹ := hmul
      _ = a⁻¹ * ENNReal.ofReal C := by ac_rfl
  rw [hleft, hfactor] at hmul'
  exact hmul'

theorem Composition.liftVecOneEndo_deriv_norm_le {d m r : ℕ} [Nonempty (Fin d)]
    (g : Vec d → Vec d) (hg : ContDiff ℝ m g) (hr : r ≤ m)
    (x : Vec d) {D : ℝ}
    (hD : derivativeSup r g ≤ ENNReal.ofReal D)
    (hDnonneg : 0 ≤ D)
    (hDtop : derivativeSup r g ≠ ⊤) :
    ‖iteratedFDeriv ℝ r (liftVecOneEndo g) (WithLp.toLp 1 x)‖ ≤
      (d : ℝ) * D := by
  let L : Vec d →L[ℝ] VecOne d := (vecOneEquiv d).symm.toContinuousLinearMap
  let T := iteratedFDeriv ℝ r (liftVecOne g) (WithLp.toLp 1 x)
  have hT := Composition.operatorDerivativeF_pointwise_le_derivativeSup (n := r) g
    (hg.of_le (by exact_mod_cast hr)) x
  have hTreal : ‖T‖ ≤ D := by
    have hT' : ENNReal.ofReal ‖T‖ ≤ derivativeSup r g := by
      simpa [T, Real.enorm_eq_ofReal_abs] using hT
    have hToReal := (ENNReal.ofReal_le_iff_le_toReal hDtop).mp hT'
    have hDreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
    rw [ENNReal.toReal_ofReal hDnonneg] at hDreal
    exact hToReal.trans hDreal
  have hcomp := L.iteratedFDeriv_comp_left (f := liftVecOne g)
    (contDiff_liftVecOne hg).contDiffAt (i := r) (by exact_mod_cast hr)
      (x := WithLp.toLp 1 x)
  have hcomp' :
      iteratedFDeriv ℝ r (liftVecOneEndo g) (WithLp.toLp 1 x) =
        L.compContinuousMultilinearMap T := by
    simpa [liftVecOneEndo, Function.comp_def, L, T] using hcomp
  calc
    ‖iteratedFDeriv ℝ r (liftVecOneEndo g) (WithLp.toLp 1 x)‖ =
        ‖L.compContinuousMultilinearMap T‖ := by rw [hcomp']
    _ ≤ ‖L‖ * ‖T‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le L T
    _ ≤ (d : ℝ) * D := by
      exact mul_le_mul (by simpa [L] using Composition.vecOneEquiv_symm_opNorm_le_card)
        hTreal (norm_nonneg _) (by positivity)

/-- The paper's derivative seminorm controls the full iterated derivative on
the `ℓ¹` coordinate realization, pointwise and with its exact factorial and
radius normalization. -/
theorem compositionDerivative_norm_le_of_snorm_le
    {d m r : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (hf : ContDiff ℝ m f) (hr : r ≤ m)
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : snorm f r R ≤ ENNReal.ofReal C) (x : Vec d) :
    ‖iteratedFDeriv ℝ r (liftVecOne f) (WithLp.toLp 1 x)‖ ≤
      C * r.factorial * R ^ r / (r + 1 : ℝ) ^ 2 := by
  let D : ℝ := C * r.factorial * R ^ r / (r + 1 : ℝ) ^ 2
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hsup := derivativeSup_le_of_snorm_le f hR hs
  have htop : derivativeSup r f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsup
  have hpoint := Composition.operatorDerivativeF_pointwise_le_derivativeSup (n := r) f
    (hf.of_le (by exact_mod_cast hr)) x
  have hpoint' : ENNReal.ofReal
      ‖iteratedFDeriv ℝ r (liftVecOne f) (WithLp.toLp 1 x)‖ ≤ derivativeSup r f := by
    simpa [Real.enorm_eq_ofReal_abs] using hpoint
  have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hpoint'
  have hsupReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
  rw [ENNReal.toReal_ofReal hDnonneg] at hsupReal
  simpa [D] using hreal.trans hsupReal

/-- Pointwise coordinate partials of any order obey the factorial and radius
bound supplied by the paper's seminorm. This is the source-side estimate used
when differentiating the transport equation. -/
theorem orderedPartial_norm_le_of_snorm_le
    {d m n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (hf : ContDiff ℝ m f) (hn : n ≤ m)
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : snorm f n R ≤ ENNReal.ofReal C)
    (x : Vec d) (I : Fin n → Fin d) :
    ‖orderedPartial n f x I‖ ≤
      C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
  calc
    ‖orderedPartial n f x I‖ ≤
        ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ := by
      calc
        _ ≤ ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ *
            ∏ j, ‖coordinateVectorOne d (I j)‖ :=
          (iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)).le_opNorm _
        _ = _ := by simp [coordinateVectorOne_norm]
    _ ≤ C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 :=
      compositionDerivative_norm_le_of_snorm_le f hf hn hR hC hs x

/-- The paper seminorm bound at order one controls the derivative on the
original supremum-norm coordinate space. The factor `d` is the norm cost of
passing from the paper's coordinate `ℓ¹` realization back to `Vec d`. -/
theorem fderiv_norm_le_of_snorm_one_le
    {d : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (hf : ContDiff ℝ 1 f)
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hs : snorm f 1 R ≤ ENNReal.ofReal C) (x : Vec d) :
    ‖fderiv ℝ f x‖ ≤ (d : ℝ) * C * R / 4 := by
  let L : Vec d →L[ℝ] VecOne d := (vecOneEquiv d).symm.toContinuousLinearMap
  let F₁ : VecOne d → F := liftVecOne f
  have hF₁ : ContDiff ℝ 1 F₁ := contDiff_liftVecOne hf
  have hF₁deriv : ‖fderiv ℝ F₁ (L x)‖ ≤ C * R / 4 := by
    have hbound := compositionDerivative_norm_le_of_snorm_le
      (r := 1) f hf (by norm_num) hR hC hs x
    rw [norm_iteratedFDeriv_one] at hbound
    simpa [F₁, L, vecOneEquiv, Nat.factorial_one,
      PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv] using hbound
      |>.trans_eq (by norm_num)
  have hcomp : fderiv ℝ f x = (fderiv ℝ F₁ (L x)).comp L := by
    have hbase : liftVecOne f ∘ L = f := by
      funext y
      simp [L, liftVecOne, vecOneEquiv, PiLp.coe_symm_continuousLinearEquiv,
        PiLp.coe_continuousLinearEquiv]
    have hcomp := (hF₁.differentiable (by norm_num) (L x)).hasFDerivAt.comp x
      L.hasFDerivAt
    rw [hbase] at hcomp
    exact hcomp.fderiv
  calc
    ‖fderiv ℝ f x‖ = ‖(fderiv ℝ F₁ (L x)).comp L‖ := by rw [hcomp]
    _ ≤ ‖fderiv ℝ F₁ (L x)‖ * ‖L‖ :=
      (fderiv ℝ F₁ (L x)).opNorm_comp_le L
    _ ≤ (C * R / 4) * (d : ℝ) := by
      exact mul_le_mul hF₁deriv
        (by simpa [L] using Composition.vecOneEquiv_symm_opNorm_le_card)
        (norm_nonneg _) (by positivity)
    _ = (d : ℝ) * C * R / 4 := by ring

theorem Composition.one_add_sum_le_prod_add_one {α : Type*} (s : Finset α)
    (f : α → ℕ) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (f i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hlocal : 1 + f a + (∑ i ∈ s, f i) ≤
          (f a + 1) * (1 + ∑ i ∈ s, f i) := by
        nlinarith [Nat.zero_le (f a * (∑ i ∈ s, f i))]
      simpa [Nat.add_assoc] using hlocal.trans (Nat.mul_le_mul_left (f a + 1) ih)

theorem Composition.composition_partSize_sum {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  classical
  calc
    ∑ i : Fin c.length, c.partSize i =
        Fintype.card (Σ i : Fin c.length, Fin (c.partSize i)) := by simp [Fintype.card_sigma]
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin n

theorem Composition.orderedFinpartition_shiftFactor {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) :
    (n + 1 : ℝ) ^ 2 ≤ (c.length + 1 : ℝ) ^ 2 *
      ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
  have hsum := Composition.composition_partSize_sum c
  have hprodNat : n + 1 ≤ ∏ i : Fin c.length, (c.partSize i + 1) := by
    have h := Composition.one_add_sum_le_prod_add_one Finset.univ c.partSize
    rw [hsum] at h
    omega
  have hprodReal : (n + 1 : ℝ) ≤
      (c.length + 1 : ℝ) * ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by
    have hprodReal' : (n + 1 : ℝ) ≤ ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by
      exact_mod_cast hprodNat
    calc
      _ ≤ 1 * ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by simpa using hprodReal'
      _ ≤ (c.length + 1 : ℝ) * ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (by norm_num) (by positivity)
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ (n + 1 : ℝ))
      (by positivity : 0 ≤ (c.length + 1 : ℝ) *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ))).2 hprodReal
  calc
    (n + 1 : ℝ) ^ 2 ≤
        ((c.length + 1 : ℝ) * ∏ i : Fin c.length,
          (c.partSize i + 1 : ℝ)) ^ 2 := hsquare
    _ = (c.length + 1 : ℝ) ^ 2 *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
      rw [mul_pow, Finset.prod_pow]

theorem snorm_le_of_derivativeSup_le {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) {R C : ℝ} (hR : 0 < R)
    (hD : derivativeSup n f ≤ ENNReal.ofReal
      (C * R ^ n * n.factorial / (n + 1 : ℝ) ^ 2)) :
    snorm f n R ≤ ENNReal.ofReal C := by
  let w : ℝ := (n + 1 : ℝ) ^ 2 / n.factorial
  let A : ℝ := C * R ^ n * n.factorial / (n + 1 : ℝ) ^ 2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hpowNonneg : 0 ≤ (R⁻¹) ^ n := by positivity
  have hreal : w * (R⁻¹) ^ n * A = C := by
    dsimp [w, A]
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp
    have hpow : (1 / R) ^ n * R ^ n = 1 := by
      rw [one_div, ← mul_pow, inv_mul_cancel₀ hRne, one_pow]
    calc
      _ = C * ((1 / R) ^ n * R ^ n) := by ring
      _ = C := by rw [hpow, mul_one]
  have hscale : ENNReal.ofReal w * (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal A =
      ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_inv_of_pos hR, ← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul (by positivity)]
    rw [hreal]
  calc
    snorm f n R = ENNReal.ofReal w * (ENNReal.ofReal R)⁻¹ ^ n * derivativeSup n f := by
      simp [snorm, w, mul_assoc]
    _ ≤ ENNReal.ofReal w * (ENNReal.ofReal R)⁻¹ ^ n * ENNReal.ofReal A :=
      mul_le_mul_right hD _
    _ = ENNReal.ofReal C := hscale

theorem Composition.orderedFinpartition_innerCoefficientProduct {n : ℕ}
    (c : OrderedFinpartition n) (D R : ℝ) :
    ∏ i : Fin c.length,
        (D * (c.partSize i).factorial * R ^ c.partSize i /
          (c.partSize i + 1 : ℝ) ^ 2) =
      D ^ c.length * (orderedPartitionFactorialProduct c : ℝ) * R ^ n /
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
  rw [Finset.prod_div_distrib]
  have hnum :
      ∏ i : Fin c.length, (D * (c.partSize i).factorial * R ^ c.partSize i) =
        D ^ c.length * (orderedPartitionFactorialProduct c : ℝ) * R ^ n := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hD : (∏ _i : Fin c.length, D) = D ^ c.length := by simp
    have hfact : (∏ i : Fin c.length, (c.partSize i).factorial : ℝ) =
        (orderedPartitionFactorialProduct c : ℝ) := by
      simp [orderedPartitionFactorialProduct, Nat.cast_prod]
    have hR : (∏ i : Fin c.length, R ^ c.partSize i) = R ^ n := by
      rw [Finset.prod_pow_eq_pow_sum, Composition.composition_partSize_sum]
    rw [hD, hfact, hR]
  rw [hnum]

/-- Proposition 10528 with the paper's sharp constant and radius. -/
theorem compositionEstimate10528 {d m : ℕ} [Nonempty (Fin d)]
    (h : Vec d → ℝ) (g : Vec d → Vec d)
    (hh : ContDiff ℝ m h) (hg : ContDiff ℝ m g)
    {C_h C_g R_h R_g : ℝ}
    (hCh : 0 < C_h) (hCg : 0 < C_g) (hRh : 0 < R_h) (hRg : 0 < R_g)
    (hH : ∀ j, j ≤ m → snorm h j R_h ≤ ENNReal.ofReal C_h)
    (hG : ∀ j, 1 ≤ j → j ≤ m → snorm g j R_g ≤ ENNReal.ofReal C_g) :
    ∀ n, n ≤ m →
      snorm (h ∘ g) n (R_g * (1 + (d : ℝ) * C_g * R_h)) ≤ ENNReal.ofReal C_h := by
  let X : ℝ := (d : ℝ) * C_g * R_h
  let R : ℝ := R_g * (1 + X)
  have hdc : (0 : ℝ) < (d : ℝ) := by
    have hc : 0 < Fintype.card (Fin d) := Fintype.card_pos_iff.mpr ‹Nonempty (Fin d)›
    simpa using hc
  have hX : 0 < X := by dsimp [X]; exact mul_pos (mul_pos hdc hCg) hRh
  have hR : 0 < R := by dsimp [R]; positivity
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    have hpoint (x : Vec d) : ‖h (g x)‖ ≤ C_h := by
      have hderiv := compositionDerivative_norm_le_of_snorm_le (r := 0) h hh
        (by omega) hRh (le_of_lt hCh) (hH 0 (by omega)) (g x)
      simpa [norm_iteratedFDeriv_zero, liftVecOne, vecOneEquiv,
        PiLp.coe_continuousLinearEquiv] using hderiv
    have hOp : operatorDerivativeSup 0 (h ∘ g) ≤ ENNReal.ofReal C_h := by
      unfold operatorDerivativeSup
      rw [eLpNormEssSup_eq_essSup_enorm]
      apply essSup_le_of_ae_le (ENNReal.ofReal C_h)
      filter_upwards with x
      have h := ENNReal.ofReal_le_ofReal (hpoint x)
      simpa [Real.enorm_eq_ofReal_abs, norm_iteratedFDeriv_zero, liftVecOne,
        vecOneEquiv, PiLp.coe_continuousLinearEquiv] using h
    have hderiv := (derivativeSup_le_operatorDerivativeSup (h ∘ g)).trans hOp
    apply snorm_le_of_derivativeSup_le (h ∘ g) hR
    simpa using hderiv
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let common : ℝ := C_h * R_g ^ n / (n + 1 : ℝ) ^ 2
    let B : ℝ := C_h * R_g ^ n * X * (1 + X) ^ (n - 1) * n.factorial /
      (n + 1 : ℝ) ^ 2
    let H : VecOne d → ℝ := liftVecOne h
    let G : VecOne d → VecOne d := liftVecOneEndo g
    have hHn : ContDiff ℝ n H := (contDiff_liftVecOne hh).of_le (by exact_mod_cast hn)
    have hGn : ContDiff ℝ n G := (contDiff_liftVecOneEndo g hg).of_le (by exact_mod_cast hn)
    have hRpoint (x : Vec d) :
        G (WithLp.toLp 1 x) = WithLp.toLp 1 (g x) := by
      simp [G, liftVecOneEndo, liftVecOne, vecOneEquiv,
        PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv]
    have hcomp : liftVecOne (h ∘ g) = H ∘ G := by
      simpa [H, G] using liftVecOne_comp_liftVecOneEndo h g
    have hpt (x : Vec d) :
        ‖iteratedFDeriv ℝ n (liftVecOne (h ∘ g)) (WithLp.toLp 1 x)‖ ≤ B := by
      let y : VecOne d := WithLp.toLp 1 x
      have hFaa := multivariateFaaDiBruno
        (hHn.contDiffAt (x := G y)) (hGn.contDiffAt (x := y))
      have hOuter (s : ℕ) (hs : s ≤ n) :
          ‖ftaylorSeries ℝ H (G y) s‖ ≤
            C_h * s.factorial * R_h ^ s / (s + 1 : ℝ) ^ 2 := by
        have hsM : s ≤ m := hs.trans hn
        have hbound := compositionDerivative_norm_le_of_snorm_le h hh hsM hRh (le_of_lt hCh)
          (hH s hsM) (g x)
        simpa [H, y, hRpoint x, ftaylorSeries] using hbound
      have hInner (c : OrderedFinpartition n) (i : Fin c.length) :
          ‖ftaylorSeries ℝ G y (c.partSize i)‖ ≤
            (d : ℝ) * (C_g * (c.partSize i).factorial *
              R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2) := by
        have hrM : c.partSize i ≤ m := (c.partSize_le i).trans hn
        have hri : 1 ≤ c.partSize i := Nat.succ_le_iff.mpr (c.partSize_pos i)
        have hSup := derivativeSup_le_of_snorm_le g hRg
          (hG (c.partSize i) hri hrM)
        have hDnonneg : 0 ≤ C_g * (c.partSize i).factorial *
            R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2 := by positivity
        have hDtop := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSup
        have hbound := Composition.liftVecOneEndo_deriv_norm_le g hg hrM x
          hSup hDnonneg hDtop
        simpa [G, y, ftaylorSeries] using hbound
      have hterm (c : OrderedFinpartition n) :
          ‖(ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
              (ftaylorSeries ℝ G y) c‖ ≤
            common * (X ^ c.length * (c.length.factorial : ℝ) *
              (orderedPartitionFactorialProduct c : ℝ)) := by
        have hs : c.length ≤ n := OrderedFinpartition.length_le c
        have houter := hOuter c.length hs
        have hcompNorm := c.norm_compAlongOrderedFinpartition_le
          (ftaylorSeries ℝ H (G y) c.length)
          (fun i ↦ ftaylorSeries ℝ G y (c.partSize i))
        have hbase :
            ‖(ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
                (ftaylorSeries ℝ G y) c‖ ≤
              (C_h * c.length.factorial * R_h ^ c.length /
                  (c.length + 1 : ℝ) ^ 2) *
                ∏ i : Fin c.length,
                  ((d : ℝ) * (C_g * (c.partSize i).factorial *
                    R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2)) := by
            simpa [FormalMultilinearSeries.compAlongOrderedFinpartition] using
            (hcompNorm.trans (mul_le_mul houter
              (Finset.prod_le_prod₀
                (fun i hi ↦ norm_nonneg (ftaylorSeries ℝ G y (c.partSize i)))
                (fun i hi ↦ hInner c i)) (by positivity) (by positivity)))
        have hdenPos : 0 < (c.length + 1 : ℝ) ^ 2 *
            ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by positivity
        have hratio : ((n + 1 : ℝ) ^ 2) /
            ((c.length + 1 : ℝ) ^ 2 *
              ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2) ≤ 1 :=
          (div_le_one₀ hdenPos).2 (Composition.orderedFinpartition_shiftFactor hnpos c)
        have hinnerShape :
            ∏ i : Fin c.length,
                ((d : ℝ) * (C_g * (c.partSize i).factorial *
                  R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2)) =
              ∏ i : Fin c.length,
                (((d : ℝ) * C_g) * (c.partSize i).factorial *
                  R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2) := by
          apply Finset.prod_congr rfl
          intro i hi
          ring
        have hcoeff :
            (C_h * c.length.factorial * R_h ^ c.length /
                (c.length + 1 : ℝ) ^ 2) *
              ∏ i : Fin c.length,
                ((d : ℝ) * (C_g * (c.partSize i).factorial *
                  R_g ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2)) =
            common * (X ^ c.length * (c.length.factorial : ℝ) *
              (orderedPartitionFactorialProduct c : ℝ)) *
              (((n + 1 : ℝ) ^ 2) /
                ((c.length + 1 : ℝ) ^ 2 *
                  ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2)) := by
          rw [hinnerShape,
            Composition.orderedFinpartition_innerCoefficientProduct c ((d : ℝ) * C_g) R_g]
          dsimp [common, X]
          field_simp [ne_of_gt hdenPos, ne_of_gt (by positivity : 0 < (n + 1 : ℝ) ^ 2)]
          ring
        calc
          _ ≤ _ := hbase
          _ = common * (X ^ c.length * (c.length.factorial : ℝ) *
              (orderedPartitionFactorialProduct c : ℝ)) *
              (((n + 1 : ℝ) ^ 2) /
                ((c.length + 1 : ℝ) ^ 2 *
                  ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2)) := hcoeff
          _ ≤ common * (X ^ c.length * (c.length.factorial : ℝ) *
              (orderedPartitionFactorialProduct c : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = common * (X ^ c.length * (c.length.factorial : ℝ) *
              (orderedPartitionFactorialProduct c : ℝ)) := by ring
      rw [hcomp, hFaa]
      calc
        ‖∑ c : OrderedFinpartition n,
            (ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
              (ftaylorSeries ℝ G y) c‖ ≤
            ∑ c : OrderedFinpartition n,
              ‖(ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
                (ftaylorSeries ℝ G y) c‖ := norm_sum_le _ _
        _ ≤ ∑ c : OrderedFinpartition n,
              common * (X ^ c.length * (c.length.factorial : ℝ) *
                (orderedPartitionFactorialProduct c : ℝ)) :=
            Finset.sum_le_sum fun c hc ↦ hterm c
        _ = common * ∑ c : OrderedFinpartition n,
              X ^ c.length * (c.length.factorial : ℝ) *
                (orderedPartitionFactorialProduct c : ℝ) := by rw [Finset.mul_sum]
        _ = B := by
          rw [orderedFinpartitionFactorialResummation10469 hnpos X]
          dsimp [B, common]
          ring
    have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
    have hOp : operatorDerivativeSup n (h ∘ g) ≤ ENNReal.ofReal B := by
      unfold operatorDerivativeSup
      rw [eLpNormEssSup_eq_essSup_enorm]
      apply essSup_le_of_ae_le (ENNReal.ofReal B)
      filter_upwards with x
      have h := ENNReal.ofReal_le_ofReal (hpt x)
      simpa [Real.enorm_eq_ofReal_abs] using h
    have hderiv := (derivativeSup_le_operatorDerivativeSup (h ∘ g)).trans hOp
    let K : ℝ := C_h * R_g ^ n * n.factorial / (n + 1 : ℝ) ^ 2
    have hpow : X * (1 + X) ^ (n - 1) ≤ (1 + X) ^ n := by
      have hXle : X ≤ 1 + X := by linarith
      calc
        X * (1 + X) ^ (n - 1) ≤ (1 + X) * (1 + X) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right hXle (by positivity)
        _ = (1 + X) ^ ((n - 1) + 1) := by rw [pow_succ]; ring
        _ = (1 + X) ^ n := by rw [Nat.sub_add_cancel (by omega)]
    have hB_eq : B = K * (X * (1 + X) ^ (n - 1)) := by dsimp [B, K]; ring
    have hKtarget : K * (1 + X) ^ n =
        C_h * R ^ n * n.factorial / (n + 1 : ℝ) ^ 2 := by
      dsimp [K, R]
      rw [mul_pow]
      ring
    have hB_le : B ≤ C_h * R ^ n * n.factorial / (n + 1 : ℝ) ^ 2 := by
      rw [hB_eq, ← hKtarget]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hderiv' := hderiv.trans (ENNReal.ofReal_le_ofReal hB_le)
    exact snorm_le_of_derivativeSup_le (h ∘ g) hR hderiv'

end AVenhance.FaaDiBruno

end
