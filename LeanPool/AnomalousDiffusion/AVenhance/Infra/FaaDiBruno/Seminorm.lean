/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Appendix B derivative seminorms

The coordinate derivatives of order `n` are represented by evaluating the
iterated Fréchet derivative on coordinate basis vectors. An ordered list of
coordinate directions presents a multi-index, and the API groups these lists
by their multiplicities. For smooth functions, identifying all orderings of
the same multi-index uses the symmetry of iterated derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace AVenhance.FaaDiBruno

open Homogenization

/-- The `ℓ¹`-normed version of the coordinate space.  It is used internally
to identify the operator norm of a multilinear derivative with the supremum
of its coordinate partials. -/
abbrev VecOne (d : ℕ) := PiLp (1 : ENNReal) (fun _ : Fin d ↦ ℝ)

/-- The canonical linear homeomorphism from the `ℓ¹` copy to `Vec d`. -/
noncomputable def vecOneEquiv (d : ℕ) : VecOne d ≃L[ℝ] Vec d :=
  PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin d ↦ ℝ)

/-- The function `f` viewed on the `ℓ¹` copy of the coordinate space. -/
def liftVecOne {d : ℕ} {F : Type*} (f : Vec d → F) : VecOne d → F := f ∘ vecOneEquiv d

@[simp] theorem liftVecOne_toLp {d : ℕ} {F : Type*} (f : Vec d → F) (x : Vec d) :
    liftVecOne f (WithLp.toLp 1 x) = f x := by
  simp [liftVecOne, vecOneEquiv, PiLp.coe_continuousLinearEquiv]

/-- Product Lebesgue measure on the coordinate realization `Vec d`. -/
noncomputable def vecVolume (d : ℕ) : Measure (Vec d) := by
  letI : MeasureSpace ℝ := Real.measureSpace
  exact Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))

/-- The coordinate basis vector associated to `i : Fin d`. -/
def coordinateVector (d : ℕ) (i : Fin d) : Vec d := Pi.single i 1

/-- The coordinate vector in the `ℓ¹` copy. -/
def coordinateVectorOne (d : ℕ) (i : Fin d) : VecOne d :=
  PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i 1

@[simp] theorem coordinateVectorOne_apply {d : ℕ} (i j : Fin d) :
    coordinateVectorOne d i j = if j = i then 1 else 0 := by
  simp [coordinateVectorOne]

theorem coordinateVectorOne_norm {d : ℕ} (i : Fin d) :
    ‖coordinateVectorOne d i‖ = 1 := by
  change ‖PiLp.single (p := 1) (β := fun _ : Fin d ↦ ℝ) i (1 : ℝ)‖ = 1
  simp

/-- On the `ℓ¹` copy of `Vec d`, the operator norm of a multilinear map is
bounded by its largest value on tuples of coordinate vectors. -/
theorem Seminorm.coordinateTupleNonempty (d n : ℕ) [Nonempty (Fin d)] :
    (Finset.univ : Finset (Fin n → Fin d)).Nonempty :=
  ⟨fun _ ↦ Classical.choice ‹Nonempty (Fin d)›, Finset.mem_univ _⟩

/-- Maximum norm of a multilinear map evaluated on coordinate basis tuples. -/
def coordinateEvaluationSup {d n : ℕ} [Nonempty (Fin d)] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) : ℝ :=
  Finset.univ.sup' (Seminorm.coordinateTupleNonempty d n)
    (fun I ↦ ‖T (fun j ↦ coordinateVectorOne d (I j))‖)

theorem norm_continuousMultilinearMap_le_coordinateEvaluationSup
    {d n : ℕ} [Nonempty (Fin d)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ VecOne d) F) :
    ‖T‖ ≤ coordinateEvaluationSup T := by
  induction n with
  | zero =>
      classical
      refine ContinuousMultilinearMap.opNorm_le_bound
        (M := coordinateEvaluationSup T) ?_ fun m ↦ ?_
      · unfold coordinateEvaluationSup
        let I : Fin 0 → Fin d := fun j ↦ Fin.elim0 j
        exact le_trans (norm_nonneg _) <| Finset.le_sup'
          (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖) (Finset.mem_univ I)
      let I : Fin 0 → Fin d := fun j ↦ Fin.elim0 j
      have hm : m = fun j ↦ coordinateVectorOne d (I j) := by
        funext j
        exact Fin.elim0 j
      rw [hm]
      have hI : ‖T (fun j ↦ coordinateVectorOne d (I j))‖ ≤ coordinateEvaluationSup T :=
        Finset.le_sup' (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
          (Finset.mem_univ I)
      simpa using hI
  | succ n ih =>
      classical
      let C := coordinateEvaluationSup T
      have hC : 0 ≤ C := by
        unfold C coordinateEvaluationSup
        let I₀ : Fin (n + 1) → Fin d := fun _ ↦ Classical.choice ‹Nonempty (Fin d)›
        exact le_trans (norm_nonneg _) <| Finset.le_sup'
          (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
          (Finset.mem_univ I₀)
      have hBasis (i : Fin d) :
          ‖T.curryLeft (coordinateVectorOne d i)‖ ≤ C := by
        calc
          ‖T.curryLeft (coordinateVectorOne d i)‖ ≤
            coordinateEvaluationSup (T.curryLeft (coordinateVectorOne d i)) := ih _
          _ ≤ C := by
            unfold C coordinateEvaluationSup
            refine Finset.sup'_le (Seminorm.coordinateTupleNonempty d n)
              (fun I ↦ ‖T.curryLeft (coordinateVectorOne d i)
                (fun j ↦ coordinateVectorOne d (I j))‖) fun I hI ↦ ?_
            have htuple :
                (fun j : Fin (n + 1) ↦
                  coordinateVectorOne d (Fin.cons (α := fun _ : Fin (n + 1) ↦ Fin d) i I j)) =
                  Fin.cons (coordinateVectorOne d i)
                    (fun j ↦ coordinateVectorOne d (I j)) := by
              funext j
              refine Fin.cases ?_ ?_ j
              · simp
              · intro j
                simp
            rw [ContinuousMultilinearMap.curryLeft_apply, ← htuple]
            exact le_rfl.trans <|
              Finset.le_sup' (fun J ↦ ‖T (fun j ↦ coordinateVectorOne d (J j))‖)
                (Finset.mem_univ (Fin.cons i I))
      have hrepr (x : VecOne d) :
          x = ∑ i : Fin d, x i • coordinateVectorOne d i := by
        ext j
        simp [coordinateVectorOne_apply]
      have hmap (x : VecOne d) :
          ‖T.curryLeft x‖ ≤ C * ‖x‖ := by
        calc
          ‖T.curryLeft x‖ =
              ‖T.curryLeft (∑ i : Fin d, x i • coordinateVectorOne d i)‖ := by
                exact congrArg (fun z ↦ ‖T.curryLeft z‖) (hrepr x)
          _ = ‖∑ i : Fin d, x i • T.curryLeft (coordinateVectorOne d i)‖ := by
                congr 1
                simp
          _ ≤
              ∑ i : Fin d, ‖x i • T.curryLeft (coordinateVectorOne d i)‖ := norm_sum_le _ _
          _ ≤ ∑ i : Fin d, ‖x i‖ * C := by
            refine Finset.sum_le_sum fun i hi ↦ ?_
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hBasis i) (norm_nonneg _)
          _ = C * ‖x‖ := by
            calc
              _ = (∑ i : Fin d, ‖x i‖) * C := by rw [← Finset.sum_mul]
              _ = C * ‖x‖ := by rw [PiLp.norm_eq_of_L1]; ring
      calc
        ‖T‖ = ‖T.curryLeft‖ := T.curryLeft_norm.symm
        _ ≤ C := T.curryLeft.opNorm_le_bound hC hmap
        _ = coordinateEvaluationSup T := rfl

/-- The order-`n` coordinate partial of `f`, with the coordinate directions
listed in `I`. This is an iterated Fréchet derivative evaluated on basis
vectors. -/
def orderedPartial {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) (x : Vec d) (I : Fin n → Fin d) : F :=
  iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)
    (fun j ↦ coordinateVectorOne d (I j))

/-- The global supremum of the derivative in the multi-index represented by
`I`. For continuous derivatives this is the pointwise representative of the
paper's `L∞` norm. -/
def partialSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) (I : Fin n → Fin d) : ENNReal :=
  letI : MeasureSpace ℝ := Real.measureSpace
  eLpNormEssSup (fun x ↦ orderedPartial n f x I) (vecVolume d)

/-- The order-`n` derivative `L∞` seminorm. -/
def derivativeSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) : ENNReal :=
  ⨆ I : Fin n → Fin d, partialSup n f I

/-- The essential supremum of the operator norm of the derivative on the
`ℓ¹` copy of the coordinate domain. -/
def operatorDerivativeSup {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) : ENNReal :=
  eLpNormEssSup
    (fun x : Vec d ↦ ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖)
    (vecVolume d)

/-- A coordinate derivative is bounded by the operator norm of the full
multilinear derivative on the `ℓ¹` coordinate space. -/
theorem orderedPartial_norm_le_operatorDerivative
    {d n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (x : Vec d) (I : Fin n → Fin d) :
    ‖orderedPartial n f x I‖ ≤
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ := by
  calc
    ‖orderedPartial n f x I‖ ≤
        ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ *
          ∏ j, ‖coordinateVectorOne d (I j)‖ :=
      (iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)).le_opNorm _
    _ = ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ := by
      simp [coordinateVectorOne_norm]

/-- The coordinate derivative seminorm is bounded by the operator-derivative
essential supremum. -/
theorem derivativeSup_le_operatorDerivativeSup {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F) :
    derivativeSup n f ≤ operatorDerivativeSup n f := by
  unfold derivativeSup operatorDerivativeSup
  refine iSup_le fun I ↦ ?_
  apply eLpNormEssSup_mono_enorm_ae
  filter_upwards with x
  have h := ENNReal.ofReal_le_ofReal (orderedPartial_norm_le_operatorDerivative f x I)
  simpa [Real.enorm_eq_ofReal_abs] using h

theorem operatorDerivative_ae_le_derivativeSup {d n : ℕ} [Nonempty (Fin d)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec d → F) :
    ∀ᵐ x ∂vecVolume d,
      ‖iteratedFDeriv ℝ n (liftVecOne f) (WithLp.toLp 1 x)‖ₑ ≤ derivativeSup n f := by
  let μ := vecVolume d
  have hcoord : ∀ᵐ x ∂μ, ∀ I : Fin n → Fin d,
      ‖orderedPartial n f x I‖ₑ ≤ derivativeSup n f := by
    apply ae_all_iff.2
    intro I
    have hI : partialSup n f I ≤ derivativeSup n f :=
      le_iSup_of_le I le_rfl
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
        have hbound : ENNReal.ofReal ‖orderedPartial n f x I‖ ≤ derivativeSup n f := by
          simpa [Real.enorm_eq_ofReal_abs] using hx I
        rw [ENNReal.ofReal_le_iff_le_toReal htop] at hbound
        simpa [T, orderedPartial] using hbound
      have hsup : coordinateEvaluationSup T ≤ (derivativeSup n f).toReal := by
        unfold coordinateEvaluationSup
        refine Finset.sup'_le (Seminorm.coordinateTupleNonempty d n) _ ?_
        intro I hI
        exact hcoordReal I
      have hop := norm_continuousMultilinearMap_le_coordinateEvaluationSup T
      have hopen : ENNReal.ofReal ‖T‖ ≤ derivativeSup n f := by
        rw [ENNReal.ofReal_le_iff_le_toReal htop]
        exact hop.trans hsup
      simpa [T] using hopen
  simpa [μ] using hOp

/-- The Appendix B seminorm `⟦f⟧_{n,R}`.  The radius is represented by an
extended-real inverse power, so the definition is total; all source estimates
assume `0 < R`. -/
def snorm {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (n : ℕ) (R : ℝ) : ENNReal :=
  ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal R)⁻¹ ^ n * derivativeSup n f

/-- Smoothness is preserved when the domain is viewed with the equivalent
`ℓ¹` product norm. -/
theorem contDiff_liftVecOne {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} {f : Vec d → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (liftVecOne f) := by
  simpa [liftVecOne] using
    (hf.comp_continuousLinearMap (g := (vecOneEquiv d : VecOne d →L[ℝ] Vec d)))

end AVenhance.FaaDiBruno

end
