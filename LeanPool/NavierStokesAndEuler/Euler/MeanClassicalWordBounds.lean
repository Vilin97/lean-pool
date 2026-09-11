/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.MeanGradientTestSpace

/-!
# Genuine classical spatial words have exactly the strong L² word norms

Each derivative of the canonical smooth representative is identified with
the corresponding actual L² translation derivative. Consequently finite
Hq sums and external ordered-word sums transfer with constant one, including
uniform time evaluation. There is no tensor-to-word radius conversion.
-/

section

/-! Strong ordinary L² spatial derivatives are the classical derivatives of the reconstructed field.
-/

@[expose] public section

noncomputable section

namespace EulerMeanSmoothRepresentative

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerVectorCalculus
  EulerMeanGradientTest
open scoped ContDiff

theorem representative_pointwise_translation_hasDerivAt (u : EulerMeanSolenoidal.L2)
    (hu : SmoothOrbit u) (v x : Space) :
    HasDerivAt (fun t : ℝ => representative u hu (x+t•v))
      (fderiv ℝ (representative u hu) x v) 0 := by
  have H := ((representative_smooth u hu).differentiable (by simp) x).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  simpa only [Function.comp_def] using H.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)

/-- No prior L² integrability of the classical derivative is assumed. -/
theorem orbitDerivative_ae_fderiv (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v : Space) :
    (orbitDerivative u v : Space → Space) =ᵐ[volume]
      fun x => fderiv ℝ (representative u hu) x v := by
  apply EulerStrongSmoothJet.lp_derivative_ae volume
    (fun t => EulerMeanSolenoidal.translation (t•v) u) (orbitDerivative u v)
    (fun t x => representative u hu (x+t•v))
    (fun x => fderiv ℝ (representative u hu) x v)
    _ (orbitDerivative_hasDerivAt u hu v) (representative_pointwise_translation_hasDerivAt u hu v)
  intro t
  filter_upwards [EulerMeanSolenoidal.translation_ae (t•v) u,
    (measurePreserving_add_right (volume : Measure Space) (t•v)).quasiMeasurePreserving.ae
      (representative_ae u hu)] with x h₁ h₂
  exact h₁.trans h₂

/-- The classical directional derivative is exactly the reconstructed strong derivative. -/
theorem fderiv_representative_apply (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v x : Space)
    :
    fderiv ℝ (representative u hu) x v =
      representative (orbitDerivative u v) (orbitDerivative_smooth u hu v) x := by
  have H := representative_unique (orbitDerivative u v) (orbitDerivative_smooth u hu v)
    (fun y => fderiv ℝ (representative u hu) y v)
    (((representative_smooth u hu).fderiv_right (m := ∞) (by
        simp)).continuous.clm_apply continuous_const)
    (orbitDerivative_ae_fderiv u hu v)
  exact (congrFun H x).symm

theorem representative_directional_memLp (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (v :
    Space) :
    MemLp (fun x => fderiv ℝ (representative u hu) x v) 2 (volume : Measure Space) :=
  (Lp.memLp (orbitDerivative u v)).ae_eq (orbitDerivative_ae_fderiv u hu v)

/-- The full classical first derivative is genuinely square-integrable. -/
theorem representative_fderiv_memLp (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    MemLp (fderiv ℝ (representative u hu)) 2 (volume : Measure Space) := by
  let f (i : Fin 3) (x : Space) := ‖fderiv ℝ (representative u hu) x (EuclideanSpace.single i 1)‖
  have hf (i : Fin 3) : MemLp (f i) 2 (volume : Measure Space) :=
    (representative_directional_memLp u hu (EuclideanSpace.single i 1)).norm
  have hs : MemLp (∑ i : Fin 3, f i) 2 (volume : Measure Space) :=
    memLp_finsetSum' Finset.univ (fun i _ => hf i)
  apply hs.mono'
    ((representative_smooth u hu).fderiv_right (m := ∞) (by simp)).continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Finset.sum_apply, f] using opNorm_le_sum_columns (fderiv ℝ (representative u hu) x)

end EulerMeanSmoothRepresentative

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanClassicalWordBounds

open MeasureTheory Set ContinuousLinearMap Finset EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation EulerParameterWordGevrey
  EulerGevrey
open scoped ContDiff

variable {ι : Type*}

/-- The actual strong L² spatial derivative for an ordered word. -/
def ordinaryWord (directions : ι → Space) (u : L2) {n : ℕ} (w : Fin n → ι) : L2 :=
  wordDerivative directions (fun a : Space => translation a u) w 0

@[simp] theorem ordinaryWord_zero (directions : ι → Space) (u : L2) (w : Fin 0 → ι) :
    ordinaryWord directions u w = u := by
  simp only [ordinaryWord, wordDerivative_zero, translation_zero]

/-- Adding a last direction is the genuine strong directional derivative. -/
theorem ordinaryWord_snoc (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) (i : ι) :
    ordinaryWord directions u (Fin.snoc w i) =
      ordinaryWord directions (orbitDerivative u (directions i)) w := by
  have he : directional directions (fun a : Space => translation a u) i =
      fun a : Space => translation a (orbitDerivative u (directions i)) :=
    funext (fun a => (orbitDerivative_translation u hu (directions i) a).symm)
  unfold ordinaryWord
  rw [wordDerivative_snoc directions _ hu w i 0, he]

/-- The translated strong word is the same actual word at any base point. -/
theorem ordinaryWord_translation (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) (a : Space) :
    translation a (ordinaryWord directions u w) =
      wordDerivative directions (fun b : Space => translation b u) w a := by
  induction n generalizing u with
  | zero => simp only [ordinaryWord_zero, wordDerivative_zero]
  | succ n ih =>
    have ho : ordinaryWord directions u w =
        ordinaryWord directions (orbitDerivative u (directions (w (Fin.last n)))) (Fin.init w) := by
      simpa only [Fin.snoc_init_self] using ordinaryWord_snoc directions u hu (Fin.init w) (w
          (Fin.last n))
    rw [ho, ih _ (orbitDerivative_smooth u hu _) (Fin.init w)]
    have he : directional directions (fun b : Space => translation b u) (w (Fin.last n)) =
        fun b : Space => translation b (orbitDerivative u (directions (w (Fin.last n)))) :=
      funext (fun b => (orbitDerivative_translation u hu _ b).symm)
    simpa only [Fin.snoc_init_self, he] using
      (wordDerivative_snoc directions (fun b : Space => translation b u) hu
        (Fin.init w) (w (Fin.last n)) a).symm

/-- Every strong word itself has the genuine smooth spatial orbit. -/
theorem ordinaryWord_smooth (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) : SmoothOrbit (ordinaryWord directions u w) := by
  have he : (fun a : Space => translation a (ordinaryWord directions u w)) =
      wordDerivative directions (fun a : Space => translation a u) w :=
    funext (ordinaryWord_translation directions u hu w)
  change ContDiff ℝ ∞ _
  rw [he]
  exact wordDerivative_contDiff directions _ hu w

theorem representative_congr {u v : L2} (h : u = v) (hu : SmoothOrbit u) (hv : SmoothOrbit v) :
    representative u hu = representative v hv := by
  subst v
  rfl

/-- Pointwise equality between the actual classical derivative word and the
canonical representative of the corresponding genuine strong L² derivative. -/
theorem representative_word (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) (x : Space) :
    wordDerivative directions (representative u hu) w x =
      representative (ordinaryWord directions u w) (ordinaryWord_smooth directions u hu w) x := by
  induction n generalizing u with
  | zero => simp only [wordDerivative_zero, ordinaryWord_zero]
  | succ n ih =>
    have ho : ordinaryWord directions u w =
        ordinaryWord directions (orbitDerivative u (directions (w (Fin.last n)))) (Fin.init w) := by
      simpa only [Fin.snoc_init_self] using ordinaryWord_snoc directions u hu (Fin.init w) (w
          (Fin.last n))
    have he : directional directions (representative u hu) (w (Fin.last n)) =
        representative (orbitDerivative u (directions (w (Fin.last n)))) (orbitDerivative_smooth u
            hu _) :=
      funext (fun y => fderiv_representative_apply u hu _ y)
    have hw : wordDerivative directions (representative u hu) w x =
        wordDerivative directions (directional directions (representative u hu) (w (Fin.last n)))
            (Fin.init w) x := by
      simpa only [Fin.snoc_init_self] using wordDerivative_snoc directions (representative u hu)
        (representative_smooth u hu) (Fin.init w) (w (Fin.last n)) x
    rw [hw, he, ih _ (orbitDerivative_smooth u hu _) (Fin.init w)]
    exact congrFun (representative_congr ho _ _).symm x

/-- No integrability of classical derivatives is assumed: it follows from
the solved field's genuine smooth L² orbit. -/
theorem ordinaryWord_ae (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) :
    (ordinaryWord directions u w : Space → Space) =ᵐ[volume]
      wordDerivative directions (representative u hu) w :=
  (representative_ae _ (ordinaryWord_smooth directions u hu w)).trans
    (Filter.Eventually.of_forall (fun x => (representative_word directions u hu w x).symm))

theorem classicalWord_memLp (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) :
    MemLp (wordDerivative directions (representative u hu) w) 2 (volume : Measure Space) :=
  (Lp.memLp (ordinaryWord directions u w)).ae_eq (ordinaryWord_ae directions u hu w)

/-- The L² class of the literal classical derivative of the smooth representative. -/
def classicalWordLp (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) : L2 :=
  (classicalWord_memLp directions u hu w).toLp (wordDerivative directions (representative u hu) w)

@[simp] theorem classicalWordLp_eq (directions : ι → Space) (u : L2) (hu : SmoothOrbit u)
    {n : ℕ} (w : Fin n → ι) :
    classicalWordLp directions u hu w = ordinaryWord directions u w := by
  apply Lp.ext
  exact (classicalWord_memLp directions u hu w).coeFn_toLp.trans
    (ordinaryWord_ae directions u hu w).symm

variable [Fintype ι]

/-- The finite sum definition of the actual classical Hq seminorms. -/
def classicalBaseSize (directions : ι → Space) (q : ℕ) (u : L2) (hu : SmoothOrbit u) : ℝ :=
  ∑ k ∈ range (q+1), ∑ w : Fin k → ι, ‖classicalWordLp directions u hu w‖

theorem classicalBaseSize_eq (directions : ι → Space) (q : ℕ) (u : L2) (hu : SmoothOrbit u) :
    classicalBaseSize directions q u hu = baseSize directions q (fun a : Space => translation a u)
        0 := by
  simp only [classicalBaseSize, classicalWordLp_eq, ordinaryWord, baseSize, wordSum]

/-- Sum of actual classical Hq sizes of the external derivative fields.
`representative_word` identifies those fields with derivatives of the original representative. -/
def classicalBlockSize (directions : ι → Space) (q : ℕ) (u : L2) (hu : SmoothOrbit u) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, classicalBaseSize directions q (ordinaryWord directions u w)
    (ordinaryWord_smooth directions u hu w)

/-- Exact identification with the blocks used by the genuine inverse estimate. -/
theorem classicalBlockSize_eq (directions : ι → Space) (q : ℕ) (u : L2) (hu : SmoothOrbit u) (n :
    ℕ) :
    classicalBlockSize directions q u hu n = block directions q (fun a : Space => translation a u)
        n 0 := by
  unfold classicalBlockSize block
  apply sum_congr rfl
  intro w _
  rw [classicalBaseSize_eq]
  exact congrArg (fun g : Space → L2 => baseSize directions q g 0)
    (funext (ordinaryWord_translation directions u hu w))

/-- Uniform time evaluation transfers all genuine classical Hq derivative
words with constant one, and without a radius change. -/
theorem path_classicalBlockSize_le (directions : ι → Space) (q : ℕ)
    (T : ℝ) (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (t : Icc (0 : ℝ) T) (n : ℕ) :
    classicalBlockSize directions q (p t) (pathTranslation_evaluation_contDiff T p hp t) n ≤
      block directions q (fun a : Space => pathTranslation T a p) n 0 := by
  rw [classicalBlockSize_eq]
  have h := block_comp_clm_le directions q
    (ContinuousMap.evalCLM ℝ t : C(Icc (0 : ℝ) T,L2) →L[ℝ] L2)
    (fun a : Space => pathTranslation T a p) hp n 0
  exact h.trans ((mul_le_mul_of_nonneg_right (evaluation_norm_le T t)
    (block_nonneg directions q (fun a : Space => pathTranslation T a p) n 0)).trans_eq (one_mul _))

end EulerMeanClassicalWordBounds
