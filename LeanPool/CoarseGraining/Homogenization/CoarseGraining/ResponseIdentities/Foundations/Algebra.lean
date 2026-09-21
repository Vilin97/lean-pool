/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
import Mathlib.Data.Real.Pointwise

/-! # Algebra -/

namespace Homogenization

noncomputable section

open Pointwise

/-!
# Scalar response-integrand algebra

Volume-average linearity, symmetric-matrix polarization lemmas,
`AHarmonicFunction` rescale/unscale/sub helpers, and basic algebraic
identities for `scalarResponseIntegrand` and `scalarVariationEnergyIntegrand`.
-/

@[simp] theorem volumeAverage_zero {d : ℕ} (U : Set (Vec d)) :
    volumeAverage U (0 : Vec d → ℝ) = 0 := by
  unfold volumeAverage
  simp

theorem volumeAverage_smul {d : ℕ} (U : Set (Vec d)) (c : ℝ) (f : Vec d → ℝ) :
    volumeAverage U (c • f) = c * volumeAverage U f := by
  unfold volumeAverage
  rw [show (fun x => (c • f) x) = fun x => c • f x by
      funext x
      simp]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul]
  ring

theorem volumeAverage_add {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f U) (hg : MeasureTheory.IntegrableOn g U) :
    volumeAverage U (f + g) = volumeAverage U f + volumeAverage U g := by
  unfold volumeAverage
  rw [show (fun x => (f + g) x) = fun x => f x + g x by
      funext x
      simp]
  rw [MeasureTheory.integral_add hf hg]
  ring

theorem volumeAverage_sub {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f U) (hg : MeasureTheory.IntegrableOn g U) :
    volumeAverage U (f - g) = volumeAverage U f - volumeAverage U g := by
  have hneg : MeasureTheory.IntegrableOn ((-1 : ℝ) • g) U := by
    simpa [MeasureTheory.IntegrableOn] using hg.integrable.smul (-1 : ℝ)
  rw [show f - g = f + (-1 : ℝ) • g by
      funext x
      simp [sub_eq_add_neg]]
  rw [volumeAverage_add hf hneg, volumeAverage_smul]
  ring

theorem volumeAverage_sum {d : ℕ} {α : Type*} {U : Set (Vec d)}
    (s : Finset α) (f : α → Vec d → ℝ)
    (hf : ∀ a ∈ s, MeasureTheory.IntegrableOn (f a) U) :
    volumeAverage U (fun x => s.sum (fun a => f a x)) = s.sum (fun a => volumeAverage U (f a)) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    change volumeAverage U (0 : Vec d → ℝ) = 0
    exact volumeAverage_zero U
  · intro a s ha ih hf
    have haInt : MeasureTheory.IntegrableOn (f a) U := hf a (Finset.mem_insert_self a s)
    have hsInt : ∀ b ∈ s, MeasureTheory.IntegrableOn (f b) U := by
      intro b hb
      exact hf b (Finset.mem_insert_of_mem hb)
    have hsumInt : MeasureTheory.IntegrableOn (fun x => s.sum (fun b => f b x)) U := by
      simpa [MeasureTheory.IntegrableOn] using
        (MeasureTheory.integrable_finsetSum
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume U) s
          (fun b hb => (hsInt b hb).integrable))
    calc
      volumeAverage U (fun x => (insert a s).sum (fun b => f b x))
          = volumeAverage U (fun x => f a x + s.sum (fun b => f b x)) := by
              simp [Finset.sum_insert, ha]
      _ = volumeAverage U (f a + fun x => s.sum (fun b => f b x)) := by
            rfl
      _ = volumeAverage U (f a) + volumeAverage U (fun x => s.sum (fun b => f b x)) := by
            rw [volumeAverage_add haInt hsumInt]
      _ = volumeAverage U (f a) + s.sum (fun b => volumeAverage U (f b)) := by
            rw [ih hsInt]
      _ = (insert a s).sum (fun b => volumeAverage U (f b)) := by
            simp [Finset.sum_insert, ha]

theorem volumeAverage_const {d : ℕ} {U : Set (Vec d)} {c : ℝ}
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    volumeAverage U (fun _ => c) = c := by
  unfold volumeAverage
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
  calc
    (MeasureTheory.volume U).toReal⁻¹ * ((MeasureTheory.volume U).toReal * c)
      = ((MeasureTheory.volume U).toReal⁻¹ * (MeasureTheory.volume U).toReal) * c := by ring
    _ = c := by rw [inv_mul_cancel₀ hvol, one_mul]

theorem volumeAverage_vecDot_left {d : ℕ} {U : Set (Vec d)} (v : Vec d) (f : Vec d → Vec d)
    (hf : ∀ i, MeasureTheory.IntegrableOn (fun x => f x i) U) :
    volumeAverage U (fun x => vecDot v (f x)) =
      vecDot v (fun i => volumeAverage U (fun x => f x i)) := by
  have hsum :
      ∀ i ∈ (Finset.univ : Finset (Fin d)), MeasureTheory.IntegrableOn (fun x => v i * f x i) U := by
    intro i hi
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using! (hf i).integrable.smul (v i)
  calc
    volumeAverage U (fun x => vecDot v (f x))
      = volumeAverage U (fun x => ∑ i, v i * f x i) := by
          simp [vecDot]
    _ = ∑ i, volumeAverage U (fun x => v i * f x i) := by
          rw [volumeAverage_sum (U := U) (s := Finset.univ) (f := fun i x => v i * f x i) hsum]
    _ = ∑ i, v i * volumeAverage U (fun x => f x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [smul_eq_mul] using! (volumeAverage_smul U (v i) (fun x => f x i))
    _ = vecDot v (fun i => volumeAverage U (fun x => f x i)) := by
          simp [vecDot]

theorem volumeAverage_vecDot_right {d : ℕ} {U : Set (Vec d)} (f : Vec d → Vec d) (v : Vec d)
    (hf : ∀ i, MeasureTheory.IntegrableOn (fun x => f x i) U) :
    volumeAverage U (fun x => vecDot (f x) v) =
      vecDot (fun i => volumeAverage U (fun x => f x i)) v := by
  calc
    volumeAverage U (fun x => vecDot (f x) v)
      = volumeAverage U (fun x => vecDot v (f x)) := by
          congr with x
          rw [vecDot_comm]
    _ = vecDot v (fun i => volumeAverage U (fun x => f x i)) :=
          volumeAverage_vecDot_left (U := U) v f hf
    _ = vecDot (fun i => volumeAverage U (fun x => f x i)) v := by
          rw [vecDot_comm]

theorem integrableOn_matVecMul_of_integrableOn_entries {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Mat d}
    (hf : ∀ i j, MeasureTheory.IntegrableOn (fun x => f x i j) U) (y : Vec d) :
    ∀ i, MeasureTheory.IntegrableOn (fun x => matVecMul (f x) y i) U := by
  intro i
  simpa [MeasureTheory.IntegrableOn, matVecMul, mul_comm, mul_left_comm, mul_assoc] using
    (MeasureTheory.integrable_finsetSum
      (μ := MeasureTheory.Measure.restrict MeasureTheory.volume U) Finset.univ
      (fun j _ => (hf i j).integrable.const_mul (y j)))

theorem integrableOn_vecDot_matVecMul_of_integrableOn_entries {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Mat d}
    (hf : ∀ i j, MeasureTheory.IntegrableOn (fun x => f x i j) U) (x y : Vec d) :
    MeasureTheory.IntegrableOn (fun z => vecDot x (matVecMul (f z) y)) U := by
  simpa [MeasureTheory.IntegrableOn, vecDot] using
    (MeasureTheory.integrable_finsetSum
      (μ := MeasureTheory.Measure.restrict MeasureTheory.volume U) Finset.univ
      (fun i _ =>
        ((integrableOn_matVecMul_of_integrableOn_entries hf y i).integrable).const_mul (x i)))

theorem matVecMul_volumeAverageMat {d : ℕ} {U : Set (Vec d)} {f : Vec d → Mat d}
    (hf : ∀ i j, MeasureTheory.IntegrableOn (fun x => f x i j) U) (y : Vec d) :
    matVecMul (volumeAverageMat U f) y =
      fun i => volumeAverage U (fun x => matVecMul (f x) y i) := by
  funext i
  calc
    matVecMul (volumeAverageMat U f) y i
      = ∑ j, volumeAverage U (fun x => f x i j) * y j := by
          simp [volumeAverageMat, matVecMul]
    _ = ∑ j, volumeAverage U (fun x => f x i j * y j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            volumeAverage U (fun x => f x i j) * y j =
                y j * volumeAverage U (fun x => f x i j) := by ring
            _ = volumeAverage U (fun x => f x i j * y j) := by
                rw [← show (y j • fun x => f x i j) =
                    (fun x => f x i j * y j) by
                  funext x
                  simp [Pi.smul_apply, smul_eq_mul, mul_comm]]
                exact (volumeAverage_smul U (y j) (fun x => f x i j)).symm
    _ = volumeAverage U (fun x => ∑ j, f x i j * y j) := by
          symm
          refine volumeAverage_sum (U := U) (s := Finset.univ)
            (f := fun j x => f x i j * y j) ?_
          intro j hj
          simpa [MeasureTheory.IntegrableOn, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
            using (hf i j).integrable.const_mul (y j)
    _ = volumeAverage U (fun x => matVecMul (f x) y i) := by
          simp [matVecMul]

theorem vecDot_matVecMul_volumeAverageMat {d : ℕ} {U : Set (Vec d)} {f : Vec d → Mat d}
    (hf : ∀ i j, MeasureTheory.IntegrableOn (fun x => f x i j) U) (x y : Vec d) :
    vecDot x (matVecMul (volumeAverageMat U f) y) =
      volumeAverage U (fun z => vecDot x (matVecMul (f z) y)) := by
  rw [matVecMul_volumeAverageMat hf y]
  symm
  exact
    volumeAverage_vecDot_left (U := U) x (fun z => matVecMul (f z) y)
      (integrableOn_matVecMul_of_integrableOn_entries hf y)

theorem volumeAverage_nonneg_of_nonneg_on {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hU : MeasurableSet U)
    (h_nonneg : ∀ x ∈ U, 0 ≤ f x) :
    0 ≤ volumeAverage U f := by
  unfold volumeAverage
  refine mul_nonneg ?_ ?_
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg
  · apply MeasureTheory.integral_nonneg_of_ae
    exact (MeasureTheory.ae_restrict_iff' hU).2 (Filter.Eventually.of_forall h_nonneg)

theorem volumeAverage_le_of_le_on {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {f : Vec d → ℝ} {c : ℝ}
    (hU : MeasurableSet U) (hf : MeasureTheory.IntegrableOn f U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (h_le : ∀ x ∈ U, f x ≤ c) :
    volumeAverage U f ≤ c := by
  have hconst : MeasureTheory.IntegrableOn (fun _ : Vec d => c) U := by
    exact MeasureTheory.integrable_const c
  have hnonneg :
      0 ≤ volumeAverage U (fun x => c - f x) := by
    apply volumeAverage_nonneg_of_nonneg_on hU
    intro x hx
    exact sub_nonneg.mpr (h_le x hx)
  have hsub :
      volumeAverage U (fun x => c - f x) = c - volumeAverage U f := by
    rw [show (fun x => c - f x) = (fun _ : Vec d => c) - f by
        funext x
        simp]
    rw [volumeAverage_sub hconst hf, volumeAverage_const hvol]
  nlinarith [hnonneg, hsub]

theorem symmPart_smul {d : ℕ} (c : ℝ) (A : Mat d) :
    symmPart (c • A) = c • symmPart A := by
  ext i j
  simp [symmPart]
  ring

theorem vecDot_matVecMul_symmPart_comm {d : ℕ} (A : Mat d) (ξ η : Vec d) :
    vecDot ξ (matVecMul (symmPart A) η) = vecDot η (matVecMul (symmPart A) ξ) := by
  calc
    vecDot ξ (matVecMul (symmPart A) η)
      = vecDot ξ (matVecMul (matTranspose (symmPart A)) η) := by
          simp
    _ = vecDot (matVecMul (symmPart A) ξ) η := by
          rw [vecDot_matVecMul_transpose]
    _ = vecDot η (matVecMul (symmPart A) ξ) := by
          rw [vecDot_comm]

theorem half_vecDot_sub_polarization_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    (1 / 2 : ℝ) * vecDot ξ (matVecMul A ξ) +
        (1 / 2 : ℝ) * vecDot η (matVecMul A η) -
          (1 / 2 : ℝ) * vecDot (ξ - η) (matVecMul A (ξ - η)) =
      vecDot η (matVecMul A ξ) := by
  have hcomm := vecDot_matVecMul_comm_of_isSymm hA ξ η
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right, hcomm]
  ring

theorem half_vecDot_sub_sub_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) (ξ η : Vec d) :
    (1 / 2 : ℝ) * vecDot (ξ - η) (matVecMul A (ξ - η)) -
        (1 / 2 : ℝ) * vecDot ξ (matVecMul A ξ) -
          (1 / 2 : ℝ) * vecDot η (matVecMul A η) =
      -vecDot η (matVecMul A ξ) := by
  have h := half_vecDot_sub_polarization_of_isSymm hA ξ η
  linarith

namespace AHarmonicFunction

instance {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} : Zero (AHarmonicFunction a U) where
  zero :=
    { toH1 := 0
      isHarmonic := isAHarmonicGradient_zero }

instance {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} : SMul ℝ (AHarmonicFunction a U) where
  smul c u :=
    { toH1 := c • u.toH1
      isHarmonic := isAHarmonicGradient_smul u.isHarmonic c }

@[simp] theorem toH1_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    (0 : AHarmonicFunction a U).toH1 = 0 :=
  rfl

@[simp] theorem toH1_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (u : AHarmonicFunction a U) :
    (c • u).toH1 = c • u.toH1 :=
  rfl

@[simp] theorem grad_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    (0 : AHarmonicFunction a U).toH1.grad = 0 :=
  rfl

@[simp] theorem grad_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (u : AHarmonicFunction a U) :
    (c • u).toH1.grad = c • u.toH1.grad :=
  rfl

def rescaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) (c : ℝ) :
    AHarmonicFunction (c • a) U :=
  { toH1 := u.toH1
    isHarmonic := by
      rcases u.isHarmonic with ⟨hpot, hsol⟩
      refine ⟨hpot, ?_⟩
      simpa [Pi.smul_apply, smul_matVecMul] using! isSolenoidalOn_smul hsol c }

@[simp] theorem toH1_rescaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) (c : ℝ) :
    (u.rescaleCoeff c).toH1 = u.toH1 :=
  rfl

@[simp] theorem grad_rescaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) (c : ℝ) :
    (u.rescaleCoeff c).toH1.grad = u.toH1.grad :=
  rfl

def unscaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (hc : c ≠ 0) (u : AHarmonicFunction (c • a) U) :
    AHarmonicFunction a U :=
  { toH1 := u.toH1
    isHarmonic := by
      rcases u.isHarmonic with ⟨hpot, hsol⟩
      refine ⟨hpot, ?_⟩
      have hscaled := isSolenoidalOn_smul hsol c⁻¹
      have hscaled' :
          IsSolenoidalOn U (fun x => c⁻¹ • matVecMul ((c • a) x) (u.toH1.grad x)) := by
        simpa [Pi.smul_apply] using! hscaled
      have hflux :
          (fun x => c⁻¹ • matVecMul ((c • a) x) (u.toH1.grad x)) =
            fun x => matVecMul (a x) (u.toH1.grad x) := by
        funext x
        simp [Pi.smul_apply, smul_matVecMul, smul_smul, hc]
      rw [hflux] at hscaled'
      exact hscaled' }

@[simp] theorem toH1_unscaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (hc : c ≠ 0) (u : AHarmonicFunction (c • a) U) :
    (u.unscaleCoeff c hc).toH1 = u.toH1 :=
  rfl

@[simp] theorem grad_unscaleCoeff {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (hc : c ≠ 0) (u : AHarmonicFunction (c • a) U) :
    (u.unscaleCoeff c hc).toH1.grad = u.toH1.grad :=
  rfl

def subOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    AHarmonicFunction a U :=
  addSMulOfIntegrable u v hu_int hv_int (-1)

@[simp] theorem toH1_subOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    (subOfIntegrable u v hu_int hv_int).toH1 = u.toH1 - v.toH1 := by
  calc
    (subOfIntegrable u v hu_int hv_int).toH1 = u.toH1 + (-1 : ℝ) • v.toH1 := by
      simp [subOfIntegrable]
    _ = u.toH1 - v.toH1 := by
      rfl

@[simp] theorem grad_subOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    (subOfIntegrable u v hu_int hv_int).toH1.grad = u.toH1.grad - v.toH1.grad := by
  calc
    (subOfIntegrable u v hu_int hv_int).toH1.grad = u.toH1.grad + (-1 : ℝ) • v.toH1.grad := by
      rfl
    _ = u.toH1.grad - v.toH1.grad := by
      funext x
      simp [sub_eq_add_neg]

end AHarmonicFunction

theorem scalarResponseIntegrand_eq_of_grad_eq {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {p q : Vec d} {u v : AHarmonicFunction a U} (hgrad : u.toH1.grad = v.toH1.grad) :
    scalarResponseIntegrand U a p q u = scalarResponseIntegrand U a p q v := by
  funext x
  simp [scalarResponseIntegrand, hgrad]

@[simp] theorem scalarResponseIntegrand_addConst {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (p q : Vec d) (u : AHarmonicFunction a U) (c : ℝ) :
    scalarResponseIntegrand U a p q (u.addConst c) = scalarResponseIntegrand U a p q u := by
  apply scalarResponseIntegrand_eq_of_grad_eq
  funext x
  simp

@[simp] theorem scalarResponseIntegrand_normalizeMeanZero {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (p q : Vec d) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand U a p q u.normalizeMeanZero = scalarResponseIntegrand U a p q u := by
  apply scalarResponseIntegrand_eq_of_grad_eq
  funext x
  simp

@[simp] theorem scalarResponseIntegrand_zero {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) :
    scalarResponseIntegrand U a p q (0 : AHarmonicFunction a U) = 0 := by
  funext x
  change
    -((1 / 2 : ℝ) * vecDot (0 : Vec d) (matVecMul (symmPart (a x)) (0 : Vec d))) -
        vecDot p (matVecMul (a x) (0 : Vec d)) +
      vecDot q (0 : Vec d) = 0
  simp [vecDot_zero_right, matVecMul_zero]

theorem scalarResponseIntegrand_smul {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (c : ℝ) (p q : Vec d) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand U a (c • p) (c • q) (c • u) =
      fun x => c ^ 2 * scalarResponseIntegrand U a p q u x := by
  funext x
  change
    -((1 / 2 : ℝ) * vecDot (c • u.toH1.grad x)
        (matVecMul (symmPart (a x)) (c • u.toH1.grad x))) -
        vecDot (c • p) (matVecMul (a x) (c • u.toH1.grad x)) +
      vecDot (c • q) (c • u.toH1.grad x) =
    c ^ 2 *
      (-((1 / 2 : ℝ) * vecDot (u.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x))) -
        vecDot p (matVecMul (a x) (u.toH1.grad x)) +
        vecDot q (u.toH1.grad x))
  simp [matVecMul_smul, vecDot_smul_left, vecDot_smul_right, pow_two]
  ring

theorem volumeAverage_scalarResponseIntegrand_smul {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (c : ℝ) (p q : Vec d) (u : AHarmonicFunction a U) :
    volumeAverage U (scalarResponseIntegrand U a (c • p) (c • q) (c • u)) =
      c ^ 2 * volumeAverage U (scalarResponseIntegrand U a p q u) := by
  unfold volumeAverage
  rw [scalarResponseIntegrand_smul]
  rw [show (fun x => c ^ 2 * scalarResponseIntegrand U a p q u x) =
      fun x => c ^ 2 • scalarResponseIntegrand U a p q u x by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

noncomputable def scalarFirstVariationIntegrand {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (p q : Vec d) (u w : AHarmonicFunction a U) : Vec d → ℝ :=
  fun x =>
    vecDot q (w.toH1.grad x)
      - vecDot p (matVecMul (a x) (w.toH1.grad x))
      - vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))

noncomputable def scalarVariationEnergyIntegrand {d : ℕ} (a : CoeffField d)
    {U : Set (Vec d)} (w : AHarmonicFunction a U) : Vec d → ℝ :=
  fun x => vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (w.toH1.grad x))

theorem scalarVariationEnergyIntegrand_smul {d : ℕ} (a : CoeffField d)
    {U : Set (Vec d)} (c : ℝ) (w : AHarmonicFunction a U) :
    scalarVariationEnergyIntegrand a (c • w) =
      fun x => c ^ 2 * scalarVariationEnergyIntegrand a w x := by
  funext x
  change
    vecDot (c • w.toH1.grad x) (matVecMul (symmPart (a x)) (c • w.toH1.grad x)) =
      c ^ 2 * vecDot (w.toH1.grad x) (matVecMul (symmPart (a x)) (w.toH1.grad x))
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

theorem volumeAverage_scalarVariationEnergyIntegrand_smul {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (c : ℝ) (w : AHarmonicFunction a U) :
    volumeAverage U (scalarVariationEnergyIntegrand a (c • w)) =
      c ^ 2 * volumeAverage U (scalarVariationEnergyIntegrand a w) := by
  unfold volumeAverage
  rw [scalarVariationEnergyIntegrand_smul]
  rw [show (fun x => c ^ 2 * scalarVariationEnergyIntegrand a w x) =
      fun x => c ^ 2 • scalarVariationEnergyIntegrand a w x by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

end

end Homogenization
