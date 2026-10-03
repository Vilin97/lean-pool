/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesOscillatory

/-! Transport integration by parts for the material oscillatory terms in l.V. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

theorem IteratesMaterial.material_cell_integrable {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  let K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc
  apply (hf.continuousOn.integrableOn_compact hK).mono_set
  intro x hx i hi
  exact ⟨(hx i hi).1.le, (hx i hi).2.le⟩

theorem IteratesMaterial.material_gradient_continuous {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : Continuous (spaceGrad u) := by
  apply continuous_pi
  intro i
  exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const

theorem IteratesMaterial.material_stream_continuous {φ : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (streamVel (fun _ => φ) 0) := by
  unfold streamVel
  exact (continuous_const.matrix_mulVec (IteratesMaterial.material_gradient_continuous hφ))

theorem IteratesMaterial.material_dot_continuous {a b : Vec 2 → Vec 2}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => vecDot (a x) (b x)) := by
  unfold vecDot
  exact continuous_finsetSum _ (fun i _ => ((continuous_apply i).comp ha).mul ((continuous_apply
      i).comp hb))

theorem iterate_amnrOp_timeOnly {b : AmnrSpace → Vec 2} {f : ℝ → ℝ} {z : AmnrSpace}
    (hf : DifferentiableAt ℝ f z.1) (d : Option (Fin 2)) :
    amnrOp b d (fun y => f y.1) z =
      match d with | none => deriv f z.1 | some _ => 0 := by
  have hh := (hf.hasDerivAt.hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := Vec 2))).fderiv
  unfold amnrOp
  change fderiv ℝ (f ∘ Prod.fst) z (amnrDirection b d z) = _
  rw [hh]
  cases d <;> simp [amnrDirection]

/-- Polarization of the stream energy cancellation gives the transport
integration by parts needed for two different increment derivatives. -/
theorem iterate_stream_transport_pairing_skew {φ u v : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφper : IsZ2Periodic φ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : IsZ2Periodic u) (hvp : IsZ2Periodic v) :
    (∫ x in unitCube, u x * vecDot (streamVel (fun _ => φ) 0 x) (spaceGrad v x)) =
      -(∫ x in unitCube, v x * vecDot (streamVel (fun _ => φ) 0 x) (spaceGrad u x)) := by
  let b := streamVel (fun _ => φ) 0
  have hbc : Continuous b := IteratesMaterial.material_stream_continuous hφ
  have hgu := IteratesMaterial.material_dot_continuous hbc
      (IteratesMaterial.material_gradient_continuous hu)
  have hgv := IteratesMaterial.material_dot_continuous hbc
      (IteratesMaterial.material_gradient_continuous hv)
  have hiuu := IteratesMaterial.material_cell_integrable (hu.continuous.mul hgu)
  have hiuv := IteratesMaterial.material_cell_integrable (hu.continuous.mul hgv)
  have hivu := IteratesMaterial.material_cell_integrable (hv.continuous.mul hgu)
  have hivv := IteratesMaterial.material_cell_integrable (hv.continuous.mul hgv)
  have hsum := theta_stream_drift_pairing_zero hφ hφper (hu.add hv)
    (fun k x => by rw [hup k x, hvp k x])
  have hgrad (x : Vec 2) : spaceGrad (fun y => u y + v y) x = spaceGrad u x + spaceGrad v x := by
    funext i
    unfold spaceGrad
    rw [fderiv_fun_add (hu.differentiable (by simp)).differentiableAt
      (hv.differentiable (by simp)).differentiableAt]
    rfl
  have hexpand : (fun x => (u x + v x) * vecDot (b x) (spaceGrad (fun y => u y + v y) x)) =
      (fun x => (u x * vecDot (b x) (spaceGrad u x) +
        u x * vecDot (b x) (spaceGrad v x)) +
        (v x * vecDot (b x) (spaceGrad u x) + v x * vecDot (b x) (spaceGrad v x))) := by
    funext x
    rw [hgrad]
    simp only [vecDot, Pi.add_apply, Finset.sum_add_distrib, mul_add]
    ring
  change (∫ x in unitCube, (u x + v x) * vecDot (b x) (spaceGrad (fun y => u y + v y) x)) = 0
      at hsum
  have hs := integral_add (hiuu.add hiuv) (hivu.add hivv)
  have hs₁ := integral_add hiuu hiuv
  have hs₂ := integral_add hivu hivv
  dsimp only [Pi.add_apply, Pi.mul_apply] at hs hs₁ hs₂
  rw [hexpand, hs, hs₁, hs₂] at hsum
  have huu := theta_stream_drift_pairing_zero hφ hφper hu hup
  have hvv := theta_stream_drift_pairing_zero hφ hφper hv hvp
  change (∫ x in unitCube, u x * vecDot (b x) (spaceGrad v x)) =
    -(∫ x in unitCube, v x * vecDot (b x) (spaceGrad u x))
  linarith only [hsum, huu, hvv]

/-- The material product pairing has exactly the same spatial integral as
its temporal product pairing. The stream terms cancel by transport IBP. -/
theorem iterate_material_product_pairing
    {φ u v : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ t)) (hφp : IsZ2Periodic (φ t))
    (hu : ContDiff ℝ (⊤ : ℕ∞) (u t)) (hv : ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hup : IsZ2Periodic (u t)) (hvp : IsZ2Periodic (v t))
    (huTime : IntegrableOn (fun x => v t x * deriv (fun s => u s x) t) unitCube)
    (hvTime : IntegrableOn (fun x => u t x * deriv (fun s => v s x) t) unitCube) :
    (∫ x in unitCube, u t x * amnrMaterial (streamVel φ) v t x) +
      (∫ x in unitCube, v t x * amnrMaterial (streamVel φ) u t x) =
    (∫ x in unitCube, u t x * deriv (fun s => v s x) t) +
      (∫ x in unitCube, v t x * deriv (fun s => u s x) t) := by
  have hb : Continuous (streamVel φ t) := IteratesMaterial.material_stream_continuous hφ
  have huv := IteratesMaterial.material_cell_integrable (hu.continuous.mul
    (IteratesMaterial.material_dot_continuous hb (IteratesMaterial.material_gradient_continuous
        hv)))
  have hvu := IteratesMaterial.material_cell_integrable (hv.continuous.mul
    (IteratesMaterial.material_dot_continuous hb (IteratesMaterial.material_gradient_continuous
        hu)))
  have hs₁ := integral_add hvTime huv
  have hs₂ := integral_add huTime hvu
  dsimp only [Pi.mul_apply] at hs₁ hs₂
  have hskew := iterate_stream_transport_pairing_skew hφ hφp hu hv hup hvp
  have heq : streamVel (fun _ => φ t) 0 = streamVel φ t := rfl
  rw [heq] at hskew
  simp only [amnrMaterial, mul_add]
  rw [hs₁, hs₂]
  linarith only [hskew]

/-- Material differentiation of a time coefficient times a space-time field.
Only entrywise differentiability is needed; the drift is arbitrary. -/
theorem iterate_material_time_mul
    {b : ℝ → Vec 2 → Vec 2} {q : ℝ → ℝ} {h : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2} (hq : DifferentiableAt ℝ q t)
    (hh : DifferentiableAt ℝ (fun z : AmnrSpace => h z.1 z.2) (t, x)) :
    amnrMaterial b (fun s y => q s * h s y) t x =
      deriv q t * h t x + q t * amnrMaterial b h t x := by
  have hqJoint : DifferentiableAt ℝ (fun z : AmnrSpace => q z.1) (t, x) :=
    hq.comp (t, x) differentiableAt_fst
  have hm := amnrOp_mul (b := fun z => b z.1 z.2) none hqJoint hh
  rw [amnrOp_material (hqJoint.mul hh), iterate_amnrOp_timeOnly hq none,
    amnrOp_material hh] at hm
  exact hm

/-- The finite primitive/Hessian contraction obeys the material product rule.
This is the algebra behind the first-increment half-square cancellation. -/
theorem iterate_material_matrix_contract
    {b : ℝ → Vec 2 → Vec 2}
    {Q : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {t : ℝ} {x : Vec 2}
    (hQ : ∀ i j, DifferentiableAt ℝ (fun s => Q s i j) t)
    (hH : ∀ i j, DifferentiableAt ℝ
      (fun z : AmnrSpace => H z.1 z.2 i j) (t, x)) :
    amnrMaterial b (fun s y => ∑ i : Fin 2, ∑ j : Fin 2, Q s i j * H s y i j) t x =
      (∑ i : Fin 2, ∑ j : Fin 2, deriv (fun s => Q s i j) t * H t x i j) +
      ∑ i : Fin 2, ∑ j : Fin 2, Q t i j *
        amnrMaterial b (fun s y => H s y i j) t x := by
  let B : AmnrSpace → Vec 2 := fun z => b z.1 z.2
  let F := fun (i j : Fin 2) (z : AmnrSpace) => Q z.1 i j * H z.1 z.2 i j
  have hF (i j : Fin 2) : DifferentiableAt ℝ (F i j) (t, x) := by
    have hq : DifferentiableAt ℝ (fun z : AmnrSpace => Q z.1 i j) (t, x) :=
      (hQ i j).comp (f := Prod.fst) (t, x) differentiableAt_fst
    exact hq.mul (hH i j)
  have hsum (i : Fin 2) : DifferentiableAt ℝ (fun z => ∑ j : Fin 2, F i j z) (t, x) :=
    DifferentiableAt.fun_sum (fun j _ => hF i j)
  have hall : DifferentiableAt ℝ (fun z => ∑ i : Fin 2, ∑ j : Fin 2, F i j z) (t, x) :=
    DifferentiableAt.fun_sum (fun i _ => hsum i)
  have hout := amnrOp_sum (b := B) Finset.univ none
    (fun i z => ∑ j : Fin 2, F i j z) (t, x) (fun i _ => hsum i)
  have hin (i : Fin 2) := amnrOp_sum (b := B) Finset.univ none
    (F i) (t, x) (fun j _ => hF i j)
  change amnrOp B none (fun z => ∑ i : Fin 2, ∑ j : Fin 2, F i j z) (t, x) =
    ∑ i : Fin 2, amnrOp B none (fun z => ∑ j : Fin 2, F i j z) (t, x) at hout
  have hinFun (i : Fin 2) :
      amnrOp B none (fun z => ∑ j : Fin 2, F i j z) (t, x) =
        ∑ j : Fin 2, amnrOp B none (F i j) (t, x) := hin i
  rw [amnrOp_material hall] at hout
  simp only [hinFun] at hout
  change amnrMaterial b (fun s y => ∑ i : Fin 2, ∑ j : Fin 2, Q s i j * H s y i j) t x =
    ∑ i : Fin 2, ∑ j : Fin 2, amnrOp B none (F i j) (t, x) at hout
  rw [hout]
  have hentry (i j : Fin 2) : amnrOp B none (F i j) (t, x) =
      deriv (fun s => Q s i j) t * H t x i j +
      Q t i j * amnrMaterial b (fun s y => H s y i j) t x := by
    rw [amnrOp_material (hF i j)]
    exact iterate_material_time_mul (hQ i j) (hH i j)
  simp only [hentry, Finset.sum_add_distrib]

end AVenhance.Infra.Section4
