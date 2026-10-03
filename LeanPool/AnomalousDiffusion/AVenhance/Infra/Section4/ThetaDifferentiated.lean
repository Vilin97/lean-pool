/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaTimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Product

/-! Higher spatial derivatives of the classical theta equation. -/

@[expose] public section

noncomputable section

open Homogenization
open Filter
open AVenhance.Infra.Section4
open scoped Topology

namespace AVenhance.Infra.Section4

/-- Pure time direction used to differentiate the temperature equation. -/
def ThetaDifferentiated.thetaTimeDir : ℝ × Vec 2 := (1, 0)

/-- Pure spatial coordinate direction used to differentiate the temperature equation. -/
def ThetaDifferentiated.thetaSpaceDir (i : Fin 2) : ℝ × Vec 2 := (0, Homogenization.basisVec i)

/-- Joint time-space domain with strictly positive time. -/
def ThetaDifferentiated.thetaJointPositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

/-- Ordered spatial derivatives of a scalar function on the joint time-space domain. -/
def thetaJointWordDerivative : List (Fin 2) →
    (ℝ × Vec 2 → ℝ) → (ℝ × Vec 2 → ℝ)
  | [], f => f
  | i :: w, f => fun p =>
      fderiv ℝ (thetaJointWordDerivative w f) p (ThetaDifferentiated.thetaSpaceDir i)

/-- Time partial derivative of a scalar function on joint time-space. -/
def thetaJointTimePartial (f : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => fderiv ℝ f p ThetaDifferentiated.thetaTimeDir

theorem thetaJointTimePartial_contDiffOn {f : ℝ × Vec 2 → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaDifferentiated.thetaJointPositiveDomain) :
    ContDiffOn ℝ (⊤ : ℕ∞) (thetaJointTimePartial f) ThetaDifferentiated.thetaJointPositiveDomain
        := by
  have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) ThetaDifferentiated.thetaJointPositiveDomain :=
    (contDiffOn_infty_iff_fderiv_of_isOpen
      (isOpen_Ioi.prod isOpen_univ)).1 hf |>.2
  have hdir : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : ℝ × Vec 2 => ThetaDifferentiated.thetaTimeDir)
          ThetaDifferentiated.thetaJointPositiveDomain :=
    contDiffOn_const
  have happly := hderiv.clm_apply hdir
  change ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p => fderiv ℝ f p ThetaDifferentiated.thetaTimeDir)
        ThetaDifferentiated.thetaJointPositiveDomain
  exact happly

theorem thetaJointWordDerivative_contDiffOn {f : ℝ × Vec 2 → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaDifferentiated.thetaJointPositiveDomain) :
    ∀ w : List (Fin 2),
      ContDiffOn ℝ (⊤ : ℕ∞) (thetaJointWordDerivative w f)
        ThetaDifferentiated.thetaJointPositiveDomain := by
  intro w
  induction w with
  | nil => exact hf
  | cons i w ih =>
      have hderiv : ContDiffOn ℝ (⊤ : ℕ∞)
          (fderiv ℝ (thetaJointWordDerivative w f)) ThetaDifferentiated.thetaJointPositiveDomain :=
        (contDiffOn_infty_iff_fderiv_of_isOpen
          (isOpen_Ioi.prod isOpen_univ)).1 ih |>.2
      have hdir : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun _ : ℝ × Vec 2 => ThetaDifferentiated.thetaSpaceDir i)
              ThetaDifferentiated.thetaJointPositiveDomain :=
        contDiffOn_const
      have happly := hderiv.clm_apply hdir
      simpa [thetaJointWordDerivative] using happly

/-- Differentiating a spatial slice is evaluation of the joint derivative in
the corresponding spatial direction. -/
theorem theta_joint_spatial_section_derivative {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      ThetaDifferentiated.thetaJointPositiveDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (u t) x i =
      fderiv ℝ (Function.uncurry u) (t, x) (0, Homogenization.basisVec i) := by
  let U : ℝ × Vec 2 → ℝ := Function.uncurry u
  have hp : (t, x) ∈ ThetaDifferentiated.thetaJointPositiveDomain := by
    simp [ThetaDifferentiated.thetaJointPositiveDomain, ht]
  have hAt : ContDiffAt ℝ (⊤ : ℕ∞) U (t, x) := by
    simpa [U] using hu.contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have hslice : HasFDerivAt (fun y : Vec 2 => (t, y))
      (ContinuousLinearMap.prod (0 : Vec 2 →L[ℝ] ℝ)
        (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) x)
  have hcomp := (hAt.differentiableAt (by simp)).hasFDerivAt.comp x hslice
  have hcomp' := hcomp.fderiv
  change fderiv ℝ (U ∘ Prod.mk t) x (Homogenization.basisVec i) = _
  rw [hcomp']
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rfl

/-- The time and spatial coordinate derivatives of a jointly smooth function commute. -/
theorem theta_time_spatial_partial_commute {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      ThetaDifferentiated.thetaJointPositiveDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fderiv ℝ (Function.uncurry u)) (t, x)
        (0, Homogenization.basisVec i) (1, 0) =
      fderiv ℝ (fderiv ℝ (Function.uncurry u)) (t, x)
        (1, 0) (0, Homogenization.basisVec i) := by
  let U : ℝ × Vec 2 → ℝ := Function.uncurry u
  let p : ℝ × Vec 2 := (t, x)
  have hp : p ∈ ThetaDifferentiated.thetaJointPositiveDomain := by
    simp [p, ThetaDifferentiated.thetaJointPositiveDomain, ht]
  have hAtTop : ContDiffAt ℝ (⊤ : ℕ∞) U p := by
    have hAt := hu.contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
    simpa [U] using hAt
  have hAt2 : ContDiffAt ℝ 2 U p := hAtTop.of_le (by norm_num)
  have hsymm := hAt2.isSymmSndFDerivAt (by norm_num)
  simpa [p, ThetaDifferentiated.thetaTimeDir, ThetaDifferentiated.thetaSpaceDir] using hsymm
      (ThetaDifferentiated.thetaSpaceDir i) ThetaDifferentiated.thetaTimeDir

/-- The ordered joint derivatives restrict to the paper's ordered spatial
coordinate derivatives on every positive-time slice. -/
theorem thetaJointWordDerivative_eq_classicalWordDerivative
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) ThetaDifferentiated.thetaJointPositiveDomain) :
    ∀ (w : List (Fin 2)) {t : ℝ}, 0 < t → ∀ x : Vec 2,
      thetaJointWordDerivative w (Function.uncurry u) (t, x) =
        classicalWordDerivative w (u t) x := by
  intro w
  induction w with
  | nil =>
      intro t ht x
      rfl
  | cons i w ih =>
      intro t ht x
      let v : ℝ → Vec 2 → ℝ := fun s y =>
        thetaJointWordDerivative w (Function.uncurry u) (s, y)
      have hv : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry v)
          ThetaDifferentiated.thetaJointPositiveDomain := by
        change ContDiffOn ℝ (⊤ : ℕ∞)
          (thetaJointWordDerivative w (Function.uncurry u))
              ThetaDifferentiated.thetaJointPositiveDomain
        exact thetaJointWordDerivative_contDiffOn hu w
      have hsection := theta_joint_spatial_section_derivative hv ht x i
      have htail : v t = classicalWordDerivative w (u t) := by
        funext y
        exact ih (t := t) ht y
      calc
        thetaJointWordDerivative (i :: w) (Function.uncurry u) (t, x) =
            fderiv ℝ (thetaJointWordDerivative w (Function.uncurry u))
              (t, x) (ThetaDifferentiated.thetaSpaceDir i) := rfl
        _ = AVenhance.spaceGrad (v t) x i := hsection.symm
        _ = classicalWordDerivative (i :: w) (u t) x := by
          rw [htail]
          rfl

/-- Any ordered collection of spatial derivatives commutes with the time
partial of a jointly smooth function on positive time. -/
theorem thetaJointWordDerivative_timePartial
    {f : ℝ × Vec 2 → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaDifferentiated.thetaJointPositiveDomain) :
    ∀ (w : List (Fin 2)) (p : ℝ × Vec 2), p ∈ ThetaDifferentiated.thetaJointPositiveDomain →
      thetaJointWordDerivative w (thetaJointTimePartial f) p =
        thetaJointTimePartial (thetaJointWordDerivative w f) p := by
  intro w
  induction w with
  | nil =>
      intro p hp
      rfl
  | cons i w ih =>
      intro p hp
      rcases p with ⟨t, x⟩
      have ht : 0 < t := by
        simpa [ThetaDifferentiated.thetaJointPositiveDomain] using hp.1
      have htail_event :
          (fun q => thetaJointWordDerivative w (thetaJointTimePartial f) q) =ᶠ[𝓝 (t, x)]
            (fun q => thetaJointTimePartial (thetaJointWordDerivative w f) q) := by
        filter_upwards [((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)] with q hq
        exact ih q hq
      let v : ℝ → Vec 2 → ℝ := fun s y =>
        thetaJointWordDerivative w f (s, y)
      have hv : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry v)
          ThetaDifferentiated.thetaJointPositiveDomain := by
        change ContDiffOn ℝ (⊤ : ℕ∞)
          (thetaJointWordDerivative w f) ThetaDifferentiated.thetaJointPositiveDomain
        exact thetaJointWordDerivative_contDiffOn hf w
      have hcomm := theta_time_spatial_partial_commute hv ht x i
      have hvEq : Function.uncurry v = thetaJointWordDerivative w f := by
        funext q
        rcases q with ⟨s, y⟩
        rfl
      rw [hvEq] at hcomm
      have hVAtTop : ContDiffAt ℝ (⊤ : ℕ∞)
          (thetaJointWordDerivative w f) (t, x) := by
        have hVOn := thetaJointWordDerivative_contDiffOn hf w
        exact hVOn.contDiffAt
          ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
      have hVAt2 : ContDiffAt ℝ 2 (thetaJointWordDerivative w f) (t, x) :=
        hVAtTop.of_le (by norm_num)
      have hGAt : ContDiffAt ℝ 1
          (fderiv ℝ (thetaJointWordDerivative w f)) (t, x) :=
        hVAt2.fderiv_right (by norm_num)
      have hGDiff : DifferentiableAt ℝ
          (fderiv ℝ (thetaJointWordDerivative w f)) (t, x) :=
        hGAt.differentiableAt (by norm_num)
      have hR : DifferentiableAt ℝ
          (thetaJointTimePartial (thetaJointWordDerivative w f)) (t, x) := by
        have hRtop := thetaJointTimePartial_contDiffOn
          (thetaJointWordDerivative_contDiffOn hf w)
        have hRAt := hRtop.contDiffAt
          ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
        exact hRAt.differentiableAt (by simp)
      have htransferred := hR.hasFDerivAt.congr_of_eventuallyEq htail_event
      have hderivEq := htransferred.fderiv
      change fderiv ℝ
          (thetaJointWordDerivative w (thetaJointTimePartial f)) (t, x)
            (ThetaDifferentiated.thetaSpaceDir i) =
        fderiv ℝ (thetaJointWordDerivative (i :: w) f) (t, x) ThetaDifferentiated.thetaTimeDir
      rw [hderivEq]
      change fderiv ℝ
          (fun q => fderiv ℝ (thetaJointWordDerivative w f) q ThetaDifferentiated.thetaTimeDir)
            (t, x) (ThetaDifferentiated.thetaSpaceDir i) =
        fderiv ℝ
          (fun q => fderiv ℝ (thetaJointWordDerivative w f) q (ThetaDifferentiated.thetaSpaceDir i))
            (t, x) ThetaDifferentiated.thetaTimeDir
      rw [fderiv_clm_apply hGDiff (differentiableAt_const ThetaDifferentiated.thetaTimeDir)]
      rw [fderiv_clm_apply hGDiff (differentiableAt_const (ThetaDifferentiated.thetaSpaceDir i))]
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
      exact hcomm

/-- The ordinary time derivative commutes with any ordered spatial word for
a classical function that is jointly smooth at positive time. -/
theorem classicalWordDerivative_timePartial_commute
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) ThetaDifferentiated.thetaJointPositiveDomain)
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    classicalWordDerivative w (fun y => classicalTimePartial u (t, y)) x =
      classicalTimePartial (fun s y => classicalWordDerivative w (u s) y) (t, x) := by
  let U : ℝ × Vec 2 → ℝ := Function.uncurry u
  have hleftFamily : ContDiffOn ℝ (⊤ : ℕ∞)
      (thetaJointTimePartial U) ThetaDifferentiated.thetaJointPositiveDomain :=
    thetaJointTimePartial_contDiffOn hu
  let leftFamily : ℝ → Vec 2 → ℝ := fun s y =>
    thetaJointTimePartial U (s, y)
  have hleftBridge := thetaJointWordDerivative_eq_classicalWordDerivative
    (u := leftFamily) (by
      change ContDiffOn ℝ (⊤ : ℕ∞) (thetaJointTimePartial U)
        ThetaDifferentiated.thetaJointPositiveDomain
      exact hleftFamily) w ht x
  have hcomm := thetaJointWordDerivative_timePartial hu w (t, x) (by
    simpa [ThetaDifferentiated.thetaJointPositiveDomain] using
      (show 0 < t ∧ x ∈ Set.univ from ⟨ht, Set.mem_univ x⟩))
  let rightFamily : ℝ → Vec 2 → ℝ := fun s y =>
    classicalWordDerivative w (u s) y
  have hrightEvent : Function.uncurry rightFamily =ᶠ[𝓝 (t, x)]
      thetaJointWordDerivative w U := by
    filter_upwards [((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (by simpa [ThetaDifferentiated.thetaJointPositiveDomain] using
        (show 0 < t ∧ x ∈ Set.univ from ⟨ht, Set.mem_univ x⟩)))] with p hp
    rcases p with ⟨s, y⟩
    have hs : 0 < s := by simpa [ThetaDifferentiated.thetaJointPositiveDomain] using hp.1
    exact (thetaJointWordDerivative_eq_classicalWordDerivative hu w hs y).symm
  have hrightSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (thetaJointWordDerivative w U) ThetaDifferentiated.thetaJointPositiveDomain :=
    thetaJointWordDerivative_contDiffOn hu w
  have hrightAt : ContDiffAt ℝ (⊤ : ℕ∞)
    (thetaJointWordDerivative w U) (t, x) :=
    hrightSmooth.contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (by simpa [ThetaDifferentiated.thetaJointPositiveDomain] using
          (show 0 < t ∧ x ∈ Set.univ from ⟨ht, Set.mem_univ x⟩)))
  have hrightDeriv := (hrightAt.differentiableAt (by simp)).hasFDerivAt
    |>.congr_of_eventuallyEq hrightEvent
  have hrightDerivEq := hrightDeriv.fderiv
  have hleftEq : leftFamily t = fun y => classicalTimePartial u (t, y) := by
    funext y
    rfl
  calc
    classicalWordDerivative w (fun y => classicalTimePartial u (t, y)) x =
        thetaJointWordDerivative w (thetaJointTimePartial U) (t, x) := by
          rw [← hleftEq]
          exact hleftBridge.symm
    _ = thetaJointTimePartial (thetaJointWordDerivative w U) (t, x) := hcomm
    _ = classicalTimePartial rightFamily (t, x) := by
          change fderiv ℝ (thetaJointWordDerivative w U) (t, x) ThetaDifferentiated.thetaTimeDir =
            fderiv ℝ (Function.uncurry rightFamily) (t, x) ThetaDifferentiated.thetaTimeDir
          exact congrArg (fun L : (ℝ × Vec 2) →L[ℝ] ℝ => L ThetaDifferentiated.thetaTimeDir)
            hrightDerivEq.symm

theorem classicalWordDerivative_add (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x + g x) =
      fun x => classicalWordDerivative w f x + classicalWordDerivative w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons i w ih =>
      have hdf := classicalWordDerivative_contDiff w f hf
      have hdg := classicalWordDerivative_contDiff w g hg
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => f y + g y)) x i = _
      rw [ih f g hf hg]
      exact classicalSpaceGrad_add (classicalWordDerivative w f)
        (classicalWordDerivative w g) hdf hdg i x

theorem classicalWordDerivative_sub (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x - g x) =
      fun x => classicalWordDerivative w f x - classicalWordDerivative w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons i w ih =>
      have hdf := classicalWordDerivative_contDiff w f hf
      have hdg := classicalWordDerivative_contDiff w g hg
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => f y - g y)) x i = _
      rw [ih f g hf hg]
      exact classicalSpaceGrad_sub (classicalWordDerivative w f)
        (classicalWordDerivative w g) hdf hdg i x

theorem ThetaDifferentiated.classicalSpaceGrad_const_mul (c : ℝ) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => c * f y) x i =
      c * AVenhance.spaceGrad f x i := by
  change fderiv ℝ (fun y => c * f y) x (Homogenization.basisVec i) = _
  rw [fderiv_const_mul (hf.differentiable (by simp) x) c]
  simp [AVenhance.spaceGrad]

theorem ThetaDifferentiated.thetaSpaceGradComponent_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad f x i) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem classicalWordDerivative_const_mul (w : List (Fin 2))
    (c : ℝ) (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (fun x => c * f x) =
      fun x => c * classicalWordDerivative w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have hdf := classicalWordDerivative_contDiff w f hf
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => c * f y)) x i = _
      rw [ih]
      exact ThetaDifferentiated.classicalSpaceGrad_const_mul c (classicalWordDerivative w f) hdf i x

theorem classicalWordDerivative_spaceLap (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (AVenhance.spaceLap f) =
      AVenhance.spaceLap (classicalWordDerivative w f) := by
  have hlap : AVenhance.spaceLap f = fun x =>
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 0) x 0 +
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 1) x 1 := by
    funext x
    simp [AVenhance.spaceLap, Fin.sum_univ_two]
  rw [hlap]
  have h0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 0) x 0) :=
    ThetaDifferentiated.thetaSpaceGradComponent_contDiff
        (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hf 0) 0
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 1) x 1) :=
    ThetaDifferentiated.thetaSpaceGradComponent_contDiff
        (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hf 1) 1
  rw [classicalWordDerivative_add w _ _ h0 h1]
  have hterm (j : Fin 2) :
        classicalWordDerivative w
            (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x j) =
          fun x => AVenhance.spaceGrad
            (fun y => AVenhance.spaceGrad (classicalWordDerivative w f) y j) x j := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => AVenhance.spaceGrad f y j) :=
      ThetaDifferentiated.thetaSpaceGradComponent_contDiff hf j
    have hfirst := classicalWordDerivative_commute_gradient w
      (fun y => AVenhance.spaceGrad f y j) hinner j
    have hsecond := classicalWordDerivative_commute_gradient w f hf j
    funext x
    calc
      _ = AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => AVenhance.spaceGrad f y j)) x j :=
            congrFun hfirst x
      _ = _ := by rw [hsecond]
  funext x
  simp only [AVenhance.spaceLap, Fin.sum_univ_two]
  rw [congrFun (hterm 0) x, congrFun (hterm 1) x]

theorem ThetaDifferentiated.theta_smooth_joint_slice {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Vec 2 → E}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ThetaDifferentiated.thetaJointPositiveDomain)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (fun x => f (t, x)) := by
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => (t, x)) Set.univ := by
    exact contDiffOn_const.prodMk contDiffOn_id
  have hmem : ∀ x : Vec 2, x ∈ Set.univ →
      (t, x) ∈ ThetaDifferentiated.thetaJointPositiveDomain := by
    intro x hx
    exact ⟨ht, Set.mem_univ x⟩
  have hcomp := hf.comp hmap hmem
  have hcomp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (t, x)) Set.univ := by
    simpa [Function.comp_def] using hcomp
  exact contDiffOn_univ.mp hcomp'

theorem ThetaDifferentiated.theta_spaceLap_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap f) := by
  have h0 := ThetaDifferentiated.thetaSpaceGradComponent_contDiff
    (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hf 0) 0
  have h1 := ThetaDifferentiated.thetaSpaceGradComponent_contDiff
    (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hf 1) 1
  rw [show AVenhance.spaceLap f = fun x =>
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 0) x 0 +
        AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y 1) x 1 by
    funext x
    simp [AVenhance.spaceLap, Fin.sum_univ_two]]
  exact h0.add h1

theorem ThetaDifferentiated.theta_transport_contDiff {b : Vec 2 → Vec 2}
    {u : Vec 2 → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hu j)

theorem ThetaDifferentiated.classicalWordDerivative_zero (w : List (Fin 2)) :
    classicalWordDerivative w (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      funext x
      change AVenhance.spaceGrad (classicalWordDerivative w (fun _ => (0 : ℝ))) x i = 0
      rw [ih]
      simp [AVenhance.spaceGrad, fderiv_const_apply]

/-- The classical equation differentiated along an arbitrary ordered spatial
word. The last term is exactly the finite transport commutator expansion. -/
theorem theta_classical_differentiated_transport_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol b κ (fun _ _ => 0) θ₀ θ)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry b)
      ThetaDifferentiated.thetaJointPositiveDomain)
    {t : ℝ} (ht : 0 < t) (w : List (Fin 2)) (x : Vec 2) :
    classicalTimePartial
        (fun s y => classicalWordDerivative w (θ s) y) (t, x) -
      κ * AVenhance.spaceLap (classicalWordDerivative w (θ t)) x +
      classicalTransport (b t) (classicalWordDerivative w (θ t)) x +
      ∑ j : Fin 2,
        classicalWordCommutatorExpansion w (fun y => b t y j)
          (fun y => AVenhance.spaceGrad (θ t) y j) x = 0 := by
  have hθOpen : ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry θ) ThetaDifferentiated.thetaJointPositiveDomain := by
    apply hsol.1.mono
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    change 0 < s at hs
    exact ⟨le_of_lt hs, Set.mem_univ y⟩
  have hθSlice := ThetaDifferentiated.theta_smooth_joint_slice hθOpen ht
  have hbSlice := ThetaDifferentiated.theta_smooth_joint_slice hb ht
  have htimeSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => classicalTimePartial θ (t, y)) :=
    ThetaDifferentiated.theta_smooth_joint_slice (thetaJointTimePartial_contDiffOn hθOpen) ht
  have hlapSmooth := ThetaDifferentiated.theta_spaceLap_contDiff hθSlice
  have htransportSmooth := ThetaDifferentiated.theta_transport_contDiff hbSlice hθSlice
  have htimefun : (fun y => deriv (fun s => θ s y) t) =
      fun y => classicalTimePartial θ (t, y) := by
    funext y
    exact (classicalTimePartial_eq_deriv hθOpen ht y).symm
  have hresidual : (fun y => AVenhance.advDiffOp b κ θ t y) =
      fun y => classicalTimePartial θ (t, y) - κ * AVenhance.spaceLap (θ t) y +
        classicalTransport (b t) (θ t) y := by
    funext y
    change deriv (fun s => θ s y) t - κ * AVenhance.spaceLap (θ t) y +
        vecDot (b t y) (AVenhance.spaceGrad (θ t) y) = _
    rw [congrFun htimefun y]
    rfl
  have hresidualZero : (fun y => AVenhance.advDiffOp b κ θ t y) = fun _ => 0 := by
    funext y
    exact hsol.2.2.2 t ht y
  have hzero := congrArg (classicalWordDerivative w) hresidualZero
  have hwordResidual :
      classicalWordDerivative w (fun y => AVenhance.advDiffOp b κ θ t y) x = 0 := by
    have h := congrFun hzero x
    simpa only [ThetaDifferentiated.classicalWordDerivative_zero] using h
  have hwordExpanded := congrArg (classicalWordDerivative w) hresidual
  have hwordExpandedAt := congrFun hwordExpanded x
  have hsplit := classicalWordDerivative_transport_eq_commutatorExpansion
    w (b t) (θ t) hbSlice hθSlice x
  have htimeCommute := classicalWordDerivative_timePartial_commute
    hθOpen ht w x
  have hlapCommute := classicalWordDerivative_spaceLap w (θ t) hθSlice
  have hκlapSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => κ * AVenhance.spaceLap (θ t) y) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => κ)).mul hlapSmooth
  have hpartSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => classicalTimePartial θ (t, y) - κ * AVenhance.spaceLap (θ t) y) :=
    htimeSmooth.sub hκlapSmooth
  rw [hresidual] at hwordResidual
  rw [classicalWordDerivative_add w
    (fun y => classicalTimePartial θ (t, y) - κ * AVenhance.spaceLap (θ t) y)
    (classicalTransport (b t) (θ t)) hpartSmooth htransportSmooth] at hwordResidual
  rw [classicalWordDerivative_sub w
    (fun y => classicalTimePartial θ (t, y))
    (fun y => κ * AVenhance.spaceLap (θ t) y) htimeSmooth hκlapSmooth] at hwordResidual
  rw [classicalWordDerivative_const_mul w κ (AVenhance.spaceLap (θ t)) hlapSmooth]
    at hwordResidual
  change classicalWordDerivative w
        (fun y => classicalTimePartial θ (t, y)) x -
      κ * classicalWordDerivative w (AVenhance.spaceLap (θ t)) x +
      classicalWordDerivative w (classicalTransport (b t) (θ t)) x = 0 at hwordResidual
  rw [htimeCommute, hlapCommute] at hwordResidual
  have htransportEq : classicalWordDerivative w (classicalTransport (b t) (θ t)) x =
      vecDot (b t x) (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) +
        ∑ j : Fin 2,
          classicalWordCommutatorExpansion w (fun y => b t y j)
            (fun y => AVenhance.spaceGrad (θ t) y j) x := by
    linarith [hsplit]
  rw [htransportEq] at hwordResidual
  have hprincipal : classicalTransport (b t) (classicalWordDerivative w (θ t)) x =
      vecDot (b t x) (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := rfl
  rw [hprincipal]
  linarith

theorem ThetaDifferentiated.list_sum_fin_sum_swap {α : Type*} (L : List α)
    (F : Fin 2 → α → ℝ) :
    (∑ j : Fin 2, (L.map fun a => F j a).sum) =
      (L.map fun a => ∑ j : Fin 2, F j a).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, Fin.sum_univ_two]
      have htail :
          (L.map fun a => F 0 a).sum + (L.map fun a => F 1 a).sum =
            (L.map fun a => F 0 a + F 1 a).sum := by
        calc
          _ = ∑ j : Fin 2, (L.map fun a => F j a).sum := by
            rw [Fin.sum_univ_two]
          _ = (L.map fun a => ∑ j : Fin 2, F j a).sum := ih
          _ = _ := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro z hz
            simp only [Fin.sum_univ_two]
      calc
        _ = F 0 a + F 1 a +
            ((L.map fun a => F 0 a).sum + (L.map fun a => F 1 a).sum) := by ring
        _ = F 0 a + F 1 a +
            (L.map fun a => F 0 a + F 1 a).sum := by rw [htail]

theorem ThetaDifferentiated.list_sum_zero_of_forall {α : Type*} (L : List α) (f : α → ℝ)
    (hf : ∀ a ∈ L, f a = 0) : (L.map f).sum = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have htail : ∀ z ∈ L, f z = 0 := by
        intro z hz
        exact hf z (by simp [hz])
      simp only [List.map_cons, List.sum_cons]
      rw [hf a (by simp), ih htail]
      simp

theorem ThetaDifferentiated.thetaDifferentiated_streamVel_components {φ : Vec 2 → ℝ}
    {x : Vec 2} :
    AVenhance.streamVel (fun _ => φ) 0 x 0 = -AVenhance.spaceGrad φ x 1 ∧
    AVenhance.streamVel (fun _ => φ) 0 x 1 = AVenhance.spaceGrad φ x 0 := by
  have hform : AVenhance.streamVel (fun _ => φ) 0 x =
      ![-AVenhance.spaceGrad φ x 1, AVenhance.spaceGrad φ x 0] := by
    funext i
    fin_cases i <;> simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  constructor
  · exact congrFun hform 0
  · exact congrFun hform 1

/-- Every ordered spatial derivative of a two-dimensional stream velocity is
divergence free. This is the cancellation that turns the differentiated
transport commutator into a divergence flux. -/
theorem theta_streamVel_ordered_derivative_divergence_free
    (φ : Vec 2 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : List (Fin 2)) (x : Vec 2) :
    (∑ j : Fin 2, AVenhance.spaceGrad
      (classicalWordDerivative w (fun y => AVenhance.streamVel (fun _ => φ) 0 y j)) x j) = 0 := by
  have hvel0 : (fun y => AVenhance.streamVel (fun _ => φ) 0 y 0) =
      fun y => (-1 : ℝ) * AVenhance.spaceGrad φ y 1 := by
    funext y
    rw [(ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := y)).1]
    ring
  have hvel1 : (fun y => AVenhance.streamVel (fun _ => φ) 0 y 1) =
      fun y => AVenhance.spaceGrad φ y 0 := by
    funext y
    exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := y)).2
  have hD0 : classicalWordDerivative w
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y 0) =
      fun y => -AVenhance.spaceGrad (classicalWordDerivative w φ) y 1 := by
    calc
      _ = classicalWordDerivative w
          (fun y => (-1 : ℝ) * AVenhance.spaceGrad φ y 1) := by rw [hvel0]
      _ = fun y => (-1 : ℝ) * classicalWordDerivative w
          (fun y => AVenhance.spaceGrad φ y 1) y :=
            classicalWordDerivative_const_mul w (-1)
              (fun y => AVenhance.spaceGrad φ y 1)
              (by exact (hφ.fderiv_right (by simp)).clm_apply contDiff_const)
      _ = fun y => -AVenhance.spaceGrad (classicalWordDerivative w φ) y 1 := by
        rw [classicalWordDerivative_commute_gradient w φ hφ 1]
        funext y
        ring
  have hD1 : classicalWordDerivative w
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y 1) =
      fun y => AVenhance.spaceGrad (classicalWordDerivative w φ) y 0 := by
    calc
      _ = classicalWordDerivative w (fun y => AVenhance.spaceGrad φ y 0) := by
        rw [hvel1]
      _ = fun y => AVenhance.spaceGrad (classicalWordDerivative w φ) y 0 :=
        classicalWordDerivative_commute_gradient w φ hφ 0
  have hf : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w φ) :=
    classicalWordDerivative_contDiff w φ hφ
  have hgrad0 : AVenhance.spaceGrad (fun y =>
      -AVenhance.spaceGrad (classicalWordDerivative w φ) y 1) x 0 =
      -AVenhance.spaceGrad (fun y =>
        AVenhance.spaceGrad (classicalWordDerivative w φ) y 1) x 0 := by
    have h := classicalSpaceGrad_sub (fun _ : Vec 2 => (0 : ℝ))
      (fun y => AVenhance.spaceGrad (classicalWordDerivative w φ) y 1)
      contDiff_const ((hf.fderiv_right (by simp)).clm_apply contDiff_const) 0 x
    simp [AVenhance.spaceGrad] at h ⊢
  rw [Fin.sum_univ_two]
  rw [hD0, hD1, hgrad0]
  rw [classicalSpaceGrad_commute (classicalWordDerivative w φ) hf 0 1 x]
  ring

/-- Ordered derivatives commute through the stream velocity's single
coordinate gradient. -/
theorem classicalWordDerivative_streamVel_component
    (w : List (Fin 2)) (φ : Vec 2 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin 2) :
    classicalWordDerivative w
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y j) =
        fun y => AVenhance.streamVel
          (fun _ => classicalWordDerivative w φ) 0 y j := by
  have hvel0 : (fun y => AVenhance.streamVel (fun _ => φ) 0 y 0) =
      fun y => (-1 : ℝ) * AVenhance.spaceGrad φ y 1 := by
    funext y
    rw [(ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := y)).1]
    ring
  have hvel1 : (fun y => AVenhance.streamVel (fun _ => φ) 0 y 1) =
      fun y => AVenhance.spaceGrad φ y 0 := by
    funext y
    exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := y)).2
  have hD0 : classicalWordDerivative w
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y 0) =
      fun y => -AVenhance.spaceGrad (classicalWordDerivative w φ) y 1 := by
    calc
      _ = classicalWordDerivative w
          (fun y => (-1 : ℝ) * AVenhance.spaceGrad φ y 1) := by rw [hvel0]
      _ = fun y => (-1 : ℝ) * classicalWordDerivative w
          (fun y => AVenhance.spaceGrad φ y 1) y :=
            classicalWordDerivative_const_mul w (-1)
              (fun y => AVenhance.spaceGrad φ y 1)
              (by exact (hφ.fderiv_right (by simp)).clm_apply contDiff_const)
      _ = fun y => -AVenhance.spaceGrad (classicalWordDerivative w φ) y 1 := by
        rw [classicalWordDerivative_commute_gradient w φ hφ 1]
        funext y
        ring
  have hD1 : classicalWordDerivative w
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y 1) =
      fun y => AVenhance.spaceGrad (classicalWordDerivative w φ) y 0 := by
    calc
      _ = classicalWordDerivative w (fun y => AVenhance.spaceGrad φ y 0) := by
        rw [hvel1]
      _ = fun y => AVenhance.spaceGrad (classicalWordDerivative w φ) y 0 :=
        classicalWordDerivative_commute_gradient w φ hφ 0
  funext y
  fin_cases j
  · change classicalWordDerivative w
        (fun y => AVenhance.streamVel (fun _ => φ) 0 y 0) y =
      AVenhance.streamVel (fun _ => classicalWordDerivative w φ) 0 y 0
    rw [hD0]
    exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components
      (φ := classicalWordDerivative w φ) (x := y)).1.symm
  · change classicalWordDerivative w
        (fun y => AVenhance.streamVel (fun _ => φ) 0 y 1) y =
      AVenhance.streamVel (fun _ => classicalWordDerivative w φ) 0 y 1
    rw [hD1]
    exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components
      (φ := classicalWordDerivative w φ) (x := y)).2.symm

/-- Smoothness of the vector field generated by a smooth stream function. -/
theorem theta_streamVel_contDiff (φ : Vec 2 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel (fun _ => φ) 0) := by
  apply contDiff_pi.2
  intro j
  fin_cases j
  · change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.streamVel (fun _ => φ) 0 x 0)
    have heq : (fun x => AVenhance.streamVel (fun _ => φ) 0 x 0) =
        fun x => -AVenhance.spaceGrad φ x 1 := by
      funext x
      exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := x)).1
    rw [heq]
    exact (ThetaDifferentiated.thetaSpaceGradComponent_contDiff hφ 1).neg
  · change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.streamVel (fun _ => φ) 0 x 1)
    have heq : (fun x => AVenhance.streamVel (fun _ => φ) 0 x 1) =
        fun x => AVenhance.spaceGrad φ x 0 := by
      funext x
      exact (ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := x)).2
    rw [heq]
    exact ThetaDifferentiated.thetaSpaceGradComponent_contDiff hφ 0

theorem ThetaDifferentiated.theta_spaceGrad_component_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : AVenhance.IsZ2Periodic f) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i) := by
  intro k x
  let v : Vec 2 := AVenhance.latticeShift k
  have hfun : (fun y : Vec 2 => f (y + v)) = f := by
    funext y
    exact hper k y
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htranslate : HasFDerivAt (fun y : Vec 2 => y + v)
      (ContinuousLinearMap.id ℝ (Vec 2)) x := by
    simpa only [id_eq] using (hasFDerivAt_id x).add_const v
  have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
  have hshift : HasFDerivAt f (fderiv ℝ f (x + v)) x := by
    have hcomp' := hcomp
    change HasFDerivAt (fun y : Vec 2 => f (y + v))
      (fderiv ℝ f (x + v) ∘L ContinuousLinearMap.id ℝ (Vec 2)) x at hcomp'
    rw [ContinuousLinearMap.comp_id, hfun] at hcomp'
    exact hcomp'
  have hbase : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x).hasFDerivAt
  have hderiv : fderiv ℝ f (x + v) = fderiv ℝ f x := hshift.unique hbase
  change fderiv ℝ f (x + AVenhance.latticeShift k)
      (Homogenization.basisVec i) = fderiv ℝ f x (Homogenization.basisVec i)
  exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i)) hderiv

/-- Ordered coordinate derivatives preserve spatial periodicity. -/
theorem classicalWordDerivative_periodic (w : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w generalizing f with
  | nil => exact hper
  | cons i w ih =>
      have htailSmooth := classicalWordDerivative_contDiff w f hf
      exact ThetaDifferentiated.theta_spaceGrad_component_periodic htailSmooth (ih hf hper) i

/-- Spatial periodicity of a stream velocity follows by differentiating the
periodicity of its scalar stream function. -/
theorem theta_streamVel_periodic (φ : Vec 2 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hper : AVenhance.IsZ2Periodic φ) :
    AVenhance.IsZ2Periodic (AVenhance.streamVel (fun _ => φ) 0) := by
  have hgrad (j : Fin 2) :
      AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad φ x j) := by
    simpa [classicalWordDerivative, Classical.classicalWordDerivative] using
      (classicalWordDerivative_periodic [j] hφ hper)
  intro k x
  have hvx := ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ) (x := x)
  have hvshift := ThetaDifferentiated.thetaDifferentiated_streamVel_components
    (φ := φ) (x := x + AVenhance.latticeShift k)
  funext j
  fin_cases j
  · change AVenhance.streamVel (fun _ => φ) 0
      (x + AVenhance.latticeShift k) 0 =
        AVenhance.streamVel (fun _ => φ) 0 x 0
    rw [hvshift.1, hvx.1]
    exact congrArg Neg.neg (hgrad 1 k x)
  · change AVenhance.streamVel (fun _ => φ) 0
      (x + AVenhance.latticeShift k) 1 =
        AVenhance.streamVel (fun _ => φ) 0 x 1
    rw [hvshift.2, hvx.2]
    exact hgrad 0 k x

theorem ThetaDifferentiated.theta_list_map_sum_congr {α : Type*} (L : List α)
    (f g : α → ℝ) (h : ∀ a ∈ L, f a = g a) :
    (L.map f).sum = (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      have htail : ∀ z ∈ L, f z = g z := by
        intro z hz
        exact h z (by simp [hz])
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp), ih htail]

/-- The stream velocity is jointly smooth on positive time, using the smooth
joint stream potential and its spatial Fréchet derivatives. -/
theorem theta_streamVel_joint_contDiffOn {φ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (AVenhance.streamVel φ))
      classicalPositiveTimeDomain := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (AVenhance.streamVel φ))
    ThetaDifferentiated.thetaJointPositiveDomain
  have hφOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      ThetaDifferentiated.thetaJointPositiveDomain := by
    exact hφ.1.contDiffOn
  have hderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fderiv ℝ (Function.uncurry φ)) ThetaDifferentiated.thetaJointPositiveDomain :=
    (contDiffOn_infty_iff_fderiv_of_isOpen
      (isOpen_Ioi.prod isOpen_univ)).1 hφOpen |>.2
  have hpartial (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => fderiv ℝ (Function.uncurry φ) p
        (0, Homogenization.basisVec i)) ThetaDifferentiated.thetaJointPositiveDomain := by
    exact hderiv.clm_apply contDiffOn_const
  apply contDiffOn_pi.2
  intro j
  fin_cases j
  · apply (hpartial 1).neg.congr
    intro p hp
    rcases p with ⟨t, x⟩
    have ht : 0 < t := by
      simpa [ThetaDifferentiated.thetaJointPositiveDomain] using hp.1
    have hvel := ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ t) (x := x)
    change AVenhance.streamVel φ t x 0 = _
    rw [show AVenhance.streamVel φ t x 0 =
        AVenhance.streamVel (fun _ => φ t) 0 x 0 from rfl,
      hvel.1, theta_joint_spatial_section_derivative hφOpen ht x 1]
  · apply (hpartial 0).congr
    intro p hp
    rcases p with ⟨t, x⟩
    have ht : 0 < t := by
      simpa [ThetaDifferentiated.thetaJointPositiveDomain] using hp.1
    have hvel := ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := φ t) (x := x)
    change AVenhance.streamVel φ t x 1 = _
    rw [show AVenhance.streamVel φ t x 1 =
        AVenhance.streamVel (fun _ => φ t) 0 x 1 from rfl,
      hvel.2, theta_joint_spatial_section_derivative hφOpen ht x 0]

/-- A single stream-form Leibniz term in the differentiated divergence
operator. -/
def thetaStreamCommutatorProductTerm (p : List (Fin 2) × List (Fin 2))
    (φ u : Vec 2 → ℝ) : Vec 2 → Vec 2 :=
  fun x j => classicalWordDerivative p.1 φ x *
    AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0 x j

/-- The stream-function flux in the ordered-word commutator expansion. -/
def thetaStreamCommutatorFlux (w : List (Fin 2))
    (φ u : Vec 2 → ℝ) : Vec 2 → Vec 2 :=
  fun x j => ((classicalWordCommutatorSplits w).map fun p =>
    thetaStreamCommutatorProductTerm p φ u x j).sum

theorem theta_product_vector_divergence
    {g : Vec 2 → ℝ} {v : Vec 2 → Vec 2}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hdiv : ∀ x, AVenhance.vecDiv v x = 0) (x : Vec 2) :
    AVenhance.vecDiv (fun y j => g y * v y j) x =
      vecDot (AVenhance.spaceGrad g x) (v x) := by
  have hcomp (j : Fin 2) (x : Vec 2) :
      AVenhance.spaceGrad (fun y => g y * v y j) x j =
        g x * AVenhance.spaceGrad (fun y => v y j) x j +
          AVenhance.spaceGrad g x j * v x j := by
    exact classicalProduct_firstDerivative g (fun y => v y j) hg
      (contDiff_pi.mp hv j) j x
  unfold AVenhance.vecDiv
  rw [Fin.sum_univ_two]
  rw [hcomp 0 x, hcomp 1 x]
  have hdiv' := hdiv x
  unfold AVenhance.vecDiv at hdiv'
  rw [Fin.sum_univ_two] at hdiv'
  change AVenhance.spaceGrad (fun y => v y 0) x 0 +
      AVenhance.spaceGrad (fun y => v y 1) x 1 = 0 at hdiv'
  simp only [vecDot, Fin.sum_univ_two]
  calc
    _ = g x * (AVenhance.spaceGrad (fun y => v y 0) x 0 +
          AVenhance.spaceGrad (fun y => v y 1) x 1) +
        AVenhance.spaceGrad g x 0 * v x 0 +
        AVenhance.spaceGrad g x 1 * v x 1 := by ring
    _ = _ := by rw [hdiv']; ring

theorem ThetaDifferentiated.theta_streamVel_dot_grad_skew
    (g h : Vec 2 → ℝ) (x : Vec 2) :
    vecDot (AVenhance.spaceGrad g x)
        (AVenhance.streamVel (fun _ => h) 0 x) =
      -vecDot (AVenhance.streamVel (fun _ => g) 0 x)
        (AVenhance.spaceGrad h x) := by
  have hg := ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := g) (x := x)
  have hh := ThetaDifferentiated.thetaDifferentiated_streamVel_components (φ := h) (x := x)
  simp [Homogenization.vecDot, Fin.sum_univ_two, hg.1, hg.2, hh.1, hh.2]

theorem ThetaDifferentiated.thetaStreamCommutatorProductTerm_contDiff
    (p : List (Fin 2) × List (Fin 2)) (φ u : Vec 2 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaStreamCommutatorProductTerm p φ u) := by
  apply contDiff_pi.2
  intro j
  exact (classicalWordDerivative_contDiff p.1 φ hφ).mul <|
    contDiff_pi.mp (theta_streamVel_contDiff (classicalWordDerivative p.2 u)
      (classicalWordDerivative_contDiff p.2 u hu)) j

/-- The stream commutator flux is smooth and periodic whenever its two scalar
inputs are. -/
theorem thetaStreamCommutatorFlux_contDiff_periodic
    (w : List (Fin 2)) {φ u : Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hφper : AVenhance.IsZ2Periodic φ) (huper : AVenhance.IsZ2Periodic u) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaStreamCommutatorFlux w φ u) ∧
      AVenhance.IsZ2Periodic (thetaStreamCommutatorFlux w φ u) := by
  have htermSmooth (j : Fin 2) : ∀ f ∈
      (classicalWordCommutatorSplits w).map fun p =>
        fun x => thetaStreamCommutatorProductTerm p φ u x j,
      ContDiff ℝ (⊤ : ℕ∞) f := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact contDiff_pi.mp (ThetaDifferentiated.thetaStreamCommutatorProductTerm_contDiff p φ u hφ
        hu) j
  have hvelPer (p : List (Fin 2) × List (Fin 2)) :
      AVenhance.IsZ2Periodic
        (AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0) :=
    theta_streamVel_periodic (classicalWordDerivative p.2 u)
      (classicalWordDerivative_contDiff p.2 u hu)
      (classicalWordDerivative_periodic p.2 hu huper)
  constructor
  · apply contDiff_pi.2
    intro j
    change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ((classicalWordCommutatorSplits w).map fun p =>
        thetaStreamCommutatorProductTerm p φ u x j).sum)
    let Terms : List (Vec 2 → ℝ) :=
      (classicalWordCommutatorSplits w).map fun p =>
        fun x => thetaStreamCommutatorProductTerm p φ u x j
    have heq : (fun x => ((classicalWordCommutatorSplits w).map fun p =>
        thetaStreamCommutatorProductTerm p φ u x j).sum) =
        Terms.sum := by
      funext x
      calc
        _ = (Terms.map fun f => f x).sum := by
          simp only [Terms, List.map_map, Function.comp_def]
        _ = Terms.sum x := (classicalListSum_eval Terms x).symm
    rw [heq]
    exact classicalContDiff_listSum Terms (by
      intro f hf
      dsimp [Terms] at hf
      exact htermSmooth j f hf)
  · intro k x
    funext j
    apply ThetaDifferentiated.theta_list_map_sum_congr
    intro p hp
    have hleft := classicalWordDerivative_periodic p.1 hφ hφper
    have hright := hvelPer p
    simp [thetaStreamCommutatorProductTerm, hleft k x,
      congrFun (hright k x) j]

/-- Divergence of the differentiated stream flux is the negative transport
commutator. This is the source's skew-symmetric divergence form; it avoids one
unnecessary derivative on the stream potential. -/
theorem thetaStreamCommutatorFlux_divergence
    (w : List (Fin 2)) (φ u : Vec 2 → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x : Vec 2) :
    AVenhance.vecDiv (thetaStreamCommutatorFlux w φ u) x =
      -∑ j : Fin 2,
        classicalWordCommutatorExpansion w
          (fun y => AVenhance.streamVel (fun _ => φ) 0 y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
  let L := classicalWordCommutatorSplits w
  have hterms (j : Fin 2) : ∀ f ∈ L.map fun p =>
      fun y => thetaStreamCommutatorProductTerm p φ u y j,
      ContDiff ℝ (⊤ : ℕ∞) f := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact contDiff_pi.mp (ThetaDifferentiated.thetaStreamCommutatorProductTerm_contDiff p φ u hφ
        hu) j
  have hderiv (j : Fin 2) :
      AVenhance.spaceGrad (fun y => thetaStreamCommutatorFlux w φ u y j) x j =
        (L.map fun p => AVenhance.spaceGrad
          (fun y => thetaStreamCommutatorProductTerm p φ u y j) x j).sum := by
    let Terms : List (Vec 2 → ℝ) := L.map fun p =>
      fun y => thetaStreamCommutatorProductTerm p φ u y j
    have heq : (fun y => thetaStreamCommutatorFlux w φ u y j) =
        Terms.sum := by
      funext y
      calc
        thetaStreamCommutatorFlux w φ u y j =
            (Terms.map fun f => f y).sum := by
          simp only [thetaStreamCommutatorFlux, Terms, L,
            List.map_map, Function.comp_def]
        _ = Terms.sum y := (classicalListSum_eval Terms y).symm
    rw [heq]
    have hs := classicalSpaceGrad_listSum Terms (by
      intro f hf
      dsimp [Terms] at hf
      exact hterms j f hf) j x
    simpa only [Terms, List.map_map, Function.comp_def] using hs
  have hfluxDiv : AVenhance.vecDiv (thetaStreamCommutatorFlux w φ u) x =
      (L.map fun p => vecDot
        (AVenhance.spaceGrad (classicalWordDerivative p.1 φ) x)
        (AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0 x)).sum := by
    have hdivEq : AVenhance.vecDiv (thetaStreamCommutatorFlux w φ u) x =
        ∑ j : Fin 2, (L.map fun p =>
          AVenhance.spaceGrad
            (fun y => thetaStreamCommutatorProductTerm p φ u y j) x j).sum := by
      unfold AVenhance.vecDiv
      apply Finset.sum_congr rfl
      intro j hj
      exact hderiv j
    rw [hdivEq, ThetaDifferentiated.list_sum_fin_sum_swap]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hdivC : ∀ y, AVenhance.vecDiv
        (AVenhance.streamVel
          (fun _ => classicalWordDerivative p.2 u) 0) y = 0 := by
      intro y
      have hdiv := theta_streamVel_ordered_derivative_divergence_free
        (classicalWordDerivative p.2 u)
        (classicalWordDerivative_contDiff p.2 u hu) [] y
      simpa [AVenhance.vecDiv, classicalWordDerivative, Classical.classicalWordDerivative]
        using hdiv
    have hdivProduct := theta_product_vector_divergence
      (classicalWordDerivative_contDiff p.1 φ hφ)
      (theta_streamVel_contDiff (classicalWordDerivative p.2 u)
        (classicalWordDerivative_contDiff p.2 u hu)) hdivC x
    change AVenhance.vecDiv
        (fun y j => classicalWordDerivative p.1 φ y *
          AVenhance.streamVel
            (fun _ => classicalWordDerivative p.2 u) 0 y j) x = _
    exact hdivProduct
  let G : Fin 2 → List (Fin 2) × List (Fin 2) → ℝ := fun j p =>
    AVenhance.streamVel (fun _ => classicalWordDerivative p.1 φ) 0 x j *
      AVenhance.spaceGrad (classicalWordDerivative p.2 u) x j
  have hdotTerm (p : List (Fin 2) × List (Fin 2)) :
      vecDot (AVenhance.spaceGrad (classicalWordDerivative p.1 φ) x)
        (AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0 x) =
      -∑ j : Fin 2, G j p := by
    simpa [G, vecDot, Fin.sum_univ_two] using
      ThetaDifferentiated.theta_streamVel_dot_grad_skew
        (classicalWordDerivative p.1 φ) (classicalWordDerivative p.2 u) x
  have hdotMap :
      (L.map fun p => vecDot
        (AVenhance.spaceGrad (classicalWordDerivative p.1 φ) x)
        (AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0 x)).sum =
      - (L.map fun p => ∑ j : Fin 2, G j p).sum := by
    have hneg (K : List (List (Fin 2) × List (Fin 2))) :
        (K.map fun p => -(∑ j : Fin 2, G j p)).sum =
          -(K.map fun p => ∑ j : Fin 2, G j p).sum := by
      induction K with
      | nil => simp
      | cons p K ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          ring
    calc
      _ = (L.map fun p => -(∑ j : Fin 2, G j p)).sum := by
        apply ThetaDifferentiated.theta_list_map_sum_congr
        intro p hp
        exact hdotTerm p
      _ = - (L.map fun p => ∑ j : Fin 2, G j p).sum := hneg L
  have hswap := ThetaDifferentiated.list_sum_fin_sum_swap L G
  have hcommj (j : Fin 2) :
      (L.map fun p => G j p).sum =
        classicalWordCommutatorExpansion w
          (fun y => AVenhance.streamVel (fun _ => φ) 0 y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
    unfold classicalWordCommutatorExpansion Classical.classicalWordCommutatorExpansion
    rw [classicalListSum_eval]
    simp only [List.map_map, Function.comp_def]
    apply ThetaDifferentiated.theta_list_map_sum_congr
    intro p hp
    have hbderiv (j : Fin 2) :
        classicalWordDerivative p.1
          (fun y => AVenhance.streamVel (fun _ => φ) 0 y j) x =
        AVenhance.streamVel (fun _ => classicalWordDerivative p.1 φ) 0 x j := by
      exact congrFun (classicalWordDerivative_streamVel_component p.1 φ hφ j) x
    have hgradderiv (j : Fin 2) :
        classicalWordDerivative p.2 (fun y => AVenhance.spaceGrad u y j) x =
          AVenhance.spaceGrad (classicalWordDerivative p.2 u) x j :=
      congrFun (classicalWordDerivative_commute_gradient p.2 u hu j) x
    change G j p = classicalWordDerivative p.1
      (fun y => AVenhance.streamVel (fun _ => φ) 0 y j) x *
        classicalWordDerivative p.2 (fun y => AVenhance.spaceGrad u y j) x
    rw [hbderiv, hgradderiv]
  have hcomm :
      (L.map fun p => vecDot
        (AVenhance.spaceGrad (classicalWordDerivative p.1 φ) x)
        (AVenhance.streamVel (fun _ => classicalWordDerivative p.2 u) 0 x)).sum =
      -∑ j : Fin 2,
        classicalWordCommutatorExpansion w
          (fun y => AVenhance.streamVel (fun _ => φ) 0 y j)
          (fun y => AVenhance.spaceGrad u y j) x := by
    calc
      _ = - (L.map fun p => ∑ j : Fin 2, G j p).sum := hdotMap
      _ = -(∑ j : Fin 2, (L.map fun p => G j p).sum) := by rw [hswap.symm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact hcommj j
  rw [hfluxDiv, hcomm]

end AVenhance.Infra.Section4
