/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC3All
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportCalculus

/-! # RelativeError: the transported scalar test along a smooth flow

The inverse flow transports initial data by characteristics. Joint C³
regularity of the flow supplies the C² regularity needed by the pairing lemma.
-/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical

/-- Pull a smooth scalar back along the inverse of the time-zero forward flow. -/
def inverseFlowTransportTest {h₀ : Vec 2 → ℝ}
    (X : ℝ → Vec 2 → ℝ → Vec 2) : ℝ → Vec 2 → ℝ :=
  fun t x => h₀ (X 0 x t)

/-- The inverse-flow pullback is a smooth periodic solution of the homogeneous
transport equation. Only C² regularity is recorded; this is sufficient for
the parabolic pairing and the periodic integration by parts used there. -/
theorem inverseFlowTransportTest_isClassicalTransportTest
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {h₀ : Vec 2 → ℝ} (hh₀ : ContDiff ℝ (⊤ : ℕ∞) h₀)
    (hh₀per : IsZ2Periodic h₀) :
    IsClassicalTransportTest b (inverseFlowTransportTest (h₀ := h₀) X) := by
  let h : ℝ → Vec 2 → ℝ := fun t x => h₀ (X 0 x t)
  have hflowSmooth : ContDiff ℝ 2
      (fun p : ℝ × Vec 2 => X 0 p.2 p.1) := by
    have hparam : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => (p.1, p.2, (0 : ℝ))) := by
      fun_prop
    change ContDiff ℝ 2
      ((fun q : ℝ × Vec 2 × ℝ => X q.2.2 q.2.1 q.1) ∘
        fun p : ℝ × Vec 2 => (p.1, p.2, (0 : ℝ)))
    exact (Infra.Flow.flow_inverse_joint_contDiff_three_all hb hX).of_le
      (by norm_num) |>.comp hparam
  have hh : ContDiff ℝ 2 (Function.uncurry h) := by
    change ContDiff ℝ 2 (fun p : ℝ × Vec 2 => h₀ (X 0 p.2 p.1))
    exact (hh₀.of_le (by norm_num)).comp hflowSmooth
  have hLip : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖ := by
    obtain ⟨L, hL0, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz hb
    exact ⟨L, hL⟩
  have hbper (t : ℝ) : IsZ2Periodic (b t) := by
    intro k x
    simpa using hb.periodic 0 k t x
  have hhper (t : ℝ) : IsZ2Periodic (h t) := by
    intro k x
    dsimp [h, inverseFlowTransportTest]
    rw [Infra.Flow.flow_lattice_equivariant b hLip hbper hX
      x t 0 k]
    exact hh₀per k (X 0 x t)
  let F : ℝ → Vec 2 → ℝ := fun _ y => h₀ y
  let Z : ℝ → Vec 2 → Vec 2 := fun r y => X 0 y r
  have hFsmooth : ContDiff ℝ 2 (Function.uncurry F) := by
    change ContDiff ℝ 2 (fun p : ℝ × Vec 2 => h₀ p.2)
    exact (hh₀.of_le (by norm_num)).comp contDiff_snd
  have hZsmooth : ContDiff ℝ 2 (Function.uncurry Z) := hflowSmooth
  have hleft : ∀ r y, Z r (X r y 0) = y := by
    intro r y
    dsimp [Z]
    calc
      X 0 (X r y 0) r = X 0 y 0 :=
        Infra.Flow.flow_group_law b hLip hX y 0 r 0
      _ = y := hX.1 y 0
  have hright : ∀ r y, X r (Z r y) 0 = y := by
    intro r y
    dsimp [Z]
    calc
      X r (X 0 y r) 0 = X r y r :=
        Infra.Flow.flow_group_law b hLip hX y r 0 r
      _ = y := hX.1 y r
  refine ⟨hh, fun t _ => hhper t, ?_⟩
  intro t ht x
  have hFderiv : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (t, Z t x)) (t, Z t x) :=
    (hFsmooth.differentiable (by simp) (t, Z t x)).hasFDerivAt
  have hZderiv : HasFDerivAt (Function.uncurry Z)
      (fderiv ℝ (Function.uncurry Z) (t, x)) (t, x) :=
    (hZsmooth.differentiable (by simp) (t, x)).hasFDerivAt
  have hinverseTransport := inverse_flow_transport_comp
    (b := b) (X := X) (F := F) (Z := Z) (s := 0) (t := t) (x := x)
    (L := fderiv ℝ (Function.uncurry F) (t, Z t x))
    (M := fderiv ℝ (Function.uncurry Z) (t, x))
    hFderiv hZderiv hX hleft hright
  have hLzero :
      (fderiv ℝ (Function.uncurry F) (t, Z t x)) (1, 0) = 0 := by
    have hline : HasDerivAt (fun r : ℝ => (r, Z t x)) (1, 0) t := by
      convert (hasDerivAt_id t).prodMk (hasDerivAt_const t (Z t x)) using 1
      simp
    have hcomp := hFderiv.comp_hasDerivAt t hline
    have hderiv : HasDerivAt (fun r => F r (Z t x))
        ((fderiv ℝ (Function.uncurry F) (t, Z t x)) (1, 0)) t := by
      simpa [Function.uncurry, Function.comp_def] using hcomp
    have hconst : HasDerivAt (fun r => F r (Z t x)) 0 t := by
      simpa [F] using (hasDerivAt_const t (h₀ (Z t x)))
    exact hderiv.unique hconst
  have hflowEquation :
      deriv (fun r => h r x) t + fderiv ℝ (h t) x (b t x) = 0 := by
    have htransport :
        deriv (fun r => F r (Z r x)) t +
          fderiv ℝ (fun y => F t (Z t y)) x (b t x) =
            (fderiv ℝ (Function.uncurry F) (t, Z t x)) (1, 0) := by
      simpa [F, Z] using hinverseTransport
    simpa [h, F, Z, inverseFlowTransportTest, hLzero] using htransport
  have htime :
      deriv (fun r => h r x) t = classicalTimePartial h (t, x) := by
    have hdomain : ContDiffOn ℝ 2 (Function.uncurry h)
        classicalPositiveTimeDomain := hh.contDiffOn.mono (Set.subset_univ _)
    exact (classicalTimeSection_hasDerivAt_of_C2 hdomain ht x).deriv
  have hspace : fderiv ℝ (h t) x (b t x) =
      vecDot (b t x) (spaceGrad (h t) x) := by
    have hdecomp : b t x =
        ∑ i : Fin 2, b t x i • basisVec i := by
      ext i
      fin_cases i <;> simp [basisVec, Fin.sum_univ_two]
    rw [hdecomp, map_sum]
    simp [vecDot, spaceGrad, Fin.sum_univ_two, smul_eq_mul]
  change classicalTimePartial h (t, x) +
    vecDot (b t x) (spaceGrad (h t) x) = 0
  rw [← htime, ← hspace]
  exact hflowEquation

end AVenhance.Infra.Section5.RelativeError

end
