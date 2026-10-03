/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Drift
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Data.List.OfFn

/-! Joint space-time bounds for ordered spatial derivatives of smooth periodic data. -/

@[expose] public section

noncomputable section

open Set
open Homogenization

namespace AVenhance.Infra.Classical

/-- Finite indices for all ordered coordinate-derivative words of length at most `s`. -/
abbrev ClassicalDerivativeWordIndex (s : ℕ) :=
  Σ n : Fin (s + 1), Fin n → Fin 2

/-- Convert a finite derivative index to its ordered coordinate word. -/
def classicalDerivativeWordOfIndex {s : ℕ}
    (a : ClassicalDerivativeWordIndex s) : List (Fin 2) := List.ofFn a.2

theorem classicalDerivativeWordOfIndex_length_le {s : ℕ}
    (a : ClassicalDerivativeWordIndex s) :
    (classicalDerivativeWordOfIndex a).length ≤ s := by
  simp only [classicalDerivativeWordOfIndex, List.length_ofFn]
  exact Nat.le_of_lt_succ a.1.isLt

/-- Every ordered coordinate word of length at most `s` has a finite derivative index. -/
def classicalDerivativeWordIndexOfList {s : ℕ}
    (w : List (Fin 2)) (hw : w.length ≤ s) : ClassicalDerivativeWordIndex s :=
  ⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩

theorem classicalDerivativeWordOfIndexOfList {s : ℕ}
    (w : List (Fin 2)) (hw : w.length ≤ s) :
    classicalDerivativeWordOfIndex (classicalDerivativeWordIndexOfList w hw) = w := by
  simp [classicalDerivativeWordOfIndex, classicalDerivativeWordIndexOfList,
    List.ofFn_get]

/-- Joint time-space domain with nonnegative time, including the initial trace. -/
def classicalHalfSpace : Set (ℝ × Vec 2) :=
  Set.Ici (0 : ℝ) ×ˢ Set.univ

theorem GalerkinBounds.classicalHalfSpace_uniqueDiff : UniqueDiffOn ℝ classicalHalfSpace := by
  exact uniqueDiffOn_Ici 0 |>.prod uniqueDiffOn_univ

theorem GalerkinBounds.classicalWordDerivative_periodic_aux (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

/-- Repeated spatial directional derivatives of a joint space-time scalar, taken using the
within-derivative on the nonnegative-time domain. -/
def classicalJointWordDerivative (w : List (Fin 2))
    (f : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  match w with
  | [] => f
  | i :: w => fun p => fderivWithin ℝ (classicalJointWordDerivative w f)
      classicalHalfSpace p (0, Homogenization.basisVec i)

theorem classicalJointWordDerivative_contDiffOn (w : List (Fin 2))
    (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f classicalHalfSpace) :
    ContDiffOn ℝ (⊤ : ℕ∞) (classicalJointWordDerivative w f) classicalHalfSpace := by
  induction w generalizing f with
  | nil => exact hf
  | cons i w ih =>
      have hprev := ih f hf
      have hdf : ContDiffOn ℝ (⊤ : ℕ∞)
          (fderivWithin ℝ (classicalJointWordDerivative w f)
            classicalHalfSpace) classicalHalfSpace :=
        hprev.fderivWithin GalerkinBounds.classicalHalfSpace_uniqueDiff (by simp)
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p => fderivWithin ℝ (classicalJointWordDerivative w f)
          classicalHalfSpace p (0, Homogenization.basisVec i))
        classicalHalfSpace
      exact hdf.clm_apply contDiffOn_const

theorem GalerkinBounds.classicalJointSection_directional_derivative
    (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f classicalHalfSpace)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (fun y => f (t, y)) x i =
      fderivWithin ℝ f classicalHalfSpace (t, x)
        (0, Homogenization.basisVec i) := by
  let S : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hpoint : (t, x) ∈ classicalHalfSpace := by
    exact ⟨ht, Set.mem_univ _⟩
  have hS : HasFDerivAt S (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) x := by
    exact hasFDerivAt_prodMk_right t x
  have hSdiff : DifferentiableWithinAt ℝ S Set.univ x :=
    hS.differentiableAt.differentiableWithinAt
  have hmaps : MapsTo S Set.univ classicalHalfSpace := by
    intro y hy
    exact ⟨ht, Set.mem_univ _⟩
  have hfD : DifferentiableWithinAt ℝ f classicalHalfSpace (S x) :=
    (hf.differentiableOn (by simp)) (S x) hpoint
  have hcomp := fderivWithin_comp (g := f) (f := S)
    (t := classicalHalfSpace) (s := Set.univ) (x := x)
    hfD hSdiff hmaps uniqueDiffWithinAt_univ
  have hSx : S x = (t, x) := rfl
  rw [hSx] at hcomp
  have hSderiv : fderivWithin ℝ S Set.univ x =
      ContinuousLinearMap.inr ℝ ℝ (Vec 2) :=
    hS.hasFDerivWithinAt.fderivWithin uniqueDiffWithinAt_univ
  rw [show (fun y : Vec 2 => f (t, y)) = f ∘ S by rfl]
  change fderiv ℝ (f ∘ S) x (Homogenization.basisVec i) = _
  rw [← fderivWithin_univ, hcomp, hSderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- On every nonnegative-time slice, the joint within-derivative agrees with the ordinary ordered
spatial derivative used by the Galerkin commutator calculus. -/
theorem classicalJointWordDerivative_eq_slice (w : List (Fin 2))
    (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f classicalHalfSpace)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec 2) :
    classicalJointWordDerivative w f (t, x) =
      classicalWordDerivative w (fun y => f (t, y)) x := by
  revert t ht x
  induction w generalizing f with
  | nil => intro t ht x; rfl
  | cons i w ih =>
      intro t ht x
      have hdf : ContDiffOn ℝ (⊤ : ℕ∞)
          (classicalJointWordDerivative w f) classicalHalfSpace :=
        classicalJointWordDerivative_contDiffOn w f hf
      have hprev (y : Vec 2) := ih f hf ht y
      have hprevFun : (fun y : Vec 2 => classicalJointWordDerivative w f (t, y)) =
          classicalWordDerivative w (fun y => f (t, y)) := by
        funext y
        exact hprev y
      have hsection := GalerkinBounds.classicalJointSection_directional_derivative
        (classicalJointWordDerivative w f) hdf ht x i
      simpa [classicalJointWordDerivative, hprevFun, classicalWordDerivative] using hsection.symm

/-- A continuous function periodic in its spatial argument is uniformly bounded on a unit time
interval times all of space. -/
theorem exists_uniform_bound_of_continuous_spatiallyPeriodic
    (f : ℝ × Vec 2 → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1 ×ˢ
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)))
    (hper : ∀ t, 0 ≤ t → ∀ k x,
      f (t, x + AVenhance.latticeShift k) = f (t, x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖f (t, x)‖ ≤ C := by
  let K : Set (ℝ × Vec 2) := Set.Icc (0 : ℝ) 1 ×ˢ
    Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    simpa [K] using isCompact_Icc.prod
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  let g : ℝ × Vec 2 → ℝ := fun p => ‖f p‖
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1 ×ˢ
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    continuous_norm.comp_continuousOn hf
  have hupper : BddAbove (g '' K) := hKcompact.bddAbove_image hg
  let C₀ : ℝ := sSup (g '' K)
  have hnonempty : (g '' K).Nonempty := by
    let x0 : Vec 2 := fun _ => 0
    have hx0 : (0, x0) ∈ K := by
      constructor
      · norm_num
      · intro i hi
        simp [x0]
    exact ⟨g (0, x0), (0, x0), hx0, rfl⟩
  have hbound (p : ℝ × Vec 2) (hp : p ∈ K) : g p ≤ C₀ :=
    le_csSup hupper ⟨p, hp, rfl⟩
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro t ht x
  let k : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let y : Vec 2 := x + AVenhance.latticeShift k
  have hyi (i : Fin 2) : y i = x i - (Int.floor (x i) : ℝ) := by
    dsimp [y, k, AVenhance.latticeShift]
    rw [Int.cast_neg]
    exact Int.self_sub_floor (a := (x i : ℝ))
  have hy : y ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    intro i
    rw [hyi]
    constructor
    · exact sub_nonneg.mpr (Int.floor_le (x i))
    · have hfloor := Int.lt_floor_add_one (x i)
      linarith
  have hp : (t, y) ∈ K := ⟨ht, hy⟩
  calc
    ‖f (t, x)‖ = ‖f (t, y)‖ := by rw [← hper t ht.1 k x]
    _ ≤ C₀ := hbound (t, y) hp
    _ ≤ max C₀ 0 := le_max_left _ _

/-- Smooth joint half-space data and spatial periodicity give uniform bounds for every ordered
spatial derivative on `[0,1] × Vec 2`. -/
theorem classicalWordDerivative_uniform_bound (w : List (Fin 2))
    (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f classicalHalfSpace)
    (hper : ∀ t, 0 ≤ t → ∀ k x, f (t, x + AVenhance.latticeShift k) = f (t, x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖classicalWordDerivative w (fun y => f (t, y)) x‖ ≤ C := by
  have hjoint : ContDiffOn ℝ (⊤ : ℕ∞)
      (classicalJointWordDerivative w f) classicalHalfSpace :=
    classicalJointWordDerivative_contDiffOn w f hf
  have hcont : ContinuousOn (classicalJointWordDerivative w f)
      (Set.Icc (0 : ℝ) 1 ×ˢ
        Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) := by
    apply hjoint.continuousOn.mono
    intro p hp
    exact ⟨hp.1.1, Set.mem_univ _⟩
  have hjointPer (t : ℝ) (ht : 0 ≤ t) (k : Fin 2 → ℤ) (x : Vec 2) :
      classicalJointWordDerivative w f (t, x + AVenhance.latticeShift k) =
        classicalJointWordDerivative w f (t, x) := by
    have hslice : AVenhance.IsZ2Periodic (fun y => f (t, y)) := hper t ht
    have hderived := GalerkinBounds.classicalWordDerivative_periodic_aux w (fun y => f (t, y))
        hslice
    rw [classicalJointWordDerivative_eq_slice w f hf ht (x + AVenhance.latticeShift k),
      classicalJointWordDerivative_eq_slice w f hf ht x]
    exact hderived k x
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_of_continuous_spatiallyPeriodic
      (classicalJointWordDerivative w f) hcont hjointPer
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← classicalJointWordDerivative_eq_slice w f hf ht.1 x]
  exact hbound t ht x

/-- Uniform derivative bounds for an admissible drift component. -/
theorem streamVel_wordDerivative_uniform_bound (φ : ℝ → Vec 2 → ℝ)
    (hφ : AVenhance.IsAdmissibleStream φ) (w : List (Fin 2)) (j : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖classicalWordDerivative w (fun y => AVenhance.streamVel φ t y j) x‖ ≤ C := by
  let f : ℝ × Vec 2 → ℝ := fun p => AVenhance.streamVel φ p.1 p.2 j
  have hjoint : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hb := (streamVel_smoothPeriodic φ hφ).smooth
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => Function.uncurry (AVenhance.streamVel φ) p j) :=
      (contDiff_pi.1 hb) j
    simpa [f, Function.uncurry] using hcoord
  have hper : ∀ t, 0 ≤ t → ∀ k x, f (t, x + AVenhance.latticeShift k) = f (t, x) := by
    intro t ht k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) j =
      AVenhance.streamVel φ t x j
    simpa using congrFun ((streamVel_smoothPeriodic φ hφ).periodic 0 k t x) j
  have hcontOn : ContDiffOn ℝ (⊤ : ℕ∞) f classicalHalfSpace := by
    exact hjoint.contDiffOn
  exact classicalWordDerivative_uniform_bound w f hcontOn hper

/-- Uniform derivative bounds for the smooth periodic forcing. -/
theorem classicalForcingWord_uniform_bound (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) classicalHalfSpace)
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t)) (w : List (Fin 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖classicalWordDerivative w (F t) x‖ ≤ C := by
  have hper : ∀ t, 0 ≤ t → ∀ k x,
      Function.uncurry F (t, x + AVenhance.latticeShift k) =
        Function.uncurry F (t, x) := by
    intro t ht k x
    exact hFper t ht k x
  exact classicalWordDerivative_uniform_bound w (Function.uncurry F) hF hper

/-- A single constant bounds every spatial derivative of the drift through order `s`,
uniformly in the component, time, and space variables. -/
theorem exists_streamVel_allWordDerivative_uniform_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w, w.length ≤ s → ∀ j t,
      t ∈ Set.Icc (0 : ℝ) 1 → ∀ x,
        ‖classicalWordDerivative w (fun y => AVenhance.streamVel φ t y j) x‖ ≤ B := by
  classical
  let C : ClassicalDerivativeWordIndex s × Fin 2 → ℝ := fun q =>
    Classical.choose (streamVel_wordDerivative_uniform_bound φ hφ
      (classicalDerivativeWordOfIndex q.1) q.2)
  have hC (q : ClassicalDerivativeWordIndex s × Fin 2) :
      0 ≤ C q ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖classicalWordDerivative (classicalDerivativeWordOfIndex q.1)
          (fun y => AVenhance.streamVel φ t y q.2) x‖ ≤ C q :=
    Classical.choose_spec (streamVel_wordDerivative_uniform_bound φ hφ
      (classicalDerivativeWordOfIndex q.1) q.2)
  let B : ℝ := ∑ q : ClassicalDerivativeWordIndex s × Fin 2, C q
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun q hq => (hC q).1
  refine ⟨B, hB, ?_⟩
  intro w hw j t ht x
  let q : ClassicalDerivativeWordIndex s × Fin 2 :=
    (classicalDerivativeWordIndexOfList w hw, j)
  have hsingle : C q ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun q hq => (hC q).1) (Finset.mem_univ q)
  have hword := classicalDerivativeWordOfIndexOfList w hw
  simpa [q, hword] using ((hC q).2 t ht x).trans hsingle

/-- A single constant bounds every spatial derivative of the forcing through order `s`,
uniformly on the physical time interval and on all of space. -/
theorem exists_classicalForcing_allWordDerivative_uniform_bound
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) classicalHalfSpace)
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t)) (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w, w.length ≤ s → ∀ t,
      t ∈ Set.Icc (0 : ℝ) 1 → ∀ x,
        ‖classicalWordDerivative w (F t) x‖ ≤ B := by
  classical
  let C : ClassicalDerivativeWordIndex s → ℝ := fun q =>
    Classical.choose (classicalForcingWord_uniform_bound F hF hFper
      (classicalDerivativeWordOfIndex q))
  have hC (q : ClassicalDerivativeWordIndex s) :
      0 ≤ C q ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
        ‖classicalWordDerivative (classicalDerivativeWordOfIndex q) (F t) x‖ ≤ C q :=
    Classical.choose_spec (classicalForcingWord_uniform_bound F hF hFper
      (classicalDerivativeWordOfIndex q))
  let B : ℝ := ∑ q : ClassicalDerivativeWordIndex s, C q
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun q hq => (hC q).1
  refine ⟨B, hB, ?_⟩
  intro w hw t ht x
  let q : ClassicalDerivativeWordIndex s := classicalDerivativeWordIndexOfList w hw
  have hsingle : C q ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun q hq => (hC q).1) (Finset.mem_univ q)
  have hword := classicalDerivativeWordOfIndexOfList w hw
  simpa [q, hword] using ((hC q).2 t ht x).trans hsingle

end AVenhance.Infra.Classical

end
