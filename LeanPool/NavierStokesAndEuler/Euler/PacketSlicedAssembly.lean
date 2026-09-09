/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureJet
public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAssembly

@[expose] public section

/-! Finite packet assembly commutes with the genuine time-within/spatial jets. -/

noncomputable section

namespace EulerPacketPointJets

open EulerFiniteGrades Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SliceDifferentiable (s : Set ℝ) (f : Domain → E) (z : Domain) : Prop :=
  DifferentiableWithinAt ℝ (fun t => f (t,z.2)) s z.1 ∧
    DifferentiableAt ℝ (fun y => f (z.1,y)) z.2

theorem SliceDifferentiable.add {s : Set ℝ} {f g : Domain → E} {z : Domain}
    (hf : SliceDifferentiable s f z) (hg : SliceDifferentiable s g z) :
    SliceDifferentiable s (f+g) z := ⟨hf.1.add hg.1,hf.2.add hg.2⟩

theorem sliceDifferentiable_zero (s : Set ℝ) (z : Domain) :
    SliceDifferentiable s (0 : Domain → E) z :=
  ⟨differentiableWithinAt_const (c := (0 : E)),differentiableAt_const (c := (0 : E))⟩

theorem joinDerivative_add (v w : E) (A B : SpatialDomain →L[ℝ] E) :
    joinDerivative (v+w) (A+B)=joinDerivative v A+joinDerivative w B := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [joinDerivative_apply, add_apply, smul_add]
  abel

theorem slicedJet_add {s : Set ℝ} {f g : Domain → E} {z : Domain}
    (hf : SliceDifferentiable s f z) (hg : SliceDifferentiable s g z) :
    slicedJet s (f+g) z=slicedJet s f z+slicedJet s g z := by
  simp only [slicedJet, Pi.add_apply, derivWithin_fun_add hf.1 hg.1,
    fderiv_fun_add hf.2 hg.2, joinDerivative_add, Prod.mk_add_mk]

theorem slicedJet_zero' (s : Set ℝ) (z : Domain) : slicedJet s (0 : Domain → E) z=0 := by
  simp [slicedJet, joinDerivative]

theorem sliceDifferentiable_truncate (s : Set ℝ) (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, SliceDifferentiable s (u i) z) :
    SliceDifferentiable s (truncate N u n) z := by
  by_cases hn : n ≤ N
  · simpa only [truncate_of_le N n _ hn] using hu n hn
  · simpa only [truncate_of_gt N n _ (by omega)] using sliceDifferentiable_zero (E := E) s z

theorem slicedJet_truncate (s : Set ℝ) (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    slicedJet s (truncate N u n) z=truncate N (fun i => slicedJet s (u i) z) n := by
  by_cases hn : n ≤ N
  · simp only [truncate_of_le N n _ hn]
  · simp only [truncate_of_gt N n _ (by omega), slicedJet_zero']

theorem sliceDifferentiable_shiftUp (s : Set ℝ) (N n : ℕ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, SliceDifferentiable s (u i) z) :
    SliceDifferentiable s (shiftUp N u n) z := by
  cases n with
  | zero => exact sliceDifferentiable_zero s z
  | succ n => exact sliceDifferentiable_truncate s N n u z hu

theorem slicedJet_shiftUp (s : Set ℝ) (N n : ℕ) (u : ℕ → Domain → E) (z : Domain) :
    slicedJet s (shiftUp N u n) z=shiftUp N (fun i => slicedJet s (u i) z) n := by
  cases n with
  | zero => exact slicedJet_zero' s z
  | succ n => exact slicedJet_truncate s N n u z

theorem slicedJet_assemble (s : Set ℝ) (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, SliceDifferentiable s (u i) z)
    (hc : ∀ i ≤ N, SliceDifferentiable s (c i) z) :
    slicedJet s (assemble N u c n) z=
      assemble N (fun i => slicedJet s (u i) z) (fun i => slicedJet s (c i) z) n := by
  change slicedJet s (truncate N u n+shiftUp N c n) z=_
  rw [slicedJet_add (sliceDifferentiable_truncate s N n u z hu)
    (sliceDifferentiable_shiftUp s N n c z hc), slicedJet_truncate, slicedJet_shiftUp]
  rfl

theorem sliceDifferentiable_assemble (s : Set ℝ) (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, SliceDifferentiable s (u i) z)
    (hc : ∀ i ≤ N, SliceDifferentiable s (c i) z) :
    SliceDifferentiable s (assemble N u c n) z :=
  (sliceDifferentiable_truncate s N n u z hu).add (sliceDifferentiable_shiftUp s N n c z hc)

theorem pressureJet_zero (z : Domain) : pressureJet (0 : Domain → ℝ) z=0 := by
  simp [pressureJet, joinDerivative]

theorem pressureJet_add (f g : Domain → ℝ) (z : Domain)
    (hf : DifferentiableAt ℝ (fun y => f (z.1,y)) z.2)
    (hg : DifferentiableAt ℝ (fun y => g (z.1,y)) z.2) :
    pressureJet (f+g) z=pressureJet f z+pressureJet g z := by
  simp only [pressureJet, Pi.add_apply, fderiv_fun_add hf hg]
  rw [show (0 : ℝ)=0+0 by simp, joinDerivative_add]
  simp only [zero_add, Prod.mk_add_mk]

theorem pressureJet_truncate (N n : ℕ) (u : ℕ → Domain → ℝ) (z : Domain) :
    pressureJet (truncate N u n) z=truncate N (fun i => pressureJet (u i) z) n := by
  by_cases hn : n ≤ N
  · simp only [truncate_of_le N n _ hn]
  · simp only [truncate_of_gt N n _ (by omega), pressureJet_zero]

theorem pressureJet_shiftUp (N n : ℕ) (u : ℕ → Domain → ℝ) (z : Domain) :
    pressureJet (shiftUp N u n) z=shiftUp N (fun i => pressureJet (u i) z) n := by
  cases n with
  | zero => exact pressureJet_zero z
  | succ n => exact pressureJet_truncate N n u z

theorem pressureJet_assemble (N n : ℕ) (u c : ℕ → Domain → ℝ) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (fun y => u i (z.1,y)) z.2)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (fun y => c i (z.1,y)) z.2) :
    pressureJet (assemble N u c n) z=
      assemble N (fun i => pressureJet (u i) z) (fun i => pressureJet (c i) z) n := by
  have htr : DifferentiableAt ℝ (fun y => truncate N u n (z.1,y)) z.2 := by
    by_cases hn : n ≤ N
    · simpa only [truncate_of_le N n _ hn] using hu n hn
    · simpa only [truncate_of_gt N n _ (by omega), Pi.zero_apply] using
        (differentiableAt_const (c := (0 : ℝ)))
  have hsh : DifferentiableAt ℝ (fun y => shiftUp N c n (z.1,y)) z.2 := by
    cases n with
    | zero => exact differentiableAt_const (c := (0 : ℝ))
    | succ n =>
      by_cases hn : n ≤ N
      · simpa only [shiftUp, truncate_of_le N n _ hn] using hc n hn
      · simpa only [shiftUp, truncate_of_gt N n _ (by omega), Pi.zero_apply] using
          (differentiableAt_const (c := (0 : ℝ)))
  change pressureJet (truncate N u n+shiftUp N c n) z=_
  rw [pressureJet_add _ _ z htr hsh, pressureJet_truncate, pressureJet_shiftUp]
  rfl

theorem spatialDifferentiable_assemble (N n : ℕ) (u c : ℕ → Domain → E) (z : Domain)
    (hu : ∀ i ≤ N, DifferentiableAt ℝ (fun y => u i (z.1,y)) z.2)
    (hc : ∀ i ≤ N, DifferentiableAt ℝ (fun y => c i (z.1,y)) z.2) :
    DifferentiableAt ℝ (fun y => assemble N u c n (z.1,y)) z.2 := by
  have htr : DifferentiableAt ℝ (fun y => truncate N u n (z.1,y)) z.2 := by
    by_cases hn : n ≤ N
    · simpa only [truncate_of_le N n _ hn] using hu n hn
    · simpa only [truncate_of_gt N n _ (by omega), Pi.zero_apply] using
        (differentiableAt_const (c := (0 : E)))
  have hsh : DifferentiableAt ℝ (fun y => shiftUp N c n (z.1,y)) z.2 := by
    cases n with
    | zero => exact differentiableAt_const (c := (0 : E))
    | succ n =>
      by_cases hn : n ≤ N
      · simpa only [shiftUp, truncate_of_le N n _ hn] using hc n hn
      · simpa only [shiftUp, truncate_of_gt N n _ (by omega), Pi.zero_apply] using
          (differentiableAt_const (c := (0 : E)))
  exact htr.add hsh

end EulerPacketPointJets
