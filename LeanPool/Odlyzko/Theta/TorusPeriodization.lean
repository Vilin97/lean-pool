/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {ι : Type*}

/-- A torus quotient map used in the Odlyzko-bound argument. -/
def torusQuotientMap (x : ι → ℝ) : UnitAddTorus ι :=
  fun i ↦ (x i : UnitAddCircle)

theorem isOpenQuotientMap_torusQuotientMap :
    IsOpenQuotientMap (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) := by
  change IsOpenQuotientMap
    (Pi.map fun _ : ι ↦ ((↑) : ℝ → UnitAddCircle))
  exact IsOpenQuotientMap.piMap fun _ ↦
    QuotientAddGroup.isOpenQuotientMap_mk

theorem surjective_torusQuotientMap :
    Function.Surjective
      (torusQuotientMap : (ι → ℝ) → UnitAddTorus ι) :=
  isOpenQuotientMap_torusQuotientMap.surjective

theorem exists_intPi_add_of_torusQuotientMap_eq
    {x y : ι → ℝ} (h : torusQuotientMap x = torusQuotientMap y) :
    ∃ n : ι → ℤ, y = x + fun i ↦ (n i : ℝ) := by
  classical
  have hi (i : ι) :
      ∃ n : ℤ, y i = x i + (n : ℝ) := by
    have hz : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      change (y i : UnitAddCircle) - (x i : UnitAddCircle) = 0
      rw [sub_eq_zero]
      exact (congrFun h i).symm
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    grind
  choose n hn using hi
  exact ⟨n, funext hn⟩

theorem torusQuotientMap_add_intPi
    (x : ι → ℝ) (n : ι → ℤ) :
    torusQuotientMap (x + fun i ↦ (n i : ℝ)) =
      torusQuotientMap x := by
  ext i
  simp [torusQuotientMap]

/-- An int periodization used in the Odlyzko-bound argument. -/
noncomputable def intPeriodization (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ))

theorem intPeriodization_add_intPi
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) (k : ι → ℤ) :
    intPeriodization f (x + fun i ↦ (k i : ℝ)) =
      intPeriodization f x := by
  unfold intPeriodization
  calc
    (∑' n : ι → ℤ,
        f ((x + fun i ↦ (k i : ℝ)) + fun i ↦ (n i : ℝ))) =
        ∑' n : ι → ℤ,
          f (x + fun i ↦ ((k + n) i : ℝ)) := by
      apply tsum_congr
      intro n
      congr 1
      funext i
      simp [add_assoc]
    _ = ∑' n : ι → ℤ, f (x + fun i ↦ (n i : ℝ)) :=
      Equiv.tsum_eq (Equiv.addLeft k)
        (fun n : ι → ℤ ↦ f (x + fun i ↦ (n i : ℝ)))

theorem intPeriodization_eq_of_torusQuotientMap_eq
    (f : (ι → ℝ) → ℂ) {x y : ι → ℝ}
    (h : torusQuotientMap x = torusQuotientMap y) :
    intPeriodization f x = intPeriodization f y := by
  obtain ⟨n, rfl⟩ := exists_intPi_add_of_torusQuotientMap_eq h
  exact (intPeriodization_add_intPi f x n).symm

/-- A torus lift used in the Odlyzko-bound argument. -/
noncomputable def torusLift {A : Type*} (f : (ι → ℝ) → A) :
    UnitAddTorus ι → A :=
  fun x ↦ f (Function.surjInv surjective_torusQuotientMap x)

theorem torusLift_comp_torusQuotientMap {A : Type*}
    (f : (ι → ℝ) → A)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    torusLift f ∘ torusQuotientMap = f := by
  funext x
  apply hf
  exact Function.rightInverse_surjInv
    surjective_torusQuotientMap (torusQuotientMap x)

theorem continuous_torusLift {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    Continuous (torusLift f) := by
  apply isOpenQuotientMap_torusQuotientMap.continuous_comp_iff.mp
  simpa [torusLift_comp_torusQuotientMap f hf] using hfc

/-- A torus continuous map used in the Odlyzko-bound argument. -/
noncomputable def torusContinuousMap {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y) :
    C(UnitAddTorus ι, A) :=
  ⟨torusLift f, continuous_torusLift f hfc hf⟩

@[simp]
theorem torusContinuousMap_comp_torusQuotientMap
    {A : Type*} [TopologicalSpace A]
    (f : (ι → ℝ) → A) (hfc : Continuous f)
    (hf : ∀ x y, torusQuotientMap x = torusQuotientMap y → f x = f y)
    (x : ι → ℝ) :
    torusContinuousMap f hfc hf (torusQuotientMap x) = f x :=
  congrFun (torusLift_comp_torusQuotientMap f hf) x

/-- A torus periodization used in the Odlyzko-bound argument. -/
noncomputable def torusPeriodization
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f)) :
    C(UnitAddTorus ι, ℂ) :=
  torusContinuousMap (intPeriodization f) hf
    (fun _x _y h ↦ intPeriodization_eq_of_torusQuotientMap_eq f h)

@[simp]
theorem torusPeriodization_apply_quotient
    (f : (ι → ℝ) → ℂ) (hf : Continuous (intPeriodization f))
    (x : ι → ℝ) :
    torusPeriodization f hf (torusQuotientMap x) =
      intPeriodization f x :=
  torusContinuousMap_comp_torusQuotientMap _ _ _ x

end NumberField.Odlyzko
