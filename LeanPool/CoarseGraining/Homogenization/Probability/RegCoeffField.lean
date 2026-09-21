/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Algebra.Support

/-!
# The regular-coefficient-field carrier

This file introduces `RegCoeffField d`, the carrier of *honest* coefficient
fields on which the probabilistic layer of the homogenization development is
based.  A `RegCoeffField d` is a map `Vec d → Mat d` whose entries are Borel
measurable and locally integrable — the minimal regularity level at which the
linear entry-test integral (see `RegCoeffField/Sigma.lean`) is genuinely
additive and at which a.e.-regularity hypotheses become free by type.

The deterministic layers (Sobolev/PDE/coarse-graining algebra) continue to work
with the raw `CoeffField d = Vec d → Mat d`; they receive `a.toFun` through the
coercion `RegCoeffField.toCoeffField`.

The carrier is a commutative monoid under pointwise addition, is closed under
real scaling and finite sums, and contains the constant fields
(`constRegCoeffField`, including `1`); each closure property is witnessed by the
corresponding closure of measurability and local integrability.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

/-- The regular-fields carrier: entrywise-Borel-measurable, locally-integrable
coefficient fields.  Regularity is now free by type: every element carries a
proof that each of its scalar entries is measurable and locally integrable
(the paper, Armstrong–Kuusi–Loher, to appear). -/
structure RegCoeffField (d : ℕ) where
  /-- The underlying raw coefficient field. -/
  toFun : Vec d → Mat d
  /-- Each scalar entry is Borel measurable. -/
  entry_measurable : ∀ i j, Measurable (fun x : Vec d => toFun x i j)
  /-- Each scalar entry is locally integrable for the Lebesgue measure. -/
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Vec d => toFun x i j) volume

namespace RegCoeffField

variable {d : ℕ}

instance : CoeFun (RegCoeffField d) (fun _ => Vec d → Mat d) := ⟨toFun⟩

@[simp] theorem coe_mk (f h₁ h₂) (x : Vec d) :
    (⟨f, h₁, h₂⟩ : RegCoeffField d) x = f x := rfl

@[simp] theorem toFun_eq_coe (a : RegCoeffField d) : a.toFun = a := rfl

/-- Coercion back to the raw deterministic carrier `CoeffField d`.  Deterministic
layers receive `a.toCoeffField = a.toFun` and are untouched by the carrier. -/
def toCoeffField (a : RegCoeffField d) : CoeffField d := a.toFun

@[simp] theorem toCoeffField_apply (a : RegCoeffField d) (x : Vec d) :
    a.toCoeffField x = a x := rfl

@[ext] theorem ext {a b : RegCoeffField d} (h : ∀ x, a x = b x) : a = b := by
  cases a; cases b; simp only [mk.injEq]; funext x; exact h x

/-! ### Zero -/

instance : Zero (RegCoeffField d) where
  zero :=
    { toFun := 0
      entry_measurable := fun i j => by
        simp only [Pi.zero_apply, Matrix.zero_apply]; exact measurable_const
      entry_locInt := fun i j => by
        simp only [Pi.zero_apply, Matrix.zero_apply]
        exact MeasureTheory.locallyIntegrable_const (0 : ℝ) }

@[simp] theorem zero_toFun : (0 : RegCoeffField d).toFun = 0 := rfl

@[simp] theorem zero_apply (x : Vec d) : (0 : RegCoeffField d) x = 0 := rfl

/-! ### Addition -/

instance : Add (RegCoeffField d) where
  add a b :=
    { toFun := a.toFun + b.toFun
      entry_measurable := fun i j =>
        (a.entry_measurable i j).add (b.entry_measurable i j)
      entry_locInt := fun i j => (a.entry_locInt i j).add (b.entry_locInt i j) }

@[simp] theorem add_toFun (a b : RegCoeffField d) :
    (a + b).toFun = a.toFun + b.toFun := rfl

@[simp] theorem add_apply (a b : RegCoeffField d) (x : Vec d) :
    (a + b) x = a x + b x := rfl

@[simp] theorem coe_add (a b : RegCoeffField d) :
    ⇑(a + b) = ⇑a + ⇑b := rfl

/-! ### Real scaling -/

instance : SMul ℝ (RegCoeffField d) where
  smul c a :=
    { toFun := fun x => c • a x
      entry_measurable := fun i j => by
        simpa using! (a.entry_measurable i j).const_smul c
      entry_locInt := fun i j => by
        show LocallyIntegrable (fun x => c • a.toFun x i j) volume
        exact (a.entry_locInt i j).smul c }

@[simp] theorem smul_toFun (c : ℝ) (a : RegCoeffField d) :
    (c • a).toFun = fun x => c • a x := rfl

@[simp] theorem smul_apply (c : ℝ) (a : RegCoeffField d) (x : Vec d) :
    (c • a) x = c • a x := rfl

/-! ### Commutative monoid structure -/

instance : AddCommMonoid (RegCoeffField d) where
  add_assoc a b c := by ext x; simp [add_assoc]
  zero_add a := by ext x; simp
  add_zero a := by ext x; simp
  add_comm a b := by ext x; simp [add_comm]
  nsmul := nsmulRec

/-- Evaluation of a finite sum of carrier elements is the finite sum of the
evaluations. -/
@[simp] theorem finset_sum_apply {ι : Type*} (s : Finset ι) (g : ι → RegCoeffField d)
    (x : Vec d) : (∑ l ∈ s, g l) x = ∑ l ∈ s, g l x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert l s hl ih => rw [Finset.sum_insert hl, Finset.sum_insert hl, add_apply, ih]

theorem finset_sum_toFun {ι : Type*} (s : Finset ι) (g : ι → RegCoeffField d) :
    (∑ l ∈ s, g l).toFun = ∑ l ∈ s, (g l).toFun := by
  funext x; simp [Finset.sum_apply]

/-! ### Constant fields -/

/-- The constant regular field with value the matrix `M`.  Constant maps are
measurable and locally integrable, so this is a genuine carrier element. -/
def constRegCoeffField (M : Mat d) : RegCoeffField d where
  toFun := fun _ => M
  entry_measurable := fun _ _ => measurable_const
  entry_locInt := fun i j => MeasureTheory.locallyIntegrable_const (M i j)

@[simp] theorem constRegCoeffField_apply (M : Mat d) (x : Vec d) :
    constRegCoeffField M x = M := rfl

@[simp] theorem constRegCoeffField_zero :
    constRegCoeffField (0 : Mat d) = 0 := by ext x; simp

/-- The constant identity-matrix field. -/
instance : One (RegCoeffField d) := ⟨constRegCoeffField 1⟩

@[simp] theorem one_apply (x : Vec d) : (1 : RegCoeffField d) x = 1 := rfl

@[simp] theorem one_toFun : (1 : RegCoeffField d).toFun = fun _ => (1 : Mat d) := rfl

/-! ### A regularity utility: bounded measurable ⟹ locally integrable -/

/-- A bounded measurable scalar field on `Vec d` is locally integrable for the
Lebesgue measure.  This discharges the local-integrability obligation for
carriers built from bounded data (e.g. the checkerboard).  The Lebesgue measure
on `Vec d = Fin d → ℝ` is finite on compacts and the space is locally compact,
so integrability on every compact set follows from the uniform bound. -/
theorem locallyIntegrable_of_bounded_measurable {f : Vec d → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  refine Measure.integrableOn_of_bounded (hk.measure_lt_top).ne hf.aestronglyMeasurable
    (M := C) ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

end RegCoeffField

end

end Homogenization
