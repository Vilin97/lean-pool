/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
import Mathlib.Data.Fintype.Pigeonhole

/-! # BinaryRelations -/



section «lp_section_1»

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

/-- Imported declaration from the Incompleteness formalization. -/
def IsSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

-- NOTE: Another convention uses `x ≺ y → x ≺ z → y ≺ z`.
/-- Imported declaration from the Incompleteness formalization. -/
def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Serial := ∀ x, ∃ y, x ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Confluent := ∀ ⦃x y z⦄, ((x ≺ y ∧ x ≺ z) → ∃ w, (y ≺ w ∧ z ≺ w))

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.RelDense := ∀ ⦃x y⦄, x ≺ y → ∃z, x ≺ z ∧ z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Connected := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Functional := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y = z

/-- Imported declaration from the Incompleteness formalization. -/
def RightConvergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y ∨ y = z

/-- Imported declaration from the Incompleteness formalization. -/
def Coreflexive := ∀ ⦃x y⦄, x ≺ y → x = y

/-- Imported declaration from the Incompleteness formalization. -/
def Equality := ∀ ⦃x y⦄, x ≺ y ↔ x = y

/-- Imported declaration from the Incompleteness formalization. -/
def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)

/-- Imported declaration from the Incompleteness formalization. -/
def Assymetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

/-- Imported declaration from the Incompleteness formalization. -/
def Universal := ∀ ⦃x y⦄, x ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ConverseWellFounded := WellFounded <| flip (· ≺ ·)

end «lp_section_1»


section «lp_section_2»

variable {α : Type u}
variable {rel : α → α → Prop}


lemma serial_of_refl (hRefl : ∀ x, rel x x) : Serial rel := by
  rintro w;
  existsi w;
  exact hRefl w;

lemma eucl_of_symm_trans (hSymm : IsSymmetric rel)
    (hTrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) :
    Euclidean rel := by
  intro x y z Rxy Rxz;
  have Ryx := hSymm Rxy;
  exact hSymm <| hTrans Ryx Rxz;

lemma trans_of_symm_eucl (hSymm : IsSymmetric rel) (hEucl : Euclidean rel) :
    ∀ ⦃x y z⦄, rel x y → rel y z → rel x z := by
  rintro x y z Rxy Ryz;
  exact hSymm <| hEucl (hSymm Rxy) Ryz;

lemma symm_of_refl_eucl (hRefl : ∀ x, rel x x) (hEucl : Euclidean rel) :
    IsSymmetric rel := by
  intro x y Rxy;
  exact hEucl (hRefl x) Rxy;

lemma trans_of_refl_eucl (hRefl : ∀ x, rel x x) (hEucl : Euclidean rel) :
    ∀ ⦃x y z⦄, rel x y → rel y z → rel x z := by
  have hSymm := symm_of_refl_eucl hRefl hEucl;
  exact trans_of_symm_eucl hSymm hEucl;

lemma refl_of_symm_serial_eucl (hSymm : IsSymmetric rel) (hSerial : Serial rel) (hEucl :
    Euclidean rel) :
    ∀ x, rel x x := by
  rintro x;
  obtain ⟨y, Rxy⟩ := hSerial x;
  have Ryx := hSymm Rxy;
  exact trans_of_symm_eucl hSymm hEucl Rxy Ryx;

lemma corefl_of_refl_assym_eucl (hRefl : ∀ x, rel x x)
    (hAntisymm : ∀ ⦃x y⦄, rel x y → rel y x → x = y) (hEucl : Euclidean rel) :
    Coreflexive rel := by
  intro x y Rxy;
  have Ryx := hEucl (hRefl x) Rxy;
  exact hAntisymm Rxy Ryx;

lemma equality_of_refl_corefl (hRefl : ∀ x, rel x x) (hCorefl : Coreflexive rel) :
    Equality rel := by
  intro x y;
  constructor;
  · apply hCorefl;
  · rintro rfl; apply hRefl;

lemma equality_of_refl_assym_eucl (hRefl : ∀ x, rel x x)
    (hAntisymm : ∀ ⦃x y⦄, rel x y → rel y x → x = y) (hEucl : Euclidean rel) :
    Equality rel := by
  apply equality_of_refl_corefl;
  · assumption;
  · exact corefl_of_refl_assym_eucl hRefl hAntisymm hEucl;

lemma refl_of_equality (h : Equality rel) : ∀ x, rel x x := by
  intro x;
  exact h.mpr rfl;

lemma corefl_of_equality (h : Equality rel) : Coreflexive rel := by
  intro x y Rxy;
  apply h.mp Rxy;

lemma irreflexive_of_assymetric (hAssym : Assymetric rel) : ∀ x, ¬ rel x x := by
  intro x Rxx;
  have := hAssym Rxx;
  contradiction;

lemma refl_of_universal (h : Universal rel) : ∀ x, rel x x := by
  intro x; exact @h x x;

lemma eucl_of_universal (h : Universal rel) : Euclidean rel := by
  rintro x y z _ _; exact @h z y;

lemma confluent_of_refl_connected (hRefl : ∀ x, rel x x) (hConfl : Connected rel) :
    Confluent rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  rcases @hConfl x y z ⟨Rxy, Rxz⟩ with (Ryz | Rzy);
  · use z;
    constructor;
    · assumption;
    · apply hRefl;
  · use y;
    constructor;
    · apply hRefl;
    · assumption;

section «lp_section_3»

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s :
    Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma Finite.converseWellFounded_of_trans_irrefl
    [Finite α] [IsTrans α rel] [Std.Irrefl rel] : ConverseWellFounded rel := by
  haveI : IsTrans α (flip rel) :=
    ⟨fun a b c rba rcb => IsTrans.trans c b a rcb rba⟩
  haveI : Std.Irrefl (flip rel) :=
    ⟨fun a h => Std.Irrefl.irrefl (r := rel) a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl (flip rel)

lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z)
  (hIrrefl : ∀ x, ¬ rel x x) : ConverseWellFounded rel :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨fun _ _ _ ba cb ↦ hTrans cb ba⟩
    ⟨hIrrefl⟩

end «lp_section_3»


@[simp]
lemma WellFounded.trivial_wellfounded : WellFounded (α := α) (fun _ _ => False) := by
  constructor; intro _;
  constructor; intro _ _;
  contradiction;

/-- Imported declaration from the Incompleteness formalization. -/
def Relation.IrreflGen (R : α → α → Prop) := fun x y => x ≠ y ∧ R x y


/-- Imported declaration from the Incompleteness formalization. -/
abbrev WeaklyConverseWellFounded (R : α → α → Prop) := ConverseWellFounded (Relation.IrreflGen R)
alias WCWF := WeaklyConverseWellFounded


section «lp_section_4»

lemma dependent_choice {R : α → α → Prop} (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, R a b)
  : ∃ f : ℕ → α, ∀ x, R (f x) (f (x + 1)) := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f :
    α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | _ | hij);
    · use i, j;
    · contradiction;
    · use j, i; simp [hij, e];

lemma antisymm_of_WCWF {R : α → α → Prop} : WCWF R → ∀ ⦃x y⦄, R x y → R y x → x = y := by
  contrapose;
  simp only [not_forall, forall_exists_index];
  intro x y Rxy Ryz hxy;
  apply ConverseWellFounded.iff_has_max.not.mpr;
  push Not;
  use {x, y};
  constructor;
  · simp;
  · intro z hz;
    by_cases z = x;
    · use y; simp_all [Relation.IrreflGen];
    · use x; simp_all [Relation.IrreflGen];

lemma WCWF_of_finite_trans_antisymm {R : α → α → Prop} (hFin : Finite α)
    (R_trans : ∀ ⦃x y z⦄, R x y → R y z → R x z) :
    (∀ ⦃x y⦄, R x y → R y x → x = y) → WCWF R := by
    contrapose;
    intro hWCWF;
    replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
    push Not at hWCWF;
    obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
    replace hf : ∀ x, f x ≠ f (x + 1) ∧ R (f x) (f (x + 1)) := by
      intro x
      exact hf x
    push Not
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f;
    use (f i), (f (i + 1));
    have ⟨hi₁, hi₂⟩ := hf i;
    refine ⟨(by assumption), ?_, (by assumption)⟩;
    have : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩;
    have H : ∀ i j, i < j → R (f i) (f j) := by
      intro i j hij
      induction hij with
      | refl => exact hf i |>.2;
      | step _ ih => exact R_trans ih <| hf _ |>.2;
    have := H (i + 1) j this;
    simpa [e];

end «lp_section_4»

end «lp_section_2»
