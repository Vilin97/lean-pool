/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
import Mathlib.Order.Interval.Finset.Nat

/-! # KHIncompleteness -/


namespace LO
namespace Modal

open System
open Kripke
open Formula
open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame} {a : ℕ}

lemma valid_atomic_H_of_valid_atomic_L : F ⊧ (Axioms.L (atom a)) → F ⊧ (Axioms.H (atom a)) := by
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ==> a)) := by
    intro y Rxy;
    exact (Satisfies.and_def.mp <| @hx y Rxy) |>.1;
  exact @h V x this;

lemma valid_atomic_L_of_valid_atomic_H : F ⊧ Axioms.H (atom a) → F ⊧ Axioms.L (atom a) := by
  intro hH V x hx;
  let V' : Valuation F := fun w a => ∀ n : ℕ, Satisfies ⟨F, V⟩ w (□^[n] a);
  have h₁ : Satisfies ⟨F, V'⟩ x (□(□a <=> a)) := by
    intro y Rxy;
    have : Satisfies ⟨F, V'⟩ y a ↔ Satisfies ⟨F, V'⟩ y (□a) := calc
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[n] a) := by simp [Satisfies, V'];
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[(n + 1)]a) := by
        constructor;
        · intro h n; apply h;
        · intro h n;
          have h₁ : Satisfies ⟨F, V⟩ y (□□^[n](atom a) ==> □^[n](atom a)) := by
            induction n with
            | zero => apply @hx y Rxy;
            | succ n => intro _; apply h;
          apply h₁;
          simpa using h n;
      _ ↔ ∀ n, ∀ z, y ≺ z → Satisfies ⟨F, V⟩ z (□^[n] a) := by
        constructor
        · intro h n z hz
          have hn : ∀ z, y ≺ z → Satisfies ⟨F, V⟩ z (□^[n] (atom a)) := by
            have := h n; rw [Box.multibox_succ] at this; exact this
          exact hn z hz
        · intro h n
          rw [Box.multibox_succ]; exact h n;
      _ ↔ ∀ z, y ≺ z → ∀ n : ℕ, Satisfies ⟨F, V⟩ z (□^[n]a) := by aesop;
      _ ↔ ∀ z, y ≺ z → Satisfies ⟨F, V'⟩ z (atom a) := by simp [Satisfies, V'];
      _ ↔ Satisfies ⟨F, V'⟩ y (□(atom a)) := by simp [Satisfies];
    simp [Satisfies, V'];
    tauto;
  have h₂ : Satisfies ⟨F, V'⟩ x (□atom a) := @hH V' x h₁;
  intro w Rxw;
  exact @h₂ w Rxw 0;

lemma valid_atomic_L_iff_valid_atomic_H : F ⊧ Axioms.L (atom 0) ↔ F ⊧ Axioms.H (atom 0) := by
  constructor;
  · exact valid_atomic_H_of_valid_atomic_L;
  · exact valid_atomic_L_of_valid_atomic_H;

lemma valid_atomic_4_of_valid_atomic_L : F ⊧ Axioms.L (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  intro h V x h₂ y Rxy z Ryz;
  refine h₂ z ?_;
  exact (trans_of_validate_L h).trans _ _ _ Rxy Ryz;

lemma valid_atomic_Four_of_valid_atomic_H : F ⊧ Axioms.H (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  trans;
  · exact valid_atomic_L_iff_valid_atomic_H.mpr;
  · exact valid_atomic_4_of_valid_atomic_L;

/-- Imported declaration from the Incompleteness formalization. -/
abbrev cresswellFrame : Kripke.Frame where
  World := ℕ × Fin 2
  Rel n m :=
    match n, m with
    | (n, 0), (m, 0) => n ≤ m + 1
    | (n, 1), (m, 1) => n > m
    | (_, 0), (_, 1) => True
    | _, _ => False

namespace cresswellFrame

/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev sharp (n : ℕ) : cresswellFrame.World := (n, 0)
/-- Imported notation from the Incompleteness formalization. -/
postfix:max "♯" => sharp


/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev flat (n : ℕ) : cresswellFrame.World := (n, 1)
/-- Imported notation from the Incompleteness formalization. -/
postfix:max "♭" => flat

variable {n m : ℕ} {x y : cresswellFrame.World}

/-- Imported declaration from the Incompleteness formalization. -/
lemma trichonomy : x ≺ y ∨ x = y ∨ y ≺ x := by
  match x, y with
  | x♯, y♯ => simp [cresswellFrame, Frame.Rel']; omega;
  | x♭, y♯ => simp [cresswellFrame, Frame.Rel'];
  | x♯, y♭ => simp [cresswellFrame, Frame.Rel'];
  | x♭, y♭ => simp [cresswellFrame, Frame.Rel']; omega;

lemma sharp_to_flat : n♯ ≺ m♭ := by simp [Frame.Rel']

@[simp] lemma not_flat_to_sharp : ¬(n♭ ≺ m♯):= by simp [Frame.Rel'];

lemma sharp_to_sharp : n♯ ≺ m♯ ↔ n ≤ m + 1 := by simp [Frame.Rel']

lemma flat_to_flat : n♭ ≺ m♭ ↔ n > m := by simp [Frame.Rel'];

lemma exists_flat_of_from_flat (h : n♭ ≺ x) : ∃ m, x = ⟨m, 1⟩ ∧ n > m := by
  match x with
  | ⟨m, 0⟩ => aesop;
  | ⟨m, 1⟩ => exact ⟨m, rfl, flat_to_flat.mp h⟩;

end cresswellFrame



/-- Imported declaration from the Incompleteness formalization. -/
abbrev cresswellModel : Kripke.Model := ⟨cresswellFrame, fun w _ => w ≠ 0♯⟩

namespace cresswellModel

end cresswellModel


open cresswellFrame cresswellModel

lemma not_valid_axiomFour_in_cresswellModel :
    ¬(Satisfies cresswellModel 2♯ (Axioms.Four (atom 0))) := by
  apply Satisfies.imp_def.not.mpr;
  push Not;
  constructor;
  · intro x;
    match x with
    | n♯ =>
      intro h2n;
      suffices n ≠ 0 by simpa [Satisfies];
      simp only [sharp_to_sharp] at h2n; omega;
    | n♭ => simp [Satisfies];
  · apply Satisfies.box_def.not.mpr
    push Not;
    refine ⟨1♯, sharp_to_sharp.mpr (by omega), ?_⟩;
    apply Satisfies.box_def.not.mpr;
    push Not;
    exact ⟨0♯, sharp_to_sharp.mpr (by omega), by tauto⟩;

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.cresswellModel.truthset (φ : Formula _) := { x :
    cresswellModel.World | Satisfies cresswellModel x φ }
local notation "‖" φ "‖" => cresswellModel.truthset φ

namespace cresswellModel
namespace truthset

lemma infinite_of_all_flat (h : ∀ n, n♭ ∈ ‖φ‖) : (‖φ‖.Infinite) :=
  Set.infinite_coe_iff.mp <|
    Infinite.of_injective (fun n => ⟨n♭, h n⟩) <| by simp [Function.Injective]

-- TODO: need golf
lemma exists_max_sharp (h₁ : ∀ n, n♭ ∈ ‖φ‖) (h₂ : ‖φ‖ᶜ.Finite) (h₃ : ‖φ‖ᶜ.Nonempty) :
  ∃ n, n♯ ∉ ‖φ‖ ∧ (∀ m > n, m♯ ∈ ‖φ‖) := by
  obtain ⟨s, hs⟩ := Set.Finite.exists_finset (s := (fun x => x.1) '' ‖φ‖ᶜ) <| Set.Finite.image _ h₂;
  have se : s.Nonempty := by
    let ⟨x, hx⟩ := h₃;
    use x.1;
    apply hs _ |>.mpr;
    use x;
  use (s.max' se);
  constructor;
  · have hmem := (@hs _).mp (Finset.max'_mem _ se)
    rcases hmem with ⟨⟨n, i⟩, hx, hxfst⟩
    cases i using Fin.cases with
    | zero =>
      simpa [cresswellFrame.sharp, ←hxfst] using hx
    | succ i =>
      cases i using Fin.cases with
      | zero => exact False.elim (hx (h₁ n))
      | succ i => exact Fin.elim0 i
  · intro m hm;
    by_contra hC;
    have : m < m := Finset.max'_lt_iff (H := se) |>.mp hm m (by
      apply hs m |>.mpr;
      use m♯;
      simpa;
    );
    simp at this;

-- TODO: need golf
open Classical in
lemma exists_min_flat (h₁ : ∃ n, n♭ ∉ ‖φ‖) :
  ∃ n, n♭ ∉ ‖φ‖ ∧ (∀ m < n, m♭ ∈ ‖φ‖) := by
  obtain ⟨n, hn⟩ := h₁;
  let s := Finset.Icc 0 n |>.filter (fun k => k♭ ∉ ‖φ‖);
  have hse : s.Nonempty := by use n; simpa [s];
  use (s.min' hse);
  have ⟨h₁, h₂⟩ := Finset.mem_filter |>.mp <| @Finset.min'_mem (s := s) _ _ hse;
  constructor;
  · exact h₂;
  · intro m hm;
    by_contra hC;
    have := Finset.lt_min'_iff _ _ |>.mp hm m <| by
      simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_Icc, zero_le, true_and, s];
      constructor;
      · simp only [Finset.lt_min'_iff, s] at hm;
        have := hm n <| by simpa [s];
        omega;
      · exact hC;
    simp at this;

lemma either_finite_cofinite : (‖φ‖.Finite) ∨ (‖φ‖ᶜ.Finite) := by
  induction φ using Formula.rec' with
  | hatom a => simp [truthset, Satisfies];
  | hfalsum => simp [truthset, Satisfies];
  | himp φ ψ ihφ ihψ =>
    rw [(show ‖φ ==> ψ‖ = ‖φ‖ᶜ ∪ ‖ψ‖ by tauto_set), Set.compl_union, compl_compl];
    rcases ihφ with (_ | _) <;> rcases ihψ with (_ | _);
    · right; apply Set.Finite.inter_of_left; assumption;
    · right; apply Set.Finite.inter_of_left; assumption;
    · left;
      rw [Set.finite_union];
      constructor <;> assumption;
    · right; apply Set.Finite.inter_of_right; assumption;
  | hbox φ ihφ =>
    by_cases h : ∀ n, n♭ ∈ ‖φ‖;
    · have tsφc_finite : ‖φ‖ᶜ.Finite :=
      or_iff_not_imp_left.mp ihφ <| truthset.infinite_of_all_flat h;
      wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
      · have : ‖□φ‖ᶜ = ∅ := by
          simp only [Set.compl_empty_iff, Set.eq_univ_iff_forall, Set.mem_setOf_eq];
          intro x y Rxy;
          match x, y with
          | m♯, k♯ =>
            have : ∀ x, Satisfies cresswellModel x φ := by
              simpa [Set.compl_empty, Set.Nonempty] using tsφc_ne;
            apply this;
          | m♭, k♯ => simp at Rxy;
          | m♯, k♭ => apply h;
          | m♭, k♭ => apply h;
        rw [this];
        simp;
      obtain ⟨n, hn, hn_max⟩ := exists_max_sharp h tsφc_finite tsφc_ne;
      right;
      apply @Set.Finite.subset (s := (·♯) '' Set.Icc 0 (n + 1));
      · apply Set.toFinite
      · intro x hx;
        replace := Satisfies.box_def.not.mp hx;
        push Not at this;
        obtain ⟨y, Rxy, _⟩ := this;
        match x, y with
        | m♯, k♯ =>
          by_contra hC; simp at hC;
          replace Rxy := sharp_to_sharp.mp Rxy;
          have : k♯ ∈ ‖φ‖ := @hn_max k (by omega);
          contradiction;
        | m♭, k♯ => simp at Rxy;
        | _♯, k♭ => have := h k; contradiction;
        | _♭, k♭ => have := h k; contradiction;
    · left;
      push Not at h;
      obtain ⟨n, hn⟩ := h;
      apply @Set.Finite.subset (s := (·♭) '' Set.Icc 0 n);
      · apply Set.toFinite
      · intro x hx;
        match x with
        | m♯ =>
          have := hx n♭ sharp_to_flat;
          contradiction;
        | m♭ =>
          by_contra hC;
          have := hx n♭ <| (cresswellFrame.flat_to_flat.mpr <| by simpa using hC);
          contradiction;

end truthset
end cresswellModel

open Classical in
lemma valid_axiomH_in_cresswellModel : cresswellModel ⊧ □(□φ <=> φ) ==> □φ := by
  rintro x;
  by_cases h : ∀ n, n♭ ∈ ‖φ‖;
  · have tsφc_fin : ‖φ‖ᶜ.Finite :=
    or_iff_not_imp_left.mp truthset.either_finite_cofinite <| truthset.infinite_of_all_flat h;
    wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
    · apply Satisfies.imp_def₂.mpr;
      right;
      intro y Rxy;
      have : ∀ x, Satisfies cresswellModel x φ := by
        simpa [Set.compl_empty, Set.Nonempty] using tsφc_ne;
      apply this;
    obtain ⟨n, hn, hn_max⟩ := truthset.exists_max_sharp h tsφc_fin tsφc_ne;
    match x with
    | m♭ =>
      apply Satisfies.imp_def₂.mpr;
      right;
      rintro y Rny;
      obtain ⟨k, ⟨rfl, _⟩⟩ := exists_flat_of_from_flat Rny;
      apply h;
    | m♯ =>
      by_cases hnm : n + 2 ≤ m;
      · apply Satisfies.imp_def₂.mpr;
        right;
        rintro y Rny;
        match y with
        | _♭ => apply h;
        | _♯ => apply hn_max; simp only [sharp_to_sharp] at Rny; omega;
      · apply Satisfies.imp_def₂.mpr;
        left;
        apply Satisfies.box_def.not.mpr;
        push Not;
        refine ⟨(n + 1)♯, sharp_to_sharp.mpr (by omega), ?_⟩;
        have : Satisfies cresswellModel (n + 1)♯ φ := hn_max (n + 1) (by omega);
        have : ¬Satisfies cresswellModel (n + 1)♯ (□φ) := by
          apply Satisfies.box_def.not.mpr;
          push Not;
          exact ⟨n♯, sharp_to_sharp.mpr (by omega), hn⟩;
        apply Satisfies.iff_def.not.mpr;
        tauto;
  · push Not at h;
    obtain ⟨n, hn, hn_max⟩ := truthset.exists_min_flat h;
    have hn₁ : Satisfies cresswellModel n♭ (□φ) := by
      intro x Rnx;
      obtain ⟨m, ⟨rfl, hnm⟩⟩ := exists_flat_of_from_flat Rnx;
      exact hn_max m hnm;
    have hn₂ : ¬Satisfies cresswellModel n♭ (□φ <=> φ) := by
      apply Satisfies.iff_def.not.mpr;
      push Not;
      tauto;
    match x with
    | m♯ =>
      apply Satisfies.imp_def₂.mpr;
      left;
      apply Satisfies.box_def.not.mpr;
      push Not;
      exact ⟨n♭, sharp_to_flat, hn₂⟩;
    | m♭ =>
      by_cases hmn : m > n;
      · intro h;
        have := @h n♭ <| (flat_to_flat.mpr hmn);
        contradiction;
      · apply Satisfies.imp_def₂.mpr;
        right;
        rintro y Rmy;
        obtain ⟨k, ⟨rfl, hk₂⟩⟩ := exists_flat_of_from_flat Rmy;
        apply hn_max;
        omega;

lemma provable_KH_of_valid_cresswellModel : Hilbert.KH ⊢! φ → cresswellModel ⊧ φ := by
  intro h;
  induction h using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    · exact Kripke.ValidOnModel.axiomK;
    · exact valid_axiomH_in_cresswellModel;
  | mdp ihφψ ihφ => exact Kripke.ValidOnModel.mdp ihφψ ihφ;
  | nec ihφ => exact Kripke.ValidOnModel.nec ihφ;
  | imply₁ => exact Kripke.ValidOnModel.imply₁;
  | imply₂ => exact Kripke.ValidOnModel.imply₂;
  | ec => exact Kripke.ValidOnModel.elimContra;

lemma KH_unprov_axiomFour : Hilbert.KH ⊬ Axioms.Four (atom 0) := fun hC =>
  not_valid_axiomFour_in_cresswellModel (provable_KH_of_valid_cresswellModel hC 2♯)

theorem KH_KripkeIncomplete : ¬∃ C : Kripke.FrameClass, ∀ φ, (Hilbert.KH ⊢! φ ↔ C ⊧ φ) := by
  rintro ⟨C, h⟩;
  have : C ⊧ Axioms.H (atom 0) := @h (Axioms.H (atom 0)) |>.mp <| by simp;
  have : C ⊧ Axioms.Four (atom 0) := fun {F} hF => valid_atomic_Four_of_valid_atomic_H (this hF);
  have : Hilbert.KH ⊢! Axioms.Four (atom 0) := @h (Axioms.Four (atom 0)) |>.mpr this;
  exact @KH_unprov_axiomFour this;

end Kripke

end Modal
end LO
