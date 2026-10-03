/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Ext -- shake: keep

/-!
# ClassifyInterval

Classification of connected open subsets of the nonnegative real numbers.
-/

public section

namespace OneMfld

open Set

theorem classify_connected_nnreal_interval (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : NNReal), (Set.Iio x = U)) ∨
  (∃ (x : NNReal), (Set.Ioi x = U)) ∨
  (U = univ) := by
  have hzeroInterval : Ici (0 : NNReal) = univ := by
    ext x
    simp only [mem_Ici, zero_le, mem_univ]
  have h := hc.isPreconnected.mem_intervals
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [← Ici_inter_Iic, interior_inter, interior_Iic] at hi
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inl ⟨sSup U, by simpa only [hzero, hzeroInterval, interior_univ,
        univ_inter] using hi⟩)
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩, Ioi_inter_Iio] at hi
      exact Or.inl ⟨sInf U, sSup U, hi⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [← Ici_inter_Iio, interior_inter, interior_Iio] at hi
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inl ⟨sSup U, by simpa only [hzero, hzeroInterval, interior_univ,
        univ_inter] using hi⟩)
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩, Ioi_inter_Iio] at hi
      exact Or.inl ⟨sInf U, sSup U, hi⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [interior_Ioc] at hi
    exact Or.inl ⟨sInf U, sSup U, hi⟩
  · exact Or.inl ⟨sInf U, sSup U, h.symm⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inr (Or.inr (by simpa only [hzero, hzeroInterval,
        interior_univ] using hi.symm)))
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩] at hi
      exact Or.inr (Or.inr (Or.inl ⟨sInf U, hi⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨sInf U, h.symm⟩))
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [interior_Iic] at hi
    exact Or.inr (Or.inl ⟨sSup U, hi⟩)
  · exact Or.inr (Or.inl ⟨sSup U, h.symm⟩)
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (hc.nonempty.ne_empty h).elim

end OneMfld
