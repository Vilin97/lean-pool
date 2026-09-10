/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod

public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Order.Ring.NNRat

/-!
# Density lemmas for finite sets
-/

namespace Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}


@[simp]
public
lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [dens, mul_div_mul_comm]

variable [DecidableEq α]



@[grind =]
public
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [sdiff_union_of_subset h] at this
  rw [dens_union_of_disjoint sdiff_disjoint, add_tsub_cancel_right]

public
lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact dens_inter_add_dens_union ..



public
lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (dens_mono h)]

end Finset
