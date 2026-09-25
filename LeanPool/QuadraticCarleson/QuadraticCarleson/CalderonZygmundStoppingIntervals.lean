/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundDyadicStopping

/-!
# Converting canonical dyadic stopping cells to centered intervals

The analytic atom estimates use a center and a length, while the canonical
stopping construction uses half-open dyadic cells. The project's centered
interval convention is also half-open, so this file supplies an exact set
identity and transfers literal pairwise disjointness without a boundary loss.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace CalderonZygmundStoppingIntervals

open CalderonZygmundDyadicStopping


noncomputable
section

/-- Center of the canonical half-open stopping interval. -/
def stoppingCenter {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  ((c.1.index : ℝ) + 1 / 2) * dyadicLength (rootLength f) c.1.depth

/-- Length of the canonical half-open stopping interval. -/
def stoppingLength {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  dyadicLength (rootLength f) c.1.depth

theorem stoppingLength_pos {f : ℝ → ℂ} (c : stoppingCell f) :
    0 < stoppingLength c :=
  dyadicLength_pos rootLength_pos c.1.depth

/-- The centered representative has the same half-open endpoints as the
stopping cell. -/
theorem centeredInterval_stopping_eq_Ico {f : ℝ → ℂ} (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =
      Ico ((c.1.index : ℝ) * stoppingLength c)
        (((c.1.index : ℝ) + 1) * stoppingLength c) := by
  unfold centeredInterval stoppingCenter stoppingLength
  congr 1 <;> ring

theorem stoppingInterval_eq_Ico {f : ℝ → ℂ} (c : stoppingCell f) :
    c.1.interval (rootLength f) =
      Ico ((c.1.index : ℝ) * stoppingLength c)
        (((c.1.index : ℝ) + 1) * stoppingLength c) := by
  rfl

/-- Exact conversion from a canonical cell to its center/length form. -/
theorem centeredInterval_eq_stoppingInterval {f : ℝ → ℂ}
    (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =
      c.1.interval (rootLength f) := by
  rw [centeredInterval_stopping_eq_Ico, stoppingInterval_eq_Ico]

theorem centeredInterval_ae_eq_stoppingInterval {f : ℝ → ℂ}
    (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =ᵐ[volume]
      c.1.interval (rootLength f) :=
  Filter.Eventually.of_forall fun x ↦ Set.ext_iff.mp
    (centeredInterval_eq_stoppingInterval c) x |> propext

/-- Center/length representatives of distinct stopping cells are literally
pairwise disjoint. -/
theorem centeredStoppingIntervals_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Function.onFun Disjoint fun c : stoppingCell f ↦
      centeredInterval (stoppingCenter c) (stoppingLength c)) := by
  intro c d hcd
  simpa only [centeredInterval_eq_stoppingInterval] using
    stoppingCell_pairwiseDisjoint hcd

/-- The corresponding almost-everywhere disjointness statement. -/
theorem centeredStoppingIntervals_pairwiseAEDisjoint {f : ℝ → ℂ} :
    Pairwise (Function.onFun (AEDisjoint volume) fun c : stoppingCell f ↦
      centeredInterval (stoppingCenter c) (stoppingLength c)) := by
  exact centeredStoppingIntervals_pairwiseDisjoint.aedisjoint

/-- Set integrals over the centered representative and the canonical stopping
cell agree. -/
theorem setIntegral_centeredStopping_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℂ} (c : stoppingCell f) (g : ℝ → E) :
    (∫ x in centeredInterval (stoppingCenter c) (stoppingLength c), g x) =
      ∫ x in c.1.interval (rootLength f), g x := by
  rw [centeredInterval_eq_stoppingInterval]

/-- The centered interval has exactly the stopping-cell length. -/
theorem volume_centeredStoppingInterval {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (centeredInterval (stoppingCenter c) (stoppingLength c)) =
      ENNReal.ofReal (stoppingLength c) := by
  rw [centeredInterval_stopping_eq_Ico, Real.volume_Ico]
  congr 1
  ring

end
end CalderonZygmundStoppingIntervals
end QuadraticCarleson
