/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Iterated

/-!
# Laurent coefficients on products of circular domains

Circle coefficients are analytic in the remaining coordinates. Iteration therefore proves
independence of the coordinate radii on products of connected circular domains.

## Main results

`analyticOnNhd_circleLaurentCoeff_cons` is holomorphy of a circle coefficient in the remaining
coordinates. `multivariableLaurentCoeff_eq_on_product` is independence of radii on a product of
connected circular domains. `multivariableLaurentCoeff_neg_on_product` vanishes negative
exponents in a factor that is a disc.
-/

public noncomputable section

open Complex Set Metric Function
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Combining an analytic first coordinate and analytic remaining coordinates is analytic. -/
private theorem analyticAt_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : E} {f : E → ℂ} {g : E → (Fin n → ℂ)}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun x => (Fin.cons (f x) (g x) : Fin (n + 1) → ℂ)) a := by
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt (g a)).comp hg

/-- Rotation invariance of each factor puts the entire coefficient torus in the product. -/
theorem torusMap_mem_product {V : Fin n → Set ℂ}
    (hrot : ∀ i, ∀ z ∈ V i, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V i)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrV : ∀ i, (r i : ℂ) ∈ V i)
    (θ : Fin n → ℝ) : torusMap 0 r θ ∈ Set.pi univ V := by
  intro i _
  apply hrot i _ (hrV i)
  simp [torusMap, abs_of_pos (hr i)]

/-- Taking the first circle coefficient preserves analyticity in the remaining coordinates. -/
theorem analyticOnNhd_circleLaurentCoeff_cons {V : Fin (n + 1) → Set ℂ}
    (ho : ∀ i, IsOpen (V i))
    (hrot : ∀ i, ∀ z ∈ V i, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V i)
    {f : (Fin (n + 1) → ℂ) → F} (hf : AnalyticOnNhd ℂ f (Set.pi univ V))
    {r : ℝ} (hr : 0 < r) (hrV : (r : ℂ) ∈ V 0) (k : ℤ) :
    AnalyticOnNhd ℂ (fun y => circleLaurentCoeff (fun x => f (Fin.cons x y)) r k)
      (Set.pi univ (V ∘ Fin.succ)) := by
  let W := {p : (Fin n → ℂ) × ℂ | Fin.cons p.2 p.1 ∈ Set.pi univ V}
  have hH : AnalyticOnNhd ℂ (fun p : (Fin n → ℂ) × ℂ => f (Fin.cons p.2 p.1)) W :=
    fun p hp => (hf _ hp).comp_of_eq (analyticAt_fin_cons (f := Prod.snd) (g := Prod.fst) (a := p)
      analyticAt_snd analyticAt_fst) rfl
  apply analyticOnNhd_circleLaurentCoeff
    (isOpen_set_pi finite_univ (fun i _ => ho i.succ)) hH hr
  intro y hy w hw
  change Fin.cons w y ∈ Set.pi univ V
  intro i _
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hrot 0 _ hrV w (by simpa [abs_of_pos hr] using mem_sphere_zero_iff_norm.mp hw)
  · exact hy j (mem_univ _)

/-- In a product of connected circular domains, Laurent coefficients are independent of radii. -/
theorem multivariableLaurentCoeff_eq_on_product {V : Fin n → Set ℂ}
    (ho : ∀ i, IsOpen (V i)) (hc : ∀ i, IsConnected (V i))
    (hrot : ∀ i, ∀ z ∈ V i, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V i)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f (Set.pi univ V))
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrV : ∀ i, (r i : ℂ) ∈ V i) (hsV : ∀ i, (s i : ℂ) ∈ V i) :
    multivariableLaurentCoeff f s = multivariableLaurentCoeff f r := by
  induction n with
  | zero => rw [Subsingleton.elim s r]
  | succ n ih =>
    have hcont (t : Fin (n + 1) → ℝ) (ht : ∀ i, 0 < t i) (htV : ∀ i, (t i : ℂ) ∈ V i) :
        Continuous (fun θ => f (torusMap 0 t θ)) :=
      hf.continuousOn.comp_continuous (continuous_torusMap 0 t)
        (torusMap_mem_product hrot ht htV)
    funext m
    rw [multivariableLaurentCoeff_succ hs (hcont s hs hsV),
      multivariableLaurentCoeff_succ hr (hcont r hr hrV)]
    let a (t : ℝ) (y : Fin n → ℂ) := circleLaurentCoeff (fun x => f (Fin.cons x y)) t (m 0)
    have ha : AnalyticOnNhd ℂ (a (r 0)) (Set.pi univ (V ∘ Fin.succ)) :=
      analyticOnNhd_circleLaurentCoeff_cons ho hrot hf (hr 0) (hrV 0) (m 0)
    have heq : EqOn (a (s 0)) (a (r 0)) (Set.pi univ (V ∘ Fin.succ)) := by
      intro y hy
      have hfy : AnalyticOnNhd ℂ (fun x => f (Fin.cons x y)) (V 0) := by
        intro x hx
        apply (hf _ ?_).comp_of_eq
          (analyticAt_fin_cons (f := id) (g := fun _ : ℂ => y) analyticAt_id analyticAt_const) rfl
        intro i _
        exact Fin.cases hx (fun j => hy j (mem_univ _)) i
      exact congrFun (circleLaurentCoeff_eq_of_connected (hc 0) (hrot 0) hfy
        (hr 0) (hs 0) (hrV 0) (hsV 0)) (m 0)
    have he := multivariableLaurentCoeff_congr (r := s ∘ Fin.succ) (fun θ =>
      heq (torusMap_mem_product (fun i => hrot i.succ) (fun i => hs i.succ)
          (fun i => hsV i.succ) θ))
    change multivariableLaurentCoeff (a (s 0)) (s ∘ Fin.succ) (m ∘ Fin.succ) = _
    rw [he]
    exact congrFun (ih (fun i => ho i.succ) (fun i => hc i.succ) (fun i => hrot i.succ) ha
      (r := r ∘ Fin.succ) (s := s ∘ Fin.succ)
      (fun i => hr i.succ) (fun i => hs i.succ) (fun i => hrV i.succ) (fun i => hsV i.succ))
      (m ∘ Fin.succ)

/-- Negative coefficients vanish in a product when the corresponding factor contains zero. -/
theorem multivariableLaurentCoeff_neg_on_product {V : Fin n → Set ℂ}
    (ho : ∀ i, IsOpen (V i)) (hc : ∀ i, IsConnected (V i))
    (hrot : ∀ i, ∀ z ∈ V i, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V i)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f (Set.pi univ V))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrV : ∀ i, (r i : ℂ) ∈ V i)
    (m : Fin n → ℤ) (i : Fin n) (hi : 0 ∈ V i) (hm : m i < 0) :
    multivariableLaurentCoeff f r m = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hcont : Continuous (fun θ => f (torusMap 0 r θ)) :=
      hf.continuousOn.comp_continuous (continuous_torusMap 0 r)
        (torusMap_mem_product hrot hr hrV)
    rw [multivariableLaurentCoeff_succ hr hcont]
    cases i using Fin.cases with
    | zero =>
      have he : multivariableLaurentCoeff
          (fun y => circleLaurentCoeff (fun x => f (Fin.cons x y)) (r 0) (m 0))
          (r ∘ Fin.succ) = multivariableLaurentCoeff (fun _ => (0 : F)) (r ∘ Fin.succ) := by
        apply multivariableLaurentCoeff_congr
        intro θ
        let y := torusMap 0 (r ∘ Fin.succ) θ
        have hy := torusMap_mem_product (fun i => hrot i.succ) (fun i => hr i.succ)
          (fun i => hrV i.succ) θ
        have hfy : AnalyticOnNhd ℂ (fun x => f (Fin.cons x y)) (V 0) := by
          intro x hx
          apply (hf _ ?_).comp_of_eq
            (analyticAt_fin_cons (f := id) (g := fun _ : ℂ => y) analyticAt_id analyticAt_const) rfl
          intro i _
          exact Fin.cases hx (fun j => hy j (mem_univ _)) i
        exact (circleLaurent_expansion (ho 0) (hc 0) (hrot 0) hfy (hr 0) (hrV 0)).2.2 hi (m 0) hm
      rw [he]
      simp [multivariableLaurentCoeff, torusIntegral]
    | succ j =>
      exact ih (fun i => ho i.succ) (fun i => hc i.succ) (fun i => hrot i.succ)
        (analyticOnNhd_circleLaurentCoeff_cons ho hrot hf (hr 0) (hrV 0) (m 0))
        (r := r ∘ Fin.succ) (fun i => hr i.succ) (fun i => hrV i.succ)
        (m ∘ Fin.succ) j hi hm

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
