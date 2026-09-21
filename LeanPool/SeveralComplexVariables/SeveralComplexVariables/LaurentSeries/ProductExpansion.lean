/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Convergence

/-!
# Laurent expansion by successive circle expansions

On circular products, induction on the number of coordinates combines the circle Laurent theorem
with Fubini for absolutely summable families. Circular product neighborhoods then give pointwise
expansion on every Reinhardt domain.

## Main results

`hasSum_multivariableLaurent_on_product` is the expansion on a finite product of circular
domains. `hasSum_multivariableLaurent` is the pointwise expansion at an arbitrary point of an
open Reinhardt domain.
-/

public noncomputable section

open Complex Set Filter
open scoped Topology NNReal

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Fixing all but the first coordinate preserves analyticity on a product. -/
private theorem analyticOnNhd_first_slice {V : Fin (n + 1) → Set ℂ}
    {f : (Fin (n + 1) → ℂ) → F} (hf : AnalyticOnNhd ℂ f (Set.pi univ V))
    {y : Fin n → ℂ} (hy : y ∈ Set.pi univ (V ∘ Fin.succ)) :
    AnalyticOnNhd ℂ (fun x => f (Fin.cons x y)) (V 0) := by
  intro x hx
  have hg : AnalyticAt ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) x := by
    apply AnalyticAt.pi
    intro i
    exact Fin.cases analyticAt_id (fun _ => analyticAt_const) i
  apply (hf _ ?_).comp_of_eq hg rfl
  intro i _
  exact Fin.cases hx (fun j => hy j (mem_univ _)) i

/-- Successive one-variable Laurent expansions give the expansion on a circular product. -/
theorem hasSum_multivariableLaurent_on_product {V : Fin n → Set ℂ}
    (ho : ∀ i, IsOpen (V i)) (hc : ∀ i, IsConnected (V i))
    (hrot : ∀ i, ∀ x ∈ V i, ∀ w : ℂ, ‖w‖ = ‖x‖ → w ∈ V i)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f (Set.pi univ V))
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrV : ∀ i, (r i : ℂ) ∈ V i)
    {z : Fin n → ℂ} (hz : z ∈ Set.pi univ V) :
    HasSum (fun m => multivariableLaurentTerm (multivariableLaurentCoeff f r) m z) (f z) := by
  induction n with
  | zero =>
    convert hasSum_fintype (fun m => multivariableLaurentTerm (multivariableLaurentCoeff f r) m z)
      using 1
    simp only [multivariableLaurentTerm, multivariableLaurentCoeff, torusIntegral_dim0,
      Fin.prod_univ_zero, pow_zero, inv_one, one_smul, Finset.sum_const, Finset.card_univ,
      Fintype.card_unique]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let a (k : ℤ) (y : Fin n → ℂ) := circleLaurentCoeff (fun x => f (Fin.cons x y)) (r 0) k
    have ha (k : ℤ) : AnalyticOnNhd ℂ (a k) (Set.pi univ (V ∘ Fin.succ)) :=
      analyticOnNhd_circleLaurentCoeff_cons ho hrot hf (hr 0) (hrV 0) k
    have hz' : z ∘ Fin.succ ∈ Set.pi univ (V ∘ Fin.succ) := fun i _ => hz i.succ (mem_univ _)
    have hinner (k : ℤ) : HasSum
        (fun m => z 0 ^ k • multivariableLaurentTerm
          (multivariableLaurentCoeff (a k) (r ∘ Fin.succ)) m (z ∘ Fin.succ))
        (z 0 ^ k • a k (z ∘ Fin.succ)) := by
      apply HasSum.const_smul
      exact ih (V := V ∘ Fin.succ) (f := a k) (z := z ∘ Fin.succ)
        (fun i => ho i.succ) (fun i => hc i.succ) (fun i => hrot i.succ) (ha k)
        (r := r ∘ Fin.succ) (fun i => hr i.succ) (fun i => hrV i.succ) hz'
    have houter := (circleLaurent_expansion (ho 0) (hc 0) (hrot 0)
      (analyticOnNhd_first_slice hf hz') (hr 0) (hrV 0)).1 (z 0) (hz 0 (mem_univ _))
    have hR : IsReinhardt (Set.pi univ V) := by
      intro x hx w hw i _
      exact hrot i _ (hx i (mem_univ _)) _ (hw i)
    have habs := summable_norm_multivariableLaurent
      (isOpen_set_pi finite_univ (fun i _ => ho i))
      (isPreconnected_univ_pi (fun i => (hc i).isPreconnected)) hR hf hr
      (fun i _ => hrV i) hz
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    have hp := e.summable_iff.mpr habs.of_norm
    have hcont : Continuous (fun θ => f (torusMap 0 r θ)) :=
      hf.continuousOn.comp_continuous (continuous_torusMap 0 r)
        (torusMap_mem_product hrot hr hrV)
    have hterm (k : ℤ) (m : Fin n → ℤ) :
        multivariableLaurentTerm (multivariableLaurentCoeff f r) (e (k, m)) z =
          z 0 ^ k • multivariableLaurentTerm (multivariableLaurentCoeff (a k) (r ∘ Fin.succ)) m
            (z ∘ Fin.succ) := by
      rw [multivariableLaurentTerm, multivariableLaurentCoeff_succ hr hcont]
      simp [multivariableLaurentTerm, e, Fin.consEquiv, Fin.prod_univ_succ, a,
        Function.comp_def, smul_smul]
    have hsum := hp.hasSum.prod_fiberwise (fun k =>
      (hinner k).congr_fun (fun m => hterm k m))
    have heq := hsum.unique houter
    apply e.hasSum_iff.mp
    convert hp.hasSum using 1
    have hzcons : Fin.cons (z 0) (z ∘ Fin.succ) = z := Fin.cons_self_tail z
    simpa only [hzcons] using heq.symm

/-- Every analytic function on an open connected Reinhardt set equals its Laurent series. -/
theorem hasSum_multivariableLaurent {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    {z : Fin n → ℂ} (hz : z ∈ U) :
    HasSum (fun m => multivariableLaurentTerm (multivariableLaurentCoeff f r) m z) (f z) := by
  obtain ⟨V, hVo, hVc, hVr, hzV, hVU⟩ := hR.exists_circular_product_neighborhood ho hz
  have hprod : IsReinhardt (Set.pi univ V) := by
    intro x hx y hy j _
    exact hVr j _ (hx j (mem_univ _)) _ (hy j)
  obtain ⟨s, hsV, hs⟩ := hprod.exists_strict_modulus_majorant
    (isOpen_set_pi finite_univ (fun i _ => hVo i)) hzV
  have hspos (j : Fin n) : 0 < (s j : ℝ) := by
    exact_mod_cast (show (0 : ℝ≥0) ≤ ‖z j‖₊ from zero_le).trans_lt (hs j)
  rw [← multivariableLaurentCoeff_eq_of_radii ho hc hR hf hr hspos hrU (hVU hsV)]
  exact hasSum_multivariableLaurent_on_product hVo hVc hVr (hf.mono hVU) hspos
    (fun i => hsV i (mem_univ _)) hzV

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
