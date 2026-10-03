/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnsatzProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.AnsatzGradient

/-! The finite-sum product rule for the material derivative of an ansatz. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- A finite model for the corrector ansatz at a space-time point. -/
def finiteAnsatzField {ι : Type*} (S : Finset ι)
    (T H : ℝ → Vec 2 → ℝ) (ξ : ι → ℝ → ℝ)
    (χ G : ι → ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  T t x + (∑ k ∈ S, ξ k t * vecDot (χ k t x) (G k t x)) + H t x

/-- Differentiate the finite corrector ansatz in time and along a spatial
direction. This is the product-rule bridge used in `e.timecomp.0`; local
finiteness of the cutoff sum is handled separately by
`ansatz_hasDerivAt`. -/
theorem finiteAnsatz_material_expansion
    {ι : Type*} (S : Finset ι)
    (T H : ℝ → Vec 2 → ℝ) (ξ : ι → ℝ → ℝ)
    (χ G : ι → ℝ → Vec 2 → Vec 2)
    (t : ℝ) (x v : Vec 2)
    (Tt Ht : ℝ) (ξt : ι → ℝ) (χt Gt : ι → Vec 2)
    (LT LH : Vec 2 →L[ℝ] ℝ)
    (Lχ LG : ι → Vec 2 →L[ℝ] Vec 2)
    (hTt : HasDerivAt (fun s => T s x) Tt t)
    (hHt : HasDerivAt (fun s => H s x) Ht t)
    (hξt : ∀ k ∈ S, HasDerivAt (ξ k) (ξt k) t)
    (hχt : ∀ k ∈ S, HasDerivAt (fun s => χ k s x) (χt k) t)
    (hGt : ∀ k ∈ S, HasDerivAt (fun s => G k s x) (Gt k) t)
    (hTx : HasFDerivAt (T t) LT x)
    (hHx : HasFDerivAt (H t) LH x)
    (hχx : ∀ k ∈ S, HasFDerivAt (χ k t) (Lχ k) x)
    (hGx : ∀ k ∈ S, HasFDerivAt (G k t) (LG k) x) :
    deriv (fun s => finiteAnsatzField S T H ξ χ G s x) t +
        fderiv ℝ (finiteAnsatzField S T H ξ χ G t) x v =
      Tt + Ht +
        (∑ k ∈ S,
          (ξt k * vecDot (χ k t x) (G k t x) +
            ξ k t * (vecDot (χt k) (G k t x) +
              vecDot (χ k t x) (Gt k)))) +
        (LT v +
          (∑ k ∈ S, ξ k t *
            (vecDot (Lχ k v) (G k t x) +
              vecDot (χ k t x) (LG k v))) + LH v) := by
  let P : ι → Vec 2 → ℝ := fun k y => vecDot (χ k t y) (G k t y)
  let LP : ι → Vec 2 →L[ℝ] ℝ := fun k =>
    vecDotDerivativeAt (χ := χ k t) (G := G k t) x (Lχ k) (LG k)
  have hP : ∀ k ∈ S, HasFDerivAt (P k) (LP k) x := by
    intro k hk
    exact hasFDerivAt_vecDot (hχx k hk) (hGx k hk)
  let Lsum : Vec 2 →L[ℝ] ℝ := ∑ k ∈ S, (ξ k t) • LP k
  have hsum : HasFDerivAt (fun y => ∑ k ∈ S, ξ k t * P k y) Lsum x := by
    have hfun : (fun y => ∑ k ∈ S, ξ k t * P k y) =
        ∑ k ∈ S, (fun y => ξ k t * P k y) := by
      funext y
      simp
    rw [hfun]
    apply HasFDerivAt.sum
    intro k hk
    simpa [Lsum, smul_eq_mul] using (hP k hk).const_mul (ξ k t)
  have hspace : HasFDerivAt
      (fun y => finiteAnsatzField S T H ξ χ G t y)
      (LT + Lsum + LH) x := by
    convert hTx.add hsum |>.add hHx using 1
    funext y
    simp [finiteAnsatzField, P]
  have htime := hasDerivAt_finiteAnsatz S
    (fun s => T s x) (fun s => H s x) (fun _ => Tt) (fun _ => Ht)
    (fun k s => ξ k s) (fun k _ => ξt k)
    (fun k s => χ k s x) (fun k s => G k s x)
    (fun k _ => χt k) (fun k _ => Gt k) hTt hHt hξt hχt hGt
  have hpair (k : ι) (hk : k ∈ S) :
      fderiv ℝ (P k) x v =
        vecDot (Lχ k v) (G k t x) +
          vecDot (χ k t x) (LG k v) := by
    rw [(hP k hk).fderiv]
    simp [LP, vecDotDerivativeAt, vecDot, Fin.sum_univ_two,
      ContinuousLinearMap.comp_apply]
    ring
  have htime' : deriv (fun s => finiteAnsatzField S T H ξ χ G s x) t =
      Tt + (∑ k ∈ S,
        (ξt k * vecDot (χ k t x) (G k t x) +
          ξ k t * (vecDot (χt k) (G k t x) + vecDot (χ k t x) (Gt k)))) + Ht := by
    simpa [finiteAnsatzField] using htime.deriv
  have hspace' : fderiv ℝ (finiteAnsatzField S T H ξ χ G t) x v =
      LT v + (∑ k ∈ S, ξ k t *
        (vecDot (Lχ k v) (G k t x) + vecDot (χ k t x) (LG k v))) + LH v := by
    rw [hspace.fderiv]
    simp only [add_apply]
    have hLsum : Lsum v = ∑ k ∈ S, ξ k t *
        (vecDot (Lχ k v) (G k t x) + vecDot (χ k t x) (LG k v)) := by
      simp only [Lsum, sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      change (ξ k t) * (LP k v) = _
      rw [← (hP k hk).fderiv, hpair k hk]
    rw [hLsum]
  rw [htime', hspace']
  abel

end AVenhance.Infra.Section5
