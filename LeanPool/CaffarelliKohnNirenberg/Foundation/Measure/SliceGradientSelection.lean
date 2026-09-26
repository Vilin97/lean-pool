/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientBumps
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceMollifierIdentity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceProductMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# A jointly measurable space-time weak gradient from slice-wise weak gradients

Lemma `lem:delta-p` of the paper produces, for almost every time `t`, a spatial
weak derivative of the pressure slice `p (·, t)` on a ball `B`.  Nothing in that
statement says that the family of slice derivatives can be chosen jointly
measurable in space and time, and the almost-everywhere uniqueness of a weak
derivative pins each slice down only up to a null set of its own.  The theorems
below supply the missing selection.

The construction is a mollification.  With `φ n` the normalized bump of outer
radius `sliceRadius n` and inner radius half of that, the function

`G n (x, t) = ∫ y, (∂ₖ φ n) y * p (x - y, t) dy`

is an explicit integral of a jointly measurable integrand, hence jointly
measurable; and for each good time `t` and each `x` whose closed
`sliceRadius n`-ball stays inside the domain, the defining integration-by-parts
identity of `HasWeakPartialDerivOn` turns it into the mollification of the slice
derivative at `x`.  Mathlib's almost-everywhere convergence of mollifications
(External Input `ext:mollify`) then makes `G n (x, t)` converge to the slice
derivative at `x` for almost every `x`, so the pointwise limit

`Dp z = limUnder atTop (fun n => G n z)`

is a single space-time function that restricts to a weak derivative on almost
every slice.  The limit is `Filter.limUnder`, whose junk value off the
convergence set is harmless: every conclusion is stated almost everywhere on the
inner box.

The identity in the last conclusion is first proved in its iterated form
`∫ t in J, ∫ x in B'`, which needs no integrability of `Dp` at all;
`setIntegral_prod_eq_of_iterated` upgrades it to an integral over the product
box once both integrands are integrable there.

The data is truncated to an intermediate open set `W` with
`closure B' ⊆ W ⊆ closure W ⊆ B` before it is mollified, so that the truncated
slices are globally integrable and Mathlib's convergence theorem applies; only
the conclusions on `B'` are used.

Space-time points use the ordinary product space `Vec3 × ℝ` of docs/DESIGN_NOTES.md, the
carrier on which `spatialPartial` and `spaceTimeTestFunction` are stated.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology ENNReal
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Between a compact set and an open neighbourhood there is an open set `W` whose closure is a
compact subset of the neighbourhood, and a radius `δ` such that every closed ball of radius at
most `δ` centred on the compact set is contained in `W`. -/
theorem exists_open_between_of_isCompact {d : ℕ} {s t : Set (Vec d)} (hs : IsCompact s)
    (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ (W : Set (Vec d)) (δ : ℝ), 0 < δ ∧ IsOpen W ∧ s ⊆ W ∧ IsCompact (closure W) ∧
      closure W ⊆ t ∧ ∀ x ∈ s, ∀ ε : ℝ, 0 < ε → ε ≤ δ → Metric.closedBall x ε ⊆ W := by
  obtain ⟨δ, hδpos, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  refine ⟨Metric.thickening δ s, δ / 2, by positivity, Metric.isOpen_thickening, ?_, ?_, ?_, ?_⟩
  · exact Metric.self_subset_thickening hδpos s
  · exact (hs.cthickening (r := δ)).of_isClosed_subset isClosed_closure
      (Metric.closure_thickening_subset_cthickening δ s)
  · exact (Metric.closure_thickening_subset_cthickening δ s).trans hδ
  · intro x hx ε hε hεδ y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, lt_of_le_of_lt hy (by linarith only [hεδ, hδpos])⟩

/-- A spatial slice of a compact space-time set is compact. -/
theorem isCompact_slice_of_isCompact {K : Set (Vec3 × ℝ)} (hK : IsCompact K) (t : ℝ) :
    IsCompact {x : Vec3 | (x, t) ∈ K} := by
  have hEq : {x : Vec3 | (x, t) ∈ K}
      = Prod.fst '' (K ∩ (Prod.snd ⁻¹' ({t} : Set ℝ))) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, t), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨hzK, hzt⟩, rfl⟩
      have hz2 : z.2 = t := hzt
      have hzeq : (z.1, t) = z := Prod.ext rfl hz2.symm
      change (z.1, t) ∈ K
      rw [hzeq]
      exact hzK
  rw [hEq]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

/-- The spatial slice of a space-time test function is a spatial test function. -/
theorem slice_testFunction {Ψ : Vec3 × ℝ → ℝ} {B' : Set Vec3} {J : Set ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) (hΨs : tsupport Ψ ⊆ B' ×ˢ J)
    (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => Ψ (x, t)) ∧
      HasCompactSupport (fun x : Vec3 => Ψ (x, t)) ∧
      tsupport (fun x : Vec3 => Ψ (x, t)) ⊆ B' := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => Ψ (x, t)) :=
    hΨ.comp (contDiff_id.prodMk contDiff_const)
  have hsubset : tsupport (fun x : Vec3 => Ψ (x, t)) ⊆ {x : Vec3 | (x, t) ∈ tsupport Ψ} := by
    have hclosed : IsClosed {x : Vec3 | (x, t) ∈ tsupport Ψ} :=
      (isClosed_tsupport Ψ).preimage (continuous_id.prodMk continuous_const)
    refine closure_minimal ?_ hclosed
    intro x hx
    exact subset_tsupport Ψ hx
  have hcompact : HasCompactSupport (fun x : Vec3 => Ψ (x, t)) :=
    IsCompact.of_isClosed_subset (isCompact_slice_of_isCompact hΨc t) (isClosed_tsupport _) hsubset
  refine ⟨hsmooth, hcompact, hsubset.trans ?_⟩
  intro x hx
  exact (hΨs hx).1

/-- The iterated space-time identity becomes an identity of integrals over the product box as
soon as both integrands are integrable there. -/
theorem setIntegral_prod_eq_of_iterated {B' : Set Vec3} {J : Set ℝ}
    {F H : Vec3 × ℝ → ℝ}
    (hF : IntegrableOn F (B' ×ˢ J) volume) (hH : IntegrableOn H (B' ×ˢ J) volume)
    (h : (∫ t in J, ∫ x in B', F (x, t)) = -∫ t in J, ∫ x in B', H (x, t)) :
    ∫ z in B' ×ˢ J, F z = -∫ z in B' ×ˢ J, H z := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B' ×ˢ J)
      = ((volume : Measure Vec3).restrict B').prod ((volume : Measure ℝ).restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hF' : Integrable F (((volume : Measure Vec3).restrict B').prod
      ((volume : Measure ℝ).restrict J)) := by rw [← hprod]; exact hF
  have hH' : Integrable H (((volume : Measure Vec3).restrict B').prod
      ((volume : Measure ℝ).restrict J)) := by rw [← hprod]; exact hH
  rw [show ∫ z in B' ×ˢ J, F z = ∫ z, F z ∂(((volume : Measure Vec3).restrict B').prod
      ((volume : Measure ℝ).restrict J)) by rw [← hprod],
    show ∫ z in B' ×ˢ J, H z = ∫ z, H z ∂(((volume : Measure Vec3).restrict B').prod
      ((volume : Measure ℝ).restrict J)) by rw [← hprod],
    integral_prod_symm F hF', integral_prod_symm H hH']
  exact h

private lemma exists_spacetime_weak_gradient_hkey_1 :
    ∀ (k : Fin 3) {B B' : Set Vec3} {J : Set ℝ} {p : Vec3 × ℝ → ℝ},
      MeasurableSet B' →
        ∀ (W : Set (Vec 3)) (δ : ℝ),
          IsCompact (closure W) →
            closure W ⊆ B →
              (∀ x ∈ closure B', ∀ (ε : ℝ), 0 < ε → ε ≤ δ → Metric.closedBall x ε ⊆ W) →
                B' ⊆ W →
                  MeasurableSet W →
                    W ⊆ B →
                      ∀
                        (hpmk :
                          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
                            (Measure.restrict volume (B ×ˢ J))),
                        let p₀ : Vec3 × ℝ → ℝ := AEStronglyMeasurable.mk p hpmk;
                        let P : Vec3 × ℝ → ℝ := (SProd.sprod (β := Set ℝ) W univ).indicator p₀;
                        let Kn : ℕ → Vec3 → ℝ := fun n y =>
                          (fderiv ℝ (mollifier (sliceRadius n) (sliceRadius_pos n)) y)
                            (basisVec k);
                        let G : ℕ → Vec3 × ℝ → ℝ := fun n z =>
                          @integral _ _ _ _ MeasureSpace.toMeasurableSpace volume
                            fun (y : Vec3) => Kn n y * P (z.1 - y, z.2);
                        (∀ᶠ (n : ℕ) in atTop, sliceRadius n ≤ δ) →
                          (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                              IntegrableOn (ε := ℝ) (mα := MeasureSpace.toMeasurableSpace)
                                (fun x => p (x, t)) B volume) →
                            (∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                                (fun x => p (x, t)) =ᵐ[Measure.restrict volume B] fun x =>
                                  p₀ (x, t)) →
                              ∀ᵐ (t : ℝ) ∂Measure.restrict volume J,
                                ∀ (g : Vec3 → ℝ),
                                  LocallyIntegrableOn g B volume →
                                    HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
                                      ∀ᵐ (x : Vec3) ∂Measure.restrict volume B',
                                        Tendsto (fun (n : ℕ) => G n (x, t)) atTop (𝓝 (g x))
    := by
  intro k B B' J p hB' W δ hWcompact hWB hWball hB'sub hWmeas hWsubB hpmk p₀ P Kn G hradius
    hpslice hp₀slice
  filter_upwards [hpslice, hp₀slice] with t htint htmk g hgloc hgweak
  set u : Vec3 → ℝ := W.indicator (fun x => p₀ (x, t)) with hudef
  have huW : ∀ x ∈ W, u x = p₀ (x, t) := by
    intro x hx
    change W.indicator (fun x => p₀ (x, t)) x = p₀ (x, t)
    exact Set.indicator_of_mem hx _
  have hPu : ∀ x : Vec3, P (x, t) = u x := by
    intro x
    by_cases hx : x ∈ W
    · change (W ×ˢ (univ : Set ℝ)).indicator p₀ (x, t) = u x
      rw [Set.indicator_of_mem (show ((x, t) : Vec3 × ℝ) ∈ W ×ˢ (univ : Set ℝ) from
        ⟨hx, Set.mem_univ t⟩), huW x hx]
    · change (W ×ˢ (univ : Set ℝ)).indicator p₀ (x, t) = u x
      rw [Set.indicator_of_notMem (show ((x, t) : Vec3 × ℝ) ∉ W ×ˢ (univ : Set ℝ) from
        fun h => hx h.1)]
      change (0 : ℝ) = W.indicator (fun x => p₀ (x, t)) x
      rw [Set.indicator_of_notMem hx]
  have hGval : ∀ (n : ℕ) (x : Vec3), G n (x, t) = ∫ y, Kn n y * u (x - y) ∂volume := by
    intro n x
    change (∫ y, Kn n y * P (x - y, t) ∂volume) = ∫ y, Kn n y * u (x - y) ∂volume
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change Kn n y * P (x - y, t) = Kn n y * u (x - y)
    rw [hPu (x - y)]
  have hpW : IntegrableOn (fun x => p (x, t)) W volume := htint.mono_set hWsubB
  have hp₀W : IntegrableOn (fun x => p₀ (x, t)) W volume :=
    hpW.congr (htmk.filter_mono (ae_mono (Measure.restrict_mono hWsubB le_rfl)))
  have huInt : Integrable u volume := hp₀W.integrable_indicator hWmeas
  have huLoc : LocallyIntegrable u volume := huInt.locallyIntegrable
  have hgW : IntegrableOn g W volume :=
    (hgloc.integrableOn_compact_subset hWB hWcompact).mono_set subset_closure
  have hgWind : Integrable (W.indicator g) volume := hgW.integrable_indicator hWmeas
  have hgWloc : LocallyIntegrable (W.indicator g) volume := hgWind.locallyIntegrable
  have hgWval : ∀ x ∈ W, (W.indicator g) x = g x := fun x hx => Set.indicator_of_mem hx g
  -- the weak-derivative identity for the truncated data
  have hweakW : HasWeakPartialDerivOn W k u (W.indicator g) := by
    intro ψ hψ hψc hψW
    have hDψzero : ∀ x, x ∉ W → (fderiv ℝ ψ x) (basisVec k) = 0 := by
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hψW h))]
      simp
    have hψzero : ∀ x, x ∉ W → ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψW h))
    have h1 : ∫ x in W, u x * (fderiv ℝ ψ x) (basisVec k) ∂volume
        = ∫ x in W, p₀ (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume := by
      refine setIntegral_congr_fun hWmeas ?_
      intro x hx
      change u x * (fderiv ℝ ψ x) (basisVec k) = p₀ (x, t) * (fderiv ℝ ψ x) (basisVec k)
      rw [huW x hx]
    have h2 : ∫ x in W, p₀ (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume
        = ∫ x in W, p (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [htmk.filter_mono (ae_mono (Measure.restrict_mono hWsubB le_rfl))]
        with x hx
      rw [hx]
    have hLW : ∫ x in W, u x * (fderiv ℝ ψ x) (basisVec k) ∂volume
        = ∫ x, p (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume := by
      rw [h1, h2]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hDψzero x hx, mul_zero])
    have hLB : ∫ x in B, p (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume
        = ∫ x, p (x, t) * (fderiv ℝ ψ x) (basisVec k) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hDψzero x (fun h => hx (hWsubB h)), mul_zero])
    have hRB : ∫ x in B, g x * ψ x ∂volume = ∫ x, g x * ψ x ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hψzero x (fun h => hx (hWsubB h)), mul_zero])
    have h3 : ∫ x in W, (W.indicator g) x * ψ x ∂volume
        = ∫ x in W, g x * ψ x ∂volume := by
      refine setIntegral_congr_fun hWmeas ?_
      intro x hx
      change (W.indicator g) x * ψ x = g x * ψ x
      rw [hgWval x hx]
    have hRW : ∫ x in W, (W.indicator g) x * ψ x ∂volume = ∫ x, g x * ψ x ∂volume := by
      rw [h3]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hψzero x hx, mul_zero])
    have hweak := hgweak ψ hψ hψc (hψW.trans hWsubB)
    rw [hLW, hRW, ← hLB, ← hRB]
    exact hweak
  -- the mollified identity at points of the inner box
  have hmoll : ∀ x ∈ closure B', ∀ n : ℕ, sliceRadius n ≤ δ →
      G n (x, t) = mollify (W.indicator g) (sliceRadius n) (sliceRadius_pos n) x := by
    intro x hx n hn
    rw [hGval n x]
    exact integral_fderiv_mollifier_mul_eq_mollify huLoc hgWloc hweakW (sliceRadius_pos n)
      (hWball x hx (sliceRadius n) (sliceRadius_pos n) hn)
  have haeB' : ∀ᵐ x ∂(volume.restrict B'), Tendsto
      (fun n => mollify (W.indicator g) (sliceRadius n) (sliceRadius_pos n) x)
      atTop (𝓝 ((W.indicator g) x)) :=
    ae_restrict_of_ae (ae_tendsto_mollify_sliceRadius (d := 3) hgWloc)
  filter_upwards [haeB', self_mem_ae_restrict hB'] with x hx hxB'
  rw [hgWval x (hB'sub hxB')] at hx
  refine hx.congr' ?_
  filter_upwards [hradius] with n hn
  exact (hmoll x (subset_closure hxB') n hn).symm

/-- Existence of a jointly measurable space-time weak spatial derivative, given slice-wise weak
derivatives for almost every time.  The four conclusions are joint measurability on the inner
box, identification with *every* slice weak derivative on the inner set at almost every time,
the iterated space-time integration-by-parts identity against test functions supported in the
inner box, and the same identity over the product box whenever both integrands are integrable
there.  The slice hypothesis is the one produced by `lem:delta-p`: the test-function identity of
`HasWeakPartialDerivOn`, holding for almost every time with a locally integrable derivative on
the outer set `B`. -/
theorem exists_spacetime_weak_gradient_of_slices (k : Fin 3)
    {B B' : Set Vec3} {J : Set ℝ} {p : Vec3 × ℝ → ℝ}
    (hB : IsOpen B) (hB' : MeasurableSet B') (hB'c : IsCompact (closure B'))
    (hB'B : closure B' ⊆ B)
    (hp : IntegrableOn p (B ×ˢ J) volume)
    (hslice : ∀ᵐ t ∂(volume.restrict J), ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧ HasWeakPartialDerivOn B k (fun x => p (x, t)) g) :
    ∃ Dp : Vec3 × ℝ → ℝ,
      AEMeasurable Dp (volume.restrict (B' ×ˢ J)) ∧
      (∀ᵐ t ∂(volume.restrict J), ∀ g : Vec3 → ℝ,
        LocallyIntegrableOn g B volume → HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
        (fun x => Dp (x, t)) =ᵐ[volume.restrict B'] g) ∧
      (∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ B' ×ˢ J →
        (∫ t in J, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
          -∫ t in J, ∫ x in B', Dp (x, t) * Ψ (x, t)) ∧
      (∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
        tsupport Ψ ⊆ B' ×ˢ J →
        IntegrableOn (fun z => p z * spatialPartial Ψ k z) (B' ×ˢ J) volume →
        IntegrableOn (fun z => Dp z * Ψ z) (B' ×ˢ J) volume →
        ∫ z in B' ×ˢ J, p z * spatialPartial Ψ k z = -∫ z in B' ×ˢ J, Dp z * Ψ z) := by
  classical
  obtain ⟨W, δ, hδ, hWopen, hB'W, hWcompact, hWB, hWball⟩ :=
    exists_open_between_of_isCompact hB'c hB hB'B
  have hB'sub : B' ⊆ W := subset_closure.trans hB'W
  have hWmeas : MeasurableSet W := hWopen.measurableSet
  have hWsubB : W ⊆ B := subset_closure.trans hWB
  have hB'subB : B' ⊆ B := subset_closure.trans hB'B
  -- A strongly measurable representative of the data.
  have hpmk := hp.aestronglyMeasurable
  set p₀ : Vec3 × ℝ → ℝ := hpmk.mk p with hp₀def
  have hp₀meas : StronglyMeasurable p₀ := hpmk.stronglyMeasurable_mk
  have hp₀ae : p =ᵐ[volume.restrict (B ×ˢ J)] p₀ := hpmk.ae_eq_mk
  -- The datum truncated to the intermediate open set.
  set P : Vec3 × ℝ → ℝ := Set.indicator (W ×ˢ (univ : Set ℝ)) p₀ with hPdef
  have hPmeas : StronglyMeasurable P :=
    hp₀meas.indicator (hWmeas.prod MeasurableSet.univ)
  -- The mollifier derivatives and the approximating family.
  set Kn : ℕ → Vec3 → ℝ := fun n y =>
    (fderiv ℝ (mollifier (d := 3) (sliceRadius n) (sliceRadius_pos n)) y) (basisVec k) with hKndef
  have hKcont : ∀ n, Continuous (Kn n) := by
    intro n
    exact ((mollifier_contDiff (d := 3) (sliceRadius_pos n) (n := 2)).continuous_fderiv
      (by simp)).clm_apply continuous_const
  set G : ℕ → Vec3 × ℝ → ℝ := fun n z => ∫ y, Kn n y * P (z.1 - y, z.2) with hGdef
  have hGmeas : ∀ n, StronglyMeasurable (G n) := fun n =>
    stronglyMeasurable_slice_kernel_integral (hKcont n) hPmeas
  -- The convergence set and the limit.
  set S : Set (Vec3 × ℝ) := {z | ∃ c : ℝ, Tendsto (fun n => G n z) atTop (𝓝 c)} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_exists_tendsto (fun n => (hGmeas n).measurable)
  set Dp : Vec3 × ℝ → ℝ := fun z => limUnder atTop (fun n => G n z) with hDpdef
  have hradius : ∀ᶠ n : ℕ in atTop, sliceRadius n ≤ δ :=
    (tendsto_sliceRadius_atTop.eventually_lt_const hδ).mono fun _ hn => hn.le
  -- Slice-wise consequences of the integrability and measurability of the data.
  have hprodB : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J)
      = ((volume : Measure Vec3).restrict B).prod ((volume : Measure ℝ).restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hpslice : ∀ᵐ t ∂(volume.restrict J),
      IntegrableOn (fun x => p (x, t)) B volume := by
    have h : Integrable p (((volume : Measure Vec3).restrict B).prod
        ((volume : Measure ℝ).restrict J)) := by
      rw [← hprodB]; exact hp
    exact h.prod_left_ae
  have hp₀slice : ∀ᵐ t ∂(volume.restrict J),
      (fun x => p (x, t)) =ᵐ[volume.restrict B] (fun x => p₀ (x, t)) := by
    have h : ∀ᵐ z ∂(((volume : Measure Vec3).restrict B).prod
        ((volume : Measure ℝ).restrict J)), p z = p₀ z := by
      rw [← hprodB]; exact hp₀ae
    exact ae_ae_of_ae_prod_snd h
  -- The core slice-wise convergence statement.
  have hkey := @exists_spacetime_weak_gradient_hkey_1 k B B' J p hB' W δ hWcompact hWB hWball
    hB'sub hWmeas hWsubB hpmk hradius hpslice hp₀slice
  -- Almost-everywhere convergence on the inner box, in both variables jointly.
  have hprodB' : (volume : Measure (Vec3 × ℝ)).restrict (B' ×ˢ J)
      = ((volume : Measure Vec3).restrict B').prod ((volume : Measure ℝ).restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hStendsto : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (B' ×ˢ J)), z ∈ S := by
    rw [hprodB']
    refine ae_prod_of_ae_ae_snd hSmeas ?_
    filter_upwards [hslice, hkey] with t hexists hall
    obtain ⟨g, hgloc, hgweak⟩ := hexists
    filter_upwards [hall g hgloc hgweak] with x hx
    exact ⟨g x, hx⟩
  have hDpAE : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (B' ×ˢ J)),
      Tendsto (fun n => G n z) atTop (𝓝 (Dp z)) := by
    filter_upwards [hStendsto] with z hz
    exact tendsto_nhds_limUnder hz
  have hid : ∀ᵐ t ∂(volume.restrict J), ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume → HasWeakPartialDerivOn B k (fun x => p (x, t)) g →
      (fun x => Dp (x, t)) =ᵐ[volume.restrict B'] g := by
    filter_upwards [hkey] with t hall g hgloc hgweak
    filter_upwards [hall g hgloc hgweak] with x hx
    exact hx.limUnder_eq
  have hiter : ∀ Ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ →
      tsupport Ψ ⊆ B' ×ˢ J →
      (∫ t in J, ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t)) =
        -∫ t in J, ∫ x in B', Dp (x, t) * Ψ (x, t) := by
    intro Ψ hΨ hΨc hΨs
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hslice, hid] with t hexists hidt
    obtain ⟨g, hgloc, hgweak⟩ := hexists
    obtain ⟨hψsmooth, hψcompact, hψsupport⟩ := slice_testFunction hΨ hΨc hΨs t
    have hψzero : ∀ x, x ∉ B' → Ψ (x, t) = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (f := fun y : Vec3 => Ψ (y, t))
        (fun h => hx (hψsupport h))
    have hDψzero : ∀ x, x ∉ B' → (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) = 0 := by
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hψsupport h))]
      simp
    have hLB' : ∫ x in B', p (x, t) * (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) ∂volume
        = ∫ x, p (x, t) * (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hDψzero x hx, mul_zero])
    have hLB : ∫ x in B, p (x, t) * (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) ∂volume
        = ∫ x, p (x, t) * (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hDψzero x (fun h => hx (hB'subB h)), mul_zero])
    have hRB : ∫ x in B, g x * Ψ (x, t) ∂volume = ∫ x, g x * Ψ (x, t) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hψzero x (fun h => hx (hB'subB h)), mul_zero])
    have hRB' : ∫ x in B', g x * Ψ (x, t) ∂volume = ∫ x, g x * Ψ (x, t) ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hψzero x hx, mul_zero])
    have hDpEq : ∫ x in B', Dp (x, t) * Ψ (x, t) ∂volume
        = ∫ x in B', g x * Ψ (x, t) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hidt g hgloc hgweak] with x hx
      rw [hx]
    have hweak := hgweak _ hψsmooth hψcompact (hψsupport.trans hB'subB)
    change ∫ x in B', p (x, t) * spatialPartial Ψ k (x, t) ∂volume
      = -∫ x in B', Dp (x, t) * Ψ (x, t) ∂volume
    rw [hDpEq, hRB', ← hRB]
    change ∫ x in B', p (x, t) * (fderiv ℝ (fun y : Vec3 => Ψ (y, t)) x) (basisVec k) ∂volume
      = -∫ x in B, g x * Ψ (x, t) ∂volume
    rw [hLB', ← hLB]
    exact hweak
  exact ⟨Dp, aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (hGmeas n).measurable.aemeasurable) hDpAE, hid, hiter,
    fun Ψ hΨ hΨc hΨs hF hH => setIntegral_prod_eq_of_iterated hF hH (hiter Ψ hΨ hΨc hΨs)⟩

end CKN

end
