/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Resample
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator

/-!
# The per-core energy split and its pi-measurability

For the Efron–Stein transfer of the fixed-phase observable we must exhibit a
genuinely **product-measurable** observable on the tuple space
`(↥K → CoeffField d)` that agrees `Π`-almost-everywhere with `F_σ ∘ corePatch`.

The reconstruction map `corePatch` is *not* measurable into the ambient
σ-algebra (a raw local event over `cubeSet` can couple two coordinates through a
non-measurable set), so the coarse observable of the glued field cannot be
obtained by composing `corePatch` with a measurable coarse map.  The way out is
that the coarse observable only sees the glued field through *fixed-competitor*
block-energy integrals, and such an integral **splits across the core
partition**: on the corridor the truncated glued field is the identity
(a constant, independent of the tuple), and on each core `coreBox ℓ σ k` it reads
only the single coordinate `y k`.

This file builds that split.  The energy is measured against the **elliptically
truncated** glued field

`glueField ℓ σ Θ a := ellipticTruncate Θ (corridorField ℓ σ a)`,

which is `(1, Θ)`-elliptic *everywhere* (needed later for the uniform global
bound and the AEE slice) and is a *pointwise* self-map of coefficient fields.

Main definitions/results:
* `glueField`, its corridor value and pointwise congruence;
* `coreLocalEnergy W X` — the block-energy of the glued field over a bounded
  set `W`, shown **ambient-measurable** via the `PointwiseLocalSigma W` generator trick
  (this is the measurability heart, using only single-field local events);
* `phaseSplitEnergy` — the manifestly pi-measurable assembled observable
  (corridor constant `+` a finite sum of single-coordinate core energies);
* `measurable_phaseSplitEnergy`;
* `blockEnergyAverage_glueField_corePatch_eq_phaseSplitEnergy` — the exact split
  identity, valid whenever the glued field is `(1, Θ)`-elliptic on `U`
  (which holds `Π`-a.e. after truncation; supplied by the caller).
-/

@[expose] public section

open Homogenization
open scoped MeasureTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## The elliptically truncated glued field -/

/-- The truncated corridor field fed to the coarse observable: the corridor
field `corridorField ℓ σ a`, then clamped by `ellipticTruncate Θ` so that every
value is `(1, Θ)`-elliptic.  It is a *pointwise* self-map: its value at `x`
depends on `a` only through `a x`. -/
noncomputable def glueField (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (a : CoeffField d) : CoeffField d :=
  ellipticTruncate Θ (corridorField ℓ σ a)

/-- On the corridor the truncated glued field is the identity (the identity
matrix is `(1, Θ)`-elliptic for `Θ ≥ 1`). -/
theorem glueField_apply_of_mem_corridor {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {a : CoeffField d} {x : Vec d} (hx : x ∈ corridorSet ℓ σ) :
    glueField ℓ σ Θ a x = (1 : Mat d) := by
  have he : IsEllipticMatrix 1 Θ (corridorField ℓ σ a x) := by
    rw [corridorField_apply_of_mem hx]; exact isEllipticMatrix_one hΘ
  unfold glueField
  rw [ellipticTruncate_of_elliptic he, corridorField_apply_of_mem hx]

/-- Pointwise congruence: the value of the glued field at `x` depends only on
`a x`. -/
theorem glueField_congr_apply {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {a b : CoeffField d}
    {x : Vec d} (h : a x = b x) :
    glueField ℓ σ Θ a x = glueField ℓ σ Θ b x := by
  have hcorr : corridorField ℓ σ a x = corridorField ℓ σ b x := by
    by_cases hx : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hx, corridorField_apply_of_mem hx]
    · rw [corridorField_apply_of_not_mem hx, corridorField_apply_of_not_mem hx, h]
  unfold glueField
  by_cases he : IsEllipticMatrix 1 Θ (corridorField ℓ σ a x)
  · rw [ellipticTruncate_of_elliptic he,
      ellipticTruncate_of_elliptic (by rw [← hcorr]; exact he)]
    exact hcorr
  · rw [ellipticTruncate_of_not_elliptic he,
      ellipticTruncate_of_not_elliptic (by rw [← hcorr]; exact he)]

/-! ## The single-core block energy of the glued field -/

/-- The block energy of the truncated glued field of `a`, integrated over a set
`W`.  When `W = coreBox ℓ σ k ∩ U` this is the per-core contribution to the
coarse energy; it depends on `a` only through `a` on `W`. -/
noncomputable def coreLocalEnergy (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (W : Set (Vec d))
    (X : BlockState d) (a : CoeffField d) : ℝ :=
  ∫ x in W, blockEnergyDensity (glueField ℓ σ Θ a) X x ∂MeasureTheory.volume

/-- `coreLocalEnergy` depends on the field only through its values on `W`. -/
theorem coreLocalEnergy_congr {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {W : Set (Vec d)}
    (hW : MeasurableSet W) {X : BlockState d} {a b : CoeffField d}
    (hab : LocalAgreementOn W a b) :
    coreLocalEnergy ℓ σ Θ W X a = coreLocalEnergy ℓ σ Θ W X b := by
  unfold coreLocalEnergy
  refine MeasureTheory.setIntegral_congr_fun hW (fun x hx => ?_)
  have h1 : glueField ℓ σ Θ a x = glueField ℓ σ Θ b x := glueField_congr_apply (hab x hx)
  simp only [blockEnergyDensity, blockCoeffField, h1]

/-- **Measurability heart.**  `coreLocalEnergy` is ambient-measurable in the
field: it is a single-field bounded-local observable, hence measurable into
`PointwiseLocalSigma W` (via the generator trick) and thus into the ambient σ-algebra.
No cross-coordinate coupling is involved — this uses only single-field local
events. -/
theorem measurable_coreLocalEnergy {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {W : Set (Vec d)}
    (hWmeas : MeasurableSet W) (hWbdd : Bornology.IsBounded W) (X : BlockState d) :
    Measurable (fun a : CoeffField d => coreLocalEnergy ℓ σ Θ W X a) := by
  have hloc : @Measurable (CoeffField d) ℝ (PointwiseLocalSigma W) (borel ℝ)
      (fun a : CoeffField d => coreLocalEnergy ℓ σ Θ W X a) := by
    intro t _ht
    refine MeasurableSpace.measurableSet_generateFrom ?_
    intro a b hab
    have hEq : coreLocalEnergy ℓ σ Θ W X a = coreLocalEnergy ℓ σ Θ W X b :=
      coreLocalEnergy_congr hWmeas hab
    simp only [Set.mem_preimage, hEq]
  exact hloc.mono (localSigma_le_coeffField_of_isBounded hWbdd) le_rfl

/-! ## The corridor constant and the assembled pi-measurable observable -/

/-- The corridor contribution to the coarse energy: the block energy of the
identity field over `U ∩ corridorSet`.  Independent of the tuple. -/
noncomputable def corridorConst (ℓ : ℝ) (σ : Vec d) (U : Set (Vec d))
    (X : BlockState d) : ℝ :=
  ∫ x in U ∩ corridorSet ℓ σ, blockEnergyDensity (fun _ => (1 : Mat d)) X x
    ∂MeasureTheory.volume

/-- The assembled split observable on the tuple space: the corridor constant
plus a finite sum of single-coordinate core energies, normalized by `1 / vol U`.
It is manifestly product-measurable. -/
noncomputable def phaseSplitEnergy (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (U : Set (Vec d))
    (X : BlockState d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → CoeffField d) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ *
    (corridorConst ℓ σ U X
      + ∑ k : {k // k ∈ K}, coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k.1 ∩ U) X (y k))

/-- **Product-measurability of the assembled observable.**  Each core term is a
single-coordinate composition of the ambient-measurable `coreLocalEnergy`, so
the finite sum is measurable for the product σ-algebra `MeasurableSpace.pi`. -/
theorem measurable_phaseSplitEnergy {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {U : Set (Vec d)}
    (hUmeas : MeasurableSet U) (hUbdd : Bornology.IsBounded U) (X : BlockState d)
    (K : Finset (Fin d → ℤ)) :
    Measurable (fun y : {k // k ∈ K} → CoeffField d => phaseSplitEnergy ℓ σ Θ U X K y) := by
  unfold phaseSplitEnergy
  refine measurable_const.mul (measurable_const.add ?_)
  refine Finset.measurable_sum _ (fun k _ => ?_)
  have hWm : MeasurableSet (coreBox ℓ σ k.1 ∩ U) :=
    (measurableSet_coreBox ℓ σ k.1).inter hUmeas
  have hWb : Bornology.IsBounded (coreBox ℓ σ k.1 ∩ U) :=
    hUbdd.subset Set.inter_subset_right
  exact (measurable_coreLocalEnergy hWm hWb X).comp (measurable_pi_apply k)

/-! ## The exact split identity -/

/-- The complement of the corridor, intersected with `U`, is the disjoint union
of the core boxes meeting `U`. -/
theorem inter_compl_corridorSet_eq_iUnion_coreBox {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d)
    {U : Set (Vec d)} {K : Finset (Fin d → ℤ)}
    (hK : ∀ k : Fin d → ℤ, (coreBox ℓ σ k ∩ U).Nonempty → k ∈ K) :
    U \ corridorSet ℓ σ = ⋃ k : {k // k ∈ K}, (U ∩ coreBox ℓ σ k.1) := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨hxU, hxnc⟩
    have hxc : x ∈ (corridorSet ℓ σ)ᶜ := hxnc
    rw [compl_corridorSet_eq_iUnion_coreBox hℓ σ, Set.mem_iUnion] at hxc
    obtain ⟨k, hxk⟩ := hxc
    have hkK : k ∈ K := hK k ⟨x, hxk, hxU⟩
    exact ⟨⟨k, hkK⟩, hxU, hxk⟩
  · rintro ⟨k, hxU, hxk⟩
    refine ⟨hxU, ?_⟩
    have hxc : x ∈ (corridorSet ℓ σ)ᶜ := by
      rw [compl_corridorSet_eq_iUnion_coreBox hℓ σ, Set.mem_iUnion]
      exact ⟨k.1, hxk⟩
    exact hxc

/-- **Exact energy split.**  Whenever the truncated glued field of
`corePatch ℓ σ K y` is `(1, Θ)`-elliptic on `U` (so its coarse energy integral
converges), the block-energy average splits as the corridor constant plus the
per-core single-coordinate energies — i.e. it equals `phaseSplitEnergy`. -/
theorem blockEnergyAverage_glueField_corePatch_eq_phaseSplitEnergy
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {U : Set (Vec d)} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ)
    (hUmeas : MeasurableSet U) [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (X : BlockState d) (hXbl : MemBlockL2 U X.eval)
    (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ, (coreBox ℓ σ k ∩ U).Nonempty → k ∈ K)
    (y : {k // k ∈ K} → CoeffField d)
    (hEll : IsEllipticFieldOn 1 Θ U (glueField ℓ σ Θ (corePatch ℓ σ K y))) :
    blockEnergyAverage U (glueField ℓ σ Θ (corePatch ℓ σ K y)) X
      = phaseSplitEnergy ℓ σ Θ U X K y := by
  classical
  have hcorrM : MeasurableSet (corridorSet ℓ σ) := measurableSet_corridorSet ℓ σ
  -- integrability of the block-energy density
  have hfint : MeasureTheory.IntegrableOn
      (blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X) U := by
    have hpair := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (a := glueField ℓ σ Θ (corePatch ℓ σ K y)) hXbl hXbl hEll
    have hEq : blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X
        = fun x => (1 / 2 : ℝ) *
            blockPairingIntegrand (glueField ℓ σ Θ (corePatch ℓ σ K y)) X X x := by
      funext x; rfl
    rw [hEq]
    exact hpair.const_mul (1 / 2)
  -- split `∫_U = ∫_{U∩corr} + ∫_{U\corr}`
  have hsplit1 :
      ∫ x in U, blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
          ∂MeasureTheory.volume
        = (∫ x in U ∩ corridorSet ℓ σ,
              blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
                ∂MeasureTheory.volume)
          + ∫ x in U \ corridorSet ℓ σ,
              blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
                ∂MeasureTheory.volume :=
    (MeasureTheory.integral_inter_add_sdiff hcorrM hfint).symm
  -- corridor piece equals the corridor constant
  have hcorrEq :
      (∫ x in U ∩ corridorSet ℓ σ,
          blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
            ∂MeasureTheory.volume)
        = corridorConst ℓ σ U X := by
    refine MeasureTheory.setIntegral_congr_fun (hUmeas.inter hcorrM) (fun x hx => ?_)
    have hxc : x ∈ corridorSet ℓ σ := hx.2
    have hval : glueField ℓ σ Θ (corePatch ℓ σ K y) x = (1 : Mat d) :=
      glueField_apply_of_mem_corridor hΘ hxc
    simp only [blockEnergyDensity, blockCoeffField, hval]
  -- core pieces: rewrite `U \ corr` as the disjoint biUnion over the cores of `K`
  have hUdiff : U \ corridorSet ℓ σ = ⋃ k : {k // k ∈ K}, (U ∩ coreBox ℓ σ k.1) :=
    inter_compl_corridorSet_eq_iUnion_coreBox hℓ σ hK
  have hmeasW : ∀ k : {k // k ∈ K}, MeasurableSet (U ∩ coreBox ℓ σ k.1) :=
    fun k => hUmeas.inter (measurableSet_coreBox ℓ σ k.1)
  have hdisjW : Set.Pairwise (↑(Finset.univ : Finset {k // k ∈ K}))
      (Function.onFun Disjoint fun k : {k // k ∈ K} => U ∩ coreBox ℓ σ k.1) := by
    intro k _ k' _ hkk'
    have hne : k.1 ≠ k'.1 := fun h => hkk' (Subtype.ext h)
    exact (Disjoint.inter_left' _ (Disjoint.inter_right' _
      (disjoint_coreBox hℓ.le σ hne)))
  have hintW : ∀ k : {k // k ∈ K}, MeasureTheory.IntegrableOn
      (blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X) (U ∩ coreBox ℓ σ k.1) :=
    fun k => hfint.mono_set Set.inter_subset_left
  have hset : (⋃ k : {k // k ∈ K}, U ∩ coreBox ℓ σ k.1)
      = ⋃ k ∈ (Finset.univ : Finset {k // k ∈ K}), U ∩ coreBox ℓ σ k.1 := by
    simp only [Finset.mem_univ, Set.iUnion_true]
  have hbiUnion :
      (∫ x in U \ corridorSet ℓ σ,
          blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
            ∂MeasureTheory.volume)
        = ∑ k : {k // k ∈ K},
            ∫ x in U ∩ coreBox ℓ σ k.1,
              blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
                ∂MeasureTheory.volume := by
    rw [hUdiff, hset]
    exact MeasureTheory.integral_biUnion_finset (Finset.univ)
      (fun k _ => hmeasW k) hdisjW (fun k _ => hintW k)
  -- each core piece equals the single-coordinate core energy of `y k`
  have hcoreEq : ∀ k : {k // k ∈ K},
      (∫ x in U ∩ coreBox ℓ σ k.1,
          blockEnergyDensity (glueField ℓ σ Θ (corePatch ℓ σ K y)) X x
            ∂MeasureTheory.volume)
        = coreLocalEnergy ℓ σ Θ (coreBox ℓ σ k.1 ∩ U) X (y k) := by
    intro k
    have hWeq : U ∩ coreBox ℓ σ k.1 = coreBox ℓ σ k.1 ∩ U := Set.inter_comm _ _
    rw [hWeq]
    unfold coreLocalEnergy
    refine MeasureTheory.setIntegral_congr_fun
      ((measurableSet_coreBox ℓ σ k.1).inter hUmeas) (fun x hx => ?_)
    have hxk : x ∈ coreBox ℓ σ k.1 := hx.1
    have hval : corePatch ℓ σ K y x = y k x :=
      corePatch_apply_of_mem hℓ.le σ y k.2 hxk
    have h1 : glueField ℓ σ Θ (corePatch ℓ σ K y) x = glueField ℓ σ Θ (y k) x :=
      glueField_congr_apply hval
    simp only [blockEnergyDensity, blockCoeffField, h1]
  -- assemble
  unfold blockEnergyAverage volumeAverage phaseSplitEnergy
  rw [hsplit1, hcorrEq, hbiUnion]
  rw [Finset.sum_congr rfl (fun k _ => hcoreEq k)]

end Homogenization
