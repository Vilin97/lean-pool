/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CorePatchEnergy
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CubeMinimizer
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.AEEOperator.CanonicalCubeSet

/-!
# The product-measurable observable and its a.e. identity

Building on the per-core split of `CorePatchEnergy`, this file assembles the
genuinely product-measurable observable

`rawPhaseObservable … y := 2 · ⨅ n, phaseSplitEnergy … (compₙ) y`

where `compₙ = canonicalMuGeneratorAffineField P (denseSeq … n)` is the canonical
countable competitor family used by the Chapter-4 `Mu`-variational representation.
The `⨅` of the pi-measurable per-competitor split energies is pi-measurable, so
`rawPhaseObservable` is measurable for `MeasurableSpace.pi` — **without** any
measurability of `corePatch` itself.

The main result is the **five-link a.e. identity**: for `P`-a.e. field `a`,

`rawPhaseObservable … (fun k => a|_{coreBox k}) = F_σ(a)`,

i.e. the product observable, evaluated on the diagonal restriction tuple `R a`,
reproduces the fixed-phase observable exactly.  The chain is
1. `phaseSplitEnergy compₙ (R a) = blockEnergyAverage U (glued) compₙ`  (split, `CorePatchEnergy`),
2. `⨅ₙ blockEnergyAverage U (glued) compₙ = Mu U P glued`  (`mu_eq_iInf …`),
3. `Mu U P glued = ½ P·𝐀(U; glued) P`  (`mu_eq_half_coarseBlockMatrix_cube`, glued is `(1,Θ)`-elliptic),
4. `𝐀(U; glued) = 𝐀(U; corridorField (corePatch (R a)))`  (`coarseBlockMatrix_congr_of_ae_eq`, truncation a.e.),
5. `P·𝐀(U; corridorField (corePatch (R a))) P = F_σ(a)`  (landed `phaseObservable_corePatch_restrict_eq`).

The genuine spatial measurability of the underlying field — required for the
`IsEllipticFieldOn` hypotheses of links 1 and 3 — is exactly the measurability
conjunct of `ThetaEllipticLaw` (amended 2026-07-22).
-/

open Homogenization
open scoped MeasureTheory BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## The canonical competitor family and the raw product observable -/

/-- The `n`-th canonical `Mu`-generator competitor on the cube `cubeSet Q`, the
countable dense family used by `mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator`. -/
noncomputable def phaseCompetitor (Q : TriadicCube d) (P : BlockVec d) (n : ℕ) : BlockState d :=
  canonicalMuGeneratorAffineField (U := cubeSet Q) P
    (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n)

/-- The raw product-measurable observable: twice the infimum, over the canonical
competitor family, of the per-competitor split energies. -/
noncomputable def rawPhaseObservable (ℓ : ℝ) (σ : Vec d) (Θ : ℝ) (m : ℤ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → CoeffField d) : ℝ :=
  2 * ⨅ n : ℕ,
    phaseSplitEnergy ℓ σ Θ (cubeSet (originCube d m)) (phaseCompetitor (originCube d m) P n) K y

/-- The fixed-phase observable `F_σ(a) = P · 𝐀(U; corridorField ℓ σ a) P`. -/
noncomputable def phaseObservable (ℓ : ℝ) (σ : Vec d) (m : ℤ) (P : BlockVec d)
    (a : CoeffField d) : ℝ :=
  blockVecDot P
    (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a)) P)

/-! ## Product-measurability -/

/-- **Product-measurability of the raw observable.**  A countable infimum of the
pi-measurable per-competitor split energies (`measurable_phaseSplitEnergy`). -/
theorem measurable_rawPhaseObservable {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ}
    (P : BlockVec d) (K : Finset (Fin d → ℤ)) :
    Measurable
      (fun y : {k // k ∈ K} → CoeffField d => rawPhaseObservable ℓ σ Θ m P K y) := by
  unfold rawPhaseObservable
  refine measurable_const.mul (Measurable.iInf (fun n => ?_))
  exact measurable_phaseSplitEnergy (measurableSet_cubeSet _) (isBounded_cubeSet _)
    (phaseCompetitor (originCube d m) P n) K

/-! ## The five-link a.e. identity -/

/-- **The a.e. identity.**  For `P`-a.e. field `a` (measurable and a.e. `(1,Θ)`-
elliptic, from `ThetaEllipticLaw`), evaluating the product observable on the
diagonal restriction tuple reproduces the fixed-phase observable exactly. -/
theorem rawPhaseObservable_restrict_eq_of_field [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ)
    (P : BlockVec d) (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (b : CoeffField d)
    (hbmeas : ∀ i j : Fin d, Measurable fun x : Vec d => b x i j)
    (hbell : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)),
      IsEllipticMatrix 1 Θ (b x)) :
    rawPhaseObservable ℓ σ Θ m P K
        (fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) b)
      = phaseObservable ℓ σ m P b := by
  classical
  have hUmeas : MeasurableSet (cubeSet (originCube d m)) :=
    measurableSet_cubeSet (originCube d m)
  have hcorrM : MeasurableSet (corridorSet ℓ σ) := measurableSet_corridorSet ℓ σ
  have hcoreUnionM : MeasurableSet (coreUnion ℓ σ K) := by
    unfold coreUnion
    exact MeasurableSet.iUnion fun k =>
      MeasurableSet.iUnion fun _ => measurableSet_coreBox ℓ σ k
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet (originCube d m))) :=
    inferInstance
  set Ra : {k // k ∈ K} → CoeffField d :=
    fun k => restrictCoeffField (coreBox ℓ σ k.val) b with hRa
  -- the diagonal reconstruction is the identity-extension of `a` off the cores
  have hgfield :
      corridorField ℓ σ (corePatch ℓ σ K Ra)
        = corridorField ℓ σ (extendByIdCoeffField (coreUnion ℓ σ K) b) := by
    rw [hRa, corePatch_restrict_eq_extendById hℓ.le σ K b]
  -- entrywise spatial measurability of the corridor field of the reconstruction
  have hmeasField :
      Measurable (fun x : Vec d => fun i j =>
        if x ∈ cubeSet (originCube d m) then
          (corridorField ℓ σ (corePatch ℓ σ K Ra)) x i j else 0) := by
    rw [hgfield]
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have hrw :
        (fun x : Vec d =>
          if x ∈ cubeSet (originCube d m) then
            (corridorField ℓ σ (extendByIdCoeffField (coreUnion ℓ σ K) b)) x i j else 0)
          = fun x : Vec d =>
            if x ∈ cubeSet (originCube d m) then
              (if x ∈ corridorSet ℓ σ then (1 : Mat d) i j
                else if x ∈ coreUnion ℓ σ K then b x i j else (1 : Mat d) i j)
              else 0 := by
      funext x
      by_cases hxU : x ∈ cubeSet (originCube d m)
      · simp only [hxU, if_true]
        by_cases hxc : x ∈ corridorSet ℓ σ
        · rw [corridorField_apply_of_mem hxc]; simp [hxc]
        · rw [corridorField_apply_of_not_mem hxc]
          by_cases hxk : x ∈ coreUnion ℓ σ K
          · rw [extendByIdCoeffField_apply_of_mem hxk]; simp [hxc, hxk]
          · rw [extendByIdCoeffField_apply_of_not_mem hxk]; simp [hxc, hxk]
      · simp [hxU]
    rw [hrw]
    refine Measurable.ite hUmeas ?_ measurable_const
    refine Measurable.ite hcorrM measurable_const ?_
    exact Measurable.ite hcoreUnionM (hbmeas i j) measurable_const
  -- genuine ellipticity of the glued (truncated) field on the cube
  have hEllGlued :
      IsEllipticFieldOn 1 Θ (cubeSet (originCube d m))
        (glueField ℓ σ Θ (corePatch ℓ σ K Ra)) :=
    isEllipticFieldOn_ellipticTruncate hUmeas hΘ hmeasField
  -- truncation a.e. identity on the cube
  have haeCorr :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (cubeSet (originCube d m))),
        IsEllipticMatrix 1 Θ (corridorField ℓ σ (corePatch ℓ σ K Ra) x) := by
    rw [hgfield]
    filter_upwards [MeasureTheory.ae_restrict_of_ae hbell] with x hx
    by_cases hxc : x ∈ corridorSet ℓ σ
    · rw [corridorField_apply_of_mem hxc]; exact isEllipticMatrix_one hΘ
    · rw [corridorField_apply_of_not_mem hxc]
      by_cases hxk : x ∈ coreUnion ℓ σ K
      · rw [extendByIdCoeffField_apply_of_mem hxk]; exact hx
      · rw [extendByIdCoeffField_apply_of_not_mem hxk]; exact isEllipticMatrix_one hΘ
  have haeGlued :
      glueField ℓ σ Θ (corePatch ℓ σ K Ra)
        =ᵐ[MeasureTheory.volume.restrict (cubeSet (originCube d m))]
      corridorField ℓ σ (corePatch ℓ σ K Ra) :=
    ellipticTruncate_ae_eq haeCorr
  -- the AEE quantitative slice
  obtain ⟨kslice, hkslice⟩ :
      ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet (originCube d m)) k
        (glueField ℓ σ Θ (corePatch ℓ σ K Ra)) :=
    AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn (by norm_num)
      (IsAEEllipticFieldOn.of_isEllipticFieldOn hEllGlued)
  -- link 1: per-competitor split
  have hsplit : ∀ n : ℕ,
      phaseSplitEnergy ℓ σ Θ (cubeSet (originCube d m))
          (phaseCompetitor (originCube d m) P n) K Ra
        = blockEnergyAverage (cubeSet (originCube d m))
            (glueField ℓ σ Θ (corePatch ℓ σ K Ra)) (phaseCompetitor (originCube d m) P n) := by
    intro n
    exact (blockEnergyAverage_glueField_corePatch_eq_phaseSplitEnergy hℓ hΘ hUmeas
      (phaseCompetitor (originCube d m) P n)
      (canonicalMuGeneratorAffineField_memBlockL2 P _) K hK Ra hEllGlued).symm
  -- links 1–2: infimum equals `Mu`
  have hInf :
      (⨅ n : ℕ, phaseSplitEnergy ℓ σ Θ (cubeSet (originCube d m))
          (phaseCompetitor (originCube d m) P n) K Ra)
        = Mu (cubeSet (originCube d m)) P (glueField ℓ σ Θ (corePatch ℓ σ K Ra)) := by
    rw [iInf_congr hsplit]
    exact (mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator (originCube d m) kslice
      ⟨glueField ℓ σ Θ (corePatch ℓ σ K Ra), hkslice⟩ P).symm
  -- links 3–5: assemble
  rw [rawPhaseObservable, hInf, mu_eq_half_coarseBlockMatrix_cube hEllGlued P,
    coarseBlockMatrix_congr_of_ae_eq haeGlued]
  have hland := phaseObservable_corePatch_restrict_eq hℓ P hK b
  rw [phaseObservable]
  rw [show (fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) b) = Ra from rfl] at hland
  rw [hland]
  ring

/-- **The a.e. identity (law form).**  Corollary of `rawPhaseObservable_restrict_eq_of_field`
under `ThetaEllipticLaw`, whose measurability + a.e.-ellipticity conjuncts supply
the per-field hypotheses. -/
theorem rawPhaseObservable_restrict_ae_eq [NeZero d]
    {ℓ : ℝ} {σ : Vec d} {Θ : ℝ} {m : ℤ} (hℓ : 0 < ℓ) (hΘ : 1 ≤ Θ)
    (P : BlockVec d) {L : MeasureTheory.Measure (RegCoeffField d)}
    (hL : ThetaEllipticLaw Θ L) (K : Finset (Fin d → ℤ))
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K) :
    ∀ᵐ a ∂L,
      rawPhaseObservable ℓ σ Θ m P K
          (fun k : {k // k ∈ K} => restrictCoeffField (coreBox ℓ σ k.val) a.toFun)
        = phaseObservable ℓ σ m P a.toFun := by
  filter_upwards [hL] with a ha
  exact rawPhaseObservable_restrict_eq_of_field hℓ hΘ P K hK a.toFun
    (fun i j => a.entry_measurable i j) ha

end Homogenization
