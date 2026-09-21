/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedFiniteBasis
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.BudgetAbsorption

/-! # Probe Max -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open Section54.VarianceBoundGoodScale

/-!
# Normalized finite-probe maxima

The quenched minimal-scale theorem needs one random observable which controls
the localized response for every unit vector.  The finite-basis reduction
allows this observable to be a finite maximum over normalized coordinate and
pair probes.
-/

noncomputable section

inductive NormalizedProbeKind where
  | coord
  | plus
  | minus
  deriving DecidableEq

instance : Fintype NormalizedProbeKind where
  elems := {NormalizedProbeKind.coord, NormalizedProbeKind.plus, NormalizedProbeKind.minus}
  complete := by intro x; cases x <;> decide

@[simp]
theorem fintype_card_normalizedProbeKind :
    Fintype.card NormalizedProbeKind = 3 := by
  decide

/-- The finite probe index set used to eliminate the continuum of unit
vectors. -/
abbrev NormalizedProbeIndex (d : ℕ) := BlockCoord d × BlockCoord d × NormalizedProbeKind

/-- Coordinate probes are already normalized; plus/minus probes are divided by
two. -/
def normalizedProbeVec {d : ℕ} : NormalizedProbeIndex d → FullBlockVec d
  | (α, _β, .coord) => fullBlockCoordinateProbe α
  | (α, β, .plus) => (1 / 2 : ℝ) • fullBlockPlusProbe α β
  | (α, β, .minus) => (1 / 2 : ℝ) • fullBlockMinusProbe α β

private theorem dotProduct_smul_self
    {d : ℕ} (c : ℝ) (q : FullBlockVec d) :
    dotProduct (c • q) (c • q) = c ^ (2 : ℕ) * dotProduct q q := by
  rw [smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, pow_two, mul_assoc]

theorem normalizedProbeVec_dotProduct_self_le_one
    {d : ℕ} (i : NormalizedProbeIndex d) :
    dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 := by
  rcases i with ⟨α, β, kind⟩
  cases kind
  · simp [normalizedProbeVec, dotProduct_coordinateProbe_self]
  · calc
      dotProduct (normalizedProbeVec (α, β, NormalizedProbeKind.plus))
          (normalizedProbeVec (α, β, NormalizedProbeKind.plus))
          =
        (1 / 2 : ℝ) ^ (2 : ℕ) *
          dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) := by
          exact dotProduct_smul_self (1 / 2 : ℝ) (fullBlockPlusProbe α β)
      _ ≤ 1 := by
          nlinarith [dotProduct_plusProbe_self_le_four α β]
  · calc
      dotProduct (normalizedProbeVec (α, β, NormalizedProbeKind.minus))
          (normalizedProbeVec (α, β, NormalizedProbeKind.minus))
          =
        (1 / 2 : ℝ) ^ (2 : ℕ) *
          dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) := by
          exact dotProduct_smul_self (1 / 2 : ℝ) (fullBlockMinusProbe α β)
      _ ≤ 1 := by
          nlinarith [dotProduct_minusProbe_self_le_four α β]

theorem normalizedProbeVec_abs_apply_le_one
    {d : ℕ} (i : NormalizedProbeIndex d) (α : BlockCoord d) :
    |normalizedProbeVec i α| ≤ 1 := by
  exact
    abs_fullBlockVec_coord_le_one_of_dotProduct_le_one
      (normalizedProbeVec i) (normalizedProbeVec_dotProduct_self_le_one i) α

/-- Localized maximum over the normalized finite probe family. -/
noncomputable def localizedNormalizedProbeJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (m n : ℕ) : RegCoeffField d → ℝ :=
  fun a =>
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    have hS : S.Nonempty := by
      classical
      let α : BlockCoord d := Classical.choice inferInstance
      exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
    S.sup' hS (fun i =>
      localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a)

theorem localizedLimitNormalizedJNormalizedProbeSumMax_le_probeJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} (hnm : n ≤ m) (a : RegCoeffField d) :
    localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a ≤
      (Fintype.card (NormalizedProbeIndex d) : ℝ) *
        localizedNormalizedProbeJMax hP hStruct m n a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  have hprobe_eq :
      localizedNormalizedProbeJMax hP hStruct m n a =
        S.sup' hS (fun i =>
          localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a) := by
    rfl
  have hsum_le :
      ∀ R ∈ D,
        limitNormalizedJNormalizedProbeSum hP hStruct R a ≤
          (Fintype.card (NormalizedProbeIndex d) : ℝ) *
            localizedNormalizedProbeJMax hP hStruct m n a := by
    intro R hR
    rw [hprobe_eq]
    unfold limitNormalizedJNormalizedProbeSum
    let M : ℝ :=
      S.sup' hS (fun j =>
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a)
    have hterm :
        ∀ α β : BlockCoord d,
          limitNormalizedBlockJObservable hP hStruct R
              (fullBlockCoordinateProbe α) a +
            limitNormalizedBlockJObservable hP hStruct R
                ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a +
            limitNormalizedBlockJObservable hP hStruct R
                ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a ≤
          3 * M := by
      intro α β
      have hcoord :
          limitNormalizedBlockJObservable hP hStruct R
              (fullBlockCoordinateProbe α) a ≤ M := by
        exact
          (limitNormalizedBlockJObservable_le_localizedLimitNormalizedJMax
            hP hStruct (m := m) (n := n)
            (fullBlockCoordinateProbe α) hR a).trans
          (Finset.le_sup' (s := S)
            (f := fun j =>
              localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a)
            (show (α, β, NormalizedProbeKind.coord) ∈ S by simp [S]))
      have hplus :
          limitNormalizedBlockJObservable hP hStruct R
              ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a ≤ M := by
        exact
          (limitNormalizedBlockJObservable_le_localizedLimitNormalizedJMax
            hP hStruct (m := m) (n := n)
            ((1 / 2 : ℝ) • fullBlockPlusProbe α β) hR a).trans
          (Finset.le_sup' (s := S)
            (f := fun j =>
              localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a)
            (show (α, β, NormalizedProbeKind.plus) ∈ S by simp [S]))
      have hminus :
          limitNormalizedBlockJObservable hP hStruct R
              ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a ≤ M := by
        exact
          (limitNormalizedBlockJObservable_le_localizedLimitNormalizedJMax
            hP hStruct (m := m) (n := n)
            ((1 / 2 : ℝ) • fullBlockMinusProbe α β) hR a).trans
          (Finset.le_sup' (s := S)
            (f := fun j =>
              localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a)
            (show (α, β, NormalizedProbeKind.minus) ∈ S by simp [S]))
      linarith
    calc
      (∑ α : BlockCoord d, ∑ β : BlockCoord d,
        (limitNormalizedBlockJObservable hP hStruct R
            (fullBlockCoordinateProbe α) a +
          limitNormalizedBlockJObservable hP hStruct R
            ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a +
          limitNormalizedBlockJObservable hP hStruct R
            ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a))
          ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d, (3 * M) := by
            exact Finset.sum_le_sum fun α _ =>
              Finset.sum_le_sum fun β _ => hterm α β
      _ = (Fintype.card (NormalizedProbeIndex d) : ℝ) * M := by
            simp [NormalizedProbeIndex, Fintype.card_prod]
            ring_nf
  have hmax_eq :
      localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a =
        D.sup' hD (fun R => limitNormalizedJNormalizedProbeSum hP hStruct R a) := by
    dsimp [localizedLimitNormalizedJNormalizedProbeSumMax]
    simp [D, hD]
  rw [hmax_eq]
  exact Finset.sup'_le hD _ hsum_le

theorem localizedLimitNormalizedJMax_le_normalizedProbeJMax_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {m n : ℕ} (hnm : n ≤ m)
    (e : FullBlockVec d) (he : dotProduct e e ≤ 1) :
    (localizedLimitNormalizedJMax hP hStruct m n e) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a := by
  have hfinite :=
    localizedLimitNormalizedJMax_le_normalizedProbeSumMax_ae
      hP hStruct hΓ hnm e he
  filter_upwards [hfinite] with a hfinite_a
  have hsum :=
    localizedLimitNormalizedJNormalizedProbeSumMax_le_probeJMax
      hP hStruct hnm a
  calc
    localizedLimitNormalizedJMax hP hStruct m n e a
        ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
            localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a := hfinite_a
    _ ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          ((Fintype.card (NormalizedProbeIndex d) : ℝ) *
            localizedNormalizedProbeJMax hP hStruct m n a) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        (4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a := by
        ring

theorem localizedNormalizedProbeJMax_sub_const_le_sup_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} (c : ℝ) (a : RegCoeffField d) :
    let S : Finset (NormalizedProbeIndex d) := Finset.univ
    ∀ hS : S.Nonempty,
      localizedNormalizedProbeJMax hP hStruct m n a - c ≤
        S.sup' hS (fun i =>
          localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a - c) := by
  intro S hS
  dsimp [localizedNormalizedProbeJMax]
  have hle :
      S.sup' hS
          (fun i =>
            localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a) ≤
        c +
          S.sup' hS (fun i =>
            localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a - c) := by
    refine Finset.sup'_le hS _ ?_
    intro i hi
    have hi_le :
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a - c ≤
          S.sup' hS (fun j =>
            localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a - c) :=
      Finset.le_sup' (s := S)
        (f := fun j =>
          localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a - c)
        hi
    linarith
  linarith

private theorem normalizedProbeIndex_univ_card_two_le
    {d : ℕ} [NeZero d] :
    2 ≤ (Finset.univ : Finset (NormalizedProbeIndex d)).card := by
  classical
  let α : BlockCoord d := Classical.choice inferInstance
  let i₁ : NormalizedProbeIndex d := (α, α, NormalizedProbeKind.coord)
  let i₂ : NormalizedProbeIndex d := (α, α, NormalizedProbeKind.plus)
  have hne : i₁ ≠ i₂ := by
    simp [i₁, i₂]
  have hpair : ({i₁, i₂} : Finset (NormalizedProbeIndex d)).card = 2 :=
    Finset.card_pair hne
  have hle :
      ({i₁, i₂} : Finset (NormalizedProbeIndex d)).card ≤
        (Finset.univ : Finset (NormalizedProbeIndex d)).card :=
    Finset.card_le_card (by intro x hx; simp)
  omega

/-- Localized first-quenched estimate for the normalized finite-probe maximum.

This is the fixed-vector localized estimate, applied to the finite normalized
probe family and combined by the Chapter 4 finite-maximum rule. -/
theorem localizedFirstQuenchedEstimate_normalizedProbeJMax
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry α : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < α ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {ℓ n m : ℕ}, ℓ < n → n < m →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        IsBigOWith P (gammaSigma (min σ 2))
          (fun a =>
            localizedNormalizedProbeJMax hP hStruct (N0 + m) (N0 + n) a -
              Real.rpow (3 : ℝ) (-α * (ℓ : ℝ)))
          (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
            (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
              (Cfluct *
                (3 : ℝ) ^
                  (-(d : ℝ) / 2 *
                    (Int.toNat
                      ((((N0 + n : ℕ) : ℤ) -
                        ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                hΓ.thetaHat ^ (2 : ℕ)))) := by
  obtain ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, hloc⟩ :=
    localizedFirstQuenchedEstimate_limitNormalized (d := d) hσ_pos params
  refine ⟨Cfluct, Centry, α, hCfluct, hCentry, hα, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams ℓ n m hℓn hnm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α0 : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α0, α0, NormalizedProbeKind.coord), by simp [S]⟩
  have hτ_pos : 0 < min σ 2 :=
    lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hS_card : 2 ≤ S.card := by
    simpa [S] using normalizedProbeIndex_univ_card_two_le (d := d)
  let r : ℝ := Real.rpow (3 : ℝ) (-α * (ℓ : ℝ))
  let A : ℝ :=
    ((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
      (Cfluct *
        (3 : ℝ) ^
          (-(d : ℝ) / 2 *
            (Int.toNat
              ((((N0 + n : ℕ) : ℤ) -
                ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
        hΓ.thetaHat ^ (2 : ℕ))
  have htail :
      ∀ i ∈ S,
        IsBigOWith P (gammaSigma (min σ 2))
          (fun a =>
            localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
                (normalizedProbeVec i) a - r)
          A := by
    intro i _hi
    have hi_norm : dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 :=
      normalizedProbeVec_dotProduct_self_le_one i
    simpa [N0, D, r, A] using
      hloc hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i) hi_norm hℓn hnm
  have hsup :
      IsBigOWith P (gammaSigma (min σ 2))
        (fun a =>
          S.sup' hS (fun i =>
            localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
              (normalizedProbeVec i) a - r))
        (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) * A) := by
    exact Ch04.isBigOWith_gammaSigma_finset_sup'
      (μ := P) (s := S) (hs := hS)
      (X := fun i a =>
        localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
          (normalizedProbeVec i) a - r)
      (A := A) (σ := min σ 2) hτ_pos hS_card htail
  refine hsup.of_le ?_
  intro a
  simpa [N0, S, r] using
    localizedNormalizedProbeJMax_sub_const_le_sup_sub
      hP hStruct (m := N0 + m) (n := N0 + n) r a hS

/-- Uniform-in-`σ` version of
`localizedFirstQuenchedEstimate_normalizedProbeJMax`. -/
theorem localizedFirstQuenchedEstimate_normalizedProbeJMax_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ {ℓ n m : ℕ}, ℓ < n → n < m →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale P
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            let D : Finset (TriadicCube d) :=
              descendantsAtScale
                (originCube d (((N0 + m : ℕ) : ℤ)))
                (((N0 + n : ℕ) : ℤ))
            let S : Finset (NormalizedProbeIndex d) := Finset.univ
            IsBigOWith P (gammaSigma (min σ 2))
              (fun aω =>
                localizedNormalizedProbeJMax hP hStruct
                    (N0 + m) (N0 + n) aω -
                  Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)))
              (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) *
                (((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
                  (Cfluct *
                    (3 : ℝ) ^
                      (-(d : ℝ) / 2 *
                        (Int.toNat
                          ((((N0 + n : ℕ) : ℤ) -
                            ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
                    hΓ.thetaHat ^ (2 : ℕ)))) := by
  obtain ⟨Centry, a, hCentry, ha, hlocBase⟩ :=
    localizedFirstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
      (d := d) params
  refine ⟨Centry, a, hCentry, ha, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cfluct, hCfluct, hloc⟩ := hlocBase hσ_pos
  refine ⟨Cfluct, hCfluct, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams ℓ n m hℓn hnm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α0 : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α0, α0, NormalizedProbeKind.coord), by simp [S]⟩
  have hτ_pos : 0 < min σ 2 :=
    lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hS_card : 2 ≤ S.card := by
    simpa [S] using normalizedProbeIndex_univ_card_two_le (d := d)
  let r : ℝ := Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
  let A : ℝ :=
    ((3 * Real.log (D.card : ℝ)) ^ (min σ 2)⁻¹) *
      (Cfluct *
        (3 : ℝ) ^
          (-(d : ℝ) / 2 *
            (Int.toNat
              ((((N0 + n : ℕ) : ℤ) -
                ((N0 + ℓ : ℕ) : ℤ))) : ℝ)) *
        hΓ.thetaHat ^ (2 : ℕ))
  have htail :
      ∀ i ∈ S,
        IsBigOWith P (gammaSigma (min σ 2))
          (fun aω =>
            localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
                (normalizedProbeVec i) aω - r)
          A := by
    intro i _hi
    have hi_norm : dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 :=
      normalizedProbeVec_dotProduct_self_le_one i
    simpa [N0, D, r, A] using
      hloc hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i) hi_norm hℓn hnm
  have hsup :
      IsBigOWith P (gammaSigma (min σ 2))
        (fun aω =>
          S.sup' hS (fun i =>
            localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
              (normalizedProbeVec i) aω - r))
        (((3 * Real.log (S.card : ℝ)) ^ (min σ 2)⁻¹) * A) := by
    exact Ch04.isBigOWith_gammaSigma_finset_sup'
      (μ := P) (s := S) (hs := hS)
      (X := fun i aω =>
        localizedLimitNormalizedJMax hP hStruct (N0 + m) (N0 + n)
          (normalizedProbeVec i) aω - r)
      (A := A) (σ := min σ 2) hτ_pos hS_card htail
  refine hsup.of_le ?_
  intro aω
  simpa [N0, S, r] using
    localizedNormalizedProbeJMax_sub_const_le_sup_sub
      hP hStruct (m := N0 + m) (n := N0 + n) r aω hS

/-- Crude Γσ estimate for the localized normalized finite-probe maximum. -/
theorem isBigO_localizedNormalizedProbeJMax
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {m n : ℕ}, n < m →
        let D : Finset (TriadicCube d) :=
          descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        IsBigO P (gammaSigma σ)
          (localizedNormalizedProbeJMax hP hStruct m n)
          (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
            (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
              (C * hΓ.thetaHat ^ (2 : ℕ)))) := by
  obtain ⟨C, hC_pos, hloc⟩ :=
    isBigO_localizedLimitNormalizedJMax (d := d) hσ_pos params
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams m n hnm
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α0 : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α0, α0, NormalizedProbeKind.coord), by simp [S]⟩
  have hS_card : 2 ≤ S.card := by
    simpa [S] using normalizedProbeIndex_univ_card_two_le (d := d)
  have htail :
      ∀ i ∈ S,
        IsBigO P (gammaSigma σ)
          (localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i))
          (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
            (C * hΓ.thetaHat ^ (2 : ℕ))) := by
    intro i _hi
    have hi_norm : dotProduct (normalizedProbeVec i) (normalizedProbeVec i) ≤ 1 :=
      normalizedProbeVec_dotProduct_self_le_one i
    simpa [D] using
      hloc hP hStruct hΓ hσ_eq hparams
        (normalizedProbeVec i) hi_norm hnm
  have hsup :
      IsBigO P (gammaSigma σ)
        (fun a =>
          S.sup' hS (fun i =>
            localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a))
        (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
          S.sup' hS
            (fun _i =>
              ((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
                (C * hΓ.thetaHat ^ (2 : ℕ)))) := by
    exact Ch04.isBigO_gammaSigma_finset_sup'_of_scales
      (μ := P) (s := S) (hs := hS)
      (X := fun i a =>
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a)
      (a := fun _i =>
        ((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
          (C * hΓ.thetaHat ^ (2 : ℕ)))
      (σ := σ) hσ_pos hS_card htail
  have hscale :
      S.sup' hS
          (fun _i =>
            ((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
              (C * hΓ.thetaHat ^ (2 : ℕ))) =
        ((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
          (C * hΓ.thetaHat ^ (2 : ℕ)) := by
    simp
  have hsup' :
      IsBigO P (gammaSigma σ)
        (fun a =>
          S.sup' hS (fun i =>
            localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a))
        (((3 * Real.log (S.card : ℝ)) ^ σ⁻¹) *
          (((3 * Real.log (D.card : ℝ)) ^ σ⁻¹) *
            (C * hΓ.thetaHat ^ (2 : ℕ)))) := by
    simpa [hscale, mul_assoc] using hsup
  simpa [localizedNormalizedProbeJMax, S, hS, D] using! hsup'

end

end Section57
end Ch05
end Book
end Homogenization
