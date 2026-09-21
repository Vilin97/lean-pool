/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ElementaryIto
import LeanPool.Malliavin.Malliavin.PredictableDensity

/-!
# Construction identities for the Brownian Itô integral

This file removes the common-partition restriction from the elementary Itô isometry.
`adaptedMono` promotes an adapted coefficient to a later sigma-algebra without changing its
ambient `L²` value. Splitting both the predictable process and its Brownian terminal value at
intermediate times reduces arbitrary overlapping intervals to the same-interval and disjoint
identities from `ElementaryIto.lean`. Consequently, arbitrary finite linear combinations have
matching Gram matrices on the predictable and terminal-value sides.

`naturalItoIntegral` then applies `LinearMap.extendOfNorm` along the dense elementary realization
map from `PredictableDensity.lean`. The resulting operator is a centered linear isometry on all
predictable `L²`, agrees with `Z (B_b - B_a)` on every elementary adapted process, and is packaged
as both `naturalItoIntegralIsometry` and `centeredNaturalItoIntegralIsometry`. Thus the Brownian
Itô integration side no longer needs to be stipulated by `ClarkOconeFamily`; the remaining family
contract concerns martingale representation and Malliavin--Itô duality.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Promote an adapted coefficient to a later sigma-algebra of the filtration. -/
noncomputable def adaptedMono
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a c : ℝ≥0} (hac : a ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : lpMeas ℝ ℝ (𝓕 c) 2 P :=
  ⟨Z.1, AEStronglyMeasurable.mono (𝓕.mono hac) (lpMeas.aestronglyMeasurable Z)⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The promoted coefficient has the same ambient `L²` value. -/
theorem adaptedMono_coe
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a c : ℝ≥0} (hac : a ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (adaptedMono 𝓕 hac Z : RandomL2 P) = (Z : RandomL2 P) :=
  rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- An elementary Brownian value splits at an intermediate time. -/
theorem elementaryBrownianValue_split
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryBrownianValue hB hsm hnat (hac.trans hcb) Z =
      elementaryBrownianValue hB hsm hnat hac Z +
        elementaryBrownianValue hB hsm hnat hcb (adaptedMono 𝓕 hac Z) := by
  apply Lp.ext
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat (hac.trans hcb) Z,
    coeFn_elementaryBrownianValue hB hsm hnat hac Z,
    coeFn_elementaryBrownianValue hB hsm hnat hcb (adaptedMono 𝓕 hac Z),
    Lp.coeFn_add (elementaryBrownianValue hB hsm hnat hac Z)
      (elementaryBrownianValue hB hsm hnat hcb (adaptedMono 𝓕 hac Z))]
    with w habw hacw hcbw hadd
  rw [habw, hadd, Pi.add_apply, hacw, hcbw]
  change (Z : W → ℝ) w * (B b w - B a w) =
    (Z : W → ℝ) w * (B c w - B a w) +
      (Z : W → ℝ) w * (B b w - B c w)
  ring

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- An elementary predictable process splits at an intermediate time. -/
theorem elementaryPredictable_split
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    {a c b : ℝ≥0} (hac : a ≤ c) (hcb : c ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictable 𝓕 a b Z =
      elementaryPredictable 𝓕 a c Z +
        elementaryPredictable 𝓕 c b (adaptedMono 𝓕 hac Z) := by
  apply Subtype.ext
  change (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P) =
    (elementaryPredictable 𝓕 a c Z : TimeProcessL2 P) +
      (elementaryPredictable 𝓕 c b (adaptedMono 𝓕 hac Z) : TimeProcessL2 P)
  apply Lp.ext
  filter_upwards [elementaryPredictable_coeFn 𝓕 a b Z,
    elementaryPredictable_coeFn 𝓕 a c Z,
    elementaryPredictable_coeFn 𝓕 c b (adaptedMono 𝓕 hac Z),
    Lp.coeFn_add (elementaryPredictable 𝓕 a c Z : TimeProcessL2 P)
      (elementaryPredictable 𝓕 c b (adaptedMono 𝓕 hac Z) : TimeProcessL2 P)]
    with p habp hacp hcbp hadd
  rw [habp, hadd, Pi.add_apply, hacp, hcbp]
  change (if p.1 ∈ Set.Ioc a b then (Z : W → ℝ) p.2 else 0) =
    (if p.1 ∈ Set.Ioc a c then (Z : W → ℝ) p.2 else 0) +
      if p.1 ∈ Set.Ioc c b then (Z : W → ℝ) p.2 else 0
  by_cases hpac : p.1 ∈ Set.Ioc a c
  · have hpab : p.1 ∈ Set.Ioc a b := ⟨hpac.1, hpac.2.trans hcb⟩
    have hpcb : p.1 ∉ Set.Ioc c b := fun hp ↦ (not_lt_of_ge hpac.2) hp.1
    simp only [hpab, ↓reduceIte, hpac, hpcb, add_zero]
  · by_cases hpcb : p.1 ∈ Set.Ioc c b
    · have hpab : p.1 ∈ Set.Ioc a b := ⟨lt_of_le_of_lt hac hpcb.1, hpcb.2⟩
      simp only [hpab, ↓reduceIte, hpac, hpcb, zero_add]
    · have hpab : p.1 ∉ Set.Ioc a b := by
        intro hp
        rcases lt_or_ge c p.1 with hcp | hpc
        · exact hpcb ⟨hcp, hp.2⟩
        · exact hpac ⟨hp.1, hpc⟩
      simp only [hpab, ↓reduceIte, hpac, hpcb, add_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- Arbitrary elementary Brownian values have the same cross inner product as their predictable
integrands, with no alignment or disjointness hypothesis on the two time intervals. -/
theorem inner_elementaryBrownianValue_eq_inner_elementaryPredictable
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hcd Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 c d Y) := by
  have hordered : ∀ {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
      (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P), a ≤ c →
      inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
          (elementaryBrownianValue hB hsm hnat hcd Y) =
        inner ℝ (elementaryPredictable 𝓕 a b Z)
          (elementaryPredictable 𝓕 c d Y) := by
    intro a b c d hab hcd Z Y hac
    by_cases hbc : b ≤ c
    · exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
        hB hsm hnat hab hbc hcd Z Y
    · have hcb : c ≤ b := le_of_lt (lt_of_not_ge hbc)
      let Zc : lpMeas ℝ ℝ (𝓕 c) 2 P := adaptedMono 𝓕 hac Z
      rw [elementaryBrownianValue_split hB hsm hnat hac hcb Z,
        elementaryPredictable_split 𝓕 hac hcb Z]
      by_cases hbd : b ≤ d
      · let Yb : lpMeas ℝ ℝ (𝓕 b) 2 P := adaptedMono 𝓕 hcb Y
        rw [elementaryBrownianValue_split hB hsm hnat hcb hbd Y,
          elementaryPredictable_split 𝓕 hcb hbd Y]
        simp only [inner_add_left, inner_add_right]
        rw [inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
              hB hsm hnat hac le_rfl hcb Z Y,
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
              hB hsm hnat hac hcb hbd Z Yb,
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
              hB hsm hnat hcb Zc Y,
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
              hB hsm hnat hcb le_rfl hbd Zc Yb]
      · have hdb : d ≤ b := le_of_lt (lt_of_not_ge hbd)
        let Zd : lpMeas ℝ ℝ (𝓕 d) 2 P := adaptedMono 𝓕 hcd Zc
        have hreverse :
            inner ℝ (elementaryBrownianValue hB hsm hnat hdb Zd)
                (elementaryBrownianValue hB hsm hnat hcd Y) =
              inner ℝ (elementaryPredictable 𝓕 d b Zd)
                (elementaryPredictable 𝓕 c d Y) := by
          calc
            inner ℝ (elementaryBrownianValue hB hsm hnat hdb Zd)
                (elementaryBrownianValue hB hsm hnat hcd Y) =
                inner ℝ (elementaryBrownianValue hB hsm hnat hcd Y)
                  (elementaryBrownianValue hB hsm hnat hdb Zd) := real_inner_comm _ _
            _ = inner ℝ (elementaryPredictable 𝓕 c d Y)
                  (elementaryPredictable 𝓕 d b Zd) :=
              inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
                hB hsm hnat hcd le_rfl hdb Y Zd
            _ = inner ℝ (elementaryPredictable 𝓕 d b Zd)
                  (elementaryPredictable 𝓕 c d Y) := real_inner_comm _ _
        rw [elementaryBrownianValue_split hB hsm hnat hcd hdb Zc,
          elementaryPredictable_split 𝓕 hcd hdb Zc]
        simp only [inner_add_left]
        rw [inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
              hB hsm hnat hac le_rfl hcd Z Y,
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
              hB hsm hnat hcd Zc Y,
          hreverse]
  rcases le_total a c with hac | hca
  · exact hordered hab hcd Z Y hac
  · calc
      inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
          (elementaryBrownianValue hB hsm hnat hcd Y) =
          inner ℝ (elementaryBrownianValue hB hsm hnat hcd Y)
            (elementaryBrownianValue hB hsm hnat hab Z) := real_inner_comm _ _
      _ = inner ℝ (elementaryPredictable 𝓕 c d Y)
            (elementaryPredictable 𝓕 a b Z) := hordered hcd hab Y Z hca
      _ = inner ℝ (elementaryPredictable 𝓕 a b Z)
            (elementaryPredictable 𝓕 c d Y) := real_inner_comm _ _

/-- A family's elementary Brownian values satisfy the arbitrary-interval cross Itô identity. -/
theorem ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z)
        (elementaryPredictable 𝓕 c d Y) := by
  rw [C.elementaryIntegralValue_eq_elementaryBrownianValue,
    C.elementaryIntegralValue_eq_elementaryBrownianValue]
  exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable
    C.isPreBrownian C.stronglyMeasurable C.naturalFiltration hab hcd Z Y

/-! ## Extension from the dense elementary span -/

/-- Formal generators `1_(a,b] Z`, including their interval-order proof. -/
abbrev ElementaryPredictableIndex
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  Σ a : ℝ≥0, {b : ℝ≥0 // a ≤ b} × lpMeas ℝ ℝ (𝓕 a) 2 P

/-- The predictable-process realization of one formal elementary generator. -/
noncomputable def elementaryPredictableGenerator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :
    ElementaryPredictableIndex 𝓕 P → PredictableProcessL2 𝓕 P :=
  fun x ↦ elementaryPredictable 𝓕 x.1 x.2.1.1 x.2.2

/-- The Brownian terminal-value realization of one formal elementary generator. -/
noncomputable def elementaryBrownianGenerator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    ElementaryPredictableIndex 𝓕 P → RandomL2 P :=
  fun x ↦ elementaryBrownianValue hB hsm hnat x.2.1.2 x.2.2

/-- Formal finite combinations realized as predictable processes. -/
noncomputable def elementaryFinsuppToPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :
    (ElementaryPredictableIndex 𝓕 P →₀ ℝ) →ₗ[ℝ] PredictableProcessL2 𝓕 P :=
  Finsupp.linearCombination ℝ (elementaryPredictableGenerator 𝓕 P)

/-- Formal finite combinations realized as Brownian terminal values. -/
noncomputable def elementaryFinsuppToBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    (ElementaryPredictableIndex 𝓕 P →₀ ℝ) →ₗ[ℝ] RandomL2 P :=
  Finsupp.linearCombination ℝ (elementaryBrownianGenerator hB hsm hnat)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- The predictable realization of a single formal generator. -/
theorem elementaryFinsuppToPredictable_single
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToPredictable 𝓕 P (Finsupp.single x c) =
      c • elementaryPredictableGenerator 𝓕 P x :=
  Finsupp.linearCombination_single _ _ _

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The Brownian realization of a single formal generator. -/
theorem elementaryFinsuppToBrownian_single
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToBrownian hB hsm hnat (Finsupp.single x c) =
      c • elementaryBrownianGenerator hB hsm hnat x :=
  Finsupp.linearCombination_single _ _ _

omit [CompleteSpace W] [BorelSpace W] in
/-- The arbitrary-pair cross identity, packaged for formal generators. -/
theorem inner_elementaryBrownianGenerator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (x y : ElementaryPredictableIndex 𝓕 P) :
    inner ℝ (elementaryBrownianGenerator hB hsm hnat x)
        (elementaryBrownianGenerator hB hsm hnat y) =
      inner ℝ (elementaryPredictableGenerator 𝓕 P x)
        (elementaryPredictableGenerator 𝓕 P y) :=
  inner_elementaryBrownianValue_eq_inner_elementaryPredictable
    hB hsm hnat x.2.1.2 y.2.1.2 x.2.2 y.2.2

omit [CompleteSpace W] [BorelSpace W] in
/-- Formal finite elementary combinations have matching Gram matrices. -/
theorem inner_elementaryFinsuppToBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (v w : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    inner ℝ (elementaryFinsuppToBrownian hB hsm hnat v)
        (elementaryFinsuppToBrownian hB hsm hnat w) =
      inner ℝ (elementaryFinsuppToPredictable 𝓕 P v)
        (elementaryFinsuppToPredictable 𝓕 P w) := by
  unfold elementaryFinsuppToBrownian elementaryFinsuppToPredictable
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  rw [inner_elementaryBrownianGenerator hB hsm hnat y x]

omit [CompleteSpace W] [BorelSpace W] in
/-- Formal finite elementary combinations have matching norms. -/
theorem norm_elementaryFinsuppToBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    ‖elementaryFinsuppToBrownian hB hsm hnat v‖ =
      ‖elementaryFinsuppToPredictable 𝓕 P v‖ := by
  have h := inner_elementaryFinsuppToBrownian hB hsm hnat v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [CompleteSpace W] [BorelSpace W] in
/-- Formal elementary combinations have dense range in predictable `L²`. -/
theorem denseRange_elementaryFinsuppToPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    DenseRange (elementaryFinsuppToPredictable 𝓕 P) := by
  change Dense (Set.range (elementaryFinsuppToPredictable 𝓕 P))
  rw [← LinearMap.coe_range, elementaryFinsuppToPredictable,
    Finsupp.range_linearCombination]
  have hrange : Set.range (elementaryPredictableGenerator 𝓕 P) =
      {U | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
        ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P,
          U = elementaryPredictable 𝓕 a b Z} := by
    ext U
    constructor
    · rintro ⟨⟨a, ⟨b, hab⟩, Z⟩, rfl⟩
      exact ⟨a, b, hab, Z, rfl⟩
    · rintro ⟨a, b, hab, Z, rfl⟩
      exact ⟨⟨a, ⟨⟨b, hab⟩, Z⟩⟩, rfl⟩
  rw [hrange]
  simpa only [elementaryPredictableSpan] using
    (dense_elementaryPredictableSpan (P := P) 𝓕)

/-- The natural-filtration Itô integral, obtained by norm-controlled extension from formal
elementary combinations. -/
noncomputable def naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PredictableProcessL2 𝓕 P →L[ℝ] RandomL2 P :=
  (elementaryFinsuppToBrownian hB hsm hnat).extendOfNorm
    (elementaryFinsuppToPredictable 𝓕 P)

omit [CompleteSpace W] [BorelSpace W] in
/-- The extended Itô integral agrees with the Brownian map on every formal finite
combination. -/
theorem naturalItoIntegral_elementaryFinsuppToPredictable
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    naturalItoIntegral hB hsm hnat (elementaryFinsuppToPredictable 𝓕 P v) =
      elementaryFinsuppToBrownian hB hsm hnat v :=
  LinearMap.extendOfNorm_eq
    (denseRange_elementaryFinsuppToPredictable (P := P) 𝓕)
    ⟨1, fun v ↦ by rw [norm_elementaryFinsuppToBrownian hB hsm hnat, one_mul]⟩ v

omit [CompleteSpace W] [BorelSpace W] in
/-- On an elementary adapted process, the constructed integral is `Z (B_b - B_a)`. -/
theorem naturalItoIntegral_elementaryPredictable
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    naturalItoIntegral hB hsm hnat (elementaryPredictable 𝓕 a b Z) =
      elementaryBrownianValue hB hsm hnat hab Z := by
  let x : ElementaryPredictableIndex 𝓕 P := ⟨a, ⟨⟨b, hab⟩, Z⟩⟩
  have h := naturalItoIntegral_elementaryFinsuppToPredictable
    hB hsm hnat (Finsupp.single x 1)
  simpa only [elementaryFinsuppToPredictable_single,
    elementaryFinsuppToBrownian_single, one_smul, elementaryPredictableGenerator,
    elementaryBrownianGenerator] using h

omit [CompleteSpace W] [BorelSpace W] in
/-- The constructed natural-filtration Itô integral preserves inner products. -/
theorem inner_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U V : PredictableProcessL2 𝓕 P) :
    inner ℝ (naturalItoIntegral hB hsm hnat U)
        (naturalItoIntegral hB hsm hnat V) = inner ℝ U V := by
  refine (denseRange_elementaryFinsuppToPredictable (P := P) 𝓕).induction_on₂
    (p := fun U V ↦ inner ℝ (naturalItoIntegral hB hsm hnat U)
      (naturalItoIntegral hB hsm hnat V) = inner ℝ U V) ?_ ?_ U V
  · exact isClosed_eq
      (((naturalItoIntegral hB hsm hnat).continuous.comp continuous_fst).inner
        ((naturalItoIntegral hB hsm hnat).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro v w
    rw [naturalItoIntegral_elementaryFinsuppToPredictable hB hsm hnat,
      naturalItoIntegral_elementaryFinsuppToPredictable hB hsm hnat,
      inner_elementaryFinsuppToBrownian hB hsm hnat]

omit [CompleteSpace W] [BorelSpace W] in
/-- The constructed natural-filtration Itô integral is norm preserving. -/
theorem norm_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) :
    ‖naturalItoIntegral hB hsm hnat U‖ = ‖U‖ := by
  have h := inner_naturalItoIntegral hB hsm hnat U U
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The constructed natural-filtration Itô integral as a linear isometry. -/
noncomputable def naturalItoIntegralIsometry
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] RandomL2 P :=
  ⟨(naturalItoIntegral hB hsm hnat).toLinearMap,
    norm_naturalItoIntegral hB hsm hnat⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Every elementary Brownian terminal value is centered. -/
theorem integral_elementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ∫ w, elementaryBrownianValue hB hsm hnat hab Z w ∂P = 0 := by
  rw [integral_congr_ae (coeFn_elementaryBrownianValue hB hsm hnat hab Z)]
  have hZ : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hΔ : AEStronglyMeasurable (fun w ↦ B b w - B a w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  change ∫ w, ((Z : W → ℝ) * fun w ↦ B b w - B a w) w ∂P = 0
  rw [(indep_increment_of_natural_adapted hB hsm hnat hab
    (lpMeas.aestronglyMeasurable Z)).symm.integral_mul_eq_mul_integral hZ hΔ]
  change (∫ w, (Z : W → ℝ) w ∂P) * (∫ w, B b w - B a w ∂P) = 0
  rw [integral_sub (hB.integrable_eval b) (hB.integrable_eval a),
    hB.integral_eval, hB.integral_eval, sub_zero, mul_zero]

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- Every formal finite combination of elementary Brownian values is centered. -/
theorem expectationMap_elementaryFinsuppToBrownian
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (v : ElementaryPredictableIndex 𝓕 P →₀ ℝ) :
    CameronMartin.expectationMap P (elementaryFinsuppToBrownian hB hsm hnat v) = 0 := by
  rw [elementaryFinsuppToBrownian, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [map_smul, elementaryBrownianGenerator, CameronMartin.expectationMap_apply,
    integral_elementaryBrownianValue, smul_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- The constructed natural-filtration Itô integral is centered on every predictable process. -/
theorem integral_naturalItoIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (U : PredictableProcessL2 𝓕 P) :
    ∫ w, naturalItoIntegral hB hsm hnat U w ∂P = 0 := by
  rw [← CameronMartin.expectationMap_apply]
  let L := (CameronMartin.expectationMap P).comp (naturalItoIntegral hB hsm hnat)
  change L U = 0
  refine (denseRange_elementaryFinsuppToPredictable (P := P) 𝓕).induction_on U
    (isClosed_eq L.continuous continuous_const) ?_
  intro v
  change CameronMartin.expectationMap P
    (naturalItoIntegral hB hsm hnat (elementaryFinsuppToPredictable 𝓕 P v)) = 0
  rw [naturalItoIntegral_elementaryFinsuppToPredictable]
  exact expectationMap_elementaryFinsuppToBrownian hB hsm hnat v

/-- The constructed natural-filtration Itô integral with codomain restricted to centered random
variables. -/
noncomputable def centeredNaturalItoIntegralIsometry
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker where
  toLinearMap := (naturalItoIntegralIsometry hB hsm hnat).toLinearMap.codRestrict
    (CameronMartin.expectationMap P).ker fun U => by
      rw [LinearMap.mem_ker]
      change CameronMartin.expectationMap P (naturalItoIntegral hB hsm hnat U) = 0
      rw [CameronMartin.expectationMap_apply]
      exact integral_naturalItoIntegral hB hsm hnat U
  norm_map' := norm_naturalItoIntegral hB hsm hnat

omit [CompleteSpace W] [BorelSpace W] in
/-- The centered isometry has the same ambient value as `naturalItoIntegral`. -/
@[simp]
theorem centeredNaturalItoIntegralIsometry_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (U : PredictableProcessL2 𝓕 P) :
    (centeredNaturalItoIntegralIsometry hB hsm hnat U : RandomL2 P) =
      naturalItoIntegral hB hsm hnat U :=
  rfl

-- Compiles at default 200k heartbeats (override removed).
/-- Any abstract family compatible with elementary Brownian integration uses exactly the
constructed natural-filtration Itô integral. -/
theorem ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq_naturalItoIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) :
    C.itoIntegral =
      naturalItoIntegral C.isPreBrownian C.stronglyMeasurable C.naturalFiltration := by
  apply ContinuousLinearMap.ext_on
    (s := {U | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
      ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P, U = elementaryPredictable 𝓕 a b Z})
  · simpa only [elementaryPredictableSpan] using
      (dense_elementaryPredictableSpan (P := P) 𝓕)
  · rintro U ⟨a, b, hab, Z, rfl⟩
    rw [hC hab Z,
      naturalItoIntegral_elementaryPredictable C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration]
    exact C.elementaryIntegralValue_eq_elementaryBrownianValue hab Z

/-- Build a full `ClarkOconeFamily` using the constructed Itô integral. The only remaining
analytic inputs are martingale representation and Malliavin--Itô duality. -/
noncomputable def ClarkOconeFamily.ofNaturalIto
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (hMRT : ∀ G : RandomL2 P, ∃ u,
      G = expectationL2 G + naturalItoIntegral hB hsm hnat u)
    (hDuality : ∀ (F : D12 P) u,
      inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat u) =
        inner ℝ (predictableProjection 𝓕
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) u) :
    ClarkOconeFamily B P 𝓕 where
  isPreBrownian := hB
  coordinate := coordinate
  coordinate_apply := coordinate_apply
  generated := generated
  stronglyMeasurable := hsm
  naturalFiltration := hnat
  itoIntegral := naturalItoIntegral hB hsm hnat
  norm_itoIntegral := norm_naturalItoIntegral hB hsm hnat
  integral_itoIntegral := integral_naturalItoIntegral hB hsm hnat
  martingaleRepresentation := hMRT
  malliavinItoDuality := hDuality

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
