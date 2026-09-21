/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetChart
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.UniformDomain

/-!
# The nonuniform chart over a general base: `𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²)` and failure of
stable uniformity

The K8 "chart" slice of the CDVF campaign (crosswalk D9): `FiniteJetChart.lean` rebuilt
over an arbitrary base `[NontriviallyNormedField K] [IsUltrametricDist K]
[CompleteSpace K]` with an explicit uniformizer `ϖ : Uniformizer K` (the K1 layer-1 API
of `CDVFBase.lean`) replacing the Laurent pseudouniformizer `LaurentSeriesExample.t`.

Source: [FJP] §3. Proposition 3.1 (verbatim): "There is a canonical isomorphism of
topological k-algebras `𝒜_in ≅ k⟨X,Q⟩/(Q²)`, `W ↦ ϖX`, `Q ↦ Q`." — where
`𝒜_in = 𝒜⟨W/ϖ⟩ = (𝒜⟨X⟩/(ϖX − W))^∧` is the completed rational localization at the datum
`(W; ϖ)`, presented by `T = {W, ϖ}`, `s = ϖ`. In our models the target ring is literally
`𝓑 = DualNumber (K⟨X⟩)`.

Key computation ((3.3)): for `y ∈ Q²𝒞` and every `n`, `y = ϖⁿXⁿ(W^{-n}y)` with
`‖W^{-n}y‖ = ‖y‖`, so `Q²𝒞` dies in the separated completion.

Corollary 3.2 (verbatim): "The ring 𝒜 is not stably uniform." — the chart is nonzero and
nonuniform: "`Q ≠ 0`, `Q² = 0`, and every element of the unbounded line `kQ` is
power-bounded, while `‖λQ‖ = |λ|`."

Everything here needs only `0 < ‖ϖ.val‖ < 1` plus exact `ϖ`-scaling — no discreteness of
the value group anywhere (K8b's finding propagates). The generic-over-the-coefficient-ring
pieces of the Laurent template (`FiniteJet.rescaleRestricted`,
`FiniteJet.norm_rescaleRestricted_le`, `FiniteJet.unitFinOne`,
`FiniteJet.isPowerBounded_map_of_ringEquiv`, `FiniteJet.isUniform_of_ringEquiv`,
`FiniteJet.isPowerBounded_of_norm_le_one`, `FiniteJet.unitBallPod`) are reused, not
re-proved.
-/

open Filter Topology

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open ValuationSpectrum

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

open scoped Classical Pointwise

/-! ### The chart datum `(W; ϖ)` -/

/-- The element `W ∈ 𝓐` (support `(1,0)`; [FJP] §1.4), over a general base. -/
def Wa : JetA K :=
  ⟨sectionD K (TrivSqZeroExt.inl (Wu (R := K)).val), by
    rw [mem_jetSupport_iff_jet_in_range, rhoC_sectionD]
    have hsupp : (Wu (R := K)).val ∈ nonnegSubring K := by
      intro a ha
      show (single (1 : ℤ) (1 : K) : RestrictedLaurent K).coeff a = 0
      rw [coeff_single]
      exact if_neg (by omega)
    refine ⟨TrivSqZeroExt.inl ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩) =
        (Wu (R := K)).val
      rw [ofRestricted_nonnegEquiv_symm]
    · show ofRestricted (R := K) 0 = 0
      exact map_zero _⟩

/-- The unit-ball pair of definition of `𝓐` at a base-field uniformizer (the generic
`FiniteJet.unitBallPod` at `piA ϖ`; ϖ-parametric analogue of the frozen
`FiniteJet.podA`). -/
def podA (ϖ : Uniformizer K) : PairOfDefinition (JetA K) :=
  unitBallPod (piA ϖ) (isUnit_piA ϖ) (norm_piA_lt_one ϖ) (norm_piA_pos ϖ) (norm_piA_mul ϖ)

/-- The chart datum `(W; ϖ)`: `T = {W, ϖ}`, `s = ϖ` — presenting the rational subset
`{|W| ≤ |ϖ| ≠ 0}` of `Spa(𝓐, 𝓐°)` ([FJP] (3.1)), over a general base. -/
def chartDatum (ϖ : Uniformizer K) : RationalLocData (JetA K) where
  P := podA K ϖ
  T := {Wa K, piA ϖ}
  s := piA ϖ
  hopen := genPiece_hopen (podA K ϖ) {Wa K, piA ϖ} (piA ϖ)
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_piA ϖ))

theorem chartDatum_isRational (ϖ : Uniformizer K) : (chartDatum K ϖ).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        show piA ϖ ∈ (({Wa K, piA ϖ} : Finset (JetA K)) : Set (JetA K))
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_piA ϖ))

/-! ### The `ϖ`-rescaling twist (Prop 3.1's normalisation `W ↦ ϖX`) -/

/-- The componentwise `ϖ`-twist of 𝓑 (`X ↦ ϖX` on both jet components; the generic
`FiniteJet.rescaleRestricted` at `a := ϖ.val`). -/
def twistB (ϖ : Uniformizer K) : JetB K →+* JetB K :=
  JetNorm.mapHom (rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le)

/-- The twisted base map `θ = twist ∘ jB` implementing Prop 3.1's `W ↦ ϖX`. -/
def thetaChart (ϖ : Uniformizer K) : JetA K →+* JetB K :=
  (twistB K ϖ).comp (jB K)

omit [CompleteSpace K] in
/-- Rescaling fixes constant power series (`rescale a (C r) = C r`). -/
theorem rescaleRestricted_const (a : K) (ha : ‖a‖ ≤ 1) (r : K) :
    rescaleRestricted a ha (constHomPS K r) = constHomPS K r := by
  refine Subtype.ext ?_
  show PowerSeries.rescale a (PowerSeries.C r : PowerSeries K) = PowerSeries.C r
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp
  | succ k => simp

/-- `jB` sends the pseudouniformizer to the pseudouniformizer. -/
theorem jB_piA (ϖ : Uniformizer K) : jB K (piA ϖ) = piB ϖ := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine ofRestricted_injective (R := K) ?_
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 0 ((piA ϖ : JetA K) : JetC K), (piA ϖ).2.1⟩) =
      ofRestricted (constHomPS K ϖ.val)
    rw [ofRestricted_nonnegEquiv_symm]
    show qCoeff K 0 (constHomC K (RestrictedLaurent.C ϖ.val)) =
      ofRestricted (constHomPS K ϖ.val)
    rw [qCoeff_constHomC, if_pos rfl]
    show RestrictedLaurent.C ϖ.val =
      ofRestricted (PowerSeries.Restricted.C (1 : ℝ) ϖ.val)
    rw [ofRestricted_C]
    rfl
  · refine ofRestricted_injective (R := K) ?_
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 1 ((piA ϖ : JetA K) : JetC K), (piA ϖ).2.2⟩) =
      ofRestricted (0 : PowerSeries.Restricted K (1 : ℝ))
    rw [ofRestricted_nonnegEquiv_symm, map_zero]
    show qCoeff K 1 (constHomC K (RestrictedLaurent.C ϖ.val)) = 0
    rw [qCoeff_constHomC, if_neg one_ne_zero]

/-- The twist fixes the pseudouniformizer: `θ(ϖ_𝓐) = ϖ_𝓑`. -/
theorem thetaChart_piA (ϖ : Uniformizer K) : thetaChart K ϖ (piA ϖ) = piB ϖ := by
  show twistB K ϖ (jB K (piA ϖ)) = piB ϖ
  rw [jB_piA]
  refine TrivSqZeroExt.ext ?_ ?_
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le (constHomPS K ϖ.val) =
      constHomPS K ϖ.val
    exact rescaleRestricted_const K _ _ _
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le 0 = 0
    exact map_zero _

/-- The twisted base map is norm-nonincreasing, hence continuous (via the generic
`FiniteJet.norm_rescaleRestricted_le`). -/
theorem continuous_thetaChart (ϖ : Uniformizer K) : Continuous (thetaChart K ϖ) := by
  refine AddMonoidHomClass.continuous_of_bound (thetaChart K ϖ) 1 fun x => ?_
  rw [one_mul]
  show ‖twistB K ϖ (jB K x)‖ ≤ ‖x‖
  refine le_trans ?_ (norm_jB_le K x)
  show ‖(⟨rescaleRestricted _ _ (jB K x).fst,
    rescaleRestricted _ _ (jB K x).snd⟩ : JetB K)‖ ≤ ‖jB K x‖
  calc ‖(⟨rescaleRestricted _ _ (jB K x).fst,
        rescaleRestricted _ _ (jB K x).snd⟩ : JetB K)‖
      = max ‖rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le (jB K x).fst‖
          ‖rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le (jB K x).snd‖ :=
        JetNorm.norm_def _
    _ ≤ max ‖(jB K x).fst‖ ‖(jB K x).snd‖ :=
        max_le_max (norm_rescaleRestricted_le _ _ _) (norm_rescaleRestricted_le _ _ _)
    _ = ‖jB K x‖ := (JetNorm.norm_def _).symm

/-- The 𝓑-jet of `W` has vanishing `Q`-part. -/
theorem jB_Wa_snd : (jB K (Wa K)).snd = 0 := by
  refine ofRestricted_injective (R := K) ?_
  rw [map_zero]
  show ofRestricted ((nonnegEquiv (R := K)).symm
    ⟨qCoeff K 1 ((Wa K : JetA K) : JetC K), (Wa K).2.2⟩) = 0
  rw [ofRestricted_nonnegEquiv_symm]
  show qCoeff K 1 (sectionD K (TrivSqZeroExt.inl (Wu (R := K)).val)) = 0
  rw [qCoeff_sectionD]
  norm_num

/-- The Laurent shadow of the 𝓑-jet of `W` is the degree-one monomial. -/
theorem ofRestricted_jB_Wa_fst :
    ofRestricted (R := K) (jB K (Wa K)).fst = single 1 1 := by
  show ofRestricted ((nonnegEquiv (R := K)).symm
    ⟨qCoeff K 0 ((Wa K : JetA K) : JetC K), (Wa K).2.1⟩) = single 1 1
  rw [ofRestricted_nonnegEquiv_symm]
  show qCoeff K 0 (sectionD K (TrivSqZeroExt.inl (Wu (R := K)).val)) = single 1 1
  rw [qCoeff_sectionD]
  norm_num
  rfl

/-- Power-series coefficients of the 𝓑-jet of `W`. -/
theorem coeff_jB_Wa_fst (n : ℕ) :
    PowerSeries.coeff n ((jB K (Wa K)).fst).1 = if n = 1 then 1 else 0 := by
  have h : (ofPowerSeries ((jB K (Wa K)).fst)).coeff (n : ℤ) =
      (single 1 1 : RestrictedLaurent K).coeff (n : ℤ) := by
    rw [show ofPowerSeries ((jB K (Wa K)).fst) =
      ofRestricted (R := K) (jB K (Wa K)).fst from rfl, ofRestricted_jB_Wa_fst K]
  rw [coeff_ofPowerSeries, if_pos (by positivity), Int.toNat_natCast, coeff_single] at h
  rw [h]
  by_cases hn : n = 1
  · rw [if_pos (by exact_mod_cast hn), if_pos hn]
  · rw [if_neg (by exact_mod_cast hn), if_neg hn]

/-- **The key jet computation** ([FJP] Prop 3.1's `W ↦ ϖX`): the twist scales the
`W`-jet by the pseudouniformizer. -/
theorem thetaChart_Wa (ϖ : Uniformizer K) :
    thetaChart K ϖ (Wa K) = piB ϖ * jB K (Wa K) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le (jB K (Wa K)).fst =
      (piB ϖ * jB K (Wa K)).fst
    rw [TrivSqZeroExt.fst_mul]
    refine Subtype.ext ?_
    refine PowerSeries.ext fun n => ?_
    show PowerSeries.coeff n (PowerSeries.rescale ϖ.val ((jB K (Wa K)).fst).1) =
      PowerSeries.coeff n
        ((PowerSeries.C ϖ.val : PowerSeries K) * ((jB K (Wa K)).fst).1)
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_jB_Wa_fst]
    by_cases hn : n = 1
    · subst hn
      rw [if_pos rfl, pow_one]
    · rw [if_neg hn, mul_zero, mul_zero]
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le (jB K (Wa K)).snd =
      (piB ϖ * jB K (Wa K)).snd
    rw [jB_Wa_snd, map_zero, TrivSqZeroExt.snd_mul]
    rw [jB_Wa_snd]
    show (0 : PowerSeries.Restricted K (1 : ℝ)) =
      (piB ϖ).fst • (0 : PowerSeries.Restricted K (1 : ℝ)) +
        MulOpposite.op ((jB K (Wa K)).fst) • (piB ϖ).snd
    rw [smul_zero, show (piB ϖ).snd = 0 from rfl, smul_zero, add_zero]

/-- The element `Q ∈ 𝓐` (support `(0,1)`; [FJP] §1.4), over a general base. -/
def Qa : JetA K :=
  ⟨sectionD K (TrivSqZeroExt.inr (1 : L K)), by
    rw [mem_jetSupport_iff_jet_in_range, rhoC_sectionD]
    refine ⟨TrivSqZeroExt.inr ((nonnegEquiv (R := K)).symm
      ⟨(1 : RestrictedLaurent K), (nonnegSubring K).one_mem⟩), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted (R := K) 0 = 0
      exact map_zero _
    · show ofRestricted ((nonnegEquiv (R := K)).symm
        ⟨(1 : RestrictedLaurent K), (nonnegSubring K).one_mem⟩) = 1
      rw [ofRestricted_nonnegEquiv_symm]⟩

/-! ### Reindexing `K⟨W⟩ = PowerSeries.Restricted` into the project `TateAlgebra` -/

/-- Norm-restricted univariate power series are topologically restricted in the
`Fin 1`-indexed model (`renameEquiv` + decay transfer; port of the Laurent-instantiated
`FiniteJet.kwToTate` at the generic base, through the generic `FiniteJet.unitFinOne`). -/
def kwToTate :
    PowerSeries.Restricted K (1 : ℝ) →+* ↥(TateAlgebra K) where
  toFun f := ⟨MvPowerSeries.renameEquiv (R := K) unitFinOne f.1, by
    show MvPowerSeries.IsRestricted _
    have hf : PowerSeries.IsRestricted (1 : ℝ) f.1 := f.2
    rw [PowerSeries.IsRestricted] at hf
    simp only [one_pow, mul_one] at hf
    rw [← Nat.cofinite_eq_atTop] at hf
    have hf' : Filter.Tendsto (fun i : ℕ => PowerSeries.coeff i f.1)
        Filter.cofinite (nhds 0) := by
      rwa [tendsto_zero_iff_norm_tendsto_zero]
    show Filter.Tendsto (fun v : Fin 1 →₀ ℕ =>
      MvPowerSeries.coeff v (MvPowerSeries.renameEquiv (R := K) unitFinOne f.1))
      Filter.cofinite (nhds 0)
    have hpt : ∀ v : Fin 1 →₀ ℕ,
        MvPowerSeries.coeff v (MvPowerSeries.renameEquiv (R := K) unitFinOne f.1) =
        PowerSeries.coeff (v 0) f.1 := by
      intro v
      have hv : v = Finsupp.embDomain unitFinOne.toEmbedding
          (Finsupp.single () (v 0)) := by
        rw [Finsupp.embDomain_single]
        refine Finsupp.ext fun i => ?_
        rw [show i = (0 : Fin 1) from by omega, Finsupp.single_apply,
          if_pos (Subsingleton.elim _ _)]
      have hemb := MvPowerSeries.coeff_embDomain_rename (R := K)
        unitFinOne.toEmbedding f.1 (Finsupp.single () (v 0))
      rw [← hv] at hemb
      exact hemb
    rw [funext hpt]
    have hinj : Function.Injective (fun v : Fin 1 →₀ ℕ => v 0) := by
      intro v w h
      refine Finsupp.ext fun i => ?_
      rw [show i = (0 : Fin 1) from by omega]
      exact h
    exact hf'.comp hinj.tendsto_cofinite⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.renameEquiv (R := K) unitFinOne))
  map_mul' f g := Subtype.ext
    (map_mul (MvPowerSeries.renameEquiv (R := K) unitFinOne) f.1 g.1)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.renameEquiv (R := K) unitFinOne))
  map_add' f g := Subtype.ext
    (map_add (MvPowerSeries.renameEquiv (R := K) unitFinOne) f.1 g.1)

/-! ### The (3.3) collapse data: `Q² = Wⁿ · (W⁻ⁿQ²)` with unit `W`-multiples -/

/-- `W`'s underlying jet is the `Q⁰`-constant at the Laurent unit `W`. -/
theorem Wa_val_eq : ((Wa K : JetA K) : JetC K) = constHomC K (Wu (R := K)).val := by
  refine Subtype.ext ?_
  refine PowerSeries.ext fun n => ?_
  show PowerSeries.coeff n (sectionD K (TrivSqZeroExt.inl (Wu (R := K)).val)).1 = _
  rw [show (sectionD K (TrivSqZeroExt.inl (Wu (R := K)).val)).1 =
    PowerSeries.mk (fun n => if n = 0 then (Wu (R := K)).val else
      if n = 1 then 0 else 0) from rfl]
  rw [PowerSeries.coeff_mk]
  show _ = PowerSeries.coeff n (PowerSeries.C ((Wu (R := K)).val) :
    PowerSeries (L K))
  rw [PowerSeries.coeff_C]
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : n = 1
    · rw [if_pos h1]
    · rw [if_neg h1]

/-- The `W⁻ⁿQ²`-family: `yQ n := W⁻ⁿ·Q²` as an element of 𝓐 (its `(0,1)`-jets vanish). -/
def yQ (n : ℕ) : JetA K :=
  ⟨constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((Qa K : JetA K) : JetC K) *
    ((Qa K : JetA K) : JetC K), by
    have hq0 : qCoeff K 0 (((Qa K : JetA K) : JetC K)) = 0 := by
      show qCoeff K 0 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 0
      rw [qCoeff_sectionD]
      norm_num
    constructor
    · simp only [qCoeff_zero_mul, hq0, mul_zero]
      exact zero_mem _
    · simp only [qCoeff_one_mul, qCoeff_zero_mul, hq0, mul_zero, zero_mul, add_zero]
      exact zero_mem _⟩

/-- The collapse identity in 𝓐: `Wⁿ · (W⁻ⁿQ²) = Q²`. -/
theorem Wa_pow_mul_yQ (n : ℕ) : Wa K ^ n * yQ K n = Qa K * Qa K := by
  refine Subtype.ext ?_
  show ((Wa K : JetA K) : JetC K) ^ n *
    (constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((Qa K : JetA K) : JetC K) *
      ((Qa K : JetA K) : JetC K)) = ((Qa K : JetA K) : JetC K) * ((Qa K : JetA K) : JetC K)
  rw [Wa_val_eq, ← map_pow, ← mul_assoc, ← mul_assoc, ← map_mul,
    show (Wu (R := K)).val ^ n * ((Wu (R := K))⁻¹).val ^ n = 1 from by
      rw [← mul_pow]
      rw [show (Wu (R := K)).val * ((Wu (R := K))⁻¹).val = 1 from (Wu (R := K)).val_inv]
      rw [one_pow],
    map_one, one_mul]

/-- The collapse family is norm-bounded: `‖W⁻ⁿQ²‖ ≤ ‖Q‖²` (unit `W`-multiples are
isometric in 𝓒; via K8b's `winv_pow_val`). -/
theorem norm_yQ_le (n : ℕ) : ‖yQ K n‖ ≤ ‖Qa K‖ * ‖Qa K‖ := by
  show ‖constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((Qa K : JetA K) : JetC K) *
    ((Qa K : JetA K) : JetC K)‖ ≤ _
  rw [norm_JetC_mul, norm_JetC_mul, norm_constHomC]
  have hWinv : ‖((Wu (R := K))⁻¹).val ^ n‖ = 1 := by
    rw [winv_pow_val, norm_single, norm_one]
  rw [hWinv, one_mul]
  exact le_refl _

/-- **The (3.3) collapse**: `ρ(Q)² = 0` in the chart — the constant `ρ(Q²)` is a limit
of the null products `ρ(ϖ)ⁿ · (gⁿ · ρ(W⁻ⁿQ²))` ([FJP] Prop 3.1 proof; the scalar decay
needs only `0 < ‖ϖ.val‖ < 1`). -/
theorem canonicalMap_Qa_sq (ϖ : Uniformizer K) :
    (chartDatum K ϖ).canonicalMap (Qa K) * (chartDatum K ϖ).canonicalMap (Qa K) = 0 := by
  classical
  rw [← RingHom.map_mul (chartDatum K ϖ).canonicalMap]
  set ρ := (chartDatum K ϖ).canonicalMap with hρ
  set g := (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s) with hgdef
  -- `ρ(W) = ρ(ϖ) · g` (clear denominators in the localization)
  have hWsplit : ρ (Wa K) = ρ (piA ϖ) * g := by
    rw [hρ, hgdef]
    show (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (Wa K)) =
      (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (piA ϖ)) *
        (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s)
    rw [← RingHom.map_mul (chartDatum K ϖ).coeRingHom]
    congr 1
    rw [mul_comm]
    symm
    show divByS (Wa K) (chartDatum K ϖ).s *
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s =
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (Wa K)
    rw [divByS, IsLocalization.mk'_spec]
  -- per-`n` factorisation of the constant `ρ(Q²)`
  have hkey : ∀ n : ℕ, ρ (Qa K * Qa K) = ρ (piA ϖ) ^ n * (g ^ n * ρ (yQ K n)) := by
    intro n
    rw [← Wa_pow_mul_yQ K n, RingHom.map_mul ρ, map_pow ρ, hWsplit, mul_pow]
    ring
  -- the second factors form a bounded set
  have hbddY : TopologicalRing.IsBounded (Set.range fun n : ℕ => ρ (yQ K n)) := by
    -- scale into the unit ball by a fixed `ϖ^k`, then unscale by the unit `ρ(ϖ)⁻¹`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖piA ϖ‖ ^ k * (‖Qa K‖ * ‖Qa K‖) ≤ 1 := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < 1 / (1 + ‖Qa K‖ * ‖Qa K‖) by positivity) (norm_piA_lt_one ϖ)
      refine ⟨k, ?_⟩
      have h1 : ‖piA ϖ‖ ^ k * (‖Qa K‖ * ‖Qa K‖) ≤
          (1 / (1 + ‖Qa K‖ * ‖Qa K‖)) * (‖Qa K‖ * ‖Qa K‖) := by
        refine mul_le_mul_of_nonneg_right hk.le (by positivity)
      refine h1.trans ?_
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith [mul_nonneg (norm_nonneg (Qa K)) (norm_nonneg (Qa K))]
    have hunit : IsUnit (ρ (piA ϖ)) := by
      rw [hρ]
      show IsUnit ((chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s))
      refine IsUnit.map _ ?_
      exact IsLocalization.map_units (Localization.Away (chartDatum K ϖ).s)
        ⟨(chartDatum K ϖ).s, Submonoid.mem_powers _⟩
    obtain ⟨u, hu⟩ := hunit
    -- the scaled family lies in the bounded `coeRingHom`-image of `locSubring`
    have hball : TopologicalRing.IsBounded
        (Set.range fun n : ℕ => ρ (piA ϖ ^ k * yQ K n)) := by
      refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
        (chartDatum K ϖ)).subset ?_
      rintro _ ⟨n, rfl⟩
      refine ⟨algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s)
        (piA ϖ ^ k * yQ K n), ?_, rfl⟩
      refine algebraMap_mem_locSubring _ _ _ ?_
      show piA ϖ ^ k * yQ K n ∈ (podA K ϖ).A₀
      show ‖piA ϖ ^ k * yQ K n‖ ≤ 1
      rw [norm_JetA_mul, norm_JetA_pow]
      calc ‖piA ϖ‖ ^ k * ‖yQ K n‖ ≤ ‖piA ϖ‖ ^ k * (‖Qa K‖ * ‖Qa K‖) := by
            refine mul_le_mul_of_nonneg_left (norm_yQ_le K n) (by positivity)
        _ ≤ 1 := hk
    -- unscale: `ρ(yQ n) = (u⁻¹)ᵏ · ρ(ϖᵏ yQ n)`
    have hres : (Set.range fun n : ℕ => ρ (yQ K n)) ⊆
        ({((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
          presheafValue (chartDatum K ϖ)) ^ k} : Set (presheafValue (chartDatum K ϖ))) *
          Set.range fun n : ℕ => ρ (piA ϖ ^ k * yQ K n) := by
      rintro _ ⟨n, rfl⟩
      refine ⟨((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) ^ k, rfl, ρ (piA ϖ ^ k * yQ K n), ⟨n, rfl⟩, ?_⟩
      show ((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) ^ k * ρ (piA ϖ ^ k * yQ K n) = ρ (yQ K n)
      rw [RingHom.map_mul ρ, map_pow ρ, ← hu, ← mul_assoc, ← mul_pow]
      rw [show ((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) * u = 1 from u.inv_mul]
      rw [one_pow, one_mul]
    exact ((TopologicalRing.isBounded_singleton _).mul hball).subset hres
  have hbddG : TopologicalRing.IsBounded
      (Set.range (g ^ · : ℕ → presheafValue (chartDatum K ϖ))) := by
    have hmem : divByS (Wa K) (chartDatum K ϖ).s ∈
        locSubring (chartDatum K ϖ).P (chartDatum K ϖ).T (chartDatum K ϖ).s :=
      divByS_mem_locSubring _ _ _ (Finset.mem_insert_self _ _)
    refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
      (chartDatum K ϖ)).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨divByS (Wa K) (chartDatum K ϖ).s ^ n, pow_mem hmem n, by
      rw [map_pow]⟩
  have hbdd : TopologicalRing.IsBounded
      (Set.range fun n : ℕ => g ^ n * ρ (yQ K n)) := by
    refine (hbddG.mul hbddY).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨g ^ n, ⟨n, rfl⟩, ρ (yQ K n), ⟨n, rfl⟩, rfl⟩
  -- the scalar powers are null
  have hnull : Filter.Tendsto (fun n : ℕ => ρ (piA ϖ) ^ n) Filter.atTop
      (nhds (0 : presheafValue (chartDatum K ϖ))) := by
    have htend : Filter.Tendsto (fun n : ℕ => piA ϖ ^ n) Filter.atTop
        (nhds (0 : JetA K)) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_JetA_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_piA_lt_one ϖ)
    have hcont := (canonicalMap_continuous (chartDatum K ϖ)).continuousAt
      (x := (0 : JetA K))
    have := hcont.tendsto.comp htend
    rw [hρ]
    simpa only [Function.comp_def, map_pow, map_zero] using this
  -- absorption: the constant `ρ(Q²)` lies in every neighbourhood of `0`
  have hmem0 : ∀ U ∈ nhds (0 : presheafValue (chartDatum K ϖ)), ρ (Qa K * Qa K) ∈ U := by
    intro U hU
    obtain ⟨V, hV, hVU⟩ := hbdd U hU
    have hev := hnull hV
    rw [Filter.mem_map] at hev
    obtain ⟨n, hn⟩ := (Filter.eventually_atTop.mp hev)
    have hnn := hn n (le_refl n)
    rw [hkey n, mul_comm]
    exact hVU (Set.mul_mem_mul ⟨n, rfl⟩ hnn)
  -- T1 separation forces the constant to be `0`
  haveI : RegularSpace (presheafValue (chartDatum K ϖ)) := UniformSpace.to_regularSpace
  have h0mem : (0 : presheafValue (chartDatum K ϖ)) ∈ closure {ρ (Qa K * Qa K)} := by
    rw [mem_closure_iff_nhds]
    intro U hU
    exact ⟨ρ (Qa K * Qa K), hmem0 U hU, rfl⟩
  rw [closure_singleton] at h0mem
  exact (Set.mem_singleton_iff.mp h0mem).symm

/-! ### The generalized (3.3) collapse: `ρ` kills the whole `Q²𝓒`-part -/

/-- The generalized `W⁻ⁿ`-family at any `Q²`-supported element. -/
def yGen (y : JetA K) (hy0 : qCoeff K 0 ((y : JetA K) : JetC K) = 0)
    (hy1 : qCoeff K 1 ((y : JetA K) : JetC K) = 0) (n : ℕ) : JetA K :=
  ⟨constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((y : JetA K) : JetC K), by
    constructor
    · simp only [qCoeff_zero_mul, hy0, mul_zero]
      exact zero_mem _
    · simp only [qCoeff_one_mul, hy0, hy1, mul_zero, add_zero]
      exact zero_mem _⟩

theorem Wa_pow_mul_yGen (y : JetA K) (hy0 : qCoeff K 0 ((y : JetA K) : JetC K) = 0)
    (hy1 : qCoeff K 1 ((y : JetA K) : JetC K) = 0) (n : ℕ) :
    Wa K ^ n * yGen K y hy0 hy1 n = y := by
  refine Subtype.ext ?_
  show ((Wa K : JetA K) : JetC K) ^ n *
    (constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((y : JetA K) : JetC K)) =
    ((y : JetA K) : JetC K)
  rw [Wa_val_eq, ← map_pow, ← mul_assoc, ← map_mul,
    show (Wu (R := K)).val ^ n * ((Wu (R := K))⁻¹).val ^ n = 1 from by
      rw [← mul_pow]
      rw [show (Wu (R := K)).val * ((Wu (R := K))⁻¹).val = 1 from (Wu (R := K)).val_inv]
      rw [one_pow],
    map_one, one_mul]

theorem norm_yGen_le (y : JetA K) (hy0 : qCoeff K 0 ((y : JetA K) : JetC K) = 0)
    (hy1 : qCoeff K 1 ((y : JetA K) : JetC K) = 0) (n : ℕ) :
    ‖yGen K y hy0 hy1 n‖ ≤ ‖y‖ := by
  show ‖constHomC K (((Wu (R := K))⁻¹).val ^ n) * ((y : JetA K) : JetC K)‖ ≤ _
  rw [norm_JetC_mul, norm_constHomC]
  have hWinv : ‖((Wu (R := K))⁻¹).val ^ n‖ = 1 := by
    rw [winv_pow_val, norm_single, norm_one]
  rw [hWinv, one_mul]
  exact le_of_eq rfl

/-- **The generalized (3.3) collapse**: `ρ` kills every `Q²`-supported element of 𝓐. -/
theorem canonicalMap_eq_zero_of_qSq (ϖ : Uniformizer K) (y : JetA K)
    (hy0 : qCoeff K 0 ((y : JetA K) : JetC K) = 0)
    (hy1 : qCoeff K 1 ((y : JetA K) : JetC K) = 0) :
    (chartDatum K ϖ).canonicalMap y = 0 := by
  classical
  set ρ := (chartDatum K ϖ).canonicalMap with hρ
  set g := (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s) with hgdef
  have hWsplit : ρ (Wa K) = ρ (piA ϖ) * g := by
    rw [hρ, hgdef]
    show (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (Wa K)) =
      (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (piA ϖ)) *
        (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s)
    rw [← RingHom.map_mul (chartDatum K ϖ).coeRingHom]
    congr 1
    rw [mul_comm]
    symm
    show divByS (Wa K) (chartDatum K ϖ).s *
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s =
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (Wa K)
    rw [divByS, IsLocalization.mk'_spec]
  have hkey : ∀ n : ℕ, ρ y = ρ (piA ϖ) ^ n * (g ^ n * ρ (yGen K y hy0 hy1 n)) := by
    intro n
    conv_lhs => rw [← Wa_pow_mul_yGen K y hy0 hy1 n]
    rw [RingHom.map_mul ρ, map_pow ρ, hWsplit, mul_pow]
    ring
  have hbddY : TopologicalRing.IsBounded
      (Set.range fun n : ℕ => ρ (yGen K y hy0 hy1 n)) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖piA ϖ‖ ^ k * ‖y‖ ≤ 1 := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < 1 / (1 + ‖y‖) by positivity) (norm_piA_lt_one ϖ)
      refine ⟨k, ?_⟩
      have h1 : ‖piA ϖ‖ ^ k * ‖y‖ ≤ (1 / (1 + ‖y‖)) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
      refine h1.trans ?_
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith [norm_nonneg y]
    have hunit : IsUnit (ρ (piA ϖ)) := by
      rw [hρ]
      show IsUnit ((chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
        (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s))
      refine IsUnit.map _ ?_
      exact IsLocalization.map_units (Localization.Away (chartDatum K ϖ).s)
        ⟨(chartDatum K ϖ).s, Submonoid.mem_powers _⟩
    obtain ⟨u, hu⟩ := hunit
    have hball : TopologicalRing.IsBounded
        (Set.range fun n : ℕ => ρ (piA ϖ ^ k * yGen K y hy0 hy1 n)) := by
      refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
        (chartDatum K ϖ)).subset ?_
      rintro _ ⟨n, rfl⟩
      refine ⟨algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s)
        (piA ϖ ^ k * yGen K y hy0 hy1 n), ?_, rfl⟩
      refine algebraMap_mem_locSubring _ _ _ ?_
      show piA ϖ ^ k * yGen K y hy0 hy1 n ∈ (podA K ϖ).A₀
      show ‖piA ϖ ^ k * yGen K y hy0 hy1 n‖ ≤ 1
      rw [norm_JetA_mul, norm_JetA_pow]
      calc ‖piA ϖ‖ ^ k * ‖yGen K y hy0 hy1 n‖ ≤ ‖piA ϖ‖ ^ k * ‖y‖ :=
            mul_le_mul_of_nonneg_left (norm_yGen_le K y hy0 hy1 n) (by positivity)
        _ ≤ 1 := hk
    have hres : (Set.range fun n : ℕ => ρ (yGen K y hy0 hy1 n)) ⊆
        ({((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
          presheafValue (chartDatum K ϖ)) ^ k} : Set (presheafValue (chartDatum K ϖ))) *
          Set.range fun n : ℕ => ρ (piA ϖ ^ k * yGen K y hy0 hy1 n) := by
      rintro _ ⟨n, rfl⟩
      refine ⟨((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) ^ k, rfl,
        ρ (piA ϖ ^ k * yGen K y hy0 hy1 n), ⟨n, rfl⟩, ?_⟩
      show ((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) ^ k * ρ (piA ϖ ^ k * yGen K y hy0 hy1 n) =
        ρ (yGen K y hy0 hy1 n)
      rw [RingHom.map_mul ρ, map_pow ρ, ← hu, ← mul_assoc, ← mul_pow]
      rw [show ((u⁻¹ : (presheafValue (chartDatum K ϖ))ˣ) :
        presheafValue (chartDatum K ϖ)) * u = 1 from u.inv_mul]
      rw [one_pow, one_mul]
    exact ((TopologicalRing.isBounded_singleton _).mul hball).subset hres
  have hbddG : TopologicalRing.IsBounded
      (Set.range (g ^ · : ℕ → presheafValue (chartDatum K ϖ))) := by
    have hmem : divByS (Wa K) (chartDatum K ϖ).s ∈
        locSubring (chartDatum K ϖ).P (chartDatum K ϖ).T (chartDatum K ϖ).s :=
      divByS_mem_locSubring _ _ _ (Finset.mem_insert_self _ _)
    refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
      (chartDatum K ϖ)).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨divByS (Wa K) (chartDatum K ϖ).s ^ n, pow_mem hmem n, by rw [map_pow]⟩
  have hbdd : TopologicalRing.IsBounded
      (Set.range fun n : ℕ => g ^ n * ρ (yGen K y hy0 hy1 n)) := by
    refine (hbddG.mul hbddY).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨g ^ n, ⟨n, rfl⟩, ρ (yGen K y hy0 hy1 n), ⟨n, rfl⟩, rfl⟩
  have hnull : Filter.Tendsto (fun n : ℕ => ρ (piA ϖ) ^ n) Filter.atTop
      (nhds (0 : presheafValue (chartDatum K ϖ))) := by
    have htend : Filter.Tendsto (fun n : ℕ => piA ϖ ^ n) Filter.atTop
        (nhds (0 : JetA K)) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_JetA_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_piA_lt_one ϖ)
    have hcont := (canonicalMap_continuous (chartDatum K ϖ)).continuousAt
      (x := (0 : JetA K))
    have := hcont.tendsto.comp htend
    rw [hρ]
    simpa only [Function.comp_def, map_pow, map_zero] using this
  have hmem0 : ∀ U ∈ nhds (0 : presheafValue (chartDatum K ϖ)), ρ y ∈ U := by
    intro U hU
    obtain ⟨V, hV, hVU⟩ := hbdd U hU
    have hev := hnull hV
    rw [Filter.mem_map] at hev
    obtain ⟨n, hn⟩ := (Filter.eventually_atTop.mp hev)
    have hnn := hn n (le_refl n)
    rw [hkey n, mul_comm]
    exact hVU (Set.mul_mem_mul ⟨n, rfl⟩ hnn)
  haveI : RegularSpace (presheafValue (chartDatum K ϖ)) := UniformSpace.to_regularSpace
  have h0mem : (0 : presheafValue (chartDatum K ϖ)) ∈ closure {ρ y} := by
    rw [mem_closure_iff_nhds]
    intro U hU
    exact ⟨ρ y, hmem0 U hU, rfl⟩
  rw [closure_singleton] at h0mem
  exact (Set.mem_singleton_iff.mp h0mem).symm

/-! ### The 2-jet decomposition of 𝓐 (step 2 of the roundtrip plan) -/

/-- `Q`'s underlying jet is the power-series variable. -/
theorem Qa_val_eq :
    (((Qa K : JetA K) : JetC K)).1 = (PowerSeries.X : PowerSeries (L K)) := by
  refine PowerSeries.ext fun n => ?_
  show PowerSeries.coeff n (sectionD K (TrivSqZeroExt.inr (1 : L K))).1 = _
  rw [show (sectionD K (TrivSqZeroExt.inr (1 : L K))).1 =
    PowerSeries.mk (fun n => if n = 0 then (TrivSqZeroExt.inr (1 : L K) : JetD K).fst
      else if n = 1 then (TrivSqZeroExt.inr (1 : L K) : JetD K).snd else 0) from rfl,
    PowerSeries.coeff_mk, PowerSeries.coeff_X]
  by_cases h1 : n = 1
  · subst h1
    norm_num
  · rw [if_neg h1]
    by_cases h0 : n = 0
    · subst h0
      norm_num
    · rw [if_neg h0, if_neg h1]

/-- The nonneg-constant lift `𝓐 ∋ constNN b` for a nonnegative Laurent series `b`. -/
def constNN (b : L K) (hb : b ∈ nonnegSubring K) : JetA K :=
  ⟨constHomC K b, by
    constructor
    · rw [qCoeff_constHomC, if_pos rfl]
      exact hb
    · rw [qCoeff_constHomC, if_neg one_ne_zero]
      exact zero_mem _⟩

/-- The 2-jet decomposition: every `a ∈ 𝓐` splits as
`constNN(a₀) + Q·constNN(a₁) + (Q²-part)`. -/
theorem jet_decomposition (a : JetA K) :
    ∃ y : JetA K, (qCoeff K 0 ((y : JetA K) : JetC K) = 0 ∧
      qCoeff K 1 ((y : JetA K) : JetC K) = 0) ∧
    a = constNN K (qCoeff K 0 ((a : JetA K) : JetC K)) a.2.1 +
      Qa K * constNN K (qCoeff K 1 ((a : JetA K) : JetC K)) a.2.2 + y := by
  refine ⟨a - (constNN K (qCoeff K 0 ((a : JetA K) : JetC K)) a.2.1 +
    Qa K * constNN K (qCoeff K 1 ((a : JetA K) : JetC K)) a.2.2), ⟨?_, ?_⟩, by ring⟩
  · show qCoeff K 0 (((a : JetA K) : JetC K) -
      (constHomC K (qCoeff K 0 ((a : JetA K) : JetC K)) +
        ((Qa K : JetA K) : JetC K) * constHomC K (qCoeff K 1 ((a : JetA K) : JetC K)))) = 0
    rw [sub_eq_add_neg, qCoeff_add, qCoeff_neg, qCoeff_add, qCoeff_constHomC,
      if_pos rfl, qCoeff_zero_mul]
    rw [show qCoeff K 0 (((Qa K : JetA K) : JetC K)) = 0 from by
      show qCoeff K 0 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 0
      rw [qCoeff_sectionD]; norm_num]
    ring
  · show qCoeff K 1 (((a : JetA K) : JetC K) -
      (constHomC K (qCoeff K 0 ((a : JetA K) : JetC K)) +
        ((Qa K : JetA K) : JetC K) * constHomC K (qCoeff K 1 ((a : JetA K) : JetC K)))) = 0
    rw [sub_eq_add_neg, qCoeff_add, qCoeff_neg, qCoeff_add, qCoeff_constHomC,
      if_neg one_ne_zero, qCoeff_one_mul]
    rw [show qCoeff K 0 (((Qa K : JetA K) : JetC K)) = 0 from by
      show qCoeff K 0 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 0
      rw [qCoeff_sectionD]; norm_num]
    rw [show qCoeff K 1 (((Qa K : JetA K) : JetC K)) = 1 from by
      show qCoeff K 1 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 1
      rw [qCoeff_sectionD]; norm_num]
    rw [qCoeff_constHomC]
    norm_num
    rw [qCoeff_constHomC, if_pos rfl]
    ring

/-! ### The forward map `𝒪_𝓐(chart) → 𝓑` (Prop 3.1's `ψ`-direction) -/

theorem isUnit_thetaChart_s (ϖ : Uniformizer K) :
    IsUnit (thetaChart K ϖ (chartDatum K ϖ).s) := by
  show IsUnit (thetaChart K ϖ (piA ϖ))
  rw [thetaChart_piA]
  exact isUnit_piB ϖ

/-- The chart's localization lift into 𝓑 (`ϖ` is already a unit there). -/
def chartLocHom (ϖ : Uniformizer K) :
    Localization.Away (chartDatum K ϖ).s →+* JetB K :=
  IsLocalization.Away.lift (S := Localization.Away (chartDatum K ϖ).s)
    (chartDatum K ϖ).s (isUnit_thetaChart_s K ϖ)

theorem chartLocHom_algebraMap (ϖ : Uniformizer K) (a : JetA K) :
    chartLocHom K ϖ (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) a) =
      thetaChart K ϖ a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The chart generator `W/ϖ` maps to the norm-one disc variable `jB(W)`
(the rescaling at work: `θ(W)/θ(ϖ) = ϖ·jB(W)/ϖ`). -/
theorem chartLocHom_divByS_Wa (ϖ : Uniformizer K) :
    chartLocHom K ϖ (divByS (Wa K) (chartDatum K ϖ).s) = jB K (Wa K) := by
  have hu := isUnit_thetaChart_s K ϖ
  have hspec : divByS (Wa K) (chartDatum K ϖ).s *
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s =
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (Wa K) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (chartLocHom K ϖ) hspec
  rw [RingHom.map_mul (chartLocHom K ϖ), chartLocHom_algebraMap,
    chartLocHom_algebraMap] at happ
  -- `chartLocHom (W/ϖ) · θ(ϖ) = θ(W) = ϖ_𝓑 · jB(W)`; cancel the unit `θ(ϖ) = ϖ_𝓑`.
  rw [show thetaChart K ϖ (chartDatum K ϖ).s = piB ϖ from thetaChart_piA K ϖ,
    show thetaChart K ϖ (Wa K) = piB ϖ * jB K (Wa K) from thetaChart_Wa K ϖ] at happ
  refine (isUnit_piB ϖ).mul_left_cancel ?_
  rw [mul_comm (piB ϖ) (chartLocHom K ϖ (divByS (Wa K) (chartDatum K ϖ).s))]
  exact happ

theorem chartLocHom_divByS_piA (ϖ : Uniformizer K) :
    chartLocHom K ϖ (divByS (piA ϖ) (chartDatum K ϖ).s) = 1 := by
  have hu := isUnit_thetaChart_s K ϖ
  have hspec : divByS (piA ϖ) (chartDatum K ϖ).s *
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s =
      algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (piA ϖ) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (chartLocHom K ϖ) hspec
  rw [RingHom.map_mul (chartLocHom K ϖ), chartLocHom_algebraMap,
    chartLocHom_algebraMap] at happ
  rw [show thetaChart K ϖ (chartDatum K ϖ).s = piB ϖ from thetaChart_piA K ϖ,
    show thetaChart K ϖ (piA ϖ) = piB ϖ from thetaChart_piA K ϖ] at happ
  refine (isUnit_piB ϖ).mul_left_cancel ?_
  rw [mul_comm (piB ϖ) (chartLocHom K ϖ (divByS (piA ϖ) (chartDatum K ϖ).s)), happ,
    mul_one]

/-- `‖jB(W)‖ = 1`. -/
theorem norm_jB_Wa : ‖jB K (Wa K)‖ = 1 := by
  have h1 : ‖(jB K (Wa K)).fst‖ = 1 := by
    rw [← ofRestricted_norm (R := K), ofRestricted_jB_Wa_fst, norm_single, norm_one]
  calc ‖jB K (Wa K)‖ = max ‖(jB K (Wa K)).fst‖ ‖(jB K (Wa K)).snd‖ :=
        JetNorm.norm_def _
    _ = 1 := by
        rw [h1, jB_Wa_snd, norm_zero]
        exact max_eq_left zero_le_one

/-- Continuity of the chart's localization lift (universal property; the generators map
to norm-`≤ 1` elements of 𝓑). -/
theorem chartLocHom_continuous (ϖ : Uniformizer K) :
    @Continuous _ _ (chartDatum K ϖ).topology _ (chartLocHom K ϖ) := by
  refine locTopology_continuous_lift (chartDatum K ϖ).P (chartDatum K ϖ).T
    (chartDatum K ϖ).s (chartDatum K ϖ).hopen _ ?_ ?_
  · have h_eq : (chartLocHom K ϖ).comp
        (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s)) =
        thetaChart K ϖ :=
      RingHom.ext fun a => chartLocHom_algebraMap K ϖ a
    rw [show ⇑((chartLocHom K ϖ).comp
        (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s)))
        = ⇑(thetaChart K ϖ) from congrArg _ h_eq]
    exact continuous_thetaChart K ϖ
  · intro t ht
    have hmem : t = Wa K ∨ t = piA ϖ := by
      rcases Finset.mem_insert.mp ht with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases hmem with rfl | rfl
    · rw [show divByS (Wa K) (chartDatum K ϖ).s = divByS (Wa K) (chartDatum K ϖ).s
        from rfl, chartLocHom_divByS_Wa]
      exact isPowerBounded_of_norm_le_one (le_of_eq (norm_jB_Wa K))
    · rw [chartLocHom_divByS_piA]
      exact isPowerBounded_of_norm_le_one (le_of_eq norm_one)

/-- Forward: `𝒪_𝓐(chart) → 𝓑` (completion extension; 𝓑 is complete Hausdorff). -/
def chartFwd (ϖ : Uniformizer K) : presheafValue (chartDatum K ϖ) →+* JetB K := by
  letI := (chartDatum K ϖ).uniformSpace
  letI : IsTopologicalRing (Localization.Away (chartDatum K ϖ).s) :=
    (chartDatum K ϖ).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (chartDatum K ϖ).s) :=
    (chartDatum K ϖ).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (chartLocHom K ϖ)
    (chartLocHom_continuous K ϖ)

theorem chartFwd_coe (ϖ : Uniformizer K) (a : Localization.Away (chartDatum K ϖ).s) :
    chartFwd K ϖ ((chartDatum K ϖ).coeRingHom a) = chartLocHom K ϖ a := by
  letI := (chartDatum K ϖ).uniformSpace
  letI : IsTopologicalRing (Localization.Away (chartDatum K ϖ).s) :=
    (chartDatum K ϖ).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (chartDatum K ϖ).s) :=
    (chartDatum K ϖ).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (chartLocHom K ϖ)
    (chartLocHom_continuous K ϖ) a

theorem chartFwd_continuous (ϖ : Uniformizer K) : Continuous (chartFwd K ϖ) := by
  letI := (chartDatum K ϖ).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! ### The reverse map `𝓑 → 𝒪_𝓐(chart)` (Prop 3.1's `φ`-direction) -/

/-- The chart generator `W/ϖ`, in the completion. -/
def gChart (ϖ : Uniformizer K) : presheafValue (chartDatum K ϖ) :=
  (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s)

theorem gChart_isBounded (ϖ : Uniformizer K) :
    TopologicalRing.IsBounded
      (Set.range (gChart K ϖ ^ · : ℕ → presheafValue (chartDatum K ϖ))) := by
  have hmem : divByS (Wa K) (chartDatum K ϖ).s ∈
      locSubring (chartDatum K ϖ).P (chartDatum K ϖ).T (chartDatum K ϖ).s :=
    divByS_mem_locSubring _ _ _ (Finset.mem_insert_self _ _)
  refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (chartDatum K ϖ)).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (Wa K) (chartDatum K ϖ).s ^ n, pow_mem hmem n, by rw [map_pow]; rfl⟩

/-- Constants of `K` in the chart (continuous base for the evaluation). -/
def chartConst (ϖ : Uniformizer K) : K →+* presheafValue (chartDatum K ϖ) :=
  (chartDatum K ϖ).canonicalMap.comp (constA K)

theorem chartConst_continuous (ϖ : Uniformizer K) : Continuous (chartConst K ϖ) := by
  refine (canonicalMap_continuous (chartDatum K ϖ)).comp ?_
  exact AddMonoidHomClass.continuous_of_bound (constA K) 1 fun a => by
    rw [one_mul, norm_constA]

/-- Evaluation of `K⟨X⟩` in the chart: `X ↦ W/ϖ`. -/
def chartEval (ϖ : Uniformizer K) :
    PowerSeries.Restricted K (1 : ℝ) →+* presheafValue (chartDatum K ϖ) :=
  (TateAlgebraWedhorn.evalHomBounded (chartConst K ϖ) (chartConst_continuous K ϖ)
    (gChart K ϖ) (gChart_isBounded K ϖ)).comp (kwToTate K)

omit [CompleteSpace K] in
/-- Coefficients pass through the reindexing bridge. -/
theorem coeff_kwToTate (f : PowerSeries.Restricted K (1 : ℝ)) (n : ℕ) :
    TateAlgebra.coeff n (kwToTate K f) = PowerSeries.coeff n f.1 := by
  show MvPowerSeries.coeff (TateAlgebra.toIndex n)
    (MvPowerSeries.renameEquiv (R := K) unitFinOne f.1) = _
  have hv : TateAlgebra.toIndex n = Finsupp.embDomain unitFinOne.toEmbedding
      (Finsupp.single () n) := by
    rw [Finsupp.embDomain_single]
    refine Finsupp.ext fun i => ?_
    rw [show i = (0 : Fin 1) from by omega, TateAlgebra.toIndex,
      Finsupp.single_apply, Finsupp.single_apply,
      if_pos (Subsingleton.elim _ _), if_pos (Subsingleton.elim _ _)]
  have hemb := MvPowerSeries.coeff_embDomain_rename (R := K)
    unitFinOne.toEmbedding f.1 (Finsupp.single () n)
  rw [← hv] at hemb
  exact hemb

/-- The evaluation fixes constants: `chartEval (C r) = ρ(constA r)`. -/
theorem chartEval_const (ϖ : Uniformizer K) (r : K) :
    chartEval K ϖ (constHomPS K r) = chartConst K ϖ r := by
  show ∑' n, TateAlgebraWedhorn.evalTerm (chartConst K ϖ) (gChart K ϖ)
    (kwToTate K (constHomPS K r)) n = chartConst K ϖ r
  rw [tsum_eq_single 0]
  · rw [TateAlgebraWedhorn.evalTerm, coeff_kwToTate]
    show chartConst K ϖ (PowerSeries.coeff 0 (PowerSeries.C r : PowerSeries K)) *
      gChart K ϖ ^ 0 = chartConst K ϖ r
    rw [PowerSeries.coeff_zero_C, pow_zero, mul_one]
  · intro n hn
    rw [TateAlgebraWedhorn.evalTerm, coeff_kwToTate]
    show chartConst K ϖ (PowerSeries.coeff n (PowerSeries.C r : PowerSeries K)) *
      gChart K ϖ ^ n = 0
    rw [PowerSeries.coeff_C, if_neg hn, map_zero, zero_mul]

/-- The evaluation sends the disc variable to the chart generator `W/ϖ`. -/
theorem chartEval_jBWa_fst (ϖ : Uniformizer K) :
    chartEval K ϖ ((jB K (Wa K)).fst) = gChart K ϖ := by
  show ∑' n, TateAlgebraWedhorn.evalTerm (chartConst K ϖ) (gChart K ϖ)
    (kwToTate K ((jB K (Wa K)).fst)) n = gChart K ϖ
  rw [tsum_eq_single 1]
  · rw [TateAlgebraWedhorn.evalTerm, coeff_kwToTate, coeff_jB_Wa_fst,
      if_pos rfl, map_one, one_mul, pow_one]
  · intro n hn
    rw [TateAlgebraWedhorn.evalTerm, coeff_kwToTate, coeff_jB_Wa_fst,
      if_neg hn, map_zero, zero_mul]

/-- Sums of open-subgroup members stay in the subgroup (local copy of the private
helper from the functoriality file). -/
private theorem tsum_mem_of_isOpen_addSubgroup'' {ι G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem fun i _ => hmem i

/-- Continuity of the chart evaluation from the norm topology on `K⟨X⟩`
(Gauss-ball mirror of the functoriality-file evaluation continuity; the T-topology
obstruction recorded in `TateAlgebraWedhorn` does not apply to the norm source). -/
theorem chartEval_continuous (ϖ : Uniformizer K) : Continuous (chartEval K ϖ) := by
  classical
  refine continuous_of_continuousAt_zero (chartEval K ϖ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := gChart_isBounded K ϖ (W : Set (presheafValue (chartDatum K ϖ)))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : chartConst K ϖ ⁻¹' V ∈ nhds (0 : K) :=
    (chartConst_continuous K ϖ).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : PowerSeries.Restricted K (1 : ℝ)) hδ) ?_
  intro f hf
  rw [Metric.mem_ball, dist_zero_right] at hf
  apply hWU
  change (∑' n, TateAlgebraWedhorn.evalTerm (chartConst K ϖ) (gChart K ϖ)
    (kwToTate K f) n) ∈ (W : Set (presheafValue (chartDatum K ϖ)))
  refine tsum_mem_of_isOpen_addSubgroup''
    (TateAlgebraWedhorn.evalTerm_summable (chartConst K ϖ) (chartConst_continuous K ϖ)
      (gChart K ϖ) (gChart_isBounded K ϖ) (kwToTate K f)) W.isOpen fun n => ?_
  have hcoeff : ‖PowerSeries.coeff n f.1‖ < δ := by
    refine lt_of_le_of_lt ?_ hf
    have h1 : ‖PowerSeries.coeff n f.1‖ * (1 : ℝ) ^ n ≤ ‖f‖ := by
      rw [Restricted.norm_eq]
      exact PowerSeries.le_gaussNorm (norm : K → ℝ) 1 f.1
        (Restricted.hasGaussNorm 1 f) n
    simpa using h1
  have hVmem : chartConst K ϖ (PowerSeries.coeff n f.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change TateAlgebraWedhorn.evalTerm (chartConst K ϖ) (gChart K ϖ) (kwToTate K f) n ∈ W
  rw [show TateAlgebraWedhorn.evalTerm (chartConst K ϖ) (gChart K ϖ) (kwToTate K f) n =
      gChart K ϖ ^ n * chartConst K ϖ (PowerSeries.coeff n f.1) from by
    rw [TateAlgebraWedhorn.evalTerm, coeff_kwToTate]
    exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨n, rfl⟩ hVmem)

/-! ### 1-variable polynomial density in `K⟨X⟩` (step 3 substrate) -/

/-- Polynomials embed into the restricted disc algebra. -/
def polyKW : Polynomial K →+* PowerSeries.Restricted K (1 : ℝ) where
  toFun p := ⟨(p : PowerSeries K), by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [PowerSeries.IsRestricted]
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Filter.eventually_atTop]
    refine ⟨p.natDegree + 1, fun n hn => ?_⟩
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      norm_zero, zero_mul]⟩
  map_one' := Subtype.ext (map_one (Polynomial.coeToPowerSeries.ringHom (R := K)))
  map_mul' p q := Subtype.ext
    (map_mul (Polynomial.coeToPowerSeries.ringHom (R := K)) p q)
  map_zero' := Subtype.ext (map_zero (Polynomial.coeToPowerSeries.ringHom (R := K)))
  map_add' p q := Subtype.ext
    (map_add (Polynomial.coeToPowerSeries.ringHom (R := K)) p q)

omit [CompleteSpace K] in
/-- Polynomials are dense in `K⟨X⟩` (truncate below any coefficient level). -/
theorem polyKW_denseRange : DenseRange (polyKW K) := by
  classical
  rw [Metric.denseRange_iff]
  intro f ε hε
  have hfin : {n : ℕ | ε / 2 ≤ ‖PowerSeries.coeff n f.1‖}.Finite := by
    have hf : PowerSeries.IsRestricted (1 : ℝ) f.1 := f.2
    rw [PowerSeries.IsRestricted] at hf
    simp only [one_pow, mul_one] at hf
    have hev := hf.eventually (eventually_lt_nhds (half_pos hε) (a := (0 : ℝ)))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro n hn
    by_contra hlt
    simp only [Set.mem_Iio, not_lt] at hlt
    exact absurd (hN n hlt) (not_lt.mpr hn)
  refine ⟨∑ n ∈ hfin.toFinset, Polynomial.monomial n (PowerSeries.coeff n f.1), ?_⟩
  rw [dist_eq_norm, Restricted.norm_eq, PowerSeries.gaussNorm_eq]
  refine lt_of_le_of_lt (Real.iSup_le (fun n => ?_) (half_pos hε).le) (half_lt_self hε)
  show ‖PowerSeries.coeff n ((f - polyKW K _ :
    PowerSeries.Restricted K (1 : ℝ))).1‖ * (1 : ℝ) ^ n ≤ ε / 2
  rw [one_pow, mul_one,
    show ((f - polyKW K (∑ n ∈ hfin.toFinset,
      Polynomial.monomial n (PowerSeries.coeff n f.1)) :
      PowerSeries.Restricted K (1 : ℝ))).1 =
      f.1 - ((∑ n ∈ hfin.toFinset,
        Polynomial.monomial n (PowerSeries.coeff n f.1) : Polynomial K) :
        PowerSeries K) from rfl,
    map_sub, Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
  by_cases hn : ε / 2 ≤ ‖PowerSeries.coeff n f.1‖
  · rw [Finset.sum_eq_single n
      (fun b _ hb => by rw [Polynomial.coeff_monomial, if_neg hb])
      (fun hnn => absurd (hfin.mem_toFinset.mpr hn) hnn),
      Polynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hn).le
    · rw [Polynomial.coeff_monomial, if_neg]
      intro hbn
      rw [hbn] at hb
      exact hn (hfin.mem_toFinset.mp hb)

/-- The `Q⁰`-constant lift `K⟨X⟩ → 𝓐` (nonnegative Laurent shadows). -/
def constKW : PowerSeries.Restricted K (1 : ℝ) →+* JetA K :=
  ((constHomC K).comp (ofRestricted (R := K))).codRestrict (jetSupport K) (fun f => by
    constructor
    · show qCoeff K 0 (constHomC K (ofRestricted (R := K) f)) ∈ _
      rw [qCoeff_constHomC, if_pos rfl]
      exact (mem_range_ofRestricted_iff K _).mp ⟨f, rfl⟩
    · show qCoeff K 1 (constHomC K (ofRestricted (R := K) f)) ∈ _
      rw [qCoeff_constHomC, if_neg one_ne_zero]
      exact zero_mem _)

theorem constKW_continuous : Continuous (constKW K) :=
  AddMonoidHomClass.continuous_of_bound (constKW K) 1 fun f => by
    rw [one_mul]
    show ‖constHomC K (ofRestricted (R := K) f)‖ ≤ ‖f‖
    rw [norm_constHomC, ofRestricted_norm]

theorem constKW_const (r : K) : constKW K (constHomPS K r) = constA K r := by
  refine Subtype.ext ?_
  show constHomC K (ofRestricted (R := K) (constHomPS K r)) = constC K r
  rw [show ofRestricted (R := K) (constHomPS K r) = single 0 r from ofRestricted_C r]
  rfl

theorem constKW_X : constKW K ((jB K (Wa K)).fst) = Wa K := by
  refine Subtype.ext ?_
  show constHomC K (ofRestricted (R := K) ((jB K (Wa K)).fst)) = ((Wa K : JetA K) : JetC K)
  rw [ofRestricted_jB_Wa_fst, Wa_val_eq]
  rfl

/-- `ρ(W) = ρ(ϖ)·(W/ϖ)` (denominator clearing, standalone form). -/
theorem rho_Wa_split (ϖ : Uniformizer K) :
    (chartDatum K ϖ).canonicalMap (Wa K) =
      (chartDatum K ϖ).canonicalMap (piA ϖ) * gChart K ϖ := by
  show (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
      (Localization.Away (chartDatum K ϖ).s) (Wa K)) =
    (chartDatum K ϖ).coeRingHom (algebraMap (JetA K)
      (Localization.Away (chartDatum K ϖ).s) (piA ϖ)) *
      (chartDatum K ϖ).coeRingHom (divByS (Wa K) (chartDatum K ϖ).s)
  rw [← RingHom.map_mul (chartDatum K ϖ).coeRingHom]
  congr 1
  rw [mul_comm]
  symm
  show divByS (Wa K) (chartDatum K ϖ).s *
    algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (chartDatum K ϖ).s =
    algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) (Wa K)
  rw [divByS, IsLocalization.mk'_spec]

/-- The rescaling scales the disc variable by `ϖ` (fst-component of `thetaChart_Wa`,
standalone form). -/
theorem rescale_jBWa_fst (ϖ : Uniformizer K) :
    rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le ((jB K (Wa K)).fst) =
      constHomPS K ϖ.val * (jB K (Wa K)).fst := by
  refine Subtype.ext ?_
  refine PowerSeries.ext fun n => ?_
  show PowerSeries.coeff n (PowerSeries.rescale ϖ.val ((jB K (Wa K)).fst).1) =
    PowerSeries.coeff n
      ((PowerSeries.C ϖ.val : PowerSeries K) * ((jB K (Wa K)).fst).1)
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_jB_Wa_fst]
  by_cases hn : n = 1
  · subst hn
    rw [if_pos rfl, pow_one]
  · rw [if_neg hn, mul_zero, mul_zero]

/-- `polyKW` sends `X` to the disc variable. -/
theorem polyKW_X : polyKW K Polynomial.X = (jB K (Wa K)).fst := by
  refine Subtype.ext ?_
  refine PowerSeries.ext fun n => ?_
  show PowerSeries.coeff n ((Polynomial.X : Polynomial K) : PowerSeries K) = _
  rw [Polynomial.coeff_coe, coeff_jB_Wa_fst]
  simp [Polynomial.coeff_X, eq_comm]

omit [CompleteSpace K] in
theorem polyKW_C (r : K) : polyKW K (Polynomial.C r) = constHomPS K r := by
  refine Subtype.ext ?_
  show ((Polynomial.C r : Polynomial K) : PowerSeries K) = PowerSeries.C r
  exact Polynomial.coe_C r

/-- **The key evaluation identity (roundtrip step 3)**: evaluating the `ϖ`-rescaled
series recovers the canonical image of the constant lift ([FJP] Prop 3.1's
`ψ ∘ φ`-coherence on the disc component). -/
theorem evalRescale_eq (ϖ : Uniformizer K) (f : PowerSeries.Restricted K (1 : ℝ)) :
    chartEval K ϖ (rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le f) =
    (chartDatum K ϖ).canonicalMap (constKW K f) := by
  haveI : RegularSpace (presheafValue (chartDatum K ϖ)) := UniformSpace.to_regularSpace
  have hrescont : Continuous (rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le) :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun g => by
      rw [one_mul]
      exact norm_rescaleRestricted_le _ _ g
  have hpoly : ((chartEval K ϖ).comp
      ((rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le).comp (polyKW K))) =
      ((chartDatum K ϖ).canonicalMap.comp ((constKW K).comp (polyKW K))) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply]
      rw [polyKW_C, rescaleRestricted_const, chartEval_const, constKW_const]
      rfl
    · simp only [RingHom.comp_apply]
      rw [polyKW_X, rescale_jBWa_fst, map_mul, chartEval_const, chartEval_jBWa_fst,
        constKW_X]
      show chartConst K ϖ ϖ.val * gChart K ϖ =
        (chartDatum K ϖ).canonicalMap (Wa K)
      rw [rho_Wa_split]
      rfl
  have h_eq : (fun g => chartEval K ϖ (rescaleRestricted ϖ.val
      ϖ.norm_val_lt_one.le g)) =
      fun g => (chartDatum K ϖ).canonicalMap (constKW K g) :=
    (polyKW_denseRange K).equalizer
      ((chartEval_continuous K ϖ).comp hrescont)
      ((canonicalMap_continuous (chartDatum K ϖ)).comp (constKW_continuous K))
      (by funext p; exact DFunLike.congr_fun hpoly p)
  exact congrFun h_eq f

/-- The reverse map `φ : 𝓑 → 𝒪_𝓐(chart)`, `(f, g) ↦ φ(f) + φ(g)·Q̄`
(a ring homomorphism because `Q̄² = 0`). -/
def chartRev (ϖ : Uniformizer K) : JetB K →+* presheafValue (chartDatum K ϖ) where
  toFun x := chartEval K ϖ x.fst + chartEval K ϖ x.snd *
    (chartDatum K ϖ).canonicalMap (Qa K)
  map_one' := by
    rw [show (1 : JetB K).fst = 1 from TrivSqZeroExt.fst_one,
      show (1 : JetB K).snd = 0 from TrivSqZeroExt.snd_one,
      map_one, map_zero, zero_mul, add_zero]
  map_zero' := by
    rw [show (0 : JetB K).fst = 0 from TrivSqZeroExt.fst_zero,
      show (0 : JetB K).snd = 0 from TrivSqZeroExt.snd_zero,
      map_zero, zero_mul, add_zero]
  map_add' x y := by
    rw [show (x + y).fst = x.fst + y.fst from TrivSqZeroExt.fst_add x y,
      show (x + y).snd = x.snd + y.snd from TrivSqZeroExt.snd_add x y,
      map_add, map_add]
    ring
  map_mul' x y := by
    rw [show (x * y).fst = x.fst * y.fst from TrivSqZeroExt.fst_mul x y,
      show (x * y).snd = x.fst • y.snd + MulOpposite.op y.fst • x.snd from
        TrivSqZeroExt.snd_mul x y]
    rw [show x.fst • y.snd + MulOpposite.op y.fst • x.snd =
      x.fst * y.snd + y.fst * x.snd from by
        rw [smul_eq_mul, op_smul_eq_mul]
        ring]
    rw [map_mul, map_add, map_mul, map_mul]
    linear_combination
      (-(chartEval K ϖ x.snd * chartEval K ϖ y.snd)) * canonicalMap_Qa_sq K ϖ

/-! ### Roundtrip step 4: `chartRev ∘ θ = ρ` -/

/-- `chartRev` on disc-only jets is the evaluation. -/
theorem chartRev_inl (ϖ : Uniformizer K) (f : PowerSeries.Restricted K (1 : ℝ)) :
    chartRev K ϖ (TrivSqZeroExt.inl f) = chartEval K ϖ f := by
  show chartEval K ϖ (TrivSqZeroExt.inl f : JetB K).fst +
    chartEval K ϖ (TrivSqZeroExt.inl f : JetB K).snd *
      (chartDatum K ϖ).canonicalMap (Qa K) = chartEval K ϖ f
  rw [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, zero_mul, add_zero]

/-- `chartRev` sends the square-zero generator to `Q̄`. -/
theorem chartRev_inr_one (ϖ : Uniformizer K) :
    chartRev K ϖ (TrivSqZeroExt.inr 1) = (chartDatum K ϖ).canonicalMap (Qa K) := by
  show chartEval K ϖ (TrivSqZeroExt.inr 1 : JetB K).fst +
    chartEval K ϖ (TrivSqZeroExt.inr 1 : JetB K).snd *
      (chartDatum K ϖ).canonicalMap (Qa K) = _
  rw [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, map_one, one_mul, zero_add]

/-- The 2-jet of a constant lift is the disc-only constant. -/
theorem jB_constNN (b : L K) (hb : b ∈ nonnegSubring K) :
    jB K (constNN K b hb) = TrivSqZeroExt.inl ((nonnegEquiv (R := K)).symm ⟨b, hb⟩) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine ofRestricted_injective (R := K) ?_
    rw [TrivSqZeroExt.fst_inl]
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 0 ((constNN K b hb : JetA K) : JetC K), (constNN K b hb).2.1⟩) =
      ofRestricted ((nonnegEquiv (R := K)).symm ⟨b, hb⟩)
    rw [ofRestricted_nonnegEquiv_symm, ofRestricted_nonnegEquiv_symm]
    show qCoeff K 0 (constHomC K b) = b
    rw [qCoeff_constHomC, if_pos rfl]
  · refine ofRestricted_injective (R := K) ?_
    rw [TrivSqZeroExt.snd_inl, map_zero]
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 1 ((constNN K b hb : JetA K) : JetC K), (constNN K b hb).2.2⟩) = 0
    rw [ofRestricted_nonnegEquiv_symm]
    show qCoeff K 1 (constHomC K b) = 0
    rw [qCoeff_constHomC, if_neg one_ne_zero]

/-- `θ` on constant lifts is the rescaled disc constant. -/
theorem theta_constNN (ϖ : Uniformizer K) (b : L K) (hb : b ∈ nonnegSubring K) :
    thetaChart K ϖ (constNN K b hb) = TrivSqZeroExt.inl
      (rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le
        ((nonnegEquiv (R := K)).symm ⟨b, hb⟩)) := by
  show twistB K ϖ (jB K (constNN K b hb)) = _
  rw [jB_constNN]
  refine TrivSqZeroExt.ext ?_ ?_
  · rfl
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le 0 = 0
    exact map_zero _

/-- `constKW` inverts the nonnegative-shadow equivalence. -/
theorem constKW_nonnegEquiv_symm (b : L K) (hb : b ∈ nonnegSubring K) :
    constKW K ((nonnegEquiv (R := K)).symm ⟨b, hb⟩) = constNN K b hb := by
  refine Subtype.ext ?_
  show constHomC K (ofRestricted (R := K) ((nonnegEquiv (R := K)).symm ⟨b, hb⟩)) =
    constHomC K b
  rw [ofRestricted_nonnegEquiv_symm]

/-- `chartRev ∘ θ = ρ` on constant lifts. -/
theorem chartRev_theta_constNN (ϖ : Uniformizer K) (b : L K)
    (hb : b ∈ nonnegSubring K) :
    chartRev K ϖ (thetaChart K ϖ (constNN K b hb)) =
      (chartDatum K ϖ).canonicalMap (constNN K b hb) := by
  rw [theta_constNN, chartRev_inl, evalRescale_eq, constKW_nonnegEquiv_symm]

/-- `θ` fixes the square-zero generator. -/
theorem theta_Qa (ϖ : Uniformizer K) :
    thetaChart K ϖ (Qa K) = TrivSqZeroExt.inr 1 := by
  show twistB K ϖ (jB K (Qa K)) = _
  have hjBQ : jB K (Qa K) = TrivSqZeroExt.inr 1 := by
    refine TrivSqZeroExt.ext ?_ ?_
    · refine ofRestricted_injective (R := K) ?_
      rw [TrivSqZeroExt.fst_inr, map_zero]
      show ofRestricted ((nonnegEquiv (R := K)).symm
        ⟨qCoeff K 0 ((Qa K : JetA K) : JetC K), (Qa K).2.1⟩) = 0
      rw [ofRestricted_nonnegEquiv_symm]
      show qCoeff K 0 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 0
      rw [qCoeff_sectionD]
      norm_num
    · refine ofRestricted_injective (R := K) ?_
      rw [TrivSqZeroExt.snd_inr, map_one]
      show ofRestricted ((nonnegEquiv (R := K)).symm
        ⟨qCoeff K 1 ((Qa K : JetA K) : JetC K), (Qa K).2.2⟩) = 1
      rw [ofRestricted_nonnegEquiv_symm]
      show qCoeff K 1 (sectionD K (TrivSqZeroExt.inr (1 : L K))) = 1
      rw [qCoeff_sectionD]
      norm_num
  rw [hjBQ]
  refine TrivSqZeroExt.ext ?_ ?_
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le 0 = 0
    exact map_zero _
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le 1 = 1
    exact map_one _

/-- **Roundtrip step 4**: `chartRev ∘ θ = ρ` ([FJP] Prop 3.1's coherence on 𝓐). -/
theorem chartRev_theta (ϖ : Uniformizer K) (a : JetA K) :
    chartRev K ϖ (thetaChart K ϖ a) = (chartDatum K ϖ).canonicalMap a := by
  obtain ⟨y, ⟨hy0, hy1⟩, hdecomp⟩ := jet_decomposition K a
  have hρy : (chartDatum K ϖ).canonicalMap y = 0 :=
    canonicalMap_eq_zero_of_qSq K ϖ y hy0 hy1
  have hjBy : jB K y = 0 := by
    refine TrivSqZeroExt.ext ?_ ?_
    · refine ofRestricted_injective (R := K) ?_
      rw [TrivSqZeroExt.fst_zero, map_zero]
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 0 ((y : JetA K) : JetC K),
        y.2.1⟩) = 0
      rw [ofRestricted_nonnegEquiv_symm]
      exact hy0
    · refine ofRestricted_injective (R := K) ?_
      rw [TrivSqZeroExt.snd_zero, map_zero]
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 1 ((y : JetA K) : JetC K),
        y.2.2⟩) = 0
      rw [ofRestricted_nonnegEquiv_symm]
      exact hy1
  have hθy : thetaChart K ϖ y = 0 := by
    show twistB K ϖ (jB K y) = 0
    rw [hjBy, map_zero]
  conv_lhs => rw [hdecomp]
  conv_rhs => rw [hdecomp]
  rw [RingHom.map_add (thetaChart K ϖ), RingHom.map_add (chartRev K ϖ), hθy,
    RingHom.map_zero (chartRev K ϖ), add_zero,
    RingHom.map_add (thetaChart K ϖ), RingHom.map_add (chartRev K ϖ),
    RingHom.map_mul (thetaChart K ϖ), RingHom.map_mul (chartRev K ϖ),
    RingHom.map_add ((chartDatum K ϖ).canonicalMap), hρy, add_zero,
    RingHom.map_add ((chartDatum K ϖ).canonicalMap),
    RingHom.map_mul ((chartDatum K ϖ).canonicalMap),
    chartRev_theta_constNN, chartRev_theta_constNN, theta_Qa, chartRev_inr_one]

/-! ### Roundtrip step 5: the two inverses, and the equivalence ([FJP] Prop 3.1) -/

/-- Continuity of the reverse map (componentwise: `fst`/`snd` are `1`-bounded for the
jet sup-norm). -/
theorem chartRev_continuous (ϖ : Uniformizer K) : Continuous (chartRev K ϖ) := by
  have hfst : Continuous (fun x : JetB K => x.fst) :=
    AddMonoidHomClass.continuous_of_bound
      (AddMonoidHom.mk' (fun x : JetB K => x.fst)
        (fun x y => TrivSqZeroExt.fst_add x y)) 1
      (fun x => by
        show ‖x.fst‖ ≤ 1 * ‖x‖
        rw [one_mul, JetNorm.norm_def]
        exact le_max_left _ _)
  have hsnd : Continuous (fun x : JetB K => x.snd) :=
    AddMonoidHomClass.continuous_of_bound
      (AddMonoidHom.mk' (fun x : JetB K => x.snd)
        (fun x y => TrivSqZeroExt.snd_add x y)) 1
      (fun x => by
        show ‖x.snd‖ ≤ 1 * ‖x‖
        rw [one_mul, JetNorm.norm_def]
        exact le_max_right _ _)
  show Continuous (fun x : JetB K => chartEval K ϖ x.fst +
    chartEval K ϖ x.snd * (chartDatum K ϖ).canonicalMap (Qa K))
  exact ((chartEval_continuous K ϖ).comp hfst).add
    (((chartEval_continuous K ϖ).comp hsnd).mul continuous_const)

/-- `chartFwd` intertwines `ρ` and `θ`. -/
theorem chartFwd_canonicalMap (ϖ : Uniformizer K) (a : JetA K) :
    chartFwd K ϖ ((chartDatum K ϖ).canonicalMap a) = thetaChart K ϖ a := by
  show chartFwd K ϖ ((chartDatum K ϖ).coeRingHom
    (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) a)) = thetaChart K ϖ a
  rw [chartFwd_coe, chartLocHom_algebraMap]

/-- **Roundtrip I**: `chartRev ∘ chartFwd = id` (agreement on the dense localization via
`chartRev_theta`, then density). -/
theorem chartRev_chartFwd (ϖ : Uniformizer K) (x : presheafValue (chartDatum K ϖ)) :
    chartRev K ϖ (chartFwd K ϖ x) = x := by
  haveI : RegularSpace (presheafValue (chartDatum K ϖ)) := UniformSpace.to_regularSpace
  have hloc : (chartRev K ϖ).comp (chartLocHom K ϖ) = (chartDatum K ϖ).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (chartDatum K ϖ).s)
      (RingHom.ext fun a => ?_)
    show chartRev K ϖ (chartLocHom K ϖ
      (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) a)) =
      (chartDatum K ϖ).coeRingHom
        (algebraMap (JetA K) (Localization.Away (chartDatum K ϖ).s) a)
    rw [chartLocHom_algebraMap, chartRev_theta]
    rfl
  letI : UniformSpace (Localization.Away (chartDatum K ϖ).s) :=
    (chartDatum K ϖ).uniformSpace
  have hdense : DenseRange ((chartDatum K ϖ).coeRingHom) :=
    UniformSpace.Completion.denseRange_coe (α := Localization.Away (chartDatum K ϖ).s)
  have h_eq : (fun y => chartRev K ϖ (chartFwd K ϖ y)) =
      (fun y : presheafValue (chartDatum K ϖ) => y) := by
    refine hdense.equalizer
      ((chartRev_continuous K ϖ).comp (chartFwd_continuous K ϖ)) continuous_id ?_
    funext a
    show chartRev K ϖ (chartFwd K ϖ ((chartDatum K ϖ).coeRingHom a)) =
      (chartDatum K ϖ).coeRingHom a
    rw [chartFwd_coe]
    exact DFunLike.congr_fun hloc a
  exact congrFun h_eq x

/-- The 2-jet of a disc constant lift is the disc-only jet. -/
theorem jB_constKW (g : PowerSeries.Restricted K (1 : ℝ)) :
    jB K (constKW K g) = TrivSqZeroExt.inl g := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine ofRestricted_injective (R := K) ?_
    rw [TrivSqZeroExt.fst_inl]
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 0 ((constKW K g : JetA K) : JetC K), (constKW K g).2.1⟩) =
      ofRestricted (R := K) g
    rw [ofRestricted_nonnegEquiv_symm]
    show qCoeff K 0 (constHomC K (ofRestricted (R := K) g)) = ofRestricted (R := K) g
    rw [qCoeff_constHomC, if_pos rfl]
  · refine ofRestricted_injective (R := K) ?_
    rw [TrivSqZeroExt.snd_inl, map_zero]
    show ofRestricted ((nonnegEquiv (R := K)).symm
      ⟨qCoeff K 1 ((constKW K g : JetA K) : JetC K), (constKW K g).2.2⟩) = 0
    rw [ofRestricted_nonnegEquiv_symm]
    show qCoeff K 1 (constHomC K (ofRestricted (R := K) g)) = 0
    rw [qCoeff_constHomC, if_neg one_ne_zero]

/-- `θ` on disc constant lifts is the rescaled disc-only jet. -/
theorem theta_constKW (ϖ : Uniformizer K) (g : PowerSeries.Restricted K (1 : ℝ)) :
    thetaChart K ϖ (constKW K g) = TrivSqZeroExt.inl
      (rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le g) := by
  show twistB K ϖ (jB K (constKW K g)) = _
  rw [jB_constKW]
  refine TrivSqZeroExt.ext ?_ ?_
  · rfl
  · show rescaleRestricted ϖ.val ϖ.norm_val_lt_one.le 0 = 0
    exact map_zero _

/-- **Roundtrip II, disc component**: `chartFwd ∘ chartEval = inl` (polynomial density:
constants via `θ`-on-constants, `X ↦ W/ϖ ↦ jB(W)`). -/
theorem chartFwd_chartEval (ϖ : Uniformizer K) (f : PowerSeries.Restricted K (1 : ℝ)) :
    chartFwd K ϖ (chartEval K ϖ f) = TrivSqZeroExt.inl f := by
  have hinl : Continuous (fun g : PowerSeries.Restricted K (1 : ℝ) =>
      (TrivSqZeroExt.inl g : JetB K)) :=
    AddMonoidHomClass.continuous_of_bound
      (AddMonoidHom.mk' (fun g : PowerSeries.Restricted K (1 : ℝ) =>
          (TrivSqZeroExt.inl g : JetB K))
        (fun a b => by
          refine TrivSqZeroExt.ext ?_ ?_
          · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inl,
              TrivSqZeroExt.fst_inl]
          · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl,
              TrivSqZeroExt.snd_inl, add_zero])) 1
      (fun g => by
        show ‖(TrivSqZeroExt.inl g : JetB K)‖ ≤ 1 * ‖g‖
        rw [one_mul, JetNorm.norm_inl])
  have hpoly : ((chartFwd K ϖ).comp ((chartEval K ϖ).comp (polyKW K))) =
      ((TrivSqZeroExt.inlHom (PowerSeries.Restricted K (1 : ℝ))
        (PowerSeries.Restricted K (1 : ℝ))).comp (polyKW K)) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply]
      rw [polyKW_C, chartEval_const]
      show chartFwd K ϖ ((chartDatum K ϖ).canonicalMap (constA K r)) =
        TrivSqZeroExt.inl (constHomPS K r)
      rw [chartFwd_canonicalMap, ← constKW_const, theta_constKW, rescaleRestricted_const]
    · simp only [RingHom.comp_apply]
      rw [polyKW_X, chartEval_jBWa_fst]
      show chartFwd K ϖ ((chartDatum K ϖ).coeRingHom
        (divByS (Wa K) (chartDatum K ϖ).s)) = TrivSqZeroExt.inl ((jB K (Wa K)).fst)
      rw [chartFwd_coe, chartLocHom_divByS_Wa]
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [TrivSqZeroExt.fst_inl]
      · rw [TrivSqZeroExt.snd_inl, jB_Wa_snd]
  have h_eq : (fun g => chartFwd K ϖ (chartEval K ϖ g)) =
      (fun g : PowerSeries.Restricted K (1 : ℝ) => (TrivSqZeroExt.inl g : JetB K)) :=
    (polyKW_denseRange K).equalizer
      ((chartFwd_continuous K ϖ).comp (chartEval_continuous K ϖ)) hinl
      (by funext p; exact DFunLike.congr_fun hpoly p)
  exact congrFun h_eq f

/-- **Roundtrip II**: `chartFwd ∘ chartRev = id`. -/
theorem chartFwd_chartRev (ϖ : Uniformizer K) (x : JetB K) :
    chartFwd K ϖ (chartRev K ϖ x) = x := by
  have hQ : chartFwd K ϖ ((chartDatum K ϖ).canonicalMap (Qa K)) =
      TrivSqZeroExt.inr 1 := by
    rw [chartFwd_canonicalMap, theta_Qa]
  show chartFwd K ϖ (chartEval K ϖ x.fst +
    chartEval K ϖ x.snd * (chartDatum K ϖ).canonicalMap (Qa K)) = x
  rw [RingHom.map_add (chartFwd K ϖ), RingHom.map_mul (chartFwd K ϖ),
    chartFwd_chartEval, chartFwd_chartEval, hQ, TrivSqZeroExt.inl_mul_inr,
    show (x.snd • (1 : PowerSeries.Restricted K (1 : ℝ))) = x.snd from by
      rw [smul_eq_mul, mul_one],
    TrivSqZeroExt.inl_fst_add_inr_snd_eq]

/-- **[FJP] Proposition 3.1** over a general base: the chart is the square-zero disc
algebra, `𝒪_𝓐({|W| ≤ |ϖ|}) ≅ K⟨X⟩[Q]/(Q²) = 𝓑`, as topological rings. -/
def chartEquiv (ϖ : Uniformizer K) : presheafValue (chartDatum K ϖ) ≃+* JetB K :=
  RingEquiv.ofRingHom (chartFwd K ϖ) (chartRev K ϖ)
    (RingHom.ext fun x => chartFwd_chartRev K ϖ x)
    (RingHom.ext fun x => chartRev_chartFwd K ϖ x)

theorem chartEquiv_continuous (ϖ : Uniformizer K) : Continuous (chartEquiv K ϖ) :=
  chartFwd_continuous K ϖ

theorem chartEquiv_symm_continuous (ϖ : Uniformizer K) :
    Continuous (chartEquiv K ϖ).symm :=
  chartRev_continuous K ϖ

/-- The chart equivalence is the canonical one of [FJP] Prop 3.1 ("`W ↦ ϖX`, `Q ↦ Q`"):
it sends `ρ(W)` to `ϖ·jB(W)` (the `ϖ`-scaled disc variable) and `ρ(Q)` to the square-zero
generator `ε`. -/
theorem chartEquiv_canonicalMap_W (ϖ : Uniformizer K) :
    chartEquiv K ϖ ((chartDatum K ϖ).canonicalMap (Wa K)) = piB ϖ * jB K (Wa K) ∧
    chartEquiv K ϖ ((chartDatum K ϖ).canonicalMap (Qa K)) = TrivSqZeroExt.inr 1 := by
  constructor
  · show chartFwd K ϖ ((chartDatum K ϖ).canonicalMap (Wa K)) = _
    rw [chartFwd_canonicalMap, thetaChart_Wa]
  · show chartFwd K ϖ ((chartDatum K ϖ).canonicalMap (Qa K)) = _
    rw [chartFwd_canonicalMap, theta_Qa]

/-! ### Failure of stable uniformity ([FJP] Corollary 3.2) -/

/-- The chart is not uniform ([FJP] Cor 3.2, via K8b's `not_isUniform_JetB` and the
generic uniformity transport `FiniteJet.isUniform_of_ringEquiv`). -/
theorem not_isUniform_chart (ϖ : Uniformizer K) :
    ¬ TopologicalRing.IsUniform (presheafValue (chartDatum K ϖ)) := fun h =>
  not_isUniform_JetB ϖ
    (isUniform_of_ringEquiv (chartEquiv K ϖ) (chartEquiv_continuous K ϖ)
      (chartEquiv_symm_continuous K ϖ) h)

/-- **[FJP] Corollary 3.2** over a general base: 𝓐 is not stably uniform. The Huber
structure of `𝓐` is taken as an instance hypothesis (any witness — e.g.
`isHuberRing_JetA ϖ`; the class is a `Prop`, so the statement does not depend on the
choice). -/
theorem not_isStablyUniform_JetA (ϖ : Uniformizer K) [IsHuberRing (JetA K)] :
    ¬ TopologicalRing.IsStablyUniform (JetA K) := fun h =>
  not_isUniform_chart K ϖ
    ⟨h.presheafValue_isUniform (chartDatum K ϖ) (chartDatum_isRational K ϖ)⟩

end

end FiniteJetOver
