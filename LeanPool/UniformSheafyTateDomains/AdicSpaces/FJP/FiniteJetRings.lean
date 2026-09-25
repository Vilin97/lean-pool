/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedLaurent
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.JetDualNumberNorm
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExampleUnitDisc

/-!
# The finite-jet pinching square: the rings 𝓐, 𝓑, 𝓒, 𝓓 and the strict Milnor row

Source: [FJP] §1.4–§2 over the base field `K := LaurentSeries F` (complete, discretely
valued — the project's standard witness field). Following [FJP] (1.4):

* `L  = K⟨W, W⁻¹⟩` — `RestrictedLaurent K` (file `RestrictedLaurent.lean`);
* `𝓑 = K⟨W, Q⟩/(Q²)` — realised norm-faithfully as `DualNumber (K⟨W⟩)` (max norm,
  [FJP] Lemma 2.2's quotient-norm computation is definitional in this model);
* `𝓒 = L⟨Q⟩` — `PowerSeries.Restricted (L F) 1` (vendored Gauss stack over base `L`);
* `𝓓 = L⟨Q⟩/(Q²)` — `DualNumber (L F)`;
* `𝓐 = 𝓑 ×_𝓓 𝓒` — **not** a new type: by [FJP] Lemma 2.2 ("Projection to 𝒞 is an isometric
  embedding of 𝒜 with image (1.7)"), 𝓐 is the closed subring of 𝓒 of series whose `Q⁰`- and
  `Q¹`-coefficients have nonnegative `W`-support ([FJP] (1.8): support
  `S = {(a,b) ∈ ℤ × ℕ : b ≤ 1 ⇒ a ≥ 0}`).

The maps ([FJP] (1.5), (5.1)): `ρB : 𝓑 → 𝓓` (componentwise `K⟨W⟩ ↪ L`), `ρC : 𝓒 → 𝓓`
(2-jet truncation, with the norm-one linear section `f₀ + Qf₁ ↦ f₀ + Qf₁`), `ιC : 𝓐 ↪ 𝓒`,
`jB : 𝓐 → 𝓑`. The strict Milnor row ([FJP] Prop 2.1, (2.1b)):
`0 → 𝓐 → 𝓑 ⊕ 𝓒 → 𝓓 → 0` is exact with **all norm constants 1**.

This file also builds the Huber-theoretic instance stack for each ring (pair of definition,
`IsTateRing`, maximal plus ring, `IsRingOfIntegralElements`, completeness w.r.t. the right
uniformity) in the pattern of `ExampleUnitDisc.lean`.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace FiniteJet

open RestrictedLaurent

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The four rings -/

/-- `L = K⟨W,W⁻¹⟩`, the radius-one Laurent algebra over `K` ([FJP] (1.4)). -/
abbrev L : Type _ := RestrictedLaurent K

/-- The discrete value group of `K`: every nonzero norm is an integer power of `2`
(the `RankOne` normalisation of `ExampleUnitDisc.lean`). -/
theorem norm_K_discrete : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = (2 : ℝ) ^ n := by
  intro x hx
  have hvx : Valued.v.restrict x ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff]
    exact fun h => hx ((Valuation.zero_iff _).mp h)
  have hne : (MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x) :
      WithZero (Multiplicative ℤ)) ≠ 0 :=
    fun h => hvx (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
      (h.trans (map_zero _).symm))
  refine ⟨Multiplicative.toAdd (WithZero.unzero hne), ?_⟩
  rw [Valued.toNormedField.norm_def]
  show ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0))
    ((MonoidWithZeroHom.ValueGroup₀.embedding) (Valued.v.restrict x)) : ℝ) = _
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  push_cast
  norm_num

/-- `𝓒 = L⟨Q⟩` ([FJP] (1.4)). -/
abbrev JetC : Type _ := PowerSeries.Restricted (L F) (1 : ℝ)

/-- `𝓑 = K⟨W,Q⟩/(Q²)`, modelled as dual numbers over `K⟨W⟩` ([FJP] (1.4) with
Lemma 2.2's isometric max-norm decomposition `k⟨W⟩ ⊕ Q·k⟨W⟩`). -/
abbrev JetB : Type _ := DualNumber (PowerSeries.Restricted K (1 : ℝ))

/-- `𝓓 = L⟨Q⟩/(Q²)`, modelled as dual numbers over `L` ([FJP] (1.4), (2.1d):
`𝓓 = L ⊕ QL` with max norm). -/
abbrev JetD : Type _ := DualNumber (L F)

/-! ### The comparison maps of the square ([FJP] (1.5), (5.1)) -/

/-- The `Q`-coefficient of index `n` of an element of `𝓒`. -/
noncomputable def qCoeff (n : ℕ) (f : JetC F) : L F := PowerSeries.coeff n f.1

theorem qCoeff_zero_mul (f g : JetC F) :
    qCoeff F 0 (f * g) = qCoeff F 0 f * qCoeff F 0 g := by
  show PowerSeries.coeff 0 (f * g : JetC F).1 = _
  rw [show (f * g : JetC F).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul]
  simp [qCoeff]

theorem qCoeff_one_mul (f g : JetC F) :
    qCoeff F 1 (f * g) = qCoeff F 0 f * qCoeff F 1 g + qCoeff F 1 f * qCoeff F 0 g := by
  show PowerSeries.coeff 1 (f * g : JetC F).1 = _
  rw [show (f * g : JetC F).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul,
    show Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  rfl

theorem qCoeff_add (f g : JetC F) (n : ℕ) :
    qCoeff F n (f + g) = qCoeff F n f + qCoeff F n g := by
  show PowerSeries.coeff n (f + g : JetC F).1 = _
  rw [show (f + g : JetC F).1 = f.1 + g.1 from rfl, map_add]
  rfl

theorem qCoeff_neg (f : JetC F) (n : ℕ) : qCoeff F n (-f) = -qCoeff F n f := by
  show PowerSeries.coeff n (-f : JetC F).1 = _
  rw [show (-f : JetC F).1 = -f.1 from rfl, map_neg]
  rfl

theorem qCoeff_one (n : ℕ) : qCoeff F n 1 = if n = 0 then 1 else 0 := by
  show PowerSeries.coeff n (1 : JetC F).1 = _
  rw [show (1 : JetC F).1 = 1 from rfl, PowerSeries.coeff_one]

theorem qCoeff_zero (n : ℕ) : qCoeff F n 0 = 0 := by
  show PowerSeries.coeff n (0 : JetC F).1 = _
  rw [show (0 : JetC F).1 = 0 from rfl, map_zero]

/-- Coefficient functionals of `𝒞` are `1`-Lipschitz, hence continuous. -/
theorem continuous_qCoeff (n : ℕ) : Continuous (qCoeff F n) := by
  have hlip : LipschitzWith 1 (qCoeff F n) := LipschitzWith.of_dist_le_mul fun f g => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : qCoeff F n f - qCoeff F n g = qCoeff F n (f - g) := by
      rw [show f - g = f + -g from sub_eq_add_neg f g, qCoeff_add, qCoeff_neg,
        sub_eq_add_neg]
    rw [hsub]
    have h := PowerSeries.le_gaussNorm norm 1 (f - g).1
      (Restricted.hasGaussNorm (R := L F) 1 (f - g)) n
    rwa [one_pow, mul_one] at h
  exact hlip.continuous

/-- `ρC : 𝓒 → 𝓓`, reduction modulo `Q²` = 2-jet truncation ([FJP] (1.5): "the second is
reduction modulo `Q²`"). -/
noncomputable def rhoC : JetC F →+* JetD F where
  toFun f := ⟨qCoeff F 0 f, qCoeff F 1 f⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (1 : JetC F).1 = (1 : JetD F).fst
      rw [show (1 : JetC F).1 = 1 from rfl, TrivSqZeroExt.fst_one, PowerSeries.coeff_zero_one]
    · show PowerSeries.coeff 1 (1 : JetC F).1 = (1 : JetD F).snd
      rw [show (1 : JetC F).1 = 1 from rfl, TrivSqZeroExt.snd_one, PowerSeries.coeff_one,
        if_neg one_ne_zero]
  map_mul' f g := by
    -- v4.33: rewriting `(f * g).1 = f.1 * g.1` into the goal leaves `Subtype.val`
    -- projections that type only after unfolding the `JetC` def, and `kabstract`
    -- rejects the follow-up rewrites; both components are exactly the proven
    -- `qCoeff`-multiplication lemmas (the `TrivSqZeroExt` structure is defeq).
    refine TrivSqZeroExt.ext ?_ ?_
    · show qCoeff F 0 (f * g) = qCoeff F 0 f * qCoeff F 0 g
      exact qCoeff_zero_mul F f g
    · show qCoeff F 1 (f * g) = qCoeff F 0 f * qCoeff F 1 g + qCoeff F 1 f * qCoeff F 0 g
      exact qCoeff_one_mul F f g
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (0 : JetC F).1 = (0 : JetD F).fst
      rw [show (0 : JetC F).1 = 0 from rfl, TrivSqZeroExt.fst_zero, map_zero]
    · show PowerSeries.coeff 1 (0 : JetC F).1 = (0 : JetD F).snd
      rw [show (0 : JetC F).1 = 0 from rfl, TrivSqZeroExt.snd_zero, map_zero]
  map_add' f g := by
    -- v4.33: same `kabstract`/`JetC`-projection issue as `map_mul'`; both components
    -- are the proven `qCoeff_add` (the `TrivSqZeroExt` addition is componentwise-defeq).
    refine TrivSqZeroExt.ext ?_ ?_
    · show qCoeff F 0 (f + g) = qCoeff F 0 f + qCoeff F 0 g
      exact qCoeff_add F f g 0
    · show qCoeff F 1 (f + g) = qCoeff F 1 f + qCoeff F 1 g
      exact qCoeff_add F f g 1

/-- `ρB : 𝓑 → 𝓓`, componentwise restriction from the disc to the annulus ([FJP] (1.5):
"the first is restriction from the `W`-disc to its radius-one boundary"). -/
noncomputable def rhoB : JetB F →+* JetD F :=
  JetNorm.mapHom (ofRestricted (R := K))

/-- The norm-one linear truncation section `𝓓 → 𝓒`, `f₀ + Qf₁ ↦ f₀ + Qf₁`
([FJP] Prop 2.1: "Reduction modulo `Q²` has the norm-preserving linear section
`f₀ + Qf₁ ↦ f₀ + Qf₁`"). -/
noncomputable def sectionD (x : JetD F) : JetC F :=
  ⟨PowerSeries.mk fun n => if n = 0 then x.fst else if n = 1 then x.snd else 0, by
    show PowerSeries.IsRestricted (1 : ℝ) _
    rw [Restricted.isRestricted_iff_cofinite]
    simp only [PowerSeries.coeff_mk, one_pow, mul_one]
    refine tendsto_nhds_of_eventually_eq ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_singleton 0).union (Set.finite_singleton 1)).subset fun n hn => ?_
    rw [Set.mem_setOf_eq] at hn
    by_contra hmem
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hmem
    exact hn (by rw [if_neg hmem.1, if_neg hmem.2, norm_zero])⟩

theorem qCoeff_sectionD (x : JetD F) (n : ℕ) :
    qCoeff F n (sectionD F x) = if n = 0 then x.fst else if n = 1 then x.snd else 0 := by
  show PowerSeries.coeff n (PowerSeries.mk fun m =>
    if m = 0 then x.fst else if m = 1 then x.snd else 0) = _
  rw [PowerSeries.coeff_mk]

@[simp] theorem rhoC_sectionD (x : JetD F) : rhoC F (sectionD F x) = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show qCoeff F 0 (sectionD F x) = x.fst
    rw [qCoeff_sectionD, if_pos rfl]
  · show qCoeff F 1 (sectionD F x) = x.snd
    rw [qCoeff_sectionD, if_neg one_ne_zero, if_pos rfl]

theorem sectionD_add (x y : JetD F) : sectionD F (x + y) = sectionD F x + sectionD F y := by
  apply Subtype.ext
  ext n
  rw [show PowerSeries.coeff n (sectionD F (x + y)).1 =
      qCoeff F n (sectionD F (x + y)) from rfl, qCoeff_sectionD,
    show (sectionD F x + sectionD F y).1 = (sectionD F x).1 + (sectionD F y).1 from rfl,
    map_add,
    show PowerSeries.coeff n (sectionD F x).1 = qCoeff F n (sectionD F x) from rfl,
    show PowerSeries.coeff n (sectionD F y).1 = qCoeff F n (sectionD F y) from rfl,
    qCoeff_sectionD, qCoeff_sectionD]
  rcases eq_or_ne n 0 with rfl | h0
  · simp [TrivSqZeroExt.fst_add]
  · rw [if_neg h0, if_neg h0, if_neg h0]
    rcases eq_or_ne n 1 with rfl | h1
    · simp [TrivSqZeroExt.snd_add]
    · rw [if_neg h1, if_neg h1, if_neg h1, add_zero]

theorem norm_sectionD (x : JetD F) : ‖sectionD F x‖ = ‖x‖ := by
  rw [Restricted.norm_eq, JetNorm.norm_def]
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n => ?_) (le_max_of_le_left (norm_nonneg _))
    rw [one_pow, mul_one]
    show ‖PowerSeries.coeff n (sectionD F x).1‖ ≤ _
    rw [show PowerSeries.coeff n (sectionD F x).1 = qCoeff F n (sectionD F x) from rfl,
      qCoeff_sectionD]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_pos rfl]; exact le_max_left _ _
    · rw [if_neg h0]
      rcases eq_or_ne n 1 with rfl | h1
      · rw [if_pos rfl]; exact le_max_right _ _
      · rw [if_neg h1, norm_zero]
        exact le_max_of_le_left (norm_nonneg _)
  · refine max_le ?_ ?_
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD F x).1
        (Restricted.hasGaussNorm (R := L F) 1 (sectionD F x)) 0
      rw [one_pow, mul_one, show PowerSeries.coeff 0 (sectionD F x).1 =
        qCoeff F 0 (sectionD F x) from rfl, qCoeff_sectionD, if_pos rfl] at h
      exact h
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD F x).1
        (Restricted.hasGaussNorm (R := L F) 1 (sectionD F x)) 1
      rw [one_pow, mul_one, show PowerSeries.coeff 1 (sectionD F x).1 =
        qCoeff F 1 (sectionD F x) from rfl, qCoeff_sectionD, if_neg one_ne_zero,
        if_pos rfl] at h
      exact h

/-- `ρC` is norm-nonincreasing. -/
theorem norm_rhoC_le (f : JetC F) : ‖rhoC F f‖ ≤ ‖f‖ := by
  rw [JetNorm.norm_def]
  refine max_le ?_ ?_
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L F) 1 f) 0
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L F) 1 f) 1
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)

/-- `ρB` is an isometry (componentwise `ofRestricted` is norm-preserving). -/
theorem norm_rhoB (b : JetB F) : ‖rhoB F b‖ = ‖b‖ :=
  JetNorm.norm_mapHom _ (fun a => ofRestricted_norm a) b

theorem rhoB_injective : Function.Injective (rhoB F) :=
  JetNorm.mapHom_injective _ (ofRestricted_injective (R := K))

/-- `ρC` is surjective ([FJP] Prop 2.1: `𝒞 → 𝒟` is a strict surjection). -/
theorem rhoC_surjective : Function.Surjective (rhoC F) :=
  fun x => ⟨sectionD F x, rhoC_sectionD F x⟩

/-! ### The pinching algebra 𝓐 ([FJP] Definition 1.2 via Lemma 2.2 / (1.7) / (1.8)) -/

/-- The support subring: elements of `𝒞` whose `Q⁰`- and `Q¹`-coefficients lie in the
nonnegative-support subring `K⟨W⟩ ⊂ L` — [FJP] (1.7):
`𝒜 = {f₀(W) + Qf₁(W) + Q²h : f₀, f₁ ∈ k⟨W⟩, h ∈ L⟨Q⟩}`. -/
noncomputable def jetSupport : Subring (JetC F) where
  carrier := {f | qCoeff F 0 f ∈ nonnegSubring K ∧ qCoeff F 1 f ∈ nonnegSubring K}
  zero_mem' := by
    constructor <;> rw [qCoeff_zero] <;> exact zero_mem _
  one_mem' := by
    constructor <;> rw [qCoeff_one]
    · rw [if_pos rfl]; exact one_mem _
    · rw [if_neg one_ne_zero]; exact zero_mem _
  add_mem' := fun {f g} hf hg => by
    constructor <;> rw [qCoeff_add]
    · exact add_mem hf.1 hg.1
    · exact add_mem hf.2 hg.2
  neg_mem' := fun {f} hf => by
    constructor <;> rw [qCoeff_neg]
    · exact neg_mem hf.1
    · exact neg_mem hf.2
  mul_mem' := fun {f g} hf hg => by
    constructor
    · rw [qCoeff_zero_mul]
      exact mul_mem hf.1 hg.1
    · rw [qCoeff_one_mul]
      exact add_mem (mul_mem hf.1 hg.2) (mul_mem hf.2 hg.1)

/-- `𝓐`, the finite-jet pinching algebra ([FJP] Definition 1.2), realised as the support
subring of `𝒞` with the restricted norm ([FJP] Lemma 2.2). -/
abbrev JetA : Type _ := ↥(jetSupport F)

/-- The support subring is closed in `𝒞` ([FJP] Lemma 2.2: "Imposing the preceding closed
condition on the `Q⁰`- and `Q¹`-coefficients therefore cuts out a closed subspace of 𝒞"). -/
theorem isClosed_jetSupport : IsClosed ((jetSupport F : Set (JetC F))) := by
  have heq : (jetSupport F : Set (JetC F)) =
      (qCoeff F 0) ⁻¹' (nonnegSubring K : Set (L F)) ∩
      (qCoeff F 1) ⁻¹' (nonnegSubring K : Set (L F)) := rfl
  rw [heq]
  exact ((isClosed_nonnegSubring (R := K)).preimage (continuous_qCoeff F 0)).inter
    ((isClosed_nonnegSubring (R := K)).preimage (continuous_qCoeff F 1))

/-- `𝓐` inherits `NormedCommRing` and `IsUltrametricDist` from `𝒞` through the mathlib
`SubringClass` instances (the norm is the restriction — [FJP] Lemma 2.2's isometry is
definitional). Completeness holds because the subring is closed. -/
instance : CompleteSpace (JetA F) := (isClosed_jetSupport F).completeSpace_coe

/-- The inclusion `ιC : 𝓐 → 𝓒` (an isometry by construction; [FJP] Lemma 2.2). -/
noncomputable def iotaC : JetA F →+* JetC F := (jetSupport F).subtype

@[simp] theorem norm_iotaC (a : JetA F) : ‖iotaC F a‖ = ‖a‖ := rfl

/-- `jB : 𝓐 → 𝓑`, the 2-jet of an element of 𝓐, with coefficients in `K⟨W⟩`
([FJP] (5.1): `ι_B : 𝒜 → ℬ`). -/
noncomputable def jB : JetA F →+* JetB F where
  toFun a :=
    ⟨(nonnegEquiv (R := K)).symm ⟨qCoeff F 0 (a : JetC F), a.2.1⟩,
     (nonnegEquiv (R := K)).symm ⟨qCoeff F 1 (a : JetC F), a.2.2⟩⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 0 ((1 : JetA F) : JetC F) = ((1 : nonnegSubring K) : L F)
        rw [show ((1 : JetA F) : JetC F) = 1 from rfl, qCoeff_one, if_pos rfl]
        rfl))).trans (map_one _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 1 ((1 : JetA F) : JetC F) = ((0 : nonnegSubring K) : L F)
        rw [show ((1 : JetA F) : JetC F) = 1 from rfl, qCoeff_one, if_neg one_ne_zero]
        rfl))).trans (map_zero _)
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 0 ((a * b : JetA F) : JetC F) = _
        rw [show ((a * b : JetA F) : JetC F) = (a : JetC F) * (b : JetC F) from rfl,
          qCoeff_zero_mul]
        rfl))).trans (map_mul _ _ _)
    · have hval : (⟨qCoeff F 1 ((a * b : JetA F) : JetC F), (a * b).2.2⟩ :
          nonnegSubring K) =
          ⟨qCoeff F 0 (a : JetC F), a.2.1⟩ * ⟨qCoeff F 1 (b : JetC F), b.2.2⟩ +
          ⟨qCoeff F 1 (a : JetC F), a.2.2⟩ * ⟨qCoeff F 0 (b : JetC F), b.2.1⟩ := by
        refine Subtype.ext ?_
        show qCoeff F 1 ((a * b : JetA F) : JetC F) = _
        rw [show ((a * b : JetA F) : JetC F) = (a : JetC F) * (b : JetC F) from rfl,
          qCoeff_one_mul]
        rfl
      exact (congrArg (nonnegEquiv (R := K)).symm hval).trans (by
        rw [map_add (nonnegEquiv (R := K)).symm, map_mul (nonnegEquiv (R := K)).symm,
          map_mul (nonnegEquiv (R := K)).symm]
        rfl)
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 0 ((0 : JetA F) : JetC F) = ((0 : nonnegSubring K) : L F)
        rw [show ((0 : JetA F) : JetC F) = 0 from rfl, qCoeff_zero]
        rfl))).trans (map_zero _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 1 ((0 : JetA F) : JetC F) = ((0 : nonnegSubring K) : L F)
        rw [show ((0 : JetA F) : JetC F) = 0 from rfl, qCoeff_zero]
        rfl))).trans (map_zero _)
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 0 ((a + b : JetA F) : JetC F) = _
        rw [show ((a + b : JetA F) : JetC F) = (a : JetC F) + (b : JetC F) from rfl,
          qCoeff_add]
        rfl))).trans (map_add _ _ _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff F 1 ((a + b : JetA F) : JetC F) = _
        rw [show ((a + b : JetA F) : JetC F) = (a : JetC F) + (b : JetC F) from rfl,
          qCoeff_add]
        rfl))).trans (map_add _ _ _)

theorem norm_nonnegEquiv_symm (x : nonnegSubring K) :
    ‖(nonnegEquiv (R := K)).symm x‖ = ‖(x : L F)‖ := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (nonnegEquiv (R := K)) x]
  exact (nonnegEquiv_norm _).symm

theorem norm_qCoeff_le (f : JetC F) (n : ℕ) : ‖qCoeff F n f‖ ≤ ‖f‖ := by
  have h := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm (R := L F) 1 f) n
  rwa [one_pow, mul_one] at h

theorem norm_jB_le (a : JetA F) : ‖jB F a‖ ≤ ‖a‖ := by
  rw [JetNorm.norm_def]
  refine max_le ?_ ?_
  · show ‖(nonnegEquiv (R := K)).symm _‖ ≤ _
    rw [norm_nonnegEquiv_symm]
    exact norm_qCoeff_le F _ 0
  · show ‖(nonnegEquiv (R := K)).symm _‖ ≤ _
    rw [norm_nonnegEquiv_symm]
    exact norm_qCoeff_le F _ 1

/-! ### The strict Milnor row ([FJP] Prop 2.1, Lemma 2.2, (2.1b))

`0 → 𝓐 →(jB, ιC) 𝓑 ⊕ 𝓒 →(ρB − ρC) 𝓓 → 0` is exact with all constants 1:
* the square commutes on 𝓐,
* an element of 𝓒 lies in 𝓐 iff its 2-jet comes from 𝓑,
* the difference map is strictly surjective via the norm-one section,
* the pullback (max) norm of `(jB a, ιC a)` equals `‖a‖` ([FJP] Lemma 2.2:
  "the maximum pullback norm of `(b, c)` equals `‖c‖_𝒞`"). -/

theorem square_commutes (a : JetA F) : rhoB F (jB F a) = rhoC F (iotaC F a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 0 (a : JetC F), a.2.1⟩) = _
    rw [ofRestricted_nonnegEquiv_symm]
    rfl
  · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 1 (a : JetC F), a.2.2⟩) = _
    rw [ofRestricted_nonnegEquiv_symm]
    rfl

theorem mem_range_ofRestricted_iff (x : L F) :
    x ∈ Set.range (ofRestricted (R := K)) ↔ x ∈ nonnegSubring K := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ((nonnegEquiv (R := K)) y).2
  · intro hx
    exact ⟨(nonnegEquiv (R := K)).symm ⟨x, hx⟩, by
      rw [ofRestricted_nonnegEquiv_symm]⟩

/-- Cartesianness, membership form: `c ∈ 𝓐 ↔ ρC c ∈ range ρB` ([FJP] (1.6)/(1.7)). -/
theorem mem_jetSupport_iff_jet_in_range (c : JetC F) :
    c ∈ jetSupport F ↔ rhoC F c ∈ Set.range (rhoB F) := by
  constructor
  · intro hc
    refine ⟨⟨(nonnegEquiv (R := K)).symm ⟨qCoeff F 0 c, hc.1⟩,
      (nonnegEquiv (R := K)).symm ⟨qCoeff F 1 c, hc.2⟩⟩, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 0 c, hc.1⟩) = _
      rw [ofRestricted_nonnegEquiv_symm]
      rfl
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 1 c, hc.2⟩) = _
      rw [ofRestricted_nonnegEquiv_symm]
      rfl
  · rintro ⟨b, hb⟩
    constructor
    · rw [← mem_range_ofRestricted_iff]
      refine ⟨b.fst, ?_⟩
      have := congrArg TrivSqZeroExt.fst hb
      exact this
    · rw [← mem_range_ofRestricted_iff]
      refine ⟨b.snd, ?_⟩
      have := congrArg TrivSqZeroExt.snd hb
      exact this

/-- Exactness in the middle with uniqueness: a compatible pair `(b, c)` comes from a unique
element of 𝓐 ([FJP] Prop 2.1: "Its kernel is the algebraic pullback (1.6)"). -/
theorem milnorRow_exact (b : JetB F) (c : JetC F) (h : rhoB F b = rhoC F c) :
    ∃! a : JetA F, jB F a = b ∧ iotaC F a = c := by
  have hmem : c ∈ jetSupport F :=
    (mem_jetSupport_iff_jet_in_range F c).mpr ⟨b, h⟩
  refine ⟨⟨c, hmem⟩, ⟨?_, rfl⟩, ?_⟩
  · -- `jB ⟨c, _⟩ = b`, componentwise via injectivity of `ofRestricted`
    refine TrivSqZeroExt.ext ?_ ?_
    · refine ofRestricted_injective (R := K) ?_
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 0 c, hmem.1⟩) =
        ofRestricted b.fst
      rw [ofRestricted_nonnegEquiv_symm]
      exact (congrArg TrivSqZeroExt.fst h).symm
    · refine ofRestricted_injective (R := K) ?_
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff F 1 c, hmem.2⟩) =
        ofRestricted b.snd
      rw [ofRestricted_nonnegEquiv_symm]
      exact (congrArg TrivSqZeroExt.snd h).symm
  · rintro a ⟨-, rfl⟩
    rfl

/-- The pullback norm identity ([FJP] Lemma 2.2): for `a ∈ 𝓐`,
`max ‖jB a‖ ‖ιC a‖ = ‖a‖`. -/
theorem max_norm_eq (a : JetA F) : max ‖jB F a‖ ‖iotaC F a‖ = ‖a‖ := by
  rw [norm_iotaC]
  exact max_eq_right (norm_jB_le F a)

/-- Strict surjectivity of the difference map with constant 1 ([FJP] Prop 2.1 and (2.1b):
"the two denominator losses in the defining square are zero"). -/
theorem difference_strict_surjective (d : JetD F) :
    ∃ c : JetC F, rhoC F c = d ∧ ‖c‖ = ‖d‖ :=
  ⟨sectionD F d, rhoC_sectionD F d, norm_sectionD F d⟩

/-! ### Pseudouniformizers and scalar embeddings -/

/-- Constants of `𝒞` over the base `L`, as a ring homomorphism. -/
noncomputable def constHomC : L F →+* JetC F where
  toFun x := PowerSeries.Restricted.C (1 : ℝ) x
  map_one' := Subtype.ext (map_one PowerSeries.C)
  map_mul' x y := Subtype.ext (map_mul PowerSeries.C x y)
  map_zero' := Subtype.ext (map_zero PowerSeries.C)
  map_add' x y := Subtype.ext (map_add PowerSeries.C x y)

theorem norm_constHomC (x : L F) : ‖constHomC F x‖ = ‖x‖ := norm_restrictedC x

theorem qCoeff_constHomC (x : L F) (n : ℕ) :
    qCoeff F n (constHomC F x) = if n = 0 then x else 0 := by
  show PowerSeries.coeff n (PowerSeries.C x) = _
  rw [PowerSeries.coeff_C]

/-- The constant embedding `K →+* 𝒞` (through `RestrictedLaurent.C` and the power-series
constants). -/
noncomputable def constC : K →+* JetC F :=
  (constHomC F).comp (RestrictedLaurent.C (R := K))

theorem norm_constC (a : K) : ‖constC F a‖ = ‖a‖ := by
  show ‖constHomC F (RestrictedLaurent.C a)‖ = ‖a‖
  rw [norm_constHomC]
  show ‖single 0 a‖ = ‖a‖
  rw [norm_single]

/-- The constants land in 𝓐 (support `(0,0)`). -/
theorem constC_mem_jetSupport (a : K) : constC F a ∈ jetSupport F := by
  constructor
  · show qCoeff F 0 (constHomC F (RestrictedLaurent.C a)) ∈ _
    rw [qCoeff_constHomC, if_pos rfl]
    intro b hb
    show (if b = 0 then a else 0) = 0
    rw [if_neg (by omega)]
  · show qCoeff F 1 (constHomC F (RestrictedLaurent.C a)) ∈ _
    rw [qCoeff_constHomC, if_neg one_ne_zero]
    exact zero_mem _

/-- The constant embedding `K →+* 𝓐`. -/
noncomputable def constA : K →+* JetA F :=
  (constC F).codRestrict (jetSupport F) (constC_mem_jetSupport F)

theorem norm_constA (a : K) : ‖constA F a‖ = ‖a‖ := norm_constC F a

/-- The pseudouniformizer `ϖ` of each jet ring: the image of `t ∈ K`. -/
noncomputable def tA : JetA F := constA F (LaurentSeriesExample.t F)

theorem norm_t_lt_one : ‖LaurentSeriesExample.t F‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, LaurentSeriesExample.valuation_t,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem norm_t_pos : 0 < ‖LaurentSeriesExample.t F‖ :=
  norm_pos_iff.mpr (LaurentSeriesExample.t_ne_zero F)

theorem norm_tA_lt_one : ‖tA F‖ < 1 := by
  rw [tA, norm_constA]
  exact norm_t_lt_one F

theorem norm_tA_pos : 0 < ‖tA F‖ := by
  rw [tA, norm_constA]
  exact norm_t_pos F

theorem isUnit_tA : IsUnit (tA F) := by
  refine IsUnit.map (constA F) ?_
  exact (LaurentSeriesExample.t_ne_zero F).isUnit

/-! ### Huber instance stacks (pattern of `ExampleUnitDisc.lean`)

Each of 𝓐, 𝓑, 𝓒, 𝓓 is a complete Tate ring; the chosen plus ring is the **maximal** one,
the full power-bounded subring ([FJP] §5 (5.2) and the sentence before it: "Give every ring
its maximal plus ring of power-bounded elements"). For 𝓑 and 𝓓 this subring is *unbounded*
([FJP] (2.1d): "the summand `kQ` is an unbounded line. These two rings are valid maximal
plus rings"), which `IsRingOfIntegralElements` permits (no boundedness field). -/

section InstanceStack

variable (E : Type*) [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]

/-- The closed unit ball of a nonarchimedean normed ring, as a subring.
(Signature fix during T108: `NormOneClass` added — `1` does not lie in the unit ball of an
arbitrary normed ring; all four jet rings satisfy it.) -/
noncomputable def unitBall : Subring E where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := norm_one.le
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rwa [norm_neg]
  mul_mem' := fun {a b} ha hb =>
    (norm_mul_le a b).trans (mul_le_one₀ ha (norm_nonneg b) hb)

theorem mem_unitBall_iff (x : E) : x ∈ unitBall E ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem isOpen_unitBall : IsOpen ((unitBall E : Set E)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Metric.mem_nhds_iff]
  refine ⟨1, one_pos, fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hy
  show ‖y‖ ≤ 1
  calc ‖y‖ = ‖(y - x) + x‖ := by ring_nf
    _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le hy.le hx

variable {E}

/-- Powers of a scaling element scale norms. -/
theorem norm_pow_mul_of_scale {t : E} (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) (n : ℕ)
    (x : E) : ‖t ^ n * x‖ = ‖t‖ ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, mul_comm (t ^ m) t, mul_assoc, hscale, ih]
    ring

/-- Membership in powers of the principal `t`-ideal of the unit ball is a norm bound. -/
theorem mem_span_unitBall_pow_iff {t : E} (htu : IsUnit t) (ht1 : ‖t‖ ≤ 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (x : unitBall E) (n : ℕ) :
    x ∈ (Ideal.span {(⟨t, ht1⟩ : unitBall E)}) ^ n ↔ ‖(x : E)‖ ≤ ‖t‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    have hcoe : (c : E) * t ^ n = (x : E) := congrArg Subtype.val hc
    rw [← hcoe, mul_comm, norm_pow_mul_of_scale hscale]
    calc ‖t‖ ^ n * ‖(c : E)‖ ≤ ‖t‖ ^ n * 1 :=
          mul_le_mul_of_nonneg_left c.2 (by positivity)
      _ = ‖t‖ ^ n := mul_one _
  · intro hx
    set y : E := ((htu.unit⁻¹ : Eˣ) : E) ^ n * (x : E) with hy
    have hyx : t ^ n * y = (x : E) := by
      rw [hy, ← mul_assoc, ← mul_pow]
      have h1 : t * ((htu.unit⁻¹ : Eˣ) : E) = 1 := htu.mul_val_inv
      rw [h1, one_pow, one_mul]
    have hnorm : ‖(x : E)‖ = ‖t‖ ^ n * ‖y‖ := by
      rw [← hyx, norm_pow_mul_of_scale hscale]
    have hymem : ‖y‖ ≤ 1 := by
      have hpos : (0 : ℝ) < ‖t‖ ^ n := by positivity
      rw [hnorm] at hx
      exact le_of_mul_le_mul_left (by linarith) hpos
    refine ⟨⟨y, hymem⟩, ?_⟩
    refine Subtype.ext ?_
    show y * t ^ n = (x : E)
    rw [mul_comm]
    exact hyx

/-- The unit-ball pair of definition attached to a norm-scaling pseudouniformizer
(generic form of `ExampleUnitDisc.podD`; instantiated at all four jet rings). -/
noncomputable def unitBallPod (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) : PairOfDefinition E where
  A₀ := unitBall E
  I := Ideal.span {⟨t, ht1.le⟩}
  isOpen := isOpen_unitBall E
  fg := ⟨{⟨t, ht1.le⟩}, by simp⟩
  isAdic := by
    rw [isAdic_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [SetLike.mem_coe, mem_span_unitBall_pow_iff htu ht1.le ht0 hscale] at hx
      rw [mem_nhds_subtype]
      refine ⟨Metric.ball (x : E) (‖t‖ ^ n),
        Metric.ball_mem_nhds _ (by positivity), ?_⟩
      intro y hy
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
      rw [SetLike.mem_coe, mem_span_unitBall_pow_iff htu ht1.le ht0 hscale]
      calc ‖(y : E)‖ = ‖((y : E) - (x : E)) + (x : E)‖ := by ring_nf
        _ ≤ max ‖(y : E) - (x : E)‖ ‖(x : E)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ‖t‖ ^ n := max_le hy.le hx
    · rw [mem_nhds_subtype] at hs
      obtain ⟨U, hU, hUs⟩ := hs
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (by simpa using hU)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ht1
      refine ⟨n, fun x hx => hUs ?_⟩
      rw [SetLike.mem_coe, mem_span_unitBall_pow_iff htu ht1.le ht0 hscale] at hx
      rw [Set.mem_preimage]
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt hx hn

/-- Generic Huber structure from a scaling pseudouniformizer. -/
theorem isHuberRing_of_scale (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) : IsHuberRing E :=
  ⟨⟨unitBallPod t htu ht1 ht0 hscale⟩⟩

/-- Generic Tate structure from a scaling pseudouniformizer. -/
theorem isTateRing_of_scale (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖) : IsTateRing E := by
  have _ : IsHuberRing E := isHuberRing_of_scale t htu ht1 ht0 hscale
  refine ⟨⟨htu.unit, ?_⟩⟩
  show Tendsto (fun n : ℕ => ((htu.unit : Eˣ) : E) ^ n) atTop (𝓝 0)
  simp only [IsUnit.unit_spec]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖t ^ n‖ = ‖t‖ ^ n := fun n => by
    have := norm_pow_mul_of_scale (E := E) hscale n 1
    rwa [mul_one, norm_one, mul_one] at this
  simp only [hnorm]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1

end InstanceStack

/-! ### Scaling pseudouniformizers for the four rings -/

/-- Constants of the vendored `K⟨W⟩`, as a ring homomorphism. -/
noncomputable def constHomPS : K →+* PowerSeries.Restricted K (1 : ℝ) where
  toFun x := PowerSeries.Restricted.C (1 : ℝ) x
  map_one' := Subtype.ext (map_one PowerSeries.C)
  map_mul' x y := Subtype.ext (map_mul PowerSeries.C x y)
  map_zero' := Subtype.ext (map_zero PowerSeries.C)
  map_add' x y := Subtype.ext (map_add PowerSeries.C x y)

/-- Scaling by a `K`-constant in `𝒞`. -/
theorem norm_constC_mul (a : K) (f : JetC F) : ‖constC F a * f‖ = ‖a‖ * ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, PowerSeries.gaussNorm_eq,
    PowerSeries.gaussNorm_eq, Real.mul_iSup_of_nonneg (norm_nonneg a)]
  refine iSup_congr fun i => ?_
  rw [show (constC F a * f).1 = PowerSeries.C (RestrictedLaurent.C a) * f.1 from rfl,
    PowerSeries.coeff_C_mul, norm_C_mul]
  ring

instance : NormOneClass (JetA F) :=
  ⟨by
    show ‖((1 : JetA F) : JetC F)‖ = 1
    rw [show ((1 : JetA F) : JetC F) = 1 from rfl, norm_one]⟩

/-- A seminormed ultrametric comm ring is a nonarchimedean topological ring
(generalizes the normed version in `ExampleUnitDisc`). Lives HERE, in the
definition layer, so that every environment containing `JetA` resolves
`NonarchimedeanRing (JetA F)` to the same instance — the comparator challenge
(`Comparator/Challenge.lean`) and the full library must elaborate the headline
statements to structurally identical types. (Moved from
`FiniteJetFunctoriality.lean`, which is outside the challenge's import closure;
with the instance there, `IsSheafy (JetA F)` embedded a different
`NonarchimedeanRing` witness on each side and comparator rightly refused the
statement match.) -/
instance instNonarchimedeanRingOfSeminormedUltra {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R :=
  ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩

theorem norm_tA : ‖tA F‖ = ‖LaurentSeriesExample.t F‖ := norm_constA F _

/-- Scaling by `tA` in `𝓐` (restriction of the `𝒞`-statement). -/
theorem norm_tA_mul (x : JetA F) : ‖tA F * x‖ = ‖tA F‖ * ‖x‖ := by
  show ‖(constC F (LaurentSeriesExample.t F) * (x : JetC F) : JetC F)‖ = _
  rw [norm_constC_mul]
  congr 1
  exact (norm_tA F).symm

/-- The pseudouniformizer of `𝓑`. -/
noncomputable def tB : JetB F := TrivSqZeroExt.inl (constHomPS F (LaurentSeriesExample.t F))

theorem norm_tB : ‖tB F‖ = ‖LaurentSeriesExample.t F‖ := by
  rw [tB, JetNorm.norm_inl]
  exact norm_restrictedC _

theorem isUnit_tB : IsUnit (tB F) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (constHomPS F)) ?_
  exact (LaurentSeriesExample.t_ne_zero F).isUnit

theorem norm_tB_mul (x : JetB F) : ‖tB F * x‖ = ‖tB F‖ * ‖x‖ := by
  have hsnd : (tB F * x).snd = constHomPS F (LaurentSeriesExample.t F) * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (tB F).snd * x.fst = _
    rw [show (tB F).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (tB F * x).fst = constHomPS F (LaurentSeriesExample.t F) * x.fst := rfl
  rw [norm_tB, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.fst‖
    ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.snd‖ = _
  rw [norm_restrictedC_mul, norm_restrictedC_mul,
    mul_max_of_nonneg _ _ (norm_nonneg (LaurentSeriesExample.t F))]

/-- The pseudouniformizer of `𝓓`. -/
noncomputable def tD : JetD F := TrivSqZeroExt.inl (RestrictedLaurent.C
  (LaurentSeriesExample.t F))

theorem norm_tD : ‖tD F‖ = ‖LaurentSeriesExample.t F‖ := by
  rw [tD, JetNorm.norm_inl]
  show ‖single 0 _‖ = _
  rw [norm_single]

theorem isUnit_tD : IsUnit (tD F) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (RestrictedLaurent.C (R := K))) ?_
  exact (LaurentSeriesExample.t_ne_zero F).isUnit

theorem norm_tD_mul (x : JetD F) : ‖tD F * x‖ = ‖tD F‖ * ‖x‖ := by
  have hsnd : (tD F * x).snd =
      RestrictedLaurent.C (LaurentSeriesExample.t F) * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (tD F).snd * x.fst = _
    rw [show (tD F).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (tD F * x).fst =
      RestrictedLaurent.C (LaurentSeriesExample.t F) * x.fst := rfl
  rw [norm_tD, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖RestrictedLaurent.C _ * x.fst‖ ‖RestrictedLaurent.C _ * x.snd‖ = _
  rw [norm_C_mul, norm_C_mul,
    mul_max_of_nonneg _ _ (norm_nonneg (LaurentSeriesExample.t F))]

/-- The pseudouniformizer of `𝒞`. -/
noncomputable def tC : JetC F := constC F (LaurentSeriesExample.t F)

theorem norm_tC : ‖tC F‖ = ‖LaurentSeriesExample.t F‖ := norm_constC F _

theorem isUnit_tC : IsUnit (tC F) :=
  IsUnit.map (constC F) (LaurentSeriesExample.t_ne_zero F).isUnit

theorem norm_tC_mul (x : JetC F) : ‖tC F * x‖ = ‖tC F‖ * ‖x‖ := by
  rw [tC, norm_constC_mul, norm_constC]

/-! ### The Huber/Tate instances -/

instance : IsHuberRing (JetA F) :=
  isHuberRing_of_scale (tA F) (isUnit_tA F) (norm_tA_lt_one F) (norm_tA_pos F)
    (norm_tA_mul F)
instance : IsHuberRing (JetB F) :=
  isHuberRing_of_scale (tB F) (isUnit_tB F)
    (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F)
instance : IsHuberRing (JetC F) :=
  isHuberRing_of_scale (tC F) (isUnit_tC F)
    (by rw [norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tC]; exact norm_t_pos F) (norm_tC_mul F)
instance : IsHuberRing (JetD F) :=
  isHuberRing_of_scale (tD F) (isUnit_tD F)
    (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F)

instance : IsTateRing (JetA F) :=
  isTateRing_of_scale (tA F) (isUnit_tA F) (norm_tA_lt_one F) (norm_tA_pos F)
    (norm_tA_mul F)
instance : IsTateRing (JetB F) :=
  isTateRing_of_scale (tB F) (isUnit_tB F)
    (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F)
instance : IsTateRing (JetC F) :=
  isTateRing_of_scale (tC F) (isUnit_tC F)
    (by rw [norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tC]; exact norm_t_pos F) (norm_tC_mul F)
instance : IsTateRing (JetD F) :=
  isTateRing_of_scale (tD F) (isUnit_tD F)
    (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F)

noncomputable instance : ValuationSpectrum.PlusSubring (JetA F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetA F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetB F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetB F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetC F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetC F)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetD F) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetD F)⟩

section MaximalPlus

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]

/-- The unit ball is bounded (Huber sense) in any nonarchimedean normed ring. -/
theorem isBounded_unitBall : TopologicalRing.IsBounded ((unitBall E : Subring E) : Set E) := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rintro z ⟨s, hs, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖s * y‖ ≤ ‖s‖ * ‖y‖ := norm_mul_le s y
    _ ≤ 1 * ‖y‖ := by
        gcongr
        exact hs
    _ = ‖y‖ := one_mul _
    _ < ε := hy

/-- Elements of the unit ball are power-bounded. -/
theorem unitBall_subset_powerBounded :
    ((unitBall E : Subring E) : Set E) ⊆ TopologicalRing.powerBoundedSubring E := by
  intro x hx
  refine (isBounded_unitBall (E := E)).subset ?_
  rintro - ⟨k, rfl⟩
  show ‖x ^ k‖ ≤ 1
  induction k with
  | zero => rw [pow_zero, norm_one]
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_one₀ ih (norm_nonneg _) hx)

/-- The maximal plus ring (the full power-bounded subring) is a valid ring of integral
elements in any nonarchimedean normed ring with the standing instances ([FJP] §5:
boundedness is not required). -/
theorem isRingOfIntegralElements_powerBounded :
    ValuationSpectrum.IsRingOfIntegralElements
      (TopologicalRing.powerBoundedSubring.toSubring E) where
  isOpen := by
    have hmem : (TopologicalRing.powerBoundedSubring.toSubring E : Set E) ∈ 𝓝 (0 : E) := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_
      intro y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      exact unitBall_subset_powerBounded (E := E) hy.le
    exact (TopologicalRing.powerBoundedSubring.toSubring E).toAddSubgroup.isOpen_of_mem_nhds
      hmem
  isIntegrallyClosed := fun a ha =>
    TopologicalRing.isPowerBounded_of_isIntegral_of_subset_powerBounded
      (fun x hx => hx) ha
  subset_powerBounded := fun x hx => hx

end MaximalPlus

/-- The maximal plus ring is a ring of integral elements ([FJP] §5, the integral-closedness
argument after (5.2): `E°` is open, integrally closed, and power-bounded — boundedness is
not required). -/
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetA F) : Subring (JetA F))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetB F) : Subring (JetB F))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetC F) : Subring (JetC F))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetD F) : Subring (JetD F))) :=
  isRingOfIntegralElements_powerBounded

instance : IsUniformAddGroup (JetA F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetB F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetC F) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetD F) := SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (JetA F) (IsTopologicalAddGroup.rightUniformSpace (JetA F)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetB F) (IsTopologicalAddGroup.rightUniformSpace (JetB F)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetC F) (IsTopologicalAddGroup.rightUniformSpace (JetC F)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetD F) (IsTopologicalAddGroup.rightUniformSpace (JetD F)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

end FiniteJet
