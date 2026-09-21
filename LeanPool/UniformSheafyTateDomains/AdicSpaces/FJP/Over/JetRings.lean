/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFBase
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetRings

/-!
# The finite-jet pinching square over a general base field: the rings 𝓐, 𝓑, 𝓒, 𝓓

Source: [FJP] §1.4–§2 over an arbitrary base `K` in the CDVF campaign's D1 stack
(`NontriviallyNormedField` + `IsUltrametricDist` + `CompleteSpace`), replacing the Laurent
witness field `LaurentSeries F` of `FiniteJetRings.lean`. This file is the K8 "generic jet
rings" slice (crosswalk decision D9): it rebuilds the four rings and the strict Milnor row
of the finite-jet pinching square verbatim over `K`, in the namespace `FiniteJetOver`; the
frozen Laurent development in the `FiniteJet` namespace is untouched, and later tickets
re-express it as the specialization `K := LaurentSeries F`.

Following [FJP] (1.4) (paper §1.2: `L₀ = k°⟨W,W⁻¹⟩`, `B₀ = k°⟨W,Q⟩/(Q²)`, `C₀ = L₀⟨Q⟩`,
`D₀ = L₀⟨Q⟩/(Q²)`, all realised here through their generic fibres):

* `L K = K⟨W, W⁻¹⟩` — `FiniteJet.RestrictedLaurent K` (already fully generic);
* `JetB K = K⟨W, Q⟩/(Q²)` — dual numbers over the vendored `K⟨W⟩` with the max norm;
* `JetC K = L⟨Q⟩` — `PowerSeries.Restricted (L K) 1`;
* `JetD K = L⟨Q⟩/(Q²)` — dual numbers over `L K`;
* `JetA K = 𝓑 ×_𝓓 𝓒` — realised as the closed support subring of `JetC K` whose `Q⁰`- and
  `Q¹`-coefficients have nonnegative `W`-support ([FJP] (1.7)/(1.8)).

The maps of the square ([FJP] (1.5), (5.1)): `rhoB : 𝓑 → 𝓓` (componentwise `K⟨W⟩ ↪ L`),
`rhoC : 𝓒 → 𝓓` (2-jet truncation, with the norm-one linear section `sectionD`),
`iotaC : 𝓐 ↪ 𝓒`, `jB : 𝓐 → 𝓑`. The strict Milnor row `0 → 𝓐 → 𝓑 ⊕ 𝓒 → 𝓓 → 0` is exact
with **all norm constants 1** (`milnorRow_exact`, `max_norm_eq`,
`difference_strict_surjective`).

The pseudouniformizers of the four rings are the images `piA ϖ`, `piB ϖ`, `piC ϖ`, `piD ϖ`
of a base-field uniformizer `ϖ : Uniformizer K` (the K1 layer-1 API of `CDVFBase.lean`) —
the generic analogues of the frozen Laurent `FiniteJet.tA/tB/tC/tD`. They feed the generic
scaling-bundle endpoints of `FiniteJetRings.lean` (`isHuberRing_of_scale`,
`isTateRing_of_scale`), giving the Huber/Tate structure of each ring; the maximal plus
rings, `IsRingOfIntegralElements`, and right-uniformity completeness are ϖ-free and stay
instances.
-/

open Filter Topology
open scoped NNReal

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### The four rings -/

/-- `L K = K⟨W,W⁻¹⟩`, the radius-one Laurent algebra over the base field `K`
([FJP] (1.4); `FiniteJet.RestrictedLaurent` is already generic). -/
abbrev L : Type u := RestrictedLaurent K

/-- `𝓒 = L⟨Q⟩` over the base field `K` ([FJP] (1.4)). -/
abbrev JetC : Type u := PowerSeries.Restricted (L K) (1 : ℝ)

/-- `𝓑 = K⟨W,Q⟩/(Q²)`, modelled as dual numbers over the vendored `K⟨W⟩` ([FJP] (1.4)
with Lemma 2.2's isometric max-norm decomposition `k⟨W⟩ ⊕ Q·k⟨W⟩`). -/
abbrev JetB : Type u := DualNumber (PowerSeries.Restricted K (1 : ℝ))

/-- `𝓓 = L⟨Q⟩/(Q²)`, modelled as dual numbers over `L K` ([FJP] (1.4), (2.1d):
`𝓓 = L ⊕ QL` with max norm). -/
abbrev JetD : Type u := DualNumber (L K)

/-! ### The comparison maps of the square ([FJP] (1.5), (5.1)) -/

/-- The `Q`-coefficient of index `n` of an element of `𝓒`. -/
noncomputable def qCoeff (n : ℕ) (f : JetC K) : L K := PowerSeries.coeff n f.1

theorem qCoeff_zero_mul (f g : JetC K) :
    qCoeff K 0 (f * g) = qCoeff K 0 f * qCoeff K 0 g := by
  show PowerSeries.coeff 0 (f * g : JetC K).1 = _
  rw [show (f * g : JetC K).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul]
  simp [qCoeff]

theorem qCoeff_one_mul (f g : JetC K) :
    qCoeff K 1 (f * g) = qCoeff K 0 f * qCoeff K 1 g + qCoeff K 1 f * qCoeff K 0 g := by
  show PowerSeries.coeff 1 (f * g : JetC K).1 = _
  rw [show (f * g : JetC K).1 = f.1 * g.1 from rfl, PowerSeries.coeff_mul,
    show Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  rfl

theorem qCoeff_add (f g : JetC K) (n : ℕ) :
    qCoeff K n (f + g) = qCoeff K n f + qCoeff K n g := by
  show PowerSeries.coeff n (f + g : JetC K).1 = _
  rw [show (f + g : JetC K).1 = f.1 + g.1 from rfl, map_add]
  rfl

theorem qCoeff_neg (f : JetC K) (n : ℕ) : qCoeff K n (-f) = -qCoeff K n f := by
  show PowerSeries.coeff n (-f : JetC K).1 = _
  rw [show (-f : JetC K).1 = -f.1 from rfl, map_neg]
  rfl

theorem qCoeff_one (n : ℕ) : qCoeff K n 1 = if n = 0 then 1 else 0 := by
  show PowerSeries.coeff n (1 : JetC K).1 = _
  rw [show (1 : JetC K).1 = 1 from rfl, PowerSeries.coeff_one]

theorem qCoeff_zero (n : ℕ) : qCoeff K n 0 = 0 := by
  show PowerSeries.coeff n (0 : JetC K).1 = _
  rw [show (0 : JetC K).1 = 0 from rfl, map_zero]

/-- Coefficient functionals of `𝒞` are `1`-Lipschitz, hence continuous. -/
theorem continuous_qCoeff (n : ℕ) : Continuous (qCoeff K n) := by
  have hlip : LipschitzWith 1 (qCoeff K n) := LipschitzWith.of_dist_le_mul fun f g => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : qCoeff K n f - qCoeff K n g = qCoeff K n (f - g) := by
      rw [show f - g = f + -g from sub_eq_add_neg f g, qCoeff_add, qCoeff_neg,
        sub_eq_add_neg]
    rw [hsub]
    have h := PowerSeries.le_gaussNorm norm 1 (f - g).1
      (Restricted.hasGaussNorm (R := L K) 1 (f - g)) n
    rwa [one_pow, mul_one] at h
  exact hlip.continuous

/-- `ρC : 𝓒 → 𝓓`, reduction modulo `Q²` = 2-jet truncation ([FJP] (1.5): "the second is
reduction modulo `Q²`"). -/
noncomputable def rhoC : JetC K →+* JetD K where
  toFun f := ⟨qCoeff K 0 f, qCoeff K 1 f⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (1 : JetC K).1 = (1 : JetD K).fst
      rw [show (1 : JetC K).1 = 1 from rfl, TrivSqZeroExt.fst_one, PowerSeries.coeff_zero_one]
    · show PowerSeries.coeff 1 (1 : JetC K).1 = (1 : JetD K).snd
      rw [show (1 : JetC K).1 = 1 from rfl, TrivSqZeroExt.snd_one, PowerSeries.coeff_one,
        if_neg one_ne_zero]
  map_mul' f g := by
    -- v4.33: rewriting `(f * g).1 = f.1 * g.1` into the goal leaves `Subtype.val`
    -- projections that type only after unfolding the `JetC` def, and `kabstract`
    -- rejects the follow-up rewrites; both components are exactly the proven
    -- `qCoeff`-multiplication lemmas (the `TrivSqZeroExt` structure is defeq).
    refine TrivSqZeroExt.ext ?_ ?_
    · show qCoeff K 0 (f * g) = qCoeff K 0 f * qCoeff K 0 g
      exact qCoeff_zero_mul K f g
    · show qCoeff K 1 (f * g) = qCoeff K 0 f * qCoeff K 1 g + qCoeff K 1 f * qCoeff K 0 g
      exact qCoeff_one_mul K f g
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · show PowerSeries.coeff 0 (0 : JetC K).1 = (0 : JetD K).fst
      rw [show (0 : JetC K).1 = 0 from rfl, TrivSqZeroExt.fst_zero, map_zero]
    · show PowerSeries.coeff 1 (0 : JetC K).1 = (0 : JetD K).snd
      rw [show (0 : JetC K).1 = 0 from rfl, TrivSqZeroExt.snd_zero, map_zero]
  map_add' f g := by
    -- v4.33: same `kabstract`/`JetC`-projection issue as `map_mul'`; both components
    -- are the proven `qCoeff_add` (the `TrivSqZeroExt` addition is componentwise-defeq).
    refine TrivSqZeroExt.ext ?_ ?_
    · show qCoeff K 0 (f + g) = qCoeff K 0 f + qCoeff K 0 g
      exact qCoeff_add K f g 0
    · show qCoeff K 1 (f + g) = qCoeff K 1 f + qCoeff K 1 g
      exact qCoeff_add K f g 1

/-- `ρB : 𝓑 → 𝓓`, componentwise restriction from the disc to the annulus ([FJP] (1.5):
"the first is restriction from the `W`-disc to its radius-one boundary"). -/
noncomputable def rhoB : JetB K →+* JetD K :=
  JetNorm.mapHom (ofRestricted (R := K))

/-- The norm-one linear truncation section `𝓓 → 𝓒`, `f₀ + Qf₁ ↦ f₀ + Qf₁`
([FJP] Prop 2.1: "Reduction modulo `Q²` has the norm-preserving linear section
`f₀ + Qf₁ ↦ f₀ + Qf₁`"). -/
noncomputable def sectionD (x : JetD K) : JetC K :=
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

theorem qCoeff_sectionD (x : JetD K) (n : ℕ) :
    qCoeff K n (sectionD K x) = if n = 0 then x.fst else if n = 1 then x.snd else 0 := by
  show PowerSeries.coeff n (PowerSeries.mk fun m =>
    if m = 0 then x.fst else if m = 1 then x.snd else 0) = _
  rw [PowerSeries.coeff_mk]

@[simp] theorem rhoC_sectionD (x : JetD K) : rhoC K (sectionD K x) = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show qCoeff K 0 (sectionD K x) = x.fst
    rw [qCoeff_sectionD, if_pos rfl]
  · show qCoeff K 1 (sectionD K x) = x.snd
    rw [qCoeff_sectionD, if_neg one_ne_zero, if_pos rfl]

theorem sectionD_add (x y : JetD K) : sectionD K (x + y) = sectionD K x + sectionD K y := by
  apply Subtype.ext
  ext n
  rw [show PowerSeries.coeff n (sectionD K (x + y)).1 =
      qCoeff K n (sectionD K (x + y)) from rfl, qCoeff_sectionD,
    show (sectionD K x + sectionD K y).1 = (sectionD K x).1 + (sectionD K y).1 from rfl,
    map_add,
    show PowerSeries.coeff n (sectionD K x).1 = qCoeff K n (sectionD K x) from rfl,
    show PowerSeries.coeff n (sectionD K y).1 = qCoeff K n (sectionD K y) from rfl,
    qCoeff_sectionD, qCoeff_sectionD]
  rcases eq_or_ne n 0 with rfl | h0
  · simp [TrivSqZeroExt.fst_add]
  · rw [if_neg h0, if_neg h0, if_neg h0]
    rcases eq_or_ne n 1 with rfl | h1
    · simp [TrivSqZeroExt.snd_add]
    · rw [if_neg h1, if_neg h1, if_neg h1, add_zero]

theorem norm_sectionD (x : JetD K) : ‖sectionD K x‖ = ‖x‖ := by
  rw [Restricted.norm_eq, JetNorm.norm_def]
  refine le_antisymm ?_ ?_
  · rw [PowerSeries.gaussNorm_eq]
    refine Real.iSup_le (fun n => ?_) (le_max_of_le_left (norm_nonneg _))
    rw [one_pow, mul_one]
    show ‖PowerSeries.coeff n (sectionD K x).1‖ ≤ _
    rw [show PowerSeries.coeff n (sectionD K x).1 = qCoeff K n (sectionD K x) from rfl,
      qCoeff_sectionD]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_pos rfl]; exact le_max_left _ _
    · rw [if_neg h0]
      rcases eq_or_ne n 1 with rfl | h1
      · rw [if_pos rfl]; exact le_max_right _ _
      · rw [if_neg h1, norm_zero]
        exact le_max_of_le_left (norm_nonneg _)
  · refine max_le ?_ ?_
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD K x).1
        (Restricted.hasGaussNorm (R := L K) 1 (sectionD K x)) 0
      rw [one_pow, mul_one, show PowerSeries.coeff 0 (sectionD K x).1 =
        qCoeff K 0 (sectionD K x) from rfl, qCoeff_sectionD, if_pos rfl] at h
      exact h
    · have h := PowerSeries.le_gaussNorm norm 1 (sectionD K x).1
        (Restricted.hasGaussNorm (R := L K) 1 (sectionD K x)) 1
      rw [one_pow, mul_one, show PowerSeries.coeff 1 (sectionD K x).1 =
        qCoeff K 1 (sectionD K x) from rfl, qCoeff_sectionD, if_neg one_ne_zero,
        if_pos rfl] at h
      exact h

/-- `ρC` is norm-nonincreasing. -/
theorem norm_rhoC_le (f : JetC K) : ‖rhoC K f‖ ≤ ‖f‖ := by
  rw [JetNorm.norm_def]
  refine max_le ?_ ?_
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L K) 1 f) 0
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)
  · have h := PowerSeries.le_gaussNorm norm 1 f.1
      (Restricted.hasGaussNorm (R := L K) 1 f) 1
    rw [one_pow, mul_one] at h
    exact h.trans (le_of_eq (Restricted.norm_eq 1 f).symm)

/-- `ρB` is an isometry (componentwise `ofRestricted` is norm-preserving). -/
theorem norm_rhoB (b : JetB K) : ‖rhoB K b‖ = ‖b‖ :=
  JetNorm.norm_mapHom _ (fun a => ofRestricted_norm a) b

theorem rhoB_injective : Function.Injective (rhoB K) :=
  JetNorm.mapHom_injective _ (ofRestricted_injective (R := K))

/-- `ρC` is surjective ([FJP] Prop 2.1: `𝒞 → 𝒟` is a strict surjection). -/
theorem rhoC_surjective : Function.Surjective (rhoC K) :=
  fun x => ⟨sectionD K x, rhoC_sectionD K x⟩

/-! ### The pinching algebra 𝓐 ([FJP] Definition 1.2 via Lemma 2.2 / (1.7) / (1.8)) -/

/-- The support subring: elements of `𝒞` whose `Q⁰`- and `Q¹`-coefficients lie in the
nonnegative-support subring `K⟨W⟩ ⊂ L` — [FJP] (1.7):
`𝒜 = {f₀(W) + Qf₁(W) + Q²h : f₀, f₁ ∈ k⟨W⟩, h ∈ L⟨Q⟩}`. -/
noncomputable def jetSupport : Subring (JetC K) where
  carrier := {f | qCoeff K 0 f ∈ nonnegSubring K ∧ qCoeff K 1 f ∈ nonnegSubring K}
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

/-- `𝓐`, the finite-jet pinching algebra over the base field `K` ([FJP] Definition 1.2),
realised as the support subring of `𝒞` with the restricted norm ([FJP] Lemma 2.2). -/
abbrev JetA : Type u := ↥(jetSupport K)

/-- The support subring is closed in `𝒞` ([FJP] Lemma 2.2: "Imposing the preceding closed
condition on the `Q⁰`- and `Q¹`-coefficients therefore cuts out a closed subspace of 𝒞"). -/
theorem isClosed_jetSupport : IsClosed ((jetSupport K : Set (JetC K))) := by
  have heq : (jetSupport K : Set (JetC K)) =
      (qCoeff K 0) ⁻¹' (nonnegSubring K : Set (L K)) ∩
      (qCoeff K 1) ⁻¹' (nonnegSubring K : Set (L K)) := rfl
  rw [heq]
  exact ((isClosed_nonnegSubring (R := K)).preimage (continuous_qCoeff K 0)).inter
    ((isClosed_nonnegSubring (R := K)).preimage (continuous_qCoeff K 1))

/-- `𝓐` inherits `NormedCommRing` and `IsUltrametricDist` from `𝒞` through the mathlib
`SubringClass` instances (the norm is the restriction — [FJP] Lemma 2.2's isometry is
definitional). Completeness holds because the subring is closed. -/
instance : CompleteSpace (JetA K) := (isClosed_jetSupport K).completeSpace_coe

/-- The inclusion `ιC : 𝓐 → 𝓒` (an isometry by construction; [FJP] Lemma 2.2). -/
noncomputable def iotaC : JetA K →+* JetC K := (jetSupport K).subtype

@[simp] theorem norm_iotaC (a : JetA K) : ‖iotaC K a‖ = ‖a‖ := rfl

/-- `jB : 𝓐 → 𝓑`, the 2-jet of an element of 𝓐, with coefficients in `K⟨W⟩`
([FJP] (5.1): `ι_B : 𝒜 → ℬ`). -/
noncomputable def jB : JetA K →+* JetB K where
  toFun a :=
    ⟨(nonnegEquiv (R := K)).symm ⟨qCoeff K 0 (a : JetC K), a.2.1⟩,
     (nonnegEquiv (R := K)).symm ⟨qCoeff K 1 (a : JetC K), a.2.2⟩⟩
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 0 ((1 : JetA K) : JetC K) = ((1 : nonnegSubring K) : L K)
        rw [show ((1 : JetA K) : JetC K) = 1 from rfl, qCoeff_one, if_pos rfl]
        rfl))).trans (map_one _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 1 ((1 : JetA K) : JetC K) = ((0 : nonnegSubring K) : L K)
        rw [show ((1 : JetA K) : JetC K) = 1 from rfl, qCoeff_one, if_neg one_ne_zero]
        rfl))).trans (map_zero _)
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 0 ((a * b : JetA K) : JetC K) = _
        rw [show ((a * b : JetA K) : JetC K) = (a : JetC K) * (b : JetC K) from rfl,
          qCoeff_zero_mul]
        rfl))).trans (map_mul _ _ _)
    · have hval : (⟨qCoeff K 1 ((a * b : JetA K) : JetC K), (a * b).2.2⟩ :
          nonnegSubring K) =
          ⟨qCoeff K 0 (a : JetC K), a.2.1⟩ * ⟨qCoeff K 1 (b : JetC K), b.2.2⟩ +
          ⟨qCoeff K 1 (a : JetC K), a.2.2⟩ * ⟨qCoeff K 0 (b : JetC K), b.2.1⟩ := by
        refine Subtype.ext ?_
        show qCoeff K 1 ((a * b : JetA K) : JetC K) = _
        rw [show ((a * b : JetA K) : JetC K) = (a : JetC K) * (b : JetC K) from rfl,
          qCoeff_one_mul]
        rfl
      exact (congrArg (nonnegEquiv (R := K)).symm hval).trans (by
        rw [map_add (nonnegEquiv (R := K)).symm, map_mul (nonnegEquiv (R := K)).symm,
          map_mul (nonnegEquiv (R := K)).symm]
        rfl)
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 0 ((0 : JetA K) : JetC K) = ((0 : nonnegSubring K) : L K)
        rw [show ((0 : JetA K) : JetC K) = 0 from rfl, qCoeff_zero]
        rfl))).trans (map_zero _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 1 ((0 : JetA K) : JetC K) = ((0 : nonnegSubring K) : L K)
        rw [show ((0 : JetA K) : JetC K) = 0 from rfl, qCoeff_zero]
        rfl))).trans (map_zero _)
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 0 ((a + b : JetA K) : JetC K) = _
        rw [show ((a + b : JetA K) : JetC K) = (a : JetC K) + (b : JetC K) from rfl,
          qCoeff_add]
        rfl))).trans (map_add _ _ _)
    · exact (congrArg (nonnegEquiv (R := K)).symm (Subtype.ext (by
        show qCoeff K 1 ((a + b : JetA K) : JetC K) = _
        rw [show ((a + b : JetA K) : JetC K) = (a : JetC K) + (b : JetC K) from rfl,
          qCoeff_add]
        rfl))).trans (map_add _ _ _)

theorem norm_nonnegEquiv_symm (x : nonnegSubring K) :
    ‖(nonnegEquiv (R := K)).symm x‖ = ‖(x : L K)‖ := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (nonnegEquiv (R := K)) x]
  exact (nonnegEquiv_norm _).symm

theorem norm_qCoeff_le (f : JetC K) (n : ℕ) : ‖qCoeff K n f‖ ≤ ‖f‖ := by
  have h := PowerSeries.le_gaussNorm norm 1 f.1 (Restricted.hasGaussNorm (R := L K) 1 f) n
  rwa [one_pow, mul_one] at h

theorem norm_jB_le (a : JetA K) : ‖jB K a‖ ≤ ‖a‖ := by
  rw [JetNorm.norm_def]
  refine max_le ?_ ?_
  · show ‖(nonnegEquiv (R := K)).symm _‖ ≤ _
    rw [norm_nonnegEquiv_symm]
    exact norm_qCoeff_le K _ 0
  · show ‖(nonnegEquiv (R := K)).symm _‖ ≤ _
    rw [norm_nonnegEquiv_symm]
    exact norm_qCoeff_le K _ 1

/-! ### The strict Milnor row ([FJP] Prop 2.1, Lemma 2.2, (2.1b))

`0 → 𝓐 →(jB, ιC) 𝓑 ⊕ 𝓒 →(ρB − ρC) 𝓓 → 0` is exact with all constants 1:
* the square commutes on 𝓐,
* an element of 𝓒 lies in 𝓐 iff its 2-jet comes from 𝓑,
* the difference map is strictly surjective via the norm-one section,
* the pullback (max) norm of `(jB a, ιC a)` equals `‖a‖` ([FJP] Lemma 2.2:
  "the maximum pullback norm of `(b, c)` equals `‖c‖_𝒞`"). -/

theorem square_commutes (a : JetA K) : rhoB K (jB K a) = rhoC K (iotaC K a) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 0 (a : JetC K), a.2.1⟩) = _
    rw [ofRestricted_nonnegEquiv_symm]
    rfl
  · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 1 (a : JetC K), a.2.2⟩) = _
    rw [ofRestricted_nonnegEquiv_symm]
    rfl

theorem mem_range_ofRestricted_iff (x : L K) :
    x ∈ Set.range (ofRestricted (R := K)) ↔ x ∈ nonnegSubring K := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ((nonnegEquiv (R := K)) y).2
  · intro hx
    exact ⟨(nonnegEquiv (R := K)).symm ⟨x, hx⟩, by
      rw [ofRestricted_nonnegEquiv_symm]⟩

/-- Cartesianness, membership form: `c ∈ 𝓐 ↔ ρC c ∈ range ρB` ([FJP] (1.6)/(1.7)). -/
theorem mem_jetSupport_iff_jet_in_range (c : JetC K) :
    c ∈ jetSupport K ↔ rhoC K c ∈ Set.range (rhoB K) := by
  constructor
  · intro hc
    refine ⟨⟨(nonnegEquiv (R := K)).symm ⟨qCoeff K 0 c, hc.1⟩,
      (nonnegEquiv (R := K)).symm ⟨qCoeff K 1 c, hc.2⟩⟩, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 0 c, hc.1⟩) = _
      rw [ofRestricted_nonnegEquiv_symm]
      rfl
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 1 c, hc.2⟩) = _
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
theorem milnorRow_exact (b : JetB K) (c : JetC K) (h : rhoB K b = rhoC K c) :
    ∃! a : JetA K, jB K a = b ∧ iotaC K a = c := by
  have hmem : c ∈ jetSupport K :=
    (mem_jetSupport_iff_jet_in_range K c).mpr ⟨b, h⟩
  refine ⟨⟨c, hmem⟩, ⟨?_, rfl⟩, ?_⟩
  · -- `jB ⟨c, _⟩ = b`, componentwise via injectivity of `ofRestricted`
    refine TrivSqZeroExt.ext ?_ ?_
    · refine ofRestricted_injective (R := K) ?_
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 0 c, hmem.1⟩) =
        ofRestricted b.fst
      rw [ofRestricted_nonnegEquiv_symm]
      exact (congrArg TrivSqZeroExt.fst h).symm
    · refine ofRestricted_injective (R := K) ?_
      show ofRestricted ((nonnegEquiv (R := K)).symm ⟨qCoeff K 1 c, hmem.2⟩) =
        ofRestricted b.snd
      rw [ofRestricted_nonnegEquiv_symm]
      exact (congrArg TrivSqZeroExt.snd h).symm
  · rintro a ⟨-, rfl⟩
    rfl

/-- The pullback norm identity ([FJP] Lemma 2.2): for `a ∈ 𝓐`,
`max ‖jB a‖ ‖ιC a‖ = ‖a‖`. -/
theorem max_norm_eq (a : JetA K) : max ‖jB K a‖ ‖iotaC K a‖ = ‖a‖ := by
  rw [norm_iotaC]
  exact max_eq_right (norm_jB_le K a)

/-- Strict surjectivity of the difference map with constant 1 ([FJP] Prop 2.1 and (2.1b):
"the two denominator losses in the defining square are zero"). -/
theorem difference_strict_surjective (d : JetD K) :
    ∃ c : JetC K, rhoC K c = d ∧ ‖c‖ = ‖d‖ :=
  ⟨sectionD K d, rhoC_sectionD K d, norm_sectionD K d⟩

/-! ### Scalar embeddings -/

/-- Constants of `𝒞` over the base `L`, as a ring homomorphism. -/
noncomputable def constHomC : L K →+* JetC K where
  toFun x := PowerSeries.Restricted.C (1 : ℝ) x
  map_one' := Subtype.ext (map_one PowerSeries.C)
  map_mul' x y := Subtype.ext (map_mul PowerSeries.C x y)
  map_zero' := Subtype.ext (map_zero PowerSeries.C)
  map_add' x y := Subtype.ext (map_add PowerSeries.C x y)

theorem norm_constHomC (x : L K) : ‖constHomC K x‖ = ‖x‖ := norm_restrictedC x

theorem qCoeff_constHomC (x : L K) (n : ℕ) :
    qCoeff K n (constHomC K x) = if n = 0 then x else 0 := by
  show PowerSeries.coeff n (PowerSeries.C x) = _
  rw [PowerSeries.coeff_C]

/-- The constant embedding `K →+* 𝒞` (through `RestrictedLaurent.C` and the power-series
constants). -/
noncomputable def constC : K →+* JetC K :=
  (constHomC K).comp (RestrictedLaurent.C (R := K))

theorem norm_constC (a : K) : ‖constC K a‖ = ‖a‖ := by
  show ‖constHomC K (RestrictedLaurent.C a)‖ = ‖a‖
  rw [norm_constHomC]
  show ‖single 0 a‖ = ‖a‖
  rw [norm_single]

/-- The constants land in 𝓐 (support `(0,0)`). -/
theorem constC_mem_jetSupport (a : K) : constC K a ∈ jetSupport K := by
  constructor
  · show qCoeff K 0 (constHomC K (RestrictedLaurent.C a)) ∈ _
    rw [qCoeff_constHomC, if_pos rfl]
    intro b hb
    show (if b = 0 then a else 0) = 0
    rw [if_neg (by omega)]
  · show qCoeff K 1 (constHomC K (RestrictedLaurent.C a)) ∈ _
    rw [qCoeff_constHomC, if_neg one_ne_zero]
    exact zero_mem _

/-- The constant embedding `K →+* 𝓐`. -/
noncomputable def constA : K →+* JetA K :=
  (constC K).codRestrict (jetSupport K) (constC_mem_jetSupport K)

theorem norm_constA (a : K) : ‖constA K a‖ = ‖a‖ := norm_constC K a

/-- Constants of the vendored `K⟨W⟩`, as a ring homomorphism. -/
noncomputable def constHomPS : K →+* PowerSeries.Restricted K (1 : ℝ) where
  toFun x := PowerSeries.Restricted.C (1 : ℝ) x
  map_one' := Subtype.ext (map_one PowerSeries.C)
  map_mul' x y := Subtype.ext (map_mul PowerSeries.C x y)
  map_zero' := Subtype.ext (map_zero PowerSeries.C)
  map_add' x y := Subtype.ext (map_add PowerSeries.C x y)

/-- Scaling by a `K`-constant in `𝒞`. -/
theorem norm_constC_mul (a : K) (f : JetC K) : ‖constC K a * f‖ = ‖a‖ * ‖f‖ := by
  rw [Restricted.norm_eq, Restricted.norm_eq, PowerSeries.gaussNorm_eq,
    PowerSeries.gaussNorm_eq, Real.mul_iSup_of_nonneg (norm_nonneg a)]
  refine iSup_congr fun i => ?_
  rw [show (constC K a * f).1 = PowerSeries.C (RestrictedLaurent.C a) * f.1 from rfl,
    PowerSeries.coeff_C_mul, norm_C_mul]
  ring

instance : NormOneClass (JetA K) :=
  ⟨by
    show ‖((1 : JetA K) : JetC K)‖ = 1
    rw [show ((1 : JetA K) : JetC K) = 1 from rfl, norm_one]⟩

/-! ### Pseudouniformizers from a base-field uniformizer

The scaling pseudouniformizer of each jet ring is the image of a uniformizer
`ϖ : Uniformizer K` (the layer-1 API of `CDVFBase.lean`): `piA ϖ`, `piB ϖ`, `piC ϖ`,
`piD ϖ` — the ϖ-parametric analogues of the frozen Laurent `FiniteJet.tA/tB/tC/tD`
(deliberately *not* named `tA/…` to avoid confusion with the frozen development).
Their norm windows and exact norm scaling are sourced from
`ϖ.norm_val_lt_one`/`ϖ.norm_val_pos`/`ϖ.isUnit_val`/`ϖ.norm_val_mul` instead of
`LaurentSeriesExample.t`. -/

section Pseudouniformizer

variable {K}

/-- The pseudouniformizer of `𝓐`: the image of the base-field uniformizer `ϖ`. -/
noncomputable def piA (ϖ : Uniformizer K) : JetA K := constA K ϖ.val

/-- The pseudouniformizer of `𝓑`: the image of the base-field uniformizer `ϖ`. -/
noncomputable def piB (ϖ : Uniformizer K) : JetB K :=
  TrivSqZeroExt.inl (constHomPS K ϖ.val)

/-- The pseudouniformizer of `𝒞`: the image of the base-field uniformizer `ϖ`. -/
noncomputable def piC (ϖ : Uniformizer K) : JetC K := constC K ϖ.val

/-- The pseudouniformizer of `𝓓`: the image of the base-field uniformizer `ϖ`. -/
noncomputable def piD (ϖ : Uniformizer K) : JetD K :=
  TrivSqZeroExt.inl (RestrictedLaurent.C ϖ.val)

theorem norm_piA (ϖ : Uniformizer K) : ‖piA ϖ‖ = ‖ϖ.val‖ := norm_constA K _

theorem norm_piA_lt_one (ϖ : Uniformizer K) : ‖piA ϖ‖ < 1 := by
  rw [norm_piA]
  exact ϖ.norm_val_lt_one

theorem norm_piA_pos (ϖ : Uniformizer K) : 0 < ‖piA ϖ‖ := by
  rw [norm_piA]
  exact ϖ.norm_val_pos

theorem isUnit_piA (ϖ : Uniformizer K) : IsUnit (piA ϖ) := by
  refine IsUnit.map (constA K) ?_
  exact ϖ.isUnit_val

/-- Scaling by `piA ϖ` in `𝓐` (restriction of the `𝒞`-statement). -/
theorem norm_piA_mul (ϖ : Uniformizer K) (x : JetA K) : ‖piA ϖ * x‖ = ‖piA ϖ‖ * ‖x‖ := by
  show ‖(constC K ϖ.val * (x : JetC K) : JetC K)‖ = _
  rw [norm_constC_mul]
  congr 1
  exact (norm_piA ϖ).symm

theorem norm_piB (ϖ : Uniformizer K) : ‖piB ϖ‖ = ‖ϖ.val‖ := by
  rw [piB, JetNorm.norm_inl]
  exact norm_restrictedC _

omit [CompleteSpace K] in
theorem isUnit_piB (ϖ : Uniformizer K) : IsUnit (piB ϖ) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (constHomPS K)) ?_
  exact ϖ.isUnit_val

theorem norm_piB_mul (ϖ : Uniformizer K) (x : JetB K) : ‖piB ϖ * x‖ = ‖piB ϖ‖ * ‖x‖ := by
  have hsnd : (piB ϖ * x).snd = constHomPS K ϖ.val * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (piB ϖ).snd * x.fst = _
    rw [show (piB ϖ).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (piB ϖ * x).fst = constHomPS K ϖ.val * x.fst := rfl
  rw [norm_piB, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.fst‖
    ‖PowerSeries.Restricted.C (1 : ℝ) _ * x.snd‖ = _
  rw [norm_restrictedC_mul, norm_restrictedC_mul,
    mul_max_of_nonneg _ _ (norm_nonneg ϖ.val)]

theorem norm_piC (ϖ : Uniformizer K) : ‖piC ϖ‖ = ‖ϖ.val‖ := norm_constC K _

theorem isUnit_piC (ϖ : Uniformizer K) : IsUnit (piC ϖ) :=
  IsUnit.map (constC K) ϖ.isUnit_val

theorem norm_piC_mul (ϖ : Uniformizer K) (x : JetC K) : ‖piC ϖ * x‖ = ‖piC ϖ‖ * ‖x‖ := by
  rw [piC, norm_constC_mul, norm_constC]

theorem norm_piD (ϖ : Uniformizer K) : ‖piD ϖ‖ = ‖ϖ.val‖ := by
  rw [piD, JetNorm.norm_inl]
  show ‖single 0 _‖ = _
  rw [norm_single]

theorem isUnit_piD (ϖ : Uniformizer K) : IsUnit (piD ϖ) := by
  refine IsUnit.map ((TrivSqZeroExt.inlHom _ _).comp (RestrictedLaurent.C (R := K))) ?_
  exact ϖ.isUnit_val

theorem norm_piD_mul (ϖ : Uniformizer K) (x : JetD K) : ‖piD ϖ * x‖ = ‖piD ϖ‖ * ‖x‖ := by
  have hsnd : (piD ϖ * x).snd = RestrictedLaurent.C ϖ.val * x.snd := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
    show _ + (piD ϖ).snd * x.fst = _
    rw [show (piD ϖ).snd = 0 from rfl, zero_mul, add_zero]
    rfl
  have hfst : (piD ϖ * x).fst = RestrictedLaurent.C ϖ.val * x.fst := rfl
  rw [norm_piD, JetNorm.norm_def, JetNorm.norm_def, hfst, hsnd]
  show max ‖RestrictedLaurent.C _ * x.fst‖ ‖RestrictedLaurent.C _ * x.snd‖ = _
  rw [norm_C_mul, norm_C_mul,
    mul_max_of_nonneg _ _ (norm_nonneg ϖ.val)]

/-! ### The Huber/Tate structure of the four rings

Each of 𝓐, 𝓑, 𝓒, 𝓓 is a complete Tate ring; the generic scaling-bundle endpoints
`FiniteJet.isHuberRing_of_scale` / `FiniteJet.isTateRing_of_scale` are fed the
pseudouniformizer of the ring. These are *theorems* taking an explicit uniformizer, not
instances: over an abstract base a uniformizer is chosen data (crosswalk D1, layer 1). -/

/-- `𝓐` is a Huber ring for any base-field uniformizer. -/
theorem isHuberRing_JetA (ϖ : Uniformizer K) : IsHuberRing (JetA K) :=
  isHuberRing_of_scale (piA ϖ) (isUnit_piA ϖ) (norm_piA_lt_one ϖ) (norm_piA_pos ϖ)
    (norm_piA_mul ϖ)

/-- `𝓑` is a Huber ring for any base-field uniformizer. -/
theorem isHuberRing_JetB (ϖ : Uniformizer K) : IsHuberRing (JetB K) :=
  isHuberRing_of_scale (piB ϖ) (isUnit_piB ϖ)
    (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos) (norm_piB_mul ϖ)

/-- `𝒞` is a Huber ring for any base-field uniformizer. -/
theorem isHuberRing_JetC (ϖ : Uniformizer K) : IsHuberRing (JetC K) :=
  isHuberRing_of_scale (piC ϖ) (isUnit_piC ϖ)
    (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piC]; exact ϖ.norm_val_pos) (norm_piC_mul ϖ)

/-- `𝓓` is a Huber ring for any base-field uniformizer. -/
theorem isHuberRing_JetD (ϖ : Uniformizer K) : IsHuberRing (JetD K) :=
  isHuberRing_of_scale (piD ϖ) (isUnit_piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos) (norm_piD_mul ϖ)

/-- `𝓐` is a Tate ring for any base-field uniformizer. -/
theorem isTateRing_JetA (ϖ : Uniformizer K) : IsTateRing (JetA K) :=
  isTateRing_of_scale (piA ϖ) (isUnit_piA ϖ) (norm_piA_lt_one ϖ) (norm_piA_pos ϖ)
    (norm_piA_mul ϖ)

/-- `𝓑` is a Tate ring for any base-field uniformizer. -/
theorem isTateRing_JetB (ϖ : Uniformizer K) : IsTateRing (JetB K) :=
  isTateRing_of_scale (piB ϖ) (isUnit_piB ϖ)
    (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos) (norm_piB_mul ϖ)

/-- `𝒞` is a Tate ring for any base-field uniformizer. -/
theorem isTateRing_JetC (ϖ : Uniformizer K) : IsTateRing (JetC K) :=
  isTateRing_of_scale (piC ϖ) (isUnit_piC ϖ)
    (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piC]; exact ϖ.norm_val_pos) (norm_piC_mul ϖ)

/-- `𝓓` is a Tate ring for any base-field uniformizer. -/
theorem isTateRing_JetD (ϖ : Uniformizer K) : IsTateRing (JetD K) :=
  isTateRing_of_scale (piD ϖ) (isUnit_piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos) (norm_piD_mul ϖ)

end Pseudouniformizer

/-! ### The maximal plus rings and the remaining instance stack

The chosen plus ring of each vertex is the **maximal** one, the full power-bounded subring
([FJP] §5 (5.2) and the sentence before it: "Give every ring its maximal plus ring of
power-bounded elements"); `FiniteJet.isRingOfIntegralElements_powerBounded` applies
verbatim. These pieces need no uniformizer and stay instances, exactly as in the Laurent
template. -/

noncomputable instance : ValuationSpectrum.PlusSubring (JetA K) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetA K)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetB K) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetB K)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetC K) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetC K)⟩
noncomputable instance : ValuationSpectrum.PlusSubring (JetD K) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (JetD K)⟩

/-- The maximal plus ring is a ring of integral elements ([FJP] §5, the integral-closedness
argument after (5.2): `E°` is open, integrally closed, and power-bounded — boundedness is
not required). -/
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetA K) : Subring (JetA K))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetB K) : Subring (JetB K))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetC K) : Subring (JetC K))) :=
  isRingOfIntegralElements_powerBounded
instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (JetD K) : Subring (JetD K))) :=
  isRingOfIntegralElements_powerBounded

instance : IsUniformAddGroup (JetA K) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetB K) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetC K) := SeminormedAddCommGroup.to_isUniformAddGroup
instance : IsUniformAddGroup (JetD K) := SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (JetA K) (IsTopologicalAddGroup.rightUniformSpace (JetA K)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetB K) (IsTopologicalAddGroup.rightUniformSpace (JetB K)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetC K) (IsTopologicalAddGroup.rightUniformSpace (JetC K)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance
instance : @CompleteSpace (JetD K) (IsTopologicalAddGroup.rightUniformSpace (JetD K)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

end FiniteJetOver
