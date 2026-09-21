/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Gelfand
import LeanPool.SNumbers.SNumbers.Kolmogorov

/-!
# Injective and surjective `s`-number sequences

Two further structural properties of `s`-number sequences from Pietsch's
theory, alongside the axioms (S1)–(S5):

* An `s`-number sequence `s` is **injective** if it is unchanged by
  post-composition with a *metric injection* (an isometric embedding):
  `sₙ(J ∘ S) = sₙ(S)` for every metric injection `J`.
* It is **surjective** if it is unchanged by pre-composition with a
  *metric surjection* (a quotient map): `sₙ(S ∘ Q) = sₙ(S)` for every
  metric surjection `Q`.

## What is in this file

* `SNumbers.IsMetricInjection`, `SNumbers.IsMetricSurjection` — the two
  classes of maps, plus the key norm facts
  `‖J ∘ T‖ = ‖T‖` and `‖T ∘ Q‖ = ‖T‖`.
* `SNumbers.Injective`, `SNumbers.Surjective` — the two properties of a
  `Family`.
* `sn_comp_metricInjection_le`, `sn_comp_metricSurjection_le` — the "free"
  inequality `sₙ(J ∘ S) ≤ sₙ(S)` resp. `sₙ(S ∘ Q) ≤ sₙ(S)`, which holds
  for **every** `s`-number sequence (it is just the (S3) ideal property
  with `‖J‖ ≤ 1`, `‖Q‖ ≤ 1`). The reverse inequality is what
  injectivity / surjectivity actually assert.
* `injective_gelfandNumber` — the **Gelfand numbers** `cₙ` are injective.
* `surjective_kolmogorovNumber` — the **Kolmogorov numbers** `dₙ` are
  surjective.

## The landscape (Pietsch)

| sequence              | injective | surjective |
|-----------------------|-----------|------------|
| approximation `aₙ`    | no¹       | no¹        |
| Gelfand `cₙ`          | **yes**   | no         |
| Kolmogorov `dₙ`       | no        | **yes**    |
| Hilbert `hₙ`          |    ?      |    ?       |

¹ The approximation numbers are the *largest* `s`-numbers but are neither
injective nor surjective in general: their approximants must live in the
original spaces, so they cannot ignore an isometric enlargement of the
codomain (or a quotient of the domain). The injective/surjective *hulls*
of `aₙ` are exactly `cₙ` and `dₙ`, which is the reason those sequences are
introduced.

The two flagship facts (`cₙ` injective, `dₙ` surjective) are proved here in
full: the defining infima of `cₙ` and `dₙ` range over restriction- /
quotient-norms, and these are literally unchanged when `S` is composed with
an isometry / a metric surjection (`‖J ∘ T‖ = ‖T‖`, `‖T ∘ Q‖ = ‖T‖`), so
the infimum sets coincide.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-! ### Metric injections and metric surjections -/

/-- A **metric injection** is a norm-preserving (isometric) continuous
linear map: `‖J y‖ = ‖y‖` for all `y`. -/
def IsMetricInjection (J : Y →L[𝕜] Z) : Prop :=
  ∀ y, ‖J y‖ = ‖y‖

/-- A **metric surjection** is a continuous linear map `Q` that maps the
open unit ball *onto* the open unit ball: it is a contraction
(`‖Q‖ ≤ 1`) and every `x` has preimages of norm arbitrarily close to
`‖x‖`. This is exactly the quotient-map condition
`‖x‖ = inf {‖w‖ : Q w = x}`. -/
structure IsMetricSurjection (Q : W →L[𝕜] X) : Prop where
  /-- A metric surjection is a contraction. -/
  norm_le_one : ‖Q‖ ≤ 1
  /-- Every point has preimages of norm arbitrarily close to its own. -/
  exists_preimage_lt : ∀ (x : X) (ε : ℝ), 0 < ε → ∃ w : W, Q w = x ∧ ‖w‖ < ‖x‖ + ε

/-- A metric injection is a contraction: `‖J‖ ≤ 1`. -/
lemma IsMetricInjection.norm_le_one {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) :
    ‖J‖ ≤ 1 :=
  J.opNorm_le_bound zero_le_one fun y => by rw [hJ y, one_mul]

/-- Post-composition with a metric injection preserves the operator norm:
`‖J ∘ T‖ = ‖T‖`. -/
lemma IsMetricInjection.norm_comp {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J)
    (T : W →L[𝕜] Y) : ‖J.comp T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · -- `‖(J ∘ T) x‖ = ‖J (T x)‖ = ‖T x‖ ≤ ‖T‖ ‖x‖`.
    refine (J.comp T).opNorm_le_bound (norm_nonneg T) fun x => ?_
    rw [ContinuousLinearMap.comp_apply, hJ]
    exact T.le_opNorm x
  · -- `‖T x‖ = ‖J (T x)‖ = ‖(J ∘ T) x‖ ≤ ‖J ∘ T‖ ‖x‖`.
    refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    have h := (J.comp T).le_opNorm x
    rwa [ContinuousLinearMap.comp_apply, hJ] at h

/-- Pre-composition with a metric surjection preserves the operator norm:
`‖T ∘ Q‖ = ‖T‖`. -/
lemma IsMetricSurjection.norm_comp {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q)
    (T : X →L[𝕜] Y) : ‖T.comp Q‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · -- `‖T ∘ Q‖ ≤ ‖T‖ ‖Q‖ ≤ ‖T‖`.
    calc ‖T.comp Q‖
        ≤ ‖T‖ * ‖Q‖ := opNorm_comp_le _ _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hQ.norm_le_one (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  · -- `‖T x‖ ≤ ‖T ∘ Q‖ ‖x‖`: lift `x` to `w` with `‖w‖ ≈ ‖x‖`, then
    -- `‖T x‖ = ‖(T ∘ Q) w‖ ≤ ‖T ∘ Q‖ ‖w‖`, and let `ε → 0`.
    refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : (0 : ℝ) < ‖T.comp Q‖ + 1 := by positivity
    obtain ⟨w, hw, hwn⟩ := hQ.exists_preimage_lt x (ε / (‖T.comp Q‖ + 1)) (by positivity)
    calc ‖T x‖
        = ‖(T.comp Q) w‖ := by rw [ContinuousLinearMap.comp_apply, hw]
      _ ≤ ‖T.comp Q‖ * ‖w‖ := (T.comp Q).le_opNorm w
      _ ≤ ‖T.comp Q‖ * (‖x‖ + ε / (‖T.comp Q‖ + 1)) :=
          mul_le_mul_of_nonneg_left hwn.le (norm_nonneg (T.comp Q))
      _ = ‖T.comp Q‖ * ‖x‖ + ‖T.comp Q‖ / (‖T.comp Q‖ + 1) * ε := by ring
      _ ≤ ‖T.comp Q‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hpos]; linarith
      _ = ‖T.comp Q‖ * ‖x‖ + ε := by ring

/-! ### Injective / surjective `s`-number sequences -/

/-- An `s`-number sequence is **injective** if post-composition with any
metric injection leaves it unchanged: `sₙ(J ∘ S) = sₙ(S)`. -/
def Injective (s : Family 𝕜) : Prop :=
  ∀ {X Y Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
      (S : X →L[𝕜] Y) (J : Y →L[𝕜] Z), IsMetricInjection J → ∀ n : ℕ,
    s (J.comp S) n = s S n

/-- An `s`-number sequence is **surjective** if pre-composition with any
metric surjection leaves it unchanged: `sₙ(S ∘ Q) = sₙ(S)`. -/
def Surjective (s : Family 𝕜) : Prop :=
  ∀ {W X Y : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedAddCommGroup X] [NormedSpace 𝕜 X]
      [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      (S : X →L[𝕜] Y) (Q : W →L[𝕜] X), IsMetricSurjection Q → ∀ n : ℕ,
    s (S.comp Q) n = s S n

/-! ### The free inequality, valid for every `s`-number sequence -/

/-- For every `s`-number sequence, `sₙ(J ∘ S) ≤ sₙ(S)` when `J` is a metric
injection. (Just the (S3) ideal property with `‖J‖ ≤ 1`.) -/
theorem sn_comp_metricInjection_le {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) (n : ℕ) :
    s (J.comp S) n ≤ s S n := by
  have h := hs.ideal (ContinuousLinearMap.id 𝕜 X) S J n
  rw [ContinuousLinearMap.comp_id] at h
  have hsn := hs.nonneg S n
  have hidX : ‖ContinuousLinearMap.id 𝕜 X‖ ≤ 1 := norm_id_le
  have hb : ‖J‖ * s S n ≤ s S n := by nlinarith [hsn, hJ.norm_le_one, norm_nonneg J]
  have hba : ‖J‖ * s S n * ‖ContinuousLinearMap.id 𝕜 X‖ ≤ s S n := by
    nlinarith [hb, hidX, mul_nonneg (norm_nonneg J) hsn]
  linarith [h]

/-- For every `s`-number sequence, `sₙ(S ∘ Q) ≤ sₙ(S)` when `Q` is a metric
surjection. (Just the (S3) ideal property with `‖Q‖ ≤ 1`.) -/
theorem sn_comp_metricSurjection_le {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q) (n : ℕ) :
    s (S.comp Q) n ≤ s S n := by
  have h := hs.ideal Q S (ContinuousLinearMap.id 𝕜 Y) n
  rw [ContinuousLinearMap.id_comp] at h
  have hsn := hs.nonneg S n
  have hidY : ‖ContinuousLinearMap.id 𝕜 Y‖ ≤ 1 := norm_id_le
  have hb : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n ≤ s S n := by
    nlinarith [hsn, hidY, norm_nonneg (ContinuousLinearMap.id 𝕜 Y)]
  have hba : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n * ‖Q‖ ≤ s S n := by
    nlinarith [hb, hQ.norm_le_one, mul_nonneg (norm_nonneg (ContinuousLinearMap.id 𝕜 Y)) hsn,
      norm_nonneg Q]
  linarith [h]

/-! ### The Gelfand numbers are injective -/

/-- The restriction-norm defining `cₙ` is preserved by post-composition
with a metric injection: `‖(J ∘ S)|_M‖ = ‖S|_M‖`. -/
lemma deviationFromRestriction_comp_metricInjection {J : Y →L[𝕜] Z}
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction (J.comp S) M = deviationFromRestriction S M := by
  unfold deviationFromRestriction
  rw [ContinuousLinearMap.comp_assoc]
  exact hJ.norm_comp _

/-- `cₙ(J ∘ S) = cₙ(S)` for every metric injection `J`: the infimum sets
defining the two Gelfand numbers coincide term by term. -/
theorem gelfandNumber_comp_metricInjection {J : Y →L[𝕜] Z}
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber (J.comp S) n = gelfandNumber S n := by
  unfold gelfandNumber
  congr 1
  ext r
  simp only [gelfandSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨M, hcl, hrank, rfl⟩
    exact ⟨M, hcl, hrank, deviationFromRestriction_comp_metricInjection hJ S M⟩
  · rintro ⟨M, hcl, hrank, rfl⟩
    exact ⟨M, hcl, hrank, (deviationFromRestriction_comp_metricInjection hJ S M).symm⟩

/-- **The Gelfand numbers are an injective `s`-number sequence.** -/
theorem injective_gelfandNumber :
    Injective (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by
  intro X Y Z _ _ _ _ _ _ S J hJ n
  show gelfandNumber (J.comp S) n = gelfandNumber S n
  exact gelfandNumber_comp_metricInjection hJ S n

/-! ### The Kolmogorov numbers are surjective -/

/-- The quotient-norm defining `dₙ` is preserved by pre-composition with a
metric surjection: `‖π_V ∘ (S ∘ Q)‖ = ‖π_V ∘ S‖`.

This is just `IsMetricSurjection.norm_comp` applied to `T = π_V ∘ S`, but we
**inline** that argument with `T` abstracted by `set`: applying the generic
lemma directly forces the elaborator to re-infer the quotient instances
`NormedSpace 𝕜 (Y ⧸ V)` through a metavariable, which sends `whnf` into a
runaway search. With `T` opaque the same proof goes through at once. -/
lemma deviationFromSubspace_comp_metricSurjection {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp Q) V = deviationFromSubspace S V := by
  show ‖V.mkQL.comp (S.comp Q)‖ = ‖V.mkQL.comp S‖
  rw [← ContinuousLinearMap.comp_assoc]
  -- Abstract `T := π_V ∘ S` as an opaque operator and inline
  -- `IsMetricSurjection.norm_comp` (goal `‖T.comp Q‖ = ‖T‖`).
  generalize V.mkQL.comp S = T
  refine le_antisymm ?_ ?_
  · calc ‖T.comp Q‖
        ≤ ‖T‖ * ‖Q‖ := opNorm_comp_le _ _
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hQ.norm_le_one (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  · refine T.opNorm_le_bound (norm_nonneg (T.comp Q)) fun x => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : (0 : ℝ) < ‖T.comp Q‖ + 1 := by positivity
    obtain ⟨w, hw, hwn⟩ := hQ.exists_preimage_lt x (ε / (‖T.comp Q‖ + 1)) (by positivity)
    calc ‖T x‖
        = ‖(T.comp Q) w‖ := by rw [ContinuousLinearMap.comp_apply, hw]
      _ ≤ ‖T.comp Q‖ * ‖w‖ := (T.comp Q).le_opNorm w
      _ ≤ ‖T.comp Q‖ * (‖x‖ + ε / (‖T.comp Q‖ + 1)) :=
          mul_le_mul_of_nonneg_left hwn.le (norm_nonneg (T.comp Q))
      _ = ‖T.comp Q‖ * ‖x‖ + ‖T.comp Q‖ / (‖T.comp Q‖ + 1) * ε := by ring
      _ ≤ ‖T.comp Q‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hpos]; linarith
      _ = ‖T.comp Q‖ * ‖x‖ + ε := by ring

/-- `dₙ(S ∘ Q) = dₙ(S)` for every metric surjection `Q`: the infimum sets
defining the two Kolmogorov numbers coincide term by term. -/
theorem kolmogorovNumber_comp_metricSurjection {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S.comp Q) n = kolmogorovNumber S n := by
  unfold kolmogorovNumber
  congr 1
  ext r
  simp only [kolmogorovSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨V, hrank, rfl⟩
    exact ⟨V, hrank, deviationFromSubspace_comp_metricSurjection hQ S V⟩
  · rintro ⟨V, hrank, rfl⟩
    exact ⟨V, hrank, (deviationFromSubspace_comp_metricSurjection hQ S V).symm⟩

/-- **The Kolmogorov numbers are a surjective `s`-number sequence.** -/
theorem surjective_kolmogorovNumber :
    Surjective (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by
  intro W X Y _ _ _ _ _ _ S Q hQ n
  beta_reduce
  exact kolmogorovNumber_comp_metricSurjection hQ S n

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
