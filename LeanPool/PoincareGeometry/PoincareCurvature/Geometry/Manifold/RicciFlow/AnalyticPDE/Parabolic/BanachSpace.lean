/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Normed.Group.SeparationQuotient
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.SpecificLimits.Normed
/-!
# The parabolic `C^{0,α}` Banach space

`Parabolic/FunctionSpace.lean` exhibits the parabolic `C^{0,α}` functions on a time-space set `s` as a
**complete seminormed real vector space** (a semi-Banach space): the submodule
`parabolicC0AlphaSubmodule X E α s` carries the bundled seminormed structure
`parabolicC0AlphaSubmodule.seminormedAddCommGroup`, the completeness fact
`parabolicC0AlphaSubmodule.completeSpace`, and the scalar structure
`parabolicC0AlphaSubmodule.normedSpace`.  Those are supplied as `def`s rather than global instances
because the underlying function-space subtype already carries the *pointwise product* topology; the
seminorm topology has to live on a dedicated carrier that displaces it.

This module supplies that carrier and the resulting **genuine Banach space**.

* `ParabolicC0AlphaSpace X E α s` — a type synonym for the parabolic `C^{0,α}` submodule whose
  *canonical* `SeminormedAddCommGroup` / `NormedSpace ℝ` / `CompleteSpace` instances are the parabolic
  Hölder ones (not the ambient pointwise ones).  This is the semi-Banach space as a first-class type.
* `ParabolicC0AlphaBanach X E α s := SeparationQuotient (ParabolicC0AlphaSpace X E α s)` — the honest
  **separated** parabolic `C^{0,α}` normed space: functions modulo agreement on `s` (`‖·‖ = 0 ↔ · = 0`).
  Mathlib's separation-quotient machinery upgrades the complete seminormed structure to a genuine
  `NormedAddCommGroup` + `CompleteSpace` + `NormedSpace ℝ` — i.e. a **Banach space**.
* `ParabolicC0AlphaBanach.mk` — the quotient projection, with the norm readout
  `‖mk u‖ = parabolicC0AlphaNorm α u s`.

Everything is proved sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.  This closes
the "only point separation remains for the genuine Banach instance" gap for the parabolic Hölder
function space (the `C^0`-level function-space realisation the Ricci–DeTurck Banach chart consumes).
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : ℝ} {s : Set (ℝ × X)}

/-! ### Precomposition (change-of-variables) norm bounds

The operator underlying gluing across overlapping charts, the DeTurck gauge-diffeomorphism action,
and parabolic Schauder scaling is precomposition `u ↦ u ∘ φ` by a map `φ : ℝ × Y → ℝ × X` of the
space-time base.  The three lemmas below control the parabolic `C^{0,α}` norm of `u ∘ φ` when `φ`
maps `t` into `s` and expands parabolic distance by at most a factor `L`.  They are the norm-level
core the bounded precomposition operator `precompL` is built on (generalising `restrictL`, which is
the special case `φ = ` inclusion, `L = 1`). -/

/-- **Precomposition does not increase the parabolic sup norm.**  If `φ` maps `t` into `s`, then the
sup norm of `u ∘ φ` on `t` is at most the sup norm of `u` on `s`. -/
theorem parabolicSupNorm_comp_mapsTo {Y : Type*} [PseudoMetricSpace Y] {u : ℝ × X → E}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ∃ B ≥ (0 : ℝ), ParabolicBoundedWith B u s) (hmaps : Set.MapsTo φ t s) :
    parabolicSupNorm (fun p => u (φ p)) t ≤ parabolicSupNorm u s := by
  refine parabolicSupNorm_le (parabolicSupNorm_nonneg u s) ?_
  intro p hp
  exact (parabolicBoundedWith_parabolicSupNorm hu) (hmaps hp)

/-- **Precomposition scales the parabolic Hölder seminorm by `L ^ α`.**  If `φ` maps `t` into `s`
and `parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q`, then the Hölder seminorm of
`u ∘ φ` on `t` is at most `L ^ α` times the Hölder seminorm of `u` on `s`. -/
theorem parabolicHolderSeminorm_comp_parabolicDistanceLe {Y : Type*} [PseudoMetricSpace Y]
    {L : ℝ} {u : ℝ × X → E} {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicHolderOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ L ^ α * parabolicHolderSeminorm α u s := by
  have hbase : ParabolicHolderWith (parabolicHolderSeminorm α u s) α u s :=
    parabolicHolderWith_parabolicHolderSeminorm hu
  have hcomp : ParabolicHolderWith (parabolicHolderSeminorm α u s * L ^ α) α
      (fun p => u (φ p)) t :=
    hbase.comp_parabolicDistanceLe (parabolicHolderSeminorm_nonneg α u s) hα hL hmaps hφ
  have hle : parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ parabolicHolderSeminorm α u s * L ^ α :=
    parabolicHolderSeminorm_le
      (mul_nonneg (parabolicHolderSeminorm_nonneg α u s) (Real.rpow_nonneg hL α)) hcomp
  exact hle.trans_eq (mul_comm _ _)

/-- **The parabolic `C^{0,α}` norm of a precomposition.**  Combining the sup and Hölder bounds:
`‖u ∘ φ‖_{C^{0,α}(t)} ≤ max 1 (L ^ α) · ‖u‖_{C^{0,α}(s)}` when `φ` maps `t` into `s` and expands
parabolic distance by at most `L`.  For a parabolic-nonexpanding change of variables (`L ≤ 1`,
`0 ≤ α`) the factor is `1`, so precomposition is norm-nonincreasing. -/
theorem parabolicC0AlphaNorm_comp_parabolicDistanceLe_le {Y : Type*} [PseudoMetricSpace Y]
    {L : ℝ} {u : ℝ × X → E} {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hu : ParabolicC0AlphaOn α u s) (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    parabolicC0AlphaNorm α (fun p => u (φ p)) t
      ≤ max 1 (L ^ α) * parabolicC0AlphaNorm α u s := by
  have hsup : parabolicSupNorm (fun p => u (φ p)) t ≤ parabolicSupNorm u s :=
    parabolicSupNorm_comp_mapsTo hu.boundedOn hmaps
  have hhol : parabolicHolderSeminorm α (fun p => u (φ p)) t
      ≤ L ^ α * parabolicHolderSeminorm α u s :=
    parabolicHolderSeminorm_comp_parabolicDistanceLe hu.holderOn hα hL hmaps hφ
  have hBs : 0 ≤ parabolicSupNorm u s := parabolicSupNorm_nonneg u s
  have hHs : 0 ≤ parabolicHolderSeminorm α u s := parabolicHolderSeminorm_nonneg α u s
  have hmax1 : (1 : ℝ) ≤ max 1 (L ^ α) := le_max_left _ _
  have hmaxL : L ^ α ≤ max 1 (L ^ α) := le_max_right _ _
  have hsup' : parabolicSupNorm u s ≤ max 1 (L ^ α) * parabolicSupNorm u s := by
    have h := mul_le_mul_of_nonneg_right hmax1 hBs
    rwa [one_mul] at h
  have hhol' : L ^ α * parabolicHolderSeminorm α u s
      ≤ max 1 (L ^ α) * parabolicHolderSeminorm α u s :=
    mul_le_mul_of_nonneg_right hmaxL hHs
  have key : parabolicC0AlphaNorm α (fun p => u (φ p)) t
      ≤ parabolicSupNorm u s + L ^ α * parabolicHolderSeminorm α u s :=
    add_le_add hsup hhol
  refine key.trans ?_
  have hstep : parabolicSupNorm u s + L ^ α * parabolicHolderSeminorm α u s
      ≤ max 1 (L ^ α) * parabolicSupNorm u s
        + max 1 (L ^ α) * parabolicHolderSeminorm α u s := add_le_add hsup' hhol'
  refine hstep.trans_eq ?_
  unfold parabolicC0AlphaNorm
  ring

/-- **The semi-Banach carrier of the parabolic `C^{0,α}` space.**  A type synonym for
`parabolicC0AlphaSubmodule X E α s` whose canonical topology/uniformity is the parabolic `C^{0,α}`
seminorm one, isolating it from the ambient pointwise product topology on the underlying function
subtype. -/
def ParabolicC0AlphaSpace (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (s : Set (ℝ × X)) : Type _ :=
  parabolicC0AlphaSubmodule X E α s

namespace ParabolicC0AlphaSpace

/-- Reinterpret a parabolic `C^{0,α}` submodule element on the seminormed carrier (identity map). -/
def ofSubmodule (u : parabolicC0AlphaSubmodule X E α s) : ParabolicC0AlphaSpace X E α s := u

/-- Recover the parabolic `C^{0,α}` submodule element underneath a seminormed carrier element
(identity map). -/
def toSubmodule (u : ParabolicC0AlphaSpace X E α s) : parabolicC0AlphaSubmodule X E α s := u

/-- The underlying time-space function of a seminormed parabolic `C^{0,α}` element. -/
def toFun (u : ParabolicC0AlphaSpace X E α s) : (ℝ × X) → E := (toSubmodule u : (ℝ × X) → E)

/-- The parabolic `C^{0,α}` seminormed additive-group structure is the canonical additive-group
structure on the carrier. -/
noncomputable instance : SeminormedAddCommGroup (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.seminormedAddCommGroup (X := X) (E := E) α s

/-- The parabolic `C^{0,α}` scalar structure is the canonical `ℝ`-module normed structure on the
carrier. -/
noncomputable instance : NormedSpace ℝ (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.normedSpace (X := X) (E := E) α s

/-- With `E` complete, the parabolic `C^{0,α}` semi-normed carrier is complete: a `C^{0,α}`-Cauchy
sequence of parabolic `C^{0,α}` functions converges in the `C^{0,α}` norm. -/
instance [CompleteSpace E] : CompleteSpace (ParabolicC0AlphaSpace X E α s) :=
  parabolicC0AlphaSubmodule.completeSpace (X := X) (E := E) α s

/-- The carrier norm is the parabolic `C^{0,α}` norm of the underlying function. -/
theorem norm_def (u : ParabolicC0AlphaSpace X E α s) :
    ‖u‖ = parabolicC0AlphaNorm α (toFun u) s :=
  rfl

/-- Distance on the carrier is the parabolic `C^{0,α}` norm of the pointwise difference. -/
theorem dist_def (u v : ParabolicC0AlphaSpace X E α s) :
    dist u v = parabolicC0AlphaNorm α (fun z => toFun u z - toFun v z) s :=
  parabolicC0AlphaSubmodule.seminormedAddCommGroup_dist (X := X) (E := E) α s u v

/-- Restriction to a subset `t ⊆ s`, as a linear map on the seminormed carriers (it does not change
the underlying function, only the domain of the parabolic estimates). -/
def restrictLM {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaSpace X E α s →ₗ[ℝ] ParabolicC0AlphaSpace X E α t :=
  parabolicC0AlphaSubmodule.restrictLinearMap hts

@[simp]
theorem toFun_restrictLM {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    toFun (restrictLM hts u) = toFun u :=
  rfl

/-- **Restriction is norm-nonincreasing.**  Restriction to a subset `t ⊆ s` is a bounded linear map
of operator norm `≤ 1` on the seminormed carriers (`parabolicC0AlphaNorm_mono_domain`). -/
noncomputable def restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace X E α t :=
  LinearMap.mkContinuous (restrictLM hts) 1 (fun u => by
    rw [one_mul]
    show parabolicC0AlphaNorm α (toFun (restrictLM hts u)) t ≤ parabolicC0AlphaNorm α (toFun u) s
    rw [toFun_restrictLM]
    exact parabolicC0AlphaNorm_mono_domain hts (toSubmodule u).2)

@[simp]
theorem toFun_restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    toFun (restrictL hts u) = toFun u :=
  rfl

/-- The restriction operator on the carrier has operator norm `≤ 1`. -/
theorem norm_restrictL_le {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ‖restrictL (X := X) (E := E) (α := α) (s := s) (t := t) hts‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ParabolicC0AlphaSpace

/-- **The parabolic `C^{0,α}` Banach space.**  The separation quotient of the complete seminormed
carrier `ParabolicC0AlphaSpace X E α s`: parabolic `C^{0,α}` functions on `s` identified when they
agree on `s` (equivalently, when their difference has zero parabolic `C^{0,α}` norm).  Mathlib's
`SeparationQuotient` upgrades the complete *seminormed* structure to a genuine `NormedAddCommGroup`
(point separation) while preserving completeness and the `ℝ`-vector-space structure, exhibiting the
parabolic Hölder space as an honest **Banach space**. -/
def ParabolicC0AlphaBanach (X E : Type*) [PseudoMetricSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (α : ℝ) (s : Set (ℝ × X)) : Type _ :=
  SeparationQuotient (ParabolicC0AlphaSpace X E α s)

namespace ParabolicC0AlphaBanach

/-- The genuine (separated) normed additive group structure of the parabolic `C^{0,α}` Banach space. -/
noncomputable instance : NormedAddCommGroup (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (NormedAddCommGroup (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- The parabolic `C^{0,α}` Banach space is an `ℝ`-normed vector space. -/
noncomputable instance : NormedSpace ℝ (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (NormedSpace ℝ (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- With `E` complete, the parabolic `C^{0,α}` Banach space is complete — a genuine Banach space. -/
instance [CompleteSpace E] : CompleteSpace (ParabolicC0AlphaBanach X E α s) :=
  inferInstanceAs (CompleteSpace (SeparationQuotient (ParabolicC0AlphaSpace X E α s)))

/-- The Banach-space quotient projection: send a parabolic `C^{0,α}` function to its class modulo
agreement on `s`. -/
def mk (u : ParabolicC0AlphaSpace X E α s) : ParabolicC0AlphaBanach X E α s :=
  SeparationQuotient.mk u

/-- The projection is surjective. -/
theorem mk_surjective : Function.Surjective (mk : ParabolicC0AlphaSpace X E α s → _) :=
  SeparationQuotient.surjective_mk

/-- **Norm readout of the projection.**  The Banach norm of the class of `u` is the parabolic
`C^{0,α}` norm of the underlying function — the quotient is *isometric* on representatives. -/
theorem norm_mk (u : ParabolicC0AlphaSpace X E α s) :
    ‖mk u‖ = parabolicC0AlphaNorm α (ParabolicC0AlphaSpace.toFun u) s := by
  change ‖SeparationQuotient.mk u‖ = _
  rw [SeparationQuotient.norm_mk, ParabolicC0AlphaSpace.norm_def]

/-- **Norm readout on submodule representatives.**  The Banach norm of the class of a parabolic
`C^{0,α}` submodule element is the parabolic `C^{0,α}` norm of its underlying function. -/
theorem norm_mk_ofSubmodule (u : parabolicC0AlphaSubmodule X E α s) :
    ‖mk (ParabolicC0AlphaSpace.ofSubmodule u)‖ = parabolicC0AlphaNorm α (u : (ℝ × X) → E) s :=
  norm_mk (ParabolicC0AlphaSpace.ofSubmodule u)

/-- **Point separation.**  Two representatives project to the same Banach class iff their difference
has zero parabolic `C^{0,α}` norm, i.e. they agree (in the `C^{0,α}` sense) on `s`. -/
theorem mk_eq_mk_iff (u v : ParabolicC0AlphaSpace X E α s) :
    mk u = mk v ↔ parabolicC0AlphaNorm α (fun z => ParabolicC0AlphaSpace.toFun u z
        - ParabolicC0AlphaSpace.toFun v z) s = 0 := by
  change SeparationQuotient.mk u = SeparationQuotient.mk v ↔ _
  rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff, ParabolicC0AlphaSpace.dist_def]

/-- **The projection as a continuous `ℝ`-linear map.**  `mk` packaged as a bounded operator
`ParabolicC0AlphaSpace →L[ℝ] ParabolicC0AlphaBanach` (`SeparationQuotient.mkCLM`). -/
def mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s :=
  SeparationQuotient.mkCLM ℝ (ParabolicC0AlphaSpace X E α s)

@[simp]
theorem mkL_apply (u : ParabolicC0AlphaSpace X E α s) : mkL u = mk u := rfl

/-- The projection operator has operator norm `≤ 1` (it is `1`-Lipschitz; in fact norm-preserving on
representatives, `norm_mk`). -/
theorem norm_mkL_le : ‖(mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] _)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
  rw [one_mul, mkL_apply]
  exact le_of_eq (SeparationQuotient.norm_mk u)

/-- **A continuous `ℝ`-linear section of the projection.**  `SeparationQuotient.outCLM` chooses, for
each Banach class, a representative parabolic `C^{0,α}` function, continuously and linearly, with
`mk (outL x) = x`. -/
noncomputable def outL : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaSpace X E α s :=
  SeparationQuotient.outCLM ℝ (ParabolicC0AlphaSpace X E α s)

/-- The section is a right inverse of the projection: `mk (outL x) = x`. -/
@[simp]
theorem mk_outL (x : ParabolicC0AlphaBanach X E α s) : mk (outL x) = x :=
  SeparationQuotient.mk_outCLM ℝ x

/-- The projection composed with the section is the identity. -/
theorem mkL_comp_outL :
    (mkL : ParabolicC0AlphaSpace X E α s →L[ℝ] _).comp outL = ContinuousLinearMap.id ℝ _ :=
  SeparationQuotient.mkCLM_comp_outCLM ℝ (ParabolicC0AlphaSpace X E α s)

/-- **The section is an isometry.**  `‖outL x‖ = ‖x‖`: the parabolic `C^{0,α}` norm of the chosen
representative equals the Banach norm of the class (the projection is norm-preserving, so its section
is an isometric linear embedding of the Banach space into the semi-Banach carrier). -/
theorem norm_outL (x : ParabolicC0AlphaBanach X E α s) : ‖outL x‖ = ‖x‖ := by
  conv_rhs => rw [← mk_outL x]
  exact (SeparationQuotient.norm_mk (outL x)).symm

/-- The section is injective. -/
theorem outL_injective :
    Function.Injective (outL : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaSpace X E α s) :=
  Function.LeftInverse.injective mk_outL

/-- **Restriction descends to the Banach spaces.**  Restriction to a subset `t ⊆ s` — well-defined on
classes because it is norm-nonincreasing, so it sends functions that agree on `s` to functions that
agree on `t` — is a bounded operator `ParabolicC0AlphaBanach … s →L[ℝ] ParabolicC0AlphaBanach … t`
(`SeparationQuotient.liftCLM` of the composite `mk ∘ (carrier restriction)`). -/
noncomputable def restrictL {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α t :=
  SeparationQuotient.liftCLM ((mkL (s := t)).comp (ParabolicC0AlphaSpace.restrictL hts))
    (fun u u' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.restrictL hts u)
          (ParabolicC0AlphaSpace.restrictL hts u') ≤ dist u u' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        calc ‖ParabolicC0AlphaSpace.restrictL hts (u - u')‖
            ≤ ‖ParabolicC0AlphaSpace.restrictL hts‖ * ‖u - u'‖ :=
              (ParabolicC0AlphaSpace.restrictL hts).le_opNorm _
          _ ≤ 1 * ‖u - u'‖ := by
              gcongr; exact ParabolicC0AlphaSpace.norm_restrictL_le hts
          _ = ‖u - u'‖ := one_mul _
      exact le_antisymm (hle.trans h0.le) dist_nonneg)

/-- **Restriction commutes with the projection.**  On the class of a representative `u`, restriction
is the class of the restricted representative. -/
@[simp]
theorem restrictL_mk {t : Set (ℝ × X)} (hts : t ⊆ s) (u : ParabolicC0AlphaSpace X E α s) :
    restrictL hts (mk u) = mk (ParabolicC0AlphaSpace.restrictL hts u) :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The restriction operator on the Banach spaces has operator norm `≤ 1`. -/
theorem norm_restrictL_le {t : Set (ℝ × X)} (hts : t ⊆ s) :
    ‖restrictL (X := X) (E := E) (α := α) (s := s) (t := t) hts‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [one_mul, restrictL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_restrictL]
  exact parabolicC0AlphaNorm_mono_domain hts (ParabolicC0AlphaSpace.toSubmodule u).2

end ParabolicC0AlphaBanach

namespace ParabolicC0AlphaSpace

/-- **Restriction to the full domain is the identity (pointwise).**  Restricting a carrier element
along `s ⊆ s` returns the same element (the underlying function is unchanged and the parabolic
`C^{0,α}` witness is proof-irrelevant). -/
@[simp]
theorem restrictL_self_apply (u : ParabolicC0AlphaSpace X E α s) :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s) u = u :=
  Subtype.ext rfl

/-- **Restriction is functorial (projective system), pointwise.**  Restricting a carrier element
from `s` to `t` and then to `r ⊆ t` gives the same element as restricting directly from `s` to
`r`. -/
@[simp]
theorem restrictL_comp_apply {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t)
    (u : ParabolicC0AlphaSpace X E α s) :
    restrictL hrt (restrictL hts u) = restrictL (hrt.trans hts) u :=
  Subtype.ext rfl

/-- **Restriction to the full domain is the identity operator.** -/
theorem restrictL_self :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaSpace X E α s) := by
  ext u
  simp

/-- **Restriction is functorial (projective system) at the operator level.**  The parabolic
`C^{0,α}` restriction operators form a projective system: `restrictL (r ⊆ t)` composed with
`restrictL (t ⊆ s)` is `restrictL (r ⊆ s)`. -/
theorem restrictL_comp {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t) :
    (restrictL hrt).comp (restrictL hts)
      = restrictL (X := X) (E := E) (α := α) (s := s) (hrt.trans hts) := by
  ext u
  simp

/-- **Point evaluation at a space-time point, as a linear map on the carrier.**  Reads off the value
`u z` of a parabolic `C^{0,α}` function; it is linear because the carrier's additive/scalar
operations are the pointwise ones on the underlying function (composition of the submodule inclusion
with `Pi` evaluation). -/
def evalLM (z : ℝ × X) : ParabolicC0AlphaSpace X E α s →ₗ[ℝ] E :=
  (LinearMap.proj z).comp (parabolicC0AlphaSubmodule X E α s).subtype

@[simp]
theorem evalLM_apply (z : ℝ × X) (u : ParabolicC0AlphaSpace X E α s) :
    evalLM z u = toFun u z :=
  rfl

/-- **Point evaluation at `z ∈ s` is a bounded linear functional** on the parabolic `C^{0,α}`
carrier, of operator norm `≤ 1`: the value `u z` is dominated by the parabolic `C^{0,α}` norm.  (The
sup part of the norm already controls the pointwise value on `s`.) -/
noncomputable def evalCLM (z : ℝ × X) (hz : z ∈ s) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] E :=
  LinearMap.mkContinuous (evalLM z) 1 (fun u => by
    rw [one_mul, norm_def]
    exact norm_le_parabolicC0AlphaNorm ((toSubmodule u).2).boundedOn hz)

@[simp]
theorem evalCLM_apply (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz u = toFun u z :=
  rfl

/-- **Pointwise domination for the carrier evaluation:** `‖u z‖ ≤ ‖u‖` for `z ∈ s`. -/
theorem norm_evalCLM_apply_le (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    ‖evalCLM z hz u‖ ≤ ‖u‖ := by
  rw [norm_def]
  exact norm_le_parabolicC0AlphaNorm ((toSubmodule u).2).boundedOn hz

/-- Point evaluation on the carrier has operator norm `≤ 1`. -/
theorem norm_evalCLM_le (z : ℝ × X) (hz : z ∈ s) :
    ‖evalCLM (X := X) (E := E) (α := α) (s := s) z hz‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Point evaluation is compatible with restriction (cone coherence, pointwise).**  The parabolic
`C^{0,α}` point-evaluation functionals are a compatible cone over the restriction projective system:
evaluating at `z ∈ t` after restricting to `t ⊆ s` equals evaluating at `z` on `s` (stated
pointwise; both sides read off the underlying value `u z`). -/
@[simp]
theorem evalCLM_restrictL_apply {t : Set (ℝ × X)} (hts : t ⊆ s) (z : ℝ × X) (hz : z ∈ t)
    (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (restrictL hts u) = evalCLM z (hts hz) u :=
  rfl

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Restriction to the full domain is the identity (pointwise) on the Banach space.** -/
@[simp]
theorem restrictL_self_apply (x : ParabolicC0AlphaBanach X E α s) :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s) x = x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, ParabolicC0AlphaSpace.restrictL_self_apply]

/-- **Restriction is functorial (projective system), pointwise, on the Banach space.** -/
@[simp]
theorem restrictL_comp_apply {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t)
    (x : ParabolicC0AlphaBanach X E α s) :
    restrictL hrt (restrictL hts x) = restrictL (hrt.trans hts) x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, restrictL_mk, restrictL_mk,
    ParabolicC0AlphaSpace.restrictL_comp_apply]

/-- **Restriction to the full domain is the identity operator on the Banach space.** -/
theorem restrictL_self :
    restrictL (X := X) (E := E) (α := α) (s := s) (Set.Subset.refl s)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaBanach X E α s) := by
  ext x
  simp

/-- **Restriction is functorial (projective system) at the operator level on the Banach space.**
The parabolic `C^{0,α}` Banach restriction operators form a projective system: `restrictL (r ⊆ t)`
composed with `restrictL (t ⊆ s)` is `restrictL (r ⊆ s)`.  This is the categorical data that gluing
of local Ricci–DeTurck Banach-chart solutions across overlapping charts (the chart-closure data)
consumes. -/
theorem restrictL_comp {t r : Set (ℝ × X)} (hts : t ⊆ s) (hrt : r ⊆ t) :
    (restrictL hrt).comp (restrictL hts)
      = restrictL (X := X) (E := E) (α := α) (s := s) (hrt.trans hts) := by
  ext x
  simp

/-- **Point evaluation at `z ∈ s` descends to the Banach space.**  Two parabolic `C^{0,α}` functions
identified in the separation quotient (they agree on `s`, having zero-norm difference) have the same
value at any `z ∈ s`, so point evaluation is well defined on classes — a bounded linear functional
`ParabolicC0AlphaBanach X E α s →L[ℝ] E` of operator norm `≤ 1`.  This is the functional that reads
off the value of a Ricci–DeTurck Banach-chart solution at a space-time point. -/
noncomputable def evalCLM (z : ℝ × X) (hz : z ∈ s) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] E :=
  SeparationQuotient.liftCLM
    (M := ParabolicC0AlphaSpace X E α s) (N := E) (R := ℝ) (S := ℝ) (σ := RingHom.id ℝ)
    (ParabolicC0AlphaSpace.evalCLM z hz)
    (fun (u u' : ParabolicC0AlphaSpace X E α s) (hins : Inseparable u u') => by
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hz0 : ‖u - u'‖ = 0 := by rw [← dist_eq_norm]; exact h0
      have hb : ‖ParabolicC0AlphaSpace.evalCLM z hz (u - u')‖ ≤ ‖u - u'‖ :=
        ParabolicC0AlphaSpace.norm_evalCLM_apply_le z hz (u - u')
      rw [hz0] at hb
      have hb0 : ParabolicC0AlphaSpace.evalCLM z hz (u - u') = 0 := norm_le_zero_iff.mp hb
      rw [map_sub, sub_eq_zero] at hb0
      exact hb0)

/-- On the class of a representative `u`, point evaluation is the value of that representative. -/
@[simp]
theorem evalCLM_mk (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (mk u) = ParabolicC0AlphaSpace.evalCLM z hz u :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The value of point evaluation on a class is the value of any representative at `z`. -/
theorem evalCLM_mk_apply (z : ℝ × X) (hz : z ∈ s) (u : ParabolicC0AlphaSpace X E α s) :
    evalCLM z hz (mk u) = ParabolicC0AlphaSpace.toFun u z :=
  rfl

/-- Point evaluation on the Banach space has operator norm `≤ 1`. -/
theorem norm_evalCLM_le (z : ℝ × X) (hz : z ∈ s) :
    ‖evalCLM (X := X) (E := E) (α := α) (s := s) z hz‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [one_mul, evalCLM_mk, norm_mk]
  exact ParabolicC0AlphaSpace.norm_evalCLM_apply_le z hz u

/-- The Banach norm is a simultaneous Hölder constant for the canonical
point-evaluation representative on the defining domain. -/
theorem eval_parabolicHolderWith
    (q : ParabolicC0AlphaBanach X E α s) :
    ParabolicHolderWith ‖q‖ α
      (ParabolicC0AlphaSpace.toFun (outL q)) s := by
  intro p hp z hz
  have h := norm_sub_le_parabolicC0AlphaNorm_mul
    (ParabolicC0AlphaSpace.toSubmodule (outL q)).2.holderOn hp hz
  have hn : parabolicC0AlphaNorm α
      (↑(ParabolicC0AlphaSpace.toSubmodule (outL q)) : (ℝ × X) → E) s = ‖q‖ := by
    change parabolicC0AlphaNorm α
      (ParabolicC0AlphaSpace.toFun (outL q)) s = ‖q‖
    exact (ParabolicC0AlphaSpace.norm_def (outL q)).symm.trans (norm_outL q)
  rw [hn] at h
  exact h

/-- Pointwise form of `eval_parabolicHolderWith`, avoiding the junk value
outside the defining domain. -/
theorem norm_eval_sub_eval_le
    (q : ParabolicC0AlphaBanach X E α s)
    {p z : ℝ × X} (hp : p ∈ s) (hz : z ∈ s) :
    ‖evalCLM p hp q - evalCLM z hz q‖ ≤
      ‖q‖ * parabolicDistance p z ^ α := by
  have hpval : evalCLM p hp q =
      ParabolicC0AlphaSpace.toFun (outL q) p := by
    calc
      evalCLM p hp q = evalCLM p hp (mk (outL q)) := by rw [mk_outL]
      _ = _ := evalCLM_mk_apply p hp (outL q)
  have hzval : evalCLM z hz q =
      ParabolicC0AlphaSpace.toFun (outL q) z := by
    calc
      evalCLM z hz q = evalCLM z hz (mk (outL q)) := by rw [mk_outL]
      _ = _ := evalCLM_mk_apply z hz (outL q)
  rw [hpval, hzval]
  exact q.eval_parabolicHolderWith hp hz

/-- Two Banach classes are equal when their canonical point evaluations agree
throughout the defining domain. -/
theorem eq_of_eval_eq (q r : ParabolicC0AlphaBanach X E α s)
    (h : ∀ (z : ℝ × X) (hz : z ∈ s), evalCLM z hz q = evalCLM z hz r) :
    q = r := by
  obtain ⟨u, rfl⟩ := mk_surjective q
  obtain ⟨v, rfl⟩ := mk_surjective r
  apply (mk_eq_mk_iff u v).2
  apply (parabolicC0AlphaNorm_sub_eq_zero_iff_eqOn
    (ParabolicC0AlphaSpace.toSubmodule u).2
    (ParabolicC0AlphaSpace.toSubmodule v).2).2
  intro z hz
  change ParabolicC0AlphaSpace.toFun u z =
    ParabolicC0AlphaSpace.toFun v z
  simpa only [evalCLM_mk_apply] using h z hz

/-- **Point evaluation is compatible with restriction (cone coherence, pointwise) on the Banach
space.**  The parabolic `C^{0,α}` Banach point-evaluation functionals are a compatible cone over the
restriction projective system — the coherence that keeps the point-values of glued Ricci–DeTurck
Banach-chart solutions consistent across overlapping charts. -/
@[simp]
theorem evalCLM_restrictL_apply {t : Set (ℝ × X)} (hts : t ⊆ s) (z : ℝ × X) (hz : z ∈ t)
    (x : ParabolicC0AlphaBanach X E α s) :
    evalCLM z hz (restrictL hts x) = evalCLM z (hts hz) x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [restrictL_mk, evalCLM_mk, evalCLM_mk,
    ParabolicC0AlphaSpace.evalCLM_restrictL_apply]

/-- **The point-evaluation functionals separate points of the Banach space.**  A parabolic `C^{0,α}`
Banach element is completely determined by its values at the space-time points of `s`: two classes
are equal iff they agree under every point-evaluation `evalCLM z hz` (`z ∈ s`).  Equivalently, the
Banach space is faithfully represented by the family of its values on `s` — the fact that a
Ricci–DeTurck Banach-chart solution is determined by its space-time values. -/
theorem eq_iff_forall_evalCLM (x y : ParabolicC0AlphaBanach X E α s) :
    x = y ↔ ∀ (z : ℝ × X) (hz : z ∈ s), evalCLM z hz x = evalCLM z hz y := by
  constructor
  · rintro rfl z hz; rfl
  · intro h
    obtain ⟨u, rfl⟩ := mk_surjective x
    obtain ⟨v, rfl⟩ := mk_surjective y
    have hpt : ∀ z ∈ s, ParabolicC0AlphaSpace.toFun u z = ParabolicC0AlphaSpace.toFun v z := by
      intro z hz
      have hz' := h z hz
      rwa [evalCLM_mk_apply, evalCLM_mk_apply] at hz'
    rw [mk_eq_mk_iff]
    set w : ℝ × X → E :=
      fun z => ParabolicC0AlphaSpace.toFun u z - ParabolicC0AlphaSpace.toFun v z with hw
    have hw0 : ∀ z ∈ s, w z = 0 := fun z hz => by
      simp only [hw, sub_eq_zero]; exact hpt z hz
    have hbound : ParabolicC0AlphaWith 0 0 α w s :=
      ⟨fun p hp => by simp [hw0 p hp], fun p hp q hq => by simp [hw0 p hp, hw0 q hq]⟩
    have hle : parabolicC0AlphaNorm α w s ≤ 0 := by
      simpa using parabolicC0AlphaNorm_le (le_refl 0) (le_refl 0) hbound
    exact le_antisymm hle (parabolicC0AlphaNorm_nonneg α w s)

end ParabolicC0AlphaBanach

namespace ParabolicC0AlphaSpace

/-- **Fiberwise post-composition with a continuous linear value map, on the seminormed carrier.**
Sends a parabolic `C^{0,α}` function `u` to `z ↦ L (u z)`, as an `ℝ`-linear map of the carriers
(reuses `parabolicC0AlphaSubmodule.continuousLinearMap`). -/
def compLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaSpace X E α s →ₗ[ℝ] ParabolicC0AlphaSpace X F α s :=
  parabolicC0AlphaSubmodule.continuousLinearMap L

@[simp]
theorem toFun_compLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (compLM L u) = fun z => L (toFun u z) :=
  rfl

/-- **Fiberwise post-composition is a bounded operator of norm `≤ ‖L‖` on the carriers.**  Applying a
continuous linear value map `L : E →L[ℝ] F` pointwise to a parabolic `C^{0,α}` function is a bounded
`ℝ`-linear map `ParabolicC0AlphaSpace … E … →L[ℝ] ParabolicC0AlphaSpace … F …` of operator norm
`≤ ‖L‖` (`parabolicC0AlphaNorm_continuousLinearMap_le`). -/
noncomputable def compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace X F α s :=
  LinearMap.mkContinuous (compLM L) ‖L‖ (fun u => by
    show parabolicC0AlphaNorm α (fun z => L (toFun u z)) s ≤ ‖L‖ * parabolicC0AlphaNorm α (toFun u) s
    exact parabolicC0AlphaNorm_continuousLinearMap_le L (toSubmodule u).2)

@[simp]
theorem toFun_compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (compL L u) = fun z => L (toFun u z) :=
  rfl

/-- The carrier post-composition operator has operator norm `≤ ‖L‖`. -/
theorem norm_compL_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ‖compL (X := X) (E := E) (α := α) (s := s) (F := F) L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Fiberwise post-composition descends to the Banach spaces.**  Applying a continuous linear value
map `L : E →L[ℝ] F` pointwise is well defined on Banach classes — it is `‖L‖`-Lipschitz, so it sends
functions that agree on `s` to functions that agree on `s` — giving a bounded operator
`ParabolicC0AlphaBanach … E … →L[ℝ] ParabolicC0AlphaBanach … F …`
(`SeparationQuotient.liftCLM` of `mk ∘ (carrier post-composition)`).  This is the functional-analytic
operation of applying a fiberwise bundle morphism / coordinate change to a Ricci–DeTurck Banach-chart
solution. -/
noncomputable def compL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X F α s :=
  SeparationQuotient.liftCLM (mkL.comp (ParabolicC0AlphaSpace.compL L))
    (fun u u' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.compL L u) (ParabolicC0AlphaSpace.compL L u')
          ≤ ‖L‖ * dist u u' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        calc ‖ParabolicC0AlphaSpace.compL L (u - u')‖
            ≤ ‖ParabolicC0AlphaSpace.compL L‖ * ‖u - u'‖ :=
              (ParabolicC0AlphaSpace.compL L).le_opNorm _
          _ ≤ ‖L‖ * ‖u - u'‖ := by
              gcongr; exact ParabolicC0AlphaSpace.norm_compL_le L
      exact le_antisymm (hle.trans (le_of_eq (by rw [h0, mul_zero]))) dist_nonneg)

/-- **Post-composition commutes with the projection.**  On the class of a representative `u`,
post-composition is the class of the post-composed representative. -/
@[simp]
theorem compL_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (u : ParabolicC0AlphaSpace X E α s) :
    compL L (mk u) = mk (ParabolicC0AlphaSpace.compL L u) :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The Banach post-composition operator has operator norm `≤ ‖L‖`. -/
theorem norm_compL_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ‖compL (X := X) (E := E) (α := α) (s := s) (F := F) L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [compL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_compL]
  exact parabolicC0AlphaNorm_continuousLinearMap_le L (ParabolicC0AlphaSpace.toSubmodule u).2

/-- **Point evaluation of a post-composed class is the value map applied to the point value (cone
coherence with the fiber map).**  Reading off the space-time value of a Ricci–DeTurck chart solution
after applying a fiberwise bundle morphism `L` is `L` applied to the value of the original solution. -/
@[simp]
theorem evalCLM_compL_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (z : ℝ × X) (hz : z ∈ s) (x : ParabolicC0AlphaBanach X E α s) :
    evalCLM z hz (compL L x) = L (evalCLM z hz x) := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  simp only [compL_mk, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_compL]

/-- **Post-composition by the identity is the identity operator.** -/
theorem compL_id :
    compL (X := X) (E := E) (α := α) (s := s) (ContinuousLinearMap.id ℝ E)
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaBanach X E α s) := by
  ext x
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.id_apply, compL_mk]
  rfl

/-- **Post-composition is functorial in the value map (composition).**  Applying `L₂ ∘ L₁` fiberwise
is applying `L₁` and then `L₂` — the parabolic `C^{0,α}` Banach post-composition operators form a
covariant functor of the value space. -/
theorem compL_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L₂ : F →L[ℝ] G) (L₁ : E →L[ℝ] F) :
    compL (X := X) (α := α) (s := s) (L₂.comp L₁)
      = (compL L₂).comp (compL L₁) := by
  ext x
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.comp_apply, compL_mk, compL_mk, compL_mk]
  rfl

end ParabolicC0AlphaBanach

/-- **Self-bound: the parabolic `C^{0,α}` norm is an admissible `ParabolicC0AlphaNormLe` bound.**  Its
own sup norm and Hölder seminorm are simultaneously achieved (`parabolicC0AlphaWith_parabolicSupNorm_…`)
and sum to the parabolic `C^{0,α}` norm. -/
theorem parabolicC0AlphaNormLe_norm {u : ℝ × X → E} (hu : ParabolicC0AlphaOn α u s) :
    ParabolicC0AlphaNormLe (parabolicC0AlphaNorm α u s) α u s :=
  ⟨parabolicSupNorm u s, parabolicSupNorm_nonneg u s,
    parabolicHolderSeminorm α u s, parabolicHolderSeminorm_nonneg α u s, le_of_eq rfl,
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu⟩

/-- **`ParabolicC0AlphaNormLe` dominates the parabolic `C^{0,α}` norm.**  Any admissible combined bound
`N` is at least the parabolic `C^{0,α}` norm. -/
theorem parabolicC0AlphaNorm_le_of_normLe {N : ℝ} {u : ℝ × X → E}
    (h : ParabolicC0AlphaNormLe N α u s) : parabolicC0AlphaNorm α u s ≤ N := by
  obtain ⟨B, hB, H, hH, hsum, hctrl⟩ := h
  exact (parabolicC0AlphaNorm_le hB hH hctrl).trans hsum

/-- **Bilinear multiplication bound.**  For a continuous bilinear map `L : E →L[ℝ] F →L[ℝ] G`, the
pointwise product `z ↦ L (a z) (v z)` obeys the parabolic `C^{0,α}` algebra estimate
`‖L(a,v)‖_{C^{0,α}} ≤ ‖L‖ · ‖a‖_{C^{0,α}} · ‖v‖_{C^{0,α}}` (the operator form of the parabolic
`C^{0,α}` product inequality that a Ricci–DeTurck coefficient multiplication consumes). -/
theorem parabolicC0AlphaNorm_continuousLinearMap₂_le {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    {a : ℝ × X → E} {v : ℝ × X → F} (ha : ParabolicC0AlphaOn α a s) (hv : ParabolicC0AlphaOn α v s) :
    parabolicC0AlphaNorm α (fun z => L (a z) (v z)) s
      ≤ ‖L‖ * parabolicC0AlphaNorm α a s * parabolicC0AlphaNorm α v s :=
  parabolicC0AlphaNorm_le_of_normLe
    ((parabolicC0AlphaNormLe_norm ha).continuousLinearMap₂ L (parabolicC0AlphaNormLe_norm hv))

namespace parabolicC0AlphaSubmodule

/-- **Frozen-coefficient bilinear multiplication as a linear map on the submodules.**  For a fixed
parabolic `C^{0,α}` coefficient field `a` and a continuous bilinear map `L`, the assignment
`v ↦ (z ↦ L (a z) (v z))` is an `ℝ`-linear map of parabolic `C^{0,α}` submodules (linear in the second
argument, the closure coming from `ParabolicC0AlphaOn.continuousLinearMap₂`). -/
def continuousLinearMap₂Coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : parabolicC0AlphaSubmodule X E α s) :
    parabolicC0AlphaSubmodule X F α s →ₗ[ℝ] parabolicC0AlphaSubmodule X G α s where
  toFun v := ⟨fun z => L (a z) (v z), a.2.continuousLinearMap₂ L v.2⟩
  map_add' v w := by
    ext z
    simp
  map_smul' c v := by
    ext z
    simp

@[simp]
theorem continuousLinearMap₂Coeff_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : parabolicC0AlphaSubmodule X E α s) (v : parabolicC0AlphaSubmodule X F α s) (z : ℝ × X) :
    continuousLinearMap₂Coeff (X := X) (E := E) (α := α) (s := s) L a v z = L (a z) (v z) :=
  rfl

end parabolicC0AlphaSubmodule

namespace ParabolicC0AlphaSpace

/-- Frozen-coefficient multiplication `v ↦ (z ↦ L (a z) (v z))` on the seminormed carriers. -/
def mulCoeffLM {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaSpace X F α s →ₗ[ℝ] ParabolicC0AlphaSpace X G α s :=
  parabolicC0AlphaSubmodule.continuousLinearMap₂Coeff L (toSubmodule a)

@[simp]
theorem toFun_mulCoeffLM {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    toFun (mulCoeffLM L a v) = fun z => L (toFun a z) (toFun v z) :=
  rfl

/-- **Frozen-coefficient multiplication is a bounded operator of norm `≤ ‖L‖ · ‖a‖` on the carriers.**
For a fixed parabolic `C^{0,α}` coefficient field `a`, multiplication `v ↦ (z ↦ L (a z) (v z))` by a
continuous bilinear map `L` is a bounded `ℝ`-linear map with operator norm `≤ ‖L‖ · ‖a‖` — the
frozen-coefficient linear operator at the heart of parabolic Schauder theory. -/
noncomputable def mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaSpace X F α s →L[ℝ] ParabolicC0AlphaSpace X G α s :=
  LinearMap.mkContinuous (mulCoeffLM L a) (‖L‖ * ‖a‖) (fun v => by
    show parabolicC0AlphaNorm α (fun z => L (toFun a z) (toFun v z)) s
        ≤ ‖L‖ * parabolicC0AlphaNorm α (toFun a) s * parabolicC0AlphaNorm α (toFun v) s
    exact parabolicC0AlphaNorm_continuousLinearMap₂_le L (toSubmodule a).2 (toSubmodule v).2)

@[simp]
theorem toFun_mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    toFun (mulCoeffL L a v) = fun z => L (toFun a z) (toFun v z) :=
  rfl

/-- The carrier frozen-coefficient operator has operator norm `≤ ‖L‖ · ‖a‖`. -/
theorem norm_mulCoeffL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ‖mulCoeffL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L a‖ ≤ ‖L‖ * ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg a)) _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Frozen-coefficient multiplication descends to the Banach spaces.**  For a fixed parabolic
`C^{0,α}` coefficient field `a`, multiplication `v ↦ (z ↦ L (a z) (v z))` by a continuous bilinear map
`L` is well defined on Banach classes (it is `(‖L‖·‖a‖)`-Lipschitz), giving a bounded operator
`ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …` of norm `≤ ‖L‖ · ‖a‖`.  This is the
frozen-coefficient linear operator whose invertibility the Ricci–DeTurck Schauder estimates
control. -/
noncomputable def mulCoeffL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ParabolicC0AlphaBanach X F α s →L[ℝ] ParabolicC0AlphaBanach X G α s :=
  SeparationQuotient.liftCLM (mkL.comp (ParabolicC0AlphaSpace.mulCoeffL L a))
    (fun v v' hins => by
      change SeparationQuotient.mk _ = SeparationQuotient.mk _
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist v v' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (ParabolicC0AlphaSpace.mulCoeffL L a v) (ParabolicC0AlphaSpace.mulCoeffL L a v')
          ≤ ‖ParabolicC0AlphaSpace.mulCoeffL L a‖ * dist v v' := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact (ParabolicC0AlphaSpace.mulCoeffL L a).le_opNorm _
      exact le_antisymm (hle.trans (le_of_eq (by rw [h0, mul_zero]))) dist_nonneg)

/-- **Frozen-coefficient multiplication commutes with the projection.** -/
@[simp]
theorem mulCoeffL_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L a (mk v) = mk (ParabolicC0AlphaSpace.mulCoeffL L a v) :=
  SeparationQuotient.liftCLM_mk _ _ v

/-- The Banach frozen-coefficient operator has operator norm `≤ ‖L‖ · ‖a‖`. -/
theorem norm_mulCoeffL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    ‖mulCoeffL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L a‖ ≤ ‖L‖ * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg a))
    (fun x => ?_)
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [mulCoeffL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_mulCoeffL]
  have := parabolicC0AlphaNorm_continuousLinearMap₂_le L
    (ParabolicC0AlphaSpace.toSubmodule a).2 (ParabolicC0AlphaSpace.toSubmodule v).2
  change parabolicC0AlphaNorm α
      (fun z => L ((ParabolicC0AlphaSpace.toSubmodule a) z)
        ((ParabolicC0AlphaSpace.toSubmodule v) z)) s ≤
    ‖L‖ * parabolicC0AlphaNorm α (ParabolicC0AlphaSpace.toSubmodule a) s *
      parabolicC0AlphaNorm α (ParabolicC0AlphaSpace.toSubmodule v) s
  simpa only [mul_assoc] using this

/-- **Point evaluation of a frozen-coefficient product is the bilinear map applied to the point
values.**  Reading off the space-time value of `L(a, ·)` applied to a chart solution `x` at `z` is
`L (a z) (evalCLM z x)` — the pointwise algebra coherence of the frozen-coefficient operator. -/
@[simp]
theorem evalCLM_mulCoeffL_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (z : ℝ × X) (hz : z ∈ s)
    (x : ParabolicC0AlphaBanach X F α s) :
    evalCLM z hz (mulCoeffL L a x) = L (ParabolicC0AlphaSpace.toFun a z) (evalCLM z hz x) := by
  obtain ⟨v, rfl⟩ := mk_surjective x
  simp only [mulCoeffL_mk, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_mulCoeffL]

end ParabolicC0AlphaBanach

namespace ParabolicC0AlphaSpace

/-- **Frozen-coefficient multiplication is additive in the coefficient (carrier).**  `L(a + a', v) =
L(a, v) + L(a', v)` pointwise, from the linearity of `L` in its first argument. -/
theorem mulCoeffL_add_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a a' : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L (a + a') v = mulCoeffL L a v + mulCoeffL L a' v := by
  apply Subtype.ext
  funext z
  show L (toFun a z + toFun a' z) (toFun v z)
      = L (toFun a z) (toFun v z) + L (toFun a' z) (toFun v z)
  rw [map_add, ContinuousLinearMap.add_apply]

/-- **Frozen-coefficient multiplication is homogeneous in the coefficient (carrier).**  `L(c • a, v) =
c • L(a, v)` pointwise. -/
theorem mulCoeffL_smul_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (c : ℝ)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulCoeffL L (c • a) v = c • mulCoeffL L a v := by
  apply Subtype.ext
  funext z
  show L (c • toFun a z) (toFun v z) = c • L (toFun a z) (toFun v z)
  rw [map_smul, ContinuousLinearMap.smul_apply]

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **Banach frozen-coefficient multiplication is additive in the coefficient.**  As operators
`ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …`, `mulCoeffL L (a + a')
= mulCoeffL L a + mulCoeffL L a'`. -/
theorem mulCoeffL_add_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a a' : ParabolicC0AlphaSpace X E α s) :
    mulCoeffL (X := X) (s := s) (G := G) L (a + a') = mulCoeffL L a + mulCoeffL L a' := by
  ext x
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.add_apply, mulCoeffL_mk, mulCoeffL_mk, mulCoeffL_mk,
    ParabolicC0AlphaSpace.mulCoeffL_add_coeff, ← mkL_apply, ← mkL_apply, ← mkL_apply, map_add]

/-- **Banach frozen-coefficient multiplication is homogeneous in the coefficient.**  As operators,
`mulCoeffL L (c • a) = c • mulCoeffL L a`. -/
theorem mulCoeffL_smul_coeff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) (c : ℝ)
    (a : ParabolicC0AlphaSpace X E α s) :
    mulCoeffL (X := X) (s := s) (G := G) L (c • a) = c • mulCoeffL L a := by
  ext x
  obtain ⟨v, rfl⟩ := mk_surjective x
  rw [ContinuousLinearMap.smul_apply, mulCoeffL_mk, mulCoeffL_mk,
    ParabolicC0AlphaSpace.mulCoeffL_smul_coeff, ← mkL_apply, ← mkL_apply, map_smul]

/-- **The parabolic `C^{0,α}` bounded bilinear multiplication operator.**  Packaging the
frozen-coefficient family `a ↦ mulCoeffL L a` as a single bounded `ℝ`-linear map
`ParabolicC0AlphaSpace … E … →L[ℝ] (ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …)`
of operator norm `≤ ‖L‖`.  Together with the boundedness of each `mulCoeffL L a` this exhibits the
genuine bounded bilinear parabolic `C^{0,α}` multiplication `‖L(a, v)‖ ≤ ‖L‖ · ‖a‖ · ‖v‖` — the
algebra structure a nonlinear Ricci–DeTurck Banach-chart RHS is built from. -/
noncomputable def mulL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ParabolicC0AlphaSpace X E α s →L[ℝ]
      (ParabolicC0AlphaBanach X F α s →L[ℝ] ParabolicC0AlphaBanach X G α s) :=
  LinearMap.mkContinuous
    { toFun := fun a => mulCoeffL L a
      map_add' := mulCoeffL_add_coeff L
      map_smul' := fun c a => mulCoeffL_smul_coeff L c a }
    ‖L‖ (fun a => norm_mulCoeffL_le L a)

/-- On a coefficient `a`, the bounded bilinear multiplication is the frozen-coefficient operator. -/
@[simp]
theorem mulL_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    mulL L a = mulCoeffL L a :=
  rfl

/-- The bounded bilinear multiplication operator has operator norm `≤ ‖L‖`. -/
theorem norm_mulL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ‖mulL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

/-- **The fully-Banach bilinear parabolic `C^{0,α}` multiplication operator.**  The frozen-coefficient
family `mulL L` takes its coefficient in the *seminormed carrier* `ParabolicC0AlphaSpace`; because it
is `‖L‖`-Lipschitz it sends coefficients agreeing on `s` (inseparable in the carrier) to the *same*
operator, so it descends through the separation quotient in the coefficient slot as well.  The result
is a genuine bounded **bilinear** map
`ParabolicC0AlphaBanach … E … →L[ℝ] (ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …)`
of operator norm `≤ ‖L‖` — i.e. `‖L(u, v)‖ ≤ ‖L‖ · ‖u‖ · ‖v‖` for Banach classes `u`, `v`.

Unlike `mulL` (whose coefficient is a fixed carrier representative — the *linearised* frozen-coefficient
operator whose invertibility the Schauder estimate controls), here **both** factors are Banach classes:
this is the algebra of the *quadratic* nonlinear Ricci–DeTurck term, whose coefficient is itself a chart
solution.  Its diagonal `u ↦ mulBilinL L u u` is the quadratic map. -/
noncomputable def mulBilinL {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ParabolicC0AlphaBanach X E α s →L[ℝ]
      (ParabolicC0AlphaBanach X F α s →L[ℝ] ParabolicC0AlphaBanach X G α s) :=
  SeparationQuotient.liftCLM (mulL L)
    (fun a a' hins => by
      have hnorm : ‖a - a'‖ = 0 := by
        rw [← dist_eq_norm]; exact Metric.inseparable_iff.mp hins
      have hzero : ‖mulL L a - mulL L a'‖ = 0 := by
        rw [← map_sub]
        refine le_antisymm ?_ (norm_nonneg _)
        calc ‖mulL L (a - a')‖ ≤ ‖mulL L‖ * ‖a - a'‖ := (mulL L).le_opNorm _
          _ = 0 := by rw [hnorm, mul_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero))

/-- **On a coefficient class the bilinear multiplication is the frozen-coefficient operator.**  For a
carrier coefficient `a`, `mulBilinL L (mk a) = mulL L a` (`= mulCoeffL L a`). -/
@[simp]
theorem mulBilinL_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) :
    mulBilinL (X := X) (s := s) (G := G) L (mk a) = mulL L a :=
  SeparationQuotient.liftCLM_mk _ _ a

/-- **On classes of carrier representatives, the bilinear multiplication is the class of the pointwise
product.** -/
theorem mulBilinL_mk_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (a : ParabolicC0AlphaSpace X E α s) (v : ParabolicC0AlphaSpace X F α s) :
    mulBilinL L (mk a) (mk v) = mk (ParabolicC0AlphaSpace.mulCoeffL L a v) := by
  rw [mulBilinL_mk, mulL_apply, mulCoeffL_mk]

/-- The bilinear multiplication operator has operator norm `≤ ‖L‖`
(the honest bounded bilinear estimate `‖L(u, v)‖ ≤ ‖L‖ · ‖u‖ · ‖v‖`). -/
theorem norm_mulBilinL_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G) :
    ‖mulBilinL (X := X) (E := E) (α := α) (s := s) (F := F) (G := G) L‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (fun x => ?_)
  obtain ⟨a, rfl⟩ := mk_surjective x
  rw [mulBilinL_mk, norm_mk]
  calc ‖mulL L a‖ ≤ ‖mulL L‖ * ‖a‖ := (mulL L).le_opNorm a
    _ ≤ ‖L‖ * ‖a‖ := by gcongr; exact norm_mulL_le L
    _ = ‖L‖ * parabolicC0AlphaNorm α (ParabolicC0AlphaSpace.toFun a) s := by
        rw [ParabolicC0AlphaSpace.norm_def]

/-- **Point evaluation of a bilinear product is the bilinear map on the two point values.**  Reading off
the space-time value of `L(u, v)` at `z ∈ s` is `L` applied to the value of `u` and the value of `v` —
the pointwise algebra coherence of the fully-Banach bilinear operator. -/
@[simp]
theorem evalCLM_mulBilinL_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] F →L[ℝ] G)
    (u : ParabolicC0AlphaBanach X E α s) (z : ℝ × X) (hz : z ∈ s)
    (x : ParabolicC0AlphaBanach X F α s) :
    evalCLM z hz (mulBilinL L u x) = L (evalCLM z hz u) (evalCLM z hz x) := by
  obtain ⟨a, rfl⟩ := mk_surjective u
  rw [mulBilinL_mk, mulL_apply, evalCLM_mulCoeffL_apply, evalCLM_mk_apply]

/-- **A priori bound on the quadratic term.**  The diagonal `u ↦ L(u, u)` of the bilinear
multiplication satisfies `‖L(u, u)‖ ≤ ‖L‖ · ‖u‖ · ‖u‖` — the size of the quadratic Ricci–DeTurck
nonlinearity on a chart solution `u`. -/
theorem norm_mulBilinL_diag_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] E →L[ℝ] G) (u : ParabolicC0AlphaBanach X E α s) :
    ‖mulBilinL L u u‖ ≤ ‖L‖ * ‖u‖ * ‖u‖ := by
  calc ‖mulBilinL L u u‖ ≤ ‖mulBilinL L u‖ * ‖u‖ := (mulBilinL L u).le_opNorm _
    _ ≤ (‖L‖ * ‖u‖) * ‖u‖ := by
        gcongr
        calc ‖mulBilinL L u‖ ≤ ‖mulBilinL L‖ * ‖u‖ := (mulBilinL L).le_opNorm _
          _ ≤ ‖L‖ * ‖u‖ := by gcongr; exact norm_mulBilinL_le L

/-- **Bilinear polarisation of the quadratic-term difference.**  `L(u, u) − L(v, v) = L(u, u − v)
+ L(u − v, v)`, the exact algebraic identity behind the local Lipschitz control of the quadratic
Ricci–DeTurck nonlinearity (from the bilinearity of `mulBilinL`). -/
theorem mulBilinL_diag_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] E →L[ℝ] G) (u v : ParabolicC0AlphaBanach X E α s) :
    mulBilinL L u u - mulBilinL L v v
      = mulBilinL L u (u - v) + mulBilinL L (u - v) v := by
  have h1 : mulBilinL L u (u - v) = mulBilinL L u u - mulBilinL L u v := map_sub _ _ _
  have h2 : mulBilinL L (u - v) v = mulBilinL L u v - mulBilinL L v v := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [h1, h2]; abel

/-- **Local Lipschitz control of the quadratic term.**  `‖L(u, u) − L(v, v)‖ ≤ ‖L‖ · (‖u‖ + ‖v‖) ·
‖u − v‖`, the quadratic nonlinearity's difference bound: on any ball of radius `R` it is
`(2‖L‖R)`-Lipschitz.  This is exactly the `k`-Lipschitz-nonlinearity datum the Ricci–DeTurck
short-time fixed-point solver (`exists_unique_affinePlusLipschitzFixedPoint` / `affinePlusLipschitzSolve`)
consumes. -/
theorem norm_mulBilinL_diag_sub_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] E →L[ℝ] G) (u v : ParabolicC0AlphaBanach X E α s) :
    ‖mulBilinL L u u - mulBilinL L v v‖ ≤ ‖L‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  rw [mulBilinL_diag_sub]
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖mulBilinL L u (u - v)‖ ≤ ‖L‖ * ‖u‖ * ‖u - v‖ := by
    calc ‖mulBilinL L u (u - v)‖ ≤ ‖mulBilinL L u‖ * ‖u - v‖ := (mulBilinL L u).le_opNorm _
      _ ≤ (‖L‖ * ‖u‖) * ‖u - v‖ := by
          gcongr
          calc ‖mulBilinL L u‖ ≤ ‖mulBilinL L‖ * ‖u‖ := (mulBilinL L).le_opNorm _
            _ ≤ ‖L‖ * ‖u‖ := by gcongr; exact norm_mulBilinL_le L
  have e2 : ‖mulBilinL L (u - v) v‖ ≤ ‖L‖ * ‖u - v‖ * ‖v‖ := by
    calc ‖mulBilinL L (u - v) v‖ ≤ ‖mulBilinL L (u - v)‖ * ‖v‖ := (mulBilinL L (u - v)).le_opNorm _
      _ ≤ (‖L‖ * ‖u - v‖) * ‖v‖ := by
          gcongr
          calc ‖mulBilinL L (u - v)‖ ≤ ‖mulBilinL L‖ * ‖u - v‖ := (mulBilinL L).le_opNorm _
            _ ≤ ‖L‖ * ‖u - v‖ := by gcongr; exact norm_mulBilinL_le L
  calc ‖mulBilinL L u (u - v)‖ + ‖mulBilinL L (u - v) v‖
      ≤ ‖L‖ * ‖u‖ * ‖u - v‖ + ‖L‖ * ‖u - v‖ * ‖v‖ := add_le_add e1 e2
    _ = ‖L‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- **The quadratic nonlinearity is Lipschitz on every closed ball.**  On `closedBall 0 R` the diagonal
`u ↦ L(u, u)` is `(2‖L‖R)`-Lipschitz — the invariant-ball nonlinearity control the Ricci–DeTurck
short-time contraction consumes (a small ball / short time makes `2‖L‖R < 1`). -/
theorem lipschitzOnWith_mulBilinL_diag {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] E →L[ℝ] G) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (2 * ‖L‖ * R).toNNReal (fun u => mulBilinL L u u)
      (Metric.closedBall (0 : ParabolicC0AlphaBanach X E α s) R) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have hu' : ‖u‖ ≤ R := by simpa [dist_eq_norm] using hu
  have hv' : ‖v‖ ≤ R := by simpa [dist_eq_norm] using hv
  have hconst : ((2 * ‖L‖ * R).toNNReal : ℝ) = 2 * ‖L‖ * R :=
    Real.coe_toNNReal _ (by positivity)
  rw [dist_eq_norm, dist_eq_norm, hconst]
  calc ‖mulBilinL L u u - mulBilinL L v v‖
      ≤ ‖L‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := norm_mulBilinL_diag_sub_le L u v
    _ ≤ ‖L‖ * (R + R) * ‖u - v‖ := by gcongr
    _ = 2 * ‖L‖ * R * ‖u - v‖ := by ring

end ParabolicC0AlphaBanach

/-! ### The precomposition (change-of-variables) operator

Precomposition by a space-time map `φ : ℝ × Y → ℝ × X` mapping `t` into `s` and expanding parabolic
distance by at most `L` is a bounded operator `ParabolicC0AlphaBanach X E α s →L ParabolicC0AlphaBanach
Y E α t` of norm `≤ max 1 (L ^ α)`.  This is the operator behind chart-transition gluing, the
DeTurck gauge-diffeomorphism action, and parabolic Schauder scaling; it generalises `restrictL`
(the special case `φ = ` inclusion, `L = 1`). -/

namespace ParabolicC0AlphaSpace

/-- Precomposition by `φ` as a linear map of the underlying parabolic `C^{0,α}` submodules. -/
def precompSubmoduleLinearMap {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    parabolicC0AlphaSubmodule X E α s →ₗ[ℝ] parabolicC0AlphaSubmodule Y E α t where
  toFun u := ⟨fun p => u.1 (φ p), u.2.comp_parabolicDistanceLe hα hL hmaps hφ⟩
  map_add' u v := by ext z; simp
  map_smul' c u := by ext z; simp

/-- Precomposition by `φ` as a linear map of the parabolic `C^{0,α}` carriers. -/
def precompLinearMap {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicC0AlphaSpace X E α s →ₗ[ℝ] ParabolicC0AlphaSpace Y E α t :=
  precompSubmoduleLinearMap hα hL hmaps hφ

@[simp]
theorem toFun_precompLinearMap {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (precompLinearMap hα hL hmaps hφ u) = fun p => toFun u (φ p) :=
  rfl

/-- **Precomposition is bounded of operator norm `≤ max 1 (L ^ α)`** on the parabolic `C^{0,α}`
carrier, via `parabolicC0AlphaNorm_comp_parabolicDistanceLe_le`. -/
noncomputable def precompL {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace Y E α t :=
  LinearMap.mkContinuous (precompLinearMap hα hL hmaps hφ) (max 1 (L ^ α)) (fun u => by
    show parabolicC0AlphaNorm α (toFun (precompLinearMap hα hL hmaps hφ u)) t
      ≤ max 1 (L ^ α) * parabolicC0AlphaNorm α (toFun u) s
    rw [toFun_precompLinearMap]
    exact parabolicC0AlphaNorm_comp_parabolicDistanceLe_le (toSubmodule u).2 hα hL hmaps hφ)

@[simp]
theorem toFun_precompL {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q)
    (u : ParabolicC0AlphaSpace X E α s) :
    toFun (precompL hα hL hmaps hφ u) = fun p => toFun u (φ p) :=
  rfl

/-- The precomposition operator on the carrier has operator norm `≤ max 1 (L ^ α)`. -/
theorem norm_precompL_le {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ‖precompL (X := X) (E := E) (α := α) (s := s) hα hL hmaps hφ‖ ≤ max 1 (L ^ α) :=
  LinearMap.mkContinuous_norm_le _ (le_trans zero_le_one (le_max_left _ _)) _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **The precomposition operator on the parabolic `C^{0,α}` Banach spaces.**  Descends the carrier
operator to the separation quotients (well-defined because bounded), giving a bounded operator
`ParabolicC0AlphaBanach X E α s →L ParabolicC0AlphaBanach Y E α t` of norm `≤ max 1 (L ^ α)`. -/
noncomputable def precompL {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach Y E α t :=
  SeparationQuotient.liftCLM
    ((mkL (X := Y) (E := E) (α := α) (s := t)).comp
      (ParabolicC0AlphaSpace.precompL hα hL hmaps hφ))
    (fun (u u' : ParabolicC0AlphaSpace X E α s) (hins : Inseparable u u') => by
      let F : ParabolicC0AlphaSpace X E α s →L[ℝ] ParabolicC0AlphaSpace Y E α t :=
        ParabolicC0AlphaSpace.precompL hα hL hmaps hφ
      change SeparationQuotient.mk (F u) = SeparationQuotient.mk (F u')
      refine SeparationQuotient.mk_eq_mk.2 ?_
      rw [Metric.inseparable_iff]
      have h0 : dist u u' = 0 := Metric.inseparable_iff.mp hins
      have hle : dist (F u) (F u') ≤ ‖F‖ * ‖u - u'‖ := by
        rw [dist_eq_norm, ← map_sub]
        exact F.le_opNorm _
      have h0' : ‖u - u'‖ = 0 := by rw [← dist_eq_norm]; exact h0
      rw [h0', mul_zero] at hle
      exact le_antisymm hle dist_nonneg)

/-- **Precomposition commutes with the projection.**  On the class of a representative `u`,
precomposition is the class of the precomposed representative. -/
@[simp]
theorem precompL_mk {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q)
    (u : ParabolicC0AlphaSpace X E α s) :
    precompL hα hL hmaps hφ (mk u) = mk (ParabolicC0AlphaSpace.precompL hα hL hmaps hφ u) :=
  SeparationQuotient.liftCLM_mk _ _ u

/-- The precomposition operator on the Banach spaces has operator norm `≤ max 1 (L ^ α)`. -/
theorem norm_precompL_le {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q) :
    ‖precompL (X := X) (E := E) (α := α) (s := s) hα hL hmaps hφ‖ ≤ max 1 (L ^ α) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _)) (fun x => ?_)
  obtain ⟨u, rfl⟩ := mk_surjective x
  rw [precompL_mk, norm_mk, norm_mk, ParabolicC0AlphaSpace.toFun_precompL]
  exact parabolicC0AlphaNorm_comp_parabolicDistanceLe_le
    (ParabolicC0AlphaSpace.toSubmodule u).2 hα hL hmaps hφ

/-- **Precomposition is compatible with point evaluation (cone coherence, pointwise).**  Evaluating
the precomposed class at a space-time point `w ∈ t` gives the value of the original class at
`φ w ∈ s`: `evalCLM w (precompL φ x) = evalCLM (φ w) x`.  This is the pullback-of-evaluation
coherence that keeps the point-values of chart-transition–glued solutions consistent. -/
theorem evalCLM_precompL_apply {Y : Type*} [PseudoMetricSpace Y] {L : ℝ}
    {φ : ℝ × Y → ℝ × X} {t : Set (ℝ × Y)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hmaps : Set.MapsTo φ t s)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q)
    (w : ℝ × Y) (hw : w ∈ t) (x : ParabolicC0AlphaBanach X E α s) :
    evalCLM w hw (precompL hα hL hmaps hφ x) = evalCLM (φ w) (hmaps hw) x := by
  obtain ⟨u, rfl⟩ := mk_surjective x
  simp only [precompL_mk, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_precompL]

/-- **Precomposition is functorial (contravariant / cocycle law).**  Precomposing first by
`φ : ℝ × Y → ℝ × X` (a `t → s`, `L`-expanding change of variables) and then by `ψ : ℝ × Z → ℝ × Y`
(an `r → t`, `M`-expanding one) equals precomposition by the composite `φ ∘ ψ` (an `r → s`,
`(L·M)`-expanding change of variables).  This is the chart-transition cocycle condition the gluing of
local Ricci–DeTurck Banach-chart solutions across overlapping charts consumes (the precomposition
analogue of `restrictL_comp` and `compL_comp`).  Proved through the point-separation representation. -/
theorem precompL_comp_apply {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {L M : ℝ} {φ : ℝ × Y → ℝ × X} {ψ : ℝ × Z → ℝ × Y} {t : Set (ℝ × Y)} {r : Set (ℝ × Z)}
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hφmaps : Set.MapsTo φ t s) (hψmaps : Set.MapsTo ψ r t)
    (hφ : ∀ ⦃p : ℝ × Y⦄, p ∈ t → ∀ ⦃q : ℝ × Y⦄, q ∈ t →
      parabolicDistance (φ p) (φ q) ≤ L * parabolicDistance p q)
    (hψ : ∀ ⦃p : ℝ × Z⦄, p ∈ r → ∀ ⦃q : ℝ × Z⦄, q ∈ r →
      parabolicDistance (ψ p) (ψ q) ≤ M * parabolicDistance p q)
    (x : ParabolicC0AlphaBanach X E α s) :
    precompL hα hM hψmaps hψ (precompL hα hL hφmaps hφ x)
      = precompL (X := X) (E := E) (α := α) (s := s) hα (mul_nonneg hL hM)
          (hφmaps.comp hψmaps)
          (fun p hp q hq =>
            (hφ (hψmaps hp) (hψmaps hq)).trans
              ((mul_le_mul_of_nonneg_left (hψ hp hq) hL).trans_eq (mul_assoc L M _).symm)) x := by
  rw [eq_iff_forall_evalCLM]
  intro w hw
  rw [evalCLM_precompL_apply, evalCLM_precompL_apply, evalCLM_precompL_apply]
  rfl

/-- **Precomposition by the identity is the identity operator.**  The `φ = id`, `L = 1`, `t = s`
case of `precompL` is `ContinuousLinearMap.id`.  Together with `precompL_comp_apply` this exhibits
the two functor laws of the precomposition (change-of-variables) action. -/
theorem precompL_id (hα : 0 ≤ α) :
    precompL (X := X) (E := E) (α := α) (s := s) (Y := X) (L := 1) (φ := id) (t := s)
        hα zero_le_one (Set.mapsTo_id s) (fun p _ q _ => le_of_eq (by simp))
      = ContinuousLinearMap.id ℝ (ParabolicC0AlphaBanach X E α s) := by
  ext x
  rw [ContinuousLinearMap.id_apply, eq_iff_forall_evalCLM]
  intro w hw
  rw [evalCLM_precompL_apply]
  rfl

end ParabolicC0AlphaBanach

/-! ### The constant-function embedding operator

Embedding a value `c : E` as the constant function `z ↦ c` is a bounded operator
`E →L ParabolicC0AlphaBanach X E α s` of norm `≤ 1`.  This is the inhomogeneous / frozen-data part
of the Ricci–DeTurck right-hand side (a constant reaction term, or frozen initial data, entering the
affine `u ↦ A u + f` structure of the Schauder fixed-point). -/

namespace ParabolicC0AlphaSpace

/-- The constant function `z ↦ c`, linear in `c`, as a linear map into the parabolic `C^{0,α}`
submodule. -/
def constSubmoduleLinearMap : E →ₗ[ℝ] parabolicC0AlphaSubmodule X E α s where
  toFun c := ⟨fun _ => c, ParabolicC0AlphaOn.const c⟩
  map_add' c c' := by ext z; simp
  map_smul' a c := by ext z; simp

/-- The constant-function embedding as a linear map into the parabolic `C^{0,α}` carrier. -/
def constLinearMap : E →ₗ[ℝ] ParabolicC0AlphaSpace X E α s :=
  constSubmoduleLinearMap

@[simp]
theorem toFun_constLinearMap (c : E) :
    toFun (constLinearMap (X := X) (α := α) (s := s) c) = fun _ => c :=
  rfl

/-- **The constant-function embedding is bounded of operator norm `≤ 1`** on the carrier, via
`parabolicC0AlphaNorm_const_le`. -/
noncomputable def constL : E →L[ℝ] ParabolicC0AlphaSpace X E α s :=
  LinearMap.mkContinuous constLinearMap 1 (fun c => by
    show parabolicC0AlphaNorm α (toFun (constLinearMap c)) s ≤ 1 * ‖c‖
    rw [one_mul, toFun_constLinearMap]
    exact parabolicC0AlphaNorm_const_le α c s)

@[simp]
theorem toFun_constL (c : E) :
    toFun (constL (X := X) (α := α) (s := s) c) = fun _ => c :=
  rfl

/-- The constant-function embedding on the carrier has operator norm `≤ 1`. -/
theorem norm_constL_le :
    ‖constL (X := X) (E := E) (α := α) (s := s)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ParabolicC0AlphaSpace

namespace ParabolicC0AlphaBanach

/-- **The constant-function embedding on the parabolic `C^{0,α}` Banach space.**  A value `c : E`
is embedded as the class of the constant function `z ↦ c`; a bounded operator of norm `≤ 1`. -/
noncomputable def constL : E →L[ℝ] ParabolicC0AlphaBanach X E α s :=
  mkL.comp (ParabolicC0AlphaSpace.constL)

@[simp]
theorem constL_apply (c : E) :
    constL (X := X) (E := E) (α := α) (s := s) c = mk (ParabolicC0AlphaSpace.constL c) :=
  rfl

/-- The constant-function embedding on the Banach space has operator norm `≤ 1`. -/
theorem norm_constL_le :
    ‖constL (X := X) (E := E) (α := α) (s := s)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun c => ?_)
  rw [one_mul, constL_apply, norm_mk, ParabolicC0AlphaSpace.toFun_constL]
  exact parabolicC0AlphaNorm_const_le α c s

/-- **Point evaluation of a constant class returns the constant.**  The value of the embedded
constant `c` at any space-time point `z ∈ s` is `c`. -/
theorem evalCLM_constL_apply (z : ℝ × X) (hz : z ∈ s) (c : E) :
    evalCLM z hz (constL (X := X) (E := E) (α := α) (s := s) c) = c := by
  rw [constL_apply, evalCLM_mk_apply, ParabolicC0AlphaSpace.toFun_constL]

/-- **Post-composition of a constant is the constant of the post-composed value.**  Applying a
fiberwise bundle morphism `L` to the embedded constant `c` gives the embedded constant `L c` — the
compatibility of the frozen-data embedding with a coordinate change / bundle morphism. -/
theorem compL_constL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (c : E) :
    compL L (constL (X := X) (E := E) (α := α) (s := s) c) = constL (L c) := by
  rw [eq_iff_forall_evalCLM]
  intro z hz
  rw [evalCLM_compL_apply, evalCLM_constL_apply, evalCLM_constL_apply]

/-! ### The affine Ricci–DeTurck fixed-point equation `A u + f = u`

The parabolic `C^{0,α}` operator API assembled above — fiberwise post-composition `compL`,
frozen-coefficient multiplication `mulL`, and the constant embedding `constL` — combines into the
**affine right-hand side** `u ↦ A u + f` of the linearised Ricci–DeTurck flow on a Banach chart
(`A` the bounded linear principal-plus-lower-order operator, `f` the inhomogeneous / frozen data).
When the linear part is a contraction (`‖A‖ < 1`), the completeness of the parabolic `C^{0,α}`
Banach space closes the linear-solvability step: the affine equation has a unique solution.  This is
the abstract Banach fixed-point core of the Ricci–DeTurck Schauder iteration. -/

/-- **The affine self-map `u ↦ A u + f` is `‖A‖`-Lipschitz.**  Translation by the fixed
inhomogeneity `f` is an isometry, so the affine right-hand side of the linearised Ricci–DeTurck flow
has the same Lipschitz constant as its linear part `A`. -/
theorem lipschitzWith_affineMap
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s) :
    LipschitzWith ‖A‖₊ (fun u => A u + f) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  have hdist : dist (A x + f) (A y + f) = dist (A x) (A y) := by
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub]
  show dist (A x + f) (A y + f) ≤ ↑‖A‖₊ * dist x y
  rw [hdist]
  exact A.lipschitz.dist_le_mul x y

/-- **The affine self-map is a contraction when its linear part is.**  If `‖A‖ < 1` then the affine
right-hand side `u ↦ A u + f` is a `ContractingWith ‖A‖₊` self-map of the (complete) parabolic
`C^{0,α}` Banach space. -/
theorem contractingWith_affineMap
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    ContractingWith ‖A‖₊ (fun u => A u + f) :=
  ⟨by exact_mod_cast hA, lipschitzWith_affineMap A f⟩

/-- **Unique solvability of the affine Ricci–DeTurck fixed-point equation.**  On the complete
parabolic `C^{0,α}` Banach chart, if the linear part `A` of the affine right-hand side `u ↦ A u + f`
is a contraction (`‖A‖ < 1`), then the equation `A u + f = u` has a *unique* solution `u`.  This is
the Banach fixed-point / linear-solvability step underlying the Ricci–DeTurck Schauder iteration:
the frozen-coefficient linear part `A` (built from `compL`/`mulL`) plus the inhomogeneous data `f`
(built from `constL`) determine a single Banach-chart solution. -/
theorem exists_unique_affineFixedPoint [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    ∃! u, A u + f = u := by
  haveI : Nonempty (ParabolicC0AlphaBanach X E α s) := ⟨0⟩
  have hg : ContractingWith ‖A‖₊ (fun u => A u + f) := contractingWith_affineMap A f hA
  refine ⟨ContractingWith.fixedPoint (fun u => A u + f) hg, hg.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hg.fixedPoint_unique hy

/-- **The solution operator of the affine Ricci–DeTurck fixed-point equation.**  When the linear
part `A` is a contraction (`‖A‖ < 1`), `1 - A` is invertible on the (complete) parabolic `C^{0,α}`
Banach space via the Neumann series, so the solution of `A u + f = u` depends *boundedly and
linearly* on the inhomogeneous data `f` through `u = (1 - A)⁻¹ f`.  This bounded linear solution
operator is the quantitative a-priori structure of the Ricci–DeTurck Schauder iteration. -/
noncomputable def affineSolveL [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s :=
  ↑(Units.oneSub A hA)⁻¹

/-- **The solution operator is a right inverse of `1 - A`.**  `(1 - A) * affineSolveL A hA = 1` in
the endomorphism ring of the parabolic `C^{0,α}` Banach space. -/
theorem oneSub_mul_affineSolveL [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    (1 - A) * affineSolveL A hA = 1 := by
  show (1 - A) * (↑(Units.oneSub A hA)⁻¹) = 1
  rw [← Units.val_oneSub A hA]
  exact (Units.oneSub A hA).mul_inv

/-- **`affineSolveL A hA f` solves the affine fixed-point equation.**  The value `u = (1 - A)⁻¹ f`
satisfies `A u + f = u`; combined with `exists_unique_affineFixedPoint` it is *the* solution. -/
theorem affineSolveL_isSolution [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1)
    (f : ParabolicC0AlphaBanach X E α s) :
    A (affineSolveL A hA f) + f = affineSolveL A hA f := by
  have h1 := congrArg (fun L : ParabolicC0AlphaBanach X E α s →L[ℝ] _ => L f)
    (oneSub_mul_affineSolveL A hA)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] at h1
  calc A (affineSolveL A hA f) + f
      = A (affineSolveL A hA f) + (affineSolveL A hA f - A (affineSolveL A hA f)) := by rw [h1]
    _ = affineSolveL A hA f := by abel

/-- **A-priori Schauder bound for the solution operator.**  `‖affineSolveL A hA‖ ≤ (1 - ‖A‖)⁻¹`:
the Neumann solution operator `(1 - A)⁻¹` of the affine Ricci–DeTurck equation is bounded by
`(1 - ‖A‖)⁻¹`, so the solution obeys the a-priori estimate `‖u‖ ≤ (1 - ‖A‖)⁻¹ ‖f‖`.  This is the
quantitative linear Schauder estimate: the fixed-point operator is `∑ₙ Aⁿ` and its norm is controlled
by the geometric bound (`‖(1 : _ →L _)‖ ≤ 1` removes the `‖1‖ - 1` correction term). -/
theorem norm_affineSolveL_le [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    ‖affineSolveL A hA‖ ≤ (1 - ‖A‖)⁻¹ := by
  have hsum : affineSolveL A hA = ∑' n : ℕ, A ^ n := rfl
  rw [hsum]
  have hb := tsum_geometric_le_of_norm_lt_one A hA
  have h1 : ‖(1 : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  linarith

/-- **A-priori estimate for the affine Ricci–DeTurck solution.**  The solution `u = affineSolveL A hA
f` of `A u + f = u` obeys the quantitative linear Schauder bound `‖u‖ ≤ (1 - ‖A‖)⁻¹ ‖f‖` in the
inhomogeneous data. -/
theorem norm_affineSolveL_apply_le [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1)
    (f : ParabolicC0AlphaBanach X E α s) :
    ‖affineSolveL A hA f‖ ≤ (1 - ‖A‖)⁻¹ * ‖f‖ :=
  le_trans ((affineSolveL A hA).le_opNorm f)
    (mul_le_mul_of_nonneg_right (norm_affineSolveL_le A hA) (norm_nonneg f))

/-- **The solution operator yields the unique solution.**  Every solution `u` of the affine
Ricci–DeTurck fixed-point equation `A u + f = u` equals `affineSolveL A hA f`, so the bounded linear
map `f ↦ affineSolveL A hA f` is *the* solution map of the linearised Ricci–DeTurck flow. -/
theorem eq_affineSolveL_of_isSolution [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1)
    {f u : ParabolicC0AlphaBanach X E α s} (hu : A u + f = u) :
    u = affineSolveL A hA f := by
  obtain ⟨w, _, hw⟩ := exists_unique_affineFixedPoint A f hA
  rw [hw u hu, hw (affineSolveL A hA f) (affineSolveL_isSolution A hA f)]

/-- **Concrete solvability under a fiberwise contraction.**  If the fiber morphism `L : E →L[ℝ] E`
is a contraction (`‖L‖ < 1`), the affine equation `compL L u + f = u` — fiberwise post-composition by
`L` (a coordinate change / bundle morphism) plus the inhomogeneity `f` — has a unique solution on the
parabolic `C^{0,α}` Banach space.  This instantiates the abstract affine solvability at the concrete
fiberwise-post-composition operator built earlier. -/
theorem exists_unique_compL_affineFixedPoint [CompleteSpace E] (L : E →L[ℝ] E) (hL : ‖L‖ < 1)
    (f : ParabolicC0AlphaBanach X E α s) :
    ∃! u, compL L u + f = u :=
  exists_unique_affineFixedPoint (compL L) f (lt_of_le_of_lt (norm_compL_le L) hL)

/-- **Concrete solvability under a frozen-coefficient contraction.**  If the frozen-coefficient
operator `mulCoeffL L a` — multiplication by the `C^{0,α}` coefficient field `a` through the bounded
bilinear map `L` — is small, `‖L‖ * ‖a‖ < 1`, then the affine equation `mulCoeffL L a u + f = u` has a
unique solution on the parabolic `C^{0,α}` Banach space.  This instantiates the abstract affine
solvability at the concrete frozen-coefficient operator at the heart of parabolic Schauder theory. -/
theorem exists_unique_mulCoeffL_affineFixedPoint {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F →L[ℝ] F)
    (a : ParabolicC0AlphaSpace X E α s) (ha : ‖L‖ * ‖a‖ < 1)
    (f : ParabolicC0AlphaBanach X F α s) :
    ∃! u, mulCoeffL L a u + f = u :=
  exists_unique_affineFixedPoint (mulCoeffL L a) f (lt_of_le_of_lt (norm_mulCoeffL_le L a) ha)

/-- **The solution operator is a left inverse of `1 - A`.**  `affineSolveL A hA * (1 - A) = 1` in the
endomorphism ring of the parabolic `C^{0,α}` Banach space (the two-sided companion of
`oneSub_mul_affineSolveL`).  Together they exhibit `affineSolveL A hA = (1 - A)⁻¹`. -/
theorem affineSolveL_mul_oneSub [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s) (hA : ‖A‖ < 1) :
    affineSolveL A hA * (1 - A) = 1 := by
  show (↑(Units.oneSub A hA)⁻¹) * (1 - A) = 1
  rw [← Units.val_oneSub A hA]
  exact (Units.oneSub A hA).inv_mul

/-- **The resolvent identity for the affine Ricci–DeTurck solution operators.**  For two contracting
linear parts `A`, `B` (`‖A‖, ‖B‖ < 1`), the Neumann solution operators differ by
`(1 - A)⁻¹ - (1 - B)⁻¹ = (1 - A)⁻¹ (A - B) (1 - B)⁻¹`.  This is the algebraic core of the *continuous
dependence of the linearised Schauder solution on its frozen coefficients*: it converts a change
`A - B` in the coefficient operator into a change in the solution operator, mediated on both sides by
the individual solution operators. -/
theorem affineSolveL_sub_eq [CompleteSpace E]
    (A B : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    affineSolveL A hA - affineSolveL B hB
      = affineSolveL A hA * (A - B) * affineSolveL B hB := by
  have hA1 : affineSolveL A hA * (1 - A) = 1 := affineSolveL_mul_oneSub A hA
  have hB1 : (1 - B) * affineSolveL B hB = 1 := oneSub_mul_affineSolveL B hB
  have e1 : A - B = (1 - B) - (1 - A) := by abel
  have key : affineSolveL A hA * (A - B) * affineSolveL B hB
      = affineSolveL A hA - affineSolveL B hB := by
    rw [e1, mul_sub, sub_mul,
      mul_assoc (affineSolveL A hA) (1 - B) (affineSolveL B hB), hB1, mul_one, hA1, one_mul]
  exact key.symm

/-- **Lipschitz dependence of the Schauder solution operator on the frozen coefficients.**  The
Neumann solution operator `affineSolveL A hA = (1 - A)⁻¹` obeys the perturbation bound
`‖affineSolveL A hA - affineSolveL B hB‖ ≤ (1 - ‖A‖)⁻¹ · ‖A - B‖ · (1 - ‖B‖)⁻¹`, so the linearised
Ricci–DeTurck solution operator depends Lipschitz-continuously (in operator norm) on the frozen
coefficient operator.  This is the quantitative continuous-dependence estimate that turns the
coefficient-dependent Ricci–DeTurck Schauder iteration into a contraction. -/
theorem norm_affineSolveL_sub_le [CompleteSpace E]
    (A B : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    ‖affineSolveL A hA - affineSolveL B hB‖ ≤ (1 - ‖A‖)⁻¹ * ‖A - B‖ * (1 - ‖B‖)⁻¹ := by
  have hApos : (0 : ℝ) ≤ (1 - ‖A‖)⁻¹ := inv_nonneg.mpr (by linarith)
  have hmid : (0 : ℝ) ≤ (1 - ‖A‖)⁻¹ * ‖A - B‖ := mul_nonneg hApos (norm_nonneg _)
  rw [affineSolveL_sub_eq A B hA hB]
  calc ‖affineSolveL A hA * (A - B) * affineSolveL B hB‖
      ≤ ‖affineSolveL A hA * (A - B)‖ * ‖affineSolveL B hB‖ := norm_mul_le _ _
    _ ≤ ‖affineSolveL A hA‖ * ‖A - B‖ * ‖affineSolveL B hB‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 - ‖A‖)⁻¹ * ‖A - B‖ * (1 - ‖B‖)⁻¹ :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (norm_affineSolveL_le A hA) (norm_nonneg _))
          (norm_affineSolveL_le B hB) (norm_nonneg _) hmid

/-- **A-priori solution-difference estimate under a coefficient change.**  For a fixed inhomogeneity
`f`, the solutions of the two linearised Ricci–DeTurck equations `A u + f = u` and `B u + f = u`
satisfy `‖affineSolveL A hA f - affineSolveL B hB f‖ ≤ (1 - ‖A‖)⁻¹ · ‖A - B‖ · (1 - ‖B‖)⁻¹ · ‖f‖`.
This is the quantitative statement that a small change in the frozen coefficients produces a
correspondingly small change in the Schauder solution — the estimate consumed by the nonlinear
(coefficient-dependent) Ricci–DeTurck contraction mapping. -/
theorem norm_affineSolveL_apply_sub_le [CompleteSpace E]
    (A B : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (f : ParabolicC0AlphaBanach X E α s) :
    ‖affineSolveL A hA f - affineSolveL B hB f‖ ≤ (1 - ‖A‖)⁻¹ * ‖A - B‖ * (1 - ‖B‖)⁻¹ * ‖f‖ := by
  have hfe : affineSolveL A hA f - affineSolveL B hB f = (affineSolveL A hA - affineSolveL B hB) f := by
    rw [ContinuousLinearMap.sub_apply]
  rw [hfe]
  calc ‖(affineSolveL A hA - affineSolveL B hB) f‖
      ≤ ‖affineSolveL A hA - affineSolveL B hB‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 - ‖A‖)⁻¹ * ‖A - B‖ * (1 - ‖B‖)⁻¹ * ‖f‖ :=
        mul_le_mul_of_nonneg_right (norm_affineSolveL_sub_le A B hA hB) (norm_nonneg f)

/-! ### Nonlinear Schauder fixed point

The affine solvability above (`exists_unique_affineFixedPoint`, `affineSolveL`) closes the
*linearised* Ricci–DeTurck step.  The genuine Ricci–DeTurck right-hand side is *quasilinear*, i.e. a
**nonlinear** self-map `g` of the parabolic `C^{0,α}` Banach chart which — on a short time interval /
a small ball around the initial data — is a contraction (`LipschitzWith k g`, `k < 1`).  The
following lemmas are the nonlinear fixed-point core the quasilinear iteration consumes: unique
solvability, the a-posteriori residual bound (which controls the iteration error from a single
residual `‖x - g x‖`), and the stability of the solution under a uniform perturbation of the
nonlinearity (which makes the coefficient- and data-dependent iteration well-posed). -/

/-- **Nonlinear Banach fixed-point solvability on the parabolic `C^{0,α}` chart.**  A self-map `g` of
the (complete) parabolic `C^{0,α}` Banach space that is a contraction (`LipschitzWith k g` with
`k < 1`) has a *unique* fixed point `g u = u`.  This is the nonlinear generalisation of
`exists_unique_affineFixedPoint` (the affine `g = A · + f` case): the Banach fixed-point solvability
of the genuine quasilinear Ricci–DeTurck right-hand side on a short-time / small-ball chart where it
contracts. -/
theorem exists_unique_lipschitzFixedPoint [CompleteSpace E] {k : ℝ≥0}
    (g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hk : k < 1) (hg : LipschitzWith k g) :
    ∃! u, g u = u := by
  haveI : Nonempty (ParabolicC0AlphaBanach X E α s) := ⟨0⟩
  have hc : ContractingWith k g := ⟨hk, hg⟩
  refine ⟨ContractingWith.fixedPoint g hc, hc.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hc.fixedPoint_unique hy

/-- **A-posteriori residual bound for the nonlinear fixed point.**  If `g` is a `k`-contraction
(`k < 1`) and `u` is *any* fixed point (`g u = u`), then every point `x` obeys
`‖x - u‖ ≤ ‖x - g x‖ / (1 - k)`: the distance from a trial point `x` to the true Ricci–DeTurck
solution is controlled by the single residual `‖x - g x‖`.  This is the a-posteriori error estimate
of the quasilinear Schauder iteration. -/
theorem norm_sub_fixedPoint_le_of_lipschitz [CompleteSpace E] {k : ℝ≥0}
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    (hk : k < 1) (hg : LipschitzWith k g) (x : ParabolicC0AlphaBanach X E α s)
    {u : ParabolicC0AlphaBanach X E α s} (hu : g u = u) :
    ‖x - u‖ ≤ ‖x - g x‖ / (1 - (k : ℝ)) := by
  have hc : ContractingWith k g := ⟨hk, hg⟩
  have h := hc.dist_le_of_fixedPoint x (y := u) hu
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- **Stability of the nonlinear fixed point under a uniform perturbation of the nonlinearity.**  Let
`g₁` be a `k`-contraction (`k < 1`) with fixed point `u₁`, and let `g₂` be *any* map with a fixed
point `u₂` that is uniformly `C`-close to `g₁` (`∀ z, ‖g₁ z - g₂ z‖ ≤ C`).  Then the fixed points
satisfy `‖u₁ - u₂‖ ≤ C / (1 - k)`.  This is the well-posedness estimate of the quasilinear
Ricci–DeTurck iteration: a `C`-sized change in the nonlinear right-hand side moves the solution by at
most `C / (1 - k)`, so the solution depends continuously on the (coefficient- and data-dependent)
nonlinearity. -/
theorem norm_fixedPoint_sub_fixedPoint_le [CompleteSpace E] {k : ℝ≥0}
    {g₁ g₂ : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    (hk : k < 1) (hg₁ : LipschitzWith k g₁)
    {u₁ u₂ : ParabolicC0AlphaBanach X E α s} (hu₁ : g₁ u₁ = u₁) (hu₂ : g₂ u₂ = u₂)
    {C : ℝ} (hC : ∀ z, ‖g₁ z - g₂ z‖ ≤ C) :
    ‖u₁ - u₂‖ ≤ C / (1 - (k : ℝ)) := by
  have hc : ContractingWith k g₁ := ⟨hk, hg₁⟩
  have hfg : ∀ z, dist (g₁ z) (g₂ z) ≤ C := fun z => by rw [dist_eq_norm]; exact hC z
  have h := hc.dist_fixedPoint_fixedPoint_of_dist_le' g₂ (x := u₁) (y := u₂) hu₁ hu₂ hfg
  rwa [dist_eq_norm] at h

/-- **Geometric convergence of the Picard/Schauder iteration.**  For a `k`-contraction `g` (`k < 1`)
with fixed point `u` (`g u = u`), the Picard iterates `g^[n] x` from any starting point `x` obey the
a-priori geometric error bound `‖g^[n] x - u‖ ≤ ‖x - g x‖ · kⁿ / (1 - k)`.  This is the quantitative
constructive form of the nonlinear Ricci–DeTurck existence: the iteration reaches the solution at an
explicit geometric rate controlled by the first residual `‖x - g x‖`. -/
theorem norm_iterate_sub_fixedPoint_le [CompleteSpace E] {k : ℝ≥0}
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    (hk : k < 1) (hg : LipschitzWith k g) (x : ParabolicC0AlphaBanach X E α s)
    {u : ParabolicC0AlphaBanach X E α s} (hu : g u = u) (n : ℕ) :
    ‖g^[n] x - u‖ ≤ ‖x - g x‖ * (k : ℝ) ^ n / (1 - (k : ℝ)) := by
  haveI : Nonempty (ParabolicC0AlphaBanach X E α s) := ⟨0⟩
  have hc : ContractingWith k g := ⟨hk, hg⟩
  have hueq : u = ContractingWith.fixedPoint g hc := hc.fixedPoint_unique hu
  have h := hc.apriori_dist_iterate_fixedPoint_le x n
  rw [dist_eq_norm, dist_eq_norm] at h
  rw [hueq]
  exact h

/-- **The Picard/Schauder iteration converges to the Ricci–DeTurck solution.**  For a `k`-contraction
`g` (`k < 1`) with fixed point `u`, the iterates `g^[n] x` from any starting point `x` converge to
`u`.  The topological (qualitative) companion of the geometric rate
`norm_iterate_sub_fixedPoint_le`: the nonlinear iteration is a convergent constructive scheme for the
Ricci–DeTurck solution. -/
theorem tendsto_iterate_fixedPoint [CompleteSpace E] {k : ℝ≥0}
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    (hk : k < 1) (hg : LipschitzWith k g) (x : ParabolicC0AlphaBanach X E α s)
    {u : ParabolicC0AlphaBanach X E α s} (hu : g u = u) :
    Filter.Tendsto (fun n => g^[n] x) Filter.atTop (𝓝 u) := by
  haveI : Nonempty (ParabolicC0AlphaBanach X E α s) := ⟨0⟩
  have hc : ContractingWith k g := ⟨hk, hg⟩
  have hueq : u = ContractingWith.fixedPoint g hc := hc.fixedPoint_unique hu
  rw [hueq]
  exact hc.tendsto_iterate_fixedPoint x

/-- **Unique solvability of the quasilinear Ricci–DeTurck fixed-point equation.**  The genuine
Ricci–DeTurck right-hand side splits as a bounded *linear* principal-plus-lower-order part `A`, a
*nonlinear* remainder `N` (`LipschitzWith k`), and the inhomogeneous / frozen data `f`.  If the
combined contraction constant is subunital, `‖A‖ + k < 1`, then the quasilinear equation
`A u + N u + f = u` has a unique solution `u` on the (complete) parabolic `C^{0,α}` Banach chart.
This exhibits the actual algebraic shape of the Ricci–DeTurck Schauder fixed point (linear principal
part + nonlinear perturbation + data): the right-hand side is shown to contract with constant
`‖A‖ + k` (the operator norm of the linear part plus the Lipschitz constant of the nonlinearity), and
`exists_unique_lipschitzFixedPoint` then supplies the unique solution.  It simultaneously generalises
the affine `exists_unique_affineFixedPoint` (the `N = 0` case) and the concrete-operator corollaries
`exists_unique_compL_affineFixedPoint` / `exists_unique_mulCoeffL_affineFixedPoint`. -/
theorem exists_unique_affinePlusLipschitzFixedPoint [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1) :
    ∃! u, A u + N u + f = u := by
  have hlin : LipschitzWith ‖A‖₊ (fun u => A u) := A.lipschitz
  have hg0 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u) := hlin.add hN
  have hgf : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u + f) := by
    simpa only [add_zero] using hg0.add (LipschitzWith.const f)
  have hlt : ‖A‖₊ + k < 1 := by exact_mod_cast hAk
  exact exists_unique_lipschitzFixedPoint (fun u => A u + N u + f) hlt hgf

/-! ### Well-posedness of the quasilinear Ricci–DeTurck solution

`exists_unique_affinePlusLipschitzFixedPoint` gives the *unique solvability* of the quasilinear
Ricci–DeTurck fixed-point equation `A u + N u + f = u` (bounded-linear principal-plus-lower-order
part `A`, nonlinear `k`-Lipschitz remainder `N`, frozen data `f`) whenever the combined contraction
constant is subunital, `‖A‖ + k < 1`.  The following lemmas are the **well-posedness data** the
Ricci–DeTurck chart-closure consumes: the continuous (Lipschitz) dependence of the solution on the
frozen data `f`, its a-priori norm bound, its stability under a uniform perturbation of the
nonlinearity, and the bundled solution operator `f ↦ u(f)` as a genuine Lipschitz map. -/

/-- **Continuous dependence of the quasilinear solution on the data.**  For the quasilinear
Ricci–DeTurck equation `A u + N u + f = u` (linear part `A`, `k`-Lipschitz nonlinearity `N`,
contraction constant `‖A‖ + k < 1`), two solutions `u₁`, `u₂` corresponding to frozen data `f₁`,
`f₂` obey `‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / (1 - (‖A‖ + k))`.  So the Ricci–DeTurck solution depends
Lipschitz-continuously on the inhomogeneous data — the well-posedness estimate underlying the
chart's continuous dependence on the (frozen) initial data.  Generalises the affine
`norm_affineSolveL_apply_sub_le` (`N = 0`) to the genuine quasilinear right-hand side. -/
theorem norm_affinePlusLipschitzFixedPoint_sub_le [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f₁ f₂ : ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    {u₁ u₂ : ParabolicC0AlphaBanach X E α s}
    (hu₁ : A u₁ + N u₁ + f₁ = u₁) (hu₂ : A u₂ + N u₂ + f₂ = u₂) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / (1 - (‖A‖ + (k : ℝ))) := by
  have hlin : LipschitzWith ‖A‖₊ (fun u => A u) := A.lipschitz
  have hg0 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u) := hlin.add hN
  have hg1 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u + f₁) := by
    simpa only [add_zero] using hg0.add (LipschitzWith.const f₁)
  have hlt : ‖A‖₊ + k < 1 := by exact_mod_cast hAk
  have hC : ∀ z, ‖(fun u => A u + N u + f₁) z - (fun u => A u + N u + f₂) z‖ ≤ ‖f₁ - f₂‖ := by
    intro z
    have he : (A z + N z + f₁) - (A z + N z + f₂) = f₁ - f₂ := by abel
    calc ‖(fun u => A u + N u + f₁) z - (fun u => A u + N u + f₂) z‖
        = ‖f₁ - f₂‖ := by rw [he]
      _ ≤ ‖f₁ - f₂‖ := le_refl _
  have h := norm_fixedPoint_sub_fixedPoint_le (k := ‖A‖₊ + k)
    (g₁ := fun u => A u + N u + f₁) (g₂ := fun u => A u + N u + f₂) hlt hg1 hu₁ hu₂ hC
  simpa only [NNReal.coe_add, coe_nnnorm] using h

/-- **A-priori norm bound for the quasilinear solution.**  Any solution `u` of the quasilinear
Ricci–DeTurck equation `A u + N u + f = u` (`k`-Lipschitz `N`, `‖A‖ + k < 1`) obeys
`‖u‖ ≤ (‖N 0‖ + ‖f‖) / (1 - (‖A‖ + k))`.  From the fixed-point identity,
`‖u‖ ≤ ‖A‖‖u‖ + ‖N u‖ + ‖f‖ ≤ (‖A‖ + k)‖u‖ + (‖N 0‖ + ‖f‖)` (the nonlinearity contributing
`‖N u‖ ≤ k‖u‖ + ‖N 0‖`), and solving for `‖u‖`.  The quantitative Schauder a-priori estimate for
the quasilinear right-hand side (the `N = 0` case recovers `‖u‖ ≤ ‖f‖ / (1 - ‖A‖)`). -/
theorem norm_affinePlusLipschitzFixedPoint_le [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    {u : ParabolicC0AlphaBanach X E α s} (hu : A u + N u + f = u) :
    ‖u‖ ≤ (‖N 0‖ + ‖f‖) / (1 - (‖A‖ + (k : ℝ))) := by
  have hNu : ‖N u‖ ≤ (k : ℝ) * ‖u‖ + ‖N 0‖ := by
    have hd : dist (N u) (N 0) ≤ (k : ℝ) * dist u 0 := hN.dist_le_mul u 0
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
    have h2 : ‖N u‖ - ‖N 0‖ ≤ ‖N u - N 0‖ := norm_sub_norm_le _ _
    linarith [h2, hd]
  have key : ‖u‖ ≤ (‖A‖ + (k : ℝ)) * ‖u‖ + (‖N 0‖ + ‖f‖) := by
    calc ‖u‖ = ‖A u + N u + f‖ := by rw [hu]
      _ ≤ ‖A u + N u‖ + ‖f‖ := norm_add_le _ _
      _ ≤ (‖A u‖ + ‖N u‖) + ‖f‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (‖A‖ * ‖u‖ + ((k : ℝ) * ‖u‖ + ‖N 0‖)) + ‖f‖ :=
          add_le_add (add_le_add (A.le_opNorm u) hNu) le_rfl
      _ = (‖A‖ + (k : ℝ)) * ‖u‖ + (‖N 0‖ + ‖f‖) := by ring
  have hpos : (0 : ℝ) < 1 - (‖A‖ + (k : ℝ)) := by linarith
  rw [le_div_iff₀ hpos, mul_sub, mul_one]
  nlinarith [key, mul_comm ‖u‖ (‖A‖ + (k : ℝ))]

/-- **Stability of the quasilinear solution under a uniform perturbation of the nonlinearity.**  For
the *same* linear part `A` and frozen data `f`, two nonlinearities `N₁`, `N₂` (with `N₁`
`k`-Lipschitz, `‖A‖ + k < 1`) that are uniformly `C`-close (`∀ z, ‖N₁ z - N₂ z‖ ≤ C`) have solutions
`u₁`, `u₂` of `A u + Nᵢ u + f = u` satisfying `‖u₁ - u₂‖ ≤ C / (1 - (‖A‖ + k))`.  A `C`-sized change
in the nonlinear (coefficient-dependent) part of the Ricci–DeTurck right-hand side moves the solution
by at most `C / (1 - (‖A‖ + k))`, so the solution depends continuously on the nonlinearity. -/
theorem norm_affinePlusLipschitzFixedPoint_sub_le_nonlinearity [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N₁ N₂ : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s)
    (hN₁ : LipschitzWith k N₁) (hAk : ‖A‖ + (k : ℝ) < 1)
    {u₁ u₂ : ParabolicC0AlphaBanach X E α s}
    (hu₁ : A u₁ + N₁ u₁ + f = u₁) (hu₂ : A u₂ + N₂ u₂ + f = u₂)
    {C : ℝ} (hC : ∀ z, ‖N₁ z - N₂ z‖ ≤ C) :
    ‖u₁ - u₂‖ ≤ C / (1 - (‖A‖ + (k : ℝ))) := by
  have hlin : LipschitzWith ‖A‖₊ (fun u => A u) := A.lipschitz
  have hg0 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N₁ u) := hlin.add hN₁
  have hg1 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N₁ u + f) := by
    simpa only [add_zero] using hg0.add (LipschitzWith.const f)
  have hlt : ‖A‖₊ + k < 1 := by exact_mod_cast hAk
  have hCg : ∀ z, ‖(fun u => A u + N₁ u + f) z - (fun u => A u + N₂ u + f) z‖ ≤ C := by
    intro z
    have he : (A z + N₁ z + f) - (A z + N₂ z + f) = N₁ z - N₂ z := by abel
    calc ‖(fun u => A u + N₁ u + f) z - (fun u => A u + N₂ u + f) z‖
        = ‖N₁ z - N₂ z‖ := by rw [he]
      _ ≤ C := hC z
  have h := norm_fixedPoint_sub_fixedPoint_le (k := ‖A‖₊ + k)
    (g₁ := fun u => A u + N₁ u + f) (g₂ := fun u => A u + N₂ u + f) hlt hg1 hu₁ hu₂ hCg
  simpa only [NNReal.coe_add, coe_nnnorm] using h

/-- **The quasilinear Ricci–DeTurck solution operator.**  For a bounded-linear principal part `A`, a
`k`-Lipschitz nonlinearity `N` with `‖A‖ + k < 1`, and any frozen data `f`, the value
`affinePlusLipschitzSolve A N hN hAk f` is *the* (unique) solution of `A u + N u + f = u`.  This is
the nonlinear solution map `f ↦ u(f)` of the quasilinear Ricci–DeTurck chart. -/
noncomputable def affinePlusLipschitzSolve [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    (f : ParabolicC0AlphaBanach X E α s) : ParabolicC0AlphaBanach X E α s :=
  (exists_unique_affinePlusLipschitzFixedPoint A N f hN hAk).choose

/-- `affinePlusLipschitzSolve A N hN hAk f` solves the quasilinear fixed-point equation. -/
theorem affinePlusLipschitzSolve_isSolution [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    (f : ParabolicC0AlphaBanach X E α s) :
    A (affinePlusLipschitzSolve A N hN hAk f) + N (affinePlusLipschitzSolve A N hN hAk f) + f
      = affinePlusLipschitzSolve A N hN hAk f :=
  (exists_unique_affinePlusLipschitzFixedPoint A N f hN hAk).choose_spec.1

/-- **Uniqueness readout of the quasilinear solution operator.**  Every solution `u` of
`A u + N u + f = u` equals `affinePlusLipschitzSolve A N hN hAk f`. -/
theorem affinePlusLipschitzSolve_eq [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    (f : ParabolicC0AlphaBanach X E α s)
    {u : ParabolicC0AlphaBanach X E α s} (hu : A u + N u + f = u) :
    u = affinePlusLipschitzSolve A N hN hAk f :=
  (exists_unique_affinePlusLipschitzFixedPoint A N f hN hAk).choose_spec.2 u hu

/-- **The quasilinear Ricci–DeTurck solution operator is Lipschitz in the data.**  The solution map
`f ↦ affinePlusLipschitzSolve A N hN hAk f` is `LipschitzWith ((1 - (‖A‖ + k))⁻¹).toNNReal` — the
bundled continuous-dependence-on-data statement (`norm_affinePlusLipschitzFixedPoint_sub_le` packaged
as a `LipschitzWith`), the well-posed nonlinear solution realisation the chart-closure data consumes.
The nonlinear analogue of the bounded *linear* affine solution operator `affineSolveL`. -/
theorem lipschitzWith_affinePlusLipschitzSolve [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1) :
    LipschitzWith ((1 - (‖A‖ + (k : ℝ)))⁻¹).toNNReal (affinePlusLipschitzSolve A N hN hAk) := by
  have hpos : (0 : ℝ) < 1 - (‖A‖ + (k : ℝ)) := by linarith
  have hinv : (0 : ℝ) ≤ (1 - (‖A‖ + (k : ℝ)))⁻¹ := le_of_lt (inv_pos.mpr hpos)
  apply LipschitzWith.of_dist_le_mul
  intro f₁ f₂
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hinv]
  have h := norm_affinePlusLipschitzFixedPoint_sub_le A N f₁ f₂ hN hAk
    (affinePlusLipschitzSolve_isSolution A N hN hAk f₁)
    (affinePlusLipschitzSolve_isSolution A N hN hAk f₂)
  rwa [div_eq_inv_mul] at h

/-! ### Local existence on an invariant ball

The fixed-point solvability above is *global* (the right-hand side contracts on the whole Banach
space).  The genuine Ricci–DeTurck right-hand side, however, is only known to contract and to preserve
a small ball around the initial data on a short time interval.  The following lemmas localise the
solution to any closed set / ball the right-hand side preserves — the honest short-time / small-ball
chart existence. -/

/-- **Localisation of the nonlinear fixed point to a closed invariant set.**  If a `k`-contraction
`g` (`k < 1`) maps a closed set `K` into itself and `K` contains a point `c`, then *the* fixed point
`u` (`g u = u`) lies in `K`.  Proof: the Picard iterates `g^[n] c` stay in `K` (invariance +
`c ∈ K`, `Set.MapsTo.iterate`) and converge to `u` (`tendsto_iterate_fixedPoint`), so the closed `K`
contains the limit (`IsClosed.mem_of_tendsto`).  The abstract "short-time / small-ball chart"
localisation: the Ricci–DeTurck solution stays inside any region the right-hand side preserves. -/
theorem fixedPoint_mem_of_mapsTo_isClosed [CompleteSpace E] {k : ℝ≥0}
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    (hk : k < 1) (hg : LipschitzWith k g)
    {K : Set (ParabolicC0AlphaBanach X E α s)} (hK : IsClosed K)
    {c : ParabolicC0AlphaBanach X E α s} (hc : c ∈ K) (hmaps : Set.MapsTo g K K)
    {u : ParabolicC0AlphaBanach X E α s} (hu : g u = u) :
    u ∈ K := by
  refine hK.mem_of_tendsto (tendsto_iterate_fixedPoint hk hg c hu) ?_
  filter_upwards with n
  exact hmaps.iterate n hc

/-- **Local existence of the quasilinear Ricci–DeTurck solution on an invariant ball.**  If the
quasilinear right-hand side `z ↦ A z + N z + f` (`k`-Lipschitz `N`, `‖A‖ + k < 1`) maps a closed ball
`closedBall c r` (`0 ≤ r`) into itself, then the solution `u` of `A u + N u + f = u` lies in that
ball (`dist u c ≤ r`).  This is the genuine short-time / small-ball chart form: on the ball around the
initial data that the Ricci–DeTurck right-hand side preserves, the (unique) solution exists *and stays
in the ball*.  Specialises `fixedPoint_mem_of_mapsTo_isClosed` to `Metric.closedBall`. -/
theorem affinePlusLipschitzFixedPoint_mem_closedBall [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f : ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    (c : ParabolicC0AlphaBanach X E α s) {r : ℝ} (hr : 0 ≤ r)
    (hmaps : Set.MapsTo (fun z => A z + N z + f)
      (Metric.closedBall c r) (Metric.closedBall c r))
    {u : ParabolicC0AlphaBanach X E α s} (hu : A u + N u + f = u) :
    u ∈ Metric.closedBall c r := by
  have hlin : LipschitzWith ‖A‖₊ (fun u => A u) := A.lipschitz
  have hg0 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u) := hlin.add hN
  have hg1 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N u + f) := by
    simpa only [add_zero] using hg0.add (LipschitzWith.const f)
  have hlt : ‖A‖₊ + k < 1 := by exact_mod_cast hAk
  exact fixedPoint_mem_of_mapsTo_isClosed hlt hg1 Metric.isClosed_closedBall
    (Metric.mem_closedBall_self hr) hmaps hu

/-- **Combined continuous dependence on the frozen data and the nonlinearity.**  For the *same*
linear part `A`, two quasilinear right-hand sides differing in *both* the nonlinearity and the frozen
data — `A u₁ + N₁ u₁ + f₁ = u₁` and `A u₂ + N₂ u₂ + f₂ = u₂` (`N₁` `k`-Lipschitz, `‖A‖ + k < 1`,
`N₁`, `N₂` uniformly `C`-close) — have solutions obeying
`‖u₁ - u₂‖ ≤ (C + ‖f₁ - f₂‖) / (1 - (‖A‖ + k))`.  The full continuous-dependence estimate on the
frozen chart data `(N, f)`, of which the pure-data `norm_affinePlusLipschitzFixedPoint_sub_le`
(`N₁ = N₂`, `C = 0`) and the pure-nonlinearity `norm_affinePlusLipschitzFixedPoint_sub_le_nonlinearity`
(`f₁ = f₂`) are the two faces: a `C`-sized perturbation of the nonlinearity together with a
`‖f₁ - f₂‖`-sized change of the data moves the Ricci–DeTurck solution by at most
`(C + ‖f₁ - f₂‖) / (1 - (‖A‖ + k))`. -/
theorem norm_affinePlusLipschitzFixedPoint_sub_le_of_data_nonlinearity [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N₁ N₂ : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (f₁ f₂ : ParabolicC0AlphaBanach X E α s)
    (hN₁ : LipschitzWith k N₁) (hAk : ‖A‖ + (k : ℝ) < 1)
    {u₁ u₂ : ParabolicC0AlphaBanach X E α s}
    (hu₁ : A u₁ + N₁ u₁ + f₁ = u₁) (hu₂ : A u₂ + N₂ u₂ + f₂ = u₂)
    {C : ℝ} (hC : ∀ z, ‖N₁ z - N₂ z‖ ≤ C) :
    ‖u₁ - u₂‖ ≤ (C + ‖f₁ - f₂‖) / (1 - (‖A‖ + (k : ℝ))) := by
  have hlin : LipschitzWith ‖A‖₊ (fun u => A u) := A.lipschitz
  have hg0 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N₁ u) := hlin.add hN₁
  have hg1 : LipschitzWith (‖A‖₊ + k) (fun u => A u + N₁ u + f₁) := by
    simpa only [add_zero] using hg0.add (LipschitzWith.const f₁)
  have hlt : ‖A‖₊ + k < 1 := by exact_mod_cast hAk
  have hCg : ∀ z, ‖(fun u => A u + N₁ u + f₁) z - (fun u => A u + N₂ u + f₂) z‖
      ≤ C + ‖f₁ - f₂‖ := by
    intro z
    have he : (A z + N₁ z + f₁) - (A z + N₂ z + f₂) = (N₁ z - N₂ z) + (f₁ - f₂) := by abel
    calc ‖(fun u => A u + N₁ u + f₁) z - (fun u => A u + N₂ u + f₂) z‖
        = ‖(N₁ z - N₂ z) + (f₁ - f₂)‖ := by rw [he]
      _ ≤ ‖N₁ z - N₂ z‖ + ‖f₁ - f₂‖ := norm_add_le _ _
      _ ≤ C + ‖f₁ - f₂‖ := add_le_add (hC z) le_rfl
  have h := norm_fixedPoint_sub_fixedPoint_le (k := ‖A‖₊ + k)
    (g₁ := fun u => A u + N₁ u + f₁) (g₂ := fun u => A u + N₂ u + f₂) hlt hg1 hu₁ hu₂ hCg
  simpa only [NNReal.coe_add, coe_nnnorm] using h

/-- **A-priori bound for the quasilinear solution operator.**  `affinePlusLipschitzSolve A N hN hAk f`
obeys `‖·‖ ≤ (‖N 0‖ + ‖f‖) / (1 - (‖A‖ + k))` — the a-priori Schauder estimate
(`norm_affinePlusLipschitzFixedPoint_le`) read off the bundled solution operator. -/
theorem norm_affinePlusLipschitzSolve_le [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1)
    (f : ParabolicC0AlphaBanach X E α s) :
    ‖affinePlusLipschitzSolve A N hN hAk f‖ ≤ (‖N 0‖ + ‖f‖) / (1 - (‖A‖ + (k : ℝ))) :=
  norm_affinePlusLipschitzFixedPoint_le A N f hN hAk
    (affinePlusLipschitzSolve_isSolution A N hN hAk f)

/-- **The quasilinear Ricci–DeTurck solution operator is continuous in the data.**  The continuity
companion of `lipschitzWith_affinePlusLipschitzSolve`: the nonlinear solution realisation
`f ↦ affinePlusLipschitzSolve A N hN hAk f` is a continuous map of the frozen data. -/
theorem continuous_affinePlusLipschitzSolve [CompleteSpace E] {k : ℝ≥0}
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (N : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s)
    (hN : LipschitzWith k N) (hAk : ‖A‖ + (k : ℝ) < 1) :
    Continuous (affinePlusLipschitzSolve A N hN hAk) :=
  (lipschitzWith_affinePlusLipschitzSolve A N hN hAk).continuous

/-! ### Banach fixed point on a closed ball, and the quadratic Ricci–DeTurck short-time existence

The `affinePlusLipschitz` solver above needs a *globally* Lipschitz nonlinearity.  The genuine
Ricci–DeTurck nonlinearity is *quadratic* (`u ↦ mulBilinL L u u`), only **locally** Lipschitz.  The
following localise the Banach fixed-point theorem to a closed ball (a complete metric subspace of the
parabolic Banach space) and apply it to the quadratic right-hand side, giving the honest short-time /
small-ball existence for the quadratic nonlinearity. -/

/-- **Banach fixed point on a closed ball.**  A self-map `g` of a closed ball `closedBall c r`
(`0 ≤ r`) that is `LipschitzOnWith K` on the ball with `K < 1` has a fixed point in the ball.  The
closed ball is complete (closed in the complete parabolic Banach space), so the
contraction-on-a-complete-subset Banach fixed-point theorem (`ContractingWith.exists_fixedPoint'`)
applies.  This is the abstract short-time small-ball existence: whenever a nonlinear parabolic
Ricci–DeTurck right-hand side preserves and contracts a small ball around the initial data, it has a
(chart) solution in that ball. -/
theorem exists_fixedPoint_of_lipschitzOnWith_closedBall [CompleteSpace E]
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    {c : ParabolicC0AlphaBanach X E α s} {r : ℝ} (hr : 0 ≤ r) {K : ℝ≥0} (hK : K < 1)
    (hg : LipschitzOnWith K g (Metric.closedBall c r))
    (hmaps : Set.MapsTo g (Metric.closedBall c r) (Metric.closedBall c r)) :
    ∃ u ∈ Metric.closedBall c r, g u = u := by
  have hcomplete : IsComplete (Metric.closedBall c r :
      Set (ParabolicC0AlphaBanach X E α s)) := Metric.isClosed_closedBall.isComplete
  have hrestrict : LipschitzWith K
      (hmaps.restrict g (Metric.closedBall c r) (Metric.closedBall c r)) := by
    intro a b
    exact hg a.2 b.2
  have hcball : c ∈ Metric.closedBall c r := Metric.mem_closedBall_self hr
  obtain ⟨u, hu_mem, hu_fix, _, _⟩ :=
    ContractingWith.exists_fixedPoint' hcomplete hmaps ⟨hK, hrestrict⟩ hcball
      (edist_ne_top _ _)
  exact ⟨u, hu_mem, hu_fix⟩

/-- **Uniqueness of the fixed point in a closed ball.**  Two fixed points of a `LipschitzOnWith K`
(`K < 1`) map that both lie in the ball coincide (`dist u u' ≤ K · dist u u'` with `K < 1` forces
`dist u u' = 0`).  With existence this makes the ball-localised Ricci–DeTurck solution unique. -/
theorem eq_of_fixedPoint_of_lipschitzOnWith_closedBall
    {g : ParabolicC0AlphaBanach X E α s → ParabolicC0AlphaBanach X E α s}
    {c : ParabolicC0AlphaBanach X E α s} {r : ℝ} {K : ℝ≥0} (hK : K < 1)
    (hg : LipschitzOnWith K g (Metric.closedBall c r))
    {u u' : ParabolicC0AlphaBanach X E α s}
    (hu : u ∈ Metric.closedBall c r) (hu' : u' ∈ Metric.closedBall c r)
    (hfu : g u = u) (hfu' : g u' = u') : u = u' := by
  have hd : dist u u' ≤ (K : ℝ) * dist u u' := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hg) u hu u' hu'
    rwa [hfu, hfu'] at h
  have hKr : (K : ℝ) < 1 := by exact_mod_cast hK
  have hnn : (0 : ℝ) ≤ dist u u' := dist_nonneg
  have hdist : dist u u' ≤ 0 := by nlinarith
  exact dist_le_zero.mp hdist

/-- **Short-time / small-ball existence for the quadratic Ricci–DeTurck right-hand side.**  For a
linear part `A`, the quadratic nonlinearity `u ↦ L(u, u)` (`mulBilinL L`), and frozen data `f`, if the
ball radius / time is small enough that the right-hand side is a *contraction* on `closedBall c r`
(`‖A‖ + 2‖L‖(‖c‖ + r) < 1`, the diagonal Lipschitz constant on the ball, `lipschitzOnWith_mulBilinL_diag`)
**and** preserves that ball (`hmaps`, the invariant-ball hypothesis), then the quadratic Ricci–DeTurck
fixed-point equation `A u + L(u, u) + f = u` has a solution in the ball.  This is the honest quadratic
short-time chart existence — the quadratic analogue of the globally-Lipschitz
`affinePlusLipschitzFixedPoint_mem_closedBall`, valid for the genuinely *only locally* Lipschitz
Ricci–DeTurck nonlinearity. -/
theorem exists_fixedPoint_quadraticRHS_closedBall [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s)
    (c : ParabolicC0AlphaBanach X E α s) {r : ℝ} (hr : 0 ≤ r)
    (hcontract : ‖A‖ + 2 * ‖L‖ * (‖c‖ + r) < 1)
    (hmaps : Set.MapsTo (fun u => A u + mulBilinL L u u + f)
      (Metric.closedBall c r) (Metric.closedBall c r)) :
    ∃ u ∈ Metric.closedBall c r, A u + mulBilinL L u u + f = u := by
  set K : ℝ≥0 := (‖A‖ + 2 * ‖L‖ * (‖c‖ + r)).toNNReal with hKdef
  have hKcoe : (K : ℝ) = ‖A‖ + 2 * ‖L‖ * (‖c‖ + r) := by
    rw [hKdef]; exact Real.coe_toNNReal _ (by positivity)
  have hK : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]; exact hcontract
  have hlip : LipschitzOnWith K (fun u => A u + mulBilinL L u u + f)
      (Metric.closedBall c r) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro u hu v hv
    have hu' : ‖u‖ ≤ ‖c‖ + r := by
      have hdc : dist u c ≤ r := Metric.mem_closedBall.mp hu
      have hsub : ‖u‖ - ‖c‖ ≤ ‖u - c‖ := norm_sub_norm_le u c
      rw [dist_eq_norm] at hdc; linarith
    have hv' : ‖v‖ ≤ ‖c‖ + r := by
      have hdc : dist v c ≤ r := Metric.mem_closedBall.mp hv
      have hsub : ‖v‖ - ‖c‖ ≤ ‖v - c‖ := norm_sub_norm_le v c
      rw [dist_eq_norm] at hdc; linarith
    have huv : ‖u‖ + ‖v‖ ≤ 2 * (‖c‖ + r) := by linarith
    rw [dist_eq_norm, dist_eq_norm, hKcoe]
    have hsplit : (A u + mulBilinL L u u + f) - (A v + mulBilinL L v v + f)
        = A (u - v) + (mulBilinL L u u - mulBilinL L v v) := by
      rw [map_sub]; abel
    rw [hsplit]
    calc ‖A (u - v) + (mulBilinL L u u - mulBilinL L v v)‖
        ≤ ‖A (u - v)‖ + ‖mulBilinL L u u - mulBilinL L v v‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖u - v‖ + ‖L‖ * (‖u‖ + ‖v‖) * ‖u - v‖ :=
          add_le_add (A.le_opNorm _) (norm_mulBilinL_diag_sub_le L u v)
      _ ≤ ‖A‖ * ‖u - v‖ + ‖L‖ * (2 * (‖c‖ + r)) * ‖u - v‖ := by gcongr
      _ = (‖A‖ + 2 * ‖L‖ * (‖c‖ + r)) * ‖u - v‖ := by ring
  exact exists_fixedPoint_of_lipschitzOnWith_closedBall hr hK hlip hmaps

/-- **The quadratic Ricci–DeTurck right-hand side preserves a small ball around the origin.**  If
`‖A‖·r + ‖L‖·r² + ‖f‖ ≤ r` then `u ↦ A u + L(u, u) + f` maps `closedBall 0 r` into itself — the
invariant-ball (self-mapping) datum, derived from explicit scalar smallness of the data.  On a short
time interval `‖f‖` is small (the initial data enters through `f`), so this holds for a suitable `r`. -/
theorem mapsTo_quadraticRHS_closedBall_zero
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s) {r : ℝ}
    (hself : ‖A‖ * r + ‖L‖ * r * r + ‖f‖ ≤ r) :
    Set.MapsTo (fun u => A u + mulBilinL L u u + f)
      (Metric.closedBall 0 r) (Metric.closedBall 0 r) := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg u) hu
  show A u + mulBilinL L u u + f ∈ Metric.closedBall 0 r
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖A u + mulBilinL L u u + f‖
      ≤ ‖A u + mulBilinL L u u‖ + ‖f‖ := norm_add_le _ _
    _ ≤ (‖A u‖ + ‖mulBilinL L u u‖) + ‖f‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (‖A‖ * ‖u‖ + ‖L‖ * ‖u‖ * ‖u‖) + ‖f‖ :=
        add_le_add (add_le_add (A.le_opNorm u) (norm_mulBilinL_diag_le L u)) le_rfl
    _ ≤ (‖A‖ * r + ‖L‖ * r * r) + ‖f‖ := by
        have h1 : ‖A‖ * ‖u‖ ≤ ‖A‖ * r := mul_le_mul_of_nonneg_left hu (norm_nonneg A)
        have hLu : ‖L‖ * ‖u‖ ≤ ‖L‖ * r := mul_le_mul_of_nonneg_left hu (norm_nonneg L)
        have h2 : ‖L‖ * ‖u‖ * ‖u‖ ≤ ‖L‖ * r * r :=
          calc ‖L‖ * ‖u‖ * ‖u‖ ≤ ‖L‖ * r * ‖u‖ := mul_le_mul_of_nonneg_right hLu (norm_nonneg u)
            _ ≤ ‖L‖ * r * r := mul_le_mul_of_nonneg_left hu (mul_nonneg (norm_nonneg L) hr0)
        linarith
    _ ≤ r := by linarith

/-- **Fully scalar-data-driven short-time existence for the quadratic Ricci–DeTurck right-hand side.**
From the contraction condition `‖A‖ + 2‖L‖r < 1` and the invariant-ball condition
`‖A‖·r + ‖L‖·r² + ‖f‖ ≤ r` alone — both explicit scalar smallness bounds on the data — the quadratic
equation `A u + L(u, u) + f = u` has a solution in `closedBall 0 r`.  Combines the self-mapping datum
`mapsTo_quadraticRHS_closedBall_zero` with the ball existence
`exists_fixedPoint_quadraticRHS_closedBall`, so no set-theoretic `MapsTo` hypothesis needs to be
supplied: the honest short-time chart existence stated purely from the operator/data norms. -/
theorem exists_fixedPoint_quadraticRHS_closedBall_zero [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s) {r : ℝ} (hr : 0 ≤ r)
    (hcontract : ‖A‖ + 2 * ‖L‖ * r < 1)
    (hself : ‖A‖ * r + ‖L‖ * r * r + ‖f‖ ≤ r) :
    ∃ u ∈ Metric.closedBall (0 : ParabolicC0AlphaBanach X E α s) r,
      A u + mulBilinL L u u + f = u := by
  refine exists_fixedPoint_quadraticRHS_closedBall A L f 0 hr ?_
    (mapsTo_quadraticRHS_closedBall_zero A L f hself)
  simpa using hcontract

/-- **The quadratic Ricci–DeTurck right-hand side is Lipschitz on every closed ball.**  On
`closedBall c r` (`0 ≤ r`), `u ↦ A u + L(u, u) + f` is `LipschitzOnWith (‖A‖ + 2‖L‖(‖c‖+r))` — the
linear part contributes `‖A‖` and the quadratic diagonal `2‖L‖(‖c‖+r)`
(`norm_mulBilinL_diag_sub_le`).  The named contraction property of the DeTurck right-hand side,
supplying both the short-time contraction (when `‖A‖ + 2‖L‖(‖c‖+r) < 1`) and the in-ball uniqueness. -/
theorem lipschitzOnWith_quadraticRHS_closedBall
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s)
    (c : ParabolicC0AlphaBanach X E α s) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzOnWith (‖A‖ + 2 * ‖L‖ * (‖c‖ + r)).toNNReal
      (fun u => A u + mulBilinL L u u + f) (Metric.closedBall c r) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have hu' : ‖u‖ ≤ ‖c‖ + r := by
    have hdc : dist u c ≤ r := Metric.mem_closedBall.mp hu
    have hsub : ‖u‖ - ‖c‖ ≤ ‖u - c‖ := norm_sub_norm_le u c
    rw [dist_eq_norm] at hdc; linarith
  have hv' : ‖v‖ ≤ ‖c‖ + r := by
    have hdc : dist v c ≤ r := Metric.mem_closedBall.mp hv
    have hsub : ‖v‖ - ‖c‖ ≤ ‖v - c‖ := norm_sub_norm_le v c
    rw [dist_eq_norm] at hdc; linarith
  have huv : ‖u‖ + ‖v‖ ≤ 2 * (‖c‖ + r) := by linarith
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have hsplit : (A u + mulBilinL L u u + f) - (A v + mulBilinL L v v + f)
      = A (u - v) + (mulBilinL L u u - mulBilinL L v v) := by rw [map_sub]; abel
  rw [hsplit]
  calc ‖A (u - v) + (mulBilinL L u u - mulBilinL L v v)‖
      ≤ ‖A (u - v)‖ + ‖mulBilinL L u u - mulBilinL L v v‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖u - v‖ + ‖L‖ * (‖u‖ + ‖v‖) * ‖u - v‖ :=
        add_le_add (A.le_opNorm _) (norm_mulBilinL_diag_sub_le L u v)
    _ ≤ ‖A‖ * ‖u - v‖ + ‖L‖ * (2 * (‖c‖ + r)) * ‖u - v‖ := by gcongr
    _ = (‖A‖ + 2 * ‖L‖ * (‖c‖ + r)) * ‖u - v‖ := by ring

/-- **Uniqueness of the quadratic Ricci–DeTurck solution in a ball.**  Under the contraction condition
`‖A‖ + 2‖L‖(‖c‖+r) < 1`, two solutions of `A u + L(u, u) + f = u` lying in `closedBall c r` coincide.
With the existence `exists_fixedPoint_quadraticRHS_closedBall` this is the full well-posedness of the
quadratic Ricci–DeTurck short-time chart solution. -/
theorem eq_of_fixedPoint_quadraticRHS_closedBall
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s)
    (c : ParabolicC0AlphaBanach X E α s) {r : ℝ}
    (hcontract : ‖A‖ + 2 * ‖L‖ * (‖c‖ + r) < 1)
    {u u' : ParabolicC0AlphaBanach X E α s}
    (hu : u ∈ Metric.closedBall c r) (hu' : u' ∈ Metric.closedBall c r)
    (hfu : A u + mulBilinL L u u + f = u) (hfu' : A u' + mulBilinL L u' u' + f = u') :
    u = u' := by
  have hr0 : (0 : ℝ) ≤ r := le_trans dist_nonneg (Metric.mem_closedBall.mp hu)
  have hK : (‖A‖ + 2 * ‖L‖ * (‖c‖ + r)).toNNReal < 1 := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity), NNReal.coe_one]
    exact hcontract
  exact eq_of_fixedPoint_of_lipschitzOnWith_closedBall hK
    (lipschitzOnWith_quadraticRHS_closedBall A L f c hr0) hu hu' hfu hfu'

/-- **Well-posedness of the quadratic Ricci–DeTurck short-time chart solution.**  From the two scalar
smallness conditions `‖A‖ + 2‖L‖r < 1` (contraction) and `‖A‖·r + ‖L‖·r² + ‖f‖ ≤ r` (invariant ball),
the quadratic equation `A u + L(u, u) + f = u` has a **unique** solution in `closedBall 0 r`.  Bundles
`exists_fixedPoint_quadraticRHS_closedBall_zero` (existence) with
`eq_of_fixedPoint_quadraticRHS_closedBall` (in-ball uniqueness): the well-posed short-time chart datum
the Ricci–DeTurck chart closure consumes, stated purely from the operator/data norms. -/
theorem existsUnique_fixedPoint_quadraticRHS_closedBall_zero [CompleteSpace E]
    (A : ParabolicC0AlphaBanach X E α s →L[ℝ] ParabolicC0AlphaBanach X E α s)
    (L : E →L[ℝ] E →L[ℝ] E) (f : ParabolicC0AlphaBanach X E α s) {r : ℝ} (hr : 0 ≤ r)
    (hcontract : ‖A‖ + 2 * ‖L‖ * r < 1)
    (hself : ‖A‖ * r + ‖L‖ * r * r + ‖f‖ ≤ r) :
    ∃! u, u ∈ Metric.closedBall (0 : ParabolicC0AlphaBanach X E α s) r ∧
      A u + mulBilinL L u u + f = u := by
  obtain ⟨u, hu_mem, hu_eq⟩ :=
    exists_fixedPoint_quadraticRHS_closedBall_zero A L f hr hcontract hself
  refine ⟨u, ⟨hu_mem, hu_eq⟩, ?_⟩
  rintro u' ⟨hu'_mem, hu'_eq⟩
  exact eq_of_fixedPoint_quadraticRHS_closedBall A L f 0 (by simpa using hcontract)
    hu'_mem hu_mem hu'_eq hu_eq

end ParabolicC0AlphaBanach

end AnalyticPDE
end RicciFlow
