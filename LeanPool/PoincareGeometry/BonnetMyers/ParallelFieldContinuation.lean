/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.TransportContinuation
import LeanPool.PoincareGeometry.BonnetMyers.GeodesicContinuation
import LeanPool.PoincareGeometry.BonnetMyers.ChartGluing
import LeanPool.PoincareGeometry.BonnetMyers.ParallelReflection

/-!
# Maximal parallel fields along a complete geodesic

This module begins the genuinely global parallel-transport construction.  A
field is represented on an open time interval of a fixed global geodesic, with
its values outside that interval normalized to zero.  At every point in its
domain it agrees, as a tangent-bundle-valued germ, with an actual local
parallel transport.  The normalization makes chain unions literal functions,
so that Zorn's lemma can later be applied without treating fields on different
domains as definitionally equal.

The endpoint-extension argument remains separate: it will use the bounded
linear-transport continuation theorem from `ODEContinuation` after converting
the field into endpoint-chart coordinates.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic
namespace GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- A local piece of a parallel field based at time `t₀` of a fixed global
geodesic.  The time parameter is relative to `t₀`; consequently the fibres
are those of `shift γ t₀`.  Each in-domain point comes with a real local
parallel germ, and `field_outside` gives a canonical representative for
chain unions. -/
structure PartialParallelField
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀)) where
  domain : Set ℝ
  domain_open : IsOpen domain
  domain_preconnected : IsPreconnected domain
  zero_mem : (0 : ℝ) ∈ domain
  field : ∀ s : ℝ, TM (curve (shift γ t₀) s)
  field_zero : field 0 = w₀
  field_outside : ∀ s, s ∉ domain → field s = 0
  local_germ : ∀ s ∈ domain,
    ∃ p : ParallelGerm (I := I) (M := M) γ (t₀ + s) (field s),
      ∀ᶠ u in 𝓝 (0 : ℝ),
        (⟨curve (shift γ (t₀ + s)) u, field (s + u)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + s)) u, p.shiftedField u⟩

private theorem totalSpace_cast_eq {x y : M} (hxy : x = y) (v : TM x) :
    (⟨y, cast (congrArg (TangentSpace I) hxy) v⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨x, v⟩ := by
  subst y
  rfl

/-- At time zero, the partial-field value agrees with its prescribed initial
tangent as a point of the tangent bundle.  This is the reusable bridge between
the shifted field fibre and the unshifted initial fibre. -/
theorem PartialParallelField.field_zero_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀) :
    (⟨curve (shift γ t₀) 0, p.field 0⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve γ t₀, w₀⟩ := by
  let hbase : curve (shift γ t₀) 0 = curve γ t₀ := by
    change curve γ (t₀ + 0) = curve γ t₀
    congr 1
    ring
  have hcast :
      cast (congrArg (TangentSpace I) hbase) (p.field 0) = w₀ := by
    exact p.field_zero
  calc
    (⟨curve (shift γ t₀) 0, p.field 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, cast (congrArg (TangentSpace I) hbase) (p.field 0)⟩ :=
        (totalSpace_cast_eq hbase (p.field 0)).symm
    _ = ⟨curve γ t₀, w₀⟩ := by rw [hcast]

/-- Reindex a parallel germ when two presentations of its base time are
equal.  The transported initial tangent is explicit; this avoids treating
associativity of time addition as a definitional equality of tangent fibres. -/
noncomputable def ParallelGerm.rebaseTime
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ t₂ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w) (h : t₁ = t₂) :
    ParallelGerm (I := I) (M := M) γ t₂
      (cast (congrArg (fun t ↦ TM (curve γ t)) h) w) := by
  subst t₂
  exact p

/-- The reindexed germ has the same actual tangent-bundle field after the
corresponding time-origin change. -/
theorem ParallelGerm.rebaseTime_shiftedField_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ t₂ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w) (h : t₁ = t₂) (s : ℝ) :
    (⟨curve (shift γ t₂) s, (p.rebaseTime h).shiftedField s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve (shift γ t₁) s, p.shiftedField s⟩ := by
  subst t₂
  rfl

/-- Reindex only the prescribed initial tangent of a parallel germ along an
equality in one fixed tangent fibre. -/
noncomputable def ParallelGerm.castInitial
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w w' : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (h : w = w') :
    ParallelGerm (I := I) (M := M) γ t₀ w' := by
  subst w'
  exact p

/-- Changing only a germ's initial-vector presentation leaves its shifted
field unchanged as a total tangent-bundle value. -/
theorem ParallelGerm.castInitial_shiftedField_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w w' : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (h : w = w') (s : ℝ) :
    (⟨curve (shift γ t₀) s, (p.castInitial h).shiftedField s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve (shift γ t₀) s, p.shiftedField s⟩ := by
  subst w'
  rfl

private theorem cast_tangent_eq_of_eq {x y : M} (hxy hxy' : x = y)
    (v : TM x) :
    cast (congrArg (TangentSpace I) hxy) v =
      cast (congrArg (TangentSpace I) hxy') v := by
  subst y
  rfl

private theorem cast_tangent_zero_of_eq {x y : M} (hxy : x = y) :
    cast (congrArg (TangentSpace I) hxy) (0 : TM x) = (0 : TM y) := by
  subst y
  rfl

private theorem cast_tangent_curve_eq_of_time_eq
    {γ : ℝ → M} {a b : ℝ} (hab : a = b) (v : TM (γ a)) :
    cast (congrArg (fun t ↦ TM (γ t)) hab) v =
      cast (congrArg (TangentSpace I) (congrArg γ hab)) v := by
  subst b
  rfl

/-- View a restarted parallel field at an absolute global-geodesic time.
The definition carries the time-arithmetic fibre transport explicitly. -/
noncomputable def ParallelGerm.absoluteField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (t : ℝ) : TM (curve γ t) := by
  let htime : t₀ + (t - t₀) = t := by ring
  exact cast (congrArg (fun s ↦ TM (curve γ s)) htime)
    (p.shiftedField (t - t₀))

/-- Total-space form of `absoluteField`: its coordinate-free value is exactly
the original shifted field, with the time arithmetic visible in the base. -/
theorem ParallelGerm.absoluteField_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (t : ℝ) :
    (⟨curve γ t, p.absoluteField t⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve (shift γ t₀) (t - t₀), p.shiftedField (t - t₀)⟩ := by
  let htime : t₀ + (t - t₀) = t := by ring
  change
    (⟨curve γ t, cast (congrArg (fun s ↦ TM (curve γ s)) htime)
      (p.shiftedField (t - t₀))⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve γ (t₀ + (t - t₀)), p.shiftedField (t - t₀)⟩
  exact totalSpace_cast_eq (I := I) (E := E)
    (congrArg (curve γ) htime) (p.shiftedField (t - t₀))

/-- At a syntactically translated time, `absoluteField` is the original
shifted field without any residual fibre transport. -/
theorem ParallelGerm.absoluteField_add_eq_shiftedField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (τ : ℝ) :
    p.absoluteField (t₀ + τ) = p.shiftedField τ := by
  have hsub : (t₀ + τ) - t₀ = τ := by ring
  have htotal := p.absoluteField_totalState (t₀ + τ)
  have hshift :
      (⟨curve (shift γ t₀) ((t₀ + τ) - t₀),
        p.shiftedField ((t₀ + τ) - t₀)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) τ, p.shiftedField τ⟩ :=
    congrArg (fun s ↦
      (⟨curve (shift γ t₀) s, p.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) hsub
  have hresult := htotal.trans hshift
  exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
    (curve γ (t₀ + τ)) (p.absoluteField (t₀ + τ)) (p.shiftedField τ)).mp
      (by simpa only [shift_curve] using hresult)

/-- Restart coherence expressed at absolute times.  This is the version used
when adjoining an endpoint-germ interval to a partial parallel field. -/
theorem ParallelGerm.eventually_absoluteField_totalState_eq_of_restart
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelGerm (I := I) (M := M) γ (t₀ + τ)
        (p.absoluteField (t₀ + τ)),
      ∀ᶠ s in 𝓝 (0 : ℝ),
        (⟨curve (shift γ (t₀ + τ)) s,
          p.absoluteField (t₀ + τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := by
  obtain ⟨r, hr, hrestart⟩ := p.eventually_totalState_eq_of_restart hmetric
  refine ⟨r, hr, ?_⟩
  intro τ hτ q
  have habs : p.absoluteField (t₀ + τ) = p.shiftedField τ :=
    p.absoluteField_add_eq_shiftedField τ
  let qraw : ParallelGerm (I := I) (M := M) γ (t₀ + τ)
      (p.shiftedField τ) := q.castInitial habs
  have hqraw : ∀ s : ℝ,
      (⟨curve (shift γ (t₀ + τ)) s, qraw.shiftedField s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := by
    intro s
    simpa only [qraw] using q.castInitial_shiftedField_totalState habs s
  filter_upwards [hrestart τ hτ qraw] with s hs
  have htime : t₀ + τ + s = t₀ + (τ + s) := by ring
  have htimeTotal := congrArg (fun r ↦
    (⟨curve γ r, p.absoluteField r⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _))) htime
  calc
    (⟨curve (shift γ (t₀ + τ)) s,
        p.absoluteField (t₀ + τ + s)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₀ + (τ + s)), p.absoluteField (t₀ + (τ + s))⟩ := by
        simpa only [shift_curve] using htimeTotal
    _ = ⟨curve γ (t₀ + (τ + s)), p.shiftedField (τ + s)⟩ := by
      rw [p.absoluteField_add_eq_shiftedField (τ + s)]
    _ = ⟨curve (shift γ (t₀ + τ)) s, p.shiftedField (τ + s)⟩ := by
      apply Bundle.TotalSpace.ext
      · exact congrArg (curve γ) htime.symm
      · exact heq_of_eq rfl
    _ = ⟨curve (shift γ (t₀ + τ)) s, qraw.shiftedField s⟩ := hs
    _ = ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := hqraw s

/-- Reexpress a local parallel germ as a field along an arbitrary shifted
presentation of the same global geodesic.  The explicit cast is essential:
the germ is centered at `t₁`, whereas the resulting field is indexed by time
relative to `origin`. -/
noncomputable def ParallelGerm.fieldAlong
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w)
    (origin s : ℝ) : TM (curve (shift γ origin) s) := by
  let htime : t₁ + ((origin + s) - t₁) = origin + s := by ring
  exact cast (congrArg (fun t ↦ TM (curve γ t)) htime)
    (p.absoluteField (t₁ + ((origin + s) - t₁)))

/-- Total-space form of `fieldAlong`.  This keeps all reindexing visible when
the field is compared with a partial field on an overlap. -/
theorem ParallelGerm.fieldAlong_totalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w)
    (origin s : ℝ) :
    (⟨curve (shift γ origin) s, p.fieldAlong origin s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve γ (t₁ + ((origin + s) - t₁)),
      p.absoluteField (t₁ + ((origin + s) - t₁))⟩ := by
  let htime : t₁ + ((origin + s) - t₁) = origin + s := by ring
  change
    (⟨curve γ (origin + s),
      cast (congrArg (fun t ↦ TM (curve γ t)) htime)
        (p.absoluteField (t₁ + ((origin + s) - t₁)))⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₁ + ((origin + s) - t₁)),
        p.absoluteField (t₁ + ((origin + s) - t₁))⟩
  exact totalSpace_cast_eq (I := I) (E := E)
    (congrArg (curve γ) htime)
    (p.absoluteField (t₁ + ((origin + s) - t₁)))

/-- The reindexed field is the original shifted germ in total-space form.
This is the bridge used to compare an endpoint restart with an old partial
field on a final overlap. -/
theorem ParallelGerm.fieldAlong_totalState_eq_shiftedField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w)
    (origin s : ℝ) :
    (⟨curve (shift γ origin) s, p.fieldAlong origin s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve (shift γ t₁) ((origin + s) - t₁),
      p.shiftedField ((origin + s) - t₁)⟩ := by
  let r : ℝ := t₁ + ((origin + s) - t₁)
  have hsub : r - t₁ = (origin + s) - t₁ := by
    dsimp [r]
    ring
  calc
    (⟨curve (shift γ origin) s, p.fieldAlong origin s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ r, p.absoluteField r⟩ := by
        simpa only [r] using p.fieldAlong_totalState origin s
    _ = ⟨curve (shift γ t₁) (r - t₁), p.shiftedField (r - t₁)⟩ :=
      p.absoluteField_totalState r
    _ = ⟨curve (shift γ t₁) ((origin + s) - t₁),
      p.shiftedField ((origin + s) - t₁)⟩ := by
        exact congrArg (fun u ↦
          (⟨curve (shift γ t₁) u, p.shiftedField u⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _))) hsub

/-- A germ supplies genuine local parallel germs for its reindexed absolute
field at every sufficiently nearby time.  Unlike a coordinate retyping, this
uses restart coherence and returns equality in the tangent-bundle total space. -/
theorem ParallelGerm.exists_relativeField_localGerm
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₁ : ℝ} {w : TM (curve γ t₁)}
    (p : ParallelGerm (I := I) (M := M) γ t₁ w)
    (hmetric : cov.IsMetricCompatibleTangent) (origin : ℝ) :
    ∃ r > (0 : ℝ), ∀ s : ℝ,
      (origin + s) - t₁ ∈ Ioo (-r) r →
      ∃ q : ParallelGerm (I := I) (M := M) γ (origin + s)
        (p.fieldAlong origin s),
        ∀ᶠ u in 𝓝 (0 : ℝ),
          (⟨curve (shift γ (origin + s)) u,
            p.fieldAlong origin (s + u)⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ (origin + s)) u, q.shiftedField u⟩ := by
  obtain ⟨r, hr, hrestart⟩ :=
    p.eventually_absoluteField_totalState_eq_of_restart hmetric
  refine ⟨r, hr, ?_⟩
  intro s hs
  let τ : ℝ := (origin + s) - t₁
  have htime : t₁ + τ = origin + s := by
    dsimp [τ]
    ring
  obtain ⟨qraw⟩ := exists_parallelGerm (I := I) (M := M) γ (t₁ + τ)
    (p.absoluteField (t₁ + τ)) hmetric
  have hqinitial :
      cast (congrArg (fun t ↦ TM (curve γ t)) htime)
        (p.absoluteField (t₁ + τ)) = p.fieldAlong origin s := by
    unfold ParallelGerm.fieldAlong
    congr 1
  let q : ParallelGerm (I := I) (M := M) γ (origin + s)
      (p.fieldAlong origin s) :=
    (qraw.rebaseTime htime).castInitial hqinitial
  refine ⟨q, ?_⟩
  have hraw := hrestart τ (by simpa only [τ] using hs) qraw
  filter_upwards [hraw] with u hu
  have htimeu :
      t₁ + ((origin + (s + u)) - t₁) = t₁ + τ + u := by
    dsimp [τ]
    ring
  have habs := congrArg (fun t ↦
    (⟨curve γ t, p.absoluteField t⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _))) htimeu
  calc
    (⟨curve (shift γ (origin + s)) u,
        p.fieldAlong origin (s + u)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₁ + ((origin + (s + u)) - t₁)),
        p.absoluteField (t₁ + ((origin + (s + u)) - t₁))⟩ := by
          convert p.fieldAlong_totalState origin (s + u) using 1
          apply Bundle.TotalSpace.ext
          · change curve γ (origin + s + u) = curve γ (origin + (s + u))
            congr 1
            ring
          · exact heq_of_eq rfl
    _ = ⟨curve γ (t₁ + τ + u), p.absoluteField (t₁ + τ + u)⟩ := habs
    _ = ⟨curve (shift γ (t₁ + τ)) u, qraw.shiftedField u⟩ := hu
    _ = ⟨curve (shift γ (origin + s)) u, q.shiftedField u⟩ := by
      calc
        (⟨curve (shift γ (t₁ + τ)) u, qraw.shiftedField u⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ (origin + s)) u,
            (qraw.rebaseTime htime).shiftedField u⟩ := by
              exact (qraw.rebaseTime_shiftedField_totalState htime u).symm
        _ = ⟨curve (shift γ (origin + s)) u, q.shiftedField u⟩ := by
              simpa only [q] using
                ((qraw.rebaseTime htime).castInitial_shiftedField_totalState
                  hqinitial u).symm

namespace PartialParallelField

/-- Read a partial field on the time-reversed complete geodesic as a field on
the original geodesic at the opposite relative time.  The two base curves are
related by explicit time arithmetic and every fibre transport is an explicit
cast rather than a definitional identification. -/
noncomputable def reflectedField
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ : ℝ) {w : TM (curve (reverseAt γ t₀) 0)}
    (p : PartialParallelField (I := I) (M := M) (reverseAt γ t₀) 0 w)
    (s : ℝ) : TM (curve (shift γ t₀) s) := by
  let hsource : curve (shift (reverseAt γ t₀) 0) (-s) =
      curve (reverseAt γ t₀) (-s) := by
    change curve γ (t₀ - (0 + -s)) = curve γ (t₀ - (-s))
    congr 1
    ring
  let z : TM (curve (reverseAt γ t₀) (-s)) :=
    cast (congrArg (TangentSpace I) hsource) (p.field (-s))
  let htarget : curve γ (t₀ - (-s)) = curve (shift γ t₀) s := by
    change curve γ (t₀ - (-s)) = curve γ (t₀ + s)
    congr 1
    ring
  exact cast (congrArg (TangentSpace I) htarget)
    (reindexedReflectInitial γ t₀ (-s) z)

/-- Total-space form of `reflectedField`: it is precisely the original
reversed partial field at opposite time. -/
theorem reflectedField_totalState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ : ℝ) {w : TM (curve (reverseAt γ t₀) 0)}
    (p : PartialParallelField (I := I) (M := M) (reverseAt γ t₀) 0 w)
    (s : ℝ) :
    (⟨curve (shift γ t₀) s, p.reflectedField t₀ s⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift (reverseAt γ t₀) 0) (-s), p.field (-s)⟩ := by
  let hsource : curve (shift (reverseAt γ t₀) 0) (-s) =
      curve (reverseAt γ t₀) (-s) := by
    change curve γ (t₀ - (0 + -s)) = curve γ (t₀ - (-s))
    congr 1
    ring
  let z : TM (curve (reverseAt γ t₀) (-s)) :=
    cast (congrArg (TangentSpace I) hsource) (p.field (-s))
  let htarget : curve γ (t₀ - (-s)) = curve (shift γ t₀) s := by
    change curve γ (t₀ - (-s)) = curve γ (t₀ + s)
    congr 1
    ring
  change (⟨curve (shift γ t₀) s,
    cast (congrArg (TangentSpace I) htarget)
      (reindexedReflectInitial γ t₀ (-s) z)⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨curve (shift (reverseAt γ t₀) 0) (-s), p.field (-s)⟩
  calc
    (⟨curve (shift γ t₀) s,
      cast (congrArg (TangentSpace I) htarget)
        (reindexedReflectInitial γ t₀ (-s) z)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₀ - (-s)), reindexedReflectInitial γ t₀ (-s) z⟩ :=
        totalSpace_cast_eq htarget (reindexedReflectInitial γ t₀ (-s) z)
    _ = ⟨curve (reverseAt γ t₀) (-s), z⟩ :=
      reindexInitialVector_totalState
        (reverseAt_reflectState γ t₀ (-s)) z
    _ = ⟨curve (shift (reverseAt γ t₀) 0) (-s), p.field (-s)⟩ :=
      totalSpace_cast_eq hsource (p.field (-s))

/-- At every reflected in-domain time there is a genuine parallel germ with
the value prescribed by `reflectedField`.  This isolates the initial-value
bookkeeping before the local-overlap proof assembles a reflected partial
field. -/
theorem exists_reflectedParallelGerm
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ : ℝ) {w : TM (curve (reverseAt γ t₀) 0)}
    (p : PartialParallelField (I := I) (M := M) (reverseAt γ t₀) 0 w)
    (hmetric : cov.IsMetricCompatibleTangent) (s : ℝ)
    (hs : -s ∈ p.domain) :
    ∃ q : ParallelGerm (I := I) (M := M) γ (t₀ + s)
      (p.reflectedField t₀ s),
      ∀ᶠ u in 𝓝 (0 : ℝ),
        (⟨curve (shift γ (t₀ + s)) u,
          p.reflectedField t₀ (s + u)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + s)) u, q.shiftedField u⟩ := by
  obtain ⟨q, hq⟩ := p.local_germ (-s) hs
  let hsource : curve (shift (reverseAt γ t₀) 0) (-s) =
      curve (reverseAt γ t₀) (-s) := by
    change curve γ (t₀ - (0 + -s)) = curve γ (t₀ - (-s))
    congr 1
    ring
  let z : TM (curve (reverseAt γ t₀) (-s)) :=
    cast (congrArg (TangentSpace I) hsource) (p.field (-s))
  let hqtime : 0 + (-s) = -s := by ring
  let hqbase : curve (reverseAt γ t₀) (0 + -s) =
      curve (reverseAt γ t₀) (-s) :=
    congrArg (fun t ↦ curve (reverseAt γ t₀) t) hqtime
  have hcast :
      cast (congrArg (fun t ↦ TM (curve (reverseAt γ t₀) t)) hqtime)
        (p.field (-s)) =
        cast (congrArg (TangentSpace I) hqbase) (p.field (-s)) :=
    by
      change cast (congrArg (TangentSpace I) hsource) (p.field (-s)) =
        cast (congrArg (TangentSpace I) hqbase) (p.field (-s))
      exact cast_tangent_eq_of_eq hsource hqbase (p.field (-s))
  have hmid :
      (⟨curve (reverseAt γ t₀) (0 + -s), p.field (-s)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift (reverseAt γ t₀) 0) (-s), p.field (-s)⟩ := by
    rfl
  have hqz :
      cast (congrArg (fun t ↦ TM (curve (reverseAt γ t₀) t)) hqtime)
        (p.field (-s)) = z := by
    apply (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
      (curve (reverseAt γ t₀) (-s)) _ _).mp
    calc
      (⟨curve (reverseAt γ t₀) (-s),
        cast (congrArg (fun t ↦ TM (curve (reverseAt γ t₀) t)) hqtime)
          (p.field (-s))⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (reverseAt γ t₀) (-s),
          cast (congrArg (TangentSpace I) hqbase) (p.field (-s))⟩ := by
          rw [hcast]
      _ = ⟨curve (reverseAt γ t₀) (0 + -s), p.field (-s)⟩ :=
        totalSpace_cast_eq hqbase (p.field (-s))
      _ = ⟨curve (shift (reverseAt γ t₀) 0) (-s), p.field (-s)⟩ := hmid
      _ = ⟨curve (reverseAt γ t₀) (-s), z⟩ :=
        (totalSpace_cast_eq hsource (p.field (-s))).symm
  let qtime := q.rebaseTime hqtime
  let q' := qtime.castInitial hqz
  let qreflect := q'.reflectReverseAt γ t₀ (-s) hmetric
  let htime : t₀ - (-s) = t₀ + s := by ring
  let qbase := qreflect.rebaseTime htime
  have hbaseinitial :
      cast (congrArg (fun t ↦ TM (curve γ t)) htime)
        (reindexedReflectInitial γ t₀ (-s) z) =
        p.reflectedField t₀ s := by
    let htarget : curve γ (t₀ - (-s)) = curve (shift γ t₀) s :=
      congrArg (fun t ↦ curve γ t) htime
    unfold reflectedField
    change cast (congrArg (fun t ↦ TM (curve γ t)) htime)
        (reindexedReflectInitial γ t₀ (-s) z) =
      cast (congrArg (TangentSpace I) htarget)
        (reindexedReflectInitial γ t₀ (-s) z)
    exact cast_tangent_curve_eq_of_time_eq htime
      (reindexedReflectInitial γ t₀ (-s) z)
  let qfinal := qbase.castInitial hbaseinitial
  refine ⟨qfinal, ?_⟩
  have hneg : Tendsto (fun u : ℝ ↦ -u) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun u : ℝ ↦ -u) 0 :=
      (continuousAt_id : ContinuousAt (fun u : ℝ ↦ u) 0).neg
    simpa using hcont.tendsto
  have hqneg := hneg.eventually hq
  have hreflect := q'.reflectReverseAt_shiftedField_eventuallyEq
    γ t₀ (-s) hmetric
  filter_upwards [hqneg, hreflect] with u hu hreflectu
  have hfield :
      (⟨curve (shift γ t₀) (s + u),
        p.reflectedField t₀ (s + u)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u), q.shiftedField (-u)⟩ := by
    calc
      (⟨curve (shift γ t₀) (s + u),
        p.reflectedField t₀ (s + u)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift (reverseAt γ t₀) 0) (-(s + u)),
          p.field (-(s + u))⟩ :=
          p.reflectedField_totalState t₀ (s + u)
      _ = ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u),
          q.shiftedField (-u)⟩ := by
          have htime : -(s + u) = -s + -u := by ring
          have hbase :
              (⟨curve (shift (reverseAt γ t₀) 0) (-s + -u),
                p.field (-s + -u)⟩ :
                  Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
              ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u),
                p.field (-s + -u)⟩ := by
            apply Bundle.TotalSpace.ext
            · change curve (reverseAt γ t₀) (0 + (-s + -u)) =
                curve (reverseAt γ t₀) ((0 + -s) + -u)
              congr 1
              ring
            · exact heq_of_eq rfl
          calc
            (⟨curve (shift (reverseAt γ t₀) 0) (-(s + u)),
              p.field (-(s + u))⟩ :
                Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
              ⟨curve (shift (reverseAt γ t₀) 0) (-s + -u),
                p.field (-s + -u)⟩ :=
                congrArg (fun r ↦
                  (⟨curve (shift (reverseAt γ t₀) 0) r, p.field r⟩ :
                    Bundle.TotalSpace E (TangentSpace I : M → Type _))) htime
            _ = ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u),
              p.field (-s + -u)⟩ := hbase
            _ = ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u),
              q.shiftedField (-u)⟩ := hu
  have hqtimeTotal := q.rebaseTime_shiftedField_totalState hqtime (-u)
  have hqcastTotal := qtime.castInitial_shiftedField_totalState hqz (-u)
  have hqbaseTotal := qreflect.rebaseTime_shiftedField_totalState htime u
  have hqfinalTotal := qbase.castInitial_shiftedField_totalState hbaseinitial u
  have htotal :
      (⟨curve (shift γ t₀) (s + u),
        p.reflectedField t₀ (s + u)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ (t₀ + s)) u, qfinal.shiftedField u⟩ := by
    calc
      (⟨curve (shift γ t₀) (s + u),
        p.reflectedField t₀ (s + u)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift (reverseAt γ t₀) (0 + -s)) (-u),
          q.shiftedField (-u)⟩ := hfield
      _ = ⟨curve (shift (reverseAt γ t₀) (-s)) (-u),
          qtime.shiftedField (-u)⟩ := hqtimeTotal.symm
      _ = ⟨curve (shift (reverseAt γ t₀) (-s)) (-u),
          q'.shiftedField (-u)⟩ := hqcastTotal.symm
      _ = ⟨curve (shift γ (t₀ - (-s))) u,
          qreflect.shiftedField u⟩ := hreflectu.symm
      _ = ⟨curve (shift γ (t₀ + s)) u,
          qbase.shiftedField u⟩ := hqbaseTotal.symm
      _ = ⟨curve (shift γ (t₀ + s)) u,
          qfinal.shiftedField u⟩ := hqfinalTotal.symm
  have hleft :
      (⟨curve (shift γ (t₀ + s)) u,
        p.reflectedField t₀ (s + u)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) (s + u), p.reflectedField t₀ (s + u)⟩ := by
    apply Bundle.TotalSpace.ext
    · change curve γ ((t₀ + s) + u) = curve γ (t₀ + (s + u))
      congr 1
      ring
    · exact heq_of_eq rfl
  exact hleft.trans htotal

/-- Retype only the prescribed initial vector of a partial parallel field.
The field and its local certificates are unchanged; the equality is kept
explicit because the base tangent fibre is dependent. -/
noncomputable def castInitial
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w w' : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w) (h : w = w') :
    PartialParallelField (I := I) (M := M) γ t₀ w' := by
  subst w'
  exact p

@[simp] theorem castInitial_domain
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w w' : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w) (h : w = w') :
    (p.castInitial h).domain = p.domain := by
  subst w'
  rfl

/-- Retype a partial field's initial vector from a certified total-space
equality at time zero.  Unlike `castInitial`, this crosses the explicit
shifted/unshifted base-point presentation. -/
noncomputable def retypeInitialOfTotalState
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w)
    {w' : TM (curve γ t₀)}
    (h : (⟨curve (shift γ t₀) 0, p.field 0⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, w'⟩) :
    PartialParallelField (I := I) (M := M) γ t₀ w' where
  domain := p.domain
  domain_open := p.domain_open
  domain_preconnected := p.domain_preconnected
  zero_mem := p.zero_mem
  field := p.field
  field_zero := by
    let hbase : curve (shift γ t₀) 0 = curve γ t₀ := by
      change curve γ (t₀ + 0) = curve γ t₀
      congr 1
      ring
    change cast (congrArg (TangentSpace I) hbase) (p.field 0) = w'
    apply (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
      (curve γ t₀) (cast (congrArg (TangentSpace I) hbase) (p.field 0)) w').mp
    calc
      (⟨curve γ t₀, cast (congrArg (TangentSpace I) hbase) (p.field 0)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ t₀) 0, p.field 0⟩ :=
          totalSpace_cast_eq hbase (p.field 0)
      _ = ⟨curve γ t₀, w'⟩ := h
  field_outside := p.field_outside
  local_germ := p.local_germ

@[simp] theorem retypeInitialOfTotalState_domain
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w)
    {w' : TM (curve γ t₀)}
    (h : (⟨curve (shift γ t₀) 0, p.field 0⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, w'⟩) :
    (p.retypeInitialOfTotalState h).domain = p.domain := rfl

/-- Coherent partial fields with the same initial tangent agree on a common
neighbourhood of their time origin, expressed in the tangent-bundle total
space.  The explicitly restarted time origin avoids hiding a fibre cast in
the splice construction. -/
theorem eventually_local_totalState_eq_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p q : PartialParallelField (I := I) (M := M) γ t₀ w₀) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      (⟨curve (shift γ (t₀ + 0)) s, p.field (0 + s)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ (t₀ + 0)) s, q.field (0 + s)⟩ := by
  obtain ⟨gp, hp⟩ := p.local_germ 0 p.zero_mem
  obtain ⟨gq, hq⟩ := q.local_germ 0 q.zero_mem
  have hinit : q.field 0 = p.field 0 := q.field_zero.trans p.field_zero.symm
  let gq' := gq.castInitial hinit
  have hparallel := gp.shiftedField_eventuallyEq_of_same_initial gq'
  filter_upwards [hp, hq, hparallel] with s hp' hq' hparallel'
  calc
    (⟨curve (shift γ (t₀ + 0)) s, p.field (0 + s)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ (t₀ + 0)) s, gp.shiftedField s⟩ := hp'
    _ = ⟨curve (shift γ (t₀ + 0)) s, gq'.shiftedField s⟩ := by
      rw [hparallel']
    _ = ⟨curve (shift γ (t₀ + 0)) s, gq.shiftedField s⟩ := by
      simpa only [gq'] using gq.castInitial_shiftedField_totalState hinit s
    _ = ⟨curve (shift γ (t₀ + 0)) s, q.field (0 + s)⟩ := hq'.symm

/-- Reflect a coherent partial parallel field from the anchored reversed
geodesic to the original geodesic.  Its domain is the negated preimage of the
old domain, and the stronger local-overlap theorem above supplies genuine
parallel germs at every reflected time. -/
noncomputable def reflectReverseAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ : ℝ) {w : TM (curve (reverseAt γ t₀) 0)}
    (p : PartialParallelField (I := I) (M := M) (reverseAt γ t₀) 0 w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    PartialParallelField (I := I) (M := M) γ t₀ (p.reflectedField t₀ 0) where
  domain := Neg.neg ⁻¹' p.domain
  domain_open := p.domain_open.preimage continuous_neg
  domain_preconnected := by
    have hdom : Neg.neg ⁻¹' p.domain = Neg.neg '' p.domain := by
      ext s
      constructor
      · intro hs
        exact ⟨-s, hs, neg_neg s⟩
      · rintro ⟨r, hr, hrs⟩
        change -s ∈ p.domain
        rw [← hrs]
        simpa using hr
    rw [hdom]
    exact p.domain_preconnected.image (fun s : ℝ ↦ -s) continuous_neg.continuousOn
  zero_mem := by
    change -(0 : ℝ) ∈ p.domain
    simpa using p.zero_mem
  field := p.reflectedField t₀
  field_zero := rfl
  field_outside := by
    intro s hs
    change -s ∉ p.domain at hs
    have htotal := p.reflectedField_totalState t₀ s
    rw [p.field_outside (-s) hs] at htotal
    have hbase : curve (shift γ t₀) s =
        curve (shift (reverseAt γ t₀) 0) (-s) := by
      change curve γ (t₀ + s) = curve γ (t₀ - (0 + -s))
      congr 1
      ring
    have hzero :
        (⟨curve (shift γ t₀) s, (0 : TM (curve (shift γ t₀) s))⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift (reverseAt γ t₀) 0) (-s),
          (0 : TM (curve (shift (reverseAt γ t₀) 0) (-s)))⟩ := by
      have hcastzero :
          cast (congrArg (TangentSpace I) hbase)
            (0 : TM (curve (shift γ t₀) s)) =
          (0 : TM (curve (shift (reverseAt γ t₀) 0) (-s))) := by
        exact cast_tangent_zero_of_eq hbase
      calc
        (⟨curve (shift γ t₀) s, (0 : TM (curve (shift γ t₀) s))⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift (reverseAt γ t₀) 0) (-s),
            cast (congrArg (TangentSpace I) hbase)
              (0 : TM (curve (shift γ t₀) s))⟩ :=
            (totalSpace_cast_eq (I := I) (E := E) hbase
              (0 : TM (curve (shift γ t₀) s))).symm
        _ = ⟨curve (shift (reverseAt γ t₀) 0) (-s),
          (0 : TM (curve (shift (reverseAt γ t₀) 0) (-s)))⟩ := by
            rw [hcastzero]
    apply (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
      (curve (shift γ t₀) s) (p.reflectedField t₀ s) 0).mp
    exact htotal.trans hzero.symm
  local_germ := by
    intro s hs
    change -s ∈ p.domain at hs
    exact p.exists_reflectedParallelGerm t₀ hmetric s hs

@[simp] theorem reflectReverseAt_domain
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ : ℝ) {w : TM (curve (reverseAt γ t₀) 0)}
    (p : PartialParallelField (I := I) (M := M) (reverseAt γ t₀) 0 w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    (p.reflectReverseAt t₀ hmetric).domain = Neg.neg ⁻¹' p.domain := rfl

/-- Extension is literal equality of the fibre-valued field on the old
domain.  Since the ambient geodesic and time origin are fixed, both field
values live in exactly the same tangent fibre. -/
def Extends
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p q : PartialParallelField (I := I) (M := M) γ t₀ w₀) : Prop :=
  p.domain ⊆ q.domain ∧ ∀ s ∈ p.domain, p.field s = q.field s

instance {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)} :
    LE (PartialParallelField (I := I) (M := M) γ t₀ w₀) :=
  ⟨Extends⟩

lemma le_def
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p q : PartialParallelField (I := I) (M := M) γ t₀ w₀) :
    p ≤ q ↔ p.domain ⊆ q.domain ∧ ∀ s ∈ p.domain, p.field s = q.field s :=
  Iff.rfl

lemma le_refl
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀) : p ≤ p := by
  exact ⟨Subset.rfl, fun _ _ ↦ rfl⟩

lemma le_trans
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    {p q r : PartialParallelField (I := I) (M := M) γ t₀ w₀}
    (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r := by
  refine ⟨hpq.1.trans hqr.1, ?_⟩
  intro s hs
  exact (hpq.2 s hs).trans (hqr.2 s (hpq.1 hs))

lemma le_antisymm
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    {p q : PartialParallelField (I := I) (M := M) γ t₀ w₀}
    (hpq : p ≤ q) (hqp : q ≤ p) : p = q := by
  have hdomain : p.domain = q.domain := Set.Subset.antisymm hpq.1 hqp.1
  have hfield : p.field = q.field := by
    funext s
    by_cases hs : s ∈ p.domain
    · exact hpq.2 s hs
    · have hs' : s ∉ q.domain := by
        intro hsq
        exact hs (hqp.1 hsq)
      rw [p.field_outside s hs, q.field_outside s hs']
  cases p
  cases q
  cases hdomain
  cases hfield
  rfl

instance {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)} :
    PartialOrder (PartialParallelField (I := I) (M := M) γ t₀ w₀) where
  le_refl := fun p ↦ PartialParallelField.le_refl p
  le_trans := fun _ _ _ hpq hqr ↦ PartialParallelField.le_trans hpq hqr
  le_antisymm := fun _ _ hpq hqp ↦ PartialParallelField.le_antisymm hpq hqp

/-- A local parallel germ supplies a nonempty initial member of the ordered
family of partial fields.  The field is only used on the explicit restart
window; outside it it is set to zero, which is essential for later chain
unions and does not affect any geometric statement. -/
theorem nonempty
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    Nonempty (PartialParallelField (I := I) (M := M) γ t₀ w₀) := by
  obtain ⟨p⟩ := exists_parallelGerm (I := I) (M := M) γ t₀ w₀ hmetric
  obtain ⟨r, hr, hrestart⟩ := p.eventually_totalState_eq_of_restart hmetric
  let U : Set ℝ := Ioo (-r) r
  let W : ∀ s : ℝ, TM (curve (shift γ t₀) s) := fun s ↦
    if hs : s ∈ U then p.shiftedField s else 0
  refine ⟨{
    domain := U
    domain_open := isOpen_Ioo
    domain_preconnected := isPreconnected_Ioo
    zero_mem := by
      change -r < 0 ∧ 0 < r
      constructor <;> linarith
    field := W
    field_zero := ?_
    field_outside := ?_
    local_germ := ?_ }⟩
  · have hzero : (0 : ℝ) ∈ U := by
      change -r < 0 ∧ 0 < r
      constructor <;> linarith
    have htotal := p.shiftedField_initial_totalState
    change (if h : (0 : ℝ) ∈ U then p.shiftedField 0 else 0) = w₀
    rw [dif_pos hzero]
    rw [shift_curve, add_zero] at htotal
    exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
      (curve γ t₀) (p.shiftedField 0) w₀).mp htotal
  · intro s hs
    change (if h : s ∈ U then p.shiftedField s else 0) = 0
    exact dif_neg hs
  · intro s hs
    have hWs : W s = p.shiftedField s := by
      change (if h : s ∈ U then p.shiftedField s else 0) = p.shiftedField s
      exact dif_pos hs
    rw [hWs]
    obtain ⟨q⟩ := exists_parallelGerm (I := I) (M := M) γ (t₀ + s)
      (p.shiftedField s) hmetric
    refine ⟨q, ?_⟩
    have hcohere := hrestart s hs q
    have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), s + u ∈ U := by
      have hopen : U ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
      have hshift : Tendsto (fun u : ℝ ↦ s + u) (𝓝 0) (𝓝 s) := by
        have hconst : ContinuousAt (fun _ : ℝ ↦ s) 0 := continuousAt_const
        have hid : ContinuousAt (fun u : ℝ ↦ u) 0 := continuousAt_id
        change Tendsto ((fun _ : ℝ ↦ s) + fun u : ℝ ↦ u) (𝓝 0) (𝓝 s)
        convert (hconst.add hid).tendsto using 1 <;> simp
      exact hshift.eventually hopen
    filter_upwards [hcohere, hnear] with u hu hsu
    have hWsu : W (s + u) = p.shiftedField (s + u) := by
      change (if h : s + u ∈ U then p.shiftedField (s + u) else 0) =
        p.shiftedField (s + u)
      exact dif_pos hsu
    rw [hWsu]
    exact hu

/-- Every nonempty chain of partial parallel fields has a coherent upper
bound.  The field is selected from a chain member at each in-domain time;
total ordering makes the choice independent on overlaps, while the explicit
zero value outside the union restores literal equality of fields. -/
theorem chain_upper_bound
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (c : Set (PartialParallelField (I := I) (M := M) γ t₀ w₀))
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty) :
    ∃ q : PartialParallelField (I := I) (M := M) γ t₀ w₀,
      (∀ p ∈ c, p ≤ q) ∧
        ∀ s ∈ q.domain, ∃ p ∈ c, s ∈ p.domain := by
  classical
  let ι := {p : PartialParallelField (I := I) (M := M) γ t₀ w₀ // p ∈ c}
  let U : Set ℝ := ⋃ p : ι, p.1.domain
  have hUopen : IsOpen U := by
    exact isOpen_iUnion fun p ↦ p.1.domain_open
  have hUpreconnected : IsPreconnected U := by
    apply isPreconnected_iUnion
    · refine ⟨0, ?_⟩
      simp only [Set.mem_iInter]
      intro p
      exact p.1.zero_mem
    · intro p
      exact p.1.domain_preconnected
  have hchoose : ∀ s : ℝ, s ∈ U → ∃ p : ι, s ∈ p.1.domain := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hp⟩
    exact ⟨p, hp⟩
  let pick : ∀ s : ℝ, s ∈ U → ι := fun s hs ↦ Classical.choose (hchoose s hs)
  have hpick : ∀ s (hs : s ∈ U), s ∈ (pick s hs).1.domain := by
    intro s hs
    exact Classical.choose_spec (hchoose s hs)
  have hfield_eq : ∀ {p q : ι} {s : ℝ},
      s ∈ p.1.domain → s ∈ q.1.domain → p.1.field s = q.1.field s := by
    intro p q s hsp hsq
    rcases hc.total p.2 q.2 with hpq | hqp
    · exact hpq.2 s hsp
    · exact (hqp.2 s hsq).symm
  let qfield : ∀ s : ℝ, TM (curve (shift γ t₀) s) := fun s ↦
    if hs : s ∈ U then (pick s hs).1.field s else 0
  have hqfield_of_mem : ∀ (p : ι) {s : ℝ}, s ∈ p.1.domain →
      qfield s = p.1.field s := by
    intro p s hs
    have hsU : s ∈ U := Set.mem_iUnion.mpr ⟨p, hs⟩
    rw [show qfield s = (pick s hsU).1.field s by simp only [qfield, dif_pos hsU]]
    exact hfield_eq (hpick s hsU) hs
  refine ⟨{
    domain := U
    domain_open := hUopen
    domain_preconnected := hUpreconnected
    zero_mem := by
      obtain ⟨p, hp⟩ := hcne
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, p.zero_mem⟩
    field := qfield
    field_zero := by
      obtain ⟨p, hp⟩ := hcne
      rw [hqfield_of_mem ⟨p, hp⟩ p.zero_mem]
      exact p.field_zero
    field_outside := by
      intro s hs
      simp only [qfield, dif_neg hs]
    local_germ := ?_ }, ?_, ?_⟩
  · intro s hs
    let p : ι := pick s hs
    have hps : s ∈ p.1.domain := hpick s hs
    have hqps : qfield s = p.1.field s := hqfield_of_mem p hps
    rw [hqps]
    obtain ⟨α, hα⟩ := p.1.local_germ s hps
    refine ⟨α, ?_⟩
    have hshift : Tendsto (fun u : ℝ ↦ s + u) (𝓝 0) (𝓝 s) := by
      have hconst : ContinuousAt (fun _ : ℝ ↦ s) 0 := continuousAt_const
      have hid : ContinuousAt (fun u : ℝ ↦ u) 0 := continuousAt_id
      change Tendsto ((fun _ : ℝ ↦ s) + fun u : ℝ ↦ u) (𝓝 0) (𝓝 s)
      convert (hconst.add hid).tendsto using 1 <;> simp
    have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), s + u ∈ p.1.domain :=
      hshift.eventually (p.1.domain_open.mem_nhds hps)
    filter_upwards [hnear, hα] with u hu hαu
    rw [hqfield_of_mem p hu]
    exact hαu
  · intro p hp
    refine ⟨?_, ?_⟩
    · intro s hs
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hs⟩
    · intro s hs
      exact (hqfield_of_mem ⟨p, hp⟩ hs).symm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hp⟩
    exact ⟨p.1, p.2, hp⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem cast_tangent_inner_of_eq {x y : M}
    (hxy : x = y) (u v : TM y) :
    inner ℝ (cast (congrArg (TangentSpace I) hxy.symm) u)
        (cast (congrArg (TangentSpace I) hxy.symm) v) = inner ℝ u v := by
  subst y
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem cast_tangent_norm_of_eq {x y : M}
    (hxy : x = y) (u : TM y) :
    ‖cast (congrArg (TangentSpace I) hxy.symm) u‖ = ‖u‖ := by
  subst y
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private theorem parallel_rhs_eq_of_totalState_eq
    {x y : M} {vx : TM x} {vy : TM y} {u : TM x} {z : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (hfield : (⟨x, u⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, z⟩)
    (W : (q : M) → TM q) :
    inner ℝ 0 (W x) + inner ℝ u (cov W x vx) =
      inner ℝ 0 (W y) + inner ℝ z (cov W y vy) := by
  cases hstate
  have huz : u = z := by
    simpa only [Bundle.TotalSpace.mk_inj] using hfield
  cases huz
  rfl

/-- A partial parallel field satisfies the intrinsic zero-covariant-derivative
equation at every point of its domain.  Its local-germ certificate is first
translated back from the freshly restarted global geodesic to the original
time origin; all comparisons are made in the tangent bundle total space so
the required fibre transports are explicit. -/
theorem isCovariantAccelerationAt_zero_of_local_germ
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    {t : ℝ} (ht : t ∈ p.domain) :
    CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀)) p.field t
      (velocity (shift γ t₀) t) 0 := by
  obtain ⟨q, hq⟩ := p.local_germ t ht
  unfold CurveConnection.IsCovariantAccelerationAt
  intro W hW
  have hscalar :
      (fun s ↦ inner ℝ (p.field (t + s))
        (W (curve (shift γ t₀) (t + s)))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ inner ℝ (q.shiftedField s)
          (W (curve (shift γ (t₀ + t)) s))) := by
    filter_upwards [hq] with s hs
    have htotal :
        (⟨curve (shift γ t₀) (t + s), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + t)) s, q.shiftedField s⟩ := by
      change
        (⟨curve γ (t₀ + (t + s)), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve γ ((t₀ + t) + s), q.shiftedField s⟩
      rw [show t₀ + (t + s) = (t₀ + t) + s by ring]
      exact hs
    exact congrArg (fun z : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
      inner ℝ z.snd (W z.proj)) htotal
  have hcurve0 : curve (shift γ (t₀ + t)) 0 =
      curve (shift γ t₀) t := by
    change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
    rw [add_zero]
  have hWq : MDiffAt (T% W) (curve (shift γ (t₀ + t)) 0) := by
    rw [hcurve0]
    exact hW
  have hstate0 : (shift γ (t₀ + t)).state 0 =
      (shift γ t₀).state t := by
    change γ.state ((t₀ + t) + 0) = γ.state (t₀ + t)
    rw [add_zero]
  have hfield0 :
      (⟨curve (shift γ (t₀ + t)) 0, q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) t, p.field t⟩ := by
    have htotal := hq.self_of_nhds
    change
      (⟨curve γ ((t₀ + t) + 0), q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₀ + t), p.field t⟩
    have hbaseq : curve (shift γ (t₀ + t)) 0 = curve γ (t₀ + t) := by
      change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
      rw [add_zero]
    rw [hbaseq] at htotal
    rw [add_zero] at htotal
    rw [add_zero]
    simpa using htotal.symm
  calc
    CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (p.field s) (W (curve (shift γ t₀) s))) t =
      CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (q.shiftedField s)
          (W (curve (shift γ (t₀ + t)) s))) 0 :=
      CurveConnection.curveScalarDeriv_eq_of_eventuallyEq_const_add hscalar
    _ = inner ℝ 0 (W (curve (shift γ (t₀ + t)) 0)) +
          inner ℝ (q.shiftedField 0)
            (cov W (curve (shift γ (t₀ + t)) 0)
              (velocity (shift γ (t₀ + t)) 0)) :=
      q.isCovariantAccelerationAt_shiftedField_zero W hWq
    _ = inner ℝ 0 (W (curve (shift γ t₀) t)) +
          inner ℝ (p.field t)
            (cov W (curve (shift γ t₀) t) (velocity (shift γ t₀) t)) := by
      exact parallel_rhs_eq_of_totalState_eq (I := I) (M := M) (cov := cov)
        hstate0 hfield0 W

/-- Reading a partial parallel field in any overlapping fixed endpoint chart
is differentiable at an in-domain time.  The proof uses the local germ to
identify the readout with the recharting of its genuine local linear transport
solution; it does not infer differentiability from a merely fibrewise value
identity. -/
theorem endpointCoordinates_differentiableAt_of_local_germ
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    {t : ℝ} (ht : t ∈ p.domain) {c : M}
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hchart : curve (shift γ t₀) t ∈ (extChartAt I c).source) :
    DifferentiableAt ℝ (fun s ↦
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.field s)) t := by
  let Q : ℝ → E := fun s ↦
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (curve (shift γ t₀) s) (p.field s)
  change DifferentiableAt ℝ Q t
  obtain ⟨q, hq⟩ := p.local_germ t ht
  have hqstate0 : (shift γ (t₀ + t)).state 0 =
      IntrinsicGeodesic.localState q.localGeodesic 0 := by
    simpa [shift_state] using q.agrees.self_of_nhds
  have hqcurve0 : curve (shift γ (t₀ + t)) 0 =
      IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0 := by
    simpa [curve, IntrinsicGeodesic.localState] using
      congrArg Bundle.TotalSpace.proj hqstate0
  have hshiftcurve0 : curve (shift γ (t₀ + t)) 0 =
      curve (shift γ t₀) t := by
    change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
    rw [add_zero]
  have hlocalChart : IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0 ∈
      (extChartAt I c).source := by
    rw [← hqcurve0, hshiftcurve0]
    exact hchart
  have hsol0 : (0 : ℝ) ∈ Ioo (-q.localGeodesic.solution.radius)
      q.localGeodesic.solution.radius := by
    constructor <;> linarith [q.localGeodesic.solution.radius_pos]
  have hcoeff0 : (0 : ℝ) ∈ Ioo (-q.coordinateSolution.radius)
      q.coordinateSolution.radius := by
    constructor <;> linarith [q.coordinateSolution.radius_pos]
  have hcoeffdiff : DifferentiableAt ℝ q.coordinateSolution.curve 0 :=
    (q.coordinateSolution.hasDeriv 0 (by simpa using hcoeff0)).differentiableAt
  have hlocalCont : ContinuousAt
      (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic) 0 :=
    (IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve q.localGeodesic hsol0).continuousAt
  have hlocalTarget : ∀ᶠ s in 𝓝 (0 : ℝ),
      IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s ∈
        (extChartAt I c).source :=
    hlocalCont.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) c).mem_nhds hlocalChart)
  have hlocalInterval : ∀ᶠ s in 𝓝 (0 : ℝ),
      s ∈ Ioo (-q.localGeodesic.solution.radius)
        q.localGeodesic.solution.radius :=
    Ioo_mem_nhds hsol0.1 hsol0.2
  have hsourceAgreement : ∀ᶠ s in 𝓝 (0 : ℝ),
      IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M)
          (curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E)) := by
    simpa [IntrinsicGeodesic.LocalGeodesic.curve] using
      IntrinsicAcceleration.local_solution_eventually_mem_smoothFrameAgreementSet
        (I := I) (M := M) (E := E) (H := H) (curve γ (t₀ + t))
        (IntrinsicGeodesic.canonicalBasis (E := E)) q.localGeodesic.solution
  have hread : (fun s ↦ Q (t + s)) =ᶠ[𝓝 (0 : ℝ)]
      CurveConnection.rechartTangent (I := I) (M := M)
        q.localGeodesic.solution q.coordinateSolution.curve c := by
    filter_upwards [hq, q.agrees, hlocalTarget, hlocalInterval, hsourceAgreement]
      with s hp hs htarget hsinterval hsource
    have hptoq :
        (⟨curve (shift γ t₀) (t + s), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + t)) s, q.shiftedField s⟩ := by
      change
        (⟨curve γ (t₀ + (t + s)), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve γ ((t₀ + t) + s), q.shiftedField s⟩
      rw [show t₀ + (t + s) = (t₀ + t) + s by ring]
      exact hp
    have hqtotal := q.shiftedField_totalState_eq_of_state_eq s hs
    have htotal := hptoq.trans hqtotal
    have hreadout := congrArg
      (fun z : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          z.proj z.snd) htotal
    have hcanonical :
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) q.localGeodesic q.coordinateSolution s =
        LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E))
          (q.coordinateSolution.curve s)
          (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s) := by
      change IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (q.coordinateSolution.curve s)
        (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s) = _
      exact CurveConnection.frameField_eq_coordinateFrameCombination_of_mem_agreement
        (I := I) (M := M) (curve γ (t₀ + t))
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (q.coordinateSolution.curve s) hsource
    calc
      Q (t + s) =
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s)
            (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
              (I := I) (M := M) q.localGeodesic q.coordinateSolution s) := hreadout
      _ = (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s)
            (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
              (x₀ := curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E))
              (q.coordinateSolution.curve s)
              (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s)) := by
        rw [hcanonical]
      _ = CurveConnection.rechartTangent (I := I) (M := M)
          q.localGeodesic.solution q.coordinateSolution.curve c s := by
        exact (CurveConnection.rechartTangent_eq_trivialization_readout_of_coordinateFrameCombination
          (I := I) (M := M) q.localGeodesic.solution
          (IntrinsicGeodesic.canonicalBasis (E := E)) btarget
          q.coordinateSolution.curve c hsinterval htarget).symm
  have hrdiff : DifferentiableAt ℝ
      (CurveConnection.rechartTangent (I := I) (M := M)
        q.localGeodesic.solution q.coordinateSolution.curve c) 0 :=
    CurveConnection.rechartTangent_differentiableAt (I := I) (M := M)
      q.localGeodesic.solution q.coordinateSolution.curve c hsol0 hlocalChart hcoeffdiff
  have hshiftDiff : DifferentiableAt ℝ (fun s ↦ Q (t + s)) 0 :=
    hrdiff.congr_of_eventuallyEq hread
  let g : ℝ → ℝ := fun s ↦ s - t
  have hg : DifferentiableAt ℝ g t := by
    change DifferentiableAt ℝ (fun s : ℝ ↦ s - t) t
    exact differentiableAt_id.sub (differentiableAt_const (c := t))
  have hgt : g t = 0 := by
    dsimp [g]
    ring
  have hshiftDiff' : DifferentiableAt ℝ (fun s ↦ Q (t + s)) (g t) := by
    rw [hgt]
    exact hshiftDiff
  have hcomp := hshiftDiff'.comp t hg
  have hcompfun : ((fun s : ℝ ↦ Q (t + s)) ∘ g) =
      (fun s ↦ Q (t + g s)) := rfl
  have hcomp' : DifferentiableAt ℝ (fun s ↦ Q (t + g s)) t := by
    rw [← hcompfun]
    exact hcomp
  have hfun : (fun s : ℝ ↦ Q (t + g s)) = Q := by
    funext s
    congr 1
    dsimp [g]
    ring
  rw [hfun] at hcomp'
  exact hcomp'

/-- The fixed-chart readout of a partial parallel field obeys the genuine
linear coordinate transport equation at every in-domain point where that
chart's smooth frame agrees with its local frame.  This combines the local
germ's intrinsic zero equation with the separately proved readout
differentiability; no endpoint ODE is postulated. -/
theorem endpointCoordinates_hasDerivAt_of_local_germ
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {t : ℝ} (ht : t ∈ p.domain) {c : M}
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hmem : curve (shift γ t₀) t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 (curve (shift γ t₀) t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i z =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame btarget i z) :
    HasDerivAt (fun s ↦
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.field s))
      (-(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov c btarget (extChartAt I c (curve (shift γ t₀) t))
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ t₀) t) (velocity (shift γ t₀) t))
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ t₀) t) (p.field t)))) t := by
  let U : ℝ → E := fun s ↦
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (curve (shift γ t₀) s) (velocity (shift γ t₀) s)
  let Q : ℝ → E := fun s ↦
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (curve (shift γ t₀) s) (p.field s)
  change HasDerivAt Q
    (-(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov c btarget (extChartAt I c (curve (shift γ t₀) t))
      (U t) (Q t))) t
  have hQdiff : DifferentiableAt ℝ Q t := by
    simpa [Q] using p.endpointCoordinates_differentiableAt_of_local_germ
      ht btarget hmem.1
  have hQ : HasDerivAt Q (deriv Q t) t := hQdiff.hasDerivAt
  have hcurveDeriv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (curve (shift γ t₀)) t
      (CurveConnection.timeTangentMap (I := I) t (velocity (shift γ t₀) t)) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    exact GlobalGeodesic.hasMFDerivAt_curve (I := I) (M := M)
      (shift γ t₀) t
  have hchart : curve (shift γ t₀) t ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact hmem.1
  have hbase : curve (shift γ t₀) t ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
      ← extChartAt_source (I := I) c]
    exact hmem.1
  have hvelocity : velocity (shift γ t₀) t =
      IntrinsicAcceleration.frameField (I := I) (M := M) btarget
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          c btarget i)
        (U t) (curve (shift γ t₀) t) := by
    calc
      velocity (shift γ t₀) t =
          LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := c) btarget (U t) (curve (shift γ t₀) t) := by
        rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
          (I := I) (M := M) c btarget hchart]
        exact ((trivializationAt E (TangentSpace I : M → Type _) c)
          |>.symmL_continuousLinearMapAt hbase (velocity (shift γ t₀) t)).symm
      _ = IntrinsicAcceleration.frameField (I := I) (M := M) btarget
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            c btarget i)
          (U t) (curve (shift γ t₀) t) :=
        (CurveConnection.frameField_eq_coordinateFrameCombination_of_mem_agreement
          (I := I) (M := M) c btarget (U t) hmem).symm
  have hzero : CurveConnection.IsCovariantAccelerationAt cov
      (curve (shift γ t₀)) p.field t (velocity (shift γ t₀) t) 0 :=
    p.isCovariantAccelerationAt_zero_of_local_germ ht
  have hcurveCont : ContinuousAt (curve (shift γ t₀)) t :=
    hcurveDeriv.continuousAt
  have hsource : ∀ᶠ s in 𝓝 t,
      curve (shift γ t₀) s ∈ (extChartAt I c).source :=
    hcurveCont.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) c).mem_nhds hmem.1)
  have hframeAt : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ s in 𝓝 t,
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i
          (curve (shift γ t₀) s) =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame btarget i
            (curve (shift γ t₀) s) := by
    intro i
    exact hcurveCont.tendsto.eventually (hframe i)
  have hframes : ∀ᶠ s in 𝓝 t,
      ∀ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i
          (curve (shift γ t₀) s) =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame btarget i
            (curve (shift γ t₀) s) :=
    (Finset.eventually_all Finset.univ).2 fun i _ ↦ hframeAt i
  have hfieldEq :
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) btarget
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          c btarget i)
        Q s (curve (shift γ t₀) s)) =ᶠ[𝓝 t] p.field := by
    filter_upwards [hsource, hframes] with s hs hframes
    have hmemAt : curve (shift γ t₀) s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget :=
      ⟨hs, fun i ↦ hframes i (Finset.mem_univ _)⟩
    have hchartAt : curve (shift γ t₀) s ∈ (chartAt H c).source := by
      rw [← extChartAt_source (I := I) c]
      exact hs
    have hbaseAt : curve (shift γ t₀) s ∈
        (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
        ← extChartAt_source (I := I) c]
      exact hs
    change IntrinsicAcceleration.frameField (I := I) (M := M) btarget
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
        c btarget i)
      (Q s) (curve (shift γ t₀) s) = p.field s
    rw [CurveConnection.frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) c btarget (Q s) hmemAt]
    rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) c btarget hchartAt]
    change (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ
      (curve (shift γ t₀) s)
      ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.field s)) = p.field s
    exact (trivializationAt E (TangentSpace I : M → Type _) c)
      |>.symmL_continuousLinearMapAt hbaseAt (p.field s)
  have hzeroFrame := hzero.congr_of_eventuallyEq hfieldEq.symm
  have hderiv := hasDerivAt_coordinateParallel_of_intrinsic_zero
    (I := I) (M := M) cov c btarget U Q (curve (shift γ t₀))
    hcurveDeriv hQ hmetric hmem hframe hvelocity hzeroFrame
  rw [show deriv Q t =
    -(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov c btarget (extChartAt I c (curve (shift γ t₀) t))
      (U t) (Q t)) by
    exact hderiv.deriv] at hQ
  exact hQ

/-- The coefficient operator read in the fixed tangent-bundle chart at a
global-geodesic time agrees, as a germ, with the coefficient operator of any
certified local geodesic restart there.  Both the base coordinate and the
velocity coordinate are recovered from equality of complete tangent-bundle
states, so this is a genuine chart-change statement rather than an
identification of dependent tangent fibres. -/
theorem endpointCoordinateParallelOperator_eventuallyEq_local
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} (t : ℝ)
    (α : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov
      (curve γ t) (velocity γ t))
    (hα : (fun s ↦ γ.state (t + s)) =ᶠ[𝓝 (0 : ℝ)]
      IntrinsicGeodesic.localState α) :
    (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E))
      (extChartAt I (curve γ t) (curve γ (t + s)))
      ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
        (curve γ (t + s)) (velocity γ (t + s)))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E))
        (α.solution.coordinate s) (α.solution.velocity s)) := by
  have hinter : ∀ᶠ s in 𝓝 (0 : ℝ),
      s ∈ Ioo (-α.solution.radius) α.solution.radius := by
    have hzero : (0 : ℝ) ∈ Ioo (-α.solution.radius) α.solution.radius := by
      constructor <;> linarith [α.solution.radius_pos]
    exact isOpen_Ioo.mem_nhds hzero
  filter_upwards [hα, hinter] with s hs hst
  have hcoordinate :
      extChartAt I (curve γ t) (IntrinsicGeodesic.LocalGeodesic.curve α s) =
        α.solution.coordinate s := by
    change extChartAt I (curve γ t)
      (BonnetMyersEntry.LocalChartSecondOrderSolution.curve α.solution s) = _
    rw [BonnetMyersEntry.LocalChartSecondOrderSolution.curve_eq_chart α.solution hst]
  have hvelocity :
      ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.LocalGeodesic.curve α s)
          (IntrinsicGeodesic.LocalGeodesic.velocity α s)) =
        α.solution.velocity s := by
    change ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
        (BonnetMyersEntry.LocalChartSecondOrderSolution.curve α.solution s)
        (LocalGeodesicData.tangentField cov (γ.state t).proj
          (IntrinsicGeodesic.canonicalBasis (E := E)) α.solution
          α.solution.velocity s)) = _
    exact LocalGeodesicData.continuousLinearMapAt_tangentField_eq
      (I := I) (M := M) (E := E) (H := H) cov (γ.state t).proj
      (IntrinsicGeodesic.canonicalBasis (E := E)) α.solution
      α.solution.velocity hst
  let read : Bundle.TotalSpace E (TangentSpace I : M → Type _) → E × E := fun z ↦
    (extChartAt I (curve γ t) z.proj,
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
        z.proj z.snd)
  have hread : read (γ.state (t + s)) = read (IntrinsicGeodesic.localState α s) :=
    congrArg read hs
  have hreadα : read (IntrinsicGeodesic.localState α s) =
      (α.solution.coordinate s, α.solution.velocity s) := by
    change (extChartAt I (curve γ t) (IntrinsicGeodesic.LocalGeodesic.curve α s),
      (trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
        (IntrinsicGeodesic.LocalGeodesic.curve α s)
          (IntrinsicGeodesic.LocalGeodesic.velocity α s)) = _
    exact Prod.ext hcoordinate hvelocity
  let op : E × E → E →L[ℝ] E := fun q ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E)) q.1 q.2
  have hop : op (read (γ.state (t + s))) =
      op (α.solution.coordinate s, α.solution.velocity s) :=
    congrArg op (hread.trans hreadα)
  change op (read (γ.state (t + s))) =
    op (α.solution.coordinate s, α.solution.velocity s)
  exact hop

/-- The coefficient operator in the fixed endpoint chart of a global
geodesic is `C¹` at every time.  The proof uses the global geodesic's actual
local state germ and reads its tangent velocity through the same
trivialization; it does not assume differentiability of an arbitrary
fibre-valued field. -/
theorem endpointCoordinateParallelOperator_contDiffAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    ContDiffAt ℝ 1
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E))
        (extChartAt I (curve γ t) (curve γ s))
        ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
          (curve γ s) (velocity γ s))) t := by
  obtain ⟨α, hα⟩ := γ.local_germ t
  let A : ℝ → E →L[ℝ] E := fun s ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E))
      (extChartAt I (curve γ t) (curve γ s))
      ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
        (curve γ s) (velocity γ s))
  let Aα : ℝ → E →L[ℝ] E := fun s ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E))
      (α.solution.coordinate s) (α.solution.velocity s)
  have hF := LocalGeodesicData.coordinateAcceleration_system_contDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := curve γ t)
    (b := IntrinsicGeodesic.canonicalBasis (E := E))
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      (curve γ t) (velocity γ t))
  have hlocal : ContDiffAt ℝ 1 Aα 0 := by
    exact LocalGeodesicData.coordinateParallelOperator_contDiffAt_along_localChartSolution
      (I := I) (M := M) (E := E) cov (curve γ t)
      (IntrinsicGeodesic.canonicalBasis (E := E)) α.solution hF
  have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    have hraw := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℝ ↦ s - t) t).tendsto
    have hfun : (id - fun _ : ℝ ↦ t) = (fun s ↦ s - t) := by
      rfl
    rw [hfun] at hraw
    simpa only [sub_self] using hraw
  have hstate : ∀ᶠ s in 𝓝 t,
      γ.state s = localState α (s - t) := by
    have hnear := hshift.eventually hα
    filter_upwards [hnear] with s hs
    rw [show t + (s - t) = s by ring] at hs
    exact hs
  have hinter : ∀ᶠ s in 𝓝 t,
      s - t ∈ Ioo (-α.solution.radius) α.solution.radius := by
    have hzero : (0 : ℝ) ∈ Ioo (-α.solution.radius) α.solution.radius := by
      constructor <;> linarith [α.solution.radius_pos]
    exact hshift.eventually ((isOpen_Ioo.mem_nhds hzero))
  have hAeq : A =ᶠ[𝓝 t] fun s ↦ Aα (s - t) := by
    filter_upwards [hstate, hinter] with s hs hst
    have hcoordinate :
        extChartAt I (curve γ t) (IntrinsicGeodesic.LocalGeodesic.curve α (s - t)) =
          α.solution.coordinate (s - t) := by
      change extChartAt I (γ.state t).proj
        (BonnetMyersEntry.LocalChartSecondOrderSolution.curve α.solution (s - t)) = _
      rw [BonnetMyersEntry.LocalChartSecondOrderSolution.curve_eq_chart α.solution hst]
    have hvelocity :
        ((trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.LocalGeodesic.curve α (s - t))
          (IntrinsicGeodesic.LocalGeodesic.velocity α (s - t))) =
          α.solution.velocity (s - t) := by
      change ((trivializationAt E (TangentSpace I : M → Type _) (γ.state t).proj).continuousLinearMapAt ℝ
          (BonnetMyersEntry.LocalChartSecondOrderSolution.curve α.solution (s - t))
          (LocalGeodesicData.tangentField cov (γ.state t).proj
            (IntrinsicGeodesic.canonicalBasis (E := E)) α.solution
            α.solution.velocity (s - t))) = _
      exact LocalGeodesicData.continuousLinearMapAt_tangentField_eq
        (I := I) (M := M) (E := E) (H := H) cov (γ.state t).proj
        (IntrinsicGeodesic.canonicalBasis (E := E)) α.solution
        α.solution.velocity hst
    let read : Bundle.TotalSpace E (TangentSpace I : M → Type _) → E × E := fun z ↦
      (extChartAt I (curve γ t) z.proj,
        (trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
          z.proj z.snd)
    have hread : read (γ.state s) = read (localState α (s - t)) :=
      congrArg read hs
    have hreadα : read (localState α (s - t)) =
        (α.solution.coordinate (s - t), α.solution.velocity (s - t)) := by
      change (extChartAt I (curve γ t)
          (IntrinsicGeodesic.LocalGeodesic.curve α (s - t)),
        (trivializationAt E (TangentSpace I : M → Type _) (curve γ t)).continuousLinearMapAt ℝ
          (IntrinsicGeodesic.LocalGeodesic.curve α (s - t))
          (IntrinsicGeodesic.LocalGeodesic.velocity α (s - t))) = _
      exact Prod.ext hcoordinate hvelocity
    have hread' : read (γ.state s) =
        (α.solution.coordinate (s - t), α.solution.velocity (s - t)) :=
      hread.trans hreadα
    let op : E × E → E →L[ℝ] E := fun q ↦
      LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve γ t) (IntrinsicGeodesic.canonicalBasis (E := E)) q.1 q.2
    have hop : op (read (γ.state s)) =
        op (α.solution.coordinate (s - t), α.solution.velocity (s - t)) :=
      congrArg op hread'
    change op (read (γ.state s)) =
      op (α.solution.coordinate (s - t), α.solution.velocity (s - t))
    exact hop
  let σ : ℝ → ℝ := fun s ↦ s - t
  have hσ : ContDiffAt ℝ 1 σ t := by
    dsimp [σ]
    exact contDiffAt_id.sub contDiffAt_const
  have hσt : σ t = 0 := by simp [σ]
  have hlocal' : ContDiffAt ℝ 1 Aα (σ t) := by
    rw [hσt]
    exact hlocal
  have hcomp : ContDiffAt ℝ 1 (Aα ∘ σ) t :=
    ContDiffAt.comp t hlocal' hσ
  have hcomp' : ContDiffAt ℝ 1 (fun s ↦ Aα (s - t)) t := by
    simpa [Function.comp_def, σ] using hcomp
  change ContDiffAt ℝ 1 A t
  exact hcomp'.congr_of_eventuallyEq hAeq

/-- At a finite upper endpoint, the actual fixed-chart coordinates of a
partial parallel field satisfy the linear transport equation on a whole
left-hand tail.  The smooth-frame agreement is first chosen on one open
neighbourhood of the endpoint, so the pointwise coordinate theorem receives
the required germ equality at every tail point. -/
theorem eventually_endpointCoordinates_hasDerivAt_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {b : ℝ} (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    ∀ᶠ t in 𝓝[<] b,
      HasDerivAt (fun s ↦
        (trivializationAt E (TangentSpace I : M → Type _)
          (curve (shift γ t₀) b)).continuousLinearMapAt ℝ
          (curve (shift γ t₀) s) (p.field s))
        (-(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
          (E := E) cov (curve (shift γ t₀) b)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (extChartAt I (curve (shift γ t₀) b) (curve (shift γ t₀) t))
          ((trivializationAt E (TangentSpace I : M → Type _)
            (curve (shift γ t₀) b)).continuousLinearMapAt ℝ
            (curve (shift γ t₀) t) (velocity (shift γ t₀) t))
          ((trivializationAt E (TangentSpace I : M → Type _)
            (curve (shift γ t₀) b)).continuousLinearMapAt ℝ
            (curve (shift γ t₀) t) (p.field t)))) t := by
  let G := shift γ t₀
  let c := curve G b
  let btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hcurve : Tendsto (curve G) (𝓝[<] b) (𝓝 c) := by
    have hcont := GlobalGeodesic.contMDiffAt_curve (I := I) (M := M) G b
    simpa [c] using hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzeroB : (0 : ℝ) < b := hupper 0 p.zero_mem
  have hdom : ∀ᶠ t in 𝓝[<] b, t ∈ p.domain := by
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) hzeroB] with t ht
    obtain ⟨u, hu, htu⟩ := hcofinal t ht.2
    exact p.domain_preconnected.Icc_subset p.zero_mem hu ⟨ht.1.le, htu.le⟩
  have hsource : ∀ᶠ t in 𝓝[<] b,
      curve G t ∈ (extChartAt I c).source :=
    hcurve (extChartAt_source_mem_nhds (I := I) c)
  have hframesC : ∀ᶠ z in 𝓝 c,
      ∀ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i z =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame btarget i z :=
    (Finset.eventually_all Finset.univ).2 fun i _ ↦
      LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
        (I := I) (M := M) (E := E) c btarget i
  obtain ⟨U, hUsub, hUopen, hcU⟩ := mem_nhds_iff.mp hframesC
  have hUtail : ∀ᶠ t in 𝓝[<] b, curve G t ∈ U :=
    hcurve (hUopen.mem_nhds hcU)
  filter_upwards [hdom, hsource, hUtail] with t ht hsourceT hUT
  have hmem : curve G t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget :=
    ⟨hsourceT, fun i ↦ hUsub hUT i (Finset.mem_univ _)⟩
  have hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 (curve G t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i z =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame btarget i z := by
    intro i
    filter_upwards [hUopen.mem_nhds hUT] with z hz
    exact hUsub hz i (Finset.mem_univ _)
  simpa [G, c, btarget] using
    p.endpointCoordinates_hasDerivAt_of_local_germ hmetric ht btarget hmem hframe

/-- The squared Riemannian norm of a partial parallel field is constant on
its entire preconnected domain.  The local-germ clause supplies a genuine
parallel transport around each time; the conclusion is then propagated
through the open preconnected domain rather than assumed globally. -/
theorem inner_self_eq_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {s : ℝ} (hs : s ∈ p.domain) :
    inner ℝ (p.field s) (p.field s) =
      inner ℝ (p.field 0) (p.field 0) := by
  let f : p.domain → ℝ := fun x ↦ inner ℝ (p.field x.1) (p.field x.1)
  have hlocal : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨g, hg⟩ := p.local_germ x.1 x.2
    obtain ⟨r, hr, hnorm⟩ :=
      g.exists_interval_shiftedField_inner_self_eq hmetric
    have hshift : Tendsto (fun y : p.domain ↦ y.1 - x.1) (𝓝 x) (𝓝 0) := by
      have hcont : ContinuousAt (fun y : p.domain ↦ y.1 - x.1) x :=
        continuousAt_subtype_val.sub continuousAt_const
      simpa using hcont.tendsto
    have hball : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [hshift.eventually hg, hshift.eventually hball]
      with y htotal hy
    have hfield : p.field (x.1 + (y.1 - x.1)) =
        g.shiftedField (y.1 - x.1) := by
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x.1)) (y.1 - x.1))
        (p.field (x.1 + (y.1 - x.1)))
        (g.shiftedField (y.1 - x.1))).mp htotal
    change inner ℝ (p.field y.1) (p.field y.1) =
      inner ℝ (p.field x.1) (p.field x.1)
    rw [show y.1 = x.1 + (y.1 - x.1) by ring, hfield]
    have hcurve : curve (shift γ t₀) (x.1 + (y.1 - x.1)) =
        curve (shift γ (t₀ + x.1)) (y.1 - x.1) := by
      change curve γ (t₀ + (x.1 + (y.1 - x.1))) =
        curve γ ((t₀ + x.1) + (y.1 - x.1))
      congr 1
      ring
    exact (cast_tangent_inner_of_eq (I := I) (M := M) hcurve
      (g.shiftedField (y.1 - x.1))
      (g.shiftedField (y.1 - x.1))).trans (hnorm _ hy)
  let _ : PreconnectedSpace p.domain :=
    Subtype.preconnectedSpace p.domain_preconnected
  have hconst := hlocal.apply_eq_of_preconnectedSpace
    (⟨s, hs⟩ : p.domain) (⟨0, p.zero_mem⟩ : p.domain)
  change inner ℝ (p.field s) (p.field s) =
    inner ℝ (p.field 0) (p.field 0) at hconst
  exact hconst

/-- Two coherent partial parallel fields preserve their mutual inner product
along any common forward interval.  At each time the proof restarts a finite
two-vector parallel germ, uses its actual-fibre Gram identity, and then
propagates the resulting local constancy through the interval.  Thus this is
not a formal polarization shortcut: it compares independently constructed
parallel fields across their chart changes. -/
theorem inner_eq_initial_of_Icc_subset
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₁ w₂ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₁)
    (q : PartialParallelField (I := I) (M := M) γ t₀ w₂)
    (hmetric : cov.IsMetricCompatibleTangent)
    {L : ℝ} (hL : 0 ≤ L)
    (hp : Icc (0 : ℝ) L ⊆ p.domain)
    (hq : Icc (0 : ℝ) L ⊆ q.domain) :
    inner ℝ (p.field L) (q.field L) =
      inner ℝ (p.field 0) (q.field 0) := by
  classical
  let f : Icc (0 : ℝ) L → ℝ := fun x ↦
    inner ℝ (p.field x.1) (q.field x.1)
  have hlocal : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hpx : x.1 ∈ p.domain := hp x.2
    have hqx : x.1 ∈ q.domain := hq x.2
    obtain ⟨gp, hgp⟩ := p.local_germ x.1 hpx
    obtain ⟨gq, hgq⟩ := q.local_germ x.1 hqx
    let w : Fin 2 → TM (curve γ (t₀ + x.1)) := fun i ↦
      if i = (0 : Fin 2) then p.field x.1 else q.field x.1
    obtain ⟨g⟩ := exists_parallelFamilyGerm (I := I) (M := M)
      γ (t₀ + x.1) w hmetric
    have hw₀ : w (0 : Fin 2) = p.field x.1 := by
      change p.field x.1 = p.field x.1
      rfl
    have hw₁ : w (1 : Fin 2) = q.field x.1 := by
      change q.field x.1 = q.field x.1
      rfl
    let g₀ : ParallelGerm (I := I) (M := M) γ (t₀ + x.1) (p.field x.1) :=
      (g.toParallelGerm (0 : Fin 2)).castInitial hw₀
    let g₁ : ParallelGerm (I := I) (M := M) γ (t₀ + x.1) (q.field x.1) :=
      (g.toParallelGerm (1 : Fin 2)).castInitial hw₁
    have hpg₀ := gp.shiftedField_eventuallyEq_of_same_initial g₀
    have hqg₁ := gq.shiftedField_eventuallyEq_of_same_initial g₁
    obtain ⟨r, hr, hgram⟩ := g.exists_interval_shiftedField_inner_eq
    have hg₀ : ∀ u : ℝ,
        g₀.shiftedField u = (g.toParallelGerm (0 : Fin 2)).shiftedField u := by
      intro u
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x.1)) u) (g₀.shiftedField u)
        ((g.toParallelGerm (0 : Fin 2)).shiftedField u)).mp (by
          simpa only [g₀] using
            (g.toParallelGerm (0 : Fin 2)).castInitial_shiftedField_totalState hw₀ u)
    have hg₁ : ∀ u : ℝ,
        g₁.shiftedField u = (g.toParallelGerm (1 : Fin 2)).shiftedField u := by
      intro u
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x.1)) u) (g₁.shiftedField u)
        ((g.toParallelGerm (1 : Fin 2)).shiftedField u)).mp (by
          simpa only [g₁] using
            (g.toParallelGerm (1 : Fin 2)).castInitial_shiftedField_totalState hw₁ u)
    have hshift : Tendsto (fun y : Icc (0 : ℝ) L ↦ y.1 - x.1) (𝓝 x) (𝓝 0) := by
      have hcont : ContinuousAt (fun y : Icc (0 : ℝ) L ↦ y.1 - x.1) x :=
        continuousAt_subtype_val.sub continuousAt_const
      simpa using hcont.tendsto
    have hball : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [hshift.eventually hgp, hshift.eventually hgq,
      hshift.eventually hpg₀, hshift.eventually hqg₁,
      hshift.eventually hball] with y hpfield hqfield hpg hqg hy
    have hpfield' : p.field (x.1 + (y.1 - x.1)) =
        g₀.shiftedField (y.1 - x.1) := by
      rw [hpg] at hpfield
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x.1)) (y.1 - x.1))
        (p.field (x.1 + (y.1 - x.1)))
        (g₀.shiftedField (y.1 - x.1))).mp hpfield
    have hqfield' : q.field (x.1 + (y.1 - x.1)) =
        g₁.shiftedField (y.1 - x.1) := by
      rw [hqg] at hqfield
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x.1)) (y.1 - x.1))
        (q.field (x.1 + (y.1 - x.1)))
        (g₁.shiftedField (y.1 - x.1))).mp hqfield
    have hinner := hgram (0 : Fin 2) (1 : Fin 2) (y.1 - x.1) hy
    change inner ℝ ((g.toParallelGerm (0 : Fin 2)).shiftedField (y.1 - x.1))
        ((g.toParallelGerm (1 : Fin 2)).shiftedField (y.1 - x.1)) = _ at hinner
    rw [← hg₀ (y.1 - x.1), ← hg₁ (y.1 - x.1)] at hinner
    change inner ℝ (p.field y.1) (q.field y.1) =
      inner ℝ (p.field x.1) (q.field x.1)
    rw [show y.1 = x.1 + (y.1 - x.1) by ring, hpfield', hqfield']
    have hcurve : curve (shift γ t₀) (x.1 + (y.1 - x.1)) =
        curve (shift γ (t₀ + x.1)) (y.1 - x.1) := by
      change curve γ (t₀ + (x.1 + (y.1 - x.1))) =
        curve γ ((t₀ + x.1) + (y.1 - x.1))
      congr 1
      ring
    exact (cast_tangent_inner_of_eq (I := I) (M := M) hcurve
      (g₀.shiftedField (y.1 - x.1))
      (g₁.shiftedField (y.1 - x.1))).trans (by
        rw [hw₀, hw₁] at hinner
        exact hinner)
  let _ : PreconnectedSpace (Icc (0 : ℝ) L) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hL⟩
  have hlast : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hconst := hlocal.apply_eq_of_preconnectedSpace
    (⟨L, hlast⟩ : Icc (0 : ℝ) L) (⟨0, hzero⟩ : Icc (0 : ℝ) L)
  change inner ℝ (p.field L) (q.field L) =
    inner ℝ (p.field 0) (q.field 0) at hconst
  exact hconst

/-- The zero-time Gram value of two partial parallel fields is the Gram value
of their prescribed initial tangent vectors.  The time-zero fibres are joined
through the explicit shifted-curve equality, so this is not relying on an
implicit dependent-type coercion. -/
theorem inner_zero_eq_initialVectors
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₁ w₂ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₁)
    (q : PartialParallelField (I := I) (M := M) γ t₀ w₂) :
    inner ℝ (p.field 0) (q.field 0) = inner ℝ w₁ w₂ := by
  have hcurve : curve (shift γ t₀) 0 = curve γ t₀ := by simp
  have hp : p.field 0 =
      cast (congrArg (TangentSpace I) hcurve.symm) w₁ := by
    exact p.field_zero
  have hq : q.field 0 =
      cast (congrArg (TangentSpace I) hcurve.symm) w₂ := by
    exact q.field_zero
  rw [hp, hq]
  exact cast_tangent_inner_of_eq (I := I) (M := M) hcurve w₁ w₂

/-- Norm preservation for a partial parallel field.  This is the scalar
boundedness statement consumed by the endpoint continuation estimate. -/
theorem norm_eq_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {s : ℝ} (hs : s ∈ p.domain) :
    ‖p.field s‖ = ‖p.field 0‖ := by
  have hinner := p.inner_self_eq_initial hmetric hs
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (p.field s), norm_nonneg (p.field 0)]

/-- The uniform bound is stated against the prescribed initial tangent as
well as the field's zero-time representative, which makes it directly usable
when a new local endpoint chart is selected. -/
theorem norm_eq_initialVector
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {s : ℝ} (hs : s ∈ p.domain) :
    ‖p.field s‖ = ‖w₀‖ := by
  have hcurve : curve (shift γ t₀) 0 = curve γ t₀ := by simp
  have hfield : p.field 0 =
      cast (congrArg (TangentSpace I) hcurve.symm) w₀ := by
    exact p.field_zero
  calc
    ‖p.field s‖ = ‖p.field 0‖ := p.norm_eq_initial hmetric hs
    _ = ‖cast (congrArg (TangentSpace I) hcurve.symm) w₀‖ :=
      congrArg norm hfield
    _ = ‖w₀‖ := cast_tangent_norm_of_eq (I := I) (M := M) hcurve w₀

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Cofinality at a finite upper endpoint fills the whole final interval of
an open preconnected partial-field domain. -/
lemma Ioo_zero_subset_domain_of_upper_cofinal
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ b : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    Ioo (0 : ℝ) b ⊆ p.domain := by
  intro t ht
  obtain ⟨u, hu, htu⟩ := hcofinal t ht.2
  exact p.domain_preconnected.Icc_subset p.zero_mem hu ⟨ht.1.le, htu.le⟩

/-- Norm preservation makes every final left tail of a partial parallel
field uniformly bounded by its prescribed initial vector. -/
theorem eventually_norm_le_initialVector_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ b : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    ∀ᶠ t in 𝓝[<] b, ‖p.field t‖ ≤ ‖w₀‖ := by
  have hzeroB : (0 : ℝ) < b := hupper 0 p.zero_mem
  filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) hzeroB] with t ht
  exact le_of_eq (p.norm_eq_initialVector hmetric
    (p.Ioo_zero_subset_domain_of_upper_cofinal hcofinal ht))

/-- On a final tail converging to an endpoint `c`, a partial parallel field
has an exact representation in the fixed tangent-bundle frame based at `c`.
This is a fibrewise identity, not an assumed coordinate proxy: the field is
read through the endpoint trivialization and reconstructed through its local
frame. -/
theorem eventually_field_eq_endpoint_coordinateFrameCombination_of_tendsto
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ b : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    {c : M}
    (hcurve : Tendsto (curve (shift γ t₀)) (𝓝[<] b) (𝓝 c))
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E) :
    ∀ᶠ t in 𝓝[<] b,
      p.field t = LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) btarget
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ t₀) t) (p.field t))
        (curve (shift γ t₀) t) := by
  have hsource : ∀ᶠ t in 𝓝[<] b,
      curve (shift γ t₀) t ∈ (extChartAt I c).source :=
    hcurve (extChartAt_source_mem_nhds (I := I) c)
  filter_upwards [hsource] with t ht
  have htchart : curve (shift γ t₀) t ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact ht
  have htbase : curve (shift γ t₀) t ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
      ← extChartAt_source (I := I) c]
    exact ht
  rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
    (I := I) (M := M) (x₀ := c) btarget htchart]
  exact ((trivializationAt E (TangentSpace I : M → Type _) c).symmL_continuousLinearMapAt
    htbase (p.field t)).symm

/-- The norm-preserving partial transport has bounded coordinates in every
fixed endpoint chart.  Together with the as-yet-unproved coordinate ODE
tail, this is precisely the boundedness input required by the analytic
linear-transport restart theorem. -/
theorem exists_eventually_norm_endpoint_coordinates_le_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ b : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t)
    {c : M}
    (hcurve : Tendsto (curve (shift γ t₀)) (𝓝[<] b) (𝓝 c))
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E) :
    ∃ B > (0 : ℝ), ∀ᶠ t in 𝓝[<] b,
      ‖(trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ t₀) t) (p.field t)‖ ≤ B := by
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
    rcases (inferInstance : IsContMDiffRiemannianBundle I 1 E
      (TangentSpace I : M → Type _)).exists_contMDiff with ⟨g, hg, hinner⟩
    exact ⟨g, hg.continuous, hinner⟩
  have hframe := p.eventually_field_eq_endpoint_coordinateFrameCombination_of_tendsto
    hcurve btarget
  have hfield := p.eventually_norm_le_initialVector_of_upper_cofinal
    hmetric hupper hcofinal
  exact exists_eventually_norm_coordinateVelocity_le_of_tendsto_of_frame_velocity_bound
    (I := I) (M := M) (E := E) (x₀ := c) btarget hcurve hframe hfield

/-- A partial parallel field that is cofinal below a finite upper endpoint
has a genuine linear-transport restart in the endpoint chart.  Its coordinate
ODE tail is proved from the local germs above, and both required bounds are
derived respectively from local coefficient regularity and metric norm
preservation. -/
theorem exists_localLinearTransportSolution_eventuallyEq_left_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {b : ℝ} (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    ∃ x : E, ∃ sol : LocalLinearTransportSolution
      (fun s ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov (curve (shift γ t₀) b)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (extChartAt I (curve (shift γ t₀) b) (curve (shift γ t₀) (b + s)))
        ((trivializationAt E (TangentSpace I : M → Type _)
          (curve (shift γ t₀) b)).continuousLinearMapAt ℝ
          (curve (shift γ t₀) (b + s)) (velocity (shift γ t₀) (b + s))))
      0 x,
      (fun t ↦ (trivializationAt E (TangentSpace I : M → Type _)
        (curve (shift γ t₀) b)).continuousLinearMapAt ℝ
        (curve (shift γ t₀) t) (p.field t)) =ᶠ[𝓝[<] b]
        (fun t ↦ sol.curve (t - b)) := by
  let G := shift γ t₀
  let c := curve G b
  let btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let A : ℝ → E →L[ℝ] E := fun t ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov c btarget (extChartAt I c (curve G t))
      ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve G t) (velocity G t))
  let Q : ℝ → E := fun t ↦
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (curve G t) (p.field t)
  have hcurve : Tendsto (curve G) (𝓝[<] b) (𝓝 c) := by
    have hcont := GlobalGeodesic.contMDiffAt_curve (I := I) (M := M) G b
    simpa [c] using hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hAcont : ContDiffAt ℝ 1 A b := by
    simpa [A, G, c, btarget] using
      endpointCoordinateParallelOperator_contDiffAt (I := I) (M := M) G b
  have hderiv : ∀ᶠ t in 𝓝[<] b, HasDerivAt Q (-(A t) (Q t)) t := by
    simpa [A, Q, G, c, btarget] using
      p.eventually_endpointCoordinates_hasDerivAt_of_upper_cofinal
        hmetric hupper hcofinal
  obtain ⟨Cq, hCq, hQbound⟩ :=
    p.exists_eventually_norm_endpoint_coordinates_le_of_upper_cofinal
      hmetric hupper hcofinal hcurve btarget
  have hQ : ∀ᶠ t in 𝓝[<] b, ‖Q t‖ ≤ Cq := by
    simpa [Q, G, c] using hQbound
  let CA : ℝ := ‖A b‖ + 1
  have hCA : 0 ≤ CA := by
    dsimp [CA]
    positivity
  have hAnear : ∀ᶠ t in 𝓝 b, A t ∈ Metric.ball (A b) (1 : ℝ) :=
    hAcont.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
  have hA : ∀ᶠ t in 𝓝[<] b, ‖A t‖ ≤ CA := by
    filter_upwards [hAnear.filter_mono nhdsWithin_le_nhds] with t ht
    rw [Metric.mem_ball] at ht
    calc
      ‖A t‖ = ‖(A t - A b) + A b‖ := by
        congr 1
        abel
      _ ≤ ‖A t - A b‖ + ‖A b‖ := norm_add_le _ _
      _ = dist (A t) (A b) + ‖A b‖ := by rw [dist_eq_norm_sub]
      _ ≤ 1 + ‖A b‖ := by gcongr
      _ = CA := by dsimp [CA]; ring
  obtain ⟨x, sol, hsol⟩ :=
    exists_localLinearTransportSolution_eventuallyEq_left_of_norm_bounds
      hAcont hCA hCq.le hderiv hA hQ
  refine ⟨x, sol, ?_⟩
  simpa [A, Q, G, c, btarget] using hsol

/-- The analytic endpoint restart of a partial parallel field is compatible
with a genuine intrinsic parallel germ at that endpoint.  The conclusion is
an equality in the tangent-bundle total space on a left tail: it therefore
contains both the coordinate ODE uniqueness calculation and the required
dependent-fibre identification. -/
theorem exists_endpointParallelGerm_eventually_totalState_eq_left_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {b : ℝ} (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    ∃ x : E, ∃ q : ParallelGerm (I := I) (M := M) γ (t₀ + b)
      ((trivializationAt E (TangentSpace I : M → Type _) (curve γ (t₀ + b))).symmL ℝ
        (curve γ (t₀ + b)) x),
      ∀ᶠ t in 𝓝[<] b,
        (⟨curve (shift γ t₀) t, p.field t⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + b)) (t - b), q.shiftedField (t - b)⟩ := by
  obtain ⟨x, sol, hsol⟩ :=
    p.exists_localLinearTransportSolution_eventuallyEq_left_of_upper_cofinal
      hmetric hupper hcofinal
  obtain ⟨q⟩ := exists_parallelGerm (I := I) (M := M) γ (t₀ + b)
    ((trivializationAt E (TangentSpace I : M → Type _) (curve γ (t₀ + b))).symmL ℝ
      (curve γ (t₀ + b)) x) hmetric
  refine ⟨x, q, ?_⟩
  let G := shift γ t₀
  let c := curve G b
  let A₁ : ℝ → E →L[ℝ] E := fun s ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov c (IntrinsicGeodesic.canonicalBasis (E := E))
      (extChartAt I c (curve G (b + s)))
      ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve G (b + s)) (velocity G (b + s)))
  let A₂ : ℝ → E →L[ℝ] E := fun s ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov c (IntrinsicGeodesic.canonicalBasis (E := E))
      (q.localGeodesic.solution.coordinate s) (q.localGeodesic.solution.velocity s)
  change LocalLinearTransportSolution A₁ 0 x at sol
  have hcoord : LocalGeodesicData.coordinateVelocity (I := I) (M := M)
      (E := E) (curve γ (t₀ + b))
      ((trivializationAt E (TangentSpace I : M → Type _) (curve γ (t₀ + b))).symmL ℝ
        (curve γ (t₀ + b)) x) = x := by
    rw [LocalGeodesicData.coordinateVelocity]
    exact (trivializationAt E (TangentSpace I : M → Type _) (curve γ (t₀ + b))).continuousLinearMapAt_symmL
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _)
          (curve γ (t₀ + b))) x
  have hqagrees : (fun s ↦ G.state (b + s)) =ᶠ[𝓝 (0 : ℝ)]
      IntrinsicGeodesic.localState q.localGeodesic := by
    filter_upwards [q.agrees] with s hs
    change γ.state (t₀ + (b + s)) =
      IntrinsicGeodesic.localState q.localGeodesic s
    rw [show t₀ + (b + s) = (t₀ + b) + s by ring]
    exact hs
  have hAeq : A₁ =ᶠ[𝓝 (0 : ℝ)] A₂ := by
    simpa [A₁, A₂, G, c] using
      endpointCoordinateParallelOperator_eventuallyEq_local
        (I := I) (M := M) (cov := cov) (γ := G) b q.localGeodesic hqagrees
  have hAglobal := endpointCoordinateParallelOperator_contDiffAt
    (I := I) (M := M) (cov := cov) G b
  have htranslate : ContDiffAt ℝ 1 (fun s : ℝ ↦ b + s) 0 := by
    exact contDiffAt_const.add contDiffAt_id
  have hA₁ : ContDiffAt ℝ 1 A₁ 0 := by
    have hAglobal' : ContDiffAt ℝ 1
        (fun r : ℝ ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
          (E := E) cov c (IntrinsicGeodesic.canonicalBasis (E := E))
          (extChartAt I c (curve G r))
          ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (curve G r) (velocity G r))) (b + 0) := by
      simpa [c] using hAglobal
    simpa [A₁, Function.comp_def] using hAglobal'.comp 0 htranslate
  have htransport : sol.curve =ᶠ[𝓝 (0 : ℝ)] q.coordinateSolution.curve := by
    simpa [A₁, A₂, G, c] using
      LocalLinearTransportSolution.eventuallyEq_of_initial_eq_of_eventuallyEq
        sol q.coordinateSolution hcoord.symm hA₁ hAeq
  have hsub : Tendsto (fun t : ℝ ↦ t - b) (𝓝[<] b) (𝓝 (0 : ℝ)) := by
    have hraw : Tendsto (fun t : ℝ ↦ t - b) (𝓝 b) (𝓝 (b - b)) :=
      (continuousAt_id.sub continuousAt_const :
        ContinuousAt (fun t : ℝ ↦ t - b) b).tendsto
    simpa only [sub_self] using
      hraw.mono_left (nhdsWithin_le_nhds : 𝓝[<] b ≤ 𝓝 b)
  have htransportLeft : (fun t : ℝ ↦ sol.curve (t - b)) =ᶠ[𝓝[<] b]
      (fun t ↦ q.coordinateSolution.curve (t - b)) :=
    hsub.eventually htransport
  have hqreadLeft : ∀ᶠ t in 𝓝[<] b,
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ (t₀ + b)) (t - b)) (q.shiftedField (t - b)) =
        q.coordinateSolution.curve (t - b) := by
    simpa [G, c] using hsub.eventually
      q.eventually_coordinateReadout_eq_coordinateSolution
  have hGcont := GlobalGeodesic.contMDiffAt_curve (I := I) (M := M) G b
  have hGlimit : Tendsto (curve G) (𝓝[<] b) (𝓝 c) := by
    exact hGcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsource : ∀ᶠ t in 𝓝[<] b,
      curve G t ∈ (extChartAt I c).source :=
    hGlimit (extChartAt_source_mem_nhds (I := I) c)
  filter_upwards [hsol, htransportLeft, hqreadLeft, hsource] with t hp htransport hqread htSource
  have hcurve : curve G t = curve (shift γ (t₀ + b)) (t - b) := by
    change curve γ (t₀ + t) = curve γ ((t₀ + b) + (t - b))
    congr 1
    ring
  have hbasep : curve G t ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
      ← extChartAt_source (I := I) c]
    exact htSource
  have hbaseq : curve (shift γ (t₀ + b)) (t - b) ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
    rw [← hcurve]
    exact hbasep
  have hread :
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve G t) (p.field t) =
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ (t₀ + b)) (t - b)) (q.shiftedField (t - b)) := by
    calc
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve G t) (p.field t) = sol.curve (t - b) := hp
      _ = q.coordinateSolution.curve (t - b) := htransport
      _ = (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ (t₀ + b)) (t - b)) (q.shiftedField (t - b)) := hqread.symm
  let e := trivializationAt E (TangentSpace I : M → Type _) c
  have hsourcep :
      (⟨curve G t, p.field t⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) ∈
        e.source := e.mem_source.mpr hbasep
  have hsourceq :
      (⟨curve (shift γ (t₀ + b)) (t - b), q.shiftedField (t - b)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) ∈ e.source :=
    e.mem_source.mpr hbaseq
  apply e.toPartialEquiv.injOn hsourcep hsourceq
  apply Prod.ext
  · change (e ⟨curve G t, p.field t⟩).1 =
      (e ⟨curve (shift γ (t₀ + b)) (t - b), q.shiftedField (t - b)⟩).1
    rw [e.coe_fst hsourcep, e.coe_fst hsourceq]
    exact hcurve
  · change (e ⟨curve G t, p.field t⟩).2 =
      (e ⟨curve (shift γ (t₀ + b)) (t - b), q.shiftedField (t - b)⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbasep (p.field t),
      ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbaseq
        (q.shiftedField (t - b))]
    simpa [e] using hread

/-- A partial parallel field that is cofinal below a finite upper endpoint
extends strictly across that endpoint.  The fresh interval is represented by
an intrinsic endpoint germ, while the old field is retained literally on its
domain; total-space overlap equality is what makes those two descriptions
cohere. -/
theorem exists_strict_extension_of_upper_cofinal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {b : ℝ} (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    ∃ q : PartialParallelField (I := I) (M := M) γ t₀ w₀,
      p ≤ q ∧ p.domain ⊂ q.domain := by
  classical
  obtain ⟨x, g, htail⟩ :=
    p.exists_endpointParallelGerm_eventually_totalState_eq_left_of_upper_cofinal
      hmetric hupper hcofinal
  obtain ⟨ρ, hρ, hrestart⟩ :=
    g.exists_relativeField_localGerm hmetric t₀
  obtain ⟨a, ha, htailSub⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp htail
  change a < b at ha
  let r : ℝ := min ((b - a) / 2) (ρ / 2)
  have hr : 0 < r := by
    dsimp [r]
    apply lt_min
    · linarith
    · linarith
  have hra : r ≤ (b - a) / 2 := min_le_left _ _
  have hrρ : r ≤ ρ / 2 := min_le_right _ _
  have htailLower : a < b - r := by
    linarith [hra]
  let J : Set ℝ := Ioo (b - r) (b + r)
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  have hJb : b ∈ J := by
    change b - r < b ∧ b < b + r
    constructor <;> linarith
  have hnotPb : b ∉ p.domain := by
    intro hb
    linarith [hupper b hb]
  have hqpre : IsPreconnected (p.domain ∪ J) := by
    obtain ⟨t, ht, htb⟩ := hcofinal (b - r / 2) (by linarith)
    have htJ : t ∈ J := by
      change b - r < t ∧ t < b + r
      constructor
      · linarith
      · linarith [hupper t ht, hr]
    exact p.domain_preconnected.union t ht htJ hJpre
  let W : ∀ s : ℝ, TM (curve (shift γ t₀) s) := fun s ↦
    if hs : s ∈ p.domain then p.field s else
      if hJ : s ∈ J then g.fieldAlong t₀ s else 0
  have hW_p : ∀ {t : ℝ}, t ∈ p.domain → W t = p.field t := by
    intro t ht
    simp only [W, dif_pos ht]
  have hW_g : ∀ {t : ℝ}, t ∈ J → W t = g.fieldAlong t₀ t := by
    intro t htJ
    by_cases ht : t ∈ p.domain
    · have htupper : t < b := hupper t ht
      have hta : a < t := lt_trans htailLower (by
        change b - r < t ∧ t < b + r at htJ
        exact htJ.1)
      have htailt := htailSub ⟨hta, htupper⟩
      have htime : (t₀ + t) - (t₀ + b) = t - b := by ring
      have hgfield :
          (⟨curve (shift γ t₀) t, g.fieldAlong t₀ t⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ (t₀ + b)) (t - b), g.shiftedField (t - b)⟩ := by
        calc
          (⟨curve (shift γ t₀) t, g.fieldAlong t₀ t⟩ :
              Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
            ⟨curve (shift γ (t₀ + b)) ((t₀ + t) - (t₀ + b)),
              g.shiftedField ((t₀ + t) - (t₀ + b))⟩ :=
              g.fieldAlong_totalState_eq_shiftedField t₀ t
          _ = ⟨curve (shift γ (t₀ + b)) (t - b),
              g.shiftedField (t - b)⟩ := by
                exact congrArg (fun u ↦
                  (⟨curve (shift γ (t₀ + b)) u, g.shiftedField u⟩ :
                    Bundle.TotalSpace E (TangentSpace I : M → Type _))) htime
      have htotal :
          (⟨curve (shift γ t₀) t, p.field t⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ t₀) t, g.fieldAlong t₀ t⟩ :=
        htailt.trans hgfield.symm
      have hfield : p.field t = g.fieldAlong t₀ t :=
        (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
          (curve (shift γ t₀) t) (p.field t) (g.fieldAlong t₀ t)).mp htotal
      simpa only [W, dif_pos ht] using hfield
    · simp only [W, dif_neg ht, dif_pos htJ]
  let q : PartialParallelField (I := I) (M := M) γ t₀ w₀ := {
    domain := p.domain ∪ J
    domain_open := p.domain_open.union hJopen
    domain_preconnected := hqpre
    zero_mem := Set.mem_union_left J p.zero_mem
    field := W
    field_zero := by
      rw [hW_p p.zero_mem]
      exact p.field_zero
    field_outside := by
      intro t ht
      have htp : t ∉ p.domain := by
        intro hp
        exact ht (Set.mem_union_left J hp)
      have htJ : t ∉ J := by
        intro hJ
        exact ht (Set.mem_union_right p.domain hJ)
      simp only [W, dif_neg htp, dif_neg htJ]
    local_germ := by
      intro t ht
      rcases ht with ht | ht
      · rw [hW_p ht]
        obtain ⟨α, hα⟩ := p.local_germ t ht
        refine ⟨α, ?_⟩
        have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
          have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
          have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
          change Tendsto ((fun _ : ℝ ↦ t) + fun s ↦ s) (𝓝 0) (𝓝 t)
          convert (hconst.add hid).tendsto using 1 <;> simp
        have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ p.domain :=
          hshift.eventually (p.domain_open.mem_nhds ht)
        filter_upwards [hnear, hα] with s hs hstate
        calc
          (⟨curve (shift γ (t₀ + t)) s, W (t + s)⟩ :
              Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
            ⟨curve (shift γ (t₀ + t)) s, p.field (t + s)⟩ := by
              rw [hW_p hs]
          _ = ⟨curve (shift γ (t₀ + t)) s, α.shiftedField s⟩ := hstate
      · have hτ : (t₀ + t) - (t₀ + b) ∈ Ioo (-ρ) ρ := by
          change -ρ < (t₀ + t) - (t₀ + b) ∧
            (t₀ + t) - (t₀ + b) < ρ
          change b - r < t ∧ t < b + r at ht
          constructor <;> linarith [hrρ, hρ]
        obtain ⟨α, hα⟩ := hrestart t hτ
        refine ⟨α.castInitial (hW_g ht).symm, ?_⟩
        have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
          have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
          have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
          change Tendsto ((fun _ : ℝ ↦ t) + fun s ↦ s) (𝓝 0) (𝓝 t)
          convert (hconst.add hid).tendsto using 1 <;> simp
        have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ J :=
          hshift.eventually (hJopen.mem_nhds ht)
        filter_upwards [hnear, hα] with s hs hstate
        calc
          (⟨curve (shift γ (t₀ + t)) s, W (t + s)⟩ :
              Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
            ⟨curve (shift γ (t₀ + t)) s, g.fieldAlong t₀ (t + s)⟩ := by
              rw [hW_g hs]
          _ = ⟨curve (shift γ (t₀ + t)) s, α.shiftedField s⟩ := hstate
          _ = ⟨curve (shift γ (t₀ + t)) s,
              (α.castInitial (hW_g ht).symm).shiftedField s⟩ := by
                exact (α.castInitial_shiftedField_totalState
                  (hW_g ht).symm s).symm }
  have hpq : p ≤ q := by
    refine ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_union_left J ht
    · intro t ht
      exact (hW_p ht).symm
  have hproper : p.domain ⊂ q.domain := by
    change p.domain ⊂ p.domain ∪ J
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_union_left J ht
    intro hEq
    apply hnotPb
    rw [hEq]
    exact Set.mem_union_right p.domain hJb
  exact ⟨q, hpq, hproper⟩

/-- An open preconnected partial-field domain which is bounded above has a
finite strict upper endpoint and is cofinal below it.  This is the order
theory needed to feed the analytic endpoint extension theorem to Zorn. -/
private theorem upper_endpoint_of_bddAbove
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : PartialParallelField (I := I) (M := M) γ t₀ w₀)
    (hBdd : BddAbove p.domain) :
    ∃ b : ℝ, (∀ t ∈ p.domain, t < b) ∧
      ∀ a < b, ∃ t ∈ p.domain, a < t := by
  have hnonempty : p.domain.Nonempty := ⟨0, p.zero_mem⟩
  refine ⟨sSup p.domain, ?_, ?_⟩
  · intro t ht
    have hle : t ≤ sSup p.domain := le_csSup hBdd ht
    apply lt_of_le_of_ne hle
    intro hEq
    obtain ⟨ε, hε, hsub⟩ :=
      Metric.mem_nhds_iff.mp (p.domain_open.mem_nhds ht)
    have hnext : t + ε / 2 ∈ p.domain := by
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq]
      have hcalc : t + ε / 2 - t = ε / 2 := by ring
      rw [hcalc, abs_of_pos (by linarith)]
      linarith
    have hnextUpper : t + ε / 2 ≤ sSup p.domain := le_csSup hBdd hnext
    rw [← hEq] at hnextUpper
    linarith
  · intro a ha
    exact exists_lt_of_lt_csSup hnonempty ha

/-- Zorn's lemma yields a maximal coherent partial parallel field.  This is
an actual field-level maximal object, not merely a selection of unrelated
local transports; the remaining endpoint theorem must prove it cannot stop
at a finite time. -/
theorem exists_maximal
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialParallelField (I := I) (M := M) γ t₀ w₀, IsMax p := by
  letI : Nonempty (PartialParallelField (I := I) (M := M) γ t₀ w₀) :=
    nonempty (I := I) (M := M) γ t₀ w₀ hmetric
  apply zorn_le_nonempty
  intro c hc hcne
  obtain ⟨q, hq, _⟩ := chain_upper_bound (I := I) (M := M) c hc hcne
  exact ⟨q, hq⟩

/-- There is a genuine coherent parallel field on every nonnegative time of
a complete global geodesic.  This one-sided result is enough for transport
along an arbitrary finite forward segment and follows solely from the
finite-upper-endpoint continuation just proved. -/
theorem exists_partialParallelField_Ici
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialParallelField (I := I) (M := M) γ t₀ w₀,
      Ici (0 : ℝ) ⊆ p.domain := by
  obtain ⟨p, hpmax⟩ := exists_maximal (I := I) (M := M) γ t₀ w₀ hmetric
  have hunbounded : ¬ BddAbove p.domain := by
    intro hBdd
    obtain ⟨b, hupper, hcofinal⟩ := upper_endpoint_of_bddAbove p hBdd
    obtain ⟨q, hpq, hproper⟩ :=
      p.exists_strict_extension_of_upper_cofinal hmetric hupper hcofinal
    have hpqeq : p = q := hpmax.eq_of_le hpq
    exact hproper.ne (congrArg PartialParallelField.domain hpqeq)
  refine ⟨p, ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ : ∃ t ∈ p.domain, s < t := by
    by_contra h
    push Not at h
    apply hunbounded
    exact ⟨s, fun u hu ↦ h u hu⟩
  exact p.domain_preconnected.Icc_subset p.zero_mem ht ⟨hs, hst.le⟩

/-- Time reflection turns forward coherent transport on the anchored reversed
geodesic into a coherent field on every nonpositive time of the original
geodesic.  The initial vector is transported through the certified complete
state equality at time zero and then retyped explicitly. -/
theorem exists_partialParallelField_Iic
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialParallelField (I := I) (M := M) γ t₀ w₀,
      Iic (0 : ℝ) ⊆ p.domain := by
  let hstate :
      γ.state t₀ =
        (⟨curve (reverseAt γ t₀) 0,
          -velocity (reverseAt γ t₀) 0⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) := by
    simpa only [sub_zero] using reverseAt_reflectState γ t₀ 0
  let wrev : TM (curve (reverseAt γ t₀) 0) :=
    reindexInitialVector hstate.symm w₀
  obtain ⟨q, hq⟩ := exists_partialParallelField_Ici
    (I := I) (M := M) (reverseAt γ t₀) 0 wrev hmetric
  let r := q.reflectReverseAt t₀ hmetric
  have hreflect :
      (⟨curve (shift γ t₀) 0, q.reflectedField t₀ 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (reverseAt γ t₀) 0, wrev⟩ := by
    have hraw := q.reflectedField_totalState t₀ 0
    have hzero : -(0 : ℝ) = 0 := by ring
    rw [hzero] at hraw
    exact hraw.trans q.field_zero_totalState
  have hreindex :
      (⟨curve (reverseAt γ t₀) 0, wrev⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ t₀, w₀⟩ := by
    change (⟨curve (reverseAt γ t₀) 0, wrev⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨(γ.state t₀).proj, w₀⟩
    exact reindexInitialVector_totalState hstate.symm w₀
  have hinit := hreflect.trans hreindex
  let p : PartialParallelField (I := I) (M := M) γ t₀ w₀ := {
    domain := r.domain
    domain_open := r.domain_open
    domain_preconnected := r.domain_preconnected
    zero_mem := r.zero_mem
    field := q.reflectedField t₀
    field_zero := by
      let hbase : curve (shift γ t₀) 0 = curve γ t₀ := by
        change curve γ (t₀ + 0) = curve γ t₀
        congr 1
        ring
      change cast (congrArg (TangentSpace I) hbase)
        (q.reflectedField t₀ 0) = w₀
      apply (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve γ t₀)
        (cast (congrArg (TangentSpace I) hbase) (q.reflectedField t₀ 0)) w₀).mp
      calc
        (⟨curve γ t₀, cast (congrArg (TangentSpace I) hbase)
          (q.reflectedField t₀ 0)⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ t₀) 0, q.reflectedField t₀ 0⟩ :=
            totalSpace_cast_eq hbase (q.reflectedField t₀ 0)
        _ = ⟨curve γ t₀, w₀⟩ := hinit
    field_outside := by
      intro s hs
      exact r.field_outside s hs
    local_germ := by
      intro s hs
      change s ∈ r.domain at hs
      rw [reflectReverseAt_domain] at hs
      change -s ∈ q.domain at hs
      exact q.exists_reflectedParallelGerm t₀ hmetric s hs }
  refine ⟨p, ?_⟩
  intro s hs
  change s ∈ r.domain
  rw [reflectReverseAt_domain]
  change -s ∈ q.domain
  apply hq
  change s ≤ 0 at hs
  change 0 ≤ -s
  linarith

/-- The actual velocity of a complete global geodesic is itself a coherent
parallel field on every relative time.  This packages the intrinsic
zero-acceleration theorem and the local transport uniqueness theorem into the
same `PartialParallelField` interface used for independently chosen tangent
vectors.  In particular, the distinguished member of a future parallel frame
can be the literal velocity rather than only a field with the same initial
value. -/
theorem exists_velocityPartialParallelField
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialParallelField (I := I) (M := M) γ t₀ (velocity γ t₀),
      p.domain = Set.univ ∧
      ∀ s, p.field s = velocity (shift γ t₀) s := by
  let p : PartialParallelField (I := I) (M := M) γ t₀ (velocity γ t₀) := {
    domain := Set.univ
    domain_open := isOpen_univ
    domain_preconnected := isPreconnected_univ
    zero_mem := mem_univ _
    field := fun s ↦ velocity (shift γ t₀) s
    field_zero := by
      have htotal :
          (⟨curve (shift γ t₀) 0, velocity (shift γ t₀) 0⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve γ t₀, velocity γ t₀⟩ := by
        change γ.state (t₀ + 0) = γ.state t₀
        rw [add_zero]
      rw [shift_curve, add_zero] at htotal
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve γ t₀) (velocity (shift γ t₀) 0) (velocity γ t₀)).mp htotal
    field_outside := by
      intro s hs
      simp at hs
    local_germ := ?_ }
  · refine ⟨p, rfl, ?_⟩
    intro s
    rfl
  · intro s hs
    obtain ⟨q⟩ := exists_parallelGerm (I := I) (M := M) γ (t₀ + s)
      (velocity (shift γ t₀) s) hmetric
    refine ⟨q, ?_⟩
    have hq := q.shiftedField_eventuallyEq_velocity_of_initial (by rfl)
    filter_upwards [hq] with u hu
    have hstate := shift_shift_state (I := I) (M := M) (γ := γ) t₀ s u
    have hvel : velocity (shift γ t₀) (s + u) =
        velocity (shift γ (t₀ + s)) u := by
      change ((shift γ t₀).state (s + u)).snd =
        ((shift γ (t₀ + s)).state u).snd
      exact congrArg Bundle.TotalSpace.snd hstate
    rw [hvel, ← hu]

/-- Any prescribed family of tangent vectors has coherent forward parallel
continuations along a complete global geodesic.  All fields are defined on
the same nonnegative time ray, satisfy the true intrinsic parallel equation,
and preserve their complete Gram matrix.  The construction deliberately
chooses the fields independently and proves compatibility afterwards, so it
does not hide a global trivialization of the tangent bundle. -/
theorem exists_forward_parallelFields_gram
    {ι : Type*}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} (w : ι → TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (w i),
      (∀ i, Ici (0 : ℝ) ⊆ (p i).domain) ∧
      (∀ i s, 0 ≤ s →
        CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
          (p i).field s (velocity (shift γ t₀) s) 0) ∧
      ∀ i j s, 0 ≤ s →
        inner ℝ ((p i).field s) ((p j).field s) =
          inner ℝ ((p i).field 0) ((p j).field 0) := by
  classical
  have hsingle : ∀ i, ∃ p : PartialParallelField (I := I) (M := M) γ t₀ (w i),
      Ici (0 : ℝ) ⊆ p.domain := by
    intro i
    exact exists_partialParallelField_Ici (I := I) (M := M) γ t₀ (w i) hmetric
  choose p hp using hsingle
  refine ⟨p, hp, ?_, ?_⟩
  · intro i s hs
    exact (p i).isCovariantAccelerationAt_zero_of_local_germ
      (hp i hs)
  · intro i j s hs
    have hpseg : Icc (0 : ℝ) s ⊆ (p i).domain := by
      intro t ht
      exact hp i ht.1
    have hqseg : Icc (0 : ℝ) s ⊆ (p j).domain := by
      intro t ht
      exact hp j ht.1
    have hinner := (p i).inner_eq_initial_of_Icc_subset (p j)
      hmetric hs hpseg hqseg
    exact hinner

/-- A unit-speed global geodesic has a coherent forward orthonormal parallel
frame whose zeroth member is its literal velocity.  The nonzero members stay
transverse for every nonnegative time, and every member satisfies the true
intrinsic covariant-zero equation.  This is the global-on-a-finite-forward-
segment frame datum required before one can instantiate the second-variation
argument; it does not assert that the geodesic is endpoint minimizing. -/
theorem exists_forward_adapted_parallelFrame
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hn : 1 ≤ Module.finrank ℝ (TM (curve γ t₀))) :
    letI : Nonempty (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
      ⟨⟨0, by omega⟩⟩
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
          (TM (curve γ t₀)),
      b ⟨0, by omega⟩ = velocity γ t₀ ∧
      ∃ p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (b i),
        (∀ i, Ici (0 : ℝ) ⊆ (p i).domain) ∧
        (∀ i s, 0 ≤ s →
          CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
            (p i).field s (velocity (shift γ t₀) s) 0) ∧
        (∀ s, 0 ≤ s →
          (p ⟨0, by omega⟩).field s = velocity (shift γ t₀) s) ∧
        (∀ s, 0 ≤ s → Orthonormal ℝ (fun i ↦ (p i).field s)) ∧
        (∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))), ∀ s, 0 ≤ s →
          inner ℝ ((p i).field s) (velocity (shift γ t₀) s) = 0) := by
  classical
  let i0 : Fin (Module.finrank ℝ (TM (curve γ t₀))) := ⟨0, by omega⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_first hunit hn
  have hb0 : b i0 = velocity γ t₀ := by
    simpa [i0] using hb
  have hsingle : ∀ i, ∃ p : PartialParallelField (I := I) (M := M) γ t₀ (b i),
      Ici (0 : ℝ) ⊆ p.domain ∧
      (i = i0 → ∀ s, p.field s = velocity (shift γ t₀) s) := by
    intro i
    by_cases hi : i = i0
    · subst i
      rw [hb0]
      obtain ⟨p, hp, hfield⟩ :=
        PartialParallelField.exists_velocityPartialParallelField
          (I := I) (M := M) γ t₀ hmetric
      refine ⟨p, ?_, ?_⟩
      · intro s hs
        rw [hp]
        exact Set.mem_univ s
      · intro _
        exact hfield
    · obtain ⟨p, hp⟩ :=
        PartialParallelField.exists_partialParallelField_Ici
          (I := I) (M := M) γ t₀ (b i) hmetric
      refine ⟨p, hp, ?_⟩
      intro h
      exact (hi h).elim
  choose p hp hvelocity using hsingle
  have hacc : ∀ i s, 0 ≤ s →
      CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
        (p i).field s (velocity (shift γ t₀) s) 0 := by
    intro i s hs
    exact (p i).isCovariantAccelerationAt_zero_of_local_germ (hp i hs)
  have hgram : ∀ i j s, 0 ≤ s →
      inner ℝ ((p i).field s) ((p j).field s) =
        inner ℝ ((p i).field 0) ((p j).field 0) := by
    intro i j s hs
    have hpi : Icc (0 : ℝ) s ⊆ (p i).domain := by
      intro t ht
      exact hp i ht.1
    have hpj : Icc (0 : ℝ) s ⊆ (p j).domain := by
      intro t ht
      exact hp j ht.1
    exact (p i).inner_eq_initial_of_Icc_subset (p j) hmetric hs hpi hpj
  refine ⟨b, ?_, p, hp, hacc, ?_, ?_, ?_⟩
  · simpa [i0] using hb0
  · intro s hs
    exact hvelocity i0 rfl s
  · intro s hs
    rw [orthonormal_iff_ite]
    intro i j
    have hborth := b.orthonormal
    rw [orthonormal_iff_ite] at hborth
    calc
      inner ℝ ((p i).field s) ((p j).field s) =
          inner ℝ ((p i).field 0) ((p j).field 0) := hgram i j s hs
      _ = inner ℝ (b i) (b j) :=
        (p i).inner_zero_eq_initialVectors (p j)
      _ = if i = j then 1 else 0 := hborth i j
  · intro i hi s hs
    have hborth := b.orthonormal
    rw [orthonormal_iff_ite] at hborth
    have hine : i ≠ i0 := (Finset.mem_erase.mp hi).1
    calc
      inner ℝ ((p i).field s) (velocity (shift γ t₀) s) =
          inner ℝ ((p i).field s) ((p i0).field s) := by
            rw [hvelocity i0 rfl s]
      _ = inner ℝ ((p i).field 0) ((p i0).field 0) := hgram i i0 s hs
      _ = inner ℝ (b i) (b i0) :=
        (p i).inner_zero_eq_initialVectors (p i0)
      _ = 0 := by simpa only [if_neg hine] using hborth i i0

/-- The coherent forward fields of an orthonormal basis give a linear
isometry from the initial tangent fibre to the fibre at any specified forward
time.  This promotes the pointwise Gram statement to an actual transport map
without choosing a chart or silently identifying tangent fibres. -/
noncomputable def forwardTransport
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) :
    TM (curve γ t₀) →ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  let f : TM (curve γ t₀) →ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    b.toBasis.constr ℝ (fun i ↦ (p i).field s)
  apply f.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  · have hf : (f : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ (p i).field s := by
      funext i
      exact b.toBasis.constr_basis ℝ (fun i ↦ (p i).field s) i
    rw [hf]
    exact horth

/-- The forward transport isometry has its intended values on the prescribed
initial frame. -/
theorem forwardTransport_apply_basis
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) (i : ι) :
    forwardTransport p horth (b i) = (p i).field s := by
  change (b.toBasis.constr ℝ (fun i ↦ (p i).field s)) (b i) = (p i).field s
  exact b.toBasis.constr_basis ℝ (fun i ↦ (p i).field s) i

/-- In finite-dimensional tangent fibres, the forward transport isometry is
surjective and hence a linear isometric equivalence.  This supplies a genuine
global-on-a-forward-segment parallel-transport equivalence. -/
noncomputable def forwardTransportEquiv
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) :
    TM (curve γ t₀) ≃ₗᵢ[ℝ] TM (curve (shift γ t₀) s) := by
  let T := forwardTransport p horth
  have hdim : Module.finrank ℝ (TM (curve γ t₀)) =
      Module.finrank ℝ (TM (curve (shift γ t₀) s)) :=
    tangent_finrank_eq (I := I) (M := M) (curve γ t₀)
      (curve (shift γ t₀) s)
  let e : TM (curve γ t₀) ≃ₗ[ℝ] TM (curve (shift γ t₀) s) :=
    T.toLinearMap.linearEquivOfInjective T.injective hdim
  apply e.isometryOfOrthonormal (v := b.toBasis)
  · simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  · have he : (e : TM (curve γ t₀) → TM (curve (shift γ t₀) s)) ∘ b.toBasis =
        fun i ↦ (p i).field s := by
      funext i
      change e (b i) = (p i).field s
      rw [show e (b i) = T.toLinearMap (b i) by
        exact LinearMap.linearEquivOfInjective_apply T.injective hdim (b i)]
      exact forwardTransport_apply_basis p horth i
    rw [he]
    exact horth

/-- The forward transport equivalence maps each initial frame vector to its
coherent parallel continuation. -/
theorem forwardTransportEquiv_apply_basis
    {ι : Type*} [Fintype ι]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ s : ℝ}
    {b : OrthonormalBasis ι ℝ (TM (curve γ t₀))}
    (p : ∀ i, PartialParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : Orthonormal ℝ (fun i ↦ (p i).field s)) (i : ι) :
    forwardTransportEquiv p horth (b i) = (p i).field s := by
  change forwardTransport p horth (b i) = (p i).field s
  exact forwardTransport_apply_basis p horth i

end PartialParallelField

/-- A genuinely global parallel field along the time-shifted complete
geodesic.  The local-germ condition is stated in the tangent-bundle total
space, so it records actual fibre values rather than a coordinate proxy. -/
structure GlobalParallelField
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀)) where
  field : ∀ s : ℝ, TM (curve (shift γ t₀) s)
  field_zero : field 0 = w₀
  local_germ : ∀ s,
    ∃ p : ParallelGerm (I := I) (M := M) γ (t₀ + s) (field s),
      ∀ᶠ u in 𝓝 (0 : ℝ),
        (⟨curve (shift γ (t₀ + s)) u, field (s + u)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + s)) u, p.shiftedField u⟩

/-- A global parallel field regarded as a partial field with domain all of
real time.  This adapter lets fixed-chart regularity theorems proved during
the continuation construction be reused without duplicating their local-germ
arguments. -/
noncomputable def GlobalParallelField.toPartialParallelField
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) :
    PartialParallelField (I := I) (M := M) γ t₀ w₀ where
  domain := Set.univ
  domain_open := isOpen_univ
  domain_preconnected := isPreconnected_univ
  zero_mem := Set.mem_univ 0
  field := p.field
  field_zero := p.field_zero
  field_outside := by simp
  local_germ := fun s _hs ↦ p.local_germ s

/-- In a fixed chart whose frame agrees with the local coordinate frame, the
coordinate readout of a global parallel field satisfies the expected linear
transport ODE. -/
theorem GlobalParallelField.fixedChartCoordinates_hasDerivAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    (t : ℝ) (c : M)
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hmem : curve (shift γ t₀) t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget)
    (hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 (curve (shift γ t₀) t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) c btarget i z =
          (trivializationAt E (TangentSpace I : M → Type _) c).localFrame
            btarget i z) :
    HasDerivAt (fun s ↦
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (curve (shift γ t₀) s) (p.field s))
      (-(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov c btarget (extChartAt I c (curve (shift γ t₀) t))
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ t₀) t) (velocity (shift γ t₀) t))
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (curve (shift γ t₀) t) (p.field t)))) t := by
  have ht : t ∈ p.toPartialParallelField.domain := by
    change t ∈ (Set.univ : Set ℝ)
    exact Set.mem_univ t
  simpa [GlobalParallelField.toPartialParallelField] using
    (p.toPartialParallelField.endpointCoordinates_hasDerivAt_of_local_germ
      hmetric (t := t) ht btarget hmem hframe)

/-- A global parallel field is continuous as a curve in the actual tangent
bundle.  This follows from the continuity of each canonical local transport
germ and its certified total-space overlap, so it does not rely on a hidden
global trivialization of the tangent bundle. -/
theorem GlobalParallelField.continuousAt_totalState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) (t : ℝ) :
    ContinuousAt (fun s ↦
      (⟨curve (shift γ t₀) s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) t := by
  obtain ⟨q, hq⟩ := p.local_germ t
  have hlocal := q.continuousAt_shiftedField_totalState_zero
  have htranslate : ContinuousAt (fun s : ℝ ↦ s - t) t :=
    continuousAt_id.sub continuousAt_const
  have hcomp : ContinuousAt (fun s ↦
      (⟨curve (shift γ (t₀ + t)) (s - t), q.shiftedField (s - t)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) t := by
    change ContinuousAt
      ((fun u ↦
        (⟨curve (shift γ (t₀ + t)) u, q.shiftedField u⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) ∘
        fun s : ℝ ↦ s - t) t
    exact hlocal.comp_of_eq htranslate (by simp)
  have htranslateT : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    change Tendsto (fun s : ℝ ↦ s - t) (𝓝 t)
      (𝓝 ((fun s : ℝ ↦ s - t) t)) at htranslate
    simpa only [sub_self] using htranslate
  have hnear : (fun s ↦
      (⟨curve (shift γ t₀) s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 t]
      (fun s ↦
        (⟨curve (shift γ (t₀ + t)) (s - t), q.shiftedField (s - t)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) := by
    have hraw := htranslateT.eventually hq
    filter_upwards [hraw] with s hs
    rw [show t + (s - t) = s by ring] at hs
    change
      (⟨curve γ (t₀ + s), p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ ((t₀ + t) + (s - t)), q.shiftedField (s - t)⟩
    rw [show t₀ + s = (t₀ + t) + (s - t) by ring]
    exact hs
  exact hcomp.congr_of_eventuallyEq hnear

/-- The total-space curve of a global parallel field is continuous on all
of real time. -/
theorem GlobalParallelField.continuous_totalState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀) :
    Continuous (fun s ↦
      (⟨curve (shift γ t₀) s, p.field s⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) :=
  continuous_iff_continuousAt.2 (fun s ↦ p.continuousAt_totalState s)

/-- Forward and backward maximal continuation splice to a genuine global
parallel field.  The value at zero is taken from the backward field; the
local uniqueness theorem reconciles it with the forward field on the other
side of zero, so this is a tangent-bundle-valued construction rather than a
pointwise choice of unrelated local transports. -/
theorem exists_globalParallelField
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    Nonempty (GlobalParallelField (I := I) (M := M) γ t₀ w₀) := by
  classical
  obtain ⟨pminus, hminus⟩ :=
    PartialParallelField.exists_partialParallelField_Iic
      (I := I) (M := M) γ t₀ w₀ hmetric
  obtain ⟨pplus, hplus⟩ :=
    PartialParallelField.exists_partialParallelField_Ici
      (I := I) (M := M) γ t₀ w₀ hmetric
  let F : ∀ s : ℝ, TM (curve (shift γ t₀) s) := fun s ↦
    if s ≤ 0 then pminus.field s else pplus.field s
  have hFminus : ∀ s : ℝ, s ≤ 0 → F s = pminus.field s := by
    intro s hs
    simpa [F, hs] using (rfl : pminus.field s = pminus.field s)
  have hFplus : ∀ s : ℝ, ¬ s ≤ 0 → F s = pplus.field s := by
    intro s hs
    simpa [F, hs] using (rfl : pplus.field s = pplus.field s)
  refine ⟨{
    field := F
    field_zero := by
      simpa [F] using pminus.field_zero
    local_germ := ?_ }⟩
  intro s
  by_cases hsneg : s < 0
  · have hsle : s ≤ 0 := hsneg.le
    rw [hFminus s hsle]
    obtain ⟨g, hg⟩ := pminus.local_germ s (hminus hsle)
    refine ⟨g, ?_⟩
    have htail : ∀ᶠ u in 𝓝 (0 : ℝ), s + u ≤ 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < -s by linarith)] with u hu
      change u < -s at hu
      linarith
    filter_upwards [hg, htail] with u hgu hu
    rw [hFminus (s + u) hu]
    exact hgu
  · by_cases hspos : 0 < s
    · have hsnot : ¬ s ≤ 0 := not_le_of_gt hspos
      rw [hFplus s hsnot]
      obtain ⟨g, hg⟩ := pplus.local_germ s (hplus hspos.le)
      refine ⟨g, ?_⟩
      have htail : ∀ᶠ u in 𝓝 (0 : ℝ), ¬ s + u ≤ 0 := by
        filter_upwards [Ioi_mem_nhds (show -s < (0 : ℝ) by linarith)] with u hu
        change -s < u at hu
        linarith
      filter_upwards [hg, htail] with u hgu hu
      rw [hFplus (s + u) hu]
      exact hgu
    · have hszero : s = 0 := by linarith
      subst s
      rw [hFminus 0 le_rfl]
      obtain ⟨g, hg⟩ := pminus.local_germ 0 pminus.zero_mem
      refine ⟨g, ?_⟩
      have hagree :=
        PartialParallelField.eventually_local_totalState_eq_of_same_initial
          pminus pplus
      filter_upwards [hg, hagree] with u hgu hagreeu
      have hleft :
          (⟨curve (shift γ (t₀ + 0)) u, F (0 + u)⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve (shift γ (t₀ + 0)) u, pminus.field (0 + u)⟩ := by
        by_cases hu : 0 + u ≤ 0
        · rw [hFminus (0 + u) hu]
        · rw [hFplus (0 + u) hu]
          exact hagreeu.symm
      exact hleft.trans hgu

/- The next two elementary total-space lemmas are deliberately kept beside
the global-field interface.  The corresponding partial-field lemmas above
are private implementation details of the Zorn construction; global
invariants should not depend on that representation. -/
private theorem global_parallel_rhs_eq_of_totalState_eq
    {x y : M} {vx : TM x} {vy : TM y} {u : TM x} {z : TM y}
    (hstate : (⟨x, vx⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, vy⟩)
    (hfield : (⟨x, u⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨y, z⟩)
    (W : (q : M) → TM q) :
    inner ℝ 0 (W x) + inner ℝ u (cov W x vx) =
      inner ℝ 0 (W y) + inner ℝ z (cov W y vy) := by
  cases hstate
  have huz : u = z := by
    simpa only [Bundle.TotalSpace.mk_inj] using hfield
  cases huz
  rfl

private theorem global_cast_tangent_inner_of_eq {x y : M}
    (hxy : x = y) (u v : TM y) :
    inner ℝ (cast (congrArg (TangentSpace I) hxy.symm) u)
        (cast (congrArg (TangentSpace I) hxy.symm) v) = inner ℝ u v := by
  subst y
  rfl

private theorem global_cast_tangent_section_of_eq {x y : M}
    (hxy : x = y) (W : (z : M) → TM z) :
    W x = cast (congrArg (TangentSpace I) hxy.symm) (W y) := by
  subst y
  rfl

/-- Scalar pairings of a global parallel field with a differentiable section
are differentiable at every time.  The proof descends to the genuine local
canonical field supplied by the global germ, proves regularity there, and
then transports it back through the time translation; no differentiability is
inferred merely from fibrewise values. -/
theorem GlobalParallelField.mdiffAt_inner_field_section
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (t : ℝ) (W : (x : M) → TM x)
    (hW : MDiffAt (T% W) (curve (shift γ t₀) t)) :
    MDiffAt (fun s ↦ inner ℝ (p.field s)
      (W (curve (shift γ t₀) s))) t := by
  let F : ℝ → ℝ := fun s ↦ inner ℝ (p.field s)
    (W (curve (shift γ t₀) s))
  change MDiffAt F t
  obtain ⟨q, hq⟩ := p.local_germ t
  have hscalar : (fun s ↦ F (t + s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ inner ℝ (q.shiftedField s)
        (W (curve (shift γ (t₀ + t)) s))) := by
    filter_upwards [hq] with s hs
    change inner ℝ (p.field (t + s))
        (W (curve (shift γ t₀) (t + s))) =
      inner ℝ (q.shiftedField s)
        (W (curve (shift γ (t₀ + t)) s))
    have htotal :
        (⟨curve (shift γ t₀) (t + s), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + t)) s, q.shiftedField s⟩ := by
      change
        (⟨curve γ (t₀ + (t + s)), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve γ ((t₀ + t) + s), q.shiftedField s⟩
      rw [show t₀ + (t + s) = (t₀ + t) + s by ring]
      exact hs
    exact congrArg (fun z : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
      inner ℝ z.snd (W z.proj)) htotal
  have hcurve0 : curve (shift γ (t₀ + t)) 0 =
      curve (shift γ t₀) t := by
    change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
    rw [add_zero]
  have hbase0 : curve (shift γ (t₀ + t)) 0 =
      IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0 := by
    have hstate := q.agrees.self_of_nhds
    simpa [curve, IntrinsicGeodesic.localState, shift_state] using
      congrArg Bundle.TotalSpace.proj hstate
  have hWq : MDiffAt (T% W)
      (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0) := by
    rw [← hbase0, hcurve0]
    exact hW
  have hqzero : (0 : ℝ) ∈ Ioo
      (0 - q.coordinateSolution.radius) (0 + q.coordinateSolution.radius) := by
    constructor <;> linarith [q.coordinateSolution.radius_pos]
  have hqderiv : HasDerivAt q.coordinateSolution.curve
      (deriv q.coordinateSolution.curve 0) 0 := by
    rw [(q.coordinateSolution.hasDeriv 0 hqzero).deriv]
    exact q.coordinateSolution.hasDeriv 0 hqzero
  have hlocalzero : (0 : ℝ) ∈ Ioo
      (-q.localGeodesic.solution.radius) q.localGeodesic.solution.radius := by
    constructor <;> linarith [q.localGeodesic.solution.radius_pos]
  have hqcurve : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic) 0
      (CurveConnection.timeTangentMap (I := I) 0
        (IntrinsicGeodesic.LocalGeodesic.velocity q.localGeodesic 0)) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    exact IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve
      q.localGeodesic hlocalzero
  have hcoeff : ∀ i,
      DifferentiableAt ℝ (fun s ↦
        (IntrinsicGeodesic.canonicalBasis (E := E)).repr
          (q.coordinateSolution.curve s) i) 0 := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦
        ((IntrinsicGeodesic.canonicalBasis (E := E)).coord i).toContinuousLinearMap)
        0 0 := hasDerivAt_const 0
      ((IntrinsicGeodesic.canonicalBasis (E := E)).coord i).toContinuousLinearMap
    exact (hc.clm_apply hqderiv).differentiableAt
  have hS : ∀ i, MDiffAt (T% (fun x ↦
      LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
        (curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E)) i x))
      (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M)
      (curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E)) i _
  have hlocal : MDiffAt (fun s ↦ inner ℝ
      (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) q.localGeodesic q.coordinateSolution s)
      (W (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s))) 0 := by
    simpa [IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel] using
      (CurveConnection.mdiffAt_inner_timeFrameField_section
        (I := I) (M := M) (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i x ↦ LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ (t₀ + t)) (IntrinsicGeodesic.canonicalBasis (E := E)) i x)
        q.coordinateSolution.curve
        (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic)
        hqcurve hcoeff hS W hWq)
  have hcurve : ∀ᶠ s in 𝓝 (0 : ℝ),
      curve (shift γ (t₀ + t)) s =
        IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s := by
    filter_upwards [q.agrees] with s hs
    simpa [curve, IntrinsicGeodesic.localState, shift_state] using
      congrArg Bundle.TotalSpace.proj hs
  have hpair : (fun s ↦ inner ℝ (q.shiftedField s)
      (W (curve (shift γ (t₀ + t)) s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦ inner ℝ
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) q.localGeodesic q.coordinateSolution s)
        (W (IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s))) := by
    filter_upwards [hcurve] with s hs
    rw [q.shiftedField_eq_of_curve_eq s hs]
    rw [global_cast_tangent_section_of_eq (I := I) hs W]
    exact global_cast_tangent_inner_of_eq (I := I) (M := M) hs _ _
  have hshifted : MDiffAt (fun s ↦ inner ℝ (q.shiftedField s)
      (W (curve (shift γ (t₀ + t)) s))) 0 :=
    hlocal.congr_of_eventuallyEq hpair
  have htranslated : MDiffAt (fun s ↦ F (t + s)) 0 :=
    hshifted.congr_of_eventuallyEq hscalar
  let translateBack : ℝ → ℝ := fun s ↦ s - t
  have htranslatedAt : DifferentiableAt ℝ (fun s ↦ F (t + s))
      (translateBack t) := by
    simpa [translateBack] using htranslated.differentiableAt
  have htranslateBack : DifferentiableAt ℝ translateBack t := by
    simpa [translateBack] using
      ((hasDerivAt_id' t).sub_const t).differentiableAt
  have hcomp : DifferentiableAt ℝ
      (fun s ↦ F (t + translateBack s)) t :=
    htranslatedAt.comp t htranslateBack
  have hrewrite : F = fun s ↦ F (t + translateBack s) := by
    funext s
    dsimp [translateBack]
    congr 1
    ring
  rw [hrewrite]
  exact hcomp.mdifferentiableAt

/-- A global parallel field satisfies the intrinsic parallel equation at
every time.  The proof reuses the field's actual local tangent-bundle germ,
then translates the scalar characterization back to the fixed time origin.
It therefore establishes a geometric covariant derivative statement rather
than merely a coordinate ODE. -/
theorem GlobalParallelField.isCovariantAccelerationAt_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (t : ℝ) :
    CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀)) p.field t
      (velocity (shift γ t₀) t) 0 := by
  obtain ⟨q, hq⟩ := p.local_germ t
  unfold CurveConnection.IsCovariantAccelerationAt
  intro W hW
  have hscalar :
      (fun s ↦ inner ℝ (p.field (t + s))
        (W (curve (shift γ t₀) (t + s)))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ inner ℝ (q.shiftedField s)
          (W (curve (shift γ (t₀ + t)) s))) := by
    filter_upwards [hq] with s hs
    have htotal :
        (⟨curve (shift γ t₀) (t + s), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + t)) s, q.shiftedField s⟩ := by
      change
        (⟨curve γ (t₀ + (t + s)), p.field (t + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve γ ((t₀ + t) + s), q.shiftedField s⟩
      rw [show t₀ + (t + s) = (t₀ + t) + s by ring]
      exact hs
    exact congrArg (fun z : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
      inner ℝ z.snd (W z.proj)) htotal
  have hcurve0 : curve (shift γ (t₀ + t)) 0 =
      curve (shift γ t₀) t := by
    change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
    rw [add_zero]
  have hWq : MDiffAt (T% W) (curve (shift γ (t₀ + t)) 0) := by
    rw [hcurve0]
    exact hW
  have hstate0 : (shift γ (t₀ + t)).state 0 =
      (shift γ t₀).state t := by
    change γ.state ((t₀ + t) + 0) = γ.state (t₀ + t)
    rw [add_zero]
  have hfield0 :
      (⟨curve (shift γ (t₀ + t)) 0, q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve (shift γ t₀) t, p.field t⟩ := by
    have htotal := hq.self_of_nhds
    change
      (⟨curve γ ((t₀ + t) + 0), q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨curve γ (t₀ + t), p.field t⟩
    have hbaseq : curve (shift γ (t₀ + t)) 0 = curve γ (t₀ + t) := by
      change curve γ ((t₀ + t) + 0) = curve γ (t₀ + t)
      rw [add_zero]
    rw [hbaseq] at htotal
    rw [add_zero] at htotal
    rw [add_zero]
    simpa using htotal.symm
  calc
    CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (p.field s) (W (curve (shift γ t₀) s))) t =
      CurveConnection.curveScalarDeriv
        (fun s ↦ inner ℝ (q.shiftedField s)
          (W (curve (shift γ (t₀ + t)) s))) 0 :=
      CurveConnection.curveScalarDeriv_eq_of_eventuallyEq_const_add hscalar
    _ = inner ℝ 0 (W (curve (shift γ (t₀ + t)) 0)) +
          inner ℝ (q.shiftedField 0)
            (cov W (curve (shift γ (t₀ + t)) 0)
              (velocity (shift γ (t₀ + t)) 0)) :=
      q.isCovariantAccelerationAt_shiftedField_zero W hWq
    _ = inner ℝ 0 (W (curve (shift γ t₀) t)) +
          inner ℝ (p.field t)
            (cov W (curve (shift γ t₀) t) (velocity (shift γ t₀) t)) := by
      exact global_parallel_rhs_eq_of_totalState_eq (I := I) (M := M) (cov := cov)
        hstate0 hfield0 W

/-- A scalar multiple of a global parallel field satisfies the intrinsic
product rule at every time.  Together with the preceding regularity theorem,
this makes scalar test fields available globally along the actual geodesic. -/
theorem GlobalParallelField.isCovariantAccelerationAt_smul
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₀ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₀)
    (f df : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (df t) t)
    (t : ℝ) :
    CurveConnection.IsCovariantAccelerationAt cov (curve (shift γ t₀))
      (fun s ↦ f s • p.field s) t (velocity (shift γ t₀) t)
      (df t • p.field t) := by
  have hparallel := p.isCovariantAccelerationAt_zero t
  have hscalar : ∀ W : (x : M) → TM x,
      MDiffAt (T% W) (curve (shift γ t₀) t) →
        MDiffAt (fun s ↦ inner ℝ (p.field s)
          (W (curve (shift γ t₀) s))) t := by
    intro W hW
    exact p.mdiffAt_inner_field_section t W hW
  have hmul := hparallel.smul
    (hf t).differentiableAt.mdifferentiableAt hscalar
  have hdf : CurveConnection.curveScalarDeriv f t = df t :=
    CurveConnection.curveScalarDeriv_eq_of_hasDerivAt (hf t)
  rw [hdf] at hmul
  simpa only [smul_zero, add_zero] using hmul

/-- Two global parallel fields preserve their mutual Riemannian inner
product at every time.  The proof restarts a finite two-vector parallel germ
at an arbitrary time, transfers its genuine local Gram identity to the two
global fields in total tangent-bundle space, and then uses connectedness of
`ℝ`; it does not presume a global trivialization of the tangent bundle. -/
theorem GlobalParallelField.inner_eq_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₁ w₂ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₁)
    (q : GlobalParallelField (I := I) (M := M) γ t₀ w₂)
    (hmetric : cov.IsMetricCompatibleTangent) (s : ℝ) :
    inner ℝ (p.field s) (q.field s) =
      inner ℝ (p.field 0) (q.field 0) := by
  classical
  let f : ℝ → ℝ := fun x ↦ inner ℝ (p.field x) (q.field x)
  have hlocal : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨gp, hgp⟩ := p.local_germ x
    obtain ⟨gq, hgq⟩ := q.local_germ x
    let w : Fin 2 → TM (curve γ (t₀ + x)) := fun i ↦
      if i = (0 : Fin 2) then p.field x else q.field x
    obtain ⟨g⟩ := exists_parallelFamilyGerm (I := I) (M := M)
      γ (t₀ + x) w hmetric
    have hw₀ : w (0 : Fin 2) = p.field x := by
      change p.field x = p.field x
      rfl
    have hw₁ : w (1 : Fin 2) = q.field x := by
      change q.field x = q.field x
      rfl
    let g₀ : ParallelGerm (I := I) (M := M) γ (t₀ + x) (p.field x) :=
      (g.toParallelGerm (0 : Fin 2)).castInitial hw₀
    let g₁ : ParallelGerm (I := I) (M := M) γ (t₀ + x) (q.field x) :=
      (g.toParallelGerm (1 : Fin 2)).castInitial hw₁
    have hpg₀ := gp.shiftedField_eventuallyEq_of_same_initial g₀
    have hqg₁ := gq.shiftedField_eventuallyEq_of_same_initial g₁
    obtain ⟨r, hr, hgram⟩ := g.exists_interval_shiftedField_inner_eq
    have hg₀ : ∀ u : ℝ,
        g₀.shiftedField u = (g.toParallelGerm (0 : Fin 2)).shiftedField u := by
      intro u
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x)) u) (g₀.shiftedField u)
        ((g.toParallelGerm (0 : Fin 2)).shiftedField u)).mp (by
          simpa only [g₀] using
            (g.toParallelGerm (0 : Fin 2)).castInitial_shiftedField_totalState hw₀ u)
    have hg₁ : ∀ u : ℝ,
        g₁.shiftedField u = (g.toParallelGerm (1 : Fin 2)).shiftedField u := by
      intro u
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x)) u) (g₁.shiftedField u)
        ((g.toParallelGerm (1 : Fin 2)).shiftedField u)).mp (by
          simpa only [g₁] using
            (g.toParallelGerm (1 : Fin 2)).castInitial_shiftedField_totalState hw₁ u)
    have hshift : Tendsto (fun y : ℝ ↦ y - x) (𝓝 x) (𝓝 0) := by
      have hraw := (continuousAt_id.sub continuousAt_const :
        ContinuousAt (id - fun _ : ℝ ↦ x) x).tendsto
      have hfun : (id - fun _ : ℝ ↦ x) = (fun y ↦ y - x) := by rfl
      rw [hfun] at hraw
      simpa only [sub_self] using hraw
    have hball : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [hshift.eventually hgp, hshift.eventually hgq,
      hshift.eventually hpg₀, hshift.eventually hqg₁,
      hshift.eventually hball] with y hpfield hqfield hpg hqg hy
    have hpfield' : p.field (x + (y - x)) =
        g₀.shiftedField (y - x) := by
      rw [hpg] at hpfield
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x)) (y - x))
        (p.field (x + (y - x))) (g₀.shiftedField (y - x))).mp hpfield
    have hqfield' : q.field (x + (y - x)) =
        g₁.shiftedField (y - x) := by
      rw [hqg] at hqfield
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve (shift γ (t₀ + x)) (y - x))
        (q.field (x + (y - x))) (g₁.shiftedField (y - x))).mp hqfield
    have hinner := hgram (0 : Fin 2) (1 : Fin 2) (y - x) hy
    change inner ℝ ((g.toParallelGerm (0 : Fin 2)).shiftedField (y - x))
        ((g.toParallelGerm (1 : Fin 2)).shiftedField (y - x)) = _ at hinner
    rw [← hg₀ (y - x), ← hg₁ (y - x)] at hinner
    change inner ℝ (p.field y) (q.field y) =
      inner ℝ (p.field x) (q.field x)
    rw [show y = x + (y - x) by ring, hpfield', hqfield']
    have hcurve : curve (shift γ t₀) (x + (y - x)) =
        curve (shift γ (t₀ + x)) (y - x) := by
      change curve γ (t₀ + (x + (y - x))) =
        curve γ ((t₀ + x) + (y - x))
      congr 1
      ring
    exact (global_cast_tangent_inner_of_eq (I := I) (M := M) hcurve
      (g₀.shiftedField (y - x)) (g₁.shiftedField (y - x))).trans (by
        rw [hw₀, hw₁] at hinner
        exact hinner)
  have hconst := hlocal.apply_eq_of_preconnectedSpace s (0 : ℝ)
  change inner ℝ (p.field s) (q.field s) =
    inner ℝ (p.field 0) (q.field 0) at hconst
  exact hconst

/-- The zero-time Gram value of two global parallel fields is exactly the
Gram value of their prescribed initial vectors.  The shift-at-zero fibre
change is made explicit here so downstream transport arguments can use the
initial vectors themselves. -/
theorem GlobalParallelField.inner_zero_eq_initialVectors
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w₁ w₂ : TM (curve γ t₀)}
    (p : GlobalParallelField (I := I) (M := M) γ t₀ w₁)
    (q : GlobalParallelField (I := I) (M := M) γ t₀ w₂) :
    inner ℝ (p.field 0) (q.field 0) = inner ℝ w₁ w₂ := by
  have hcurve : curve (shift γ t₀) 0 = curve γ t₀ := by simp
  have hp : p.field 0 =
      cast (congrArg (TangentSpace I) hcurve.symm) w₁ := by
    exact p.field_zero
  have hq : q.field 0 =
      cast (congrArg (TangentSpace I) hcurve.symm) w₂ := by
    exact q.field_zero
  rw [hp, hq]
  exact global_cast_tangent_inner_of_eq (I := I) (M := M) hcurve w₁ w₂

/-- Every finite or infinite prescribed family has coherent global parallel
continuations with its full Gram matrix preserved.  This packages global
parallel existence into the chart-independent interface needed for genuine
parallel frames and later curvature/index-form constructions. -/
theorem exists_globalParallelFields_gram
    {ι : Type*}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} (w : ι → TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (w i),
      (∀ i s, CurveConnection.IsCovariantAccelerationAt cov
        (curve (shift γ t₀)) (p i).field s (velocity (shift γ t₀) s) 0) ∧
      ∀ i j s, inner ℝ ((p i).field s) ((p j).field s) =
        inner ℝ (w i) (w j) := by
  classical
  let p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (w i) := fun i ↦
    Classical.choice (exists_globalParallelField (I := I) (M := M)
      γ t₀ (w i) hmetric)
  refine ⟨p, ?_, ?_⟩
  · intro i s
    exact (p i).isCovariantAccelerationAt_zero s
  · intro i j s
    calc
      inner ℝ ((p i).field s) ((p j).field s) =
          inner ℝ ((p i).field 0) ((p j).field 0) :=
        (p i).inner_eq_initial (p j) hmetric s
      _ = inner ℝ (w i) (w j) :=
        (p i).inner_zero_eq_initialVectors (p j)

/-- The actual velocity of a global ODE geodesic is itself a global parallel
field.  This makes the distinguished tangent direction available to global
frame constructions without selecting an unrelated continuation having the
same initial vector. -/
theorem exists_velocityGlobalParallelField
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ : ℝ)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : GlobalParallelField (I := I) (M := M) γ t₀ (velocity γ t₀),
      ∀ s, p.field s = velocity (shift γ t₀) s := by
  let p : GlobalParallelField (I := I) (M := M) γ t₀ (velocity γ t₀) := {
    field := fun s ↦ velocity (shift γ t₀) s
    field_zero := by
      have htotal :
          (⟨curve (shift γ t₀) 0, velocity (shift γ t₀) 0⟩ :
            Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
          ⟨curve γ t₀, velocity γ t₀⟩ := by
        change γ.state (t₀ + 0) = γ.state t₀
        rw [add_zero]
      rw [shift_curve, add_zero] at htotal
      exact (@Bundle.TotalSpace.mk_inj M E (TangentSpace I : M → Type _)
        (curve γ t₀) (velocity (shift γ t₀) 0) (velocity γ t₀)).mp htotal
    local_germ := ?_ }
  · refine ⟨p, ?_⟩
    intro s
    rfl
  · intro s
    obtain ⟨q⟩ := exists_parallelGerm (I := I) (M := M) γ (t₀ + s)
      (velocity (shift γ t₀) s) hmetric
    refine ⟨q, ?_⟩
    have hq := q.shiftedField_eventuallyEq_velocity_of_initial (by rfl)
    filter_upwards [hq] with u hu
    have hstate := shift_shift_state (I := I) (M := M) (γ := γ) t₀ s u
    have hvel : velocity (shift γ t₀) (s + u) =
        velocity (shift γ (t₀ + s)) u := by
      change ((shift γ t₀).state (s + u)).snd =
        ((shift γ (t₀ + s)).state u).snd
      exact congrArg Bundle.TotalSpace.snd hstate
    rw [hvel, ← hu]

/-- A unit-speed complete global ODE geodesic carries a global orthonormal
parallel frame adapted to its actual velocity.  The zeroth member is exactly
the velocity at every time, all other members remain transverse, and the
parallel equation is intrinsic.  This is the global frame datum needed by a
future second-variation proof; it makes no endpoint-minimizing claim. -/
theorem exists_global_adapted_parallelFrame
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hn : 1 ≤ Module.finrank ℝ (TM (curve γ t₀))) :
    letI : Nonempty (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
      ⟨⟨0, by omega⟩⟩
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
          (TM (curve γ t₀)),
      b ⟨0, by omega⟩ = velocity γ t₀ ∧
      ∃ p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i),
        (∀ i s, CurveConnection.IsCovariantAccelerationAt cov
          (curve (shift γ t₀)) (p i).field s (velocity (shift γ t₀) s) 0) ∧
        (∀ s, (p ⟨0, by omega⟩).field s = velocity (shift γ t₀) s) ∧
        (∀ s, Orthonormal ℝ (fun i ↦ (p i).field s)) ∧
        (∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))), ∀ s,
          inner ℝ ((p i).field s) (velocity (shift γ t₀) s) = 0) := by
  classical
  let i0 : Fin (Module.finrank ℝ (TM (curve γ t₀))) := ⟨0, by omega⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_first hunit hn
  have hb0 : b i0 = velocity γ t₀ := by
    simpa [i0] using hb
  have hsingle : ∀ i, ∃ p : GlobalParallelField (I := I) (M := M) γ t₀ (b i),
      (i = i0 → ∀ s, p.field s = velocity (shift γ t₀) s) := by
    intro i
    by_cases hi : i = i0
    · subst i
      rw [hb0]
      obtain ⟨p, hp⟩ := exists_velocityGlobalParallelField
        (I := I) (M := M) γ t₀ hmetric
      exact ⟨p, fun _ ↦ hp⟩
    · obtain ⟨p⟩ := exists_globalParallelField (I := I) (M := M)
        γ t₀ (b i) hmetric
      exact ⟨p, fun h ↦ (hi h).elim⟩
  choose p hvelocity using hsingle
  have hacc : ∀ i s, CurveConnection.IsCovariantAccelerationAt cov
      (curve (shift γ t₀)) (p i).field s (velocity (shift γ t₀) s) 0 := by
    intro i s
    exact (p i).isCovariantAccelerationAt_zero s
  have hgram : ∀ i j s,
      inner ℝ ((p i).field s) ((p j).field s) =
        inner ℝ ((p i).field 0) ((p j).field 0) := by
    intro i j s
    exact (p i).inner_eq_initial (p j) hmetric s
  refine ⟨b, ?_, p, hacc, ?_, ?_, ?_⟩
  · simpa [i0] using hb0
  · intro s
    exact hvelocity i0 rfl s
  · intro s
    rw [orthonormal_iff_ite]
    intro i j
    have hborth := b.orthonormal
    rw [orthonormal_iff_ite] at hborth
    calc
      inner ℝ ((p i).field s) ((p j).field s) =
          inner ℝ ((p i).field 0) ((p j).field 0) := hgram i j s
      _ = inner ℝ (b i) (b j) :=
        (p i).inner_zero_eq_initialVectors (p j)
      _ = if i = j then 1 else 0 := hborth i j
  · intro i hi s
    have hborth := b.orthonormal
    rw [orthonormal_iff_ite] at hborth
    have hine : i ≠ i0 := (Finset.mem_erase.mp hi).1
    calc
      inner ℝ ((p i).field s) (velocity (shift γ t₀) s) =
          inner ℝ ((p i).field s) ((p i0).field s) := by
            rw [hvelocity i0 rfl s]
      _ = inner ℝ ((p i).field 0) ((p i0).field 0) := hgram i i0 s
      _ = inner ℝ (b i) (b i0) :=
        (p i).inner_zero_eq_initialVectors (p i0)
      _ = 0 := by simpa only [if_neg hine] using hborth i i0

/-- Once a partial parallel field can be extended strictly at every finite
endpoint, its Zorn-maximal representative has all of `ℝ` as domain and hence
is an actual global parallel field.  This isolates the remaining analytic
endpoint obligation from the already-complete gluing and order theory. -/
theorem exists_globalParallelField_of_strict_extension
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t₀ : ℝ) (w₀ : TM (curve γ t₀))
    (hmetric : cov.IsMetricCompatibleTangent)
    (hextend : ∀ p : PartialParallelField (I := I) (M := M) γ t₀ w₀,
      p.domain ≠ Set.univ →
        ∃ q : PartialParallelField (I := I) (M := M) γ t₀ w₀,
          p ≤ q ∧ p.domain ⊂ q.domain) :
    Nonempty (GlobalParallelField (I := I) (M := M) γ t₀ w₀) := by
  obtain ⟨p, hpmax⟩ := PartialParallelField.exists_maximal
    (I := I) (M := M) γ t₀ w₀ hmetric
  have hdomain : p.domain = Set.univ := by
    by_contra hne
    obtain ⟨q, hpq, hproper⟩ := hextend p hne
    have hpqeq : p = q := hpmax.eq_of_le hpq
    exact hproper.ne (congrArg PartialParallelField.domain hpqeq)
  refine ⟨{
    field := p.field
    field_zero := p.field_zero
    local_germ := ?_ }⟩
  intro s
  exact p.local_germ s (by simpa [hdomain])

end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
