/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Limits
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Neighborhoods
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.LocallyUniform

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Compact selection lemmas for stability arguments (CompactContact)

Part of the compact-extremum selection tools used in viscosity stability
proofs. Split from `Selection.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/-- A continuous function is upper semicontinuous on a set. -/
theorem ContinuousOn.upperSemicontinuousOn_real {C : Set (Point n)}
    {φ : Point n -> Real} (hφ : ContinuousOn φ C) :
    UpperSemicontinuousOn φ C :=
  (continuousOn_iff_lower_upperSemicontinuousOn.mp hφ).2

/-- A continuous function is lower semicontinuous on a set. -/
theorem ContinuousOn.lowerSemicontinuousOn_real {C : Set (Point n)}
    {φ : Point n -> Real} (hφ : ContinuousOn φ C) :
    LowerSemicontinuousOn φ C :=
  (continuousOn_iff_lower_upperSemicontinuousOn.mp hφ).1

/--
Subtracting a continuous perturbation preserves upper semicontinuity.
-/
theorem UpperSemicontinuousOn.sub_continuousOn
    {C : Set (Point n)} {u φ : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hφ : ContinuousOn φ C) :
    UpperSemicontinuousOn (fun x => u x - φ x) C := by
  have hnegφ : UpperSemicontinuousOn (fun x => -φ x) C :=
    ContinuousOn.upperSemicontinuousOn_real hφ.neg
  simpa [sub_eq_add_neg] using hu.add hnegφ

/--
Subtracting a continuous perturbation preserves lower semicontinuity.
-/
theorem LowerSemicontinuousOn.sub_continuousOn
    {C : Set (Point n)} {u φ : Point n -> Real}
    (hu : LowerSemicontinuousOn u C) (hφ : ContinuousOn φ C) :
    LowerSemicontinuousOn (fun x => u x - φ x) C := by
  have hnegφ : LowerSemicontinuousOn (fun x => -φ x) C :=
    ContinuousOn.lowerSemicontinuousOn_real hφ.neg
  simpa [sub_eq_add_neg] using hu.add hnegφ

/--
An upper semicontinuous function attains its maximum on a nonempty compact set.
-/
theorem exists_isMaxOn_of_upperSemicontinuousOn_isCompact
    {K : Set (Point n)} {u : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K) (hu : UpperSemicontinuousOn u K) :
    ∃ x ∈ K, IsMaxOn u K x :=
  UpperSemicontinuousOn.exists_isMaxOn hne hK hu

/--
A lower semicontinuous function attains its minimum on a nonempty compact set.
-/
theorem exists_isMinOn_of_lowerSemicontinuousOn_isCompact
    {K : Set (Point n)} {u : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K) (hu : LowerSemicontinuousOn u K) :
    ∃ x ∈ K, IsMinOn u K x :=
  LowerSemicontinuousOn.exists_isMinOn hne hK hu

/--
Upper semicontinuous functions minus continuous perturbations attain maxima on
nonempty compact sets.
-/
theorem exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
    {K : Set (Point n)} {u φ : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K)
    (hu : UpperSemicontinuousOn u K) (hφ : ContinuousOn φ K) :
    ∃ x ∈ K, IsMaxOn (fun y => u y - φ y) K x :=
  exists_isMaxOn_of_upperSemicontinuousOn_isCompact hne hK
    (UpperSemicontinuousOn.sub_continuousOn hu hφ)

/--
Lower semicontinuous functions minus continuous perturbations attain minima on
nonempty compact sets.
-/
theorem exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
    {K : Set (Point n)} {u φ : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K)
    (hu : LowerSemicontinuousOn u K) (hφ : ContinuousOn φ K) :
    ∃ x ∈ K, IsMinOn (fun y => u y - φ y) K x :=
  exists_isMinOn_of_lowerSemicontinuousOn_isCompact hne hK
    (LowerSemicontinuousOn.sub_continuousOn hu hφ)

/--
The compact maximum selected above is also a local maximum on the compact set.
-/
theorem exists_isLocalMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
    {K : Set (Point n)} {u φ : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K)
    (hu : UpperSemicontinuousOn u K) (hφ : ContinuousOn φ K) :
    ∃ x ∈ K, IsLocalMaxOn (fun y => u y - φ y) K x := by
  rcases exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
    hne hK hu hφ with ⟨x, hx, hmax⟩
  exact ⟨x, hx, hmax.isLocalMaxOn⟩

/--
The compact minimum selected above is also a local minimum on the compact set.
-/
theorem exists_isLocalMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
    {K : Set (Point n)} {u φ : Point n -> Real}
    (hne : K.Nonempty) (hK : IsCompact K)
    (hu : LowerSemicontinuousOn u K) (hφ : ContinuousOn φ K) :
    ∃ x ∈ K, IsLocalMinOn (fun y => u y - φ y) K x := by
  rcases exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
    hne hK hu hφ with ⟨x, hx, hmin⟩
  exact ⟨x, hx, hmin.isLocalMinOn⟩

/--
A local maximum of `u - φ` is exactly a touching from above of `u` by `φ`.
-/
theorem touchesAboveOn_of_isLocalMaxOn_sub
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n}
    (hmax : IsLocalMaxOn (fun y => u y - φ y) C x) :
    TouchesAboveOn C u φ x :=
  hmax

/--
A local minimum of `u - φ` is exactly a touching from below of `u` by `φ`.
-/
theorem touchesBelowOn_of_isLocalMinOn_sub
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n}
    (hmin : IsLocalMinOn (fun y => u y - φ y) C x) :
    TouchesBelowOn C u φ x :=
  hmin

/--
A global maximum of `u - φ` on `C` gives a touching from above on `C`.
-/
theorem touchesAboveOn_of_isMaxOn_sub
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n}
    (hmax : IsMaxOn (fun y => u y - φ y) C x) :
    TouchesAboveOn C u φ x :=
  touchesAboveOn_of_isLocalMaxOn_sub hmax.isLocalMaxOn

/--
A global minimum of `u - φ` on `C` gives a touching from below on `C`.
-/
theorem touchesBelowOn_of_isMinOn_sub
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n}
    (hmin : IsMinOn (fun y => u y - φ y) C x) :
    TouchesBelowOn C u φ x :=
  touchesBelowOn_of_isLocalMinOn_sub hmin.isLocalMinOn

/--
If the half-size identity-Hessian perturbation supports `u` from above on `K`,
then the full perturbation has strict contact from above on `K`.
-/
theorem strict_isMaxOn_sub_quadraticModel_add_identity_of_forall_le_half
    {K : Set (Point n)} {u : Point n -> Real} {x p : Point n}
    {X : Hessian n} {δ : Real} (hδ : 0 < δ)
    (hle : ∀ y : Point n, y ∈ K ->
      u y <= quadraticModel x (u x) p (X + (δ / 2) • (1 : Hessian n)) y) :
    ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - quadraticModel x (u x) p (X + δ • (1 : Hessian n)) y <=
          u x - quadraticModel x (u x) p (X + δ • (1 : Hessian n)) x - η := by
  intro V hV
  rcases Metric.mem_nhds_iff.1 hV with ⟨ε, hε, hballV⟩
  refine ⟨((1 / 4 : Real) * δ) * ε ^ 2, by positivity, ?_⟩
  intro y hyK hyV
  let qhalf : Real := quadraticModel x (u x) p (X + (δ / 2) • (1 : Hessian n)) y
  let qfull : Real := quadraticModel x (u x) p (X + δ • (1 : Hessian n)) y
  let qid : Real := quadraticModel x 0 0 ((δ / 2) • (1 : Hessian n)) y
  have hnotBall : y ∉ Metric.ball x ε := fun hyball => hyV (hballV hyball)
  have hεnorm : ε <= ‖y - x‖ := by
    have hnot : ¬ dist y x < ε := by
      simpa [Metric.mem_ball] using hnotBall
    simpa [dist_eq_norm] using le_of_not_gt hnot
  have hεsq : ε ^ 2 <= ‖y - x‖ ^ 2 :=
    pow_le_pow_left₀ hε.le hεnorm 2
  have hqid_lower : ((1 / 2 : Real) * (δ / 2)) * ‖y - x‖ ^ 2 <= qid :=
    quadraticModel_scalar_identity_lower_bound x y (by positivity)
  have hgap_le_qid : ((1 / 4 : Real) * δ) * ε ^ 2 <= qid := by
    calc
      ((1 / 4 : Real) * δ) * ε ^ 2 <=
          ((1 / 4 : Real) * δ) * ‖y - x‖ ^ 2 := by
        gcongr
      _ = ((1 / 2 : Real) * (δ / 2)) * ‖y - x‖ ^ 2 := by ring
      _ <= qid := hqid_lower
  have hH : X + δ • (1 : Hessian n) =
      (X + (δ / 2) • (1 : Hessian n)) + (δ / 2) • (1 : Hessian n) := by
    ext i j
    by_cases hij : i = j
    · simp [hij]
      ring
    · simp [hij]
  have hsplit : qfull = qhalf + qid := by
    dsimp [qfull, qhalf, qid]
    rw [hH]
    simpa using
      (quadraticModel_add x (u x) 0 p 0
        (X + (δ / 2) • (1 : Hessian n)) ((δ / 2) • (1 : Hessian n)) y)
  have hxmodel :
      quadraticModel x (u x) p (X + δ • (1 : Hessian n)) x = u x := by
    simp [quadraticModel]
  calc
    u y - quadraticModel x (u x) p (X + δ • (1 : Hessian n)) y =
        u y - qfull := by rfl
    _ <= -qid := by
      have := hle y hyK
      linarith
    _ <= -(((1 / 4 : Real) * δ) * ε ^ 2) := by linarith
    _ = u x - quadraticModel x (u x) p (X + δ • (1 : Hessian n)) x -
        ((1 / 4 : Real) * δ) * ε ^ 2 := by
      rw [hxmodel]
      ring

/--
If the half-size identity-Hessian perturbation supports `u` from below on `K`,
then the full perturbation has strict contact from below on `K`.
-/
theorem strict_isMinOn_sub_quadraticModel_sub_identity_of_forall_half_le
    {K : Set (Point n)} {u : Point n -> Real} {x p : Point n}
    {X : Hessian n} {δ : Real} (hδ : 0 < δ)
    (hle : ∀ y : Point n, y ∈ K ->
      quadraticModel x (u x) p (X - (δ / 2) • (1 : Hessian n)) y <= u y) :
    ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ η > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - quadraticModel x (u x) p (X - δ • (1 : Hessian n)) x + η <=
          u y - quadraticModel x (u x) p (X - δ • (1 : Hessian n)) y := by
  intro V hV
  rcases Metric.mem_nhds_iff.1 hV with ⟨ε, hε, hballV⟩
  refine ⟨((1 / 4 : Real) * δ) * ε ^ 2, by positivity, ?_⟩
  intro y hyK hyV
  let qhalf : Real := quadraticModel x (u x) p (X - (δ / 2) • (1 : Hessian n)) y
  let qfull : Real := quadraticModel x (u x) p (X - δ • (1 : Hessian n)) y
  let qid : Real := quadraticModel x 0 0 ((δ / 2) • (1 : Hessian n)) y
  have hnotBall : y ∉ Metric.ball x ε := fun hyball => hyV (hballV hyball)
  have hεnorm : ε <= ‖y - x‖ := by
    have hnot : ¬ dist y x < ε := by
      simpa [Metric.mem_ball] using hnotBall
    simpa [dist_eq_norm] using le_of_not_gt hnot
  have hεsq : ε ^ 2 <= ‖y - x‖ ^ 2 :=
    pow_le_pow_left₀ hε.le hεnorm 2
  have hqid_lower : ((1 / 2 : Real) * (δ / 2)) * ‖y - x‖ ^ 2 <= qid :=
    quadraticModel_scalar_identity_lower_bound x y (by positivity)
  have hgap_le_qid : ((1 / 4 : Real) * δ) * ε ^ 2 <= qid := by
    calc
      ((1 / 4 : Real) * δ) * ε ^ 2 <=
          ((1 / 4 : Real) * δ) * ‖y - x‖ ^ 2 := by
        gcongr
      _ = ((1 / 2 : Real) * (δ / 2)) * ‖y - x‖ ^ 2 := by ring
      _ <= qid := hqid_lower
  have hH : X - (δ / 2) • (1 : Hessian n) =
      (X - δ • (1 : Hessian n)) + (δ / 2) • (1 : Hessian n) := by
    ext i j
    by_cases hij : i = j
    · simp [hij]
      ring
    · simp [hij]
  have hsplit : qhalf = qfull + qid := by
    dsimp [qfull, qhalf, qid]
    rw [hH]
    simpa using
      (quadraticModel_add x (u x) 0 p 0
        (X - δ • (1 : Hessian n)) ((δ / 2) • (1 : Hessian n)) y)
  have hxmodel :
      quadraticModel x (u x) p (X - δ • (1 : Hessian n)) x = u x := by
    simp [quadraticModel]
  calc
    u x - quadraticModel x (u x) p (X - δ • (1 : Hessian n)) x +
        ((1 / 4 : Real) * δ) * ε ^ 2 =
        ((1 / 4 : Real) * δ) * ε ^ 2 := by
      rw [hxmodel]
      ring
    _ <= qid := hgap_le_qid
    _ <= u y - qfull := by
      have := hle y hyK
      linarith
    _ = u y - quadraticModel x (u x) p (X - δ • (1 : Hessian n)) y := by rfl

/--
A selected local maximum contact gives a superjet graph point.
-/
theorem superjetGraph_of_isLocalMaxOn_sub_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hmax : IsLocalMaxOn (fun y => u y - φ y) C x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    ((x, u x), J) ∈ SuperjetGraph C u := by
  exact ⟨hx, rfl,
    superjet_of_touchesAbove_hasSecondOrderExpansionWithin
      (touchesAboveOn_of_isLocalMaxOn_sub hmax) hφ⟩

/--
A selected local minimum contact gives a subjet graph point.
-/
theorem subjetGraph_of_isLocalMinOn_sub_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hmin : IsLocalMinOn (fun y => u y - φ y) C x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    ((x, u x), J) ∈ SubjetGraph C u := by
  exact ⟨hx, rfl,
    subjet_of_touchesBelow_hasSecondOrderExpansionWithin
      (touchesBelowOn_of_isLocalMinOn_sub hmin) hφ⟩

/--
A selected compact maximum contact gives a superjet graph point.
-/
theorem superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hmax : IsMaxOn (fun y => u y - φ y) C x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    ((x, u x), J) ∈ SuperjetGraph C u :=
  superjetGraph_of_isLocalMaxOn_sub_hasSecondOrderExpansionWithin hx
    hmax.isLocalMaxOn hφ

/--
A selected compact minimum contact gives a subjet graph point.
-/
theorem subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x : Point n} {J : Jet n}
    (hx : x ∈ C)
    (hmin : IsMinOn (fun y => u y - φ y) C x)
    (hφ : HasSecondOrderExpansionWithin C φ x J) :
    ((x, u x), J) ∈ SubjetGraph C u :=
  subjetGraph_of_isLocalMinOn_sub_hasSecondOrderExpansionWithin hx
    hmin.isLocalMinOn hφ

/--
If the set of indices `i` for which there exists a local maximum contact
between `uᵢ i` and a test function `φ` with second-order expansion `Jᵢ i`
belongs to `l`, then the set of indices `i` for which there exists a
corresponding superjet graph point belongs to `l`.
-/
theorem eventually_exists_superjetGraph_of_isLocalMaxOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι}
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsLocalMaxOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i)) :
    ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SuperjetGraph C (uᵢ i) := by
  exact h.mono fun i hi => by
    rcases hi with ⟨x, hx, hmax, hφ⟩
    exact ⟨x, hx,
      superjetGraph_of_isLocalMaxOn_sub_hasSecondOrderExpansionWithin
        hx hmax hφ⟩

/--
If the set of indices `i` for which there exists a local minimum contact
between `uᵢ i` and a test function `φ` with second-order expansion `Jᵢ i`
belongs to `l`, then the set of indices `i` for which there exists a
corresponding subjet graph point belongs to `l`.
-/
theorem eventually_exists_subjetGraph_of_isLocalMinOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι}
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsLocalMinOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i)) :
    ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SubjetGraph C (uᵢ i) := by
  exact h.mono fun i hi => by
    rcases hi with ⟨x, hx, hmin, hφ⟩
    exact ⟨x, hx,
      subjetGraph_of_isLocalMinOn_sub_hasSecondOrderExpansionWithin
        hx hmin hφ⟩

/--
If the set of indices `i` for which there exists a maximum point of
`uᵢ i - φ` on `C` with second-order expansion `Jᵢ i` belongs to `l`, then the
set of indices `i` for which there exists a corresponding superjet graph point
belongs to `l`.
-/
theorem eventually_exists_superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι}
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsMaxOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i)) :
    ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SuperjetGraph C (uᵢ i) := by
  exact h.mono fun i hi => by
    rcases hi with ⟨x, hx, hmax, hφ⟩
    exact ⟨x, hx,
      superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin hx hmax hφ⟩

/--
If the set of indices `i` for which there exists a minimum point of
`uᵢ i - φ` on `C` with second-order expansion `Jᵢ i` belongs to `l`, then the
set of indices `i` for which there exists a corresponding subjet graph point
belongs to `l`.
-/
theorem eventually_exists_subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι}
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsMinOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i)) :
    ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SubjetGraph C (uᵢ i) := by
  exact h.mono fun i hi => by
    rcases hi with ⟨x, hx, hmin, hφ⟩
    exact ⟨x, hx,
      subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin hx hmin hφ⟩

/--
Assume that the set of indices `i` for which there exists `x ∈ C` with
`((x, uᵢ i x), Jᵢ i) ∈ SuperjetGraph C (uᵢ i)` belongs to the filter `l`.
Then, for every set of indices `A` with `A ∈ l`, the union
`⋃ i ∈ A, SuperjetGraph C (uᵢ i)` is nonempty.
-/
theorem exists_mem_tailUnion_superjetGraph_of_eventually_exists_superjetGraph
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {Jᵢ : ι -> Jet n} {l : Filter ι} [l.NeBot]
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SuperjetGraph C (uᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ z : (Point n × Real) × Jet n,
      z ∈ ⋃ i ∈ A, SuperjetGraph C (uᵢ i) := by
  have hlarge : A ∩ {i | ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SuperjetGraph C (uᵢ i)} ∈ l :=
    inter_mem hA h
  rcases Filter.nonempty_of_mem hlarge with ⟨i, hiA, x, hx, hz⟩
  exact ⟨((x, uᵢ i x), Jᵢ i),
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hz⟩⟩⟩

/--
Assume that the set of indices `i` for which there exists `x ∈ C` with
`((x, uᵢ i x), Jᵢ i) ∈ SubjetGraph C (uᵢ i)` belongs to the filter `l`.
Then, for every set of indices `A` with `A ∈ l`, the union
`⋃ i ∈ A, SubjetGraph C (uᵢ i)` is nonempty.
-/
theorem exists_mem_tailUnion_subjetGraph_of_eventually_exists_subjetGraph
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {Jᵢ : ι -> Jet n} {l : Filter ι} [l.NeBot]
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SubjetGraph C (uᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ z : (Point n × Real) × Jet n,
      z ∈ ⋃ i ∈ A, SubjetGraph C (uᵢ i) := by
  have hlarge : A ∩ {i | ∃ x ∈ C,
      ((x, uᵢ i x), Jᵢ i) ∈ SubjetGraph C (uᵢ i)} ∈ l :=
    inter_mem hA h
  rcases Filter.nonempty_of_mem hlarge with ⟨i, hiA, x, hx, hz⟩
  exact ⟨((x, uᵢ i x), Jᵢ i),
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiA, hz⟩⟩⟩

/--
Assume that the set of indices `i` for which there exists `x ∈ C` satisfying
`IsMaxOn (fun y => uᵢ i y - φ y) C x` and
`HasSecondOrderExpansionWithin C φ x (Jᵢ i)` belongs to the filter `l`.
Then, for every set of indices `A` with `A ∈ l`, the union
`⋃ i ∈ A, SuperjetGraph C (uᵢ i)` contains a graph point.
-/
theorem exists_mem_tailUnion_superjetGraph_of_eventually_exists_isMaxOn_sub
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι} [l.NeBot]
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsMaxOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ z : (Point n × Real) × Jet n,
      z ∈ ⋃ i ∈ A, SuperjetGraph C (uᵢ i) :=
  exists_mem_tailUnion_superjetGraph_of_eventually_exists_superjetGraph
    (eventually_exists_superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin h)
    hA

/--
Assume that the set of indices `i` for which there exists `x ∈ C` satisfying
`IsMinOn (fun y => uᵢ i y - φ y) C x` and
`HasSecondOrderExpansionWithin C φ x (Jᵢ i)` belongs to the filter `l`.
Then, for every set of indices `A` with `A ∈ l`, the union
`⋃ i ∈ A, SubjetGraph C (uᵢ i)` contains a graph point.
-/
theorem exists_mem_tailUnion_subjetGraph_of_eventually_exists_isMinOn_sub
    {ι : Type*} {C : Set (Point n)} {uᵢ : ι -> Point n -> Real}
    {φ : Point n -> Real} {Jᵢ : ι -> Jet n} {l : Filter ι} [l.NeBot]
    (h : ∀ᶠ i in l, ∃ x ∈ C,
      IsMinOn (fun y => uᵢ i y - φ y) C x ∧
      HasSecondOrderExpansionWithin C φ x (Jᵢ i))
    {A : Set ι} (hA : A ∈ l) :
    ∃ z : (Point n × Real) × Jet n,
      z ∈ ⋃ i ∈ A, SubjetGraph C (uᵢ i) :=
  exists_mem_tailUnion_subjetGraph_of_eventually_exists_subjetGraph
    (eventually_exists_subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin h)
    hA

/--
Selected compact maximum contacts whose graph triples converge give
tail-closure membership for the limiting superjet triple.
-/
theorem tailClosureSuperjetGraph_of_tendsto_isMaxOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMaxOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  refine tailClosureSuperjetGraph_of_tendsto_superjetGraph_components
    (uᵢ := uᵢ) hx hu hJ ?_
  exact hcontact.mono fun i hi =>
    superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin
      hi.1 hi.2.1 hi.2.2

/--
Selected compact minimum contacts whose graph triples converge give
tail-closure membership for the limiting subjet triple.
-/
theorem tailClosureSubjetGraph_of_tendsto_isMinOn_sub_hasSecondOrderExpansionWithin
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMinOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (Jᵢ i)) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  refine tailClosureSubjetGraph_of_tendsto_subjetGraph_components
    (uᵢ := uᵢ) hx hu hJ ?_
  exact hcontact.mono fun i hi =>
    subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin
      hi.1 hi.2.1 hi.2.2

/--
Let `K ⊆ C`. Suppose `xᵢ → x`, `uᵢ i (xᵢ i) → u x`, and `Jᵢ → J` along `l`.
Assume that the set of indices `i` for which `xᵢ i ∈ K`,
`IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i)`, and
`HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)` all hold belongs to `l`.
Assume also that the set of indices `i` for which
`K ∈ nhdsWithin (xᵢ i) C` belongs to `l`. Then `((x, u x), J)` belongs to the
tail closure of the superjet graphs on `C`.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_tendsto_isMaxOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, u x), J) ∈ TailClosureSuperjetGraph C uᵢ l := by
  refine tailClosureSuperjetGraph_of_tendsto_superjetGraph_mem_nhdsWithin
    hKC hx hu hJ ?_ hKnhds
  exact hcontact.mono fun i hi =>
    superjetGraph_of_isMaxOn_sub_hasSecondOrderExpansionWithin
      hi.1 hi.2.1 hi.2.2

/--
Let `K ⊆ C`. Suppose `xᵢ → x`, `uᵢ i (xᵢ i) → u x`, and `Jᵢ → J` along `l`.
Assume that the set of indices `i` for which `xᵢ i ∈ K`,
`IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i)`, and
`HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i)` all hold belongs to `l`.
Assume also that the set of indices `i` for which
`K ∈ nhdsWithin (xᵢ i) C` belongs to `l`. Then `((x, u x), J)` belongs to the
tail closure of the subjet graphs on `C`.
-/
theorem tailClosureSubjetGraph_to_ambient_of_tendsto_isMinOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {J : Jet n}
    {xᵢ : ι -> Point n} {Jᵢ : ι -> Jet n}
    (hKC : K ⊆ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hu : Tendsto (fun i => uᵢ i (xᵢ i)) l (nhds (u x)))
    (hJ : Tendsto Jᵢ l (nhds J))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (Jᵢ i))
    (hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C) :
    ((x, u x), J) ∈ TailClosureSubjetGraph C uᵢ l := by
  refine tailClosureSubjetGraph_of_tendsto_subjetGraph_mem_nhdsWithin
    hKC hx hu hJ ?_ hKnhds
  exact hcontact.mono fun i hi =>
    subjetGraph_of_isMinOn_sub_hasSecondOrderExpansionWithin
      hi.1 hi.2.1 hi.2.2

end ViscositySolns
