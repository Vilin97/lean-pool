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

import LeanPool.PoincareGeometry.BonnetMyers.GlobalIntrinsicGeodesic

/-!
# Consequences of an endpoint-minimizing global geodesic

The metric Hopf--Rinow layer has already produced a continuous exact metric
segment, while the ODE layer has produced smooth complete geodesics. The
remaining regularity bridge must identify one of those objects. This module
records the nontrivial consequence once that identification is established:
an endpoint distance equality for a constant-speed global geodesic forces
every subsegment to be distance-realizing and minimal among smooth
competitors. No existence of such an endpoint-matching geodesic is assumed
or claimed here.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

/-! ### A finite extended-real saturation lemma -/

/-- If three quantities are bounded above by finite budgets and their sum is
at least the sum of those budgets, then the middle quantity attains its
budget. This is the cancellation step used to pass endpoint minimality to a
subsegment without silently assuming finite Riemannian distance. -/
private lemma ennreal_middle_eq_of_total_lower_bound
    {a b c A B C : ℝ≥0∞}
    (hA : A ≠ ⊤) (hC : C ≠ ⊤)
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (htotal : A + B + C ≤ a + b + c) : b = B := by
  apply le_antisymm hb
  have hsum : A + B + C ≤ A + b + C := by
    calc
      A + B + C ≤ a + b + c := htotal
      _ ≤ A + b + C := by
        gcongr
  have hsum' : A + B ≤ A + b := by
    apply (ENNReal.add_le_add_iff_right hC).mp
    simpa [add_assoc] using hsum
  exact (ENNReal.add_le_add_iff_left hA).mp hsum'

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- If a constant-speed global ODE geodesic realizes the Riemannian distance
between two endpoints, it realizes the distance between every ordered pair of
intermediate times. The proof uses the Riemannian triangle inequality and
finite `ENNReal` cancellation, so it is valid before replacing the intrinsic
extended distance by a finite metric. -/
theorem riemannianEDist_eq_constant_speed_mul_of_endpoint_distance_eq_length
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {a b r s : ℝ} (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b)
    (hendpoint : riemannianEDist I (curve γ a) (curve γ b) =
      ‖v₀‖ₑ * ENNReal.ofReal (b - a)) :
    riemannianEDist I (curve γ r) (curve γ s) =
      ‖v₀‖ₑ * ENNReal.ofReal (s - r) := by
  let A : ℝ≥0∞ := ‖v₀‖ₑ * ENNReal.ofReal (r - a)
  let B : ℝ≥0∞ := ‖v₀‖ₑ * ENNReal.ofReal (s - r)
  let C : ℝ≥0∞ := ‖v₀‖ₑ * ENNReal.ofReal (b - s)
  let d₁ : ℝ≥0∞ := riemannianEDist I (curve γ a) (curve γ r)
  let d₂ : ℝ≥0∞ := riemannianEDist I (curve γ r) (curve γ s)
  let d₃ : ℝ≥0∞ := riemannianEDist I (curve γ s) (curve γ b)
  have hA : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hC : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hd₁ : d₁ ≤ A := by
    exact riemannianEDist_le_constant_speed_mul (I := I) (M := M)
      γ hmetric har
  have hd₂ : d₂ ≤ B := by
    exact riemannianEDist_le_constant_speed_mul (I := I) (M := M)
      γ hmetric hrs
  have hd₃ : d₃ ≤ C := by
    exact riemannianEDist_le_constant_speed_mul (I := I) (M := M)
      γ hmetric hsb
  have htriangle : riemannianEDist I (curve γ a) (curve γ b) ≤
      d₁ + d₂ + d₃ := by
    calc
      riemannianEDist I (curve γ a) (curve γ b) ≤
          riemannianEDist I (curve γ a) (curve γ r) +
            riemannianEDist I (curve γ r) (curve γ b) :=
        riemannianEDist_triangle
      _ ≤ riemannianEDist I (curve γ a) (curve γ r) +
          (riemannianEDist I (curve γ r) (curve γ s) +
            riemannianEDist I (curve γ s) (curve γ b)) := by
        gcongr
        exact riemannianEDist_triangle
      _ = d₁ + d₂ + d₃ := by
        dsimp [d₁, d₂, d₃]
        ac_rfl
  have hsum_eq : A + B + C = ‖v₀‖ₑ * ENNReal.ofReal (b - a) := by
    dsimp [A, B, C]
    have hra : 0 ≤ r - a := sub_nonneg.mpr har
    have hrs' : 0 ≤ s - r := sub_nonneg.mpr hrs
    have hsb' : 0 ≤ b - s := sub_nonneg.mpr hsb
    rw [← mul_add, ← mul_add,
      ← ENNReal.ofReal_add hra hrs',
      ← ENNReal.ofReal_add (add_nonneg hra hrs') hsb']
    congr 1
    ring_nf
  have htotal : A + B + C ≤ d₁ + d₂ + d₃ := by
    rw [hsum_eq, ← hendpoint]
    exact htriangle
  have hmiddle := ennreal_middle_eq_of_total_lower_bound hA hC hd₁ hd₂ hd₃ htotal
  simpa [d₂, B] using hmiddle

/-- Every smooth competitor between two subsegment endpoints has length at
least the constant-speed length of an endpoint-minimizing global geodesic.
This is the precise smooth-competitor minimum needed before a second-variation
nonnegativity theorem can be applied. -/
theorem constant_speed_mul_le_pathELength_of_endpoint_distance_eq_length
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {a b r s : ℝ} (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b)
    (hendpoint : riemannianEDist I (curve γ a) (curve γ b) =
      ‖v₀‖ₑ * ENNReal.ofReal (b - a))
    {η : ℝ → M} {u z : ℝ} (huz : u ≤ z)
    (hη : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 η (Icc u z))
    (hηu : η u = curve γ r) (hηz : η z = curve γ s) :
    ‖v₀‖ₑ * ENNReal.ofReal (s - r) ≤ pathELength I η u z := by
  rw [← riemannianEDist_eq_constant_speed_mul_of_endpoint_distance_eq_length
    (I := I) (M := M) γ hmetric har hrs hsb hendpoint]
  exact riemannianEDist_le_pathELength hη hηu hηz huz

/-- Thus the global ODE geodesic itself has path length exactly equal to the
intrinsic Riemannian distance on every subinterval of an endpoint-minimizing
segment. -/
theorem pathELength_eq_riemannianEDist_of_endpoint_distance_eq_length
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    {a b r s : ℝ} (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b)
    (hendpoint : riemannianEDist I (curve γ a) (curve γ b) =
      ‖v₀‖ₑ * ENNReal.ofReal (b - a)) :
    pathELength I (curve γ) r s = riemannianEDist I (curve γ r) (curve γ s) := by
  rw [pathELength_eq_constant_speed_mul (I := I) (M := M) γ hmetric]
  exact (riemannianEDist_eq_constant_speed_mul_of_endpoint_distance_eq_length
    (I := I) (M := M) γ hmetric har hrs hsb hendpoint).symm

end IntrinsicGeodesic.GlobalGeodesic
end BonnetMyersEntry
