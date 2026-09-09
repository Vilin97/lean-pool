/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.Covariance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-!
# Smooth positive covariance solves

For an actual real two-by-two matrix and target, the signed areas in Cramer's
rule give an explicit strict cone. On that cone, the inverse solution and its
positive square roots depend smoothly on smooth input data. A compact family
has a uniform positive lower bound and a uniform tolerance for perturbing both
the matrix and the target.

No assertion here supplies smoothness or error estimates for the manuscript's
integrated columns. No assertion concerns extension through a zero-amplitude
edge, where the strict cone hypotheses fail.
-/

noncomputable section

namespace NavierStokes.SmoothCovariance

open Matrix Set
open scoped ContDiff Topology

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec2 := Fin 2 → ℝ

/- The entrywise sup norm makes all metric assertions below unambiguous. -/
local instance : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

local instance : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

abbrev Datum := Mat2 × Vec2

/-- Oriented areas obtained by replacing each column by the target. -/
def cramerNumerator (H : Mat2) (T : Vec2) : Vec2 :=
  ![T 0 * H 1 1 - H 0 1 * T 1, H 0 0 * T 1 - T 0 * H 1 0]

/-- Cramer's explicit formula, including Lean's total division convention. -/
def weights (H : Mat2) (T : Vec2) : Vec2 :=
  fun i => cramerNumerator H T i / H.det

/-- Both target-column oriented areas have the same nonzero orientation as
the two original columns. The definition uses only polynomial inequalities. -/
def StrictCone (H : Mat2) (T : Vec2) : Prop :=
  0 < cramerNumerator H T 0 * H.det ∧
  0 < cramerNumerator H T 1 * H.det

def amplitudes (H : Mat2) (T : Vec2) : Vec2 :=
  fun i => Real.sqrt (weights H T i)

theorem StrictCone.det_ne_zero {H : Mat2} {T : Vec2} (h : StrictCone H T) :
    H.det ≠ 0 :=
  (mul_ne_zero_iff.mp (ne_of_gt h.1)).2

theorem weights_pos_iff (H : Mat2) (T : Vec2) :
    (∀ i, 0 < weights H T i) ↔ StrictCone H T := by
  constructor
  · intro h
    exact ⟨mul_pos_iff.mpr (div_pos_iff.mp (h 0)),
      mul_pos_iff.mpr (div_pos_iff.mp (h 1))⟩
  · intro h i
    fin_cases i
    · exact div_pos_iff.mpr (mul_pos_iff.mp h.1)
    · exact div_pos_iff.mpr (mul_pos_iff.mp h.2)

theorem StrictCone.weights_pos {H : Mat2} {T : Vec2} (h : StrictCone H T) (i : Fin 2) :
    0 < weights H T i :=
  (weights_pos_iff H T).mpr h i

theorem reconstruct (H : Mat2) (T : Vec2) (hdet : H.det ≠ 0) :
    H.mulVec (weights H T) = T := by
  have hc : H.mulVec (cramerNumerator H T) = H.det • T := by
    ext i
    fin_cases i <;>
      simp [cramerNumerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.det_fin_two] <;> ring
  have hw : weights H T = H.det⁻¹ • cramerNumerator H T := by
    funext i
    simp only [weights, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hw, Matrix.mulVec_smul, hc, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem inverse_formula (H : Mat2) (T : Vec2) (hdet : H.det ≠ 0) :
    H⁻¹.mulVec T = weights H T := by
  calc
    H⁻¹.mulVec T = H⁻¹.mulVec (H.mulVec (weights H T)) := by
      rw [reconstruct H T hdet]
    _ = weights H T := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem StrictCone.amplitudes_pos {H : Mat2} {T : Vec2}
    (h : StrictCone H T) (i : Fin 2) : 0 < amplitudes H T i :=
  Real.sqrt_pos.mpr (h.weights_pos i)

theorem reconstruct_amplitudes {H : Mat2} {T : Vec2} (h : StrictCone H T) :
    H.mulVec (fun i => amplitudes H T i ^ 2) = T := by
  have hs : (fun i => amplitudes H T i ^ 2) = weights H T := by
    funext i
    exact Real.sq_sqrt (le_of_lt (h.weights_pos i))
  rw [hs]
  exact reconstruct H T h.det_ne_zero

/-- Agreement with the earlier exact signed-column formula. -/
theorem weights_signed_model {a b sm sp : ℝ} (m t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < sm) (hp : 0 < sp) :
    weights (Covariance.signedMatrix a b sm sp) (Covariance.target m t) =
      Covariance.coefficients a b sm sp m t := by
  rw [← inverse_formula _ _ (Covariance.determinant_ne_zero ha hb hm hp)]
  exact Covariance.inverse_formula m t ha hb hm hp

theorem signed_model_strictCone {a b sm sp m t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < sm) (hp : 0 < sp)
    (hcone : |a * t| < b * m) :
    StrictCone (Covariance.signedMatrix a b sm sp) (Covariance.target m t) := by
  apply (weights_pos_iff _ _).mp
  rw [weights_signed_model m t ha hb hm hp]
  exact Covariance.coefficients_pos ha hb hm hp hcone

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E} {H : E → Mat2} {T : E → Vec2}

theorem contDiffOn_determinant
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s) :
    ContDiffOn ℝ ∞ (fun x => (H x).det) s := by
  simpa only [Pi.mul_apply, Pi.sub_apply, Matrix.det_fin_two] using
    ((hH 0 0).mul (hH 1 1)).sub ((hH 0 1).mul (hH 1 0))

theorem contDiffOn_numerator
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => cramerNumerator (H x) (T x) i) s := by
  fin_cases i
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hT 0).mul (hH 1 1)).sub ((hH 0
    1).mul (hT 1))
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hH 0 0).mul (hT 1)).sub ((hT 0).mul
    (hH 1 0))

/-- Smoothness requires a nonvanishing determinant, independently of positivity. -/
theorem contDiffOn_weights
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (H x).det ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => weights (H x) (T x) i) s :=
  (contDiffOn_numerator hH hT i).div (contDiffOn_determinant hH) hdet

theorem contDiffOn_inverse_solution
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (H x).det ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => (H x)⁻¹.mulVec (T x) i) s := by
  apply (contDiffOn_weights hH hT hdet i).congr
  intro x hx
  exact congrFun (inverse_formula (H x) (T x) (hdet x hx)) i

/-- Positive square-root amplitudes are smooth on the strict cone. -/
theorem contDiffOn_amplitudes
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, StrictCone (H x) (T x)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => amplitudes (H x) (T x) i) s :=
  (contDiffOn_weights hH hT (fun x hx => (hcone x hx).det_ne_zero) i).sqrt
    (fun x hx => ne_of_gt ((hcone x hx).weights_pos i))

/-- The complete amplitude vector, not only its coordinates, is smooth. -/
theorem contDiffOn_amplitude_vector
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, StrictCone (H x) (T x)) :
    ContDiffOn ℝ ∞ (fun x => amplitudes (H x) (T x)) s :=
  contDiffOn_pi.mpr (contDiffOn_amplitudes hH hT hcone)

/-- Smooth dependence of the coefficients as named in the original exact
signed-slot module. All six scalar input functions are genuinely smooth. -/
theorem contDiffOn_signed_coefficients {a b sm sp m t : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s)
    (hsm : ContDiffOn ℝ ∞ sm s) (hsp : ContDiffOn ℝ ∞ sp s)
    (hm : ContDiffOn ℝ ∞ m s) (ht : ContDiffOn ℝ ∞ t s)
    (hpos : ∀ x ∈ s, 0 < a x ∧ 0 < b x ∧ 0 < sm x ∧ 0 < sp x)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun x => Covariance.coefficients (a x) (b x) (sm x) (sp x) (m x) (t x) i) s := by
  fin_cases i
  · change ContDiffOn ℝ ∞
      (fun x => (b x * m x - a x * t x) / (2 * a x * b x * sm x)) s
    apply ((hb.mul hm).sub (ha.mul ht)).div
      (((contDiffOn_const.mul ha).mul hb).mul hsm)
    intro x hx
    rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
    exact ne_of_gt (by positivity)
  · change ContDiffOn ℝ ∞
      (fun x => (b x * m x + a x * t x) / (2 * a x * b x * sp x)) s
    apply ((hb.mul hm).add (ha.mul ht)).div
      (((contDiffOn_const.mul ha).mul hb).mul hsp)
    intro x hx
    rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
    exact ne_of_gt (by positivity)

theorem contDiffOn_signed_amplitudes {a b sm sp m t : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s)
    (hsm : ContDiffOn ℝ ∞ sm s) (hsp : ContDiffOn ℝ ∞ sp s)
    (hm : ContDiffOn ℝ ∞ m s) (ht : ContDiffOn ℝ ∞ t s)
    (hpos : ∀ x ∈ s, 0 < a x ∧ 0 < b x ∧ 0 < sm x ∧ 0 < sp x)
    (hcone : ∀ x ∈ s, |a x * t x| < b x * m x) (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun x => Covariance.amplitudes (a x) (b x) (sm x) (sp x) (m x) (t x) i) s := by
  apply (contDiffOn_signed_coefficients ha hb hsm hsp hm ht hpos i).sqrt
  intro x hx
  rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
  exact ne_of_gt (Covariance.coefficients_pos hap hbp hsmp hspp (hcone x hx) i)

end Smooth

section Compact

variable {X : Type*} [TopologicalSpace X]
variable {K : Set X} {H : X → Mat2} {T : X → Vec2}

theorem continuousOn_determinant
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K) :
    ContinuousOn (fun x => (H x).det) K := by
  simpa only [Pi.mul_apply, Pi.sub_apply, Matrix.det_fin_two] using
    ((hH 0 0).fun_mul (hH 1 1)).fun_sub ((hH 0 1).fun_mul (hH 1 0))

theorem continuousOn_numerator
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K) (i : Fin 2) :
    ContinuousOn (fun x => cramerNumerator (H x) (T x) i) K := by
  fin_cases i
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hT 0).fun_mul (hH 1 1)).fun_sub
    ((hH 0 1).fun_mul (hT 1))
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hH 0 0).fun_mul (hT 1)).fun_sub
    ((hT 0).fun_mul (hH 1 0))

theorem continuousOn_weights
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hdet : ∀ x ∈ K, (H x).det ≠ 0) (i : Fin 2) :
    ContinuousOn (fun x => weights (H x) (T x) i) K :=
  (continuousOn_numerator hH hT i).div (continuousOn_determinant hH) hdet

/-- Compactness supplies an actual common lower bound for the determinant
magnitude and both solution coordinates, including an empty parameter set. -/
theorem compact_uniform_positive (hK : IsCompact K)
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ |(H x).det| ∧ ∀ i, δ ≤ weights (H x) (T x) i := by
  have hw := continuousOn_weights hH hT (fun x hx => (hcone x hx).det_ne_zero)
  let margin : X → ℝ := fun x => min |(H x).det|
    (min (weights (H x) (T x) 0) (weights (H x) (T x) 1))
  have hm : ContinuousOn margin K :=
    continuous_min.comp_continuousOn ((continuousOn_determinant hH).abs.prodMk
      (continuous_min.comp_continuousOn ((hw 0).prodMk (hw 1))))
  have hmp : ∀ x ∈ K, 0 < margin x := by
    intro x hx
    exact lt_min (abs_pos.mpr ((hcone x hx).det_ne_zero))
      (lt_min ((hcone x hx).weights_pos 0) ((hcone x hx).weights_pos 1))
  obtain ⟨δ, hδ, hbound⟩ := hK.exists_forall_le' hm hmp
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  refine ⟨(hbound x hx).trans (min_le_left _ _), ?_⟩
  intro i
  fin_cases i
  · exact (hbound x hx).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (hbound x hx).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The same compact family keeps every positive amplitude uniformly away
from zero; no claim is made for a family touching a zero-stress edge. -/
theorem compact_uniform_amplitudes (hK : IsCompact K)
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ |(H x).det| ∧ ∀ i,
        δ ≤ weights (H x) (T x) i ∧ δ ≤ amplitudes (H x) (T x) i := by
  obtain ⟨δ, hδ, hbound⟩ := compact_uniform_positive hK hH hT hcone
  refine ⟨min δ (Real.sqrt δ), lt_min hδ (Real.sqrt_pos.mpr hδ), ?_⟩
  intro x hx
  refine ⟨(min_le_left _ _).trans (hbound x hx).1, ?_⟩
  intro i
  exact ⟨(min_le_left _ _).trans ((hbound x hx).2 i),
    (min_le_right _ _).trans (Real.sqrt_le_sqrt ((hbound x hx).2 i))⟩

end Compact

/-- The strict area inequalities define an open set of matrix-target pairs. -/
def strictConeRegion : Set Datum := {z | StrictCone z.1 z.2}

theorem isOpen_strictConeRegion : IsOpen strictConeRegion := by
  have hH : ∀ i j, Continuous (fun z : Datum => z.1 i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hT : ∀ i, Continuous (fun z : Datum => z.2 i) := fun i =>
    (continuous_apply i).comp continuous_snd
  have hd : Continuous (fun z : Datum => z.1.det) := by
    exact continuousOn_univ.mp
      (continuousOn_determinant (fun i j => (hH i j).continuousOn))
  have hn : ∀ i, Continuous (fun z : Datum => cramerNumerator z.1 z.2 i) := by
    intro i
    exact continuousOn_univ.mp (continuousOn_numerator
      (fun i j => (hH i j).continuousOn) (fun i => (hT i).continuousOn) i)
  exact (isOpen_lt continuous_const ((hn 0).fun_mul hd)).inter
    (isOpen_lt continuous_const ((hn 1).fun_mul hd))

/-- The solution map itself is C-infinity on the open set of admissible
matrix-target data, without a prechosen parameterization. -/
theorem contDiffOn_universal_weights :
    ContDiffOn ℝ ∞ (fun z : Datum => weights z.1 z.2) strictConeRegion := by
  apply contDiffOn_pi.mpr
  apply contDiffOn_weights
  · intro i j
    exact ((contDiff_apply_apply ℝ ℝ i j).comp contDiff_fst).contDiffOn
  · intro i
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn
  · intro z hz
    exact StrictCone.det_ne_zero hz

/-- The positive square-root solution is C-infinity on that same open set. -/
theorem contDiffOn_universal_amplitudes :
    ContDiffOn ℝ ∞ (fun z : Datum => amplitudes z.1 z.2) strictConeRegion := by
  apply contDiffOn_amplitude_vector
  · intro i j
    exact ((contDiff_apply_apply ℝ ℝ i j).comp contDiff_fst).contDiffOn
  · intro i
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn
  · intro z hz
    exact hz

/-- A single positive perturbation radius works for every datum in a compact
subset of the strict cone. The perturbed data may be arbitrary actual matrices. -/
theorem compact_perturbation_stability {S : Set Datum} (hS : IsCompact S)
    (hcone : S ⊆ strictConeRegion) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ S, ∀ z' : Datum,
      dist z' z ≤ ρ → StrictCone z'.1 z'.2 := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hS.exists_cthickening_subset_open isOpen_strictConeRegion hcone
  exact ⟨ρ, hρ, fun z hz z' hdist =>
    hsub (Metric.mem_cthickening_of_dist_le z' z ρ S hz hdist)⟩

/-- Uniform perturbation stability for a continuous family on a compact
parameter set. Competing matrices need not form a continuous family. -/
theorem compact_family_perturbation_stability
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {H : X → Mat2} {T : X → Vec2}
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ H' : Mat2, ∀ T' : Vec2,
      dist (H', T') (H x, T x) ≤ ρ →
        H'.det ≠ 0 ∧ (∀ i, 0 < weights H' T' i) ∧
          (∀ i, 0 < amplitudes H' T' i) := by
  let f : X → Datum := fun x => (H x, T x)
  have hf : ContinuousOn f K :=
    (continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (hH i))).prodMk
      (continuousOn_pi.mpr hT)
  have himage : f '' K ⊆ strictConeRegion := by
    rintro z ⟨x, hx, rfl⟩
    exact hcone x hx
  obtain ⟨ρ, hρ, hstable⟩ :=
    compact_perturbation_stability (hK.image_of_continuousOn hf) himage
  refine ⟨ρ, hρ, ?_⟩
  intro x hx H' T' hdist
  have hc := hstable (f x) (mem_image_of_mem f hx) (H', T') hdist
  exact ⟨hc.det_ne_zero, hc.weights_pos, hc.amplitudes_pos⟩

end NavierStokes.SmoothCovariance
