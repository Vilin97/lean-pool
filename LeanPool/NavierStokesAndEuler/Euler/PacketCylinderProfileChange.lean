/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
public import LeanPool.NavierStokesAndEuler.Euler.PacketGradeAbsorption

@[expose] public section

/-! Comparison of the actual time profiles and absorption of a finite family at a fixed radius. -/

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerGevrey
open scoped ContDiff

def profileRatio {K : Type*} [TopologicalSpace K]
    (g b : C(K,ℝ)) (hb : ∀ t, 0 < b t) : C(K,ℝ) :=
  ⟨fun t => g t/b t,g.continuous.div b.continuous (fun t => (hb t).ne')⟩

@[simp] theorem profileRatio_apply {K : Type*} [TopologicalSpace K]
    (g b : C(K,ℝ)) (hb : ∀ t, 0 < b t) (t : K) : profileRatio g b hb t = g t/b t := rfl

theorem profileRatio_abs_le {K : Type*} [TopologicalSpace K]
    (g b : C(K,ℝ)) (hg : ∀ t, 0 ≤ g t) (hb : ∀ t, 0 < b t)
    (C : ℝ) (hC : ∀ t, g t ≤ C*b t) (t : K) : |profileRatio g b hb t| ≤ C := by
  rw [profileRatio_apply,abs_of_nonneg (div_nonneg (hg t) (hb t).le)]
  exact (div_le_iff₀ (hb t)).mpr (hC t)

namespace Field

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)
  (hT : 0 ≤ T) (g b : C(Icc (0 : ℝ) T,ℝ))
  (hg : ∀ t, 0 < g t) (hb : ∀ t, 0 < b t)

theorem normalized_changeProfile_path : (G.normalized hT b hb).path =
    ((G.normalized hT g hg).weighted hT (profileRatio g b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change profileRatio g b hb (projIcc 0 T hT t) •
      ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) =
        (b (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))
  rw [projIcc_of_mem hT t.property]
  simp only [profileRatio_apply,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hb t).ne']

variable {G g hg}

theorem WordBound.changeProfile {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ t, g t ≤ C*b t) :
    (G.normalized hT b hb).WordBound q R (C*A) d := by
  have hw := hG.weighted hT (profileRatio g b hb) C hC
    (profileRatio_abs_le g b (fun t => (hg t).le) hb C hgb)
  exact hw.of_path_eq _ (G.normalized_changeProfile_path hT g b hg hb)

theorem WordBound.enlargeProfile {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d) (hgb : ∀ t, g t ≤ b t) :
    (G.normalized hT b hb).WordBound q R A d := by
  have hh := hG.changeProfile hT b hb 1 zero_le_one (by simpa only [one_mul] using hgb)
  simpa only [one_mul] using hh

theorem wordBound_normalized_finset_absorb {ι : Type*} (s : Finset ι)
    (f : ι → VectorField) (W : ∀ i, Field P T (f i))
    (q : ℕ) (R C : ℝ) (d : ℕ) (shift : ι → ℕ)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hCR : C ≤ R) (hd : 0 < d)
    (hcount : s.card ≤ d^2) (hshift : ∀ i ∈ s, shift i < d)
    (hW : ∀ i ∈ s, ((W i).normalized hT b hb).WordBound q R C (shift i)) :
    ((Field.finsetSum s f W).normalized hT b hb).WordBound q R 1 d := by
  have hh := wordBound_finset_absorb s _ (fun i => (W i).normalized hT b hb)
    q R C d shift hR hC hCR hd hcount hshift hW
  exact hh.of_path_eq _ (normalized_finsetSum_path hT b hb s f W)

end Field
end EulerPacketCylinderField
