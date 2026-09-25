/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry

/-! # One Cube -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem cubeLpNorm_infty_descendant_le {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (f : Vec d → Vec d)
    (hf : MeasureTheory.MemLp f ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm R ∞ f ≤ cubeLpNorm Q ∞ f := by
  have hsmul_ne_zero :
      ENNReal.ofReal (cubeVolume Q / cubeVolume R) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 <|
      div_pos (cubeVolume_pos Q) (cubeVolume_pos R)
  have hle :
      MeasureTheory.eLpNorm f ∞ (normalizedCubeMeasure R) ≤
        MeasureTheory.eLpNorm f ∞ (normalizedCubeMeasure Q) := by
    calc
      MeasureTheory.eLpNorm f ∞ (normalizedCubeMeasure R)
          = MeasureTheory.eLpNorm f ∞
              ((normalizedCubeMeasure Q).restrict (cubeSet R)) := by
                rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
                simpa using
                  (MeasureTheory.eLpNorm_smul_measure_of_ne_zero hsmul_ne_zero f ∞
                    ((normalizedCubeMeasure Q).restrict (cubeSet R)))
      _ ≤ MeasureTheory.eLpNorm f ∞ (normalizedCubeMeasure Q) := by
            exact MeasureTheory.eLpNorm_mono_measure f MeasureTheory.Measure.restrict_le_self
  have htoReal := ENNReal.toReal_mono (ne_of_lt hf.2) hle
  simpa [cubeLpNorm] using htoReal

theorem cubeLpNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → E)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g p (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    cubeLpNorm Q p (fun x => f x + g x) ≤ cubeLpNorm Q p f + cubeLpNorm Q p g := by
  have hsum :
      MeasureTheory.eLpNorm (fun x => f x + g x) p (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) +
          MeasureTheory.eLpNorm g p (normalizedCubeMeasure Q) := by
    simpa using! MeasureTheory.eLpNorm_add_le hf.1 hg.1 hp
  have hsum_top :
      MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) +
        MeasureTheory.eLpNorm g p (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ne_of_lt hf.2, ne_of_lt hg.2⟩
  have htoReal :=
    ENNReal.toReal_mono hsum_top hsum
  rw [ENNReal.toReal_add (ne_of_lt hf.2) (ne_of_lt hg.2)] at htoReal
  simpa [cubeLpNorm, ne_of_lt hf.2, ne_of_lt hg.2] using htoReal

theorem cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => -cubeAverageVec Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (-cubeAverageVec Q u)
  have hadd :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverageVec Q u) := by
    have hfun :
        cubeFluctuationVec Q u = fun x => u x + (fun _ : Vec d => -cubeAverageVec Q u) x := by
      funext x
      simp [cubeFluctuationVec, sub_eq_add_neg]
    rw [hfun]
    exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) u (fun _ : Vec d => -cubeAverageVec Q u)
      hu hconst (by norm_num)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) u +
            cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverageVec Q u) := hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) u + ‖cubeAverageVec Q u‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞)) (c := -cubeAverageVec Q u) (by norm_num)]
          simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u + cubeLpNorm Q (2 : ℝ≥0∞) u := by
          gcongr
          exact norm_cubeAverageVec_le_cubeLpNorm_two Q u hu
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by ring

theorem cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two_sub_const {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (c : Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - c) := by
  have hu_sub :
      MeasureTheory.MemLp (fun x => u x - c) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const c)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)
        = cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => u x - c)) := by
            rw [cubeFluctuationVec_sub_const Q u c hu]
    _ ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - c) :=
          cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two Q (fun x => u x - c) hu_sub

theorem cubeLpNorm_two_smul_le_mul_cubeLpNorm_infty {d : ℕ} (Q : TriadicCube d)
    (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x • ξ x) ≤
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) v := by
  have hmul :
      MeasureTheory.eLpNorm (fun x => v x • ξ x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) *
          MeasureTheory.eLpNorm ξ ∞ (normalizedCubeMeasure Q) := by
    simpa using!
      (MeasureTheory.eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top
        (p := (2 : ℝ≥0∞)) (f := ξ) hv.1)
  have hmul_top :
      MeasureTheory.eLpNorm v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) *
        MeasureTheory.eLpNorm ξ ∞ (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top (ne_of_lt hv.2) (ne_of_lt hξ.2)
  have htoReal := ENNReal.toReal_mono hmul_top hmul
  simpa [cubeLpNorm, ne_of_lt hv.2, ne_of_lt hξ.2, mul_comm, mul_left_comm, mul_assoc] using htoReal

theorem norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    ‖cubeAverageVec Q (fun x => u x • ξ x)‖ ≤
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  calc
    ‖cubeAverageVec Q (fun x => u x • ξ x)‖
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x • ξ x) := by
            exact norm_cubeAverageVec_le_cubeLpNorm_two Q (fun x => u x • ξ x) <|
              by
                let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
                simpa using! hξ.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hu
    _ ≤ cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) u := by
          exact cubeLpNorm_two_smul_le_mul_cubeLpNorm_infty Q u ξ hu hξ

theorem cubeLpNorm_two_scalarFluctuation_smul_const_le {d : ℕ} (Q : TriadicCube d)
    (v : Vec d → ℝ) (c : Vec d)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => cubeFluctuation Q v x • c) ≤
      ‖c‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
  have hv_fluct :
      MeasureTheory.MemLp (cubeFluctuation Q v) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hv.sub (MeasureTheory.memLp_const (cubeAverage Q v))
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => c) ∞ (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const c
  have hmul :
      MeasureTheory.eLpNorm (fun x => cubeFluctuation Q v x • c) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) ≤
        MeasureTheory.eLpNorm (cubeFluctuation Q v) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) *
          MeasureTheory.eLpNorm (fun _ : Vec d => c) ∞ (normalizedCubeMeasure Q) := by
    simpa using!
      (MeasureTheory.eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top
        (p := (2 : ℝ≥0∞)) (f := fun _ : Vec d => c) hv_fluct.1)
  have hmul_top :
      MeasureTheory.eLpNorm (cubeFluctuation Q v) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) *
        MeasureTheory.eLpNorm (fun _ : Vec d => c) ∞ (normalizedCubeMeasure Q) ≠ ∞ :=
    ENNReal.mul_ne_top (ne_of_lt hv_fluct.2) (ne_of_lt hconst.2)
  have htoReal := ENNReal.toReal_mono hmul_top hmul
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => cubeFluctuation Q v x • c)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v) *
            cubeLpNorm Q ∞ (fun _ : Vec d => c) := by
              simpa [cubeLpNorm, ne_of_lt hv_fluct.2, ne_of_lt hconst.2,
                mul_comm, mul_left_comm, mul_assoc] using htoReal
    _ = cubeBesovOscillation Q (2 : ℝ≥0∞) v * ‖c‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (∞ : ℝ≥0∞)) (c := c) (by norm_num)]
          simp [cubeBesovOscillation]
    _ = ‖c‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) v := by ring

theorem cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_note_terms {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (ξ : Vec d → Vec d)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => v x • ξ x)) ≤
      2 * (cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) * cubeLpNorm Q (2 : ℝ≥0∞) v +
        cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  have hprod :
      MeasureTheory.MemLp (fun x => v x • ξ x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! hξ.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv
  have hξ_sub :
      MeasureTheory.MemLp (fun x => ξ x - cubeAverageVec Q ξ) ∞ (normalizedCubeMeasure Q) :=
    hξ.sub (MeasureTheory.memLp_const (cubeAverageVec Q ξ))
  have hfirst :
      MeasureTheory.MemLp (fun x => v x • (ξ x - cubeAverageVec Q ξ))
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! hξ_sub.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv
  have hv_fluct :
      MeasureTheory.MemLp (cubeFluctuation Q v) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hv.sub (MeasureTheory.memLp_const (cubeAverage Q v))
  have hsecond :
      MeasureTheory.MemLp (fun x => cubeFluctuation Q v x • cubeAverageVec Q ξ)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using!
      (MeasureTheory.memLp_const (cubeAverageVec Q ξ)).smul
        (p := (2 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv_fluct
  have hsplit :
      (fun x => v x • ξ x - cubeAverage Q v • cubeAverageVec Q ξ) =
        fun x => v x • (ξ x - cubeAverageVec Q ξ) +
          cubeFluctuation Q v x • cubeAverageVec Q ξ := by
    funext x
    ext i
    simp [cubeFluctuation, sub_eq_add_neg]
    ring
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => v x • ξ x))
        ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => v x • ξ x - cubeAverage Q v • cubeAverageVec Q ξ) := by
              exact cubeLpNorm_two_cubeFluctuationVec_le_two_mul_cubeLpNorm_two_sub_const
                Q (fun x => v x • ξ x) (cubeAverage Q v • cubeAverageVec Q ξ) hprod
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => v x • (ξ x - cubeAverageVec Q ξ) +
            cubeFluctuation Q v x • cubeAverageVec Q ξ) := by
          rw [hsplit]
    _ ≤ 2 * (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => v x • (ξ x - cubeAverageVec Q ξ)) +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => cubeFluctuation Q v x • cubeAverageVec Q ξ)) := by
          gcongr
          exact cubeLpNorm_add_le Q (2 : ℝ≥0∞)
            (fun x => v x • (ξ x - cubeAverageVec Q ξ))
            (fun x => cubeFluctuation Q v x • cubeAverageVec Q ξ)
            hfirst hsecond (by norm_num)
    _ ≤ 2 * (cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) * cubeLpNorm Q (2 : ℝ≥0∞) v +
          ‖cubeAverageVec Q ξ‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
          gcongr
          · exact cubeLpNorm_two_smul_le_mul_cubeLpNorm_infty Q v
              (fun x => ξ x - cubeAverageVec Q ξ) hv hξ_sub
          · exact cubeLpNorm_two_scalarFluctuation_smul_const_le Q v (cubeAverageVec Q ξ) hv
    _ ≤ 2 * (cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) * cubeLpNorm Q (2 : ℝ≥0∞) v +
          cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
          have hosc_nonneg : 0 ≤ cubeBesovOscillation Q (2 : ℝ≥0∞) v :=
            cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) v
          have hmul :
              ‖cubeAverageVec Q ξ‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) v ≤
                cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
            exact mul_le_mul_of_nonneg_right
              (norm_cubeAverageVec_le_cubeLpNorm_infty Q ξ hξ) hosc_nonneg
          have hadd :
              cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) *
                  cubeLpNorm Q (2 : ℝ≥0∞) v +
                ‖cubeAverageVec Q ξ‖ * cubeBesovOscillation Q (2 : ℝ≥0∞) v ≤
                cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) *
                    cubeLpNorm Q (2 : ℝ≥0∞) v +
                  cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v := by
            exact add_le_add le_rfl hmul
          exact mul_le_mul_of_nonneg_left hadd (by norm_num)

theorem cubeLpNorm_two_cubeFluctuationVec_centered_scalar_smul_le_note_terms {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (ξ : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞)
      (cubeFluctuationVec Q (fun x => (u x - cubeAverage Q u) • ξ x)) ≤
      2 * (cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u)) := by
  have hu_centered :
      MeasureTheory.MemLp (fun x => u x - cubeAverage Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  simpa using
    cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_note_terms
      Q (fun x => u x - cubeAverage Q u) ξ hu_centered hξ

theorem cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (v : Vec d → ℝ) (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => v x • ξ x)) ≤
      2 * ((cubeScaleFactor Q * B) * cubeLpNorm Q (2 : ℝ≥0∞) v +
        cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
  have hoscξ :
      cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) ≤ cubeScaleFactor Q * B :=
    cubeLpNorm_infty_sub_cubeAverageVec_le_cubeScaleFactor_mul_of_contDiff_component_bound
      Q hB hξLp hξ hderiv
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q (fun x => v x • ξ x))
        ≤ 2 * (cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) *
            cubeLpNorm Q (2 : ℝ≥0∞) v +
          cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
            exact cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_note_terms
              Q v ξ hv hξLp
    _ ≤ 2 * ((cubeScaleFactor Q * B) * cubeLpNorm Q (2 : ℝ≥0∞) v +
          cubeLpNorm Q ∞ ξ * cubeBesovOscillation Q (2 : ℝ≥0∞) v) := by
          have hv_nonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) v :=
            cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v
          have hmul :
              cubeLpNorm Q ∞ (fun x => ξ x - cubeAverageVec Q ξ) *
                  cubeLpNorm Q (2 : ℝ≥0∞) v ≤
                (cubeScaleFactor Q * B) * cubeLpNorm Q (2 : ℝ≥0∞) v := by
            exact mul_le_mul_of_nonneg_right hoscξ hv_nonneg
          exact mul_le_mul_of_nonneg_left (add_le_add hmul le_rfl) (by norm_num)

theorem cubeLpNorm_two_cubeFluctuationVec_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q, ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeLpNorm Q (2 : ℝ≥0∞)
      (cubeFluctuationVec Q (fun x => (u x - cubeAverage Q u) • ξ x)) ≤
      2 * ((cubeScaleFactor Q * B) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u) +
        cubeLpNorm Q ∞ ξ *
          cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u)) := by
  have hu_centered :
      MeasureTheory.MemLp (fun x => u x - cubeAverage Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  simpa using
    cubeLpNorm_two_cubeFluctuationVec_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q (fun x => u x - cubeAverage Q u) ξ hB hu_centered hξLp hξ hderiv


end

end Homogenization
