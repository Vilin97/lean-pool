/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketKnownDecomposition
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderAngularRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPrefixLocality

@[expose] public section

/-! Genuine cylinder-path witnesses for each of the fifteen known-force families. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

def PrefixFields.termField (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {corrector_t : VectorField}
    (Ct : Field P T corrector_t)
    (hCt : TimeDerivative hT.le (F.corrector (p-1) (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a (p-1)).highPressure))
    (k : KnownTerm) (i j : ℕ) : Field P T (k.raw O p a i j) := by
  cases k with
  | previousLinear =>
    by_cases h : i=0 ∧ j=0
    · exact (Field.linearPart C.strain (F.corrector (p-1) (by omega)) Ct hT hCt
        O.interval C.interval_eq).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | previousPressure =>
    by_cases h : i=0 ∧ j=0
    · exact (Field.slowPressure C.inverse (a (p-1)).highPressure pressure).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | slow l r =>
    by_cases h : i+j=p
    · exact (SpatialJetField.slowAdvection C.inverse (F.pieceJet O l i) (F.pieceJet O r j)).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | fastMeanHigh =>
    by_cases h : i+j=p+1
    · exact (SpatialJetField.fastAdvection C.normal (F.pieceJet O .mean i) (F.pieceJet O .high
      j)).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | fastMeanCorrector =>
    by_cases h : i+j=p+1
    · exact (SpatialJetField.fastAdvection C.normal (F.pieceJet O .mean i) (F.pieceJet O .corrector
      j)).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | fastCorrectorHigh =>
    by_cases h : i+j=p+1
    · exact (SpatialJetField.fastAdvection C.normal (F.pieceJet O .corrector i) (F.pieceJet O .high
      j)).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])
  | fastCorrectorCorrector =>
    by_cases h : i+j=p+1
    · exact (SpatialJetField.fastAdvection C.normal (F.pieceJet O .corrector i) (F.pieceJet O
      .corrector j)).congr
        (fun _ _ _ => by simp [KnownTerm.raw, h])
    · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.raw, h])

theorem KnownTerm.integral_zero_of_zeroMean (F : PrefixFields P T p a)
    (C : CoefficientData P T O)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))
    (k : KnownTerm) (hk : k.zeroMean = true) (i j : ℕ)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (∫ θ in (0 : ℝ)..P, k.raw O p a i j (t,(x,θ))) = 0 := by
  cases k <;> simp only [KnownTerm.zeroMean, Bool.false_eq_true] at hk
  · by_cases h : i+j=p+1
    · simpa only [KnownTerm.raw, h, ite_true, KnownPiece.jet] using
        mean_primary_integral_zero C.normal (F.piece .high j) O.interval
          (KnownPiece.mean_angle hB i) t x
    · simp only [KnownTerm.raw, h, ite_false, intervalIntegral.integral_zero]
  · by_cases h : i+j=p+1
    · simpa only [KnownTerm.raw, h, ite_true, KnownPiece.jet] using
        mean_primary_integral_zero C.normal (F.piece .corrector j) O.interval
          (KnownPiece.mean_angle hB i) t x
    · simp only [KnownTerm.raw, h, ite_false, intervalIntegral.integral_zero]

theorem KnownTerm.angleIndependent_of_meanOnly (F : PrefixFields P T p a)
    (C : CoefficientData P T O)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))
    (k : KnownTerm) (hk : k.meanOnly = true) (i j : ℕ)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    k.raw O p a i j (t,(x,θ)) = k.raw O p a i j (t,(x,0)) := by
  cases k with
  | slow l r =>
    cases l <;> cases r <;> simp only [KnownTerm.meanOnly, Bool.false_eq_true] at hk
    by_cases h : i+j=p
    · have hA : ∀ s : ℝ, O.inverseFrame (t,(x,s)) = O.inverseFrame (t,(x,0)) := by
        intro s
        rw [C.inverse.raw_eq,C.inverse.raw_eq]
      simpa only [KnownTerm.raw, h, ite_true] using
        (F.meanPiece_angleIndependent hB i t x).slowAdvection
          (F.meanPiece_angleIndependent hB j t x) (fun s => O.inverseFrame (t,(x,s))) hA θ
    · simp [KnownTerm.raw, h]
  | _ => simp only [KnownTerm.meanOnly, Bool.false_eq_true] at hk

theorem angleMean_eq_of_angleIndependent {raw : VectorField}
    (t : ℝ) (x : Space) (h : ∀ θ : ℝ, raw (t,(x,θ)) = raw (t,(x,0))) (θ : ℝ) :
    angleMean P raw (t,(x,θ)) = raw (t,(x,θ)) := by
  have he : (fun s : ℝ => raw (t,(x,s))) = fun _ => raw (t,(x,0)) := funext h
  unfold angleMean
  rw [he, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (Fact.out : 0 < P)), one_smul]
  exact (h θ).symm

namespace KnownTerm

def meanRaw (k : KnownTerm) (O : Operators) (p : ℕ) (a : ℕ → Profile) (i j : ℕ) : VectorField :=
  if k.zeroMean then 0 else angleMean O.period (k.raw O p a i j)

def highRaw (k : KnownTerm) (O : Operators) (p : ℕ) (a : ℕ → Profile) (i j : ℕ) : VectorField :=
  if k.meanOnly then 0 else if k.zeroMean then k.raw O p a i j else
    k.raw O p a i j-angleMean O.period (k.raw O p a i j)

theorem meanRaw_eq (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))
    (k : KnownTerm) (i j : ℕ) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    k.meanRaw O p a i j (t,(x,θ)) = angleMean O.period (k.raw O p a i j) (t,(x,θ)) := by
  by_cases hk : k.zeroMean = true
  · simp only [meanRaw, ite_eq_left hk, Pi.zero_apply, angleMean, C.period_eq,
      integral_zero_of_zeroMean F C hB k hk i j t x, smul_zero]
  · simp only [meanRaw, ite_eq_right hk]

theorem highRaw_eq (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hB : ∀ i, i < p → ∀ (t : Icc (0 : ℝ) T) x θ,
      (a i).mean (t,(x,θ)) = (a i).mean (t,(x,0)))
    (k : KnownTerm) (i j : ℕ) (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    k.highRaw O p a i j (t,(x,θ)) =
      k.raw O p a i j (t,(x,θ))-angleMean O.period (k.raw O p a i j) (t,(x,θ)) := by
  by_cases hm : k.meanOnly = true
  · simp only [highRaw, ite_eq_left hm, Pi.zero_apply, C.period_eq]
    rw [angleMean_eq_of_angleIndependent (t : ℝ) x (angleIndependent_of_meanOnly F C hB k hm i j t
      x), sub_self]
  · by_cases hz : k.zeroMean = true
    · simp only [highRaw, ite_eq_right hm, ite_eq_left hz, angleMean, C.period_eq,
        integral_zero_of_zeroMean F C hB k hz i j t x, smul_zero, sub_zero]
    · simp only [highRaw, ite_eq_right hm, ite_eq_right hz, Pi.sub_apply]

end KnownTerm

def PrefixFields.meanTermField (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {corrector_t : VectorField}
    (Ct : Field P T corrector_t)
    (hCt : TimeDerivative hT.le (F.corrector (p-1) (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a (p-1)).highPressure))
    (k : KnownTerm) (i j : ℕ) : Field P T (k.meanRaw O p a i j) := by
  by_cases h : k.zeroMean = true
  · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.meanRaw, h])
  · exact (F.termField C hp hT Ct hCt pressure k i j).angleMean.congr
      (fun _ _ _ => by simp [KnownTerm.meanRaw, h, C.period_eq])

def PrefixFields.highTermField (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {corrector_t : VectorField}
    (Ct : Field P T corrector_t)
    (hCt : TimeDerivative hT.le (F.corrector (p-1) (by omega)) Ct)
    (pressure : Field P T (pressureGradient (a (p-1)).highPressure))
    (k : KnownTerm) (i j : ℕ) : Field P T (k.highRaw O p a i j) := by
  by_cases hm : k.meanOnly = true
  · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.highRaw, hm])
  · by_cases hz : k.zeroMean = true
    · exact (F.termField C hp hT Ct hCt pressure k i j).congr
        (fun _ _ _ => by simp [KnownTerm.highRaw, hm, hz])
    · exact (F.termField C hp hT Ct hCt pressure k i j).highPart.congr
        (fun _ _ _ => by simp [KnownTerm.highRaw, hm, hz, C.period_eq])

end EulerPacketCylinderField
