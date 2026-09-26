/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.GramCertificateData

/-!
# The finite cover of second-child radii

Both second-child radii lie in `[barC - 1, 1]`.  Eight bands cover that interval, and every
ordered pair of bands is contained in the radius rectangle of one stored certificate, after
swapping the two sibling pairs when the blue band precedes the red one.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Lower endpoints of the eight radius bands. -/
def bandLower : Fin 8 → ℚ
  | 0 => 967 / 2500
  | 1 => 1 / 2
  | 2 => 3 / 5
  | 3 => 13 / 20
  | 4 => 7 / 10
  | 5 => 3 / 4
  | 6 => 4 / 5
  | 7 => 9 / 10

/-- Upper endpoints of the eight radius bands. -/
def bandUpper : Fin 8 → ℚ
  | 0 => 1 / 2
  | 1 => 3 / 5
  | 2 => 13 / 20
  | 3 => 7 / 10
  | 4 => 3 / 4
  | 5 => 4 / 5
  | 6 => 9 / 10
  | 7 => 1

/-- The certificate covering a given ordered pair of bands. -/
def bandCertificate : Fin 8 → Fin 8 → Fin 30
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 2
  | 0, 4 => 3
  | 0, 5 => 4
  | 0, 6 => 5
  | 0, 7 => 6
  | 1, 0 => 1
  | 1, 1 => 7
  | 1, 2 => 8
  | 1, 3 => 8
  | 1, 4 => 9
  | 1, 5 => 10
  | 1, 6 => 11
  | 1, 7 => 12
  | 2, 0 => 2
  | 2, 1 => 8
  | 2, 2 => 27
  | 2, 3 => 28
  | 2, 4 => 13
  | 2, 5 => 14
  | 2, 6 => 15
  | 2, 7 => 16
  | 3, 0 => 2
  | 3, 1 => 8
  | 3, 2 => 28
  | 3, 3 => 29
  | 3, 4 => 13
  | 3, 5 => 14
  | 3, 6 => 15
  | 3, 7 => 16
  | 4, 0 => 3
  | 4, 1 => 9
  | 4, 2 => 13
  | 4, 3 => 13
  | 4, 4 => 17
  | 4, 5 => 18
  | 4, 6 => 19
  | 4, 7 => 20
  | 5, 0 => 4
  | 5, 1 => 10
  | 5, 2 => 14
  | 5, 3 => 14
  | 5, 4 => 18
  | 5, 5 => 21
  | 5, 6 => 22
  | 5, 7 => 23
  | 6, 0 => 5
  | 6, 1 => 11
  | 6, 2 => 15
  | 6, 3 => 15
  | 6, 4 => 19
  | 6, 5 => 22
  | 6, 6 => 24
  | 6, 7 => 25
  | 7, 0 => 6
  | 7, 1 => 12
  | 7, 2 => 16
  | 7, 3 => 16
  | 7, 4 => 20
  | 7, 5 => 23
  | 7, 6 => 25
  | 7, 7 => 26

/-- Whether the covering certificate needs the two sibling pairs swapped. -/
def bandSwapped : Fin 8 → Fin 8 → Bool
  | 0, 0 => false
  | 0, 1 => false
  | 0, 2 => false
  | 0, 3 => false
  | 0, 4 => false
  | 0, 5 => false
  | 0, 6 => false
  | 0, 7 => false
  | 1, 0 => true
  | 1, 1 => false
  | 1, 2 => false
  | 1, 3 => false
  | 1, 4 => false
  | 1, 5 => false
  | 1, 6 => false
  | 1, 7 => false
  | 2, 0 => true
  | 2, 1 => true
  | 2, 2 => false
  | 2, 3 => false
  | 2, 4 => false
  | 2, 5 => false
  | 2, 6 => false
  | 2, 7 => false
  | 3, 0 => true
  | 3, 1 => true
  | 3, 2 => true
  | 3, 3 => false
  | 3, 4 => false
  | 3, 5 => false
  | 3, 6 => false
  | 3, 7 => false
  | 4, 0 => true
  | 4, 1 => true
  | 4, 2 => true
  | 4, 3 => true
  | 4, 4 => false
  | 4, 5 => false
  | 4, 6 => false
  | 4, 7 => false
  | 5, 0 => true
  | 5, 1 => true
  | 5, 2 => true
  | 5, 3 => true
  | 5, 4 => true
  | 5, 5 => false
  | 5, 6 => false
  | 5, 7 => false
  | 6, 0 => true
  | 6, 1 => true
  | 6, 2 => true
  | 6, 3 => true
  | 6, 4 => true
  | 6, 5 => true
  | 6, 6 => false
  | 6, 7 => false
  | 7, 0 => true
  | 7, 1 => true
  | 7, 2 => true
  | 7, 3 => true
  | 7, 4 => true
  | 7, 5 => true
  | 7, 6 => true
  | 7, 7 => false

/-- Every radius in range lies in one of the eight bands. -/
theorem exists_band (x : ℝ) (h0 : barC - 1 ≤ x) (h1 : x ≤ 1) :
    ∃ k : Fin 8, (bandLower k : ℝ) ≤ x ∧ x ≤ (bandUpper k : ℝ) := by
  have hb : (barC : ℝ) - 1 = 967 / 2500 := by norm_num [barC]
  rw [hb] at h0
  by_cases c0 : x ≤ 1 / 2
  · exact ⟨0, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c1 : x ≤ 3 / 5
  · exact ⟨1, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c2 : x ≤ 13 / 20
  · exact ⟨2, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c3 : x ≤ 7 / 10
  · exact ⟨3, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c4 : x ≤ 3 / 4
  · exact ⟨4, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c5 : x ≤ 4 / 5
  · exact ⟨5, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  by_cases c6 : x ≤ 9 / 10
  · exact ⟨6, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩
  · exact ⟨7, by norm_num [bandLower]; linarith, by norm_num [bandUpper]; linarith⟩

/-- The band pair is contained in the radius rectangle of its covering certificate. -/
theorem bandCertificate_contains (k l : Fin 8) :
    (if bandSwapped k l then
        (gramCertificates (bandCertificate k l)).pLower ≤ bandLower l ∧
          bandUpper l ≤ (gramCertificates (bandCertificate k l)).pUpper ∧
          (gramCertificates (bandCertificate k l)).wLower ≤ bandLower k ∧
          bandUpper k ≤ (gramCertificates (bandCertificate k l)).wUpper
      else
        (gramCertificates (bandCertificate k l)).pLower ≤ bandLower k ∧
          bandUpper k ≤ (gramCertificates (bandCertificate k l)).pUpper ∧
          (gramCertificates (bandCertificate k l)).wLower ≤ bandLower l ∧
          bandUpper l ≤ (gramCertificates (bandCertificate k l)).wUpper) := by
  fin_cases k <;> fin_cases l <;>
    norm_num [bandCertificate, bandSwapped, bandLower, bandUpper]

end LeanPool.Besicovitch
