/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch022`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells9faa13f35d

/-- Subcell `0010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `0011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0010)))

/-- Subcell `00102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0010)))

/-- Subcell `00103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0010)))

/-- Subcell `00103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0010)))

/-- Subcell `00112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0011)))

/-- Subcell `00112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0011)))

/-- Subcell `00113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0011)))

/-- Subcell `00113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0011)))

/-- Subcell `00113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0011)))

end GerverSofa.PartE.CertificateCells9faa13f35d

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatch3b6d17fd8ecf6129`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9faa13f35d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9faa13f35d

open CertificateCells9faa13f35d
theorem e24KC2ThetaAboveLeaf0010221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102211))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102211))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102211))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102211))) h)
theorem e24KC2ThetaAboveLeaf0010221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102212))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102212))) h)
theorem e24KC2ThetaAboveLeaf0010221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102212))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102212))) h)
theorem e24KC2ThetaAboveLeaf0010221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102212))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102212))) h)
theorem e24KC2ThetaAboveLeaf0010221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102212))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102212))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102212))) h)
theorem e24KC2ThetaAboveLeaf0010221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102213))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102213))) h)
theorem e24KC2ThetaAboveLeaf0010221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102213))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102213))) h)
theorem e24KC2ThetaAboveLeaf0010221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102213))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102213))) h)
theorem e24KC2ThetaAboveLeaf0010221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102213))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102213))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102213))) h)
theorem e24KC2ThetaAboveLeaf0010230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102300))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102300))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102300))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102300))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102300))) h)
theorem e24KC2ThetaAboveLeaf0010230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102301))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102301))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102301))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102301))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102301))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102301))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102301))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102301))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102301))) h)
theorem e24KC2ThetaAboveLeaf0010230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102302))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102302))) h)
theorem e24KC2ThetaAboveLeaf0010230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102302))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102302))) h)
theorem e24KC2ThetaAboveLeaf0010230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102302))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102302))) h)
theorem e24KC2ThetaAboveLeaf0010230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102302))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102302))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102302))) h)
theorem e24KC2ThetaAboveLeaf0010230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102303))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102303))) h)
theorem e24KC2ThetaAboveLeaf0010230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102303))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102303))) h)
theorem e24KC2ThetaAboveLeaf0010230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102303))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102303))) h)
theorem e24KC2ThetaAboveLeaf0010230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102303))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102303))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102303))) h)
theorem e24KC2ThetaAboveLeaf0010231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102310))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102310))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102310))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102310))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102310))) h)
theorem e24KC2ThetaAboveLeaf0010231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00102311))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00102311))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00102311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00102311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00102311))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00102311))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00102311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00102311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00102311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00102311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00102311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00102311))) h)
theorem e24KC2ThetaAboveLeaf0010231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102312))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102312))) h)
theorem e24KC2ThetaAboveLeaf0010231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102312))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102312))) h)
theorem e24KC2ThetaAboveLeaf0010231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102312))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102312))) h)
theorem e24KC2ThetaAboveLeaf0010231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102312))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102312))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102312))) h)
theorem e24KC2ThetaAboveLeaf0010231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00102313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00102313))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00102313))) h)
theorem e24KC2ThetaAboveLeaf0010231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00102313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00102313))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00102313))) h)
theorem e24KC2ThetaAboveLeaf0010231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00102313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00102313))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00102313))) h)
theorem e24KC2ThetaAboveLeaf0010231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00102313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00102313))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00102313))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00102313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00102313))) h)
theorem e24KC2ThetaAboveLeaf0010320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103200))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103200))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103200))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103200))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103200))) h)
theorem e24KC2ThetaAboveLeaf0010320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103201))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103201))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103201))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103201))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103201))) h)
theorem e24KC2ThetaAboveLeaf0010320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103202))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103202))) h)
theorem e24KC2ThetaAboveLeaf0010320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103202))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103202))) h)
theorem e24KC2ThetaAboveLeaf0010320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103202))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103202))) h)
theorem e24KC2ThetaAboveLeaf0010320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103202))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103202))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103202))) h)
theorem e24KC2ThetaAboveLeaf0010320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103203))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103203))) h)
theorem e24KC2ThetaAboveLeaf0010320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103203))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103203))) h)
theorem e24KC2ThetaAboveLeaf0010320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103203))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103203))) h)
theorem e24KC2ThetaAboveLeaf0010320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103203))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103203))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103203))) h)
theorem e24KC2ThetaAboveLeaf0010321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103210))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103210))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103210))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103210))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103210))) h)
theorem e24KC2ThetaAboveLeaf0010321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103211))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103211))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103211))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103211))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103211))) h)
theorem e24KC2ThetaAboveLeaf0010321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103212))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103212))) h)
theorem e24KC2ThetaAboveLeaf0010321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103212))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103212))) h)
theorem e24KC2ThetaAboveLeaf0010321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103212))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103212))) h)
theorem e24KC2ThetaAboveLeaf0010321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103212))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103212))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103212))) h)
theorem e24KC2ThetaAboveLeaf0010321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103213))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103213))) h)
theorem e24KC2ThetaAboveLeaf0010321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103213))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103213))) h)
theorem e24KC2ThetaAboveLeaf0010321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103213))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103213))) h)
theorem e24KC2ThetaAboveLeaf0010321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103213))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103213))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103213))) h)
theorem e24KC2ThetaAboveLeaf0010330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103300))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103300))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103300))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103300))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103300))) h)
theorem e24KC2ThetaAboveLeaf0010330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103301))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103301))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103301))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103301))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103301))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103301))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103301))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103301))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103301))) h)
theorem e24KC2ThetaAboveLeaf0010330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103302))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103302))) h)
theorem e24KC2ThetaAboveLeaf0010330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103302))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103302))) h)
theorem e24KC2ThetaAboveLeaf0010330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103302))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103302))) h)
theorem e24KC2ThetaAboveLeaf0010330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103302))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103302))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103302))) h)
theorem e24KC2ThetaAboveLeaf0010330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103303))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103303))) h)
theorem e24KC2ThetaAboveLeaf0010330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103303))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103303))) h)
theorem e24KC2ThetaAboveLeaf0010330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103303))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103303))) h)
theorem e24KC2ThetaAboveLeaf0010330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103303))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103303))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103303))) h)
theorem e24KC2ThetaAboveLeaf0010331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103310))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103310))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103310))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103310))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103310))) h)
theorem e24KC2ThetaAboveLeaf0010331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00103311))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00103311))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00103311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00103311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00103311))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00103311))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00103311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00103311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00103311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00103311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00103311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00103311))) h)
theorem e24KC2ThetaAboveLeaf0010331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103312))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103312))) h)
theorem e24KC2ThetaAboveLeaf0010331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103312))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103312))) h)
theorem e24KC2ThetaAboveLeaf0010331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103312))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103312))) h)
theorem e24KC2ThetaAboveLeaf0010331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103312))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103312))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103312))) h)
theorem e24KC2ThetaAboveLeaf0010331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00103313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00103313))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00103313))) h)
theorem e24KC2ThetaAboveLeaf0010331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00103313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00103313))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00103313))) h)
theorem e24KC2ThetaAboveLeaf0010331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00103313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00103313))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00103313))) h)
theorem e24KC2ThetaAboveLeaf0010331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00103313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00103313))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00103313))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00103313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00103313))) h)
theorem e24KC2ThetaAboveLeaf0011220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112200))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112200))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112200))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112200))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112200))) h)
theorem e24KC2ThetaAboveLeaf0011220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112201))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112201))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112201))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112201))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112201))) h)
theorem e24KC2ThetaAboveLeaf0011220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112202))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112202))) h)
theorem e24KC2ThetaAboveLeaf0011220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112202))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112202))) h)
theorem e24KC2ThetaAboveLeaf0011220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112202))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112202))) h)
theorem e24KC2ThetaAboveLeaf0011220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112202))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112202))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112202))) h)
theorem e24KC2ThetaAboveLeaf0011220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112203))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112203))) h)
theorem e24KC2ThetaAboveLeaf0011220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112203))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112203))) h)
theorem e24KC2ThetaAboveLeaf0011220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112203))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112203))) h)
theorem e24KC2ThetaAboveLeaf0011220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112203))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112203))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112203))) h)
theorem e24KC2ThetaAboveLeaf0011221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112210))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112210))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112210))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112210))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112210))) h)
theorem e24KC2ThetaAboveLeaf0011221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112211))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112211))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112211))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112211))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112211))) h)
theorem e24KC2ThetaAboveLeaf0011221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112212))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112212))) h)
theorem e24KC2ThetaAboveLeaf0011221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112212))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112212))) h)
theorem e24KC2ThetaAboveLeaf0011221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112212))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112212))) h)
theorem e24KC2ThetaAboveLeaf0011221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112212))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112212))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112212))) h)
theorem e24KC2ThetaAboveLeaf0011221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112213))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112213))) h)
theorem e24KC2ThetaAboveLeaf0011221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112213))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112213))) h)
theorem e24KC2ThetaAboveLeaf0011221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112213))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112213))) h)
theorem e24KC2ThetaAboveLeaf0011221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112213))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112213))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112213))) h)
theorem e24KC2ThetaAboveLeaf0011230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112300))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112300))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112300))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112300))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112300))) h)
theorem e24KC2ThetaAboveLeaf0011230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112301))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112301))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112301))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112301))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112301))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112301))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112301))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112301))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112301))) h)
theorem e24KC2ThetaAboveLeaf0011230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112302))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112302))) h)
theorem e24KC2ThetaAboveLeaf0011230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112302))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112302))) h)
theorem e24KC2ThetaAboveLeaf0011230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112302))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112302))) h)
theorem e24KC2ThetaAboveLeaf0011230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112302))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112302))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112302))) h)
theorem e24KC2ThetaAboveLeaf0011230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112303))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112303))) h)
theorem e24KC2ThetaAboveLeaf0011230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112303))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112303))) h)
theorem e24KC2ThetaAboveLeaf0011230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112303))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112303))) h)
theorem e24KC2ThetaAboveLeaf0011230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112303))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112303))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112303))) h)
theorem e24KC2ThetaAboveLeaf0011231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112310))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00112310))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childLH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childLH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHL
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00112310))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childLL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childLL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHH
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00112310))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childLH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childLH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childHH
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112310))) h)
theorem e24KC2ThetaAboveLeaf0011231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00112311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00112311))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHL (childLL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHH (childLL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childHL
        thetaAboveCell00112311))) h)
theorem e24KC2ThetaAboveLeaf0011231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00112311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00112311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00112311))) h)
theorem e24KC2ThetaAboveLeaf0011231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00112311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00112311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00112311))) h)
theorem e24KC2ThetaAboveLeaf0011231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00112311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00112311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00112311))) h)
theorem e24KC2ThetaAboveLeaf0011231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00112311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00112311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00112311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00112311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00112311))) h)
theorem e24KC2ThetaAboveLeaf0011231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112312))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112312))) h)
theorem e24KC2ThetaAboveLeaf0011231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112312))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112312))) h)
theorem e24KC2ThetaAboveLeaf0011231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112312))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112312))) h)
theorem e24KC2ThetaAboveLeaf0011231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112312)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112312))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112312))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112312)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112312))) h)
theorem e24KC2ThetaAboveLeaf0011231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00112313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00112313))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00112313))) h)
theorem e24KC2ThetaAboveLeaf0011231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00112313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00112313))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00112313))) h)
theorem e24KC2ThetaAboveLeaf0011231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00112313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00112313))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00112313))) h)
theorem e24KC2ThetaAboveLeaf0011231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00112313)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00112313))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00112313))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00112313)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00112313))) h)
theorem e24KC2ThetaAboveLeaf0011320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113200))) h)
theorem e24KC2ThetaAboveLeaf0011320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113200))) h)
theorem e24KC2ThetaAboveLeaf0011320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113200))) h)
theorem e24KC2ThetaAboveLeaf0011320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113200))) h)
theorem e24KC2ThetaAboveLeaf0011320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113201))) h)
theorem e24KC2ThetaAboveLeaf0011320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113201))) h)
theorem e24KC2ThetaAboveLeaf0011320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113201))) h)
theorem e24KC2ThetaAboveLeaf0011320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113201))) h)
theorem e24KC2ThetaAboveLeaf0011320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113202))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113202))) h)
theorem e24KC2ThetaAboveLeaf0011320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113202))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113202))) h)
theorem e24KC2ThetaAboveLeaf0011320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113202))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113202))) h)
theorem e24KC2ThetaAboveLeaf0011320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113202)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113202))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113202))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113202)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113202))) h)
theorem e24KC2ThetaAboveLeaf0011320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113203))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113203))) h)
theorem e24KC2ThetaAboveLeaf0011320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113203))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113203))) h)
theorem e24KC2ThetaAboveLeaf0011320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113203))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113203))) h)
theorem e24KC2ThetaAboveLeaf0011320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113203)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113203))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113203))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113203)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113203))) h)
theorem e24KC2ThetaAboveLeaf0011321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113210))) h)
theorem e24KC2ThetaAboveLeaf0011321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113210))) h)
theorem e24KC2ThetaAboveLeaf0011321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113210))) h)
theorem e24KC2ThetaAboveLeaf0011321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113210))) h)
theorem e24KC2ThetaAboveLeaf0011321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113211))) h)
theorem e24KC2ThetaAboveLeaf0011321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113211))) h)
theorem e24KC2ThetaAboveLeaf0011321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113211))) h)
theorem e24KC2ThetaAboveLeaf0011321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113211))) h)
theorem e24KC2ThetaAboveLeaf0011321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113212))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113212))) h)
theorem e24KC2ThetaAboveLeaf0011321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113212))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113212))) h)
theorem e24KC2ThetaAboveLeaf0011321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113212))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113212))) h)
theorem e24KC2ThetaAboveLeaf0011321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113212)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113212))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113212))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113212)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113212))) h)
theorem e24KC2ThetaAboveLeaf0011321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113213))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113213))) h)
theorem e24KC2ThetaAboveLeaf0011321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113213))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113213))) h)
theorem e24KC2ThetaAboveLeaf0011321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113213))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113213))) h)
theorem e24KC2ThetaAboveLeaf0011321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113213)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113213))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113213))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113213)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113213))) h)
theorem e24KC2ThetaAboveLeaf0011330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113300))) h)
theorem e24KC2ThetaAboveLeaf0011330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113300))) h)
theorem e24KC2ThetaAboveLeaf0011330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113300))) h)
theorem e24KC2ThetaAboveLeaf0011330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113300))) h)
theorem e24KC2ThetaAboveLeaf0011330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00113301))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00113301))) h)
theorem e24KC2ThetaAboveLeaf0011330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00113301))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00113301))) h)
theorem e24KC2ThetaAboveLeaf0011330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00113301))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00113301))) h)
theorem e24KC2ThetaAboveLeaf0011330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00113301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00113301))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00113301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00113301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00113301))) h)
theorem e24KC2ThetaAboveLeaf0011330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113302))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113302))) h)
theorem e24KC2ThetaAboveLeaf0011330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113302))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113302))) h)
theorem e24KC2ThetaAboveLeaf0011330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113302))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113302))) h)
theorem e24KC2ThetaAboveLeaf0011330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113302)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113302))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113302))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113302)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113302))) h)
theorem e24KC2ThetaAboveLeaf0011330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00113303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLL thetaAboveCell00113303))
    (by
      have h : ((childLL (childLL (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childLH (childLL (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHL (childLL (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHH (childLL (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLL
        thetaAboveCell00113303))) h)
theorem e24KC2ThetaAboveLeaf0011330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00113303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLL thetaAboveCell00113303))
    (by
      have h : ((childLL (childLH (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childLH (childLH (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHL (childLH (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLL
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHH (childLH (childLL thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLL
        thetaAboveCell00113303))) h)
theorem e24KC2ThetaAboveLeaf0011330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00113303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childLH thetaAboveCell00113303))
    (by
      have h : ((childLL (childLL (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLL (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childLH (childLL (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLL (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHL (childLL (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLL (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHH (childLL (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLL (childLH
        thetaAboveCell00113303))) h)
theorem e24KC2ThetaAboveLeaf0011330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00113303)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childLH thetaAboveCell00113303))
    (by
      have h : ((childLL (childLH (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childLH (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childLH (childLH (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childLH (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHL (childLH (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childLH (childLH
        thetaAboveCell00113303))) h)
    (by
      have h : ((childHH (childLH (childLH thetaAboveCell00113303)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childLH (childLH
        thetaAboveCell00113303))) h)

end PartE
end GerverSofa

end

end

end

end

end

end
