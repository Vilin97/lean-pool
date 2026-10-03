/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch032`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells27082ce600

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `1111331130100210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130100333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130100333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113010)))

/-- Subcell `1111331130101020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101130 : AngleCell :=
  childLL (childHH (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101131 : AngleCell :=
  childLH (childHH (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101132 : AngleCell :=
  childHL (childHH (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101133 : AngleCell :=
  childHH (childHH (childLH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113010)))

/-- Subcell `1111331130101333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130101333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113010)))

end GerverSofa.PartE.CertificateCells27082ce600

namespace GerverSofa.PartE.CertificateCellsc3c599388b

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsc3c599388b

namespace GerverSofa.PartE.CertificateCells6f9c2931ea

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6f9c2931ea

namespace GerverSofa.PartE.CertificateCells5955d51af9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022002101)))

/-- Subcell `0000220021013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022002101)))

end GerverSofa.PartE.CertificateCells5955d51af9

namespace GerverSofa.PartE.CertificateCellsde04ff5fef

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131000020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000020 : AngleCell :=
  childLL (childHL (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000021 : AngleCell :=
  childLH (childHL (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000022 : AngleCell :=
  childHL (childHL (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000023 : AngleCell :=
  childHH (childHL (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000030 : AngleCell :=
  childLL (childHH (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000031 : AngleCell :=
  childLH (childHH (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000032 : AngleCell :=
  childHL (childHH (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000033 : AngleCell :=
  childHH (childHH (childLL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000120 : AngleCell :=
  childLL (childHL (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000121 : AngleCell :=
  childLH (childHL (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000122 : AngleCell :=
  childHL (childHL (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000123 : AngleCell :=
  childHH (childHL (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000130 : AngleCell :=
  childLL (childHH (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000131 : AngleCell :=
  childLH (childHH (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000132 : AngleCell :=
  childHL (childHH (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000133 : AngleCell :=
  childHH (childHH (childLH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113100)))

/-- Subcell `1111331131000333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113100)))

end GerverSofa.PartE.CertificateCellsde04ff5fef

namespace GerverSofa.PartE.CertificateCells750522796b

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells750522796b

namespace GerverSofa.PartE.CertificateCells99ba2b246f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022002101)))

end GerverSofa.PartE.CertificateCells99ba2b246f

namespace GerverSofa.PartE.CertificateCells6443c5ba4b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022002111)))

/-- Subcell `0000220021112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022002111)))

end GerverSofa.PartE.CertificateCells6443c5ba4b

namespace GerverSofa.PartE.CertificateCells03dbb8f506

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells03dbb8f506

namespace GerverSofa.PartE.CertificateCells15b8ca5094

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022002101)))

end GerverSofa.PartE.CertificateCells15b8ca5094

namespace GerverSofa.PartE.CertificateCellsecf9e4e90b

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsecf9e4e90b

namespace GerverSofa.PartE.CertificateCellsdb6ee29ee4

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022002110)))

/-- Subcell `0000220021103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022002110)))

end GerverSofa.PartE.CertificateCellsdb6ee29ee4

namespace GerverSofa.PartE.CertificateCells4003309a28

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `000022002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells4003309a28

namespace GerverSofa.PartE.CertificateCellsf3f1dbc459

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCellsf3f1dbc459

namespace GerverSofa.PartE.CertificateCells441cc2b0d8

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCells441cc2b0d8

namespace GerverSofa.PartE.CertificateCells5980303e93

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5980303e93

namespace GerverSofa.PartE.CertificateCellsa9276513a2

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsa9276513a2

namespace GerverSofa.PartE.CertificateCells9972cada5a

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells9972cada5a

namespace GerverSofa.PartE.CertificateCellsa6306b8bb7

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131112000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCellsa6306b8bb7

namespace GerverSofa.PartE.CertificateCellsc1e1941644

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131012000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell111133113101)))

/-- Subcell `1111331131012113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell111133113101)))

end GerverSofa.PartE.CertificateCellsc1e1941644

namespace GerverSofa.PartE.CertificateCells5a169f617b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells5a169f617b

namespace GerverSofa.PartE.CertificateCellsc15ab9b9a5

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsc15ab9b9a5

namespace GerverSofa.PartE.CertificateCells861ec8c785

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells861ec8c785

namespace GerverSofa.PartE.CertificateCells854f59bf16

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `1111331130011320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113001)))

/-- Subcell `1111331130011333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113001)))

end GerverSofa.PartE.CertificateCells854f59bf16

namespace GerverSofa.PartE.CertificateCells5153122198

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131112100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell111133113111)))

/-- Subcell `1111331131112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCells5153122198

namespace GerverSofa.PartE.CertificateCells0a969d2c42

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131102000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell111133113110)))

/-- Subcell `1111331131102113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell111133113110)))

end GerverSofa.PartE.CertificateCells0a969d2c42

namespace GerverSofa.PartE.CertificateCells50ae5a428f

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131101220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113110)))

/-- Subcell `1111331131101313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131101313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113110)))

end GerverSofa.PartE.CertificateCells50ae5a428f

namespace GerverSofa.PartE.CertificateCells754567fdeb

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022002101)))

end GerverSofa.PartE.CertificateCells754567fdeb

namespace GerverSofa.PartE.CertificateCells146a7460c7

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells146a7460c7

namespace GerverSofa.PartE.CertificateCells5446bfae87

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131100220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113110)))

/-- Subcell `1111331131100313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131100313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113110)))

end GerverSofa.PartE.CertificateCells5446bfae87

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6R4Subtree01d19858ee032aa8`.
* `KernelOnly.PartE.E24KC6R4Subtree04c8a4da4d3d19a1`.
* `KernelOnly.PartE.E24KC6R4Subtree1033056e03edbb99`.
* `KernelOnly.PartE.E24KC6R4Subtree1952c351f5a890d0`.
* `KernelOnly.PartE.E24KC6R4Subtree1974d41b8023f47d`.
* `KernelOnly.PartE.E24KC6R4Subtree19ea3647d9c4385d`.
* `KernelOnly.PartE.E24KC6R4Subtree1df7325990c509b9`.
* `KernelOnly.PartE.E24KC6R4Subtree1ec47ff132608c89`.
* `KernelOnly.PartE.E24KC6R4Subtree23aa11edc1c0beab`.
* `KernelOnly.PartE.E24KC6R4Subtree291bec528ce09a45`.
* `KernelOnly.PartE.E24KC6R4Subtree31a1bf2506de3a6b`.
* `KernelOnly.PartE.E24KC6R4Subtree35d8a6b024243cfb`.
* `KernelOnly.PartE.E24KC6R4Subtree369cc1bf8a73ac93`.
* `KernelOnly.PartE.E24KC6R4Subtree3bdce31885f964fb`.
* `KernelOnly.PartE.E24KC6R4Subtree3e7c6f0a436cdb12`.
* `KernelOnly.PartE.E24KC6R4Subtree403b497f85c69738`.
* `KernelOnly.PartE.E24KC6R4Subtree428fdb9c294c5957`.
* `KernelOnly.PartE.E24KC6R4Subtree4417485270da2542`.
* `KernelOnly.PartE.E24KC6R4Subtree55d98d161eaa82bf`.
* `KernelOnly.PartE.E24KC6R4Subtree60715e5435db178e`.
* `KernelOnly.PartE.E24KC6R4Subtree60cca7d0a876716e`.
* `KernelOnly.PartE.E24KC6R4Subtree639075a28aed7212`.
* `KernelOnly.PartE.E24KC6R4Subtree6ec7ee50125cb2b8`.
* `KernelOnly.PartE.E24KC6R4Subtree70c72a172c9cfd93`.
* `KernelOnly.PartE.E24KC6R4Subtree70d61ab175d41a4a`.
* `KernelOnly.PartE.E24KC6R4Subtree7734a7147db71699`.
* `KernelOnly.PartE.E24KC6R4Subtree77fe1988ff8cd192`.
* `KernelOnly.PartE.E24KC6R4Subtree7a80e3dfcc4f34f3`.
* `KernelOnly.PartE.E24KC6R4Subtree7a9ec2fb66ec8862`.
* `KernelOnly.PartE.E24KC6R4Subtree7ae79e99a9b79eaf`.
-/

public section

noncomputable section

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells27082ce600

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells27082ce600

open CertificateCells27082ce600
theorem cover_subtree_49690a55e534 :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113010))
    (by
      have h : ((childLL (childHL (childLL thetaBelowCell111133113010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
        thetaBelowCell111133113010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100210 h)
        (by
          have h : (thetaBelowCell1111331130100211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100211 h)
        (by
          have h : (thetaBelowCell1111331130100212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100212 h)
        (by
          have h : (thetaBelowCell1111331130100213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100220 h)
        (by
          have h : (thetaBelowCell1111331130100221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100221 h)
        (by
          have h : (thetaBelowCell1111331130100222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100222 h)
        (by
          have h : (thetaBelowCell1111331130100223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100230 h)
        (by
          have h : (thetaBelowCell1111331130100231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100231 h)
        (by
          have h : (thetaBelowCell1111331130100232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100232 h)
        (by
          have h : (thetaBelowCell1111331130100233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100233 h))

theorem cover_subtree_ca9ffb091c53 :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113010))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100300 h)
        (by
          have h : (thetaBelowCell1111331130100301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100301 h)
        (by
          have h : (thetaBelowCell1111331130100302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100302 h)
        (by
          have h : (thetaBelowCell1111331130100303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100310 h)
        (by
          have h : (thetaBelowCell1111331130100311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100311 h)
        (by
          have h : (thetaBelowCell1111331130100312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100312 h)
        (by
          have h : (thetaBelowCell1111331130100313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100320 h)
        (by
          have h : (thetaBelowCell1111331130100321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100321 h)
        (by
          have h : (thetaBelowCell1111331130100322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100322 h)
        (by
          have h : (thetaBelowCell1111331130100323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130100330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100330 h)
        (by
          have h : (thetaBelowCell1111331130100331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100331 h)
        (by
          have h : (thetaBelowCell1111331130100332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100332 h)
        (by
          have h : (thetaBelowCell1111331130100333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130100333 h))

theorem cover_subtree_afcf5ef458d7 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113010)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113010))) h))
    cover_subtree_49690a55e534
    cover_subtree_ca9ffb091c53

theorem cover_subtree_51fb51ed5b56 :
    adaptiveCoverCheck 4 (childLL (childLH thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113010))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell111133113010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
        thetaBelowCell111133113010))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell111133113010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
        thetaBelowCell111133113010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101020 h)
        (by
          have h : (thetaBelowCell1111331130101021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101021 h)
        (by
          have h : (thetaBelowCell1111331130101022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101022 h)
        (by
          have h : (thetaBelowCell1111331130101023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101030 h)
        (by
          have h : (thetaBelowCell1111331130101031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101031 h)
        (by
          have h : (thetaBelowCell1111331130101032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101032 h)
        (by
          have h : (thetaBelowCell1111331130101033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101033 h))

theorem cover_subtree_f305258c7368 :
    adaptiveCoverCheck 4 (childLH (childLH thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113010))
    (by
      have h : ((childLL (childLH (childLH thetaBelowCell111133113010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
        thetaBelowCell111133113010))) h)
    (by
      have h : ((childLH (childLH (childLH thetaBelowCell111133113010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
        thetaBelowCell111133113010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101120 h)
        (by
          have h : (thetaBelowCell1111331130101121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101121 h)
        (by
          have h : (thetaBelowCell1111331130101122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101122 h)
        (by
          have h : (thetaBelowCell1111331130101123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101130 h)
        (by
          have h : (thetaBelowCell1111331130101131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101131 h)
        (by
          have h : (thetaBelowCell1111331130101132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101132 h)
        (by
          have h : (thetaBelowCell1111331130101133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101133 h))

theorem cover_subtree_5599471dbfbf :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113010))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101200 h)
        (by
          have h : (thetaBelowCell1111331130101201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101201 h)
        (by
          have h : (thetaBelowCell1111331130101202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101202 h)
        (by
          have h : (thetaBelowCell1111331130101203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101210 h)
        (by
          have h : (thetaBelowCell1111331130101211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101211 h)
        (by
          have h : (thetaBelowCell1111331130101212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101212 h)
        (by
          have h : (thetaBelowCell1111331130101213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101220 h)
        (by
          have h : (thetaBelowCell1111331130101221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101221 h)
        (by
          have h : (thetaBelowCell1111331130101222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101222 h)
        (by
          have h : (thetaBelowCell1111331130101223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101230 h)
        (by
          have h : (thetaBelowCell1111331130101231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101231 h)
        (by
          have h : (thetaBelowCell1111331130101232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101232 h)
        (by
          have h : (thetaBelowCell1111331130101233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101233 h))

theorem cover_subtree_5b939cb0e15c :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113010))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101300 h)
        (by
          have h : (thetaBelowCell1111331130101301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101301 h)
        (by
          have h : (thetaBelowCell1111331130101302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101302 h)
        (by
          have h : (thetaBelowCell1111331130101303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101310 h)
        (by
          have h : (thetaBelowCell1111331130101311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101311 h)
        (by
          have h : (thetaBelowCell1111331130101312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101312 h)
        (by
          have h : (thetaBelowCell1111331130101313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101320 h)
        (by
          have h : (thetaBelowCell1111331130101321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101321 h)
        (by
          have h : (thetaBelowCell1111331130101322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101322 h)
        (by
          have h : (thetaBelowCell1111331130101323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
        thetaBelowCell111133113010)))
        (by
          have h : (thetaBelowCell1111331130101330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101330 h)
        (by
          have h : (thetaBelowCell1111331130101331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101331 h)
        (by
          have h : (thetaBelowCell1111331130101332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101332 h)
        (by
          have h : (thetaBelowCell1111331130101333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130101333 h))

theorem cover_subtree_2f4f93c67946 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113010)
    cover_subtree_51fb51ed5b56
    cover_subtree_f305258c7368
    cover_subtree_5599471dbfbf
    cover_subtree_5b939cb0e15c

theorem cover_subtree_1374b272a307 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113010)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
            thetaBelowCell111133113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133113010))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell111133113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113010)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113010)) h)

theorem cover_subtree_91c9f04664e0 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113010)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
            thetaBelowCell111133113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113010))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
            thetaBelowCell111133113010))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell111133113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
            thetaBelowCell111133113010))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell111133113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH thetaBelowCell111133113010)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell111133113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH thetaBelowCell111133113010)) h)

theorem e24KC2ThetaBelowLeaf111133113_c0_c1_c0 :
    adaptiveCoverCheck 6 thetaBelowCell111133113010 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113010
    cover_subtree_afcf5ef458d7
    cover_subtree_2f4f93c67946
    cover_subtree_1374b272a307
    cover_subtree_91c9f04664e0

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc3c599388b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc3c599388b

open CertificateCellsc3c599388b
theorem e24KC2ThetaBelowLeaf111133113_c1_c2 :
    adaptiveCoverCheck 7 (childHL (childLH (childHH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLH (childHH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133113120).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113120 h)
    (by
      have h : (thetaBelowCell111133113121).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113121 h)
    (by
      have h : (thetaBelowCell111133113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113122 h)
    (by
      have h : (thetaBelowCell111133113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113123 h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6f9c2931ea

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6f9c2931ea

open CertificateCells6f9c2931ea
theorem e24KC2ThetaAboveLeaf0000220021_c2 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00002200)))
    (by
      have h : (thetaAboveCell000022002120).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002120 h)
    (by
      have h : (thetaAboveCell000022002121).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002121 h)
    (by
      have h : (thetaAboveCell000022002122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002122 h)
    (by
      have h : (thetaAboveCell000022002123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002123 h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5955d51af9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5955d51af9

open CertificateCells5955d51af9
theorem cover_subtree_f2e068b42d23 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021013000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013000 h)
    (by
      have h : (thetaAboveCell0000220021013001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013002
        (by
          have h : ((childLL thetaAboveCell0000220021013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013002) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013002) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013002) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013003
        (by
          have h : ((childLL thetaAboveCell0000220021013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013003) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013003) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013003) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013003) h))

theorem cover_subtree_6c2a359fbe9a :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021013010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013010 h)
    (by
      have h : (thetaAboveCell0000220021013011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013012
        (by
          have h : ((childLL thetaAboveCell0000220021013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013012) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013012) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013012) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013013
        (by
          have h : ((childLL thetaAboveCell0000220021013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013013) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013013) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013013) h))

theorem cover_subtree_fe0ef8f0f647 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022002101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013020
        (by
          have h : ((childLL thetaAboveCell0000220021013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013020) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013020) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013020) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013021
        (by
          have h : ((childLL thetaAboveCell0000220021013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013021) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013021) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013021) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013022
        (by
          have h : ((childLL thetaAboveCell0000220021013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013023
        (by
          have h : ((childLL thetaAboveCell0000220021013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013023) h))

theorem cover_subtree_fdabca9a4955 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022002101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013030
        (by
          have h : ((childLL thetaAboveCell0000220021013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013030) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013030) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013030) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013031
        (by
          have h : ((childLL thetaAboveCell0000220021013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013031) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013031) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013031) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013032
        (by
          have h : ((childLL thetaAboveCell0000220021013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013033
        (by
          have h : ((childLL thetaAboveCell0000220021013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013033) h))

theorem cover_subtree_c4b02e6e9e8a :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002101))
    cover_subtree_f2e068b42d23
    cover_subtree_6c2a359fbe9a
    cover_subtree_fe0ef8f0f647
    cover_subtree_fdabca9a4955

theorem cover_subtree_6859a502ecc6 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021013100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013100 h)
    (by
      have h : (thetaAboveCell0000220021013101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013102
        (by
          have h : ((childLL thetaAboveCell0000220021013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013103
        (by
          have h : ((childLL thetaAboveCell0000220021013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013103) h))

theorem cover_subtree_f4d742b10a6f :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021013110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013110 h)
    (by
      have h : (thetaAboveCell0000220021013111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013112
        (by
          have h : ((childLL thetaAboveCell0000220021013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013113
        (by
          have h : ((childLL thetaAboveCell0000220021013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013113) h))

theorem cover_subtree_659abecde61a :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022002101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013120
        (by
          have h : ((childLL thetaAboveCell0000220021013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013120) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013120) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013120) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013121
        (by
          have h : ((childLL thetaAboveCell0000220021013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013121) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013121) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013121) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013122
        (by
          have h : ((childLL thetaAboveCell0000220021013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013123
        (by
          have h : ((childLL thetaAboveCell0000220021013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013123) h))

theorem cover_subtree_ad8d4e6209b9 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022002101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013130
        (by
          have h : ((childLL thetaAboveCell0000220021013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013130) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013130) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013130) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013131
        (by
          have h : ((childLL thetaAboveCell0000220021013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013132
        (by
          have h : ((childLL thetaAboveCell0000220021013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021013133
        (by
          have h : ((childLL thetaAboveCell0000220021013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021013133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021013133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021013133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021013133) h))

theorem cover_subtree_465622ba8fb4 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002101))
    cover_subtree_6859a502ecc6
    cover_subtree_f4d742b10a6f
    cover_subtree_659abecde61a
    cover_subtree_ad8d4e6209b9

theorem cover_subtree_f5a0481cebfc :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022002101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013200 h)
        (by
          have h : (thetaAboveCell0000220021013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013201 h)
        (by
          have h : (thetaAboveCell0000220021013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013202 h)
        (by
          have h : (thetaAboveCell0000220021013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013210 h)
        (by
          have h : (thetaAboveCell0000220021013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013211 h)
        (by
          have h : (thetaAboveCell0000220021013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013212 h)
        (by
          have h : (thetaAboveCell0000220021013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022002101))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022002101))) h)

theorem cover_subtree_c6ead7987dc9 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022002101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013300 h)
        (by
          have h : (thetaAboveCell0000220021013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013301 h)
        (by
          have h : (thetaAboveCell0000220021013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013302 h)
        (by
          have h : (thetaAboveCell0000220021013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013310 h)
        (by
          have h : (thetaAboveCell0000220021013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013311 h)
        (by
          have h : (thetaAboveCell0000220021013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013312 h)
        (by
          have h : (thetaAboveCell0000220021013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022002101))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022002101))) h)

theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002101)
    cover_subtree_c4b02e6e9e8a
    cover_subtree_465622ba8fb4
    cover_subtree_f5a0481cebfc
    cover_subtree_c6ead7987dc9

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsde04ff5fef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsde04ff5fef

open CertificateCellsde04ff5fef
theorem cover_subtree_0d52430fd500 :
    adaptiveCoverCheck 4 (childLL (childLL thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113100))
    (by
      have h : ((childLL (childLL (childLL thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
        thetaBelowCell111133113100))) h)
    (by
      have h : ((childLH (childLL (childLL thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
        thetaBelowCell111133113100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000020 h)
        (by
          have h : (thetaBelowCell1111331131000021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000021 h)
        (by
          have h : (thetaBelowCell1111331131000022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000022 h)
        (by
          have h : (thetaBelowCell1111331131000023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000030 h)
        (by
          have h : (thetaBelowCell1111331131000031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000031 h)
        (by
          have h : (thetaBelowCell1111331131000032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000032 h)
        (by
          have h : (thetaBelowCell1111331131000033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000033 h))

theorem cover_subtree_f0f2a49a1c42 :
    adaptiveCoverCheck 4 (childLH (childLL thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113100))
    (by
      have h : ((childLL (childLH (childLL thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
        thetaBelowCell111133113100))) h)
    (by
      have h : ((childLH (childLH (childLL thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
        thetaBelowCell111133113100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000120 h)
        (by
          have h : (thetaBelowCell1111331131000121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000121 h)
        (by
          have h : (thetaBelowCell1111331131000122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000122 h)
        (by
          have h : (thetaBelowCell1111331131000123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000130 h)
        (by
          have h : (thetaBelowCell1111331131000131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000131 h)
        (by
          have h : (thetaBelowCell1111331131000132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000132 h)
        (by
          have h : (thetaBelowCell1111331131000133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000133 h))

theorem cover_subtree_ac65d29ed71a :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113100))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000200 h)
        (by
          have h : (thetaBelowCell1111331131000201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000201 h)
        (by
          have h : (thetaBelowCell1111331131000202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000202 h)
        (by
          have h : (thetaBelowCell1111331131000203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000210 h)
        (by
          have h : (thetaBelowCell1111331131000211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000211 h)
        (by
          have h : (thetaBelowCell1111331131000212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000212 h)
        (by
          have h : (thetaBelowCell1111331131000213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000220 h)
        (by
          have h : (thetaBelowCell1111331131000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000221 h)
        (by
          have h : (thetaBelowCell1111331131000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000222 h)
        (by
          have h : (thetaBelowCell1111331131000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000230 h)
        (by
          have h : (thetaBelowCell1111331131000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000231 h)
        (by
          have h : (thetaBelowCell1111331131000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000232 h)
        (by
          have h : (thetaBelowCell1111331131000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000233 h))

theorem cover_subtree_b80d2217aa18 :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113100))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000300 h)
        (by
          have h : (thetaBelowCell1111331131000301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000301 h)
        (by
          have h : (thetaBelowCell1111331131000302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000302 h)
        (by
          have h : (thetaBelowCell1111331131000303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000310 h)
        (by
          have h : (thetaBelowCell1111331131000311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000311 h)
        (by
          have h : (thetaBelowCell1111331131000312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000312 h)
        (by
          have h : (thetaBelowCell1111331131000313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000320 h)
        (by
          have h : (thetaBelowCell1111331131000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000321 h)
        (by
          have h : (thetaBelowCell1111331131000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000322 h)
        (by
          have h : (thetaBelowCell1111331131000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000330 h)
        (by
          have h : (thetaBelowCell1111331131000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000331 h)
        (by
          have h : (thetaBelowCell1111331131000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000332 h)
        (by
          have h : (thetaBelowCell1111331131000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131000333 h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c0 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113100)
    cover_subtree_0d52430fd500
    cover_subtree_f0f2a49a1c42
    cover_subtree_ac65d29ed71a
    cover_subtree_b80d2217aa18

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells750522796b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells750522796b

open CertificateCells750522796b
theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c2 :
    adaptiveCoverCheck 6 thetaBelowCell111133113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113102
    (by
      have h : ((childLL thetaBelowCell111133113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113102) h)
    (by
      have h : ((childLH thetaBelowCell111133113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113102) h)
    (by
      have h : ((childHL thetaBelowCell111133113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113102) h)
    (by
      have h : ((childHH thetaBelowCell111133113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113102) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells99ba2b246f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells99ba2b246f

open CertificateCells99ba2b246f
theorem cover_subtree_bda1c51066a4 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021012100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012100 h)
    (by
      have h : (thetaAboveCell0000220021012101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012102
        (by
          have h : ((childLL thetaAboveCell0000220021012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012103
        (by
          have h : ((childLL thetaAboveCell0000220021012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012103) h))

theorem cover_subtree_c820aa5287c7 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021012110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012110 h)
    (by
      have h : (thetaAboveCell0000220021012111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012112
        (by
          have h : ((childLL thetaAboveCell0000220021012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012113
        (by
          have h : ((childLL thetaAboveCell0000220021012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012113) h))

theorem cover_subtree_538d3ba3b92e :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012120 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012120
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012120)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012120)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012120)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012120)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012120)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012120) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012120)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012120) h)

theorem cover_subtree_ba0b8d4abb41 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012121 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012121
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012121)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012121)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012121)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012121)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012121)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012121) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012121)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012121) h)

theorem cover_subtree_d11d13dd2be9 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022002101)))
    cover_subtree_538d3ba3b92e
    cover_subtree_ba0b8d4abb41
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012122
        (by
          have h : ((childLL thetaAboveCell0000220021012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012123
        (by
          have h : ((childLL thetaAboveCell0000220021012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012123) h))

theorem cover_subtree_60696ffddf60 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012130 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012130
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012130)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012130)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012130)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012130)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012130)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012130) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012130)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012130) h)

theorem cover_subtree_90c18ca6ca12 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022002101)))
    cover_subtree_60696ffddf60
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012131
        (by
          have h : ((childLL thetaAboveCell0000220021012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012132
        (by
          have h : ((childLL thetaAboveCell0000220021012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012133
        (by
          have h : ((childLL thetaAboveCell0000220021012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012133) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002101))
    cover_subtree_bda1c51066a4
    cover_subtree_c820aa5287c7
    cover_subtree_d11d13dd2be9
    cover_subtree_90c18ca6ca12

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6443c5ba4b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6443c5ba4b

open CertificateCells6443c5ba4b
theorem cover_subtree_100284623361 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021112000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112000 h)
    (by
      have h : (thetaAboveCell0000220021112001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112002
        (by
          have h : ((childLL thetaAboveCell0000220021112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112002) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112002) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112002) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112003
        (by
          have h : ((childLL thetaAboveCell0000220021112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112003) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112003) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112003) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112003) h))

theorem cover_subtree_06468370fe05 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021112010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112010 h)
    (by
      have h : (thetaAboveCell0000220021112011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112012
        (by
          have h : ((childLL thetaAboveCell0000220021112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112012) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112012) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112012) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112013
        (by
          have h : ((childLL thetaAboveCell0000220021112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112013) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112013) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112013) h))

theorem cover_subtree_a6aeae3aff5e :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112020
        (by
          have h : ((childLL thetaAboveCell0000220021112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112020) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112020) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112020) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112021
        (by
          have h : ((childLL thetaAboveCell0000220021112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112021) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112021) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112021) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112022
        (by
          have h : ((childLL thetaAboveCell0000220021112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112023
        (by
          have h : ((childLL thetaAboveCell0000220021112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112023) h))

theorem cover_subtree_e6a5a6a1c8c7 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112030
        (by
          have h : ((childLL thetaAboveCell0000220021112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112030) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112030) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112030) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112031
        (by
          have h : ((childLL thetaAboveCell0000220021112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112031) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112031) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112031) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112032
        (by
          have h : ((childLL thetaAboveCell0000220021112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112033
        (by
          have h : ((childLL thetaAboveCell0000220021112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112033) h))

theorem cover_subtree_b7bd7dd08527 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002111))
    cover_subtree_100284623361
    cover_subtree_06468370fe05
    cover_subtree_a6aeae3aff5e
    cover_subtree_e6a5a6a1c8c7

theorem cover_subtree_19177aff5ede :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021112100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112100 h)
    (by
      have h : (thetaAboveCell0000220021112101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112102
        (by
          have h : ((childLL thetaAboveCell0000220021112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112103
        (by
          have h : ((childLL thetaAboveCell0000220021112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112103) h))

theorem cover_subtree_a6e5897577a8 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021112110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112110 h)
    (by
      have h : (thetaAboveCell0000220021112111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112112
        (by
          have h : ((childLL thetaAboveCell0000220021112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112113
        (by
          have h : ((childLL thetaAboveCell0000220021112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112113) h))

theorem cover_subtree_c0e11192bd72 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112120
        (by
          have h : ((childLL thetaAboveCell0000220021112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112120) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112120) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112120) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112121
        (by
          have h : ((childLL thetaAboveCell0000220021112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112121) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112121) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112121) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112122
        (by
          have h : ((childLL thetaAboveCell0000220021112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112123
        (by
          have h : ((childLL thetaAboveCell0000220021112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112123) h))

theorem cover_subtree_3544788b12c5 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112130
        (by
          have h : ((childLL thetaAboveCell0000220021112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112130) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112130) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112130) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112131
        (by
          have h : ((childLL thetaAboveCell0000220021112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112132
        (by
          have h : ((childLL thetaAboveCell0000220021112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021112133
        (by
          have h : ((childLL thetaAboveCell0000220021112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021112133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021112133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021112133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021112133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021112133) h))

theorem cover_subtree_4f053fea53cc :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002111))
    cover_subtree_19177aff5ede
    cover_subtree_a6e5897577a8
    cover_subtree_c0e11192bd72
    cover_subtree_3544788b12c5

theorem cover_subtree_ad3586fc5d64 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022002111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112200 h)
        (by
          have h : (thetaAboveCell0000220021112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112201 h)
        (by
          have h : (thetaAboveCell0000220021112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112202 h)
        (by
          have h : (thetaAboveCell0000220021112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112210 h)
        (by
          have h : (thetaAboveCell0000220021112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112211 h)
        (by
          have h : (thetaAboveCell0000220021112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112212 h)
        (by
          have h : (thetaAboveCell0000220021112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022002111))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022002111))) h)

theorem cover_subtree_a8dfb5281914 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022002111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112300 h)
        (by
          have h : (thetaAboveCell0000220021112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112301 h)
        (by
          have h : (thetaAboveCell0000220021112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112302 h)
        (by
          have h : (thetaAboveCell0000220021112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112310 h)
        (by
          have h : (thetaAboveCell0000220021112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112311 h)
        (by
          have h : (thetaAboveCell0000220021112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112312 h)
        (by
          have h : (thetaAboveCell0000220021112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022002111))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022002111))) h)

theorem e24KC2ThetaAboveLeaf0000220021_c1_c1_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002111)
    cover_subtree_b7bd7dd08527
    cover_subtree_4f053fea53cc
    cover_subtree_ad3586fc5d64
    cover_subtree_a8dfb5281914

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells03dbb8f506

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells03dbb8f506

open CertificateCells03dbb8f506
theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002101)
    (by
      have h : ((childLL (childLH thetaAboveCell000022002101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022002101)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022002101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022002101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022002101))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022002101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022002101))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022002101))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells15b8ca5094

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells15b8ca5094

open CertificateCells15b8ca5094
theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022002101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012300 h)
        (by
          have h : (thetaAboveCell0000220021012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012301 h)
        (by
          have h : (thetaAboveCell0000220021012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012302 h)
        (by
          have h : (thetaAboveCell0000220021012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012310 h)
        (by
          have h : (thetaAboveCell0000220021012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012311 h)
        (by
          have h : (thetaAboveCell0000220021012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012312 h)
        (by
          have h : (thetaAboveCell0000220021012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022002101))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022002101))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsecf9e4e90b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsecf9e4e90b

open CertificateCellsecf9e4e90b
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c2 :
    adaptiveCoverCheck 4 (childHL (childHL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHL (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHL (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHL (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHL (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHL
        thetaBelowCell111133113111))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb6ee29ee4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdb6ee29ee4

open CertificateCellsdb6ee29ee4
theorem cover_subtree_4cc417ccb089 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021103000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103000 h)
    (by
      have h : (thetaAboveCell0000220021103001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103002
        (by
          have h : ((childLL thetaAboveCell0000220021103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103002) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103002) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103002) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103003
        (by
          have h : ((childLL thetaAboveCell0000220021103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103003) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103003) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103003) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103003) h))

theorem cover_subtree_3b70ffafef44 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021103010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103010 h)
    (by
      have h : (thetaAboveCell0000220021103011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103012
        (by
          have h : ((childLL thetaAboveCell0000220021103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103012) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103012) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103012) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103013
        (by
          have h : ((childLL thetaAboveCell0000220021103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103013) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103013) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103013) h))

theorem cover_subtree_dcf1d830bfb7 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103020
        (by
          have h : ((childLL thetaAboveCell0000220021103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103020) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103020) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103020) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103021
        (by
          have h : ((childLL thetaAboveCell0000220021103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103021) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103021) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103021) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103022
        (by
          have h : ((childLL thetaAboveCell0000220021103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103023
        (by
          have h : ((childLL thetaAboveCell0000220021103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103023) h))

theorem cover_subtree_8808b93a2a5b :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103030
        (by
          have h : ((childLL thetaAboveCell0000220021103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103030) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103030) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103030) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103031
        (by
          have h : ((childLL thetaAboveCell0000220021103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103031) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103031) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103031) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103032
        (by
          have h : ((childLL thetaAboveCell0000220021103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103033
        (by
          have h : ((childLL thetaAboveCell0000220021103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103033) h))

theorem cover_subtree_adc568740138 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002110))
    cover_subtree_4cc417ccb089
    cover_subtree_3b70ffafef44
    cover_subtree_dcf1d830bfb7
    cover_subtree_8808b93a2a5b

theorem cover_subtree_9d7ffe00b1e7 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021103100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103100 h)
    (by
      have h : (thetaAboveCell0000220021103101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103102
        (by
          have h : ((childLL thetaAboveCell0000220021103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103103
        (by
          have h : ((childLL thetaAboveCell0000220021103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103103) h))

theorem cover_subtree_0d9aaf9c725c :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021103110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103110 h)
    (by
      have h : (thetaAboveCell0000220021103111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103112
        (by
          have h : ((childLL thetaAboveCell0000220021103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103113
        (by
          have h : ((childLL thetaAboveCell0000220021103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103113) h))

theorem cover_subtree_d26de62ce5c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103120
        (by
          have h : ((childLL thetaAboveCell0000220021103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103120) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103120) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103120) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103121
        (by
          have h : ((childLL thetaAboveCell0000220021103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103121) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103121) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103121) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103122
        (by
          have h : ((childLL thetaAboveCell0000220021103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103123
        (by
          have h : ((childLL thetaAboveCell0000220021103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103123) h))

theorem cover_subtree_6e084944e1b7 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103130
        (by
          have h : ((childLL thetaAboveCell0000220021103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103130) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103130) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103130) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103131
        (by
          have h : ((childLL thetaAboveCell0000220021103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103132
        (by
          have h : ((childLL thetaAboveCell0000220021103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021103133
        (by
          have h : ((childLL thetaAboveCell0000220021103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021103133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021103133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021103133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021103133) h))

theorem cover_subtree_e73271ac6053 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002110))
    cover_subtree_9d7ffe00b1e7
    cover_subtree_0d9aaf9c725c
    cover_subtree_d26de62ce5c2
    cover_subtree_6e084944e1b7

theorem cover_subtree_0ec46983a3e4 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022002110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103200 h)
        (by
          have h : (thetaAboveCell0000220021103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103201 h)
        (by
          have h : (thetaAboveCell0000220021103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103202 h)
        (by
          have h : (thetaAboveCell0000220021103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103210 h)
        (by
          have h : (thetaAboveCell0000220021103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103211 h)
        (by
          have h : (thetaAboveCell0000220021103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103212 h)
        (by
          have h : (thetaAboveCell0000220021103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022002110))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022002110))) h)

theorem cover_subtree_5cbb0735d9b5 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022002110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103300 h)
        (by
          have h : (thetaAboveCell0000220021103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103301 h)
        (by
          have h : (thetaAboveCell0000220021103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103302 h)
        (by
          have h : (thetaAboveCell0000220021103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103310 h)
        (by
          have h : (thetaAboveCell0000220021103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103311 h)
        (by
          have h : (thetaAboveCell0000220021103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103312 h)
        (by
          have h : (thetaAboveCell0000220021103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022002110))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022002110))) h)

theorem e24KC2ThetaAboveLeaf0000220021_c1_c0_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002110)
    cover_subtree_adc568740138
    cover_subtree_e73271ac6053
    cover_subtree_0ec46983a3e4
    cover_subtree_5cbb0735d9b5

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4003309a28

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4003309a28

open CertificateCells4003309a28
theorem e24KC2ThetaAboveLeaf0000220021_c3 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00002200)))
    (by
      have h : (thetaAboveCell000022002130).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002130 h)
    (by
      have h : (thetaAboveCell000022002131).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002131 h)
    (by
      have h : (thetaAboveCell000022002132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002132 h)
    (by
      have h : (thetaAboveCell000022002133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022002133 h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf3f1dbc459

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf3f1dbc459

open CertificateCellsf3f1dbc459
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022002100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002300 h)
        (by
          have h : (thetaAboveCell0000220021002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002301 h)
        (by
          have h : (thetaAboveCell0000220021002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002302 h)
        (by
          have h : (thetaAboveCell0000220021002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002310 h)
        (by
          have h : (thetaAboveCell0000220021002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002311 h)
        (by
          have h : (thetaAboveCell0000220021002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002312 h)
        (by
          have h : (thetaAboveCell0000220021002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022002100))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022002100))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells441cc2b0d8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells441cc2b0d8

open CertificateCells441cc2b0d8
theorem cover_subtree_9a19b7b479a6 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113100 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113100
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113100)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113100)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113100)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113100)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113100)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113100)) h))

theorem cover_subtree_d45287132b6e :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113101 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113101
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113101)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113101)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113101)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113101)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113101)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113101)) h))

theorem cover_subtree_e155163f58e6 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113102
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113102)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113102)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113102)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113102)) h))
    (by
      have h : ((childHL thetaBelowCell1111331131113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113102) h)
    (by
      have h : ((childHH thetaBelowCell1111331131113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113102) h)

theorem cover_subtree_8c5c60491e76 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113103
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113103)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113103)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113103)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113103)) h))
    (by
      have h : ((childHL thetaBelowCell1111331131113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113103) h)
    (by
      have h : ((childHH thetaBelowCell1111331131113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113103) h)

theorem cover_subtree_deda1d8f689c :
    adaptiveCoverCheck 3 (childLL (childLH (childHH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHH
    thetaBelowCell111133113111)))
    cover_subtree_9a19b7b479a6
    cover_subtree_d45287132b6e
    cover_subtree_e155163f58e6
    cover_subtree_8c5c60491e76

theorem cover_subtree_afe933400d68 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113110 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113110
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113110)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113110)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113110)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113110)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113110)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113110)) h))

theorem cover_subtree_3d26797fa2c0 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113111 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113111
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113111)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113111)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113111)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113111)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113111)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113111)) h))

theorem cover_subtree_2306090dc6e1 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113112
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113112)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113112)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113112)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113112)) h))
    (by
      have h : ((childHL thetaBelowCell1111331131113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113112) h)
    (by
      have h : ((childHH thetaBelowCell1111331131113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113112) h)

theorem cover_subtree_f50a24eff089 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113113
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113113)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113113)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113113)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113113)) h))
    (by
      have h : ((childHL thetaBelowCell1111331131113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113113) h)
    (by
      have h : ((childHH thetaBelowCell1111331131113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113113) h)

theorem cover_subtree_5a8fcf48e536 :
    adaptiveCoverCheck 3 (childLH (childLH (childHH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHH
    thetaBelowCell111133113111)))
    cover_subtree_afe933400d68
    cover_subtree_3d26797fa2c0
    cover_subtree_2306090dc6e1
    cover_subtree_f50a24eff089

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c1 :
    adaptiveCoverCheck 4 (childLH (childHH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113111))
    cover_subtree_deda1d8f689c
    cover_subtree_5a8fcf48e536
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childHH
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113120 h)
        (by
          have h : (thetaBelowCell1111331131113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113121 h)
        (by
          have h : (thetaBelowCell1111331131113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113122 h)
        (by
          have h : (thetaBelowCell1111331131113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childHH
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113130 h)
        (by
          have h : (thetaBelowCell1111331131113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113131 h)
        (by
          have h : (thetaBelowCell1111331131113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113132 h)
        (by
          have h : (thetaBelowCell1111331131113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113133 h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5980303e93

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5980303e93

open CertificateCells5980303e93
theorem e24KC2ThetaAboveLeaf0000220021_c1_c0_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002110)
    (by
      have h : ((childLL (childLH thetaAboveCell000022002110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022002110)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022002110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022002110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022002110))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022002110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022002110))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022002110))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa9276513a2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa9276513a2

open CertificateCellsa9276513a2
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c2 :
    adaptiveCoverCheck 6 thetaBelowCell111133113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113112
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113112)
        (by
          have h : ((childLL (childLL thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113112)
        (by
          have h : ((childLL (childLH thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133113112)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133113112)) h))
    (by
      have h : ((childHL thetaBelowCell111133113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113112) h)
    (by
      have h : ((childHH thetaBelowCell111133113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113112) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9972cada5a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9972cada5a

open CertificateCells9972cada5a
theorem e24KC2ThetaBelowLeaf111133113_c2 :
    adaptiveCoverCheck 8 (childHL (childHH thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH thetaBelowCell11113311))
    (by
      have h : ((childLL (childHL (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHL (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHL (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHL (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHL (childHH
        thetaBelowCell11113311))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa6306b8bb7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa6306b8bb7

open CertificateCellsa6306b8bb7
theorem cover_subtree_64ca6a23a782 :
    adaptiveCoverCheck 3 (childLL (childLL (childHL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHL
    thetaBelowCell111133113111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112000
        (by
          have h : ((childLL thetaBelowCell1111331131112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112000) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112000) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112000) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112001
        (by
          have h : ((childLL thetaBelowCell1111331131112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112001) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112001) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112001) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112002
        (by
          have h : ((childLL thetaBelowCell1111331131112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112002) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112002) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112002) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112003
        (by
          have h : ((childLL thetaBelowCell1111331131112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112003) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112003) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112003) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112003) h))

theorem cover_subtree_5f702c8c435f :
    adaptiveCoverCheck 3 (childLH (childLL (childHL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHL
    thetaBelowCell111133113111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112010
        (by
          have h : ((childLL thetaBelowCell1111331131112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112010) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112010) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112010) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112011
        (by
          have h : ((childLL thetaBelowCell1111331131112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112011) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112011) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112011) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131112011)
            (by
              have h : ((childLL (childHH thetaBelowCell1111331131112011))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
                thetaBelowCell1111331131112011)) h)
            (by
              have h : ((childLH (childHH thetaBelowCell1111331131112011))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
                thetaBelowCell1111331131112011)) h)
            (by
              have h : ((childHL (childHH thetaBelowCell1111331131112011))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
                thetaBelowCell1111331131112011)) h)
            (by
              have h : ((childHH (childHH thetaBelowCell1111331131112011))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
                thetaBelowCell1111331131112011)) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112012
        (by
          have h : ((childLL thetaBelowCell1111331131112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112012) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112012) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112012) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112013
        (by
          have h : ((childLL thetaBelowCell1111331131112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112013) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112013) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112013) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112013) h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c0 :
    adaptiveCoverCheck 4 (childLL (childHL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113111))
    cover_subtree_64ca6a23a782
    cover_subtree_5f702c8c435f
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childHL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112020 h)
        (by
          have h : (thetaBelowCell1111331131112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112021 h)
        (by
          have h : (thetaBelowCell1111331131112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112022 h)
        (by
          have h : (thetaBelowCell1111331131112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childHL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112030 h)
        (by
          have h : (thetaBelowCell1111331131112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112031 h)
        (by
          have h : (thetaBelowCell1111331131112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112032 h)
        (by
          have h : (thetaBelowCell1111331131112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112033 h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc1e1941644

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc1e1941644

open CertificateCellsc1e1941644
theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c2 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113101))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHL
            thetaBelowCell111133113101)))
            (by
              have h : (thetaBelowCell1111331131012000).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012000 h)
            (by
              have h : (thetaBelowCell1111331131012001).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012001 h)
            (by
              have h : (thetaBelowCell1111331131012002).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012002 h)
            (by
              have h : (thetaBelowCell1111331131012003).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012003 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHL
            thetaBelowCell111133113101)))
            (by
              have h : (thetaBelowCell1111331131012010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012010 h)
            (by
              have h : (thetaBelowCell1111331131012011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012011 h)
            (by
              have h : (thetaBelowCell1111331131012012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012012 h)
            (by
              have h : (thetaBelowCell1111331131012013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012013 h))
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
            thetaBelowCell111133113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113101))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL
            thetaBelowCell111133113101)))
            (by
              have h : (thetaBelowCell1111331131012100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012100 h)
            (by
              have h : (thetaBelowCell1111331131012101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012101 h)
            (by
              have h : (thetaBelowCell1111331131012102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012102 h)
            (by
              have h : (thetaBelowCell1111331131012103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL
            thetaBelowCell111133113101)))
            (by
              have h : (thetaBelowCell1111331131012110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012110 h)
            (by
              have h : (thetaBelowCell1111331131012111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012111 h)
            (by
              have h : (thetaBelowCell1111331131012112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012112 h)
            (by
              have h : (thetaBelowCell1111331131012113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131012113 h))
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133113101))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell111133113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113101)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113101)) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5a169f617b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5a169f617b

open CertificateCells5a169f617b
theorem e24KC2ThetaAboveLeaf0000220021_c1_c1_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002111)
    (by
      have h : ((childLL (childLH thetaAboveCell000022002111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022002111)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022002111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022002111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022002111))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022002111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022002111))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022002111))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc15ab9b9a5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc15ab9b9a5

open CertificateCellsc15ab9b9a5
theorem e24KC2ThetaBelowLeaf111133113_c0_c1_c3 :
    adaptiveCoverCheck 6 thetaBelowCell111133113013 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113013
    (by
      have h : ((childLL thetaBelowCell111133113013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113013) h)
    (by
      have h : ((childLH thetaBelowCell111133113013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113013) h)
    (by
      have h : ((childHL thetaBelowCell111133113013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113013) h)
    (by
      have h : ((childHH thetaBelowCell111133113013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113013) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells861ec8c785

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells861ec8c785

open CertificateCells861ec8c785
theorem e24KC2ThetaAboveLeaf0000220021_c1_c0_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002110)
    (by
      have h : ((childLL (childLL thetaAboveCell000022002110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022002110)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022002110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022002110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022002110))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022002110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022002110))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022002110))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022002110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022002110))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells854f59bf16

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells854f59bf16

open CertificateCells854f59bf16
theorem cover_subtree_868906559995 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113000)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113000))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113000))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113000))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113000))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133113000))) h))

theorem cover_subtree_cf661e32fd3c :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113000)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113000))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113000))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113000))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113000))
        (by
          have h : ((childLL (childHH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childLH (childHH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHL (childHH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLH
            thetaBelowCell111133113000))) h)
        (by
          have h : ((childHH (childHH (childLH thetaBelowCell111133113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLH
            thetaBelowCell111133113000))) h))

theorem cover_subtree_852412a1da1f :
    adaptiveCoverCheck 6 thetaBelowCell111133113000 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113000
    cover_subtree_868906559995
    cover_subtree_cf661e32fd3c
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113000)
        (by
          have h : ((childLL (childHL thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL
            thetaBelowCell111133113000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113000)
        (by
          have h : ((childLL (childHH thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH
            thetaBelowCell111133113000)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell111133113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH
            thetaBelowCell111133113000)) h))

theorem cover_subtree_5c713f8b8f83 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113001)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childHL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childHL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childHL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childHL (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLL
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childHH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childHH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childHH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childLL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childHH (childLL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childLL
            thetaBelowCell111133113001))) h))

theorem cover_subtree_9ce321b0f1ea :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113001))
    (by
      have h : ((childLL (childHH (childLH thetaBelowCell111133113001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
        thetaBelowCell111133113001))) h)
    (by
      have h : ((childLH (childHH (childLH thetaBelowCell111133113001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
        thetaBelowCell111133113001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
        thetaBelowCell111133113001)))
        (by
          have h : (thetaBelowCell1111331130011320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011320 h)
        (by
          have h : (thetaBelowCell1111331130011321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011321 h)
        (by
          have h : (thetaBelowCell1111331130011322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011322 h)
        (by
          have h : (thetaBelowCell1111331130011323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
        thetaBelowCell111133113001)))
        (by
          have h : (thetaBelowCell1111331130011330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011330 h)
        (by
          have h : (thetaBelowCell1111331130011331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011331 h)
        (by
          have h : (thetaBelowCell1111331130011332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011332 h)
        (by
          have h : (thetaBelowCell1111331130011333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130011333 h))

theorem cover_subtree_5f41a0b225f7 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113001)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113001))
        (by
          have h : ((childLL (childHL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childHL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childHL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childLH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childHL (childLH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childLH
            thetaBelowCell111133113001))) h))
    cover_subtree_9ce321b0f1ea

theorem cover_subtree_dce958c46e4b :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113001)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133113001))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell111133113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113001)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113001)) h)

theorem cover_subtree_5f44219dd9e0 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113001)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
            thetaBelowCell111133113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113001))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
            thetaBelowCell111133113001))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell111133113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
            thetaBelowCell111133113001))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell111133113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH thetaBelowCell111133113001)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell111133113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH thetaBelowCell111133113001)) h)

theorem cover_subtree_f79674f0cd5e :
    adaptiveCoverCheck 6 thetaBelowCell111133113001 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113001
    cover_subtree_5c713f8b8f83
    cover_subtree_5f41a0b225f7
    cover_subtree_dce958c46e4b
    cover_subtree_5f44219dd9e0

theorem e24KC2ThetaBelowLeaf111133113_c0_c0 :
    adaptiveCoverCheck 7 (childLL (childLL (childHH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childLL (childLL (childHH thetaBelowCell11113311)))
    cover_subtree_852412a1da1f
    cover_subtree_f79674f0cd5e
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113002
        (by
          have h : ((childLL thetaBelowCell111133113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113002) h)
        (by
          have h : ((childLH thetaBelowCell111133113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113002) h)
        (by
          have h : ((childHL thetaBelowCell111133113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113002) h)
        (by
          have h : ((childHH thetaBelowCell111133113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113003
        (by
          have h : ((childLL thetaBelowCell111133113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113003) h)
        (by
          have h : ((childLH thetaBelowCell111133113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113003) h)
        (by
          have h : ((childHL thetaBelowCell111133113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113003) h)
        (by
          have h : ((childHH thetaBelowCell111133113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113003) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5153122198

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5153122198

open CertificateCells5153122198
theorem cover_subtree_4d0609015f95 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131112100 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112100
    (by
      have h : ((childLL thetaBelowCell1111331131112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112100) h)
    (by
      have h : ((childLH thetaBelowCell1111331131112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112100) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131112100)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131112100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131112100)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131112100)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131112100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131112100)) h))

theorem cover_subtree_dc10eb0281eb :
    adaptiveCoverCheck 2 thetaBelowCell1111331131112101 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112101
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131112101)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131112101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131112101)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131112101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131112101)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131112101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131112101)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131112101)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131112101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131112101)) h))

theorem cover_subtree_115058b1a8cb :
    adaptiveCoverCheck 3 (childLL (childLH (childHL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL
    thetaBelowCell111133113111)))
    cover_subtree_4d0609015f95
    cover_subtree_dc10eb0281eb
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112102
        (by
          have h : ((childLL thetaBelowCell1111331131112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112102) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112102) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112102) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112103
        (by
          have h : ((childLL thetaBelowCell1111331131112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112103) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112103) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112103) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112103) h))

theorem cover_subtree_73eb4fcea78d :
    adaptiveCoverCheck 2 thetaBelowCell1111331131112110 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112110
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131112110)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131112110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131112110)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131112110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131112110)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131112110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131112110)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131112110)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131112110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131112110)) h))

theorem cover_subtree_44584246e90e :
    adaptiveCoverCheck 2 thetaBelowCell1111331131112111 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112111
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131112111)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131112111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131112111)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131112111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131112111)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131112111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131112111)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131112111)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131112111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131112111)) h))

theorem cover_subtree_0e57e75e5954 :
    adaptiveCoverCheck 3 (childLH (childLH (childHL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL
    thetaBelowCell111133113111)))
    cover_subtree_73eb4fcea78d
    cover_subtree_44584246e90e
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112112
        (by
          have h : ((childLL thetaBelowCell1111331131112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112112) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112112) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112112) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131112113
        (by
          have h : ((childLL thetaBelowCell1111331131112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131112113) h)
        (by
          have h : ((childLH thetaBelowCell1111331131112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131112113) h)
        (by
          have h : ((childHL thetaBelowCell1111331131112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131112113) h)
        (by
          have h : ((childHH thetaBelowCell1111331131112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131112113) h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c1 :
    adaptiveCoverCheck 4 (childLH (childHL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113111))
    cover_subtree_115058b1a8cb
    cover_subtree_0e57e75e5954
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childHL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112120 h)
        (by
          have h : (thetaBelowCell1111331131112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112121 h)
        (by
          have h : (thetaBelowCell1111331131112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112122 h)
        (by
          have h : (thetaBelowCell1111331131112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childHL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112130 h)
        (by
          have h : (thetaBelowCell1111331131112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112131 h)
        (by
          have h : (thetaBelowCell1111331131112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112132 h)
        (by
          have h : (thetaBelowCell1111331131112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131112133 h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0a969d2c42

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0a969d2c42

open CertificateCells0a969d2c42
theorem cover_subtree_6164650f4936 :
    adaptiveCoverCheck 3 (childLL (childLL (childHL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102000
        (by
          have h : ((childLL thetaBelowCell1111331131102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102000) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102000) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102000) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102001
        (by
          have h : ((childLL thetaBelowCell1111331131102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102001) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102001) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102001) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102001) h))
    (by
      have h : (thetaBelowCell1111331131102002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102002 h)
    (by
      have h : (thetaBelowCell1111331131102003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102003 h)

theorem cover_subtree_3db66bc1eb1b :
    adaptiveCoverCheck 3 (childLH (childLL (childHL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102010
        (by
          have h : ((childLL thetaBelowCell1111331131102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102010) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102010) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102010) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102011
        (by
          have h : ((childLL thetaBelowCell1111331131102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102011) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102011) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102011) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102011) h))
    (by
      have h : (thetaBelowCell1111331131102012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102012 h)
    (by
      have h : (thetaBelowCell1111331131102013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102013 h)

theorem cover_subtree_3f70d11b4e7e :
    adaptiveCoverCheck 4 (childLL (childHL thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113110))
    cover_subtree_6164650f4936
    cover_subtree_3db66bc1eb1b
    (by
      have h : ((childHL (childLL (childHL thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
        thetaBelowCell111133113110))) h)
    (by
      have h : ((childHH (childLL (childHL thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
        thetaBelowCell111133113110))) h)

theorem cover_subtree_261557c5db75 :
    adaptiveCoverCheck 3 (childLL (childLH (childHL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102100
        (by
          have h : ((childLL thetaBelowCell1111331131102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102100) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102100) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102100) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102101
        (by
          have h : ((childLL thetaBelowCell1111331131102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102101) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102101) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102101) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102101) h))
    (by
      have h : (thetaBelowCell1111331131102102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102102 h)
    (by
      have h : (thetaBelowCell1111331131102103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102103 h)

theorem cover_subtree_12428cd495c4 :
    adaptiveCoverCheck 3 (childLH (childLH (childHL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102110
        (by
          have h : ((childLL thetaBelowCell1111331131102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102110) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102110) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102110) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131102111
        (by
          have h : ((childLL thetaBelowCell1111331131102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131102111) h)
        (by
          have h : ((childLH thetaBelowCell1111331131102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131102111) h)
        (by
          have h : ((childHL thetaBelowCell1111331131102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131102111) h)
        (by
          have h : ((childHH thetaBelowCell1111331131102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131102111) h))
    (by
      have h : (thetaBelowCell1111331131102112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102112 h)
    (by
      have h : (thetaBelowCell1111331131102113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131102113 h)

theorem cover_subtree_adb043cdb732 :
    adaptiveCoverCheck 4 (childLH (childHL thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113110))
    cover_subtree_261557c5db75
    cover_subtree_12428cd495c4
    (by
      have h : ((childHL (childLH (childHL thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
        thetaBelowCell111133113110))) h)
    (by
      have h : ((childHH (childLH (childHL thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
        thetaBelowCell111133113110))) h)

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c2 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113110)
    cover_subtree_3f70d11b4e7e
    cover_subtree_adb043cdb732
    (by
      have h : ((childHL (childHL thetaBelowCell111133113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113110)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113110)) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells50ae5a428f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells50ae5a428f

open CertificateCells50ae5a428f
theorem cover_subtree_2e97d4844408 :
    adaptiveCoverCheck 3 (childHL (childHL (childLH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101220
        (by
          have h : ((childLL thetaBelowCell1111331131101220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101220) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101220) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101220) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101221
        (by
          have h : ((childLL thetaBelowCell1111331131101221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101221) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101221) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101221) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101222
        (by
          have h : ((childLL thetaBelowCell1111331131101222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101222) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101222) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101222) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101223
        (by
          have h : ((childLL thetaBelowCell1111331131101223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101223) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101223) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101223) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101223) h))

theorem cover_subtree_0dc0f2664d18 :
    adaptiveCoverCheck 3 (childHH (childHL (childLH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101230
        (by
          have h : ((childLL thetaBelowCell1111331131101230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101230) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101230) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101230) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101231
        (by
          have h : ((childLL thetaBelowCell1111331131101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101231) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101231) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101231) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101232
        (by
          have h : ((childLL thetaBelowCell1111331131101232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101232) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101232) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101232) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101233
        (by
          have h : ((childLL thetaBelowCell1111331131101233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101233) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101233) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101233) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101233) h))

theorem cover_subtree_60a2aff6cef2 :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113110))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131101200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101200 h)
        (by
          have h : (thetaBelowCell1111331131101201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101201 h)
        (by
          have h : (thetaBelowCell1111331131101202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101202 h)
        (by
          have h : (thetaBelowCell1111331131101203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131101210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101210 h)
        (by
          have h : (thetaBelowCell1111331131101211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101211 h)
        (by
          have h : (thetaBelowCell1111331131101212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101212 h)
        (by
          have h : (thetaBelowCell1111331131101213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101213 h))
    cover_subtree_2e97d4844408
    cover_subtree_0dc0f2664d18

theorem cover_subtree_ab4066e0c111 :
    adaptiveCoverCheck 3 (childHL (childHH (childLH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101320
        (by
          have h : ((childLL thetaBelowCell1111331131101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101320) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101320) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101320) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101321
        (by
          have h : ((childLL thetaBelowCell1111331131101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101321) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101321) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101321) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101322
        (by
          have h : ((childLL thetaBelowCell1111331131101322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101322) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101322) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101322) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101323
        (by
          have h : ((childLL thetaBelowCell1111331131101323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101323) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101323) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101323) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101323) h))

theorem cover_subtree_8607f2894d1c :
    adaptiveCoverCheck 3 (childHH (childHH (childLH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101330
        (by
          have h : ((childLL thetaBelowCell1111331131101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101330) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101330) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101330) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101331
        (by
          have h : ((childLL thetaBelowCell1111331131101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101331) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101331) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101331) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101332
        (by
          have h : ((childLL thetaBelowCell1111331131101332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131101333
        (by
          have h : ((childLL thetaBelowCell1111331131101333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131101333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131101333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131101333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131101333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131101333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131101333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131101333) h))

theorem cover_subtree_dca1503025ec :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113110))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131101300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101300 h)
        (by
          have h : (thetaBelowCell1111331131101301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101301 h)
        (by
          have h : (thetaBelowCell1111331131101302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101302 h)
        (by
          have h : (thetaBelowCell1111331131101303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131101310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101310 h)
        (by
          have h : (thetaBelowCell1111331131101311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101311 h)
        (by
          have h : (thetaBelowCell1111331131101312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101312 h)
        (by
          have h : (thetaBelowCell1111331131101313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131101313 h))
    cover_subtree_ab4066e0c111
    cover_subtree_8607f2894d1c

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113110)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113110))) h))
    cover_subtree_60a2aff6cef2
    cover_subtree_dca1503025ec

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells754567fdeb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells754567fdeb

open CertificateCells754567fdeb
theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022002101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012200 h)
        (by
          have h : (thetaAboveCell0000220021012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012201 h)
        (by
          have h : (thetaAboveCell0000220021012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012202 h)
        (by
          have h : (thetaAboveCell0000220021012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022002101)))
        (by
          have h : (thetaAboveCell0000220021012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012210 h)
        (by
          have h : (thetaAboveCell0000220021012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012211 h)
        (by
          have h : (thetaAboveCell0000220021012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012212 h)
        (by
          have h : (thetaAboveCell0000220021012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022002101))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022002101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022002101))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells146a7460c7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells146a7460c7

open CertificateCells146a7460c7
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022002100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002200 h)
        (by
          have h : (thetaAboveCell0000220021002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002201 h)
        (by
          have h : (thetaAboveCell0000220021002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002202 h)
        (by
          have h : (thetaAboveCell0000220021002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002210 h)
        (by
          have h : (thetaAboveCell0000220021002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002211 h)
        (by
          have h : (thetaAboveCell0000220021002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002212 h)
        (by
          have h : (thetaAboveCell0000220021002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022002100))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022002100))) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5446bfae87

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells5446bfae87

open CertificateCells5446bfae87
theorem cover_subtree_847043a66fa6 :
    adaptiveCoverCheck 3 (childHL (childHL (childLL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100220
        (by
          have h : ((childLL thetaBelowCell1111331131100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100220) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100220) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100220) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100221
        (by
          have h : ((childLL thetaBelowCell1111331131100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100221) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100221) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100221) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100222
        (by
          have h : ((childLL thetaBelowCell1111331131100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100222) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100222) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100222) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100223
        (by
          have h : ((childLL thetaBelowCell1111331131100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100223) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100223) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100223) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100223) h))

theorem cover_subtree_9cd5da4b1592 :
    adaptiveCoverCheck 3 (childHH (childHL (childLL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100230
        (by
          have h : ((childLL thetaBelowCell1111331131100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100230) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100230) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100230) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100231
        (by
          have h : ((childLL thetaBelowCell1111331131100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100231) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100231) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100231) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100232
        (by
          have h : ((childLL thetaBelowCell1111331131100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100232) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100232) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100232) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100233
        (by
          have h : ((childLL thetaBelowCell1111331131100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100233) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100233) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100233) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100233) h))

theorem cover_subtree_49612604cfd8 :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113110))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131100200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100200 h)
        (by
          have h : (thetaBelowCell1111331131100201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100201 h)
        (by
          have h : (thetaBelowCell1111331131100202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100202 h)
        (by
          have h : (thetaBelowCell1111331131100203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131100210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100210 h)
        (by
          have h : (thetaBelowCell1111331131100211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100211 h)
        (by
          have h : (thetaBelowCell1111331131100212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100212 h)
        (by
          have h : (thetaBelowCell1111331131100213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100213 h))
    cover_subtree_847043a66fa6
    cover_subtree_9cd5da4b1592

theorem cover_subtree_e94de792d061 :
    adaptiveCoverCheck 3 (childHL (childHH (childLL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100320
        (by
          have h : ((childLL thetaBelowCell1111331131100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100320) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100320) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100320) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100321
        (by
          have h : ((childLL thetaBelowCell1111331131100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100321) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100321) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100321) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100322
        (by
          have h : ((childLL thetaBelowCell1111331131100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100322) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100322) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100322) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100323
        (by
          have h : ((childLL thetaBelowCell1111331131100323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100323) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100323) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100323) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100323) h))

theorem cover_subtree_0fbb14a9cae8 :
    adaptiveCoverCheck 3 (childHH (childHH (childLL thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100330
        (by
          have h : ((childLL thetaBelowCell1111331131100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100330) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100330) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100330) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100331
        (by
          have h : ((childLL thetaBelowCell1111331131100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100331) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100331) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100331) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100332
        (by
          have h : ((childLL thetaBelowCell1111331131100332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131100333
        (by
          have h : ((childLL thetaBelowCell1111331131100333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131100333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131100333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131100333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131100333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131100333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131100333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131100333) h))

theorem cover_subtree_ac6486a45a05 :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113110))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131100300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100300 h)
        (by
          have h : (thetaBelowCell1111331131100301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100301 h)
        (by
          have h : (thetaBelowCell1111331131100302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100302 h)
        (by
          have h : (thetaBelowCell1111331131100303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131100310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100310 h)
        (by
          have h : (thetaBelowCell1111331131100311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100311 h)
        (by
          have h : (thetaBelowCell1111331131100312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100312 h)
        (by
          have h : (thetaBelowCell1111331131100313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131100313 h))
    cover_subtree_e94de792d061
    cover_subtree_0fbb14a9cae8

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c0 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113110)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113110))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113110))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113110))) h))
    cover_subtree_49612604cfd8
    cover_subtree_ac6486a45a05

end PartE
end GerverSofa

end

end

end

end

end

end
